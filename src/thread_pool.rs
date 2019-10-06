use std::{
    collections::BTreeMap,
    future::Future,
    mem::{replace, transmute},
    pin::Pin,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, RwLock, Weak,
    },
    task::{Context, Poll},
    thread,
};

use abort_on_panic::abort_on_panic;
use async_task::{JoinHandle, Task};
use crossbeam_channel::{unbounded, Sender};

type Prio = (usize, usize, u8, usize);
type WeakSchedule = Weak<RwLock<Option<Task<()>>>>;

#[derive(Default)]
struct Pending {
    next_gc: usize,
    queue: BTreeMap<Prio, WeakSchedule>,
}

pub struct ThreadPool {
    queue: Sender<Task<()>>,
    pending_queue: Sender<(Prio, WeakSchedule)>,
    pending: Arc<RwLock<Pending>>,
    pending_id: AtomicUsize,
}

pub struct Handle<T> {
    handle: JoinHandle<T, ()>,
}

#[derive(Clone)]
pub struct Schedule {
    task: Arc<RwLock<Option<Task<()>>>>,
}

impl Schedule {
    pub fn schedule(&self) -> bool {
        if let Some(task) = self.task.write().unwrap().take() {
            task.schedule();
            true
        } else {
            false
        }
    }

    pub fn is_scheduled(&self) -> bool {
        self.task.read().unwrap().is_none()
    }
}

impl<T> Future for Handle<T> {
    type Output = T;

    fn poll(mut self: Pin<&mut Self>, ctx: &mut Context) -> Poll<Self::Output> {
        Pin::new(&mut self.handle)
            .poll(ctx)
            .map(|result| result.unwrap())
    }
}

impl<T> Drop for Handle<T> {
    fn drop(&mut self) {
        self.handle.cancel();
    }
}

impl ThreadPool {
    pub fn spawn<'a, O>(&'a self, future: Pin<Box<dyn Future<Output = O> + Send + 'a>>) -> Handle<O>
    where
        O: Send + 'static,
    {
        let (handle, schedule) = self.spawn_delayed(future);
        schedule.schedule();
        handle
    }

    pub fn spawn_delayed<'a, O>(
        &'a self,
        future: Pin<Box<dyn Future<Output = O> + Send + 'a>>,
    ) -> (Handle<O>, Schedule)
    where
        O: Send + 'static,
    {
        let queue = self.queue.clone();

        let future = unsafe {
            transmute::<
                Pin<Box<dyn Future<Output = O> + Send + '_>>,
                Pin<Box<dyn Future<Output = O> + Send + 'static>>,
            >(future)
        };

        let (task, handle) = async_task::spawn(
            future,
            {
                move |task| {
                    queue.send(task).unwrap();
                }
            },
            (),
        );
        (
            Handle { handle },
            Schedule {
                task: Arc::new(RwLock::new(Some(task))),
            },
        )
    }

    pub fn add_pending(&self, level: usize, len: usize, bound: u8, schedule: &Schedule) {
        let id = self.pending_id.fetch_add(1, Ordering::Relaxed);

        self.pending_queue
            .send(((level, len, bound, id), Arc::downgrade(&schedule.task)))
            .unwrap();
    }

    pub fn scope<T>(in_scope: impl FnOnce(&ThreadPool) -> T) -> T {
        let (sender, receiver) = unbounded::<Task<()>>();

        let (pending_sender, pending_receiver) = unbounded::<(Prio, WeakSchedule)>();

        let pool = Self {
            queue: sender,
            pending_queue: pending_sender,
            pending: Default::default(),
            pending_id: 0.into(),
        };

        let threads = num_cpus::get().max(1);

        let workers = (0..threads)
            .map(|_worker| {
                let receiver = receiver.clone();
                let pending_receiver = pending_receiver.clone();
                let pending = pool.pending.clone();
                thread::spawn(move || 'outer: loop {
                    while let Ok(task) = receiver.try_recv() {
                        abort_on_panic!("task panicked", { task.run() });
                    }

                    {
                        let mut pending_mut = pending.write().unwrap();

                        let queue_limit = pending_receiver.len() * 2;

                        let mut counter = 0;
                        while let Ok((prio, task)) = pending_receiver.try_recv() {
                            if pending_mut.queue.len() >= pending_mut.next_gc {
                                let old_queue = replace(&mut pending_mut.queue, Default::default());

                                pending_mut.queue = old_queue
                                    .into_iter()
                                    .filter(|(_prio, schedule)| {
                                        if let Some(schedule) = schedule.upgrade() {
                                            !(Schedule { task: schedule }).is_scheduled()
                                        } else {
                                            false
                                        }
                                    })
                                    .collect();

                                pending_mut.next_gc = pending_mut.queue.len().max(5000) * 2;
                            }

                            pending_mut.queue.insert(prio, task);
                            counter += 1;
                            if counter >= queue_limit {
                                break;
                            }
                        }

                        while let Some(&prio) = pending_mut.queue.keys().next() {
                            let schedule = pending_mut.queue.remove(&prio).unwrap();
                            if let Some(schedule) = schedule.upgrade() {
                                if (Schedule { task: schedule }).schedule() {
                                    continue 'outer;
                                }
                            }
                        }
                    }

                    if let Ok(task) = receiver.recv() {
                        abort_on_panic!("task panicked", { task.run() });
                    } else {
                        break;
                    }
                })
            })
            .collect::<Vec<_>>();

        let _guard = scopeguard::guard((), |_| {
            for worker in workers {
                let _ignored = worker.join();
            }
        });

        let result = in_scope(&pool);

        drop(pool);

        result
    }
}
