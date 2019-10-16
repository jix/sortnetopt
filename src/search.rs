use std::{
    collections::hash_map::Entry,
    fs::{create_dir, File},
    io::{self, BufWriter, ErrorKind, Write},
    path::PathBuf,
    pin::Pin,
    sync::Arc,
    time::{Duration, Instant},
};

use async_std::{prelude::*, task, task::sleep};
use futures::{pending, poll, task::Poll};
use rustc_hash::FxHashMap as HashMap;

mod states;

use self::states::{State, StateMap};
use crate::{
    huffman::max_plus_1_huffman,
    output_set::{CVec, OutputSet},
    thread_pool::{Handle, Schedule, ThreadPool},
};

pub struct Search {
    states: StateMap,
}

type Prio = (usize, usize, u8);

impl Search {
    pub fn search(
        initial: OutputSet<&[bool]>,
        limit: Option<usize>,
        output: Option<PathBuf>,
    ) -> usize {
        let search = Self {
            states: StateMap::default(),
        };

        let mut initial = initial.to_owned_bvec();

        let limit = limit.unwrap_or(usize::max_value());

        initial.canonicalize(true);

        let final_bound = ThreadPool::scope(|pool| {
            let _info_thread = pool.spawn(Box::pin(async {
                let mut last_msg = Instant::now();
                loop {
                    let next_msg = last_msg + Duration::from_secs(10);
                    let sleep_for = next_msg.saturating_duration_since(Instant::now());
                    last_msg = next_msg;
                    sleep(sleep_for).await;
                    search.log_stats();
                }
            }));

            let main_loop = pool.spawn(Box::pin(async {
                let mut state = search.states.get(initial.as_ref());
                loop {
                    if state.bounds[0] == state.bounds[1] || state.bounds[0] as usize >= limit {
                        break state.bounds[0] as usize;
                    }
                    state = search.improve(pool, 0, state, initial.as_ref()).await;
                    log::info!("bounds: {:?}", state);
                    search.log_stats();
                }
            }));

            task::block_on(main_loop)
        });

        if let Some(output) = output {
            search.dump_states(output).unwrap();
        }

        final_bound
    }

    fn dump_states(self, output: PathBuf) -> io::Result<()> {
        match create_dir(&output) {
            Err(err) if err.kind() == ErrorKind::AlreadyExists => Ok(()),
            res => res,
        }?;

        let mut index = BufWriter::new(File::create(output.join("index.txt"))?);

        let mut group_files = HashMap::<(usize, u8), BufWriter<File>>::default();
        for mut shard in self.states.into_shards() {
            for (channels, packed, state) in shard.drain_packed() {
                let group = (channels, state.bounds[0]);
                let group_file = match group_files.entry(group) {
                    Entry::Occupied(entry) => entry.into_mut(),
                    Entry::Vacant(entry) => {
                        let group_name = format!("group_{}_{}.bin", group.0, group.1);
                        writeln!(&mut index, "{}", group_name)?;
                        let group_file = BufWriter::new(File::create(output.join(group_name))?);
                        entry.insert(group_file)
                    }
                };

                group_file.write_all(&packed)?;
            }
        }

        Ok(())
    }

    fn log_stats(&self) {
        log::info!("states: {:?}", self.states.len());
    }

    fn improve_boxed<'a>(
        &'a self,
        pool: &'a ThreadPool<Prio>,
        level: usize,
        previous_state: State,
        output_set: OutputSet,
    ) -> Pin<Box<dyn Future<Output = State> + Send + 'a>> {
        Box::pin(async move {
            self.improve(pool, level, previous_state, output_set.as_ref())
                .await
        })
    }

    #[allow(unreachable_code)]
    async fn improve(
        &self,
        pool: &ThreadPool<Prio>,
        level: usize,
        previous_state: State,
        output_set: OutputSet<&[bool]>,
    ) -> State {
        let _locked = loop {
            let state = self.states.get(output_set);
            if state != previous_state {
                return state;
            }
            if state.bounds[0] == state.bounds[1] {
                return state;
            }

            if let Some(locked) = self.states.lock(output_set).await {
                break locked;
            }
        };

        let mut state = self.states.get(output_set);

        if state != previous_state {
            return state;
        }
        if state.bounds[0] == state.bounds[1] {
            return state;
        }

        let mut extremal_channels = [CVec::new(), CVec::new()];

        for (pol, pol_channels) in extremal_channels.iter_mut().enumerate() {
            for channel in 0..output_set.channels() {
                if output_set.channel_is_extremal(pol > 0, channel) {
                    pol_channels.push(channel);
                }
            }
        }

        for (pol, pol_channels) in extremal_channels.iter().enumerate() {
            if pol_channels.len() == 1 {
                let mut pruned_output_set = OutputSet::all_values(output_set.channels() - 1);
                output_set.prune_extremal_channel_into(
                    pol > 0,
                    pol_channels[0],
                    pruned_output_set.as_mut(),
                );

                pruned_output_set.canonicalize(true);

                let mut pruned_state = self.states.get(pruned_output_set.as_ref());

                loop {
                    if pruned_state.bounds[1] < state.bounds[1] {
                        state.bounds[1] = pruned_state.bounds[1];
                        state.huffman_bounds[1] = pruned_state.bounds[1];

                        self.states.set(output_set.as_ref(), state);

                        if state.bounds[0] == state.bounds[1] {
                            return state;
                        }
                    }

                    if pruned_state.bounds[0] > state.bounds[0] {
                        state.bounds[0] = pruned_state.bounds[0];
                        state.huffman_bounds[0] = pruned_state.bounds[0];

                        self.states.set(output_set.as_ref(), state);

                        return state;
                    }

                    pruned_state = self
                        .improve_boxed(pool, level, pruned_state, pruned_output_set.clone())
                        .await;
                }
            }
        }

        while state.huffman_bounds[1] > state.bounds[0] {
            let new_state = self.improve_huffman(pool, level, output_set).await;
            if new_state.bounds[0] > state.bounds[0] {
                return new_state;
            }
            state = new_state;
        }

        let mut edges = Edges::default();

        for i in 0..output_set.channels() {
            for j in 0..i {
                let mut target = output_set.to_owned();
                if target.apply_comparator([i, j]) {
                    target.canonicalize(true);

                    edges.add_edge(self, target);
                }
            }
        }

        loop {
            let combined_upper_bound =
                edges.states().map(|state| state.bounds[1]).min().unwrap() + 1;

            if combined_upper_bound < state.bounds[1] {
                state.bounds[1] = combined_upper_bound;
                if combined_upper_bound < state.huffman_bounds[1] {
                    state.huffman_bounds[1] = combined_upper_bound;
                }
                self.states.set(output_set, state);
                if state.bounds[0] == state.bounds[1] {
                    return state;
                }
            }

            let combined_lower_bound =
                edges.states().map(|state| state.bounds[0]).min().unwrap() + 1;

            if combined_lower_bound > state.bounds[0] {
                let mut state = self.states.get(output_set);
                state.bounds[0] = combined_lower_bound;
                self.states.set(output_set, state);

                return state;
            }

            edges
                .improve_next(self, pool, level + 1, Some(state.bounds[0]))
                .await;
        }
    }

    async fn improve_huffman(
        &self,
        pool: &ThreadPool<Prio>,
        level: usize,
        output_set: OutputSet<&[bool]>,
    ) -> State {
        let mut state = self.states.get(output_set);

        if state.huffman_bounds[1] <= state.bounds[0] {
            return state;
        }

        let mut extremal_channels = [CVec::new(), CVec::new()];

        for (pol, pol_channels) in extremal_channels.iter_mut().enumerate() {
            for channel in 0..output_set.channels() {
                if output_set.channel_is_extremal(pol > 0, channel) {
                    pol_channels.push(channel);
                }
            }
        }

        let mut edges = Edges::default();

        let mut pruned_ids = [vec![], vec![]];

        for (pol, (pol_channels, pol_ids)) in extremal_channels
            .iter()
            .zip(pruned_ids.iter_mut())
            .enumerate()
        {
            for &channel in pol_channels.iter() {
                let mut target = OutputSet::all_values(output_set.channels() - 1);
                output_set.prune_extremal_channel_into(pol > 0, channel, target.as_mut());
                target.canonicalize(true);

                pol_ids.push(edges.add_edge(self, target));
            }
        }

        let mut upper_huffman_bounds = [state.huffman_bounds[1], state.huffman_bounds[1]];

        while state.huffman_bounds[1] > state.bounds[0] {
            for (pol, pol_ids) in pruned_ids.iter().enumerate() {
                if upper_huffman_bounds[pol] > state.bounds[0] {
                    let lower_bounds = pol_ids
                        .iter()
                        .map(|&id| edges.state(id).bounds[0])
                        .collect::<CVec<_>>();
                    let upper_bounds = pol_ids
                        .iter()
                        .map(|&id| edges.state(id).bounds[1])
                        .collect::<CVec<_>>();

                    let lower_huffman_bound = max_plus_1_huffman(&lower_bounds);
                    let upper_huffman_bound = max_plus_1_huffman(&upper_bounds);

                    if upper_huffman_bound <= state.bounds[0] {
                        edges.retain_edges(|id| pruned_ids[1 - pol].contains(&id));
                    }

                    upper_huffman_bounds[pol] = upper_huffman_bound;

                    if lower_huffman_bound > state.huffman_bounds[0] {
                        state.huffman_bounds[0] = lower_huffman_bound;
                        if lower_huffman_bound > state.bounds[0] {
                            state.bounds[0] = lower_huffman_bound;
                            self.states.set(output_set, state);
                            return state;
                        }
                        self.states.set(output_set, state);
                    }
                }
            }

            let max_upper_huffman_bound = *upper_huffman_bounds.iter().max().unwrap();

            if max_upper_huffman_bound < state.huffman_bounds[1] {
                state.huffman_bounds[1] = max_upper_huffman_bound;
                self.states.set(output_set, state);
            }

            edges.improve_next(self, pool, level + 1, None).await;
        }

        state
    }
}

#[derive(Default)]
struct Edges {
    target_to_id: HashMap<Arc<OutputSet>, usize>,
    targets: Vec<EdgeTarget>,
    active_ids: Vec<usize>,
}

struct EdgeTarget {
    output_set: Arc<OutputSet>,
    state: State,
    len: usize,
    running: Option<(Handle<State>, Schedule)>,
}

impl Edges {
    fn add_edge(&mut self, search: &Search, target: OutputSet) -> usize {
        let target = Arc::new(target);

        let targets = &mut self.targets;
        let active_ids = &mut self.active_ids;
        match self.target_to_id.entry(target.clone()) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let id = targets.len();
                let state = search.states.get(target.as_ref().as_ref());
                let len = target.len();
                targets.push(EdgeTarget {
                    output_set: target,
                    state,
                    len,
                    running: None,
                });
                if state.bounds[0] != state.bounds[1] {
                    active_ids.push(id);
                }
                entry.insert(id);
                id
            }
        }
    }

    fn states<'a>(&'a self) -> impl Iterator<Item = State> + 'a {
        self.targets.iter().map(|target| target.state)
    }

    fn state(&self, id: usize) -> State {
        self.targets[id].state
    }

    fn retain_edges(&mut self, mut should_retain: impl FnMut(usize) -> bool) {
        let targets = &mut self.targets;
        self.active_ids.retain(move |&id| {
            let retain = should_retain(id);
            if !retain {
                targets[id].running = None;
            }
            retain
        })
    }

    #[allow(unreachable_code)]
    async fn improve_next(
        &mut self,
        search: &Search,
        pool: &ThreadPool<Prio>,
        level: usize,
        order: Option<u8>,
    ) {
        let targets = &mut self.targets;

        let mut block = false;

        loop {
            let mut finished = false;

            let mut num_running = 0;

            for &id in self.active_ids.iter() {
                let target = &mut targets[id];

                if let Some((handle, schedule)) = target.running.as_mut() {
                    if let Poll::Ready(new_state) = poll!(handle) {
                        target.state = new_state;
                        target.running = None;
                        finished = true;
                    } else if schedule.is_scheduled() {
                        num_running += 1;
                    }
                }
            }

            self.active_ids.retain(|&id| {
                let state = targets[id].state;
                let retain = state.bounds[0] != state.bounds[1];
                if !retain {
                    assert!(targets[id].running.is_none());
                }
                retain
            });

            if finished || self.active_ids.is_empty() {
                return;
            }

            if block && num_running > 0 {
                pending!();
            }

            block = true;

            if let Some(limit) = order {
                self.active_ids.sort_by_key(|&id| {
                    let target = &targets[id];

                    (
                        target.state.bounds[0] >= limit,
                        target.len,
                        target.state.bounds[0],
                        target.state.bounds[1],
                    )
                });
            } else {
                self.active_ids.sort_by_key(|&id| {
                    let target = &targets[id];

                    (target.state.bounds[0], target.len, target.state.bounds[1])
                });
            }

            for (index, &id) in self.active_ids.iter().enumerate() {
                let target = &mut targets[id];
                if target.running.is_none() {
                    block = false;
                    assert_ne!(target.state.bounds[0], target.state.bounds[1]);

                    let (handle, schedule) = pool.spawn_delayed(search.improve_boxed(
                        pool,
                        level,
                        target.state,
                        target.output_set.as_ref().clone(),
                    ));
                    if index != 0 {
                        if let Some(limit) = order {
                            if target.state.bounds[0] < limit {
                                pool.add_pending(
                                    (level, target.len, target.state.bounds[0]),
                                    &schedule,
                                );
                            }
                        }
                    }
                    target.running = Some((handle, schedule));
                }

                if index == 0 {
                    target.running.as_ref().unwrap().1.schedule();
                }
            }
        }
    }
}
