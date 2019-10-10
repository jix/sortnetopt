use std::{
    collections::BTreeMap,
    hash::{Hash, Hasher},
    mem::{replace, transmute},
    sync::RwLock,
};

use arrayref::array_ref;
use futures::{
    channel::oneshot,
    future::{FutureExt, Shared},
};
use rustc_hash::FxHasher;

use crate::output_set::OutputSet;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct State {
    pub bounds: [u8; 2],
    pub huffman_bounds: [u8; 2],
}

pub struct StateMap {
    state_shards: Vec<RwLock<OutputSetMap<State>>>,
    lock_shards: Vec<RwLock<OutputSetMap<Shared<oneshot::Receiver<()>>>>>,
}

impl Default for StateMap {
    fn default() -> Self {
        let threads = num_cpus::get();
        let shards = (threads * threads * 8).next_power_of_two();

        Self {
            state_shards: (0..shards).map(|_| Default::default()).collect(),
            lock_shards: (0..shards).map(|_| Default::default()).collect(),
        }
    }
}

impl StateMap {
    pub fn len(&self) -> usize {
        self.state_shards
            .iter()
            .map(|shard| shard.read().unwrap().len())
            .sum()
    }

    pub fn get(&self, output_set: OutputSet<&[bool]>) -> State {
        let packed = output_set.packed_pvec();

        let mut hasher = FxHasher::default();
        packed.hash(&mut hasher);
        let hash = hasher.finish();
        let shard = (hash & (self.state_shards.len() - 1) as u64) as usize;

        if let Some(result) = self.state_shards[shard]
            .read()
            .unwrap()
            .get_with_packed(output_set.channels(), &packed)
        {
            result
        } else {
            if output_set.is_sorted() {
                State {
                    bounds: [0, 0],
                    huffman_bounds: [0, 0],
                }
            } else if output_set.channels() <= 2 {
                State {
                    bounds: [1, 1],
                    huffman_bounds: [1, 1],
                }
            } else {
                let quadratic_bound = (output_set.channels() * (output_set.channels() - 1)) / 2;

                let known_bounds = [0, 0, 1, 3, 5, 9, 12, 16, 19, 25, 29, 35];

                let bound = known_bounds
                    .get(output_set.channels())
                    .cloned()
                    .unwrap_or(quadratic_bound as u8);

                State {
                    bounds: [1, bound],
                    huffman_bounds: [1, bound],
                }
            }
        }
    }

    pub fn set(&self, output_set: OutputSet<&[bool]>, state: State) {
        let packed = output_set.packed_pvec();

        let mut hasher = FxHasher::default();
        packed.hash(&mut hasher);
        let hash = hasher.finish();
        let shard = (hash & (self.state_shards.len() - 1) as u64) as usize;

        self.state_shards[shard].write().unwrap().set_with_packed(
            output_set.channels(),
            &output_set.packed_pvec(),
            state,
        )
    }

    pub async fn lock<'a>(&'a self, output_set: OutputSet<&'a [bool]>) -> Option<StateLock<'a>> {
        let packed = output_set.packed();

        let mut hasher = FxHasher::default();
        packed.hash(&mut hasher);
        let hash = hasher.finish();
        let shard = (hash & (self.lock_shards.len() - 1) as u64) as usize;

        match self.get_lock(output_set, shard, &packed) {
            Ok(lock) => {
                lock.await.unwrap();
                None
            }
            Err(unlock) => Some(StateLock {
                states: self,
                unlock: Some(unlock),
                channels: output_set.channels(),
                packed,
                shard,
            }),
        }
    }

    fn get_lock<'a>(
        &'a self,
        output_set: OutputSet<&'a [bool]>,
        shard: usize,
        packed: &[u8],
    ) -> Result<Shared<oneshot::Receiver<()>>, oneshot::Sender<()>> {
        let mut shard_mut = self.lock_shards[shard].write().unwrap();

        if let Some(existing) = shard_mut.get_with_packed(output_set.channels(), &packed) {
            Ok(existing)
        } else {
            let (unlock, lock) = oneshot::channel();
            shard_mut.set_with_packed(output_set.channels(), &packed, lock.shared());
            Err(unlock)
        }
    }

    pub fn into_shards(self) -> Vec<OutputSetMap<State>> {
        self.state_shards
            .into_iter()
            .map(|shard| shard.into_inner().unwrap())
            .collect()
    }
}

pub struct StateLock<'a> {
    states: &'a StateMap,
    unlock: Option<oneshot::Sender<()>>,
    channels: usize,
    packed: Vec<u8>,
    shard: usize,
}

impl<'a> Drop for StateLock<'a> {
    fn drop(&mut self) {
        let mut shard_mut = self.states.lock_shards[self.shard].write().unwrap();

        self.unlock.take().unwrap().send(()).unwrap();
        shard_mut.remove_with_packed(self.channels, &self.packed);
    }
}

pub struct OutputSetMap<T> {
    states_3_channels: BTreeMap<[u8; 1 << 0], T>,
    states_4_channels: BTreeMap<[u8; 1 << 1], T>,
    states_5_channels: BTreeMap<[u8; 1 << 2], T>,
    states_6_channels: BTreeMap<[u8; 1 << 3], T>,
    states_7_channels: BTreeMap<[u8; 1 << 4], T>,
    states_8_channels: BTreeMap<[u8; 1 << 5], T>,
    states_9_channels: BTreeMap<[[u8; 1 << 5]; 1 << 1], T>,
    states_10_channels: BTreeMap<[[u8; 1 << 5]; 1 << 2], T>,
    states_11_channels: BTreeMap<[[u8; 1 << 5]; 1 << 3], T>,
}

impl<T> Default for OutputSetMap<T> {
    fn default() -> Self {
        Self {
            states_3_channels: Default::default(),
            states_4_channels: Default::default(),
            states_5_channels: Default::default(),
            states_6_channels: Default::default(),
            states_7_channels: Default::default(),
            states_8_channels: Default::default(),
            states_9_channels: Default::default(),
            states_10_channels: Default::default(),
            states_11_channels: Default::default(),
        }
    }
}

impl<T: Clone> OutputSetMap<T> {
    pub fn len(&self) -> usize {
        self.states_3_channels.len()
            + self.states_4_channels.len()
            + self.states_5_channels.len()
            + self.states_6_channels.len()
            + self.states_7_channels.len()
            + self.states_8_channels.len()
            + self.states_9_channels.len()
            + self.states_10_channels.len()
            + self.states_11_channels.len()
    }

    pub fn drain_packed(&mut self) -> impl Iterator<Item = (usize, Vec<u8>, T)> {
        let result = replace(&mut self.states_3_channels, Default::default())
            .into_iter()
            .map(|(packed, state)| (3, packed.as_ref().to_owned(), state))
            .chain(
                replace(&mut self.states_4_channels, Default::default())
                    .into_iter()
                    .map(|(packed, state)| (4, packed.as_ref().to_owned(), state)),
            )
            .chain(
                replace(&mut self.states_5_channels, Default::default())
                    .into_iter()
                    .map(|(packed, state)| (5, packed.as_ref().to_owned(), state)),
            )
            .chain(
                replace(&mut self.states_6_channels, Default::default())
                    .into_iter()
                    .map(|(packed, state)| (6, packed.as_ref().to_owned(), state)),
            )
            .chain(
                replace(&mut self.states_7_channels, Default::default())
                    .into_iter()
                    .map(|(packed, state)| (7, packed.as_ref().to_owned(), state)),
            )
            .chain(
                replace(&mut self.states_8_channels, Default::default())
                    .into_iter()
                    .map(|(packed, state)| (8, packed.as_ref().to_owned(), state)),
            )
            .chain(
                replace(&mut self.states_9_channels, Default::default())
                    .into_iter()
                    .map(|(packed, state)| {
                        (
                            9,
                            unsafe { transmute::<_, [u8; 1 << 6]>(packed) }
                                .as_ref()
                                .to_owned(),
                            state,
                        )
                    }),
            )
            .chain(
                replace(&mut self.states_10_channels, Default::default())
                    .into_iter()
                    .map(|(packed, state)| {
                        (
                            10,
                            unsafe { transmute::<_, [u8; 1 << 7]>(packed) }
                                .as_ref()
                                .to_owned(),
                            state,
                        )
                    }),
            )
            .chain(
                replace(&mut self.states_11_channels, Default::default())
                    .into_iter()
                    .map(|(packed, state)| {
                        (
                            11,
                            unsafe { transmute::<_, [u8; 1 << 8]>(packed) }
                                .as_ref()
                                .to_owned(),
                            state,
                        )
                    }),
            );

        // Works around vscode's broken syntax highlighting
        let _ignored: [(); 0 >> 1] = [];
        let _ignored: [(); 0 >> 1] = [];
        let _ignored: [(); 0 >> 1] = [];

        result
    }

    pub fn get_with_packed(&self, channels: usize, packed: &[u8]) -> Option<T> {
        let result = match channels {
            3 => self
                .states_3_channels
                .get(array_ref!(packed, 0, 1 << 0))
                .cloned(),
            4 => self
                .states_4_channels
                .get(array_ref!(packed, 0, 1 << 1))
                .cloned(),
            5 => self
                .states_5_channels
                .get(array_ref!(packed, 0, 1 << 2))
                .cloned(),
            6 => self
                .states_6_channels
                .get(array_ref!(packed, 0, 1 << 3))
                .cloned(),
            7 => self
                .states_7_channels
                .get(array_ref!(packed, 0, 1 << 4))
                .cloned(),
            8 => self
                .states_8_channels
                .get(array_ref!(packed, 0, 1 << 5))
                .cloned(),

            9 => self
                .states_9_channels
                .get(unsafe { &transmute::<_, [_; 1 << 1]>(*array_ref!(packed, 0, 1 << 6)) })
                .cloned(),
            10 => self
                .states_10_channels
                .get(unsafe { &transmute::<_, [_; 1 << 2]>(*array_ref!(packed, 0, 1 << 7)) })
                .cloned(),
            11 => self
                .states_11_channels
                .get(unsafe { &transmute::<_, [_; 1 << 3]>(*array_ref!(packed, 0, 1 << 8)) })
                .cloned(),
            _ => None,
        };

        // Works around vscode's broken syntax highlighting
        let _ignored: [(); 0 >> 1] = [];
        let _ignored: [(); 0 >> 1] = [];
        let _ignored: [(); 0 >> 1] = [];

        result
    }

    pub fn set_with_packed(&mut self, channels: usize, packed: &[u8], value: T) {
        assert!(channels > 2);

        match channels {
            3 => self
                .states_3_channels
                .insert(*array_ref!(packed, 0, 1 << 0), value),
            4 => self
                .states_4_channels
                .insert(*array_ref!(packed, 0, 1 << 1), value),
            5 => self
                .states_5_channels
                .insert(*array_ref!(packed, 0, 1 << 2), value),
            6 => self
                .states_6_channels
                .insert(*array_ref!(packed, 0, 1 << 3), value),
            7 => self
                .states_7_channels
                .insert(*array_ref!(packed, 0, 1 << 4), value),
            8 => self
                .states_8_channels
                .insert(*array_ref!(packed, 0, 1 << 5), value),

            9 => self.states_9_channels.insert(
                unsafe { transmute::<_, [_; 1 << 1]>(*array_ref!(packed, 0, 1 << 6)) },
                value,
            ),
            10 => self.states_10_channels.insert(
                unsafe { transmute::<_, [_; 1 << 2]>(*array_ref!(packed, 0, 1 << 7)) },
                value,
            ),
            11 => self.states_11_channels.insert(
                unsafe { transmute::<_, [_; 1 << 3]>(*array_ref!(packed, 0, 1 << 8)) },
                value,
            ),
            _ => unreachable!(),
        };

        // Works around vscode's broken syntax highlighting
        let _ignored: [(); 0 >> 1] = [];
        let _ignored: [(); 0 >> 1] = [];
        let _ignored: [(); 0 >> 1] = [];
    }

    pub fn remove_with_packed(&mut self, channels: usize, packed: &[u8]) {
        assert!(channels > 2);

        match channels {
            3 => self.states_3_channels.remove(array_ref!(packed, 0, 1 << 0)),
            4 => self.states_4_channels.remove(array_ref!(packed, 0, 1 << 1)),
            5 => self.states_5_channels.remove(array_ref!(packed, 0, 1 << 2)),
            6 => self.states_6_channels.remove(array_ref!(packed, 0, 1 << 3)),
            7 => self.states_7_channels.remove(array_ref!(packed, 0, 1 << 4)),
            8 => self.states_8_channels.remove(array_ref!(packed, 0, 1 << 5)),

            9 => self
                .states_9_channels
                .remove(unsafe { &transmute::<_, [_; 1 << 1]>(*array_ref!(packed, 0, 1 << 6)) }),
            10 => self
                .states_10_channels
                .remove(unsafe { &transmute::<_, [_; 1 << 2]>(*array_ref!(packed, 0, 1 << 7)) }),
            11 => self
                .states_11_channels
                .remove(unsafe { &transmute::<_, [_; 1 << 3]>(*array_ref!(packed, 0, 1 << 8)) }),
            _ => unreachable!(),
        };

        // Works around vscode's broken syntax highlighting
        let _ignored: [(); 0 >> 1] = [];
        let _ignored: [(); 0 >> 1] = [];
        let _ignored: [(); 0 >> 1] = [];
    }
}
