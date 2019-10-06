use std::{
    cmp::Reverse,
    collections::BinaryHeap,
    rc::Rc,
    time::{Duration, Instant},
};

use rustc_hash::FxHashMap as HashMap;

mod states;

use states::{State, StateMap};

use crate::output_set::{CVec, OutputSet};

pub struct Search {
    states: StateMap,
    counter: usize,
    last_status: Instant,
}

impl Search {
    pub fn search(initial: OutputSet<&[bool]>) -> usize {
        let mut search = Self {
            states: StateMap::default(),
            counter: 0,
            last_status: Instant::now(),
        };

        let mut initial = initial.to_owned_bvec();

        initial.canonicalize(true);

        let mut state = search.states.get(initial.as_ref());
        loop {
            if state.bounds[0] == state.bounds[1] {
                search.log_stats();
                return state.bounds[0] as usize;
            }
            state = search.improve(initial.as_ref());
            log::info!("bounds: {:?}", state);
            search.log_stats();
        }
    }

    fn log_stats(&self) {
        log::info!("states: {:?}", self.states.len());
    }

    fn improve(&mut self, output_set: OutputSet<&[bool]>) -> State {
        self.counter += 1;
        if self.counter == 100 {
            self.counter = 0;
            let interval = Duration::from_secs(10);
            if self.last_status.elapsed() > interval {
                self.log_stats();
                self.last_status += interval
            }
        }

        let mut state = self.states.get(output_set);

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
                let mut pruned_output_set = OutputSet::all_values_bvec(output_set.channels() - 1);
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

                    pruned_state = self.improve(pruned_output_set.as_ref());
                }
            }
        }

        while state.huffman_bounds[1] > state.bounds[0] {
            let new_state = self.improve_huffman(output_set);
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

            edges.improve_next(self);
        }
    }

    fn improve_huffman(&mut self, output_set: OutputSet<&[bool]>) -> State {
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
                        edges
                            .active_ids
                            .retain(|id| pruned_ids[1 - pol].contains(id));
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

            edges.improve_next(self);
        }

        state
    }
}

#[derive(Default)]
struct Edges {
    target_to_id: HashMap<Rc<OutputSet>, usize>,
    targets: Vec<(Rc<OutputSet>, State, usize)>,
    active_ids: Vec<usize>,
}

impl Edges {
    fn add_edge(&mut self, search: &Search, target: OutputSet) -> usize {
        let target = Rc::new(target);

        let targets = &mut self.targets;
        let active_ids = &mut self.active_ids;
        *self.target_to_id.entry(target.clone()).or_insert_with(|| {
            let id = targets.len();
            let state = search.states.get(target.as_ref().as_ref());
            let len = target.len();
            targets.push((target, state, len));
            if state.bounds[0] != state.bounds[1] {
                active_ids.push(id);
            }
            id
        })
    }

    fn states<'a>(&'a self) -> impl Iterator<Item = State> + 'a {
        self.targets.iter().map(|(_, state, _)| *state)
    }

    fn state(&self, id: usize) -> State {
        let (_, state, _) = self.targets[id];
        state
    }

    fn sort_key(&self, id: usize) -> (u8, usize, u8) {
        let (_, state, len) = &self.targets[id];

        (state.bounds[0], *len, state.bounds[1])
    }

    fn improve_next(&mut self, search: &mut Search) -> bool {
        for i in (1..self.active_ids.len()).rev() {
            if self.sort_key(self.active_ids[i]) < self.sort_key(self.active_ids[i - 1]) {
                self.active_ids.swap(i, i - 1);
            }
        }

        if self.active_ids.is_empty() {
            false
        } else {
            // TODO allow work stealing
            let id = self.active_ids[0];
            let (output_set, state, _len) = &mut self.targets[id];
            *state = search.improve(output_set.as_ref().as_ref());

            if state.bounds[0] == state.bounds[1] {
                self.active_ids.swap_remove(0);
            }
            true
        }
    }
}

fn max_plus_1_huffman(values: &[u8]) -> u8 {
    let mut heap: BinaryHeap<Reverse<u8>> = values.iter().map(|&v| Reverse(v)).collect();

    while let Some(Reverse(first)) = heap.pop() {
        if let Some(Reverse(second)) = heap.pop() {
            heap.push(Reverse(first.max(second) + 1));
        } else {
            return first;
        }
    }
    0
}
