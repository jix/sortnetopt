use std::{
    cmp::Reverse,
    collections::BinaryHeap,
    time::{Duration, Instant},
};

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

        let mut successors = vec![];

        for i in 0..output_set.channels() {
            for j in 0..i {
                let mut successor = output_set.to_owned();
                if successor.apply_comparator([i, j]) {
                    successor.canonicalize(true);
                    successors.push(successor);
                }
            }
        }

        successors.sort_unstable();
        successors.dedup();

        loop {
            successors.sort_by_cached_key(|successor| {
                let successor_state = self.states.get(successor.as_ref());
                (successor_state.bounds[0], successor.len())
            });

            let successor_combined_upper_bound = successors
                .iter()
                .map(|successor| {
                    let successor_state = self.states.get(successor.as_ref());
                    successor_state.bounds[1]
                })
                .min()
                .unwrap()
                + 1;

            if successor_combined_upper_bound < state.bounds[1] {
                state.bounds[1] = successor_combined_upper_bound;
                if successor_combined_upper_bound < state.huffman_bounds[1] {
                    state.huffman_bounds[1] = successor_combined_upper_bound;
                }
                self.states.set(output_set, state);
                if state.bounds[0] == state.bounds[1] {
                    return state;
                }
            }

            let successor_combined_lower_bound = successors
                .iter()
                .map(|successor| {
                    let successor_state = self.states.get(successor.as_ref());
                    successor_state.bounds[0]
                })
                .min()
                .unwrap()
                + 1;

            if successor_combined_lower_bound > state.bounds[0] {
                let mut state = self.states.get(output_set);
                state.bounds[0] = successor_combined_lower_bound;
                self.states.set(output_set, state);

                return state;
            }

            for successor in successors.iter() {
                let mut successor_state = self.states.get(successor.as_ref());
                let mut explored = false;
                while successor_state.bounds[0] != successor_state.bounds[1]
                    && successor_state.bounds[0] + 1 <= state.bounds[0]
                {
                    successor_state = self.improve(successor.as_ref());
                    explored = true;
                }

                if explored {
                    break;
                }
            }
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

        let mut pruned_output_sets = [vec![], vec![]];

        for (pol, (pol_channels, pol_output_sets)) in extremal_channels
            .iter()
            .zip(pruned_output_sets.iter_mut())
            .enumerate()
        {
            for &channel in pol_channels.iter() {
                let mut pruned_output_set = OutputSet::all_values(output_set.channels() - 1);
                output_set.prune_extremal_channel_into(
                    pol > 0,
                    channel,
                    pruned_output_set.as_mut(),
                );
                pruned_output_set.canonicalize(true);

                pol_output_sets.push((
                    self.states.get(pruned_output_set.as_ref()),
                    pruned_output_set.len(),
                    pruned_output_set,
                ));
            }
        }

        let mut upper_huffman_bounds = [state.huffman_bounds[1], state.huffman_bounds[1]];

        while state.huffman_bounds[1] > state.bounds[0] {
            for (pol, pol_output_sets) in pruned_output_sets.iter().enumerate() {
                if upper_huffman_bounds[pol] > state.bounds[0] {
                    let lower_bounds = pol_output_sets
                        .iter()
                        .map(|(pruned_state, _, _)| pruned_state.bounds[0])
                        .collect::<CVec<_>>();
                    let upper_bounds = pol_output_sets
                        .iter()
                        .map(|(pruned_state, _, _)| pruned_state.bounds[1])
                        .collect::<CVec<_>>();

                    let lower_huffman_bound = max_plus_1_huffman(&lower_bounds);
                    let upper_huffman_bound = max_plus_1_huffman(&upper_bounds);

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

            if let Some((cached_pruned_state, _len, pruned_output_set)) = pruned_output_sets
                .iter_mut()
                .zip(upper_huffman_bounds.iter())
                .filter(|(_, upper_bound)| **upper_bound > state.bounds[0])
                .flat_map(|(pol_output_sets, _)| pol_output_sets.iter_mut())
                .filter(|(pruned_state, _, _)| pruned_state.bounds[0] != pruned_state.bounds[1])
                .min_by_key(|(pruned_state, len, _)| (pruned_state.bounds[0], *len))
            {
                let pruned_state = self.states.get(pruned_output_set.as_ref());
                if pruned_state != *cached_pruned_state {
                    *cached_pruned_state = pruned_state;
                } else {
                    *cached_pruned_state = self.improve(pruned_output_set.as_ref());
                }
            } else {
                break;
            }
        }

        state
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
