use std::{
    cmp::Reverse,
    collections::BinaryHeap,
    time::{Duration, Instant},
};

use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};

use crate::output_set::{
    index::{Lower, OutputSetIndex, Upper},
    AVec, BVec, CVec, OutputSet,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct State {
    bounds: [u8; 2],
    huffman_bounds: [u8; 2],
}

pub struct Search {
    states: HashMap<OutputSet<BVec<bool>>, State>,
    counter: usize,
    last_status: Instant,
}

impl Search {
    pub fn search(initial: OutputSet<&[bool]>) -> usize {
        let mut search = Self {
            states: Default::default(),
            counter: 0,
            last_status: Instant::now(),
        };

        let mut initial = initial.to_owned_bvec();

        initial.canonicalize(true);

        let mut state = search.get_state(&initial);
        loop {
            if state.bounds[0] == state.bounds[1] {
                search.log_stats();
                return state.bounds[0] as usize;
            }
            state = search.improve(&initial);
            log::info!("bounds: {:?}", state);
        }
    }

    fn log_stats(&self) {
        log::info!("states: {:?}", self.states.len());
    }

    fn get_state(&self, output_set: &OutputSet<BVec<bool>>) -> State {
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
        } else if let Some(&state) = self.states.get(output_set) {
            state
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

    fn get_state_mut(&mut self, output_set: &OutputSet<BVec<bool>>) -> &mut State {
        if self.states.contains_key(output_set) {
            self.states.get_mut(output_set).unwrap()
        } else {
            let default_state = self.get_state(output_set);
            self.states
                .entry(output_set.clone())
                .or_insert(default_state)
        }
    }

    fn improve(&mut self, output_set: &OutputSet<BVec<bool>>) -> State {
        let mut state = self.get_state(output_set);

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

                let mut pruned_state = self.get_state(&pruned_output_set);

                loop {
                    let state = self.get_state_mut(output_set);

                    if pruned_state.bounds[1] < state.bounds[1] {
                        state.bounds[1] = pruned_state.bounds[1];
                        state.huffman_bounds[1] = pruned_state.bounds[1];

                        if state.bounds[0] == state.bounds[1] {
                            return *state;
                        }
                    }

                    if pruned_state.bounds[0] > state.bounds[0] {
                        state.bounds[0] = pruned_state.bounds[0];
                        state.huffman_bounds[0] = pruned_state.bounds[0];
                        return *state;
                    }

                    pruned_state = self.improve(&pruned_output_set);
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
                let mut successor = output_set.to_owned_bvec();
                if successor.apply_comparator([i, j]) {
                    successor.canonicalize(false);
                    successors.push(successor);
                }
            }
        }

        successors.sort_unstable();
        successors.dedup();

        loop {
            successors.sort_by_cached_key(|successor| {
                let successor_state = self.get_state(successor);
                (successor_state.bounds[0], successor.len())
            });

            let successor_combined_upper_bound = successors
                .iter()
                .map(|successor| {
                    let successor_state = self.get_state(successor);
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
                *self.get_state_mut(output_set) = state;
                if state.bounds[0] == state.bounds[1] {
                    return state;
                }
            }

            let successor_combined_lower_bound = successors
                .iter()
                .map(|successor| {
                    let successor_state = self.get_state(successor);
                    successor_state.bounds[0]
                })
                .min()
                .unwrap()
                + 1;

            if successor_combined_lower_bound > state.bounds[0] {
                let state = self.get_state_mut(output_set);
                state.bounds[0] = successor_combined_lower_bound;

                return *state;
            }

            for successor in successors.iter() {
                let mut successor_state = self.get_state(successor);
                let mut explored = false;
                while successor_state.bounds[0] != successor_state.bounds[1]
                    && successor_state.bounds[0] + 1 <= state.bounds[0]
                {
                    successor_state = self.improve(successor);
                    explored = true;
                }

                if explored {
                    break;
                }
            }
        }
    }

    fn improve_huffman(&mut self, output_set: &OutputSet<BVec<bool>>) -> State {
        let mut state = self.get_state(output_set);

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
                let mut pruned_output_set = OutputSet::all_values_bvec(output_set.channels() - 1);
                output_set.prune_extremal_channel_into(
                    pol > 0,
                    channel,
                    pruned_output_set.as_mut(),
                );
                pruned_output_set.canonicalize(true);

                pol_output_sets.push((
                    self.get_state(&pruned_output_set),
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
                            *self.get_state_mut(output_set) = state;
                            return state;
                        }
                        *self.get_state_mut(output_set) = state;
                    }
                }
            }

            state.huffman_bounds[1] = *upper_huffman_bounds.iter().max().unwrap();
            *self.get_state_mut(output_set) = state;

            if let Some((cached_pruned_state, _len, pruned_output_set)) = pruned_output_sets
                .iter_mut()
                .zip(upper_huffman_bounds.iter())
                .filter(|(_, upper_bound)| **upper_bound > state.bounds[0])
                .flat_map(|(pol_output_sets, _)| pol_output_sets.iter_mut())
                .filter(|(pruned_state, _, _)| pruned_state.bounds[0] != pruned_state.bounds[1])
                .min_by_key(|(pruned_state, len, _)| (pruned_state.bounds[0], *len))
            {
                let pruned_state = self.get_state(pruned_output_set);
                if pruned_state != *cached_pruned_state {
                    *cached_pruned_state = pruned_state;
                } else {
                    *cached_pruned_state = self.improve(pruned_output_set);
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
