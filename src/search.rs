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

pub struct Search {
    indexes: Vec<(OutputSetIndex<Lower>, OutputSetIndex<Upper>)>,
    counter: usize,
    last_status: Instant,
}

impl Search {
    pub fn search(initial: OutputSet<&[bool]>) -> usize {
        let mut search = Self {
            indexes: (3..=initial.channels())
                .map(|channels| ((OutputSetIndex::new(channels), OutputSetIndex::new(channels))))
                .collect(),
            counter: 0,
            last_status: Instant::now(),
        };

        let abstraction = initial.abstraction();

        let mut bounds = search.get_bounds(initial, &abstraction);

        while bounds[0] != bounds[1] {
            search.improve(initial, &abstraction, &mut bounds);
            log::info!("bounds: {:?}", bounds);
        }

        search.log_stats();

        bounds[0] as usize
    }

    fn log_stats(&self) {
        let stats = self
            .indexes
            .iter()
            .enumerate()
            .map(|(channels, (lower, upper))| (channels + 3, lower.len(), upper.len()))
            .collect::<Vec<_>>();
        log::info!("index sizes: {:?}", stats);
    }

    fn get_bounds(&self, output_set: OutputSet<&[bool]>, abstraction: &[u16]) -> [u8; 2] {
        if output_set.is_sorted() {
            return [0, 0];
        }

        if output_set.channels() == 2 {
            return [1, 1];
        }

        let (lower_index, upper_index) = &self.indexes[output_set.channels() - 3];

        let lower_bound = lower_index
            .lookup_with_abstraction(output_set, abstraction)
            .unwrap_or(1);

        let upper_bound = upper_index
            .lookup_with_abstraction(output_set, abstraction)
            .unwrap_or_else(|| ((output_set.channels() * (output_set.channels() - 1)) / 2) as u8);

        [lower_bound, upper_bound]
    }

    fn update_bounds(
        &mut self,
        output_set: OutputSet<&[bool]>,
        abstraction: &[u16],
        bounds: &mut [u8; 2],
        new_bounds: [u8; 2],
    ) -> bool {
        self.counter += 1;
        if self.counter == 100 {
            self.counter = 0;
            let interval = Duration::from_secs(10);
            if self.last_status.elapsed() > interval {
                self.log_stats();
                self.last_status += interval
            }
        }

        if output_set.channels() == 2 {
            return false;
        }

        let (lower_index, upper_index) = &mut self.indexes[output_set.channels() - 3];

        let mut improved = false;

        if new_bounds[0] > bounds[0] {
            improved = true;
            bounds[0] = lower_index.insert_with_abstraction(output_set, abstraction, new_bounds[0]);
        }

        if new_bounds[1] < bounds[1] {
            improved = true;
            bounds[1] = upper_index.insert_with_abstraction(output_set, abstraction, new_bounds[1]);
        }

        assert!(bounds[0] <= bounds[1]);

        improved
    }

    fn improve(
        &mut self,
        output_set: OutputSet<&[bool]>,
        abstraction: &[u16],
        bounds: &mut [u8; 2],
    ) {
        assert!(output_set.channels() >= 2);
        let mut pruned_output_set = OutputSet::all_values_bvec(output_set.channels() - 1);

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
                output_set.prune_extremal_channel_into(
                    pol > 0,
                    pol_channels[0],
                    pruned_output_set.as_mut(),
                );

                pruned_output_set.canonicalize(false);

                let pruned_abstraction = pruned_output_set.abstraction();

                let mut pruned_bounds =
                    self.get_bounds(pruned_output_set.as_ref(), &pruned_abstraction);

                while !self.update_bounds(output_set, abstraction, bounds, pruned_bounds) {
                    self.improve(
                        pruned_output_set.as_ref(),
                        &pruned_abstraction,
                        &mut pruned_bounds,
                    );
                }

                return;
            }
        }

        let mut pruned_set_ids = HashMap::<OutputSet<BVec<bool>>, usize>::default();

        struct PrunedSet {
            output_set: OutputSet<BVec<bool>>,
            abstraction: AVec<u16>,
            bounds: [u8; 2],
            pol: [bool; 2],
        }

        let mut pruned_sets: Vec<PrunedSet> = vec![];

        let mut pruned_by_pol = [vec![], vec![]];

        for (pol, pol_channels) in extremal_channels.iter().enumerate() {
            for &channel in pol_channels.iter() {
                output_set.prune_extremal_channel_into(
                    pol > 0,
                    channel,
                    pruned_output_set.as_mut(),
                );

                pruned_output_set.canonicalize(false);

                if let Some(&pruned_set_id) = pruned_set_ids.get(&pruned_output_set) {
                    pruned_by_pol[pol].push(pruned_set_id);
                    pruned_sets[pruned_set_id].pol[pol] = true;
                } else {
                    let pruned_set_id = pruned_sets.len();
                    pruned_set_ids.insert(pruned_output_set.clone(), pruned_set_id);

                    let pruned_abstraction = pruned_output_set.abstraction();
                    let pruned_bounds =
                        self.get_bounds(pruned_output_set.as_ref(), &pruned_abstraction);

                    pruned_sets.push(PrunedSet {
                        output_set: pruned_output_set.clone(),
                        abstraction: pruned_abstraction,
                        bounds: pruned_bounds,
                        pol: [pol == 0, pol == 1],
                    });
                    pruned_by_pol[pol].push(pruned_set_id);
                }
            }
        }

        let mut max_huffman_lower_bound = 0;

        for pruned_ids in pruned_by_pol.iter() {
            let lower_bounds = pruned_ids
                .iter()
                .map(|&pruned_id| pruned_sets[pruned_id].bounds[0])
                .collect::<CVec<_>>();
            max_huffman_lower_bound =
                max_huffman_lower_bound.max(max_plus_1_huffman(&lower_bounds[..]));
        }

        if self.update_bounds(
            output_set,
            abstraction,
            bounds,
            [max_huffman_lower_bound, bounds[1]],
        ) {
            return;
        }

        let mut active_pruned_ids = HashSet::<usize>::default();

        let mut active_pols = [true; 2];

        for (pol, pruned_ids) in pruned_by_pol.iter().enumerate() {
            let upper_bounds = pruned_ids
                .iter()
                .map(|&pruned_id| pruned_sets[pruned_id].bounds[1])
                .collect::<CVec<_>>();

            let huffman_upper_bound = max_plus_1_huffman(&upper_bounds[..]);

            if huffman_upper_bound > bounds[0] {
                active_pruned_ids.extend(&pruned_ids[..]);
            } else {
                active_pols[pol] = false;
            }
        }

        let mut active_pruned_heap = active_pruned_ids
            .into_iter()
            .filter(|&pruned_id| {
                pruned_sets[pruned_id].bounds[0] != pruned_sets[pruned_id].bounds[1]
            })
            .map(|pruned_id| Reverse((pruned_sets[pruned_id].bounds[0], pruned_id)))
            .collect::<BinaryHeap<_>>();

        while let Some(Reverse((_, pruned_id))) = active_pruned_heap.pop() {
            let pruned_set = &mut pruned_sets[pruned_id];

            if !pruned_set
                .pol
                .iter()
                .zip(active_pols.iter())
                .any(|(pol, active)| pol & active)
            {
                continue;
            }

            self.improve(
                pruned_set.output_set.as_ref(),
                &pruned_set.abstraction,
                &mut pruned_set.bounds,
            );

            if pruned_set.bounds[0] != pruned_set.bounds[1] {
                active_pruned_heap.push(Reverse((pruned_set.bounds[0], pruned_id)));
            }

            let mut max_huffman_lower_bound = 0;

            for (pol, pruned_ids) in pruned_by_pol.iter().enumerate() {
                let lower_bounds = pruned_ids
                    .iter()
                    .map(|&pruned_id| pruned_sets[pruned_id].bounds[0])
                    .collect::<CVec<_>>();
                let upper_bounds = pruned_ids
                    .iter()
                    .map(|&pruned_id| pruned_sets[pruned_id].bounds[1])
                    .collect::<CVec<_>>();
                max_huffman_lower_bound =
                    max_huffman_lower_bound.max(max_plus_1_huffman(&lower_bounds[..]));

                let huffman_upper_bound = max_plus_1_huffman(&upper_bounds[..]);

                if huffman_upper_bound <= bounds[0] {
                    active_pols[pol] = false;
                }
            }

            if self.update_bounds(
                output_set,
                abstraction,
                bounds,
                [max_huffman_lower_bound, bounds[1]],
            ) {
                return;
            }
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

        let mut successors_data = vec![];

        let mut min_lower_bound = bounds[1] - 1;

        for successor in successors {
            let successor_abstraction = successor.abstraction();
            let successor_bounds = self.get_bounds(successor.as_ref(), &successor_abstraction);

            if self.update_bounds(
                output_set,
                abstraction,
                bounds,
                [0, successor_bounds[1] + 1],
            ) {
                return;
            }

            min_lower_bound = min_lower_bound.min(successor_bounds[0]);

            successors_data.push((successor, successor_abstraction, successor_bounds));
        }

        if self.update_bounds(
            output_set,
            abstraction,
            bounds,
            [min_lower_bound + 1, bounds[1]],
        ) {
            return;
        }

        successors_data.sort_by_cached_key(|(successor, _, successor_bounds)| {
            (successor.len(), *successor_bounds)
        });

        let mut min_lower_bound = bounds[1] - 1;

        for (successor, successor_abstraction, successor_bounds) in successors_data.iter_mut() {
            while successor_bounds[0] + 1 <= bounds[0] {
                self.improve(successor.as_ref(), successor_abstraction, successor_bounds);

                if self.update_bounds(
                    output_set,
                    abstraction,
                    bounds,
                    [0, successor_bounds[1] + 1],
                ) {
                    return;
                }
            }

            min_lower_bound = min_lower_bound.min(successor_bounds[0]);
        }

        assert!(self.update_bounds(
            output_set,
            abstraction,
            bounds,
            [min_lower_bound + 1, bounds[1]]
        ))
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
