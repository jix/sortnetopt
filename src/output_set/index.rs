use std::{cmp::Reverse, iter::repeat, mem::replace};

use super::{BVec, CVec, OutputSet};

mod tree;

use tree::{Augmentation, TraversalMut, Tree};

pub enum Lower {}
pub enum LowerInvert {}

pub enum Upper {}

const TREE_THRESHOLD: usize = 32;

pub trait IndexDirection {
    type Perm;

    fn lookup_dir() -> bool;

    fn can_improve(best_so_far: Option<u8>, range: [u8; 2]) -> bool;
    fn does_improve(best_so_far: Option<u8>, value: u8) -> bool;

    fn can_be_updated(range: [u8; 2], value: u8) -> bool;
    fn would_be_updated(candidate_value: u8, lookup_value: u8) -> bool;

    fn test_abstraction_range(candidate_range: &[[u16; 2]], lookup: &[u16]) -> bool;

    fn test_abstraction_range_update(candidate_range: &[[u16; 2]], lookup: &[u16]) -> bool;

    fn test_abstraction(candidate: &[u16], lookup: &[u16]) -> bool;

    fn test_abstraction_update(candidate: &[u16], lookup: &[u16]) -> bool {
        Self::test_abstraction(lookup, candidate)
    }

    fn test_precise(
        candidate: OutputSet<&[bool]>,
        candidate_abstraction: &[u16],
        lookup: OutputSet<&[bool]>,
        lookup_abstraction: &[u16],
    ) -> Option<Self::Perm>;

    fn test_precise_update(
        candidate: OutputSet<&[bool]>,
        candidate_abstraction: &[u16],
        lookup: OutputSet<&[bool]>,
        lookup_abstraction: &[u16],
    ) -> bool {
        Self::test_precise(lookup, lookup_abstraction, candidate, candidate_abstraction).is_some()
    }

    fn id_perm(channels: usize) -> Self::Perm;
}

impl IndexDirection for Lower {
    type Perm = CVec<usize>;

    fn lookup_dir() -> bool {
        false
    }

    fn can_improve(best_so_far: Option<u8>, range: [u8; 2]) -> bool {
        if let Some(best_so_far) = best_so_far {
            range[1] > best_so_far
        } else {
            true
        }
    }

    fn does_improve(best_so_far: Option<u8>, value: u8) -> bool {
        if let Some(best_so_far) = best_so_far {
            value > best_so_far
        } else {
            true
        }
    }

    fn can_be_updated(range: [u8; 2], value: u8) -> bool {
        range[0] <= value
    }

    fn would_be_updated(candidate_value: u8, lookup_value: u8) -> bool {
        candidate_value <= lookup_value
    }

    fn test_abstraction_range(candidate_range: &[[u16; 2]], lookup: &[u16]) -> bool {
        candidate_range
            .iter()
            .zip(lookup.iter())
            .all(|(candidate, &lookup)| candidate[0] <= lookup)
    }

    fn test_abstraction_range_update(candidate_range: &[[u16; 2]], lookup: &[u16]) -> bool {
        candidate_range
            .iter()
            .zip(lookup.iter())
            .all(|(candidate, &lookup)| candidate[1] >= lookup)
    }

    fn test_abstraction(candidate: &[u16], lookup: &[u16]) -> bool {
        candidate
            .iter()
            .zip(lookup.iter())
            .all(|(&candidate, &lookup)| candidate <= lookup)
    }

    fn test_precise(
        candidate: OutputSet<&[bool]>,
        _candidate_abstraction: &[u16],
        lookup: OutputSet<&[bool]>,
        _lookup_abstraction: &[u16],
    ) -> Option<Self::Perm> {
        candidate.subsumes_permuted(lookup)
    }

    fn id_perm(channels: usize) -> Self::Perm {
        (0..channels).collect()
    }
}

impl IndexDirection for LowerInvert {
    type Perm = (bool, CVec<usize>);

    fn lookup_dir() -> bool {
        false
    }

    fn can_improve(best_so_far: Option<u8>, range: [u8; 2]) -> bool {
        if let Some(best_so_far) = best_so_far {
            range[1] > best_so_far
        } else {
            true
        }
    }

    fn does_improve(best_so_far: Option<u8>, value: u8) -> bool {
        if let Some(best_so_far) = best_so_far {
            value > best_so_far
        } else {
            true
        }
    }

    fn can_be_updated(range: [u8; 2], value: u8) -> bool {
        range[0] <= value
    }

    fn would_be_updated(candidate_value: u8, lookup_value: u8) -> bool {
        candidate_value <= lookup_value
    }

    fn test_abstraction_range(candidate_range: &[[u16; 2]], lookup: &[u16]) -> bool {
        (0..2).any(|invert| {
            let mask = invert * 3;
            candidate_range
                .iter()
                .enumerate()
                .all(|(i, candidate)| candidate[0] <= lookup[i ^ mask])
        })
    }

    fn test_abstraction_range_update(candidate_range: &[[u16; 2]], lookup: &[u16]) -> bool {
        (0..2).any(|invert| {
            let mask = invert * 3;
            candidate_range
                .iter()
                .enumerate()
                .all(|(i, candidate)| candidate[1] >= lookup[i ^ mask])
        })
    }

    fn test_abstraction(candidate: &[u16], lookup: &[u16]) -> bool {
        (0..2).any(|invert| {
            let mask = invert * 3;
            candidate
                .iter()
                .enumerate()
                .all(|(i, &candidate)| candidate <= lookup[i ^ mask])
        })
    }

    fn test_precise(
        candidate: OutputSet<&[bool]>,
        candidate_abstraction: &[u16],
        lookup: OutputSet<&[bool]>,
        lookup_abstraction: &[u16],
    ) -> Option<Self::Perm> {
        if Lower::test_abstraction(candidate_abstraction, lookup_abstraction) {
            if let Some(perm) = candidate.subsumes_permuted(lookup) {
                return Some((false, perm));
            }
        }
        let mut inverted = candidate.to_owned();
        inverted.invert();
        if let Some(perm) = inverted.subsumes_permuted(lookup) {
            return Some((true, perm));
        }
        None
    }

    fn id_perm(channels: usize) -> Self::Perm {
        (false, (0..channels).collect())
    }
}

impl IndexDirection for Upper {
    type Perm = CVec<usize>;

    fn lookup_dir() -> bool {
        true
    }

    fn can_improve(best_so_far: Option<u8>, range: [u8; 2]) -> bool {
        if let Some(best_so_far) = best_so_far {
            range[0] < best_so_far
        } else {
            true
        }
    }

    fn does_improve(best_so_far: Option<u8>, value: u8) -> bool {
        if let Some(best_so_far) = best_so_far {
            value < best_so_far
        } else {
            true
        }
    }

    fn can_be_updated(range: [u8; 2], value: u8) -> bool {
        range[1] >= value
    }

    fn would_be_updated(candidate_value: u8, lookup_value: u8) -> bool {
        candidate_value >= lookup_value
    }

    fn test_abstraction_range(candidate_range: &[[u16; 2]], lookup: &[u16]) -> bool {
        candidate_range
            .iter()
            .zip(lookup.iter())
            .all(|(candidate, &lookup)| candidate[1] >= lookup)
    }

    fn test_abstraction_range_update(candidate_range: &[[u16; 2]], lookup: &[u16]) -> bool {
        candidate_range
            .iter()
            .zip(lookup.iter())
            .all(|(candidate, &lookup)| candidate[0] <= lookup)
    }

    fn test_abstraction(candidate: &[u16], lookup: &[u16]) -> bool {
        candidate
            .iter()
            .zip(lookup.iter())
            .all(|(&candidate, &lookup)| candidate >= lookup)
    }

    fn test_precise(
        candidate: OutputSet<&[bool]>,
        _candidate_abstraction: &[u16],
        lookup: OutputSet<&[bool]>,
        _lookup_abstraction: &[u16],
    ) -> Option<Self::Perm> {
        lookup.subsumes_permuted(candidate)
    }

    fn id_perm(channels: usize) -> Self::Perm {
        (0..channels).collect()
    }
}

pub struct OutputSetIndex<Dir> {
    direction: std::marker::PhantomData<Dir>,
    channels: usize,
    trees: Vec<Tree>,
    point_dim: usize,
    points: Vec<u16>,
    packed_dim: usize,
    packed: Vec<u8>,
    values: Vec<u8>,
}

impl<Dir: IndexDirection> OutputSetIndex<Dir> {
    pub fn new(channels: usize) -> Self {
        Self {
            direction: std::marker::PhantomData,
            channels,
            trees: vec![],
            point_dim: OutputSet::abstraction_len_for_channels(channels),
            points: vec![],
            packed_dim: OutputSet::packed_len_for_channels(channels),
            packed: vec![],
            values: vec![],
        }
    }

    pub fn lookup_subsuming_with_abstraction(
        &self,
        output_set: OutputSet<&[bool]>,
        abstraction: &[u16],
    ) -> Option<(u8, Dir::Perm, OutputSet)> {
        let mut best_so_far = None;

        let mut bitmap = repeat(false).take(1 << self.channels).collect::<BVec<_>>();
        let mut candidate_output_set = OutputSet::from_bitmap(self.channels, &mut bitmap[..]);

        let mut node_filter = |best_so_far: &mut Option<(u8, Dir::Perm, OutputSet)>,
                               augmentation: &Augmentation,
                               ranges: &[[u16; 2]]|
         -> bool {
            Dir::can_improve(best_so_far.as_ref().map(|x| x.0), augmentation.value_range)
                && Dir::test_abstraction_range(ranges, abstraction)
        };

        let mut action = |best_so_far: &mut Option<(u8, Dir::Perm, OutputSet)>,
                          candidate_abstraction: &[u16],
                          packed_candidate: &[u8],
                          value: u8|
         -> bool {
            if !Dir::does_improve(best_so_far.as_ref().map(|x| x.0), value) {
                return true;
            }
            if !Dir::test_abstraction(candidate_abstraction, abstraction) {
                return true;
            }
            candidate_output_set.unpack_from_slice(packed_candidate);
            let perm = if candidate_output_set == output_set {
                Dir::id_perm(output_set.channels())
            } else {
                let perm = Dir::test_precise(
                    candidate_output_set.as_ref(),
                    candidate_abstraction,
                    output_set,
                    abstraction,
                );
                if let Some(perm) = perm {
                    perm
                } else {
                    return true;
                }
            };

            *best_so_far = Some((value, perm, candidate_output_set.to_owned()));

            true
        };

        for tree in self.trees.iter() {
            best_so_far = tree.traverse(
                best_so_far,
                Dir::lookup_dir(),
                &mut node_filter,
                &mut action,
            );
        }

        for (index, &value) in self.values.iter().enumerate() {
            action(
                &mut best_so_far,
                &self.points[index * self.point_dim..][..self.point_dim],
                &self.packed[index * self.packed_dim..][..self.packed_dim],
                value,
            );
        }

        best_so_far
    }

    pub fn lookup_with_abstraction(
        &self,
        output_set: OutputSet<&[bool]>,
        abstraction: &[u16],
    ) -> Option<u8> {
        let mut best_so_far = None;

        let mut bitmap = repeat(false).take(1 << self.channels).collect::<BVec<_>>();
        let mut candidate_output_set = OutputSet::from_bitmap(self.channels, &mut bitmap[..]);

        let mut node_filter = |best_so_far: &mut Option<u8>,
                               augmentation: &Augmentation,
                               ranges: &[[u16; 2]]|
         -> bool {
            Dir::can_improve(*best_so_far, augmentation.value_range)
                && Dir::test_abstraction_range(ranges, abstraction)
        };

        let mut action = |best_so_far: &mut Option<u8>,
                          candidate_abstraction: &[u16],
                          packed_candidate: &[u8],
                          value: u8|
         -> bool {
            if !Dir::does_improve(*best_so_far, value) {
                return true;
            }
            if !Dir::test_abstraction(candidate_abstraction, abstraction) {
                return true;
            }
            candidate_output_set.unpack_from_slice(packed_candidate);
            if candidate_output_set != output_set {
                if Dir::test_precise(
                    candidate_output_set.as_ref(),
                    candidate_abstraction,
                    output_set,
                    abstraction,
                )
                .is_none()
                {
                    return true;
                }
            }

            *best_so_far = Some(value);

            true
        };

        for tree in self.trees.iter() {
            best_so_far = tree.traverse(
                best_so_far,
                Dir::lookup_dir(),
                &mut node_filter,
                &mut action,
            );
        }

        for (index, &value) in self.values.iter().enumerate() {
            action(
                &mut best_so_far,
                &self.points[index * self.point_dim..][..self.point_dim],
                &self.packed[index * self.packed_dim..][..self.packed_dim],
                value,
            );
        }

        best_so_far
    }

    pub fn insert_new_unchecked_with_abstraction(
        &mut self,
        output_set: OutputSet<&[bool]>,
        abstraction: &[u16],
        value: u8,
    ) {
        let old_size = self.packed.len();
        self.packed.resize(old_size + self.packed_dim, 0);
        output_set.pack_into_slice(&mut self.packed[old_size..]);

        self.points.extend_from_slice(abstraction);
        self.values.push(value);

        if self.values.len() >= TREE_THRESHOLD {
            self.trees.sort_by_key(|tree| Reverse(tree.len()));

            while let Some(tree) = self.trees.pop() {
                if tree.len() > self.values.len() {
                    self.trees.push(tree);
                    break;
                }
                tree.traverse(
                    (),
                    Dir::lookup_dir(),
                    |_, _, _| true,
                    |_, point, packed, value| {
                        self.points.extend_from_slice(point);
                        self.packed.extend_from_slice(packed);
                        self.values.push(value);
                        true
                    },
                );
            }

            let tree = Tree::new(
                self.point_dim,
                replace(&mut self.points, vec![]),
                self.packed_dim,
                replace(&mut self.packed, vec![]),
                replace(&mut self.values, vec![]),
            );

            self.trees.push(tree);
        }
    }

    pub fn insert_with_abstraction(
        &mut self,
        output_set: OutputSet<&[bool]>,
        abstraction: &[u16],
        value: u8,
    ) -> u8 {
        let best_so_far = self.lookup_with_abstraction(output_set, abstraction);

        let mut bitmap = repeat(false).take(1 << self.channels).collect::<BVec<_>>();
        let mut candidate_output_set = OutputSet::from_bitmap(self.channels, &mut bitmap[..]);

        let mut updated_in_place = false;

        if !Dir::does_improve(best_so_far, value) {
            return best_so_far.unwrap();
        }

        let mut node_filter =
            |_: &mut (), augmentation: &Augmentation, ranges: &[[u16; 2]]| -> bool {
                Dir::can_be_updated(augmentation.value_range, value)
                    && Dir::test_abstraction_range_update(ranges, abstraction)
            };

        let mut action = |_: &mut (),
                          candidate_abstraction: &[u16],
                          packed_candidate: &[u8],
                          candidate_value: &mut u8|
         -> TraversalMut {
            if !Dir::would_be_updated(*candidate_value, value) {
                return TraversalMut::Retain;
            }
            if !Dir::test_abstraction_update(candidate_abstraction, abstraction) {
                return TraversalMut::Retain;
            }
            candidate_output_set.unpack_from_slice(packed_candidate);
            if candidate_output_set == output_set {
                assert!(!updated_in_place);
                *candidate_value = value;
                updated_in_place = true;
                return TraversalMut::Retain;
            }
            if !Dir::test_precise_update(
                candidate_output_set.as_ref(),
                candidate_abstraction,
                output_set,
                abstraction,
            ) {
                return TraversalMut::Retain;
            }

            TraversalMut::Remove
        };

        for tree in self.trees.iter_mut() {
            tree.traverse_mut((), Dir::lookup_dir(), &mut node_filter, &mut action);
        }

        self.trees.retain(|tree| !tree.is_empty());

        let mut index = 0;

        while index < self.values.len() {
            let action_result = action(
                &mut (),
                &self.points[index * self.point_dim..][..self.point_dim],
                &self.packed[index * self.packed_dim..][..self.packed_dim],
                &mut self.values[index],
            );

            if action_result == TraversalMut::Remove {
                self.values.swap_remove(index);

                if index != self.values.len() {
                    let (keep, last) = self.points.split_at_mut(self.values.len() * self.point_dim);
                    keep[index * self.point_dim..][..self.point_dim].copy_from_slice(last);

                    let (keep, last) = self
                        .packed
                        .split_at_mut(self.values.len() * self.packed_dim);
                    keep[index * self.packed_dim..][..self.packed_dim].copy_from_slice(last);
                }
                self.points.truncate(self.values.len() * self.point_dim);
                self.packed.truncate(self.values.len() * self.packed_dim);
            } else {
                index += 1;
            }
        }

        if updated_in_place {
            return value;
        }

        self.insert_new_unchecked_with_abstraction(output_set, abstraction, value);
        value
    }

    pub fn for_each(&self, mut action: impl FnMut(OutputSet<&[bool]>, &[u16], u8)) {
        let mut bitmap = repeat(false).take(1 << self.channels).collect::<BVec<_>>();
        let mut output_set = OutputSet::from_bitmap(self.channels, &mut bitmap[..]);

        let mut action = |_: &mut (), abstraction: &[u16], packed: &[u8], value: u8| -> bool {
            output_set.unpack_from_slice(packed);

            action(output_set.as_ref(), abstraction, value);
            true
        };

        for tree in self.trees.iter() {
            tree.traverse((), Dir::lookup_dir(), |_, _, _| true, &mut action);
        }

        for (index, &value) in self.values.iter().enumerate() {
            action(
                &mut (),
                &self.points[index * self.point_dim..][..self.point_dim],
                &self.packed[index * self.packed_dim..][..self.packed_dim],
                value,
            );
        }
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty() && self.trees.is_empty()
    }

    pub fn len(&self) -> usize {
        self.values.len() + self.trees.iter().map(|tree| tree.len()).sum::<usize>()
    }

    pub fn dump_dot(&self, output: &mut impl std::io::Write) -> std::io::Result<()> {
        writeln!(output, "digraph {{")?;
        for (tree_id, tree) in self.trees.iter().enumerate() {
            tree.dump_dot(tree_id, output)?;
        }
        writeln!(output, "}}")?;
        Ok(())
    }
}
