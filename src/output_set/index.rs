use std::{
    hash::{BuildHasherDefault, Hash, Hasher},
    iter::repeat,
    mem::replace,
    ops::Range,
};

use hashbrown::{hash_map::RawEntryMut, HashMap};
use rustc_hash::FxHasher;

use self::indexed_vec::IndexedVec;
use super::{packed_vec::PackedOutputSetVec, OutputSet};

pub mod indexed_vec;

struct ExternHash<T> {
    value: T,
    hash: u64,
}

impl<T> Hash for ExternHash<T> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        hasher.write_u64(self.hash)
    }
}

#[derive(Default)]
struct ExternHasher(u64);

impl Hasher for ExternHasher {
    fn write(&mut self, _bytes: &[u8]) {
        panic!("only write_u64 is supported")
    }

    fn write_u64(&mut self, hash: u64) {
        self.0 = hash;
    }

    fn finish(&self) -> u64 {
        self.0
    }
}

pub trait OutputSetIndexValue {
    fn filter_len() -> usize;

    fn filter(&self, filters: &mut [usize]);
}

impl OutputSetIndexValue for () {
    fn filter_len() -> usize {
        0
    }

    fn filter(&self, _filters: &mut [usize]) {}
}

impl OutputSetIndexValue for usize {
    fn filter_len() -> usize {
        1
    }

    fn filter(&self, filters: &mut [usize]) {
        filters[0] = *self
    }
}

pub struct OutputSetIndex<T> {
    output_sets: PackedOutputSetVec,
    lookup: HashMap<ExternHash<usize>, (), BuildHasherDefault<ExternHasher>>,
    values: Vec<T>,
    filters: Vec<IndexedVec<u16>>,
    byte_buffer: Vec<u8>,
    usize_buffer: Vec<usize>,
}

impl<T: OutputSetIndexValue> OutputSetIndex<T> {
    pub fn new(channels: usize) -> Self {
        assert!(channels >= 2);

        Self {
            output_sets: PackedOutputSetVec::new(channels),
            lookup: Default::default(),
            values: vec![],
            filters: repeat(IndexedVec::<u16>::default())
                .take(OutputSet::abstraction_len_for_channels(channels) + T::filter_len())
                .collect(),
            byte_buffer: vec![],
            usize_buffer: vec![],
        }
    }

    pub fn len(&self) -> usize {
        self.output_sets.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn insert(&mut self, output_set: OutputSet<&[bool]>, value: T) -> Option<T> {
        self.byte_buffer.resize(output_set.packed_len(), 0);
        output_set.pack_into_slice(&mut self.byte_buffer);

        let mut hasher = FxHasher::default();
        self.byte_buffer.hash(&mut hasher);
        let hash = hasher.finish();

        let (output_sets, byte_buffer) = (&self.output_sets, &self.byte_buffer);

        match self.lookup.raw_entry_mut().from_hash(hash, |entry| {
            entry.hash == hash && output_sets.get_packed(entry.value) == byte_buffer.as_slice()
        }) {
            RawEntryMut::Occupied(entry) => {
                let index = entry.key().value;

                self.usize_buffer.resize(T::filter_len(), 0);
                value.filter(&mut self.usize_buffer);

                for (filter, &abstraction_value) in
                    self.filters.iter_mut().zip(self.usize_buffer.iter())
                {
                    filter.set(index, abstraction_value as u64)
                }

                Some(replace(&mut self.values[index], value))
            }
            RawEntryMut::Vacant(entry) => {
                let index = self.output_sets.len();
                self.output_sets.push_packed(&self.byte_buffer);

                let abstraction_len = output_set.abstraction_len();

                self.usize_buffer
                    .resize(abstraction_len + T::filter_len(), 0);
                output_set.write_abstraction_into(&mut self.usize_buffer[T::filter_len()..]);
                value.filter(&mut self.usize_buffer[..T::filter_len()]);

                for (filter, &abstraction_value) in
                    self.filters.iter_mut().zip(self.usize_buffer.iter())
                {
                    filter.push(abstraction_value as u64)
                }

                self.values.push(value);

                entry.insert_hashed_nocheck(hash, ExternHash { value: index, hash }, ());
                None
            }
        }
    }

    pub fn packed_lookup_id(&self, packed: &[u8]) -> Option<usize> {
        let mut hasher = FxHasher::default();
        packed.hash(&mut hasher);
        let hash = hasher.finish();

        let output_sets = &self.output_sets;

        match self.lookup.raw_entry().from_hash(hash, |entry| {
            entry.hash == hash && output_sets.get_packed(entry.value) == packed
        }) {
            Some((key, _value)) => Some(key.value),
            None => None,
        }
    }

    pub fn lookup_id(&self, output_set: OutputSet<&[bool]>) -> Option<usize> {
        let mut buffer = vec![0; output_set.packed_len()];
        output_set.pack_into_slice(&mut buffer);
        self.packed_lookup_id(&buffer)
    }

    pub fn remove_by_id(&mut self, id: usize) -> T {
        let value = self.values.swap_remove(id);
        for filter in self.filters.iter_mut() {
            filter.swap_remove(id);
        }

        let last_id = self.output_sets.len() - 1;

        if id != last_id {
            let packed_last = self.output_sets.get_packed(last_id);
            self.byte_buffer.clear();
            self.byte_buffer.extend_from_slice(packed_last);

            let mut hasher = FxHasher::default();
            packed_last.hash(&mut hasher);
            let hash = hasher.finish();

            let output_sets = &self.output_sets;

            match self.lookup.raw_entry_mut().from_hash(hash, |entry| {
                entry.hash == hash && output_sets.get_packed(entry.value) == packed_last
            }) {
                RawEntryMut::Occupied(mut entry) => entry.key_mut().value = id,
                _ => unreachable!(),
            }
        }

        let packed = self.output_sets.get_packed(id);
        let mut hasher = FxHasher::default();
        packed.hash(&mut hasher);
        let hash = hasher.finish();

        let output_sets = &self.output_sets;

        match self.lookup.raw_entry_mut().from_hash(hash, |entry| {
            entry.hash == hash && output_sets.get_packed(entry.value) == packed
        }) {
            RawEntryMut::Occupied(entry) => entry.remove(),
            _ => unreachable!(),
        }

        if id != last_id {
            self.output_sets.set_packed(id, &self.byte_buffer);
        }
        self.output_sets.remove_last();

        value
    }

    pub fn get_packed_by_id(&self, id: usize) -> &[u8] {
        self.output_sets.get_packed(id)
    }

    pub fn get_value_by_id(&self, id: usize) -> &T {
        &self.values[id]
    }

    fn scan_ids(&self, filter_ranges: &[Range<usize>], action: &mut impl FnMut(usize) -> bool) {
        let mut offset = 0;
        let mut counter = 0;
        let mut filter_index = 0;
        loop {
            let filter_range = &filter_ranges[filter_index];
            if let Some(next_offset) = self.filters[filter_index]
                .find_value_in_range(offset, filter_range.start as u64..filter_range.end as u64)
            {
                if next_offset == offset {
                    counter += 1;
                    if counter == filter_ranges.len() {
                        if !action(offset) {
                            return;
                        }
                        counter = 0;
                        offset += 1;
                    }
                } else {
                    offset = next_offset;
                    counter = 1;
                }
            } else {
                return;
            }
            filter_index += 1;
            if filter_index == filter_ranges.len() {
                filter_index = 0;
            }
        }
    }

    pub fn scan_subsumption(
        &self,
        subsuming: bool,
        output_set: OutputSet<&[bool]>,
        filter: &[Range<usize>],
        strict: bool,
        action: &mut impl FnMut(usize, OutputSet<&[bool]>, &T) -> bool,
    ) -> (usize, usize) {
        assert_eq!(output_set.channels(), self.output_sets.channels());
        assert_eq!(filter.len(), T::filter_len());

        let mut filter_ranges = Vec::with_capacity(output_set.abstraction_len() + T::filter_len());
        filter_ranges.extend_from_slice(filter);

        if subsuming {
            filter_ranges.extend(
                output_set
                    .abstraction()
                    .into_iter()
                    .map(|value| 0..value + 1),
            );

            if strict {
                filter_ranges[T::filter_len()].end -= 1;
            }
        } else {
            filter_ranges.extend(
                output_set
                    .abstraction()
                    .into_iter()
                    .map(|value| value..usize::max_value()),
            );

            if strict {
                filter_ranges[T::filter_len()].start += 1;
            }
        }

        let mut candidate = OutputSet::all_values(output_set.channels());

        let mut scan_hits = 0;
        let mut exact_hits = 0;

        self.scan_ids(&filter_ranges, &mut |id| {
            scan_hits += 1;
            self.output_sets.get_into(id, candidate.as_mut());
            let exact_test = if subsuming {
                candidate.subsumes_permuted(output_set)
            } else {
                output_set.subsumes_permuted(candidate.as_ref())
            };
            if exact_test {
                exact_hits += 1;
                action(id, candidate.as_ref(), &self.values[id])
            } else {
                true
            }
        });

        (scan_hits, exact_hits)
    }

    pub fn scan_subsuming(
        &self,
        output_set: OutputSet<&[bool]>,
        filter: &[Range<usize>],
        strict: bool,
        action: &mut impl FnMut(usize, OutputSet<&[bool]>, &T) -> bool,
    ) -> (usize, usize) {
        self.scan_subsumption(true, output_set, filter, strict, action)
    }

    pub fn scan_subsumed(
        &self,
        output_set: OutputSet<&[bool]>,
        filter: &[Range<usize>],
        strict: bool,
        action: &mut impl FnMut(usize, OutputSet<&[bool]>, &T) -> bool,
    ) -> (usize, usize) {
        self.scan_subsumption(false, output_set, filter, strict, action)
    }

    pub fn for_each(&self, action: &mut impl FnMut(usize, OutputSet<&[bool]>, &T) -> bool) {
        let mut output_set = OutputSet::all_values(self.output_sets.channels());

        for (id, value) in self.values.iter().enumerate() {
            self.output_sets.get_into(id, output_set.as_mut());
            if !action(id, output_set.as_ref(), value) {
                break;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn repeated_insert() {
        crate::logging::setup(false);
        let mut index = OutputSetIndex::<usize>::new(11);

        let output_set_0 = OutputSet::all_values(11);
        let mut output_set_1 = OutputSet::all_values(11);
        let mut output_set_2 = OutputSet::all_values(11);

        output_set_1.apply_comparator([0, 1]);
        output_set_2.apply_comparator([2, 3]);
        output_set_2.apply_comparator([4, 5]);

        assert_eq!(index.insert(output_set_0.as_ref(), 0), None);
        assert_eq!(index.insert(output_set_1.as_ref(), 1), None);
        assert_eq!(index.insert(output_set_1.as_ref(), 2), Some(1));
        assert_eq!(index.insert(output_set_1.as_ref(), 3), Some(2));
        assert_eq!(index.insert(output_set_0.as_ref(), 4), Some(0));
        assert_eq!(index.insert(output_set_1.as_ref(), 5), Some(3));
        assert_eq!(index.insert(output_set_2.as_ref(), 6), None);
        assert_eq!(index.insert(output_set_0.as_ref(), 7), Some(4));
        assert_eq!(index.insert(output_set_0.as_ref(), 8), Some(7));
    }
}
