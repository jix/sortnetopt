use std::{
    convert::TryFrom,
    fmt::Debug,
    ops::{Bound, RangeBounds},
};

use arrayref::array_mut_ref;

const SCALE: usize = 8;
const MASK: usize = SCALE - 1;

pub trait IndexableValue: Copy + Ord + TryFrom<u64> + Into<u64> + Default + Debug {
    fn max_value() -> Self;
}

impl IndexableValue for u8 {
    fn max_value() -> Self {
        u8::max_value()
    }
}

impl IndexableValue for u16 {
    fn max_value() -> Self {
        u16::max_value()
    }
}

impl IndexableValue for u32 {
    fn max_value() -> Self {
        u32::max_value()
    }
}

impl IndexableValue for u64 {
    fn max_value() -> Self {
        u64::max_value()
    }
}

#[derive(Default, Debug, Clone)]
pub struct IndexedVec<T: IndexableValue> {
    values: Vec<T>,
    range_indexes: Vec<Vec<[T; 2]>>,
}

impl<T: IndexableValue> IndexedVec<T> {
    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn get(&self, index: usize) -> u64 {
        self.values[index].into()
    }

    pub fn set(&mut self, index: usize, value: u64) {
        let value = T::try_from(value).ok().expect("value out of range");

        self.values[index] = value;
        self.reindex(index);
    }

    pub fn swap(&mut self, a: usize, b: usize) {
        self.values.swap(a, b);
        self.reindex(a);
        self.reindex(b);
    }

    pub fn swap_remove(&mut self, a: usize) {
        self.values.swap_remove(a);
        if a < self.values.len() {
            self.reindex(a);
        }

        if self.values.len() > 0 {
            self.reindex(self.values.len() - 1);
        }
    }

    fn reindex(&mut self, index: usize) {
        if self.range_indexes.is_empty() {
            return;
        }

        let mut range_index_index = index / SCALE;

        let mut sub_slice = &self.values[index & !MASK..];
        sub_slice = &sub_slice[..SCALE.min(sub_slice.len())];

        self.range_indexes[0][range_index_index] = [
            sub_slice.iter().cloned().min().unwrap(),
            sub_slice.iter().cloned().max().unwrap(),
        ];

        for i in 0..self.range_indexes.len() - 1 {
            let range_index_from_index = range_index_index & !MASK;
            range_index_index /= SCALE;
            let [range_index_from, range_index_to] = array_mut_ref!(self.range_indexes, i, 2);

            let mut sub_slice = &range_index_from[range_index_from_index..];
            sub_slice = &sub_slice[..SCALE.min(sub_slice.len())];

            let min = sub_slice.iter().map(|&[min, _]| min).min().unwrap();
            let max = sub_slice.iter().map(|&[_, max]| max).max().unwrap();

            range_index_to[range_index_index] = [min, max];
        }
    }

    pub fn push(&mut self, value: u64) {
        let value = T::try_from(value).ok().expect("value out of storage range");

        let index = self.values.len();
        self.values.push(value);

        self.resize_index();
        self.reindex(index);
    }

    pub fn pop(&mut self) -> Option<u64> {
        let value = self.values.pop()?.into();

        self.resize_index();

        if self.values.len() > 0 {
            self.reindex(self.values.len() - 1);
        }

        Some(value)
    }

    fn resize_index(&mut self) {
        if self.values.len() < 2 {
            self.range_indexes.clear();
            return;
        }

        let mut index_len = (self.values.len() + MASK) / SCALE;

        if self.range_indexes.is_empty() {
            self.range_indexes.push(vec![]);
        }

        self.range_indexes[0].resize(index_len, Default::default());

        let mut index_level = 1;

        while index_len > 1 {
            index_len = (index_len + MASK) / SCALE;
            if self.range_indexes.len() == index_level {
                self.range_indexes.push(vec![]);
            }
            self.range_indexes[index_level].resize(index_len, Default::default());

            index_level += 1;
        }

        self.range_indexes.truncate(index_level);
    }

    pub fn find_value_in_range(&self, start: usize, range: impl RangeBounds<u64>) -> Option<usize> {
        if start >= self.values.len() {
            return None;
        }

        let low = match range.start_bound() {
            Bound::Unbounded => T::default(),
            Bound::Excluded(&value) if value >= T::max_value().into() => return None,
            Bound::Included(&value) if value > T::max_value().into() => return None,
            Bound::Excluded(&value) => T::try_from(value + 1).ok().unwrap(),
            Bound::Included(&value) => T::try_from(value).ok().unwrap(),
        };
        let high = match range.end_bound() {
            Bound::Unbounded => T::max_value(),
            Bound::Excluded(&value) if value <= low.into() => return None,
            Bound::Included(&value) if value < low.into() => return None,
            Bound::Excluded(&value) if value > T::max_value().into() => T::max_value(),
            Bound::Included(&value) if value >= T::max_value().into() => T::max_value(),
            Bound::Excluded(&value) => T::try_from(value - 1).ok().unwrap(),
            Bound::Included(&value) => T::try_from(value).ok().unwrap(),
        };

        self.find_value_in_range_internal(start, [low, high])
    }

    fn find_value_in_range_internal(&self, start: usize, [low, high]: [T; 2]) -> Option<usize> {
        let mut index = start;

        loop {
            if (low..=high).contains(&self.values[index]) {
                return Some(index);
            }
            index += 1;
            if index == self.values.len() {
                return None;
            } else if index & MASK == 0 {
                break;
            }
        }

        let mut index_level = 0;
        let mut range_index_index = index / SCALE;

        'outer: loop {
            loop {
                let [min, max] = self.range_indexes[index_level][range_index_index];
                if !(max < low || min > high) {
                    break 'outer;
                }
                range_index_index += 1;
                if range_index_index == self.range_indexes[index_level].len() {
                    return None;
                } else if range_index_index & MASK == 0 {
                    break;
                }
            }
            index_level += 1;
            range_index_index /= SCALE;
        }

        range_index_index *= SCALE;

        while index_level > 0 {
            loop {
                let [min, max] = self.range_indexes[index_level - 1][range_index_index];
                if !(max < low || min > high) {
                    break;
                }
                range_index_index += 1;
            }
            index_level -= 1;
            range_index_index *= SCALE;
        }

        index = range_index_index;

        loop {
            if (low..=high).contains(&self.values[index]) {
                return Some(index);
            }
            index += 1;
        }
    }

    #[cfg(test)]
    fn check_index(&self) {
        if self.values.len() < 2 {
            assert!(self.range_indexes.is_empty());
            return;
        }

        let mut index_len = (self.values.len() + MASK) / SCALE;

        assert_eq!(self.range_indexes[0].len(), index_len);

        for (i, &[min, max]) in self.range_indexes[0].iter().enumerate() {
            let mut sub_slice = &self.values[i * SCALE..];
            sub_slice = &sub_slice[..SCALE.min(sub_slice.len())];

            assert_eq!(sub_slice.iter().cloned().min(), Some(min));
            assert_eq!(sub_slice.iter().cloned().max(), Some(max));
        }

        let mut index_level = 1;

        while index_len > 1 {
            index_len = (index_len + MASK) / SCALE;
            assert_eq!(self.range_indexes[index_level].len(), index_len);

            for (i, &[min, max]) in self.range_indexes[index_level].iter().enumerate() {
                let mut sub_slice = &self.range_indexes[index_level - 1][i * SCALE..];
                sub_slice = &sub_slice[..SCALE.min(sub_slice.len())];

                assert_eq!(sub_slice.iter().map(|&[min, _]| min).min(), Some(min));
                assert_eq!(sub_slice.iter().map(|&[_, max]| max).max(), Some(max));
            }

            index_level += 1;
        }

        assert_eq!(self.range_indexes.len(), index_level);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn push_pop_many_values() {
        crate::logging::setup(false);
        let mut indexed_vec = IndexedVec::<u16>::default();
        let mut ref_vec = vec![];

        for i in 0..1024 {
            indexed_vec.push((101 * i) % 1024);
            ref_vec.push((101 * i) % 1024);
            indexed_vec.check_index();
        }

        for i in 0..1024 {
            let value = (101 * i) % 1024;
            assert_eq!(
                indexed_vec.find_value_in_range(0, value..=value),
                Some(i as usize)
            );
            for j in 0..1024 {
                assert_eq!(
                    indexed_vec.find_value_in_range(i as usize, j..1024),
                    ref_vec[i as usize..]
                        .iter()
                        .position(|value| (j..1024).contains(value))
                        .map(|offset| offset + i as usize)
                );
                assert_eq!(
                    indexed_vec.find_value_in_range(i as usize, 0..j),
                    ref_vec[i as usize..]
                        .iter()
                        .position(|value| (0..j).contains(value))
                        .map(|offset| offset + i as usize)
                );
            }
        }

        for i in (0..1024).rev() {
            assert_eq!(indexed_vec.pop(), Some((101 * i) % 1024));
            indexed_vec.check_index();
        }

        assert_eq!(indexed_vec.pop(), None);
    }
}
