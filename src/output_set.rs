use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
    iter::repeat,
    mem::replace,
};

use arrayvec::ArrayVec;
use rustc_hash::FxHasher;

const PAIR_ABSTRACTION_GROUPS: usize = 4;

pub const MAX_CHANNELS: usize = 11;

pub type CVec<T> = ArrayVec<[T; MAX_CHANNELS]>;
pub type WVec<T> = ArrayVec<[T; MAX_CHANNELS + 1]>;

pub mod index;
pub mod packed_vec;

mod canon;
mod subsume;

#[derive(Copy, Clone, Hash, Debug)]
pub struct OutputSet<Bitmap = Vec<bool>> {
    channels: usize,
    bitmap: Bitmap,
}

impl<BitmapA, BitmapB> PartialEq<OutputSet<BitmapB>> for OutputSet<BitmapA>
where
    BitmapA: AsRef<[bool]>,
    BitmapB: AsRef<[bool]>,
{
    fn eq(&self, other: &OutputSet<BitmapB>) -> bool {
        self.bitmap() == other.bitmap()
    }
}

impl<Bitmap> Eq for OutputSet<Bitmap> where Bitmap: AsRef<[bool]> {}

impl<BitmapA, BitmapB> PartialOrd<OutputSet<BitmapB>> for OutputSet<BitmapA>
where
    BitmapA: AsRef<[bool]>,
    BitmapB: AsRef<[bool]>,
{
    fn partial_cmp(&self, other: &OutputSet<BitmapB>) -> Option<Ordering> {
        Some(self.bitmap().cmp(other.bitmap()))
    }
}

impl<Bitmap> Ord for OutputSet<Bitmap>
where
    Bitmap: AsRef<[bool]>,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl OutputSet {
    pub fn all_values(channels: usize) -> Self {
        debug_assert!(channels <= MAX_CHANNELS);
        Self {
            channels,
            bitmap: vec![true; 1 << channels],
        }
    }

    pub fn abstraction_len_for_channels(channels: usize) -> usize {
        channels.saturating_sub(1) + 1 + channels * (channels - 1) * PAIR_ABSTRACTION_GROUPS
    }
}

impl<Bitmap> OutputSet<Bitmap>
where
    Bitmap: AsRef<[bool]>,
{
    pub fn channels(&self) -> usize {
        self.channels
    }

    pub fn from_bitmap(channels: usize, bitmap: Bitmap) -> Self {
        debug_assert!(channels <= MAX_CHANNELS);
        debug_assert_eq!(bitmap.as_ref().len(), 1 << channels);
        Self { channels, bitmap }
    }

    pub fn into_bitmap(self) -> Bitmap {
        self.bitmap
    }

    pub fn bitmap(&self) -> &[bool] {
        self.bitmap.as_ref()
    }

    pub fn as_ref(&self) -> OutputSet<&[bool]> {
        OutputSet {
            channels: self.channels,
            bitmap: self.bitmap(),
        }
    }

    pub fn to_owned(&self) -> OutputSet<Vec<bool>> {
        OutputSet {
            channels: self.channels,
            bitmap: self.bitmap().to_owned(),
        }
    }

    pub fn len(&self) -> usize {
        self.bitmap().iter().map(|&present| present as usize).sum()
    }

    pub fn weight_histogram(&self) -> WVec<usize> {
        let mut histogram = repeat(0).take(self.channels + 1).collect::<WVec<_>>();

        for (index, &present) in self.bitmap().iter().enumerate() {
            histogram[index.count_ones() as usize] += present as usize;
        }

        histogram
    }

    pub fn is_sorted(&self) -> bool {
        let mut already_present: WVec<bool> =
            repeat(false).take(self.channels + 1).collect::<WVec<_>>();

        for (index, &present) in self.bitmap().iter().enumerate() {
            let weight = index.count_ones() as usize;
            if already_present[weight] & present {
                return false;
            } else {
                already_present[weight] |= present;
            }
        }

        true
    }

    pub fn is_channel_unconstrained(&self, channel: usize) -> bool {
        let bitmap = self.bitmap();
        let mask = 1 << channel;

        let mut index = mask;
        let size = bitmap.len();

        while index < size {
            if bitmap[index] != bitmap[index ^ mask] {
                return false;
            }
            index = (index + 1) | mask;
        }

        true
    }

    pub fn channel_fingerprint(&self, channel: usize) -> u64 {
        let bitmap = self.bitmap();
        let all_mask = bitmap.len() - 1;
        let mask = 1 << channel;
        let mut fingerprint = 0;
        fingerprint += bitmap[mask] as u64;
        fingerprint += bitmap[mask ^ all_mask] as u64 * 2;

        let mut index = mask;
        let size = bitmap.len();

        while index < size {
            fingerprint += bitmap[index] as u64 * 4;
            index = (index + 1) | mask;
        }

        fingerprint
    }

    pub fn low_channels_fingerprint(&self, low_channels: usize, buffer: &mut Vec<usize>) -> u64 {
        let weights = self.channels() + 1 - low_channels;
        let low_indices = 1 << low_channels;

        let low_mask = low_indices - 1;

        buffer.clear();
        buffer.resize(weights * low_indices, 0);

        for (index, &present) in self.bitmap().iter().enumerate() {
            let low_index = index & low_mask;
            let high_weight = (index & !low_mask).count_ones() as usize;
            buffer[high_weight + weights * low_index] += present as usize;
        }

        let mut hasher = FxHasher::default();
        buffer.hash(&mut hasher);
        hasher.finish()
    }

    pub fn low_channels_channel_fingerprint(
        &self,
        low_channels: usize,
        channel: usize,
        buffer: &mut Vec<usize>,
    ) -> u64 {
        debug_assert!(channel >= low_channels);

        let bitmap = self.bitmap();
        let weights = self.channels() - low_channels;
        let low_indices = 1 << low_channels;

        let mask = 1 << channel;

        let low_mask = low_indices - 1;
        let high_mask = !(low_mask | mask);

        buffer.clear();
        buffer.resize(weights * low_indices, 0);

        let mut index = mask;
        let size = bitmap.len();

        while index < size {
            let low_index = index & low_mask;
            let high_weight = (index & high_mask).count_ones() as usize;
            buffer[high_weight + weights * low_index] += bitmap[index] as usize;
            index = (index + 1) | mask;
        }

        let mut hasher = FxHasher::default();
        buffer.hash(&mut hasher);
        hasher.finish()
    }

    pub fn low_channels_channel_abstraction_len(&self, low_channels: usize) -> usize {
        let weights = self.channels() - low_channels;
        let low_indices = 1 << low_channels;
        weights * low_indices * 3
    }

    pub fn low_channels_channel_abstraction(
        &self,
        low_channels: usize,
        channel: usize,
        buffer: &mut [usize],
    ) {
        debug_assert!(channel >= low_channels);

        let bitmap = self.bitmap();

        let weights = self.channels() - low_channels;
        let low_indices = 1 << low_channels;

        let mask = 1 << channel;

        buffer.iter_mut().for_each(|value| *value = 0);

        let low_mask = low_indices - 1;
        let high_mask = !(low_mask | mask);

        let mut index = mask;
        let size = bitmap.len();

        while index < size {
            let low_index = index & low_mask;
            let high_weight = (index & high_mask).count_ones() as usize;
            let value_hi = bitmap[index];
            let value_lo = bitmap[index ^ mask];
            buffer[0 + 3 * (high_weight + weights * low_index)] += value_lo as usize;
            buffer[1 + 3 * (high_weight + weights * low_index)] += value_hi as usize;
            buffer[2 + 3 * (high_weight + weights * low_index)] += (value_lo & value_hi) as usize;
            index = (index + 1) | mask;
        }
    }

    pub fn channel_abstraction(&self, channel: usize) -> [CVec<usize>; 3] {
        let bitmap = self.bitmap();

        let weights = self.channels();
        let mut abstraction = [
            repeat(0).take(weights).collect::<CVec<_>>(),
            repeat(0).take(weights).collect::<CVec<_>>(),
            repeat(0).take(weights).collect::<CVec<_>>(),
        ];

        let mask = 1 << channel;

        let mut index = mask;
        let size = bitmap.len();

        while index < size {
            let weight = (index & !mask).count_ones() as usize;
            let value_hi = bitmap[index];
            let value_lo = bitmap[index ^ mask];
            abstraction[0][weight] += value_lo as usize;
            abstraction[1][weight] += value_hi as usize;
            abstraction[2][weight] += (value_lo & value_hi) as usize;
            index = (index + 1) | mask;
        }

        abstraction
    }

    pub fn channel_pair_abstraction(
        &self,
        channel_pair: [usize; 2],
    ) -> [usize; PAIR_ABSTRACTION_GROUPS] {
        let bitmap = self.bitmap();

        let mut abstraction = [0; PAIR_ABSTRACTION_GROUPS];

        let mask_0 = 1 << channel_pair[0];
        let mask_1 = 1 << channel_pair[1];

        let mask = mask_0 | mask_1;

        let mut index = mask;
        let size = bitmap.len();

        while index < size {
            let value_0 = bitmap[index];
            let value_1 = bitmap[index ^ mask_0];
            let value_2 = bitmap[index ^ mask_1];
            let value_3 = bitmap[index ^ mask];

            abstraction[0] += value_0 as usize;
            abstraction[1] += value_1 as usize;
            abstraction[2] += value_2 as usize;
            abstraction[3] += value_3 as usize;

            index = (index + 1) | mask;
        }

        abstraction
    }

    pub fn subsumes_unpermuted(&self, other: OutputSet<impl AsRef<[bool]>>) -> bool {
        self.bitmap()
            .iter()
            .zip(other.bitmap().iter())
            .all(|(&my_value, &other_value)| !my_value | other_value)
    }

    pub fn subsumes_permuted(&self, other: OutputSet<impl AsRef<[bool]>>) -> bool {
        subsume::Subsume::new([self.to_owned(), other.to_owned()]).search()
    }

    pub fn packed_len(&self) -> usize {
        (self.bitmap().len() + 7) / 8
    }

    pub fn pack_into_slice(&self, slice: &mut [u8]) {
        use bitvec::prelude::*;

        let bits = BitSlice::<LittleEndian, u8>::from_slice_mut(slice);

        for (index, &value) in self.bitmap().iter().enumerate() {
            bits.set(index, value);
        }
    }

    pub fn abstraction_len(&self) -> usize {
        OutputSet::abstraction_len_for_channels(self.channels())
    }

    pub fn write_abstraction_into(&self, abstraction: &mut [usize]) {
        assert_eq!(abstraction.len(), self.abstraction_len());

        let histogram = self.weight_histogram();
        let total_weight = histogram.iter().cloned().sum::<usize>();

        abstraction[0] = total_weight;

        if abstraction.len() == 1 {
            return;
        }

        abstraction[1..histogram.len() - 1].copy_from_slice(&histogram[1..histogram.len() - 1]);

        let pair_abstractions = &mut abstraction[histogram.len() - 1..];

        for channel in 0..self.channels() {
            let mut groups = <[CVec<usize>; PAIR_ABSTRACTION_GROUPS]>::default();
            for other_channel in 0..self.channels() {
                if other_channel == channel {
                    continue;
                }
                for (&abstraction_value, group_values) in self
                    .channel_pair_abstraction([channel, other_channel])
                    .iter()
                    .zip(groups.iter_mut())
                {
                    group_values.push(abstraction_value);
                }
            }
            for group_values in groups.iter_mut() {
                group_values.sort();
            }
            for (group, group_values) in groups.iter().enumerate() {
                for (index, &abstraction_value) in group_values.iter().enumerate() {
                    pair_abstractions
                        [channel + self.channels() * (group + PAIR_ABSTRACTION_GROUPS * index)] =
                        abstraction_value;
                }
            }
        }

        for chunk in pair_abstractions.chunks_mut(self.channels()) {
            chunk.sort();
        }
    }

    pub fn abstraction(&self) -> Vec<usize> {
        let mut result = vec![0; self.abstraction_len()];
        self.write_abstraction_into(&mut result);
        result
    }
}

impl<Bitmap> OutputSet<Bitmap>
where
    Bitmap: AsMut<[bool]> + AsRef<[bool]>,
{
    pub fn as_mut(&mut self) -> OutputSet<&mut [bool]> {
        OutputSet {
            channels: self.channels,
            bitmap: self.bitmap_mut(),
        }
    }

    pub fn bitmap_mut(&mut self) -> &mut [bool] {
        self.bitmap.as_mut()
    }

    pub fn apply_comparator(&mut self, channels: [usize; 2]) -> bool {
        debug_assert_ne!(channels[0], channels[1]);
        debug_assert!(channels[0] < self.channels);
        debug_assert!(channels[1] < self.channels);

        let mask_0 = 1 << channels[0];
        let mask_1 = 1 << channels[1];

        let comparator_mask = mask_0 | mask_1;

        let mut index = comparator_mask;

        let bitmap = self.bitmap_mut();

        let size = bitmap.len();

        let mut out_of_order_present = false;
        let mut in_order_present = false;

        while index < size {
            let out_of_order = replace(&mut bitmap[index ^ mask_0], false);
            out_of_order_present |= out_of_order;
            let in_order = &mut bitmap[index ^ mask_1];
            in_order_present |= *in_order;
            *in_order |= out_of_order;
            index = (index + 1) | comparator_mask;
        }

        out_of_order_present & in_order_present
    }

    pub fn swap_channels(&mut self, channels: [usize; 2]) {
        debug_assert!(channels[0] < self.channels);
        debug_assert!(channels[1] < self.channels);
        if channels[0] == channels[1] {
            return;
        }

        let mask_0 = 1 << channels[0];
        let mask_1 = 1 << channels[1];

        let comparator_mask = mask_0 | mask_1;

        let mut index = comparator_mask;

        let bitmap = self.bitmap_mut();

        let size = bitmap.len();

        while index < size {
            bitmap.swap(index ^ mask_0, index ^ mask_1);
            index = (index + 1) | comparator_mask;
        }
    }

    pub fn invert(&mut self) {
        self.bitmap_mut().reverse()
    }

    pub fn canonicalize(&mut self, inversion: bool) -> Perm {
        if self.channels() == 0 {
            return Perm::identity(0);
        }

        let mut canonicalize = canon::Canonicalize::new(self.as_mut(), inversion);

        let (result, perm) = canonicalize.canonicalize();

        self.bitmap_mut().copy_from_slice(result.bitmap());

        perm
    }

    pub fn unpack_from_slice(&mut self, slice: &[u8]) {
        use bitvec::prelude::*;

        let bits = BitSlice::<LittleEndian, u8>::from_slice(slice);

        for (index, value) in self.bitmap_mut().iter_mut().enumerate() {
            *value = bits[index];
        }
    }

    pub fn copy_from(&mut self, other: OutputSet<impl AsRef<[bool]>>) {
        self.bitmap_mut().copy_from_slice(other.bitmap())
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Perm {
    pub invert: bool,
    pub perm: CVec<usize>,
}

impl Perm {
    fn identity(channels: usize) -> Self {
        Self {
            invert: false,
            perm: (0..channels).collect(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[rustfmt::skip]
    static SORT_11: &[[usize; 2]] = &[
        [0, 9], [1, 6], [2, 4], [3, 7], [5, 8],
        [0, 1], [3, 5], [4, 10], [6, 9], [7, 8],
        [1, 3], [2, 5], [4, 7], [8, 10],
        [0, 4], [1, 2], [3, 7], [5, 9], [6, 8],
        [0, 1], [2, 6], [4, 5], [7, 8], [9, 10],
        [2, 4], [3, 6], [5, 7], [8, 9],
        [1, 2], [3, 4], [5, 6], [7, 8],
        [2, 3], [4, 5], [6, 7],
    ];

    #[test]
    fn sort_11_sorts() {
        crate::logging::setup(false);

        let mut output_set = OutputSet::all_values(11);

        for (i, &comparator) in SORT_11.iter().enumerate() {
            assert!(!output_set.is_sorted());
            output_set.apply_comparator(comparator);
            log::info!(
                "step {}: histogram = {:?}",
                i,
                output_set.weight_histogram()
            );
        }

        assert!(output_set.is_sorted());
    }

    #[test]
    fn sort_canonicalize() {
        crate::logging::setup(false);

        for &limit in &[1, 4, 8, 16, 30] {
            let mut output_set = OutputSet::all_values(11);
            for (i, &comparator) in SORT_11.iter().enumerate() {
                assert!(!output_set.is_sorted());
                output_set.apply_comparator(comparator);
                let mut canonical = output_set.clone();
                canonical.canonicalize(true);

                let mut canonical_2 = output_set.clone();

                if i & 1 != 0 {
                    canonical_2.invert();
                }

                for &pair in SORT_11[..limit].iter() {
                    canonical_2.swap_channels(pair);
                }
                canonical_2.canonicalize(true);

                assert_eq!(canonical, canonical_2);

                log::info!(
                    "step {}: histogram = {:?}",
                    i,
                    output_set.weight_histogram(),
                );
            }

            assert!(output_set.is_sorted());
        }
    }

    #[test]
    fn sort_subsume_permuted() {
        crate::logging::setup(false);

        for &limit in &[1, 4, 8, 16, 30] {
            let mut output_set = OutputSet::all_values(11);
            for (i, &comparator) in SORT_11.iter().enumerate() {
                assert!(!output_set.is_sorted());
                let previous_output_set = output_set.clone();
                output_set.apply_comparator(comparator);

                let mut permuted = output_set.clone();

                for &pair in SORT_11[..limit].iter() {
                    permuted.swap_channels(pair);
                }

                assert!(permuted.subsumes_permuted(output_set.as_ref()));
                assert!(output_set.subsumes_permuted(permuted.as_ref()));
                assert!(!previous_output_set.subsumes_permuted(permuted.as_ref()));
                let strict_progress = permuted.subsumes_permuted(previous_output_set.as_ref());

                log::info!(
                    "step {}: histogram = {:?} strict progress = {:?}",
                    i,
                    output_set.weight_histogram(),
                    strict_progress
                );
            }
            assert!(output_set.is_sorted());
        }
    }
}
