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
pub const MAX_BITMAP_SIZE: usize = 1 << MAX_CHANNELS;
pub const MAX_PACKED_SIZE: usize = 1 << (MAX_CHANNELS - 3);
pub const MAX_ABSTRACTION_SIZE: usize = MAX_CHANNELS * (MAX_CHANNELS - 1) * PAIR_ABSTRACTION_GROUPS;

pub type CVec<T> = ArrayVec<[T; MAX_CHANNELS]>;
pub type WVec<T> = ArrayVec<[T; MAX_CHANNELS + 1]>;
pub type BVec<T> = ArrayVec<[T; MAX_BITMAP_SIZE]>;
pub type PVec<T> = ArrayVec<[T; MAX_PACKED_SIZE]>;
pub type AVec<T> = ArrayVec<[T; 512]>;

pub mod index;

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

    pub fn all_values_bvec(channels: usize) -> OutputSet<BVec<bool>> {
        debug_assert!(channels <= MAX_CHANNELS);
        OutputSet {
            channels,
            bitmap: repeat(true).take(1 << channels).collect(),
        }
    }

    pub fn packed_len_for_channels(channels: usize) -> usize {
        ((1 << channels) + 7) / 8
    }

    pub fn abstraction_len_for_channels(channels: usize) -> usize {
        channels * (channels - 1) * PAIR_ABSTRACTION_GROUPS
    }

    pub fn from_packed(channels: usize, packed: &[u8]) -> Self {
        let mut result = Self::all_values(channels);
        result.unpack_from_slice(packed);
        result
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

    pub fn to_owned_bvec(&self) -> OutputSet<BVec<bool>> {
        let mut bitmap = BVec::new();
        bitmap.try_extend_from_slice(self.bitmap()).unwrap();
        OutputSet {
            channels: self.channels,
            bitmap,
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
        if self.channels() < 2 {
            return true;
        }

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

    pub fn subsumes_permuted(&self, other: OutputSet<impl AsRef<[bool]>>) -> Option<CVec<usize>> {
        subsume::Subsume::new([self.to_owned(), other.to_owned()]).search()
    }

    pub fn packed_len(&self) -> usize {
        (self.bitmap().len() + 7) / 8
    }

    pub fn pack_into_slice(&self, slice: &mut [u8]) {
        let bitmap = self.bitmap();

        let mut byte_chunks = bitmap.chunks_exact(8);
        let mut target_bytes = slice.iter_mut();

        for (byte_chunk, target_byte) in (&mut byte_chunks).zip(&mut target_bytes) {
            unsafe {
                *target_byte = (*byte_chunk.get_unchecked(0) as u8)
                    | ((*byte_chunk.get_unchecked(1) as u8) << 1)
                    | ((*byte_chunk.get_unchecked(2) as u8) << 2)
                    | ((*byte_chunk.get_unchecked(3) as u8) << 3)
                    | ((*byte_chunk.get_unchecked(4) as u8) << 4)
                    | ((*byte_chunk.get_unchecked(5) as u8) << 5)
                    | ((*byte_chunk.get_unchecked(6) as u8) << 6)
                    | ((*byte_chunk.get_unchecked(7) as u8) << 7);
            }
        }

        let remainder = byte_chunks.remainder();
        if !remainder.is_empty() {
            let target_byte = target_bytes.next().unwrap();
            *target_byte = (remainder.get(0).cloned().unwrap_or(false) as u8)
                | ((remainder.get(1).cloned().unwrap_or(false) as u8) << 1)
                | ((remainder.get(2).cloned().unwrap_or(false) as u8) << 2)
                | ((remainder.get(3).cloned().unwrap_or(false) as u8) << 3)
                | ((remainder.get(4).cloned().unwrap_or(false) as u8) << 4)
                | ((remainder.get(5).cloned().unwrap_or(false) as u8) << 5)
                | ((remainder.get(6).cloned().unwrap_or(false) as u8) << 6)
                | ((remainder.get(7).cloned().unwrap_or(false) as u8) << 7);
        }
    }

    pub fn packed_pvec(&self) -> PVec<u8> {
        let mut result = repeat(0).take(self.packed_len()).collect::<PVec<_>>();

        self.pack_into_slice(&mut result[..]);

        result
    }

    pub fn packed(&self) -> Vec<u8> {
        let mut result = repeat(0).take(self.packed_len()).collect::<Vec<_>>();

        self.pack_into_slice(&mut result[..]);

        result
    }

    pub fn abstraction_len(&self) -> usize {
        OutputSet::abstraction_len_for_channels(self.channels())
    }

    pub fn write_abstraction_into(&self, abstraction: &mut [u16]) {
        assert_eq!(abstraction.len(), self.abstraction_len());

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
                group_values.sort_unstable_by(|a, b| b.cmp(a));
            }
            for (group, group_values) in groups.iter().enumerate() {
                for (index, &abstraction_value) in group_values.iter().enumerate() {
                    abstraction
                        [channel + self.channels() * (group + PAIR_ABSTRACTION_GROUPS * index)] =
                        abstraction_value as u16;
                }
            }
        }

        for chunk in abstraction.chunks_mut(self.channels()) {
            chunk.sort_unstable();
        }

        for chunk in abstraction.chunks_mut(self.channels() * 4) {
            let mut tmp = ArrayVec::<[u16; 64]>::new();
            tmp.try_extend_from_slice(chunk).unwrap();

            for i in 0..4 {
                for j in 0..self.channels() {
                    chunk[i + j * 4] = tmp[j + i * self.channels()];
                }
            }
        }
    }

    pub fn abstraction(&self) -> AVec<u16> {
        let mut result = repeat(0).take(self.abstraction_len()).collect::<AVec<_>>();

        self.write_abstraction_into(&mut result[..]);

        result
    }

    pub fn channel_is_extremal(&self, polarity: bool, channel: usize) -> bool {
        let bitmap = self.bitmap();
        let all_mask = bitmap.len() - 1;
        let mask = 1 << channel;
        let index = mask ^ (all_mask * polarity as usize);

        bitmap[index]
    }

    pub fn prune_extremal_channel_into(
        &self,
        polarity: bool,
        channel: usize,
        mut target: OutputSet<&mut [bool]>,
    ) {
        assert_eq!(target.channels() + 1, self.channels());

        let target_bitmap = target.bitmap_mut();

        for value in target_bitmap.iter_mut() {
            *value = false;
        }

        let mut queue = BVec::<u16>::new();

        let bitmap = self.bitmap();
        let all_mask = bitmap.len() - 1;
        let mask = 1 << channel;
        let flip = all_mask * polarity as usize;
        let index = mask ^ flip;

        assert!(bitmap[index]);

        let new_all_mask = all_mask >> 1;

        let mask_low = mask - 1;
        let mask_high = new_all_mask ^ mask_low;

        let new_flip = new_all_mask * polarity as usize;

        queue.push(mask as u16);
        target_bitmap[new_flip] = true;

        while let Some(index) = queue.pop() {
            let index = index as usize;
            let mut bit = 1;
            for _ in 0..self.channels() {
                let next = index | bit;

                let next_target = ((next & mask_low) | ((next >> 1) & mask_high)) ^ new_flip;

                if bitmap[next ^ flip] & !target_bitmap[next_target] {
                    target_bitmap[next_target] = true;
                    queue.push(next as u16);
                }

                bit <<= 1;
            }
        }
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
        let bitmap = self.bitmap_mut();

        let mut byte_chunks = bitmap.chunks_exact_mut(8);
        let mut source_bytes = slice.iter();

        for (byte_chunk, source_byte) in (&mut byte_chunks).zip(&mut source_bytes) {
            unsafe {
                *byte_chunk.get_unchecked_mut(0) = source_byte & (1 << 0) != 0;
                *byte_chunk.get_unchecked_mut(1) = source_byte & (1 << 1) != 0;
                *byte_chunk.get_unchecked_mut(2) = source_byte & (1 << 2) != 0;
                *byte_chunk.get_unchecked_mut(3) = source_byte & (1 << 3) != 0;
                *byte_chunk.get_unchecked_mut(4) = source_byte & (1 << 4) != 0;
                *byte_chunk.get_unchecked_mut(5) = source_byte & (1 << 5) != 0;
                *byte_chunk.get_unchecked_mut(6) = source_byte & (1 << 6) != 0;
                *byte_chunk.get_unchecked_mut(7) = source_byte & (1 << 7) != 0;
            }
        }

        let remainder = byte_chunks.into_remainder();
        if !remainder.is_empty() {
            let source_byte = source_bytes.next().unwrap();
            for (i, target_bit) in remainder.iter_mut().enumerate() {
                *target_bit = source_byte & (1 << i) != 0
            }
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
    fn sort_11_pack_unpack() {
        crate::logging::setup(false);

        let mut output_set = OutputSet::all_values(11);

        for (i, &comparator) in SORT_11.iter().enumerate() {
            assert!(!output_set.is_sorted());
            output_set.apply_comparator(comparator);
            let unpacked = OutputSet::from_packed(11, &output_set.packed());
            assert_eq!(output_set, unpacked);

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

                assert!(permuted.subsumes_permuted(output_set.as_ref()).is_some());
                assert!(output_set.subsumes_permuted(permuted.as_ref()).is_some());
                assert!(previous_output_set
                    .subsumes_permuted(permuted.as_ref())
                    .is_none());
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

    #[test]
    fn prune_extremal_channel() {
        let mut output_set_large = OutputSet::all_values(11);
        let mut output_set_small = OutputSet::all_values(10);
        let mut output_set_ref = OutputSet::all_values(10);

        output_set_large.prune_extremal_channel_into(false, 0, output_set_small.as_mut());
        assert_eq!(output_set_small, output_set_ref);

        output_set_large.apply_comparator([0, 1]);
        output_set_large.prune_extremal_channel_into(false, 0, output_set_small.as_mut());
        assert_eq!(output_set_small, output_set_ref);

        output_set_large.apply_comparator([2, 3]);
        output_set_ref.apply_comparator([1, 2]);
        output_set_large.prune_extremal_channel_into(false, 0, output_set_small.as_mut());
        assert_eq!(output_set_small, output_set_ref);

        let mut output_set_large = OutputSet::all_values(11);
        let mut output_set_small = OutputSet::all_values(10);
        let mut output_set_ref = OutputSet::all_values(10);

        output_set_large.prune_extremal_channel_into(true, 1, output_set_small.as_mut());
        assert_eq!(output_set_small, output_set_ref);

        output_set_large.apply_comparator([0, 1]);
        output_set_large.prune_extremal_channel_into(true, 1, output_set_small.as_mut());
        assert_eq!(output_set_small, output_set_ref);

        output_set_large.apply_comparator([2, 3]);
        output_set_ref.apply_comparator([1, 2]);
        output_set_large.prune_extremal_channel_into(true, 1, output_set_small.as_mut());
        assert_eq!(output_set_small, output_set_ref);
    }
}
