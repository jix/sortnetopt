use std::{iter::repeat, mem::replace};

use arrayvec::ArrayVec;

pub const MAX_CHANNELS: usize = 11;

pub type CVec<T> = ArrayVec<[T; MAX_CHANNELS]>;
pub type WVec<T> = ArrayVec<[T; MAX_CHANNELS + 1]>;

#[derive(Copy, Clone)]
pub struct OutputSet<Bitmap = Vec<bool>> {
    channels: usize,
    bitmap: Bitmap,
}

impl OutputSet {
    pub fn all_values(channels: usize) -> Self {
        assert!(channels <= MAX_CHANNELS);
        Self {
            channels,
            bitmap: vec![true; 1 << channels],
        }
    }
}

impl<Bitmap> OutputSet<Bitmap>
where
    Bitmap: AsRef<[bool]>,
{
    pub fn from_bitmap(channels: usize, bitmap: Bitmap) -> Self {
        assert!(channels <= MAX_CHANNELS);
        assert_eq!(bitmap.as_ref().len(), 1 << channels);
        Self { channels, bitmap }
    }

    pub fn into_bitmap(self) -> Bitmap {
        self.bitmap
    }

    pub fn bitmap(&self) -> &[bool] {
        self.bitmap.as_ref()
    }

    pub fn bitmap_mut(&mut self) -> &mut [bool]
    where
        Bitmap: AsMut<[bool]>,
    {
        self.bitmap.as_mut()
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

    pub fn apply_comparator(&mut self, channels: [usize; 2])
    where
        Bitmap: AsMut<[bool]>,
    {
        assert_ne!(channels[0], channels[1]);
        assert!(channels[0] < self.channels);
        assert!(channels[1] < self.channels);

        let mask_0 = 1 << channels[0];
        let mask_1 = 1 << channels[1];

        let comparator_mask = mask_0 | mask_1;

        let mut index = comparator_mask;

        let bitmap = self.bitmap.as_mut();

        let size = bitmap.len();

        while index < size {
            let out_of_order = replace(&mut bitmap[index ^ mask_0], false);
            bitmap[index ^ mask_1] |= out_of_order;
            index = (index + 1) | comparator_mask;
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
}
