use std::iter::repeat;

use super::OutputSet;

pub struct PackedOutputSetVec {
    channels: usize,
    len: usize,
    buffer: Vec<u8>,
}

impl PackedOutputSetVec {
    pub fn new(channels: usize) -> Self {
        PackedOutputSetVec {
            channels,
            len: 0,
            buffer: vec![],
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn push(&mut self, output_set: OutputSet<&[bool]>) {
        assert_eq!(output_set.channels(), self.channels);
        let stride = self.stride();
        let offset = self.buffer.len();
        self.buffer.extend(repeat(0).take(stride));
        output_set.pack_into_slice(&mut self.buffer[offset..]);
        self.len += 1;
    }

    pub fn set(&mut self, index: usize, output_set: OutputSet<&[bool]>) {
        assert_eq!(output_set.channels(), self.channels);
        assert!(index < self.len);
        let stride = self.stride();
        let offset = stride * index;
        output_set.pack_into_slice(&mut self.buffer[offset..])
    }

    pub fn get_into(&self, index: usize, mut output_set: OutputSet<&mut [bool]>) {
        assert_eq!(output_set.channels(), self.channels);
        assert!(index < self.len);
        let stride = self.stride();
        let offset = stride * index;
        output_set.unpack_from_slice(&self.buffer[offset..])
    }

    pub fn get(&self, index: usize) -> OutputSet {
        let mut result = OutputSet::all_values(self.channels);
        self.get_into(index, result.as_mut());
        result
    }

    pub fn remove_last(&mut self) {
        if self.len > 0 {
            self.len -= 1;
            let new_len = self.buffer.len() - self.stride();
            self.buffer.truncate(new_len);
        }
    }

    pub fn swap(&mut self, a: usize, b: usize) {
        assert!(a < self.len);
        assert!(b < self.len);

        let stride = self.stride();
        let offset_a = a * stride;
        let offset_b = b * stride;

        for i in 0..stride {
            self.buffer.swap(offset_a + i, offset_b + i);
        }
    }

    fn stride(&self) -> usize {
        ((1 << self.channels) + 7) / 8
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
    fn packed_vec_ops() {
        crate::logging::setup(false);

        let mut output_set = OutputSet::all_values(11);

        let mut steps = PackedOutputSetVec::new(11);

        for &comparator in SORT_11.iter() {
            output_set.apply_comparator(comparator);
            steps.push(output_set.as_ref());
        }

        output_set = OutputSet::all_values(11);

        for (i, &comparator) in SORT_11.iter().enumerate() {
            output_set.apply_comparator(comparator);
            assert_eq!(steps.get(i), output_set);
        }

        for i in 0..SORT_11.len() / 2 {
            let j = steps.len() - 1 - i;
            steps.swap(i, j);
        }

        output_set = OutputSet::all_values(11);

        for (i, &comparator) in SORT_11.iter().enumerate() {
            output_set.apply_comparator(comparator);
            assert_eq!(steps.get(steps.len() - 1 - i), output_set);
        }
    }
}
