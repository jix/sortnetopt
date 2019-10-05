use arrayref::array_ref;

use crate::{dense_map::DenseMap, output_set::OutputSet};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct State {
    pub bounds: [u8; 2],
    pub huffman_bounds: [u8; 2],
}

impl State {
    pub fn encode(&self) -> [u8; 4] {
        [
            self.bounds[0],
            self.bounds[1],
            self.huffman_bounds[0],
            self.huffman_bounds[1],
        ]
    }

    pub fn decode(encoded: &[u8; 4]) -> Self {
        Self {
            bounds: *array_ref!(encoded, 0, 2),
            huffman_bounds: *array_ref!(encoded, 2, 2),
        }
    }
}

pub struct StateMap {
    by_channels: Vec<DenseMap>,
}

impl StateMap {
    pub fn new(max_channels: usize) -> Self {
        Self {
            by_channels: (3..=max_channels)
                .map(|channels| DenseMap::new(OutputSet::packed_len_for_channels(channels), 4))
                .collect(),
        }
    }

    pub fn len(&self) -> usize {
        self.by_channels
            .iter()
            .map(|by_channels| by_channels.len())
            .sum()
    }

    pub fn get(&self, output_set: OutputSet<&[bool]>) -> State {
        self.get_with_packed(output_set, &output_set.packed_pvec())
    }

    pub fn get_with_packed(&self, output_set: OutputSet<&[bool]>, packed: &[u8]) -> State {
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
        } else {
            if let Some(encoded) = self.by_channels[output_set.channels() - 3].get(&packed) {
                State::decode(array_ref![encoded, 0, 4])
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
    }

    pub fn set(&mut self, output_set: OutputSet<&[bool]>, state: State) {
        assert!(output_set.channels() > 2);
        let packed = output_set.packed_pvec();
        let encoded = state.encode();

        self.by_channels[output_set.channels() - 3]
            .get_mut_or_insert(&packed, &encoded)
            .copy_from_slice(&encoded);
    }
}
