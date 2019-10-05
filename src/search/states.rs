use std::{collections::BTreeMap, mem::transmute};

use arrayref::array_ref;

use crate::output_set::OutputSet;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct State {
    pub bounds: [u8; 2],
    pub huffman_bounds: [u8; 2],
}

#[derive(Default)]
pub struct StateMap {
    states_3_channels: BTreeMap<[u8; 1 << 0], State>,
    states_4_channels: BTreeMap<[u8; 1 << 1], State>,
    states_5_channels: BTreeMap<[u8; 1 << 2], State>,
    states_6_channels: BTreeMap<[u8; 1 << 3], State>,
    states_7_channels: BTreeMap<[u8; 1 << 4], State>,
    states_8_channels: BTreeMap<[u8; 1 << 5], State>,
    states_9_channels: BTreeMap<[[u8; 1 << 5]; 1 << 1], State>,
    states_10_channels: BTreeMap<[[u8; 1 << 5]; 1 << 2], State>,
    states_11_channels: BTreeMap<[[u8; 1 << 5]; 1 << 3], State>,
}

impl StateMap {
    pub fn len(&self) -> usize {
        self.states_3_channels.len()
            + self.states_4_channels.len()
            + self.states_5_channels.len()
            + self.states_6_channels.len()
            + self.states_7_channels.len()
            + self.states_8_channels.len()
            + self.states_9_channels.len()
            + self.states_10_channels.len()
            + self.states_11_channels.len()
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
            let lookup = match output_set.channels() {
                3 => self.states_3_channels.get(array_ref!(packed, 0, 1 << 0)),
                4 => self.states_4_channels.get(array_ref!(packed, 0, 1 << 1)),
                5 => self.states_5_channels.get(array_ref!(packed, 0, 1 << 2)),
                6 => self.states_6_channels.get(array_ref!(packed, 0, 1 << 3)),
                7 => self.states_7_channels.get(array_ref!(packed, 0, 1 << 4)),
                8 => self.states_8_channels.get(array_ref!(packed, 0, 1 << 5)),

                9 => self
                    .states_9_channels
                    .get(unsafe { &transmute::<_, [_; 1 << 1]>(*array_ref!(packed, 0, 1 << 6)) }),
                10 => self
                    .states_10_channels
                    .get(unsafe { &transmute::<_, [_; 1 << 2]>(*array_ref!(packed, 0, 1 << 7)) }),
                11 => self
                    .states_11_channels
                    .get(unsafe { &transmute::<_, [_; 1 << 3]>(*array_ref!(packed, 0, 1 << 8)) }),
                _ => unreachable!(),
            };

            // Works around vscode's broken syntax highlighting
            let _ignored: [(); 0 >> 1] = [];
            let _ignored: [(); 0 >> 1] = [];
            let _ignored: [(); 0 >> 1] = [];

            if let Some(&state) = lookup {
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
    }

    pub fn set(&mut self, output_set: OutputSet<&[bool]>, state: State) {
        assert!(output_set.channels() > 2);

        let packed = output_set.packed_pvec();

        match output_set.channels() {
            3 => self
                .states_3_channels
                .insert(*array_ref!(packed, 0, 1 << 0), state),
            4 => self
                .states_4_channels
                .insert(*array_ref!(packed, 0, 1 << 1), state),
            5 => self
                .states_5_channels
                .insert(*array_ref!(packed, 0, 1 << 2), state),
            6 => self
                .states_6_channels
                .insert(*array_ref!(packed, 0, 1 << 3), state),
            7 => self
                .states_7_channels
                .insert(*array_ref!(packed, 0, 1 << 4), state),
            8 => self
                .states_8_channels
                .insert(*array_ref!(packed, 0, 1 << 5), state),

            9 => self.states_9_channels.insert(
                unsafe { transmute::<_, [_; 1 << 1]>(*array_ref!(packed, 0, 1 << 6)) },
                state,
            ),
            10 => self.states_10_channels.insert(
                unsafe { transmute::<_, [_; 1 << 2]>(*array_ref!(packed, 0, 1 << 7)) },
                state,
            ),
            11 => self.states_11_channels.insert(
                unsafe { transmute::<_, [_; 1 << 3]>(*array_ref!(packed, 0, 1 << 8)) },
                state,
            ),
            _ => unreachable!(),
        };

        // Works around vscode's broken syntax highlighting
        let _ignored: [(); 0 >> 1] = [];
        let _ignored: [(); 0 >> 1] = [];
        let _ignored: [(); 0 >> 1] = [];
    }
}
