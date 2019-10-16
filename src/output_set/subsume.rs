use std::{iter::repeat, mem::replace};

use super::{CVec, OutputSet, MAX_CHANNELS};

#[derive(Copy, Clone)]
enum UndoAction {
    Matching {
        channels: [usize; 2],
    },
    Swap {
        target_channel: usize,
        source_channels: [usize; 2],
    },
}

pub struct Subsume {
    channels: usize,
    output_sets: [OutputSet; 2],
    perms: [CVec<usize>; 2],
    matching: [CVec<u16>; 2],
    undo_stack: Vec<UndoAction>,
    fixed_channels: usize,
    buffer: Vec<usize>,
}

impl Subsume {
    pub fn new(output_sets: [OutputSet; 2]) -> Self {
        assert_eq!(output_sets[0].channels(), output_sets[1].channels());
        let channels = output_sets[0].channels();
        let identity_perm = (0..channels).collect::<CVec<_>>();
        let all_mask = (1 << channels) - 1;
        let full_matching = repeat(all_mask).take(channels).collect::<CVec<_>>();
        Self {
            channels,
            output_sets,
            perms: [identity_perm.clone(), identity_perm],
            matching: [full_matching.clone(), full_matching],
            undo_stack: vec![],
            fixed_channels: 0,
            buffer: vec![],
        }
    }

    pub fn search(&mut self) -> Option<CVec<usize>> {
        loop {
            loop {
                if self.fixed_channels == self.channels {
                    if self.output_sets[0].subsumes_unpermuted(self.output_sets[1].as_ref()) {
                        let mut perm = (0..self.channels).collect::<CVec<_>>();

                        for i in 0..self.channels {
                            perm[self.perms[1][i]] = self.perms[0][i];
                        }

                        return Some(perm);
                    } else {
                        return None;
                    }
                }
                if !self.filter_matching() {
                    return None;
                }
                if !self.move_unique() {
                    break;
                }
            }

            let guess = self.select_guess();

            let stack_depth = self.undo_stack.len();
            let fixed_channels = self.fixed_channels;

            if self.isolate_matching(guess) {
                self.move_unique();
                let result = self.search();
                if result.is_some() {
                    self.rollback(stack_depth, fixed_channels);
                    return result;
                }
            }

            self.rollback(stack_depth, fixed_channels);

            if !self.remove_matching(guess) {
                return None;
            }
            self.move_unique();
        }
    }

    fn rollback(&mut self, depth: usize, fixed_channels: usize) {
        self.fixed_channels = fixed_channels;
        for action in self.undo_stack.drain(depth..).rev() {
            match action {
                UndoAction::Matching { channels } => {
                    for side in 0..2 {
                        let side_a = side;
                        let side_b = 1 - side;
                        let channel_a = channels[side_a];
                        let channel_b = channels[side_b];
                        self.matching[side_a][channel_a] |= 1 << channel_b;
                        self.matching[side_b][channel_b] |= 1 << channel_a;
                    }
                }
                UndoAction::Swap {
                    target_channel,
                    source_channels,
                } => {
                    for (&source_channel, (output_set, perm)) in source_channels
                        .iter()
                        .zip(self.output_sets.iter_mut().zip(self.perms.iter_mut()))
                    {
                        output_set.swap_channels([target_channel, source_channel]);
                        perm.swap(target_channel, source_channel);
                    }
                }
            }
        }
    }

    fn get_matching(&self, channels: [usize; 2]) -> bool {
        self.matching[0][channels[0]] & (1 << channels[1]) != 0
    }

    fn remove_matching(&mut self, channels: [usize; 2]) -> bool {
        debug_assert!(self.get_matching(channels));

        for side in 0..2 {
            let mask = self.matching[side][channels[side]];
            if mask & (mask - 1) == 0 {
                return false;
            }
        }

        self.undo_stack.push(UndoAction::Matching { channels });

        for side in 0..2 {
            self.matching[side][channels[side]] &= !(1 << channels[1 - side]);
        }

        for side in 0..2 {
            let mask = self.matching[side][channels[side]];
            if mask & (mask - 1) == 0 {
                let other_channel = mask.trailing_zeros() as usize;

                loop {
                    let other_mask =
                        self.matching[1 - side][other_channel] & !(1 << channels[side]);
                    if other_mask == 0 {
                        break;
                    }

                    let mut channels_rec = [0, 0];
                    channels_rec[1 - side] = other_channel;

                    let target_channel = other_mask.trailing_zeros() as usize;
                    channels_rec[side] = target_channel;

                    if !self.remove_matching(channels_rec) {
                        return false;
                    }
                }
            }
        }

        true
    }

    fn isolate_matching(&mut self, channels: [usize; 2]) -> bool {
        loop {
            let other_mask = self.matching[1][channels[1]] & !(1 << channels[0]);
            if other_mask == 0 {
                break;
            }
            let target_channel = other_mask.trailing_zeros() as usize;

            if !self.remove_matching([target_channel, channels[1]]) {
                return false;
            }
        }
        true
    }

    fn select_guess(&self) -> [usize; 2] {
        let mut min_choice = (MAX_CHANNELS + 1, 0, 0);

        for side in 0..2 {
            for channel in self.fixed_channels..self.channels {
                let matching_channel = self.perms[side][channel];
                let weight = self.matching[side][matching_channel].count_ones() as usize;
                let choice = (weight, side, matching_channel);
                min_choice = min_choice.min(choice);
            }
        }

        let (_weight, min_side, min_matching_channel) = min_choice;

        let mut min_other_choice = (MAX_CHANNELS + 1, 0);

        let mut mask = self.matching[min_side][min_matching_channel];

        while mask != 0 {
            let matching_channel = mask.trailing_zeros() as usize;
            mask &= mask - 1;
            let weight = self.matching[1 - min_side][matching_channel].count_ones() as usize;
            let other_choice = (weight, matching_channel);
            min_other_choice = min_other_choice.min(other_choice);
        }

        let (_weight, min_other_matching_channel) = min_other_choice;

        let mut result = [0, 0];
        result[min_side] = min_matching_channel;
        result[1 - min_side] = min_other_matching_channel;

        result
    }

    fn filter_matching(&mut self) -> bool {
        let abstraction_len =
            self.output_sets[0].low_channels_channel_abstraction_len(self.fixed_channels);

        self.buffer.resize(
            abstraction_len * (self.channels - self.fixed_channels) * 2,
            0,
        );

        let mut buffer_vec = replace(&mut self.buffer, vec![]);
        let mut buffer = &mut buffer_vec[..];

        let mut abstraction_buffers = [CVec::new(), CVec::new()];

        for (side, buffers) in abstraction_buffers.iter_mut().enumerate() {
            for channel in self.fixed_channels..self.channels {
                let (current_buffer, buffer_rest) = buffer.split_at_mut(abstraction_len);

                self.output_sets[side].low_channels_channel_abstraction(
                    self.fixed_channels,
                    channel,
                    current_buffer,
                );

                buffer = buffer_rest;
                buffers.push(current_buffer);
            }
        }

        let mut result = true;

        'outer: for (channel_lo, buffer_lo) in
            (self.fixed_channels..self.channels).zip(abstraction_buffers[0].iter())
        {
            let matching_channel_lo = self.perms[0][channel_lo];

            for (channel_hi, buffer_hi) in
                (self.fixed_channels..self.channels).zip(abstraction_buffers[1].iter())
            {
                let matching_channel_hi = self.perms[1][channel_hi];
                if self.get_matching([matching_channel_lo, matching_channel_hi]) {
                    if buffer_lo
                        .iter()
                        .zip(buffer_hi.iter())
                        .any(|(&lo, &hi)| lo > hi)
                    {
                        if !self.remove_matching([matching_channel_lo, matching_channel_hi]) {
                            result = false;
                            break 'outer;
                        }
                    }
                }
            }
        }

        drop(abstraction_buffers);

        self.buffer = buffer_vec;
        result
    }

    fn move_unique(&mut self) -> bool {
        let mut moved = false;

        for channel_lo in self.fixed_channels..self.channels {
            let matching_channel_lo = self.perms[0][channel_lo];
            let mask = self.matching[0][matching_channel_lo];
            if mask & (mask - 1) == 0 {
                let matching_channel_hi = mask.trailing_zeros() as usize;
                let channel_hi = self.perms[1]
                    .iter()
                    .position(|&matching_channel| matching_channel == matching_channel_hi)
                    .unwrap();

                self.undo_stack.push(UndoAction::Swap {
                    target_channel: self.fixed_channels,
                    source_channels: [channel_lo, channel_hi],
                });

                for (side, &channel) in [channel_lo, channel_hi].iter().enumerate() {
                    self.output_sets[side].swap_channels([self.fixed_channels, channel]);
                    self.perms[side].swap(self.fixed_channels, channel);
                }

                self.fixed_channels += 1;
                moved = true;
            }
        }
        moved
    }
}
