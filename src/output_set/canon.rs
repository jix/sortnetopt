use std::{
    cmp::Reverse,
    mem::{replace, swap},
};

use super::{CVec, OutputSet, Perm};

#[derive(Clone)]
struct CandidateData {
    perm: Perm,
    fingerprint: CVec<u64>,
    partition: CVec<(u16, u16)>,
    partition_score: (usize, usize),
}

impl CandidateData {
    pub fn score(&self) -> (usize, usize, &[u64]) {
        (
            self.partition_score.0,
            self.partition_score.1,
            self.fingerprint.as_ref(),
        )
    }

    pub fn sort_partition(&mut self) {
        self.partition
            .sort_unstable_by_key(|&(part_mask, part_id)| {
                (Reverse(part_mask.count_ones()), part_id, part_mask)
            });

        let singleton_count = self
            .partition
            .iter()
            .rev()
            .take_while(|&(part_mask, _)| part_mask & (part_mask - 1) == 0)
            .count();

        let max_partition_size = self.partition[0].0.count_ones() as usize;

        self.partition_score = (singleton_count, !max_partition_size);
    }
}

pub struct Canonicalize {
    bitmap_len: usize,
    channels: usize,
    used_channels: usize,
    bitmaps: Vec<bool>,
    data: Vec<CandidateData>,
    free_list: Vec<usize>,
    layer: Vec<usize>,
    next_layer: Vec<usize>,
    fixed: usize,
    buffer: Vec<usize>,
    temp: OutputSet,
}

macro_rules! get_mut {
    ($s:ident, $i:expr) => {
        match $i {
            index => OutputSet::from_bitmap(
                $s.channels,
                &mut $s.bitmaps[index * $s.bitmap_len..(index + 1) * $s.bitmap_len],
            ),
        }
    };
}

macro_rules! get {
    ($s:ident, $i:expr) => {
        match $i {
            index => OutputSet::from_bitmap(
                $s.channels,
                &$s.bitmaps[index * $s.bitmap_len..(index + 1) * $s.bitmap_len],
            ),
        }
    };
}

macro_rules! reborrow {
    ($s:ident) => {{
        struct Reborrow<'a> {
            bitmaps: &'a [bool],
            channels: usize,
            bitmap_len: usize,
        };
        Reborrow {
            bitmaps: $s.bitmaps.as_ref(),
            channels: $s.channels,
            bitmap_len: $s.bitmap_len,
        }
    }};
}

macro_rules! alloc {
    ($s:ident, $output_set:expr, $data:expr) => {
        match ($output_set, $data) {
            (output_set, data) => {
                if let Some(index) = $s.free_list.pop() {
                    $s.data[index] = data;
                    $s.bitmaps[index * $s.bitmap_len..(index + 1) * $s.bitmap_len]
                        .copy_from_slice(output_set.bitmap());
                    index
                } else {
                    let index = $s.data.len();
                    $s.data.push(data);
                    $s.bitmaps.extend_from_slice(output_set.bitmap());
                    index
                }
            }
        }
    };
}

impl Canonicalize {
    pub fn new(mut output_set: OutputSet<&mut [bool]>, inversion: bool) -> Self {
        let mut new = Self {
            bitmap_len: 1 << output_set.channels(),
            channels: output_set.channels(),
            used_channels: output_set.channels(),
            bitmaps: vec![],
            data: vec![],
            free_list: vec![],
            layer: vec![],
            next_layer: vec![],
            fixed: 0,
            buffer: vec![],
            temp: output_set.to_owned(),
        };

        let mut data = CandidateData {
            perm: Perm::identity(output_set.channels()),
            fingerprint: CVec::new(),
            partition: CVec::new(),
            partition_score: Default::default(),
        };

        for channel in (0..new.channels).rev() {
            if output_set.is_channel_unconstrained(channel) {
                new.used_channels -= 1;
                output_set.swap_channels([channel, new.used_channels]);
                data.perm.perm.swap(channel, new.used_channels);
            }
        }

        let identity = alloc!(new, output_set.as_ref(), data.clone());
        new.layer.push(identity);

        if inversion {
            data.perm.invert = true;
            let inverted = alloc!(new, output_set.as_ref(), data);
            get_mut!(new, inverted).invert();
            if get!(new, inverted) == get!(new, identity) {
                new.free_list.push(inverted);
            } else {
                new.layer.push(inverted);
            }
        }

        new
    }

    pub fn canonicalize(&mut self) -> (OutputSet<&[bool]>, Perm) {
        self.initialize_partitions();

        loop {
            self.prune_using_fingerprints();
            let mut prune = false;
            while self.move_singleton() {
                prune = true;
            }
            if prune {
                self.prune(true);
            }
            if self.fixed == self.used_channels {
                break;
            }
            self.individualize();
            self.prune(false);
            if self.fixed == self.used_channels {
                break;
            }
            self.refine();
        }

        let index = self.layer[0];
        (get!(self, index), self.data[index].perm.clone())
    }

    fn initialize_partitions(&mut self) {
        for &index in self.layer.iter() {
            let output_set = get!(self, index);
            let mut fingerprints = (0..self.used_channels)
                .map(|channel| (output_set.channel_fingerprint(channel), channel))
                .collect::<CVec<_>>();

            fingerprints.sort_unstable();

            let mut part_fingerprint = fingerprints[0].0;
            let mut part_id = 0;
            let mut part_mask = 0u16;

            let data = &mut self.data[index];

            for &(fingerprint, channel) in fingerprints.iter() {
                if part_fingerprint != fingerprint {
                    data.partition.push((part_mask, part_id));
                    part_mask = 0;
                    part_fingerprint = fingerprint;
                    part_id += 1;
                }
                data.fingerprint.push(fingerprint);
                part_mask |= 1 << channel;
            }

            data.partition.push((part_mask, part_id));

            data.sort_partition();
        }
    }

    fn prune_using_fingerprints(&mut self) {
        let data = &self.data;
        let min_index = self
            .layer
            .iter()
            .cloned()
            .min_by(|&a, &b| data[b].score().cmp(&data[a].score()))
            .unwrap();
        let min_score = self.data[min_index].clone();

        let free_list = &mut self.free_list;

        self.layer.retain(|&index| {
            if data[index].score() == min_score.score() {
                true
            } else {
                free_list.push(index);
                false
            }
        });
    }

    fn move_singleton(&mut self) -> bool {
        for &index in self.layer.iter() {
            let data = &mut self.data[index];

            let source_channel = match data.partition.last() {
                None => return false,
                Some((part, _)) if part & (part - 1) != 0 => return false,
                Some((part, _)) => part.trailing_zeros() as usize,
            };

            data.partition.pop();

            if source_channel != self.fixed {
                get_mut!(self, index).swap_channels([source_channel, self.fixed]);
                data.perm.perm.swap(source_channel, self.fixed);

                let source_mask = 1 << source_channel;
                let fixed_mask = 1 << self.fixed;

                for (part, _id) in data.partition.iter_mut() {
                    let fixed_present = *part & fixed_mask != 0;

                    *part = (*part & !fixed_mask) | (source_mask * fixed_present as u16);
                }
            }
        }
        self.fixed += 1;
        true
    }

    fn prune(&mut self, recompute_fingerprints: bool) {
        if self.layer.len() == 1 {
            return;
        }

        let reborrow = reborrow!(self);
        let free_list = &mut self.free_list;

        if self.fixed == self.used_channels {
            let min_output_set_index = *self
                .layer
                .iter()
                .min_by_key(|&index| get!(reborrow, index))
                .unwrap();

            self.layer.retain(|&index| {
                if index == min_output_set_index {
                    true
                } else {
                    free_list.push(index);
                    false
                }
            });
            return;
        }

        self.layer.sort_by_key(|&index| get!(reborrow, index));
        self.layer.dedup_by(|&mut test, &mut repr| {
            if get!(reborrow, test) == get!(reborrow, repr) {
                free_list.push(test);
                true
            } else {
                false
            }
        });

        if self.layer.len() == 1 || !recompute_fingerprints {
            return;
        }

        let mut max_fingerprint = 0;

        for &index in self.layer.iter() {
            let fingerprint =
                get!(self, index).low_channels_fingerprint(self.fixed, &mut self.buffer);
            self.data[index].fingerprint[0] = fingerprint;
            max_fingerprint = max_fingerprint.max(fingerprint);
        }

        let data = &self.data;

        self.layer.retain(|&index| {
            if data[index].fingerprint[0] == max_fingerprint {
                true
            } else {
                free_list.push(index);
                false
            }
        })
    }

    fn individualize(&mut self) {
        let mut max_fingerprint = 0;
        for index in self.layer.drain(..) {
            let mut part_iter = self.data[index].partition.last().unwrap().0;

            while part_iter != 0 {
                let source_channel = part_iter.trailing_zeros() as usize;
                part_iter = part_iter & (part_iter - 1);
                self.temp
                    .bitmap_mut()
                    .copy_from_slice(get!(self, index).bitmap());

                self.temp.swap_channels([source_channel, self.fixed]);
                let fingerprint = self
                    .temp
                    .low_channels_fingerprint(self.fixed + 1, &mut self.buffer);

                if fingerprint > max_fingerprint {
                    for free_index in self.next_layer.drain(..) {
                        self.free_list.push(free_index);
                    }
                    max_fingerprint = fingerprint
                } else if fingerprint < max_fingerprint {
                    continue;
                }

                let mut data = self.data[index].clone();

                data.perm.perm.swap(source_channel, self.fixed);
                let last_part = data.partition.last_mut().unwrap();
                last_part.0 &= !(1 << source_channel);

                let source_mask = 1 << source_channel;
                let fixed_mask = 1 << self.fixed;

                for (part, _id) in data.partition.iter_mut() {
                    let fixed_present = *part & fixed_mask != 0;

                    *part = (*part & !fixed_mask) | (source_mask * fixed_present as u16);
                }

                let next_index = alloc!(self, self.temp.as_ref(), data);
                self.next_layer.push(next_index);
            }

            self.free_list.push(index);
        }

        swap(&mut self.layer, &mut self.next_layer);

        self.fixed += 1;
    }

    fn refine(&mut self) {
        for &index in self.layer.iter() {
            let data = &mut self.data[index];
            let output_set = get!(self, index);

            data.fingerprint.clear();

            let mut part_id = 0;

            for (part, _id) in replace(&mut data.partition, CVec::new()) {
                let mut part_iter = part;

                let mut fingerprints = CVec::<(u64, usize)>::new();

                while part_iter != 0 {
                    let channel = part_iter.trailing_zeros() as usize;
                    part_iter = part_iter & (part_iter - 1);
                    fingerprints.push((
                        output_set.low_channels_channel_fingerprint(
                            self.fixed,
                            channel,
                            &mut self.buffer,
                        ),
                        channel,
                    ));
                }

                fingerprints.sort_unstable();

                let mut part_fingerprint = fingerprints[0].0;
                let mut part_mask = 0u16;

                for &(fingerprint, channel) in fingerprints.iter() {
                    if part_fingerprint != fingerprint {
                        data.partition.push((part_mask, part_id));
                        part_mask = 0;
                        part_fingerprint = fingerprint;
                        part_id += 1;
                    }
                    data.fingerprint.push(fingerprint);
                    part_mask |= 1 << channel;
                }

                data.partition.push((part_mask, part_id));

                part_id += 1;
            }

            data.sort_partition();
        }
    }
}
