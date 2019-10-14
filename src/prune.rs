use std::{
    collections::BTreeMap,
    fs::{self, File},
    io::{BufRead, BufReader, BufWriter, Write},
    path::PathBuf,
};

use indicatif::{ProgressBar, ProgressStyle};
use memmap::{Mmap, MmapOptions};
use rayon::prelude::*;

use crate::output_set::{
    index::{LowerInvert, OutputSetIndex},
    OutputSet,
};

struct PackedOutputSets {
    stride: usize,
    packed_buf: Mmap,
}

impl PackedOutputSets {
    fn new(channels: usize, packed_buf: Mmap) -> Self {
        let stride = OutputSet::packed_len_for_channels(channels);
        Self { stride, packed_buf }
    }

    fn iter_packed<'a>(&'a self) -> impl Iterator<Item = &'a [u8]> {
        self.packed_buf.chunks(self.stride)
    }

    fn get_packed(&self, index: usize) -> &[u8] {
        &self.packed_buf[self.stride * index..][..self.stride]
    }
}

pub fn prune(channels: usize, input: PathBuf) {
    let input_file = File::open(&input).unwrap();
    let input_data = unsafe { MmapOptions::new().map(&input_file).unwrap() };

    let output_path = input.with_extension("pbin");
    if output_path.exists() {
        log::info!("{:?} already exists", output_path);
        return;
    }
    let output_tmp_path = input.with_extension("tmp");
    let mut output_file = BufWriter::new(File::create(&output_tmp_path).unwrap());

    let packed_output_sets = PackedOutputSets::new(channels, input_data);

    let mut by_state_len = BTreeMap::<usize, Vec<usize>>::default();

    let mut total_input_len = 0;

    for (i, packed) in packed_output_sets.iter_packed().enumerate() {
        let state_len = packed
            .iter()
            .map(|byte| byte.count_ones() as usize)
            .sum::<usize>();

        by_state_len
            .entry(state_len)
            .or_insert_with(|| vec![])
            .push(i);

        total_input_len += 1;
    }

    let mut index = OutputSetIndex::<LowerInvert>::new(channels);

    let template = "{elapsed_precise} [{wide_bar:.green/blue}] {percent}% {pos}/{len} {eta}";
    let bar = ProgressBar::new(total_input_len);
    bar.set_style(
        ProgressStyle::default_bar()
            .template(template)
            .progress_chars("#>-"),
    );

    for (state_len, ids) in by_state_len {
        log::info!("len = {}, count = {}", state_len, ids.len());
        log::info!("");

        let ids = ids
            .into_par_iter()
            .filter(|&id| {
                bar.inc(1);
                let packed = packed_output_sets.get_packed(id);
                let output_set = OutputSet::from_packed(channels, packed);

                index
                    .lookup_with_abstraction(output_set.as_ref(), &output_set.abstraction())
                    .is_none()
            })
            .collect::<Vec<_>>();

        for id in ids {
            let packed = packed_output_sets.get_packed(id);
            output_file.write_all(packed).unwrap();
            let output_set = OutputSet::from_packed(channels, packed);

            index.insert_new_unchecked_with_abstraction(
                output_set.as_ref(),
                &output_set.abstraction(),
                0,
            );
        }

        log::info!("subsumed_len = {}", index.len());
    }

    drop(output_file);
    fs::rename(output_tmp_path, output_path).unwrap();
}

pub fn prune_all(input: PathBuf) {
    let index = input.join("index.txt");
    let index_file = BufReader::new(File::open(index).unwrap());
    for line in index_file.lines() {
        let line = line.unwrap();
        let channels = str::parse::<usize>(line.split('_').nth(1).unwrap()).unwrap();
        log::info!("pruning {}", line);

        prune(channels, input.join(line));
    }
}
