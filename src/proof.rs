use std::{
    collections::BTreeMap,
    fs::File,
    io::{BufRead, BufReader, BufWriter, Write},
    path::PathBuf,
    sync::Arc,
};

use byteorder::{LittleEndian, WriteBytesExt};
use indicatif::{ProgressBar, ProgressStyle};
use memmap::MmapOptions;
use rayon::prelude::*;
use rustc_hash::FxHashMap as HashMap;

use crate::{
    huffman::max_plus_1_huffman,
    output_set::{
        index::{LowerInvert, OutputSetIndex},
        CVec, OutputSet,
    },
};

pub fn gen_proof(input: PathBuf) {
    let mut pruned_indexes = BTreeMap::default();

    let index = input.join("index.txt");
    let index_file = BufReader::new(File::open(index).unwrap());
    for line in index_file.lines() {
        let line = line.unwrap();
        let channels = str::parse::<usize>(line.split('_').nth(1).unwrap()).unwrap();
        let bound =
            str::parse::<u8>(line.split('_').nth(2).unwrap().split('.').next().unwrap()).unwrap();

        log::info!("loading {}_{}", channels, bound);

        let pruned_path = input.join(line).with_extension("pbin");

        let pruned_file = File::open(pruned_path).unwrap();
        let pruned_data = unsafe { MmapOptions::new().map(&pruned_file).unwrap() };

        let pruned_index = pruned_indexes
            .entry(channels)
            .or_insert_with(|| OutputSetIndex::<LowerInvert>::new(channels));

        let stride = OutputSet::packed_len_for_channels(channels);
        for packed in pruned_data.chunks(stride) {
            let output_set = OutputSet::from_packed(channels, packed);
            pruned_index.insert_new_unchecked_with_abstraction(
                output_set.as_ref(),
                &output_set.abstraction(),
                bound,
            );
        }
    }

    for (channels, pruned_index) in pruned_indexes.iter() {
        log::info!("{} channels: {}", channels, pruned_index.len())
    }

    let max_channels = *pruned_indexes.keys().rev().next().unwrap();
    let mut gen = GenProof::new(pruned_indexes);

    gen.prove_all();

    gen.encode_proof(&Arc::new(OutputSet::all_values(max_channels)));

    log::info!("proof using {} steps", gen.step_data.len());

    let proof_path = input.join("proof.bin");
    let mut proof_file = BufWriter::new(File::create(proof_path).unwrap());

    gen.write_proof(&mut proof_file);
}

#[derive(Clone)]
enum ProofStep {
    Trivial,
    NotSorted,
    Huffman {
        pol: bool,
        witnesses: Vec<Option<(bool, CVec<usize>, Arc<OutputSet>)>>,
    },
    Successors {
        witnesses: Vec<Option<(bool, CVec<usize>, Arc<OutputSet>)>>,
    },
}

struct GenProof {
    pruned_indexes: BTreeMap<usize, OutputSetIndex<LowerInvert>>,
    output_sets: HashMap<Arc<OutputSet>, (u8, Arc<OutputSet>)>,
    steps: HashMap<Arc<OutputSet>, ProofStep>,
    step_ids: HashMap<Arc<OutputSet>, usize>,
    step_data: Vec<Box<[u8]>>,
}

impl GenProof {
    pub fn new(pruned_indexes: BTreeMap<usize, OutputSetIndex<LowerInvert>>) -> Self {
        let mut output_sets = HashMap::default();
        for pruned_index in pruned_indexes.values() {
            pruned_index.for_each(|output_set, _abstraction, bound| {
                let shared_output_set = Arc::new(output_set.to_owned());
                output_sets.insert(shared_output_set.clone(), (bound, shared_output_set));
            })
        }
        Self {
            output_sets,
            pruned_indexes,
            steps: Default::default(),
            step_ids: Default::default(),
            step_data: vec![],
        }
    }

    pub fn prove_all(&mut self) {
        let template = "{elapsed_precise} [{wide_bar:.green/blue}] {percent}% {pos}/{len} {eta}";
        let bar = ProgressBar::new(self.output_sets.len() as u64);
        bar.set_style(
            ProgressStyle::default_bar()
                .template(template)
                .progress_chars("#>-"),
        );

        self.steps = self
            .output_sets
            .iter()
            .collect::<Vec<_>>()
            .into_par_iter()
            .map(|(output_set, &(bound, _))| {
                bar.inc(1);
                let proof_step = self
                    .trivial_step(bound, output_set.as_ref().as_ref())
                    .or_else(|| self.huffman_step(bound, output_set.as_ref().as_ref()))
                    .or_else(|| self.successor_step(bound, output_set.as_ref().as_ref()));

                (
                    output_set.clone(),
                    proof_step.expect("no valid proof step found"),
                )
            })
            .collect();
    }

    pub fn encode_proof(&mut self, target: &Arc<OutputSet>) -> Option<usize> {
        if let Some(&id) = self.step_ids.get(target) {
            Some(id)
        } else {
            let mut step_data = vec![];

            let bound = self.output_sets.get(target).unwrap().0;

            step_data.push(target.channels() as u8);
            step_data.push(bound);
            step_data.extend(target.packed());

            let step_witnesses;
            match self.steps.get(target).unwrap().clone() {
                ProofStep::Trivial | ProofStep::NotSorted => return None,
                ProofStep::Huffman { pol, witnesses } => {
                    step_data.push(pol as u8);
                    step_witnesses = witnesses;
                }
                ProofStep::Successors { witnesses } => {
                    step_data.push(2);
                    step_witnesses = witnesses;
                }
            }

            for witness in step_witnesses {
                if let Some((invert, perm, id)) = witness.and_then(|witness| {
                    Some((witness.0, witness.1, self.encode_proof(&witness.2)?))
                }) {
                    step_data.push(invert as u8);
                    step_data.extend(perm.iter().map(|&index| index as u8));
                    step_data.write_u32::<LittleEndian>(id as u32).unwrap();
                } else {
                    step_data.push(2);
                }
            }

            let id = self.step_data.len();

            self.step_ids.insert(target.clone(), id);
            self.step_data.push(step_data.into_boxed_slice());

            Some(id)
        }
    }

    pub fn write_proof(&self, target: &mut impl Write) {
        target
            .write_u32::<LittleEndian>(self.step_data.len() as u32)
            .unwrap();

        let mut offset = 4 + (8 + 4) * self.step_data.len() as u64;

        for step in self.step_data.iter() {
            target.write_u64::<LittleEndian>(offset).unwrap();
            target.write_u32::<LittleEndian>(step.len() as u32).unwrap();
            offset += step.len() as u64;
        }

        for step in self.step_data.iter() {
            target.write_all(step).unwrap();
        }
    }

    fn lookup_witness(
        &self,
        target: OutputSet<&[bool]>,
    ) -> (u8, Option<(bool, CVec<usize>, Arc<OutputSet>)>) {
        let subsuming = self
            .pruned_indexes
            .get(&target.channels())
            .and_then(|index| {
                index.lookup_subsuming_with_abstraction(target, &target.abstraction())
            });

        if let Some((bound, (invert, perm), output_set)) = subsuming {
            (
                bound,
                Some((
                    invert,
                    perm,
                    self.output_sets.get(&output_set).unwrap().1.clone(),
                )),
            )
        } else {
            (if target.is_sorted() { 0 } else { 1 }, None)
        }
    }

    fn trivial_step(&self, bound: u8, target: OutputSet<&[bool]>) -> Option<ProofStep> {
        if bound == 0 {
            Some(ProofStep::Trivial)
        } else if bound == 1 && !target.is_sorted() {
            Some(ProofStep::NotSorted)
        } else {
            None
        }
    }

    fn huffman_step(&self, bound: u8, target: OutputSet<&[bool]>) -> Option<ProofStep> {
        let mut extremal_channels = [CVec::new(), CVec::new()];

        for (pol, pol_channels) in extremal_channels.iter_mut().enumerate() {
            for channel in 0..target.channels() {
                if target.channel_is_extremal(pol > 0, channel) {
                    pol_channels.push(channel);
                }
            }
        }

        let mut pols = [0, 1];
        pols.sort_unstable_by_key(|&pol| extremal_channels[pol].len());

        for &pol in pols.iter() {
            let mut bounds = vec![];
            let mut witnesses = vec![];
            let mut pruned_output_sets = vec![];
            for &channel in extremal_channels[pol].iter() {
                let mut pruned = OutputSet::all_values(target.channels() - 1);
                target.prune_extremal_channel_into(pol > 0, channel, pruned.as_mut());
                let (bound, witness) = self.lookup_witness(pruned.as_ref());
                bounds.push(bound);
                witnesses.push(witness);
                pruned_output_sets.push(pruned);
            }

            let huffman_bound = max_plus_1_huffman(&bounds);
            if huffman_bound >= bound {
                return Some(ProofStep::Huffman {
                    pol: pol > 0,
                    witnesses,
                });
            }
        }

        None
    }

    fn successor_step(&self, bound: u8, target: OutputSet<&[bool]>) -> Option<ProofStep> {
        let mut witnesses = vec![];
        for i in 0..target.channels() {
            for j in 0..i {
                let mut successor = target.to_owned();
                if successor.apply_comparator([i, j]) {
                    let (successor_bound, witness) = self.lookup_witness(successor.as_ref());
                    if successor_bound + 1 < bound {
                        return None;
                    }
                    witnesses.push(witness);
                }
            }
        }

        Some(ProofStep::Successors { witnesses })
    }
}
