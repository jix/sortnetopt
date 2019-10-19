use std::{
    collections::BTreeMap,
    fs::File,
    io::{BufRead, BufReader, BufWriter, Read, Write},
    path::PathBuf,
};

use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use memmap::MmapOptions;

use crate::output_set::OutputSet;

pub fn fix_proof(input: PathBuf) {
    let mut pruned_sets = BTreeMap::default();

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

        let stride = OutputSet::packed_len_for_channels(channels);
        for packed in pruned_data.chunks(stride) {
            pruned_sets.insert((channels, packed.to_owned()), bound);
        }
    }

    let proof_path = input.join("proof.old.bin");
    let mut proof_file = BufReader::new(File::open(proof_path).unwrap());

    let proof_fix_path = input.join("proof.bin");
    if proof_fix_path.exists() {
        panic!("proof.bin already exists");
    }
    let mut proof_fix_file = BufWriter::new(File::create(proof_fix_path).unwrap());

    let step_count = proof_file.read_u32::<LittleEndian>().unwrap();

    proof_fix_file
        .write_u32::<LittleEndian>(step_count)
        .unwrap();

    let mut lengths = vec![];

    for step in 0..step_count {
        let offset = proof_file.read_u64::<LittleEndian>().unwrap();
        let len = proof_file.read_u32::<LittleEndian>().unwrap();

        lengths.push(len);

        proof_fix_file
            .write_u64::<LittleEndian>(offset + step as u64)
            .unwrap();

        proof_fix_file.write_u32::<LittleEndian>(len + 1).unwrap();
    }

    for len in lengths {
        let mut buffer = vec![];
        (&mut proof_file)
            .take(len as u64)
            .read_to_end(&mut buffer)
            .unwrap();

        let channels = buffer[0] as usize;
        let packed = buffer[1..][..OutputSet::packed_len_for_channels(channels)].to_owned();
        let bound = *pruned_sets.get(&(channels, packed)).expect("set not found");

        proof_fix_file.write_u8(buffer[0]).unwrap();
        proof_fix_file.write_u8(bound).unwrap();
        proof_fix_file.write_all(&buffer[1..]).unwrap();
    }
}
