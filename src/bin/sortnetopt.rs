#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use std::path::PathBuf;

use rustc_hash::FxHashSet as HashSet;
use structopt::StructOpt;

use sortnetopt::{
    logging,
    output_set::{
        index::{Lower, OutputSetIndex},
        OutputSet, MAX_CHANNELS,
    },
    search::Search,
};

#[derive(Debug, StructOpt)]
struct Opt {
    /// Print peak memory usage
    #[structopt(short, long)]
    mem_usage: bool,
    #[structopt(subcommand)]
    command: OptCommand,
}

#[derive(Debug, StructOpt)]
enum OptCommand {
    Search(OptSearch),
    Gnp(OptGnp),
}

#[derive(Debug, StructOpt)]
struct OptSearch {
    /// Number of channels in the sorting network
    channels: usize,
    #[structopt(parse(from_os_str))]
    output: Option<PathBuf>,
    #[structopt(short, long)]
    limit: Option<usize>,
}

#[derive(Debug, StructOpt)]
struct OptGnp {
    /// Number of channels in the sorting network
    channels: usize,
    /// Dump index trees as graphviz graph
    #[structopt(short, long)]
    dump_index: bool,
}

fn main() {
    let opt = Opt::from_args();
    logging::setup(opt.mem_usage);

    match opt.command {
        OptCommand::Search(opt) => cmd_search(opt),
        OptCommand::Gnp(opt) => cmd_gnp(opt),
    }
}

fn cmd_search(opt: OptSearch) {
    log::info!("options: {:?}", opt);

    let initial = OutputSet::all_values(opt.channels);

    log::info!(
        "result = {}",
        Search::search(initial.as_ref(), opt.limit, opt.output.clone())
    );
}

fn cmd_gnp(opt: OptGnp) {
    log::info!("options: {:?}", opt);

    assert!(opt.channels <= MAX_CHANNELS);

    let initial = OutputSet::all_values(opt.channels);
    let abstraction = initial.abstraction();

    let mut layer = OutputSetIndex::<Lower>::new(opt.channels);

    layer.insert_with_abstraction(initial.as_ref(), &abstraction, 0);

    let mut layer_count = 0;

    while !layer.is_empty() {
        let mut next_layer = OutputSetIndex::<Lower>::new(opt.channels);

        let mut next_output_sets = HashSet::default();

        layer.for_each(|output_set: OutputSet<&[bool]>, _abstraction, _value| {
            for i in 0..opt.channels {
                for j in 0..i {
                    let mut next_output_set = output_set.to_owned();
                    if next_output_set.apply_comparator([i, j]) {
                        next_output_set.canonicalize(false);
                        next_output_sets.insert(next_output_set);
                    }
                }
            }

            for next_output_set in next_output_sets.drain() {
                let abstraction = next_output_set.abstraction();
                next_layer.insert_with_abstraction(next_output_set.as_ref(), &abstraction[..], 0);
            }
        });

        layer_count += 1;

        log::info!("layer {} size is {}", layer_count, next_layer.len(),);

        layer = next_layer;

        if opt.dump_index {
            layer
                .dump_dot(&mut std::io::BufWriter::new(
                    std::fs::File::create(format!("_layer_{}.dot", layer_count)).unwrap(),
                ))
                .unwrap();
        }
    }
}
