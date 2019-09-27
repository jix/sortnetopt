#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use rustc_hash::FxHashSet as HashSet;
use structopt::StructOpt;

use sortnetopt::{
    logging,
    output_set::{index::OutputSetIndex, OutputSet, MAX_CHANNELS},
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
}

#[derive(Debug, StructOpt)]
struct OptSearch {
    /// Number of channels in the sorting network
    channels: usize,
}

fn main() {
    let opt = Opt::from_args();
    logging::setup(opt.mem_usage);

    match opt.command {
        OptCommand::Search(opt) => cmd_search(opt),
    }
}

fn cmd_search(opt: OptSearch) {
    assert!(opt.channels <= MAX_CHANNELS);

    let mut layer = OutputSetIndex::<()>::new(opt.channels);

    layer.insert(OutputSet::all_values(opt.channels).as_ref(), ());

    let mut layer_count = 0;

    while !layer.is_empty() {
        let mut next_layer = OutputSetIndex::<()>::new(opt.channels);

        let mut next_output_sets = HashSet::default();

        let mut to_remove = vec![];

        let mut scan_hits = 0;
        let mut exact_hits = 0;

        layer.for_each(&mut |_id, output_set, _value| {
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
                if next_layer.lookup_id(next_output_set.as_ref()).is_some() {
                    continue;
                }
                let mut subsumed = false;
                let (this_scan_hits, this_exact_hits) = next_layer.scan_subsuming(
                    next_output_set.as_ref(),
                    &[],
                    true,
                    &mut |_id, _output_set, _value| {
                        subsumed = true;
                        false
                    },
                );
                scan_hits += this_scan_hits;
                exact_hits += this_exact_hits;
                if subsumed {
                    continue;
                }
                let (this_scan_hits, this_exact_hits) = next_layer.scan_subsumed(
                    next_output_set.as_ref(),
                    &[],
                    true,
                    &mut |id, _output_set, _value| {
                        to_remove.push(id);
                        true
                    },
                );
                scan_hits += this_scan_hits;
                exact_hits += this_exact_hits;

                for id in to_remove.drain(..).rev() {
                    next_layer.remove_by_id(id);
                }

                next_layer.insert(next_output_set.as_ref(), ());
            }

            true
        });

        layer_count += 1;

        log::info!(
            "layer {} size is {} scan {} exact {} ratio {}",
            layer_count,
            next_layer.len(),
            scan_hits,
            exact_hits,
            exact_hits as f64 / scan_hits as f64
        );

        layer = next_layer;
    }

    log::info!("options: {:?}", opt);
}
