#[global_allocator]
static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use structopt::StructOpt;

use sortnetopt::{logging, output_set::MAX_CHANNELS};

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
    log::info!("options: {:?}", opt);
}
