use clap::Parser;
use nomt_playground::rollup::RollupNode;

#[derive(Parser, Debug)]
#[command(name = "rollup_emulator")]
#[command(about = "A rollup emulator for nomt")]
struct Args {
    /// Number of blocks to process
    #[arg(short, long)]
    number_of_blocks: usize,

    /// Path to the storage directory
    #[arg(short, long)]
    storage_path: Option<String>,

    /// Number of sequencer background tasks
    #[arg(long, default_value = "10")]
    fast_sequencers: usize,
    /// Number of sequencer background tasks
    #[arg(long, default_value = "2")]
    sleepy_sequencers: usize,
    /// Probability of finalization (0-100)
    #[arg(long, default_value = "80")]
    finalization_probability: u8,
    /// Number of simulation runs
    #[arg(long, default_value = "1")]
    simulation_runs: usize,
}

#[tokio::main]
async fn main() {
    // Exit the whole process if any thread panics
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        default_hook(info);
        std::process::exit(1);
    }));

    tracing_subscriber::fmt::init();

    let args = Args::parse();

    for run in 0..args.simulation_runs {
        tracing::info!(run, total = args.simulation_runs, "Starting rollup emulator");
        let node = RollupNode::new(
            args.storage_path.clone(),
            args.fast_sequencers,
            args.sleepy_sequencers,
            args.finalization_probability,
        );
        node.run(args.number_of_blocks);
        tracing::info!(run, "Rollup emulator run finished");
    }
    tracing::info!("All simulation runs completed");
}
