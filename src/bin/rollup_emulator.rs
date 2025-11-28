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
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();

    let args = Args::parse();

    tracing::info!("Starting rollup emulator");
    let node = RollupNode::new(args.storage_path);
    node.run(args.number_of_blocks);
    tracing::info!("Rollup emulator finished");
}
