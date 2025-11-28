use nomt_playground::rollup::Node;

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();

    tracing::info!("Starting rollup emulator");
    let node = Node::new();
    node.run(1000);
    tracing::info!("Rollup emulator finished");
}
