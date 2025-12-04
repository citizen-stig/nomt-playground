# NOMT Playground

Experimental code for testing [NOMT](https://github.com/thrumdev/nomt) (binary hash trie storage).

## Rollup Emulator

Simulates rollup interaction with NOMT, extracted from Sovereign SDK. 
Runs multiple sequencer tasks that generate random reads/writes while the main loop processes blocks and manages finalization.

### Build

```bash
cargo build --release
```

### Usage

```bash
# Basic: process 100 blocks
./target/release/rollup_emulator -n 100

# With custom storage path
./target/release/rollup_emulator -n 100 -s /tmp/nomt_data

# Full options
./target/release/rollup_emulator \
    -n 1000 \
    -s /tmp/nomt_data \
    --fast-sequencers 10 \
    --sleepy-sequencers 2 \
    --finalization-probability 80
```

### Options

| Flag                         | Description                 | Default  |
|------------------------------|-----------------------------|----------|
| `-n, --number-of-blocks`     | Number of blocks to process | required |
| `-s, --storage-path`         | Storage directory path      | temp dir |
| `--fast-sequencers`          | Fast sequencer task count   | 10       |
| `--sleepy-sequencers`        | Slow sequencer task count   | 2        |
| `--finalization-probability` | Finalization chance (0-100) | 80       |

### Enable Logging

```bash
RUST_LOG=info ./target/release/rollup_emulator -n 100
```
