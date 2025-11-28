use nomt::hasher::BinaryHasher;
use nomt::{Nomt, Overlay, SessionParams, WitnessMode};
use sha2::digest;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use tempfile::TempDir;
// TODO: replace K with u64

// Storage

pub struct NomtSessionBuilder<H> {
    state_db: Arc<Nomt<BinaryHasher<H>>>,
    relevant_snapshot_refs: Vec<u64>,
    all_snapshots: Arc<RwLock<HashMap<u64, Overlay>>>,
}

impl<H> NomtSessionBuilder<H>
where
    H: digest::Digest<OutputSize = digest::typenum::U32> + Send + Sync,
{
    pub fn new(
        state_db: Arc<Nomt<BinaryHasher<H>>>,
        relevant_snapshot_refs: Vec<u64>,
        all_snapshots: Arc<RwLock<HashMap<u64, Overlay>>>,
    ) -> Self {
        Self {
            state_db,
            relevant_snapshot_refs,
            all_snapshots,
        }
    }

    #[tracing::instrument(skip(self))]
    pub fn begin_session(&self) -> anyhow::Result<nomt::Session<BinaryHasher<H>>> {
        let start = std::time::Instant::now();
        let params = {
            let mut overlays = Vec::with_capacity(self.relevant_snapshot_refs.len());
            let snapshots = self.all_snapshots.read().expect("Snapshots lock poisoned");
            for overlay_ref in &self.relevant_snapshot_refs {
                let Some(state_overlay) = snapshots.get(overlay_ref) else {
                    tracing::debug!(
                        "Cannot find snapshot from reference, assuming it has been committed"
                    );
                    continue;
                };
                overlays.push(state_overlay);
            }
            SessionParams::default()
                .overlay(overlays)
                .map_err(|e| {
                    anyhow::anyhow!(
                        "Failed to construct session params for user session: {:?}",
                        e
                    )
                })?
                .witness_mode(WitnessMode::read_write())
        };
        let session = self.state_db.begin_session(params);
        let init_time = start.elapsed();
        let overlays = self.relevant_snapshot_refs.len();
        tracing::debug!(?init_time, overlays, "Session has been initialized");
        Ok(session)
    }
}

pub struct StorageManager<H> {
    dir: TempDir,
    state_db: Arc<Nomt<BinaryHasher<H>>>,
    all_snapshots: Arc<RwLock<HashMap<u64, Overlay>>>,
}

impl<H> StorageManager<H>
where
    H: digest::Digest<OutputSize = digest::typenum::U32> + Send + Sync,
{
    pub fn new() -> Self {
        let dir = tempfile::tempdir().unwrap();
        todo!()
    }
}
