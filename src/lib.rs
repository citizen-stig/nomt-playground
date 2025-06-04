#[cfg(test)]
mod rollup;

use nomt::hasher::Sha2Hasher;
use nomt::trie::Node;
use nomt::{FinishedSession, Nomt, Options, Root, Session, SessionParams, Witness, WitnessMode};
use sha2::Digest;
use std::collections::BTreeMap;
use std::collections::btree_map::Entry;

pub struct NomtContainer {
    nomt: Nomt<Sha2Hasher>,
    _dir: tempfile::TempDir,
}

impl NomtContainer {
    pub fn new() -> Self {
        let dir = tempfile::tempdir().unwrap();
        let mut opts = Options::new();
        opts.path(dir.path().join("nomt_db"));
        opts.commit_concurrency(1);

        let nomt = Nomt::<Sha2Hasher>::open(opts).unwrap();

        Self { nomt, _dir: dir }
    }

    pub fn session(&self) -> Session<Sha2Hasher> {
        self.nomt
            .begin_session(SessionParams::default().witness_mode(WitnessMode::read_write()))
    }

    pub fn commit(&self, finished_session: FinishedSession) {
        finished_session.commit(&self.nomt).unwrap();
    }
}

type Key = Vec<u8>;
type Value = Vec<u8>;

#[derive(Debug, Clone)]
pub struct ReadsAndWrites {
    reads: Vec<(Key, Option<Value>)>,
    writes: Vec<(Key, Option<Value>)>,
}

// Returns prev_root and finished session
pub fn prover(
    session: Session<Sha2Hasher>,
    state_accesses: ReadsAndWrites,
) -> (Root, FinishedSession) {
    let prev_root = session.prev_root();
    println!("prover prev root  : {}", hex::encode(prev_root));

    let mut merged_accesses: BTreeMap<nomt::trie::KeyPath, nomt::KeyReadWrite> = BTreeMap::new();

    let ReadsAndWrites { reads, writes } = state_accesses;
    for (key, read_value) in reads {
        let key_hash: nomt::trie::KeyPath = sha2::Sha256::digest(&key).into();
        session.warm_up(key_hash);
        println!(
            "prover read  : {} = {:?}",
            hex::encode(key_hash),
            read_value.as_ref().map(hex::encode)
        );

        let nomt_read = nomt::KeyReadWrite::Read(read_value);
        if merged_accesses.insert(key_hash, nomt_read).is_some() {
            panic!(
                "Duplicate key read not allowed in this case: {:?}",
                key_hash
            );
        };
    }

    for (key, write_value) in writes {
        let key_hash: nomt::trie::KeyPath = sha2::Sha256::digest(&key).into();
        match merged_accesses.entry(key_hash) {
            Entry::Vacant(vacant) => {
                println!(
                    "prover write: {} = {:?}",
                    hex::encode(key_hash),
                    write_value.as_ref().map(hex::encode)
                );
                vacant.insert(nomt::KeyReadWrite::Write(write_value));
            }
            Entry::Occupied(occupied) => match occupied.remove() {
                nomt::KeyReadWrite::Read(read_value) => {
                    println!(
                        "prover read-then-write: {} = {:?} {:?}",
                        hex::encode(key_hash),
                        read_value.as_ref().map(hex::encode),
                        write_value.as_ref().map(hex::encode),
                    );
                    merged_accesses.insert(
                        key_hash,
                        nomt::KeyReadWrite::ReadThenWrite(read_value, write_value),
                    );
                }
                _ => {
                    panic!("Duplicate key write are not allowed: {:?}", key_hash);
                }
            },
        }
    }

    let nomt_accesses = merged_accesses.into_iter().collect::<Vec<_>>();

    let finished = session.finish(nomt_accesses).expect("finish failed");

    (prev_root, finished)
}

// Verifies and returns new root.
pub fn verifier(state_accesses: ReadsAndWrites, prev_root: Root, witness: Witness) -> Node {
    let ReadsAndWrites { reads, writes } = state_accesses;

    let prev_root = prev_root.into_inner();
    println!("verifier prev root: {}", hex::encode(prev_root));

    let Witness {
        path_proofs,
        operations:
            nomt::WitnessedOperations {
                reads: mut witnessed_reads,
                writes: mut witnessed_writes,
            },
    } = witness;

    // Reads
    let mut state_reads_with_hashes = reads
        .into_iter()
        .map(|(key, v)| {
            let key_hash: nomt::trie::KeyPath = sha2::Sha256::digest(&key).into();
            (key_hash, key, v)
        })
        .collect::<Vec<_>>();

    state_reads_with_hashes.sort_by(|a, b| a.0.cmp(&b.0));
    witnessed_reads.sort_by(|a, b| a.key.cmp(&b.key));
    if state_reads_with_hashes.len() != witnessed_reads.len() {
        panic!(
            "Number of state reads ({}) does not match number of witnessed reads ({})",
            state_reads_with_hashes.len(),
            witnessed_reads.len()
        );
    }
    for ((key_hash, key, read_value), witnessed_read) in state_reads_with_hashes
        .into_iter()
        .zip(witnessed_reads.into_iter())
    {
        if key_hash != witnessed_read.key {
            panic!(
                "Missing witnessed read: {}, hash({})",
                hex::encode(&key),
                hex::encode(key_hash),
            );
        }

        println!(
            "verifier read: {} = {:?}",
            hex::encode(key_hash),
            read_value,
        );

        let witnessed_path = &path_proofs[witnessed_read.path_index];

        let verified = witnessed_path
            .inner
            .verify::<Sha2Hasher>(witnessed_path.path.path(), prev_root)
            .expect("failed to verify read");
        match read_value {
            // Check for non-existence if the return value was None
            None => assert!(verified.confirm_nonexistence(&witnessed_read.key).unwrap()),
            // Verify the correctness of the returned value when it is Some(_)
            Some(ref v) => {
                let leaf = nomt::trie::LeafData {
                    key_path: witnessed_read.key,
                    value_hash: sha2::Sha256::digest(v).into(),
                };
                assert!(verified.confirm_value(&leaf).unwrap());
            }
        }
    }

    // Writes
    let mut state_writes_with_hashes = writes
        .into_iter()
        .map(|(key, v)| {
            let key_hash: nomt::trie::KeyPath = sha2::Sha256::digest(&key).into();
            (key_hash, key, v)
        })
        .collect::<Vec<_>>();
    state_writes_with_hashes.sort_by(|a, b| a.0.cmp(&b.0));
    witnessed_writes.sort_by(|a, b| a.key.cmp(&b.key));
    if state_writes_with_hashes.len() != witnessed_writes.len() {
        panic!(
            "Number of state writes ({}) does not match number of witnessed writes ({})",
            state_writes_with_hashes.len(),
            witnessed_writes.len()
        );
    }
    let mut updates = Vec::with_capacity(witnessed_writes.len());

    for ((key_hash, key, write_value), witnessed_write) in state_writes_with_hashes
        .into_iter()
        .zip(witnessed_writes.into_iter())
    {
        if key_hash != witnessed_write.key {
            panic!(
                "Missing witnessed write: {}, hash({})",
                hex::encode(&key),
                hex::encode(key_hash),
            );
        }

        println!(
            "verifier write: {} = {:?}",
            hex::encode(key_hash),
            write_value.as_ref().map(hex::encode)
        );
        let witnessed_path = &path_proofs[witnessed_write.path_index];

        // TODO: In case of read then write, verification is done twice!
        let verified = witnessed_path
            .inner
            .verify::<Sha2Hasher>(witnessed_path.path.path(), prev_root)
            .expect("failed to verify write");

        updates.push(nomt::proof::PathUpdate {
            inner: verified,
            ops: vec![(
                witnessed_write.key,
                write_value.as_ref().map(|v| sha2::Sha256::digest(v).into()),
            )],
        });
    }

    // This is failing because of terminator node returned
    // nomt::proof::verify_update::<Sha2Hasher>(prev_root, &updates)
    //     .expect("update verification failed")

    // So doing this piece of logic to handle that.
    if updates.is_empty() {
        prev_root
    } else {
        let new_root = nomt::proof::verify_update::<Sha2Hasher>(prev_root, &updates)
            .expect("update verification failed");
        new_root
    }
}

pub struct TestCase {
    rounds: Vec<ReadsAndWrites>,
}

impl TestCase {
    pub fn rounds_of_same_key() -> Self {
        let key_1 = b"key_1".to_vec();
        let value_a = b"value_a".to_vec();
        Self {
            rounds: vec![
                // 1. read nothing
                ReadsAndWrites {
                    reads: vec![(key_1.clone(), None)],
                    writes: Vec::new(),
                },
                // 2. write something
                ReadsAndWrites {
                    reads: Vec::new(),
                    writes: vec![(key_1.clone(), Some(value_a.clone()))],
                },
                // 3. read something
                ReadsAndWrites {
                    reads: vec![(key_1.clone(), Some(value_a.clone()))],
                    writes: Vec::new(),
                },
                // 4. write nothing
                ReadsAndWrites {
                    reads: Vec::new(),
                    writes: vec![(key_1.clone(), None)],
                },
                // 5. Read nothing again
                ReadsAndWrites {
                    reads: vec![(key_1.clone(), None)],
                    writes: Vec::new(),
                },
            ],
        }
    }
}

pub fn run_test_case(test_case: TestCase) {
    let nomt_container = NomtContainer::new();
    for (idx, state_accesses) in test_case.rounds.into_iter().enumerate() {
        println!("===== Round {}", idx + 1);
        let session = nomt_container.session();
        let (prev_root, mut finished_session) = prover(session, state_accesses.clone());

        let prover_root = finished_session.root();

        let witness = finished_session.take_witness().unwrap();
        let verifier_root = verifier(state_accesses, prev_root, witness);

        println!("prover root  : {}", hex::encode(prover_root));
        println!("verifier root: {}", hex::encode(verifier_root));

        let overlay = finished_session.into_overlay();

        overlay.commit(&nomt_container.nomt).unwrap();

        assert_eq!(
            verifier_root,
            prover_root.into_inner(),
            "verifier root does not match prover root"
        );
        // nomt_container.commit(finished_session);
        // println!("===== Round {} completed", idx + 1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nomt::hasher::BinaryHasher;
    use nomt::trie::{KeyPath, LeafData};
    use nomt::{KeyReadWrite, Overlay, proof};
    use sha2::Sha256;
    use std::collections::HashMap;
    use std::sync::{Arc, RwLock};

    #[test]
    fn test_single_node_rounds() {
        run_test_case(TestCase::rounds_of_same_key());
    }

    fn commit_session(
        session: Session<Sha2Hasher>,
        key: Vec<u8>,
        value: Option<Vec<u8>>,
    ) -> FinishedSession {
        let key_path = sha2::Sha256::digest(&key).into();
        session.warm_up(key_path);
        let accesses = vec![(key_path, nomt::KeyReadWrite::Write(value))];
        session.finish(accesses).expect("finish failed")
    }

    /// A -> B
    ///  \-> C
    #[test]
    fn test_overlays() {
        let nomt_container = NomtContainer::new();
        let key_a = b"key_a".to_vec();
        let key_path: KeyPath = sha2::Sha256::digest(&key_a).into();
        let value_a = b"value_a".to_vec();
        let value_b = b"value_b".to_vec();

        let session_a = nomt_container.session();
        let finished_a = commit_session(session_a, key_a.clone(), Some(value_a.clone()));
        let overlay_a = finished_a.into_overlay();
        let mut overlays = vec![overlay_a];
        // overlay_a.commit(&nomt_container.nomt).unwrap();

        let session_b = nomt_container.nomt.begin_session(
            SessionParams::default()
                .witness_mode(WitnessMode::read_write())
                .overlay(&overlays)
                .unwrap(),
        );
        let session_c = nomt_container.nomt.begin_session(
            SessionParams::default()
                .witness_mode(WitnessMode::read_write())
                .overlay(&overlays)
                .unwrap(),
        );

        let val_b = session_b.read(key_path).unwrap();
        let val_c = session_c.read(key_path).unwrap();
        assert_eq!(val_b, val_c);

        let finished_b = commit_session(session_b, key_a.clone(), Some(value_b.clone()));
        let overlay_b = finished_b.into_overlay();

        let _handle = std::thread::spawn(move || {
            println!("SLEEPING");
            std::thread::sleep(std::time::Duration::from_secs(5));
            let x = session_c.read(key_path).unwrap();
            println!("x: {:?}", x);
            // let _finished_c = commit_session(session_c, key_a.clone(), Some(value_c.clone()));
            // println!("FINISHED C: {:?}", _finished_c.root());
            // panic!("OOOPS");
        });

        println!("COMMITING A");
        overlays
            .pop()
            .unwrap()
            .commit(&nomt_container.nomt)
            .unwrap();

        println!("COMMITING B");
        overlay_b.commit(&nomt_container.nomt).unwrap();
        println!("COMMITED");

        // handle.join().expect("thread panicked");
        println!("COMPLETED");
    }

    #[test]
    fn test_get_merkle_proof() {
        let dir = tempfile::tempdir().unwrap();
        let mut opts = Options::new();
        opts.path(dir.path().join("nomt_db"));
        opts.commit_concurrency(1);

        let key = b"key".to_vec();
        let key_path: KeyPath = sha2::Sha256::digest(&key).into();
        let value_1 = b"value_1".to_vec();

        let nomt = Nomt::<Sha2Hasher>::open(opts).unwrap();

        let session =
            nomt.begin_session(SessionParams::default().witness_mode(WitnessMode::read_write()));
        session.warm_up(key_path);
        let accesses = vec![(key_path, nomt::KeyReadWrite::Write(Some(value_1.clone())))];
        let finished_session = session.finish(accesses).expect("finish failed");

        finished_session.commit(&nomt).unwrap();

        let session =
            nomt.begin_session(SessionParams::default().witness_mode(WitnessMode::read_write()));

        let fetched_value = session.read(key_path).unwrap();
        assert_eq!(fetched_value, Some(value_1));
        let _root = session.prev_root();
        // How to get merkle proof, that this value is included in `prev_root`, without finishing the session?
        // Something like `VerifiedPathProof` for `key_path`,
        // let key_proof: VerifiedPathProof = session.read_with_proof(key_path).unwrap();
        // assert!(key_proof.confirm_value(&nomt::trie::LeafData {
        //     key_path,
        //     value_hash: sha2::Sha256::digest(&value_1).into(),
        // }));
    }

    #[test]
    fn multi_proof_without_writes() {
        let mut opts = Options::new();
        // Changing this to 1 fixes the issue
        opts.commit_concurrency(2);
        opts.path("user_nomt_db");

        let nomt = Nomt::<Sha2Hasher>::open(opts).unwrap();
        let key1: KeyPath = sha2::Sha256::digest([
            115, 111, 118, 95, 99, 104, 97, 105, 110, 95, 115, 116, 97, 116, 101, 47, 67, 104, 97,
            105, 110, 83, 116, 97, 116, 101, 47, 99, 117, 114, 114, 101, 110, 116, 95, 104, 101,
            105, 103, 104, 116, 115, 47,
        ])
        .into();
        let key2: KeyPath = sha2::Sha256::digest([
            115, 111, 118, 95, 115, 101, 113, 117, 101, 110, 99, 101, 114, 95, 114, 101, 103, 105,
            115, 116, 114, 121, 47, 83, 101, 113, 117, 101, 110, 99, 101, 114, 82, 101, 103, 105,
            115, 116, 114, 121, 47, 112, 114, 101, 102, 101, 114, 114, 101, 100, 95, 115, 101, 113,
            117, 101, 110, 99, 101, 114, 47,
        ])
        .into();
        let key3: KeyPath = sha2::Sha256::digest([
            115, 111, 118, 95, 99, 104, 97, 105, 110, 95, 115, 116, 97, 116, 101, 47, 67, 104, 97,
            105, 110, 83, 116, 97, 116, 101, 47, 115, 108, 111, 116, 95, 110, 117, 109, 98, 101,
            114, 95, 104, 105, 115, 116, 111, 114, 121, 47, 0, 0, 0, 0, 0, 0, 0, 0,
        ])
        .into();

        let rounds = vec![vec![
            (
                key1.clone(),
                nomt::KeyReadWrite::Read(Some(vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                ])),
            ),
            (
                key2.clone(),
                nomt::KeyReadWrite::Read(Some(vec![
                    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    0, 0, 0, 0, 0, 0,
                ])),
            ),
            (
                key3.clone(),
                nomt::KeyReadWrite::Read(Some(vec![0, 0, 0, 0, 0, 0, 0, 0])),
            ),
        ]];

        for nomt_accesses in rounds {
            println!("ACCESSES: {:?}", nomt_accesses);
            let session = nomt
                .begin_session(SessionParams::default().witness_mode(WitnessMode::read_write()));
            for (k, v) in &nomt_accesses {
                session.warm_up(k.clone());
                let val = session.read(k.clone()).unwrap();
                println!("ACTUAL VALUE: {:?}, EXPECTED VALUE {:?}", val, v);
            }

            let mut finished = session.finish(nomt_accesses).unwrap();
            let nomt_witness = finished.take_witness().expect("Witness cannot be missing");
            let nomt::Witness {
                path_proofs,
                operations: nomt::WitnessedOperations { .. },
            } = nomt_witness;
            // Note, we discard `p.path`, but maybe there's a way to use to have more efficient verification?
            let path_proofs_inner = path_proofs.into_iter().map(|p| p.inner).collect::<Vec<_>>();
            let multi_proof = nomt::proof::MultiProof::from_path_proofs(path_proofs_inner);
            println!("P LEN {}", multi_proof.paths.len());
        }
    }

    #[test]
    fn multi_proof_without_writes_2() {
        let dir = tempfile::tempdir().unwrap();
        let mut opts = Options::new();
        opts.path(dir.path().join("nomt_db"));
        opts.commit_concurrency(2);
        opts.prepopulate_page_cache(true);
        // opts.path("user_nomt_db");

        let nomt = Nomt::<Sha2Hasher>::open(opts).unwrap();
        let key1: KeyPath = sha2::Sha256::digest([
            115, 111, 118, 95, 99, 104, 97, 105, 110, 95, 115, 116, 97, 116, 101, 47, 67, 104, 97,
            105, 110, 83, 116, 97, 116, 101, 47, 99, 117, 114, 114, 101, 110, 116, 95, 104, 101,
            105, 103, 104, 116, 115, 47,
        ])
        .into();
        let key2: KeyPath = sha2::Sha256::digest([
            115, 111, 118, 95, 115, 101, 113, 117, 101, 110, 99, 101, 114, 95, 114, 101, 103, 105,
            115, 116, 114, 121, 47, 83, 101, 113, 117, 101, 110, 99, 101, 114, 82, 101, 103, 105,
            115, 116, 114, 121, 47, 112, 114, 101, 102, 101, 114, 114, 101, 100, 95, 115, 101, 113,
            117, 101, 110, 99, 101, 114, 47,
        ])
        .into();
        let key3: KeyPath = sha2::Sha256::digest([
            115, 111, 118, 95, 99, 104, 97, 105, 110, 95, 115, 116, 97, 116, 101, 47, 67, 104, 97,
            105, 110, 83, 116, 97, 116, 101, 47, 115, 108, 111, 116, 95, 110, 117, 109, 98, 101,
            114, 95, 104, 105, 115, 116, 111, 114, 121, 47, 0, 0, 0, 0, 0, 0, 0, 0,
        ])
        .into();

        let rounds = vec![
            // First round,
            vec![
                (
                    key1.clone(),
                    nomt::KeyReadWrite::ReadThenWrite(
                        None,
                        Some(vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
                    ),
                ),
                (
                    key2.clone(),
                    nomt::KeyReadWrite::Write(Some(vec![
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0,
                    ])),
                ),
                (
                    key3.clone(),
                    nomt::KeyReadWrite::Write(Some(vec![0, 0, 0, 0, 0, 0, 0, 0])),
                ),
            ],
            // Second round,
            vec![
                (
                    key1.clone(),
                    nomt::KeyReadWrite::Read(Some(vec![
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                    ])),
                ),
                (
                    key2.clone(),
                    nomt::KeyReadWrite::Read(Some(vec![
                        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                        0, 0, 0, 0, 0, 0, 0,
                    ])),
                ),
                (
                    key3.clone(),
                    nomt::KeyReadWrite::Read(Some(vec![0, 0, 0, 0, 0, 0, 0, 0])),
                ),
            ],
        ];

        for nomt_accesses in rounds {
            println!("ACCESSES: {:?}", nomt_accesses);
            let session = nomt
                .begin_session(SessionParams::default().witness_mode(WitnessMode::read_write()));
            for (k, v) in &nomt_accesses {
                session.warm_up(k.clone());
                let val = session.read(k.clone()).unwrap();
                println!("ACTUAL VALUE: {:?}, EXPECTED VALUE {:?}", val, v);
            }

            let mut finished = session.finish(nomt_accesses).unwrap();
            let nomt_witness = finished.take_witness().expect("Witness cannot be missing");
            let nomt::Witness {
                path_proofs,
                operations: nomt::WitnessedOperations { .. },
            } = nomt_witness;
            // Note, we discard `p.path`, but maybe there's a way to use to have more efficient verification?
            let path_proofs_inner = path_proofs.into_iter().map(|p| p.inner).collect::<Vec<_>>();
            let multi_proof = nomt::proof::MultiProof::from_path_proofs(path_proofs_inner);
            println!("P LEN {}", multi_proof.paths.len());
        }
    }

    type H = sha2::Sha256;

    fn from_key(key: u64) -> (nomt::trie::KeyPath, Option<Vec<u8>>) {
        let raw_data = key.to_be_bytes();
        let key_path: nomt::trie::KeyPath = H::digest(&raw_data).into();
        (key_path, Some(raw_data.to_vec()))
    }

    struct NomtSessionBuilder {
        nomt: Arc<Nomt<BinaryHasher<H>>>,
        overlay_refs: Vec<u64>,
        snapshots: Arc<RwLock<HashMap<u64, nomt::Overlay>>>,
    }

    impl NomtSessionBuilder {
        fn begin_session(&self) -> Session<BinaryHasher<H>> {
            let params = {
                let mut overlays = Vec::with_capacity(self.overlay_refs.len());
                let snapshots = self.snapshots.read().expect("Snapshots lock poisoned");
                for overlay_ref in &self.overlay_refs {
                    let Some(state_overlay) = snapshots.get(overlay_ref) else {
                        println!(
                            "Cannot find snapshot from reference {}, assuming it has been committed",
                            overlay_ref,
                        );
                        continue;
                    };
                    overlays.push(state_overlay);
                }
                SessionParams::default()
                    .overlay(overlays)
                    .expect("Failed to build session params")
                    .witness_mode(WitnessMode::read_write())
            };
            self.nomt.begin_session(params)
        }
    }

    #[test]
    fn overlays_with_session_builder() {
        let dir = tempfile::tempdir().unwrap();
        let mut opts = Options::new();
        opts.path(dir.path().join("nomt_db"));
        opts.rollback(true);
        opts.max_rollback_log_len(1);
        opts.commit_concurrency(1);
        let nomt = std::sync::Arc::new(Nomt::<BinaryHasher<H>>::open(opts).unwrap());

        let all_overlays: HashMap<u64, Overlay> = HashMap::new();
        let all_overlays = Arc::new(RwLock::new(all_overlays));
        let rounds = 10;

        // First, build some overlays with data.
        for this_ref in 0..rounds {
            let mut overlay_refs = (0..this_ref).collect::<Vec<_>>();
            overlay_refs.reverse();
            let builder = NomtSessionBuilder {
                nomt: nomt.clone(),
                overlay_refs,
                snapshots: all_overlays.clone(),
            };

            let (key_path, data) = from_key(this_ref);
            let writes = vec![(key_path, nomt::KeyReadWrite::Write(data))];

            let session = builder.begin_session();

            let finished_session = session.finish(writes.clone()).unwrap();
            let overlay = finished_session.into_overlay();
            let mut overlays = all_overlays.write().unwrap();
            overlays.insert(this_ref, overlay);
        }

        let mut overlay_refs = (0..rounds).collect::<Vec<_>>();
        overlay_refs.reverse();
        let validator = NomtSessionBuilder {
            nomt: nomt.clone(),
            overlay_refs,
            snapshots: all_overlays.clone(),
        };

        for commiting_ref in 0..rounds {
            let validator_session = validator.begin_session();

            for checking_ref in 0..rounds {
                println!(
                    "Checking ref: {} At before commiting {}",
                    checking_ref, commiting_ref
                );
                let (key_path, expected_value) = from_key(checking_ref);
                let actual_value = validator_session.read(key_path).unwrap();
                assert_eq!(actual_value, expected_value);
            }

            let mut overlays = all_overlays.write().unwrap();
            let overlay_to_commit = overlays.remove(&commiting_ref).unwrap();
            drop(validator_session);
            overlay_to_commit.commit(&nomt).unwrap();
        }
    }

    #[test]
    fn overlays_with_session_builder_concurrent_reading() {
        let dir = tempfile::tempdir().unwrap();
        let mut opts = Options::new();
        opts.path(dir.path().join("nomt_db"));
        opts.rollback(true);
        opts.max_rollback_log_len(1);
        let nomt = std::sync::Arc::new(Nomt::<BinaryHasher<H>>::open(opts).unwrap());

        let all_overlays: HashMap<u64, Overlay> = HashMap::new();
        let all_overlays = Arc::new(RwLock::new(all_overlays));
        let overlays_count = 100;
        let parallel_readers = 10;
        let read_rounds = 1000;

        for this_ref in 0..overlays_count {
            let mut overlay_refs = (0..this_ref).collect::<Vec<_>>();
            overlay_refs.reverse();
            let builder = NomtSessionBuilder {
                nomt: nomt.clone(),
                overlay_refs,
                snapshots: all_overlays.clone(),
            };

            let (key_path, data) = from_key(this_ref);
            let writes = vec![(key_path, nomt::KeyReadWrite::Write(data))];

            let session = builder.begin_session();

            let finished_session = session.finish(writes.clone()).unwrap();
            let overlay = finished_session.into_overlay();
            let mut overlays = all_overlays.write().unwrap();
            overlays.insert(this_ref, overlay);
        }

        let mut handles = Vec::with_capacity(parallel_readers);

        for id in 0..parallel_readers {
            let reader_overlays = all_overlays.clone();
            let mut reader_refs = (0..overlays_count).collect::<Vec<_>>();
            reader_refs.reverse();

            let nomt_clone = nomt.clone();
            let handle = std::thread::spawn(move || {
                let reader = NomtSessionBuilder {
                    nomt: nomt_clone,
                    overlay_refs: reader_refs,
                    snapshots: reader_overlays,
                };
                let expected_values = (0..overlays_count).map(from_key).collect::<Vec<_>>();
                let start = std::time::Instant::now();
                println!("reader {} starts reading", id);
                // Check every value multiple times
                for _ in 0..read_rounds {
                    let session = reader.begin_session();
                    for (key_path, expected_value) in &expected_values {
                        let actual_value = session.read(*key_path).unwrap();
                        assert_eq!(&actual_value, expected_value);
                    }
                }
                println!("reader {} ends reading, took {:?}", id, start.elapsed());
            });

            handles.push(handle);
        }
        println!("Readers spawned, commiting");

        for commiting_ref in 0..(overlays_count - 1) {
            let mut overlays = all_overlays.write().unwrap();
            let overlay_to_commit = overlays.remove(&commiting_ref).unwrap();
            drop(overlays);
            overlay_to_commit.commit(&nomt).unwrap();
        }
        println!("Commiting done");

        for handle in handles {
            handle.join().unwrap();
        }
        println!("All readers joined");
    }

    #[test]
    fn random_read_no_impact() {
        let dir = tempfile::tempdir().unwrap();
        let mut opts = Options::new();
        opts.path(dir.path().join("nomt_db"));
        opts.commit_concurrency(1);
        let nomt = Nomt::<BinaryHasher<H>>::open(opts).unwrap();

        let key = b"key".to_vec();
        let key_path: KeyPath = sha2::Sha256::digest(&key).into();
        let value_1 = b"value_1".to_vec();
        // let value_1_hash = sha2::Sha256::digest(&value_1);
        let value_2 = b"value_2".to_vec();
        // let value_2_hash = sha2::Sha256::digest(&value_1);

        let writes = vec![value_1, value_2];

        for write in writes {
            let prev_root = nomt.root();
            // Building session
            let session = nomt
                .begin_session(SessionParams::default().witness_mode(WitnessMode::read_write()));
            session.warm_up(key_path);

            let actual_access: Vec<_> = vec![(
                key_path,
                // ADDING SOME RANDOM BYTES =)
                KeyReadWrite::ReadThenWrite(Some(vec![255, 255, 1, 2]), Some(write.clone())),
            )];

            let mut finished = session.finish(actual_access).unwrap();
            let witness = finished.take_witness().unwrap();
            let new_root = finished.root();
            finished.commit(&nomt).unwrap();

            // Verifying
            // Copied from examples
            let mut updates = Vec::new();
            // A witness is composed of multiple WitnessedPath objects,
            // which stores all the necessary information to verify the operations
            // performed on the same path
            for (i, witnessed_path) in witness.path_proofs.iter().enumerate() {
                // Constructing the verified operations
                let verified = witnessed_path
                    .inner
                    .verify::<BinaryHasher<Sha256>>(
                        &witnessed_path.path.path(),
                        prev_root.into_inner(),
                    )
                    .unwrap();

                for read in witness
                    .operations
                    .reads
                    .iter()
                    .skip_while(|r| r.path_index != i)
                    .take_while(|r| r.path_index == i)
                {
                    match read.value {
                        // Check for non-existence if the return value was None
                        None => assert!(verified.confirm_nonexistence(&read.key).unwrap()),
                        // Verify the correctness of the returned value when it is Some(_)
                        Some(value_hash) => {
                            let leaf = LeafData {
                                key_path: read.key,
                                value_hash,
                            };
                            assert!(verified.confirm_value(&leaf).unwrap());
                        }
                    }
                }

                let mut write_ops = Vec::new();
                for write in witness
                    .operations
                    .writes
                    .iter()
                    .skip_while(|r| r.path_index != i)
                    .take_while(|r| r.path_index == i)
                {
                    write_ops.push((write.key, write.value));
                }

                if !write_ops.is_empty() {
                    updates.push(proof::PathUpdate {
                        inner: verified,
                        ops: write_ops,
                    });
                }
            }

            assert_eq!(
                proof::verify_update::<BinaryHasher<sha2::Sha256>>(
                    prev_root.into_inner(),
                    &updates
                )
                .unwrap(),
                new_root.into_inner(),
            );
        }
    }
}
