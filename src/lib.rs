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
    nomt::proof::verify_update::<Sha2Hasher>(prev_root, &updates)
        .expect("update verification failed")
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

        assert_eq!(
            verifier_root,
            prover_root.into_inner(),
            "verifier root does not match prover root"
        );
        nomt_container.commit(finished_session);
        println!("===== Round {} completed", idx + 1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_node_rounds() {
        run_test_case(TestCase::rounds_of_same_key());
    }
}
