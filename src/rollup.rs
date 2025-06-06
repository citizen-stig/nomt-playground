#![allow(dead_code)]
use nomt::hasher::Sha2Hasher;
use nomt::trie::KeyPath;
use nomt::{
    FinishedSession, KeyReadWrite, Nomt, Options, Overlay, Session, SessionParams, WitnessMode,
};
use sha2::Digest;
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

#[test]
fn handling_web_thread() {
    let dir = tempfile::tempdir().unwrap();
    let mut opts = Options::new();
    opts.path(dir.path().join("nomt_db"));
    opts.commit_concurrency(1);
    let nomt = Nomt::<Sha2Hasher>::open(opts).unwrap();

    let key = b"key".to_vec();
    let key_path: KeyPath = sha2::Sha256::digest(&key).into();

    let blocks: u64 = 20;
    let finality: u64 = 3;

    let mut overlays = VecDeque::with_capacity(finality as usize);

    let build_session = |current_overlays: &VecDeque<Overlay>| {
        println!("Building session from {} overlays", current_overlays.len());
        let params = SessionParams::default()
            .overlay(current_overlays.iter().rev())
            .unwrap()
            .witness_mode(WitnessMode::read_write());
        nomt.begin_session(params)
    };

    // This background task represents "web" storage, which works in the background to the main thread.
    let mut web_session = build_session(&overlays);
    let (web_session_sender, web_session_receiver) =
        std::sync::mpsc::channel::<(Session<Sha2Hasher>, Option<Vec<u8>>)>();
    let background_task_handle = std::thread::spawn(move || {
        println!("Background task started: Listening for sequencer updates and shutdown signal.");
        let initial_value = web_session.read(key_path.clone()).unwrap();
        assert_eq!(initial_value, None);
        for _ in 0..blocks {
            let (session, expected_value) = web_session_receiver.recv().unwrap();
            web_session = session;
            println!("Web storage received");
            let value = web_session.read(key_path).unwrap();
            assert_eq!(expected_value, value);
            println!("Web storage actual   value: {:?}", value);
            println!("Web storage expected value: {:?}", expected_value);
        }
    });

    // This loop represents the main execution thread.
    for height in 0..blocks {
        let session = build_session(&overlays);
        session.warm_up(key_path);

        let expected_value = height.checked_sub(1).map(|v| v.to_be_bytes().to_vec());
        let actual_value = session.read(key_path).unwrap();
        println!("Height {} Actual Value: {:?}", height, actual_value);
        assert_eq!(actual_value, expected_value);

        let written_value = Some(height.to_be_bytes().to_vec());
        let accesses = vec![(key_path, nomt::KeyReadWrite::Write(written_value.clone()))];
        let finished_session = session.finish(accesses).expect("finish failed");
        overlays.push_back(finished_session.into_overlay());

        // Build after committing
        let web_session = build_session(&overlays);
        web_session_sender
            .send((web_session, written_value))
            .unwrap();

        if let Some(f_height) = height.checked_sub(finality) {
            println!(
                "H {}:Finalizing overlay at supposed height {}",
                height, f_height
            );
            let oldest_overlay = overlays.pop_front().unwrap();
            oldest_overlay.commit(&nomt).unwrap();
            println!(
                "H {}: Overlays after finalization: {}",
                height,
                overlays.len()
            );
        }
        // Build after committing
        // let web_session = build_session(&overlays);
        // web_session_sender
        //     .send((web_session, written_value))
        //     .unwrap();
    }

    background_task_handle.join().unwrap();
    println!("Completed");
}

#[derive(Clone)]
struct ClonableSession {
    session: Arc<Mutex<Option<Session<Sha2Hasher>>>>,
}

#[derive(Clone)]
struct SessionBuilder {
    overlays: Vec<Arc<Overlay>>,
    nomt: Arc<Nomt<Sha2Hasher>>,
}

impl SessionBuilder {
    pub fn new_session(&self) -> Session<Sha2Hasher> {
        let params = SessionParams::default()
            .overlay(self.overlays.iter().map(|a| a.as_ref()))
            .unwrap()
            .witness_mode(WitnessMode::read_write());
        self.nomt.begin_session(params)
    }
}

struct ProverProtoDesign {
    current_session: Session<Sha2Hasher>,
    builder: SessionBuilder,
}

impl Clone for ProverProtoDesign {
    fn clone(&self) -> Self {
        let new_session = self.builder.new_session();
        Self {
            current_session: new_session,
            builder: self.builder.clone(),
        }
    }
}

impl ClonableSession {
    fn new(session: Session<Sha2Hasher>) -> Self {
        Self {
            session: Arc::new(Mutex::new(Some(session))),
        }
    }

    fn finish(self, actuals: Vec<(KeyPath, KeyReadWrite)>) -> FinishedSession {
        let mut session_lock = self.session.lock().unwrap();
        let session = session_lock.take().unwrap();

        session.finish(actuals).unwrap()
    }

    fn ref_count(&self) {
        println!("Strong count: {}", Arc::strong_count(&self.session));
        println!("Weak count: {}", Arc::weak_count(&self.session));
    }

    fn read(&self, key: KeyPath) -> Option<Vec<u8>> {
        let session_lock = self.session.lock().unwrap();
        let session = session_lock.as_ref().unwrap();
        session.warm_up(key);
        session.read(key).unwrap()
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn handling_web_thread_with_tokio() {
    let dir = tempfile::tempdir().unwrap();
    let mut opts = Options::new();
    opts.path(dir.path().join("nomt_db"));
    opts.commit_concurrency(1);
    let nomt = Nomt::<Sha2Hasher>::open(opts).unwrap();

    let key = b"key".to_vec();
    let key_path: KeyPath = sha2::Sha256::digest(&key).into();

    let blocks: u64 = 20;
    let finality: u64 = 3;

    let mut overlays = VecDeque::with_capacity(finality as usize);

    let build_session = |current_overlays: &VecDeque<Overlay>| {
        println!("Building session from {} overlays", current_overlays.len());
        let params = SessionParams::default()
            .overlay(current_overlays.iter().rev())
            .unwrap()
            .witness_mode(WitnessMode::read_write());
        ClonableSession::new(nomt.begin_session(params))
    };

    // This background task represents "web" storage, which works in the background to the main thread.
    let web_storage = build_session(&overlays);
    let (web_session_sender, mut web_storage_receiver) =
        tokio::sync::watch::channel((web_storage, None));

    let background_task_handle = tokio::spawn(async move {
        println!("Background task started: Listening for web storage updates and shutdown signal.");
        //
        let mut i = 0;
        while i < blocks {
            match web_storage_receiver.changed().await {
                Ok(_) => {
                    println!("Web storage received");
                    let (storage, expected_value) = (*web_storage_receiver.borrow()).clone();
                    storage.ref_count();
                    let value = storage.read(key_path);
                    println!("Web storage actual   value: {:?}", value);
                    println!("Web storage expected value: {:?}", expected_value);
                    assert_eq!(expected_value, value);
                    i += 1;
                }
                Err(e) => {
                    println!("Web storage error: {:?}", e);
                }
            }
        }
    });

    // Main thread
    for height in 0..blocks {
        let session = build_session(&overlays);

        let expected_value = height.checked_sub(1).map(|v| v.to_be_bytes().to_vec());
        let actual_value = session.read(key_path);
        println!("Height {} Actual Value: {:?}", height, actual_value);
        assert_eq!(actual_value, expected_value);

        let written_value = Some(height.to_be_bytes().to_vec());
        let accesses = vec![(key_path, nomt::KeyReadWrite::Write(written_value.clone()))];
        let finished_session = session.finish(accesses);
        overlays.push_back(finished_session.into_overlay());

        let web_session = build_session(&overlays);
        web_session_sender
            .send((web_session, written_value))
            .unwrap();

        // if finalization is enabled, `oldest_overlay.commit`
        if let Some(f_height) = height.checked_sub(finality) {
            println!(
                "H {}:Finalizing overlay at supposed height {}",
                height, f_height
            );
            let oldest_overlay = overlays.pop_front().unwrap();
            // Blocks here because..
            oldest_overlay.commit(&nomt).unwrap();
            println!(
                "H {}: Overlays after finalization: {}",
                height,
                overlays.len()
            );
        }
    }

    background_task_handle.await.unwrap();
    println!("Completed");
}

// BEFORE: WEB STORAGE []
// LOOP 0: PRODUCE SNAPSHOT 1, SAVED TO SNAPSHOTS, WEB STORAGE [SNAP1,] in channel
// LOOP 1: PRODUCE SNAPSHOT 2, SAVED TO SNAPSHOTS, WEB STORAGE [SNAP1,SNAP2] in channel
// LOOP 2: PRODUCE SNAPSHOT 3, SAVED TO SNAPSHOTS, WEB STORAGE [SNAP1,SNAP2,SNAP3] in channel
// LOOP 3: PRODUCE SNAPSHOT 4, SAVED TO SNAPSHOTS, TRY TO FINALIZE SNAPSHOT 1

struct Channel<T> {
    values: Mutex<Option<T>>,
    notify: tokio::sync::Notify,
}

impl<T> Channel<T> {
    pub fn new(initial_value: T) -> Self {
        Self {
            values: Mutex::new(Some(initial_value)),
            notify: tokio::sync::Notify::new(),
        }
    }

    pub fn send(&self, value: T) {
        self.values.lock().unwrap().replace(value);

        // Notify the consumer a value is available
        self.notify.notify_one();
    }

    // This is a single-consumer channel, so several concurrent calls to
    // `recv` are not allowed.
    pub async fn recv(&self) -> T {
        loop {
            // Drain values
            if let Some(value) = self.values.lock().unwrap().take() {
                return value;
            }

            // Wait for values to be available
            self.notify.notified().await;
        }
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn handling_web_thread_with_tokio_with_mutex() {
    let dir = tempfile::tempdir().unwrap();
    let mut opts = Options::new();
    opts.path(dir.path().join("nomt_db"));
    opts.commit_concurrency(1);
    let nomt = Nomt::<Sha2Hasher>::open(opts).unwrap();

    let key = b"key".to_vec();
    let key_path: KeyPath = sha2::Sha256::digest(&key).into();

    let blocks: u64 = 20;
    let finality: u64 = 3;

    let mut overlays = VecDeque::with_capacity(finality as usize);

    let build_session = |current_overlays: &VecDeque<Overlay>| {
        println!("Building session from {} overlays", current_overlays.len());
        let params = SessionParams::default()
            .overlay(current_overlays.iter().rev())
            .unwrap()
            .witness_mode(WitnessMode::read_write());
        ClonableSession::new(nomt.begin_session(params))
    };

    // This background task represents "web" storage, which works in the background to the main thread.
    let web_storage = build_session(&overlays);

    let web_storage_sender: Arc<Channel<(ClonableSession, Option<Vec<u8>>)>> =
        Arc::new(Channel::new((web_storage, None)));

    let web_storage_receiver = web_storage_sender.clone();

    let background_task_handle = tokio::spawn(async move {
        println!("Background task started: Listening for web storage updates and shutdown signal.");
        for _ in 0..blocks {
            let (storage, expected_value) = web_storage_receiver.recv().await;
            storage.ref_count();
            let value = storage.read(key_path);
            println!("Web storage actual   value: {:?}", value);
            println!("Web storage expected value: {:?}", expected_value);
            assert_eq!(expected_value, value);
        }
    });

    // Main thread
    for height in 0..blocks {
        let session = build_session(&overlays);

        let expected_value = height.checked_sub(1).map(|v| v.to_be_bytes().to_vec());
        let actual_value = session.read(key_path);
        println!("Height {} Actual Value: {:?}", height, actual_value);
        assert_eq!(actual_value, expected_value);

        let written_value = Some(height.to_be_bytes().to_vec());
        let accesses = vec![(key_path, nomt::KeyReadWrite::Write(written_value.clone()))];
        let finished_session = session.finish(accesses);
        overlays.push_back(finished_session.into_overlay());

        // if finalization is enabled, `oldest_overlay.commit`
        if let Some(f_height) = height.checked_sub(finality) {
            println!(
                "H {}:Finalizing overlay at supposed height {}",
                height, f_height
            );
            let oldest_overlay = overlays.pop_front().unwrap();
            // Blocks here because..
            oldest_overlay.commit(&nomt).unwrap();
            println!(
                "H {}: Overlays after finalization: {}",
                height,
                overlays.len()
            );
        }

        let web_session = build_session(&overlays);
        web_storage_sender.send((web_session, written_value));
    }

    background_task_handle.await.unwrap();
    println!("Completed");
}
