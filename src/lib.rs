use nomt::hasher::Sha2Hasher;
use nomt::{Nomt, Options, Session, SessionParams, WitnessMode};

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
}

#[cfg(test)]
mod tests {}
