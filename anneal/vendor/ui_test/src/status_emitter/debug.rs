//! A debug emitter for when things get stuck. Mostly useful for debugging of ui_test itself

use crate::Error;
use std::path::{Path, PathBuf};

/// Very verbose status emitter
pub struct StatusEmitter;

impl super::StatusEmitter for StatusEmitter {
    fn register_test(&self, path: PathBuf) -> Box<dyn super::TestStatus + 'static> {
        eprintln!("START {}", path.display());
        Box::new(TestStatus(path, String::new()))
    }

    fn finalize(
        &self,
        failed: usize,
        succeeded: usize,
        ignored: usize,
        filtered: usize,
        aborted: bool,
    ) -> Box<dyn super::Summary> {
        eprintln!("{failed}, {succeeded}, {ignored}, {filtered}, {aborted}");
        Box::new(Summary)
    }
}

struct Summary;

impl super::Summary for Summary {
    fn test_failure(&mut self, status: &dyn super::TestStatus, errors: &Vec<Error>) {
        eprintln!(
            "FAILED: {} ({})",
            status.path().display(),
            status.revision()
        );
        eprintln!("{errors:#?}");
    }
}

struct TestStatus(PathBuf, String);

impl super::TestStatus for TestStatus {
    fn for_revision(
        &self,
        revision: &str,
        _style: super::RevisionStyle,
    ) -> Box<dyn super::TestStatus> {
        eprintln!(
            "REVISION {}: {} (old: {})",
            self.0.display(),
            revision,
            self.1
        );
        Box::new(TestStatus(self.0.clone(), revision.to_string()))
    }

    fn for_path(&self, path: &Path) -> Box<dyn super::TestStatus> {
        eprintln!(
            "PATH {} (old: {} ({}))",
            path.display(),
            self.0.display(),
            self.1
        );
        Box::new(TestStatus(path.to_owned(), String::new()))
    }

    fn failed_test<'a>(
        &'a self,
        cmd: &'a str,
        stderr: &'a [u8],
        stdout: &'a [u8],
    ) -> Box<dyn std::fmt::Debug + 'a> {
        eprintln!("failed {} ({})", self.0.display(), self.1);
        eprintln!("{cmd}");
        eprintln!("{}", std::str::from_utf8(stderr).unwrap());
        eprintln!("{}", std::str::from_utf8(stdout).unwrap());
        eprintln!();
        Box::new(())
    }

    fn path(&self) -> &Path {
        &self.0
    }

    fn revision(&self) -> &str {
        &self.1
    }
}

impl Drop for TestStatus {
    fn drop(&mut self) {
        eprintln!("DONE {} ({})", self.0.display(), self.1);
    }
}
