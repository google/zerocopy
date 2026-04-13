//! Various schemes for reporting messages during testing or after testing is done.
//!
//! The testing framework employs the implementations of the various emitter traits
//! as follows:
//!
//! The framework first creates an instance of a `StatusEmitter`.
//!
//! The framework then searches for tests in its perview, and if it finds one, it
//! calls `StatusEmitter::register_test()` to obtain a `TestStatus` for that test.
//! The tests are then executed in an asynchonous manner.
//!
//! Once a single test finish executing, the framework calls `TestStatus::done()`.
//!
//! Once all tests finish executing, the framework calls `StatusEmitter::finalize()`
//! to obtain a Summary.
//!
//! For each failed test, the framework calls both `TestStatus::failed_test()` and
//! `Summary::test_failure()`.

use crate::{test_result::TestResult, Errors, Format};

use std::{
    boxed::Box,
    fmt::Debug,
    panic::RefUnwindSafe,
    path::{Path, PathBuf},
};
pub mod debug;
#[cfg(feature = "gha")]
pub use gha::*;
#[cfg(feature = "gha")]
mod gha;
pub use json::*;
mod json;
pub use text::*;
mod text;

/// A generic way to handle the output of this crate.
pub trait StatusEmitter: Send + Sync + RefUnwindSafe {
    /// Invoked the moment we know a test will later be run.
    /// Useful for progress bars and such.
    fn register_test(&self, path: PathBuf) -> Box<dyn TestStatus + 'static>;

    /// Create a report about the entire test run at the end.
    #[allow(clippy::type_complexity)]
    fn finalize(
        &self,
        failed: usize,
        succeeded: usize,
        ignored: usize,
        filtered: usize,
        aborted: bool,
    ) -> Box<dyn Summary>;
}

impl From<Format> for Box<dyn StatusEmitter> {
    fn from(format: Format) -> Box<dyn StatusEmitter> {
        match format {
            Format::JSON => Box::new(JSON::new()),
            Format::Pretty => Box::new(Text::verbose()),
            Format::Terse => Box::new(Text::quiet()),
        }
    }
}

/// Some configuration options for revisions
#[derive(Debug, Clone, Copy)]
pub enum RevisionStyle {
    /// Things like dependencies or aux files building are not really nested
    /// below the build, but it is waiting on it.
    Separate,
    /// Always show them, even if rendering to a file
    Show,
}

/// Information about a specific test run.
pub trait TestStatus: Send + Sync + RefUnwindSafe {
    /// Create a copy of this test for a new revision.
    fn for_revision(&self, revision: &str, style: RevisionStyle) -> Box<dyn TestStatus>;

    /// Create a copy of this test for a new path.
    fn for_path(&self, path: &Path) -> Box<dyn TestStatus>;

    /// Invoked before each failed test prints its errors along with a drop guard that can
    /// get invoked afterwards.
    fn failed_test<'a>(
        &'a self,
        cmd: &'a str,
        stderr: &'a [u8],
        stdout: &'a [u8],
    ) -> Box<dyn Debug + 'a>;

    /// A test has finished, handle the result immediately.
    fn done(&self, _result: &TestResult, _aborted: bool) {}

    /// The path of the test file.
    fn path(&self) -> &Path;

    /// The revision, usually an empty string.
    fn revision(&self) -> &str;
}

/// Report a summary at the end of a test run.
pub trait Summary {
    /// A test has finished, handle the result.
    fn test_failure(&mut self, _status: &dyn TestStatus, _errors: &Errors) {}
}

/// Report no summary
impl Summary for () {}

/// Emit nothing
impl StatusEmitter for () {
    fn register_test(&self, path: PathBuf) -> Box<dyn TestStatus> {
        Box::new(SilentStatus {
            path,
            revision: String::new(),
        })
    }

    fn finalize(
        &self,
        _failed: usize,
        _succeeded: usize,
        _ignored: usize,
        _filtered: usize,
        _aborted: bool,
    ) -> Box<dyn Summary> {
        Box::new(())
    }
}

/// When you need a dummy value that doesn't actually print anything
pub struct SilentStatus {
    /// Forwarded to `TestStatus::revision`
    pub revision: String,
    /// Forwarded to `TestStatus::path`
    pub path: PathBuf,
}

impl TestStatus for SilentStatus {
    fn for_revision(&self, revision: &str, _style: RevisionStyle) -> Box<dyn TestStatus> {
        Box::new(SilentStatus {
            revision: revision.into(),
            path: self.path.clone(),
        })
    }

    fn for_path(&self, path: &Path) -> Box<dyn TestStatus> {
        Box::new(SilentStatus {
            revision: self.revision.clone(),
            path: path.to_path_buf(),
        })
    }

    fn failed_test<'a>(
        &'a self,
        _cmd: &'a str,
        _stderr: &'a [u8],
        _stdout: &'a [u8],
    ) -> Box<dyn Debug + 'a> {
        Box::new(())
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn revision(&self) -> &str {
        &self.revision
    }
}

impl<T: TestStatus, U: TestStatus> TestStatus for (T, U) {
    fn done(&self, result: &TestResult, aborted: bool) {
        self.0.done(result, aborted);
        self.1.done(result, aborted);
    }

    fn failed_test<'a>(
        &'a self,
        cmd: &'a str,
        stderr: &'a [u8],
        stdout: &'a [u8],
    ) -> Box<dyn Debug + 'a> {
        Box::new((
            self.0.failed_test(cmd, stderr, stdout),
            self.1.failed_test(cmd, stderr, stdout),
        ))
    }

    fn path(&self) -> &Path {
        let path = self.0.path();
        assert_eq!(path, self.1.path());
        path
    }

    fn revision(&self) -> &str {
        let rev = self.0.revision();
        assert_eq!(rev, self.1.revision());
        rev
    }

    fn for_revision(&self, revision: &str, style: RevisionStyle) -> Box<dyn TestStatus> {
        Box::new((
            self.0.for_revision(revision, style),
            self.1.for_revision(revision, style),
        ))
    }

    fn for_path(&self, path: &Path) -> Box<dyn TestStatus> {
        Box::new((self.0.for_path(path), self.1.for_path(path)))
    }
}

impl<T: StatusEmitter, U: StatusEmitter> StatusEmitter for (T, U) {
    fn register_test(&self, path: PathBuf) -> Box<dyn TestStatus> {
        Box::new((
            self.0.register_test(path.clone()),
            self.1.register_test(path),
        ))
    }

    fn finalize(
        &self,
        failures: usize,
        succeeded: usize,
        ignored: usize,
        filtered: usize,
        aborted: bool,
    ) -> Box<dyn Summary> {
        Box::new((
            self.1
                .finalize(failures, succeeded, ignored, filtered, aborted),
            self.0
                .finalize(failures, succeeded, ignored, filtered, aborted),
        ))
    }
}

/// Forwards directly to `T`, exists only so that tuples can be used with `cfg` to filter
/// out individual fields
impl<T: StatusEmitter> StatusEmitter for (T,) {
    fn register_test(&self, path: PathBuf) -> Box<dyn TestStatus> {
        self.0.register_test(path.clone())
    }

    fn finalize(
        &self,
        failures: usize,
        succeeded: usize,
        ignored: usize,
        filtered: usize,
        aborted: bool,
    ) -> Box<dyn Summary> {
        self.0
            .finalize(failures, succeeded, ignored, filtered, aborted)
    }
}

impl<T: TestStatus + ?Sized> TestStatus for Box<T> {
    fn done(&self, result: &TestResult, aborted: bool) {
        (**self).done(result, aborted);
    }

    fn path(&self) -> &Path {
        (**self).path()
    }

    fn revision(&self) -> &str {
        (**self).revision()
    }

    fn for_revision(&self, revision: &str, style: RevisionStyle) -> Box<dyn TestStatus> {
        (**self).for_revision(revision, style)
    }

    fn for_path(&self, path: &Path) -> Box<dyn TestStatus> {
        (**self).for_path(path)
    }

    fn failed_test<'a>(
        &'a self,
        cmd: &'a str,
        stderr: &'a [u8],
        stdout: &'a [u8],
    ) -> Box<dyn Debug + 'a> {
        (**self).failed_test(cmd, stderr, stdout)
    }
}

impl<T: StatusEmitter + ?Sized> StatusEmitter for Box<T> {
    fn register_test(&self, path: PathBuf) -> Box<dyn TestStatus> {
        (**self).register_test(path)
    }

    fn finalize(
        &self,
        failures: usize,
        succeeded: usize,
        ignored: usize,
        filtered: usize,
        aborted: bool,
    ) -> Box<dyn Summary> {
        (**self).finalize(failures, succeeded, ignored, filtered, aborted)
    }
}

impl Summary for (Box<dyn Summary>, Box<dyn Summary>) {
    fn test_failure(&mut self, status: &dyn TestStatus, errors: &Errors) {
        self.0.test_failure(status, errors);
        self.1.test_failure(status, errors);
    }
}
