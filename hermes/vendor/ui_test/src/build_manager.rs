//! Auxiliary and dependency builder. Extendable to custom builds.

use crate::{
    per_test_config::TestConfig,
    status_emitter::{RevisionStyle, TestStatus},
    test_result::{TestResult, TestRun},
    Config, Errored,
};
use color_eyre::eyre::Result;
use crossbeam_channel::{bounded, Sender};
use std::{
    collections::{hash_map::Entry, HashMap},
    ffi::OsString,
    sync::{Arc, OnceLock, RwLock},
};

/// A build shared between all tests of the same `BuildManager`
pub trait Build {
    /// Runs the build and returns command line args to add to the test so it can find
    /// the built things.
    fn build(&self, build_manager: &BuildManager) -> Result<Vec<OsString>, Errored>;
    /// Must uniquely describe the build, as it is used for checking that a value
    /// has already been cached.
    fn description(&self) -> String;
}

/// Deduplicates builds
pub struct BuildManager {
    #[allow(clippy::type_complexity)]
    cache: RwLock<HashMap<String, Arc<OnceLock<Result<Vec<OsString>, ()>>>>>,
    pub(crate) config: Config,
    new_job_submitter: Sender<NewJob>,
}

/// Type of closure that is used to run individual tests.
pub type NewJob = Box<dyn Send + for<'a> FnOnce(&'a Sender<TestRun>) -> Result<()>>;

impl BuildManager {
    /// Create a new `BuildManager` for a specific `Config`. Each `Config` needs
    /// to have its own.
    pub fn new(config: Config, new_job_submitter: Sender<NewJob>) -> Self {
        Self {
            cache: Default::default(),
            config,
            new_job_submitter,
        }
    }

    /// Create a new `BuildManager` that cannot create new sub-jobs.
    pub fn one_off(config: Config) -> Self {
        Self::new(config, bounded(0).0)
    }

    /// Lazily add more jobs after a test has finished. These are added to the queue
    /// as normally, but nested below the test.
    pub fn add_new_job(
        &self,
        mut config: TestConfig,
        job: impl Send + 'static + FnOnce(&mut TestConfig) -> TestResult,
    ) {
        if self.aborted() {
            return;
        }
        self.new_job_submitter
            .send(Box::new(move |sender| {
                let result = job(&mut config);
                let result = TestRun {
                    result,
                    status: config.status,
                    abort_check: config.config.abort_check,
                };
                Ok(sender.send(result)?)
            }))
            .unwrap()
    }

    /// This function will block until the build is done and then return the arguments
    /// that need to be passed in order to build the dependencies.
    /// The error is only reported once, all follow up invocations of the same build will
    /// have a generic error about a previous build failing.
    pub fn build(
        &self,
        what: impl Build,
        status: &dyn TestStatus,
    ) -> Result<Vec<OsString>, Errored> {
        let description = what.description();
        // Fast path without much contention.
        if let Some(res) = self
            .cache
            .read()
            .unwrap()
            .get(&description)
            .and_then(|o| o.get())
        {
            return res.clone().map_err(|()| Errored {
                command: format!("{description:?}"),
                errors: vec![],
                stderr: b"previous build failed".to_vec(),
                stdout: vec![],
            });
        }
        let mut lock = self.cache.write().unwrap();
        let once = match lock.entry(description) {
            Entry::Occupied(entry) => {
                if let Some(res) = entry.get().get() {
                    return res.clone().map_err(|()| Errored {
                        command: format!("{:?}", what.description()),
                        errors: vec![],
                        stderr: b"previous build failed".to_vec(),
                        stdout: vec![],
                    });
                }
                entry.get().clone()
            }
            Entry::Vacant(entry) => {
                let once = Arc::new(OnceLock::new());
                entry.insert(once.clone());
                once
            }
        };
        drop(lock);

        let mut err = None;
        once.get_or_init(|| {
            let description = what.description();
            let build = status.for_revision(&description, RevisionStyle::Separate);
            let res = what.build(self).map_err(|e| err = Some(e));
            build.done(
                &res.as_ref()
                    .map(|_| crate::test_result::TestOk::Ok)
                    .map_err(|()| Errored {
                        command: description,
                        errors: vec![],
                        stderr: vec![],
                        stdout: vec![],
                    }),
                self.aborted(),
            );
            res
        })
        .clone()
        .map_err(|()| {
            err.unwrap_or_else(|| Errored {
                command: what.description(),
                errors: vec![],
                stderr: b"previous build failed".to_vec(),
                stdout: vec![],
            })
        })
    }

    /// The `Config` used for all builds.
    pub fn config(&self) -> &Config {
        &self.config
    }

    /// Whether the build was cancelled
    pub fn aborted(&self) -> bool {
        self.config.abort_check.aborted()
    }
}
