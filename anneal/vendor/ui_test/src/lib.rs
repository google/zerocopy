#![allow(
    clippy::enum_variant_names,
    clippy::useless_format,
    clippy::too_many_arguments,
    rustc::internal,
    // `unnameable_types` was stabilized in 1.79 which is higher than the current MSRV.
    // Ignore the "unknown lint" warning which is emitted on older versions.
    unknown_lints
)]
#![warn(unreachable_pub, unnameable_types)]
#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

use build_manager::BuildManager;
use build_manager::NewJob;
pub use color_eyre;
use color_eyre::eyre::eyre;
pub use color_eyre::eyre::Result;
pub use core::run_and_collect;
pub use core::CrateType;
use crossbeam_channel::Sender;
use crossbeam_channel::TryRecvError;
pub use filter::Match;
use per_test_config::TestConfig;
use spanned::Spanned;
use status_emitter::RevisionStyle;
use status_emitter::SilentStatus;
use status_emitter::{StatusEmitter, TestStatus};
use std::collections::VecDeque;
use std::panic::AssertUnwindSafe;
use std::path::Path;
#[cfg(feature = "rustc")]
use std::process::Command;
use std::sync::Arc;
use test_result::TestRun;
pub use test_result::{Errored, TestOk};

pub mod aux_builds;
pub mod build_manager;
mod cmd;
mod config;
pub mod core;
pub mod custom_flags;
#[cfg(feature = "rustc")]
pub mod dependencies;
pub mod diagnostics;
mod diff;
mod error;
pub mod filter;
#[cfg(feature = "gha")]
pub mod github_actions;
mod mode;
pub mod nextest;
mod parser;
pub mod per_test_config;
pub mod status_emitter;
pub mod test_result;

#[cfg(test)]
mod tests;

pub use cmd::*;
pub use config::*;
pub use error::*;
pub use parser::*;
pub use spanned;

/// Run all tests as described in the config argument.
/// Will additionally process command line arguments.
pub fn run_tests(mut config: Config) -> Result<()> {
    let args = Args::test()?;
    if let Format::Pretty = args.format {
        println!(
            "Compiler: {}",
            config.program.display().to_string().replace('\\', "/")
        );
    }

    #[cfg(feature = "gha")]
    let name = display(&config.root_dir);

    let emitter: Box<dyn StatusEmitter> = args.format.into();

    config.with_args(&args);

    run_tests_generic(
        vec![config],
        default_file_filter,
        default_per_file_config,
        (
            emitter,
            #[cfg(feature = "gha")]
            status_emitter::Gha { name, group: true },
        ),
    )
}

/// The filter used by `run_tests` to only run on `.rs` files that are
/// specified by [`Config::filter_files`] and [`Config::skip_files`].
///
/// Returns `None` if there is no extension or the extension is not `.rs`.
pub fn default_file_filter(path: &Path, config: &Config) -> Option<bool> {
    path.extension().filter(|&ext| ext == "rs")?;
    Some(default_any_file_filter(path, config))
}

/// Run on all files that are specified by [`Config::filter_files`] and
/// [`Config::skip_files`].
///
/// To only include rust files see [`default_file_filter`].
pub fn default_any_file_filter(path: &Path, config: &Config) -> bool {
    let path = display(path);
    let contains_path = |files: &[String]| {
        files.iter().any(|f| {
            if config.filter_exact {
                *f == path
            } else {
                path.contains(f)
            }
        })
    };

    if contains_path(&config.skip_files) {
        return false;
    }

    config.filter_files.is_empty() || contains_path(&config.filter_files)
}

/// The default per-file config used by `run_tests`.
pub fn default_per_file_config(config: &mut Config, file_contents: &Spanned<Vec<u8>>) {
    config.program.args.push(
        match CrateType::from_file_contents(file_contents) {
            CrateType::ProcMacro => "--crate-type=proc-macro",
            CrateType::Test => "--test",
            CrateType::Bin => return,
            CrateType::Lib => "--crate-type=lib",
        }
        .into(),
    )
}

/// Create a command for running a single file, with the settings from the `config` argument.
/// Ignores various settings from `Config` that relate to finding test files.
#[cfg(feature = "rustc")]
pub fn test_command(mut config: Config, path: &Path) -> Result<Command> {
    config.fill_host_and_target()?;

    let content = Spanned::read_from_file(path).transpose()?;
    let comments = Comments::parse(content.as_ref(), &config)
        .map_err(|errors| color_eyre::eyre::eyre!("{errors:#?}"))?;
    let config = TestConfig {
        config,
        comments: Arc::new(comments),
        aux_dir: path.parent().unwrap().join("auxiliary"),
        status: Box::new(SilentStatus {
            revision: String::new(),
            path: path.to_path_buf(),
        }),
    };
    let build_manager = BuildManager::new(config.config.clone(), crossbeam_channel::bounded(0).0);

    Ok(config.build_command(&build_manager).unwrap())
}

/// A version of `run_tests` that allows more fine-grained control over running tests.
///
/// All `configs` are being run in parallel.
/// If multiple configs are provided, the [`Config::threads`] value of the first one is used;
/// the thread count of all other configs is ignored.
/// The file filter is supposed to return `None` if it was filtered because of file extensions
/// and `Some(false)` if the file was rejected out of other reasons like the file path not matching
/// a user defined filter.
pub fn run_tests_generic(
    mut configs: Vec<Config>,
    file_filter: impl Fn(&Path, &Config) -> Option<bool> + Sync,
    per_file_config: impl Copy + Fn(&mut Config, &Spanned<Vec<u8>>) + Send + Sync + 'static,
    status_emitter: impl StatusEmitter,
) -> Result<()> {
    if nextest::emulate(&mut configs) {
        return Ok(());
    }

    for (i, config) in configs.iter_mut().enumerate() {
        config.fill_host_and_target()?;
        config.out_dir.push(i.to_string())
    }

    let mut results = vec![];

    let num_threads = match configs.first().and_then(|config| config.threads) {
        Some(threads) => threads,
        None => match std::env::var_os("RUST_TEST_THREADS") {
            Some(n) => n
                .to_str()
                .ok_or_else(|| eyre!("could not parse RUST_TEST_THREADS env var"))?
                .parse()?,
            None => std::thread::available_parallelism()?,
        },
    };

    let mut filtered = 0;
    core::run_and_collect(
        num_threads,
        |[submit, priority_submit]| {
            let mut todo = VecDeque::new();

            let configs: Vec<_> = configs
                .into_iter()
                .map(|config| Arc::new(BuildManager::new(config, priority_submit.clone())))
                .collect();
            for build_manager in &configs {
                todo.push_back((
                    build_manager.config().root_dir.clone(),
                    build_manager.clone(),
                ));
            }
            while let Some((path, build_manager)) = todo.pop_front() {
                if path.is_dir() {
                    if path.file_name().unwrap() == "auxiliary" {
                        continue;
                    }
                    // Enqueue everything inside this directory.
                    // We want it sorted, to have some control over scheduling of slow tests.
                    let mut entries = std::fs::read_dir(path)
                        .unwrap()
                        .map(|e| e.unwrap().path())
                        .collect::<Vec<_>>();
                    entries.sort_by(|a, b| a.file_name().cmp(&b.file_name()));
                    for entry in entries {
                        todo.push_back((entry, build_manager.clone()));
                    }
                } else if let Some(matched) = file_filter(&path, build_manager.config()) {
                    if matched {
                        let status = status_emitter.register_test(path.clone());
                        // Forward .rs files to the test workers.
                        submit
                            .send(Box::new(move |finished_files_sender: &Sender<TestRun>| {
                                let file_contents =
                                    Spanned::read_from_file(&path).transpose().unwrap();
                                let mut config = build_manager.config().clone();
                                let abort_check = config.abort_check.clone();
                                per_file_config(&mut config, &file_contents);
                                let status = AssertUnwindSafe(status);
                                let result = std::panic::catch_unwind(|| {
                                    let status = status;
                                    parse_and_test_file(
                                        build_manager,
                                        status.0,
                                        config,
                                        file_contents,
                                    )
                                });
                                let result = match result {
                                    Ok(Ok(res)) => res,
                                    Ok(Err((status, err))) => {
                                        finished_files_sender.send(TestRun {
                                            result: Err(err),
                                            status,
                                            abort_check,
                                        })?;
                                        return Ok(());
                                    }
                                    Err(err) => {
                                        finished_files_sender.send(TestRun {
                                            result: Err(Errored {
                                                command: "<unknown>".into(),
                                                errors: vec![Error::Bug(
                                                            *Box::<
                                                                dyn std::any::Any + Send + 'static,
                                                            >::downcast::<String>(
                                                                err
                                                            )
                                                            .unwrap(),
                                                        )],
                                                stderr: vec![],
                                                stdout: vec![],
                                            }),
                                            status: Box::new(SilentStatus {
                                                revision: String::new(),
                                                path,
                                            }),
                                            abort_check,
                                        })?;
                                        return Ok(());
                                    }
                                };
                                for result in result {
                                    finished_files_sender.send(result)?;
                                }
                                Ok(())
                            }) as NewJob)
                            .unwrap();
                    } else {
                        filtered += 1;
                    }
                }
            }
        },
        |[receive, priority_receive], finished_files_sender| -> Result<()> {
            loop {
                for closure in priority_receive.try_iter() {
                    closure(&finished_files_sender)?;
                }
                match receive.try_recv() {
                    Ok(closure) => {
                        closure(&finished_files_sender)?;
                    }
                    Err(TryRecvError::Empty) => {}
                    Err(TryRecvError::Disconnected) => {
                        for closure in priority_receive {
                            closure(&finished_files_sender)?;
                        }
                        return Ok(());
                    }
                }
            }
        },
        |finished_files_recv| {
            for run in finished_files_recv {
                let aborted = run.abort_check.aborted();
                run.status.done(&run.result, aborted);

                // Do not write summaries for cancelled tests
                if !aborted {
                    results.push(run);
                }
            }
        },
    )?;

    let mut failures = vec![];
    let mut succeeded = 0;
    let mut ignored = 0;
    let mut aborted = false;

    for run in results {
        aborted |= run.abort_check.aborted();
        match run.result {
            Ok(TestOk::Ok) => succeeded += 1,
            Ok(TestOk::Ignored) => ignored += 1,
            Err(errored) => failures.push((run.status, errored)),
        }
    }

    let mut failure_emitter =
        status_emitter.finalize(failures.len(), succeeded, ignored, filtered, aborted);
    for (
        status,
        Errored {
            command,
            errors,
            stderr,
            stdout,
        },
    ) in &failures
    {
        let _guard = status.failed_test(command, stderr, stdout);
        failure_emitter.test_failure(status, errors);
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(eyre!("tests failed"))
    }
}

fn parse_and_test_file(
    build_manager: Arc<BuildManager>,
    status: Box<dyn TestStatus>,
    config: Config,
    file_contents: Spanned<Vec<u8>>,
) -> Result<Vec<TestRun>, (Box<dyn TestStatus>, Errored)> {
    let comments = match Comments::parse(file_contents.as_ref(), &config) {
        Ok(t) => t,
        Err(errors) => return Err((status, Errored::new(errors, "parse comments"))),
    };
    let comments = Arc::new(comments);
    // Run the test for all revisions
    let mut runs = vec![];
    for i in 0.. {
        match comments.revisions.as_deref() {
            Some(revisions) => {
                let Some(revision) = revisions.get(i) else {
                    status.done(&Ok(TestOk::Ok), build_manager.aborted());
                    break;
                };
                let status = status.for_revision(revision, RevisionStyle::Show);
                test_file(&config, &comments, status, &mut runs, &build_manager)
            }
            None => {
                test_file(&config, &comments, status, &mut runs, &build_manager);
                break;
            }
        }
    }
    Ok(runs)
}

fn test_file(
    config: &Config,
    comments: &Arc<Comments>,
    status: Box<dyn TestStatus>,
    runs: &mut Vec<TestRun>,
    build_manager: &Arc<BuildManager>,
) {
    if !config.test_file_conditions(comments, status.revision()) {
        runs.push(TestRun {
            result: Ok(TestOk::Ignored),
            status,
            abort_check: config.abort_check.clone(),
        });
        return;
    }
    let mut test_config = TestConfig {
        config: config.clone(),
        comments: comments.clone(),
        aux_dir: status.path().parent().unwrap().join("auxiliary"),
        status,
    };
    let result = test_config.run_test(build_manager);
    // Ignore file if only/ignore rules do (not) apply

    runs.push(TestRun {
        result,
        status: test_config.status,
        abort_check: test_config.config.abort_check,
    });
}

fn display(path: &Path) -> String {
    path.display().to_string().replace('\\', "/")
}
