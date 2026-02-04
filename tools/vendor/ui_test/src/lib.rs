#![allow(
    clippy::enum_variant_names,
    clippy::useless_format,
    clippy::too_many_arguments,
    rustc::internal
)]
#![deny(missing_docs)]

//! A crate to run the Rust compiler (or other binaries) and test their command line output.

use build_manager::BuildManager;
pub use color_eyre;
use color_eyre::eyre::eyre;
#[cfg(feature = "rustc")]
use color_eyre::eyre::Context as _;
pub use color_eyre::eyre::Result;
pub use core::run_and_collect;
pub use core::CrateType;
pub use filter::Match;
use per_test_config::TestConfig;
use spanned::Spanned;
use status_emitter::{StatusEmitter, TestStatus};
use std::collections::VecDeque;
use std::path::Path;
use std::process::Command;
use test_result::TestRun;
pub use test_result::{Errored, TestOk};

use crate::parser::Comments;

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
pub mod github_actions;
mod mode;
pub mod nextest;
mod parser;
pub mod per_test_config;
#[cfg(feature = "rustc")]
mod rustc_stderr;
pub mod status_emitter;
pub mod test_result;

#[cfg(test)]
mod tests;

pub use cmd::*;
pub use config::*;
pub use error::*;

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

    let name = display(&config.root_dir);

    let text = match args.format {
        Format::Terse => status_emitter::Text::quiet(),
        Format::Pretty => status_emitter::Text::verbose(),
    };
    config.with_args(&args);

    run_tests_generic(
        vec![config],
        default_file_filter,
        default_per_file_config,
        (text, status_emitter::Gha::<true> { name }),
    )
}

/// The filter used by `run_tests` to only run on `.rs` files that are
/// specified by [`Config::filter_files`] and [`Config::skip_files`].
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
    use status_emitter::SilentStatus;

    config.fill_host_and_target()?;

    let content = Spanned::read_from_file(path)
        .wrap_err_with(|| format!("failed to read {}", display(path)))?;
    let comments = Comments::parse(content.as_ref(), &config)
        .map_err(|errors| color_eyre::eyre::eyre!("{errors:#?}"))?;
    let config = TestConfig {
        config,
        comments: &comments,
        aux_dir: &path.parent().unwrap().join("auxiliary"),
        status: Box::new(SilentStatus {
            revision: String::new(),
            path: path.to_path_buf(),
        }),
    };
    let build_manager = BuildManager::new(&(), config.config.clone());

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
    per_file_config: impl Fn(&mut Config, &Spanned<Vec<u8>>) + Sync,
    status_emitter: impl StatusEmitter + Send,
) -> Result<()> {
    if nextest::emulate(&mut configs) {
        return Ok(());
    }

    for config in &mut configs {
        config.fill_host_and_target()?;
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

    let configs: Vec<_> = configs
        .into_iter()
        .map(|config| BuildManager::new(&status_emitter, config))
        .collect();

    let mut filtered = 0;
    core::run_and_collect(
        num_threads,
        |submit| {
            let mut todo = VecDeque::new();
            for build_manager in &configs {
                todo.push_back((build_manager.config().root_dir.clone(), build_manager));
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
                        todo.push_back((entry, build_manager));
                    }
                } else if let Some(matched) = file_filter(&path, build_manager.config()) {
                    if matched {
                        let status = status_emitter.register_test(path);
                        // Forward .rs files to the test workers.
                        submit.send((status, build_manager)).unwrap();
                    } else {
                        filtered += 1;
                    }
                }
            }
        },
        |receive, finished_files_sender| -> Result<()> {
            for (status, build_manager) in receive {
                let path = status.path();
                let file_contents = Spanned::read_from_file(path).unwrap();
                let mut config = build_manager.config().clone();
                per_file_config(&mut config, &file_contents);
                let result = match std::panic::catch_unwind(|| {
                    parse_and_test_file(build_manager, &status, config, file_contents)
                }) {
                    Ok(Ok(res)) => res,
                    Ok(Err(err)) => {
                        finished_files_sender.send(TestRun {
                            result: Err(err),
                            status,
                        })?;
                        continue;
                    }
                    Err(err) => {
                        finished_files_sender.send(TestRun {
                            result: Err(Errored {
                                command: "<unknown>".into(),
                                errors: vec![Error::Bug(
                                    *Box::<dyn std::any::Any + Send + 'static>::downcast::<String>(
                                        err,
                                    )
                                    .unwrap(),
                                )],
                                stderr: vec![],
                                stdout: vec![],
                            }),
                            status,
                        })?;
                        continue;
                    }
                };
                for result in result {
                    finished_files_sender.send(result)?;
                }
            }
            Ok(())
        },
        |finished_files_recv| {
            for run in finished_files_recv {
                run.status.done(&run.result);

                results.push(run);
            }
        },
    )?;

    let mut failures = vec![];
    let mut succeeded = 0;
    let mut ignored = 0;

    for run in results {
        match run.result {
            Ok(TestOk::Ok) => succeeded += 1,
            Ok(TestOk::Ignored) => ignored += 1,
            Err(errored) => failures.push((run.status, errored)),
        }
    }

    let mut failure_emitter = status_emitter.finalize(failures.len(), succeeded, ignored, filtered);
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
    build_manager: &BuildManager<'_>,
    status: &dyn TestStatus,
    config: Config,
    file_contents: Spanned<Vec<u8>>,
) -> Result<Vec<TestRun>, Errored> {
    let comments = Comments::parse(file_contents.as_ref(), &config)
        .map_err(|errors| Errored::new(errors, "parse comments"))?;
    const EMPTY: &[String] = &[String::new()];
    // Run the test for all revisions
    let revisions = comments.revisions.as_deref().unwrap_or(EMPTY);
    let mut runs = vec![];
    for revision in revisions {
        let status = status.for_revision(revision);
        // Ignore file if only/ignore rules do (not) apply
        if !config.test_file_conditions(&comments, revision) {
            runs.push(TestRun {
                result: Ok(TestOk::Ignored),
                status,
            });
            continue;
        }

        let mut test_config = TestConfig {
            config: config.clone(),
            comments: &comments,
            aux_dir: &status.path().parent().unwrap().join("auxiliary"),
            status,
        };

        let result = test_config.run_test(build_manager, &mut runs);
        runs.push(TestRun {
            result,
            status: test_config.status,
        })
    }
    Ok(runs)
}

fn display(path: &Path) -> String {
    path.display().to_string().replace('\\', "/")
}
