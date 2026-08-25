// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Local, human-readable access to the typed CI configuration.
//!
//! `cargo-zerocopy` routes its `ci` subcommand here before it reads the Cargo
//! toolchain metadata used for ordinary Cargo delegation. Both repository
//! wrappers run that binary with `zerocopy` as the current directory, so the
//! caller passes `..` as the repository root. Keep that working-directory
//! contract coordinated with `tools/cargo-zerocopy/src/main.rs`,
//! `zerocopy/cargo.sh`, and `zerocopy/win-cargo.bat`.
//!
//! Argument parsing and output live here rather than in `cargo-zerocopy` so CI
//! policy has one typed command surface on every host. This module reports
//! errors to its caller and never terminates the process itself.

use std::{
    collections::BTreeSet,
    fs,
    io::{self, Write},
    path::{Path, PathBuf},
};

use thiserror::Error;

use crate::{
    ci::{CiInputs, LoadCiError},
    github::{GitHubProjection, ProjectionError, ProjectionWriteError},
    plan::{
        BuildPlanCell, ExecutionMode, FeatureSelection, MiriPlanCell, Plan, PlanError,
        PlanExplanation,
    },
};

/// Runs one local `cargo-zerocopy ci` command.
///
/// `args` begins after the literal `ci` argument. Inputs are loaded only after
/// syntax has been accepted, and are loaded exactly once per invocation.
pub fn run(
    repository_root: impl AsRef<Path>,
    args: impl IntoIterator<Item = String>,
    mut output: impl Write,
) -> Result<(), CliError> {
    let command = Command::parse(args)?;
    if let Command::GitHubPlan { github_output, artifact, .. } = &command {
        validate_publication_paths(github_output, artifact)?;
    }
    let inputs =
        CiInputs::load(repository_root).map_err(|error| CliError::LoadInputs(Box::new(error)))?;
    match command {
        Command::Audit => audit(&inputs, &mut output),
        Command::Plan { event } => print_plan(&inputs, &event, &mut output),
        Command::Explain { event } => explain(&inputs, &event, &mut output),
        Command::GitHubPlan { event, github_output, artifact } => {
            write_github_plan(&inputs, &event, &github_output, &artifact, &mut output)
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Command {
    Audit,
    Plan { event: String },
    Explain { event: String },
    GitHubPlan { event: String, github_output: PathBuf, artifact: PathBuf },
}

impl Command {
    fn parse(args: impl IntoIterator<Item = String>) -> Result<Self, CliError> {
        let mut args = args.into_iter();
        let command = args.next().ok_or(CliError::MissingCommand)?;
        match command.as_str() {
            "audit" => {
                if let Some(argument) = args.next() {
                    Err(CliError::UnexpectedArgument { command, argument })
                } else {
                    Ok(Self::Audit)
                }
            }
            "plan" | "explain" => {
                let event = parse_event(&command, args)?;
                if command == "plan" {
                    Ok(Self::Plan { event })
                } else {
                    Ok(Self::Explain { event })
                }
            }
            "github-plan" => parse_github_plan(args),
            _ => Err(CliError::UnknownCommand { command }),
        }
    }
}

fn parse_github_plan(args: impl IntoIterator<Item = String>) -> Result<Command, CliError> {
    let command = "github-plan";
    let mut args = args.into_iter();
    let mut event = None;
    let mut github_output = None;
    let mut artifact = None;

    while let Some(argument) = args.next() {
        let (name, inline_value) = argument
            .split_once('=')
            .map_or((argument.as_str(), None), |(name, value)| (name, Some(value)));
        let destination = match name {
            "--event" => &mut event,
            "--github-output" => &mut github_output,
            "--artifact" => &mut artifact,
            _ => {
                return Err(CliError::UnknownArgument { command: command.to_owned(), argument });
            }
        };
        if destination.is_some() {
            return Err(CliError::DuplicateOption {
                command: command.to_owned(),
                option: name.to_owned(),
            });
        }
        let value = match inline_value {
            Some(value) => value.to_owned(),
            None => {
                let value = args.next().ok_or_else(|| CliError::MissingOptionValue {
                    command: command.to_owned(),
                    option: name.to_owned(),
                })?;
                if value.starts_with('-') {
                    return Err(CliError::MissingOptionValueBefore {
                        command: command.to_owned(),
                        option: name.to_owned(),
                        argument: value,
                    });
                }
                value
            }
        };
        if value.is_empty() {
            return Err(CliError::MissingOptionValue {
                command: command.to_owned(),
                option: name.to_owned(),
            });
        }
        *destination = Some(value);
    }

    let event = required_option(command, "--event", event)?;
    let github_output = PathBuf::from(required_option(command, "--github-output", github_output)?);
    let artifact = PathBuf::from(required_option(command, "--artifact", artifact)?);
    Ok(Command::GitHubPlan { event, github_output, artifact })
}

fn validate_publication_paths(github_output: &Path, artifact: &Path) -> Result<(), CliError> {
    // GitHub creates GITHUB_OUTPUT before invoking a step. Requiring that
    // existing regular file makes this workflow-specific command fail closed
    // when it is called with a misspelled or surprising destination.
    let resolved_output =
        github_output.canonicalize().map_err(|source| CliError::ResolvePublicationPath {
            purpose: "GitHub output",
            path: github_output.to_path_buf(),
            source,
        })?;
    let output_metadata =
        fs::metadata(&resolved_output).map_err(|source| CliError::ResolvePublicationPath {
            purpose: "GitHub output",
            path: github_output.to_path_buf(),
            source,
        })?;
    if !output_metadata.is_file() {
        return Err(CliError::PublicationPathNotFile {
            purpose: "GitHub output",
            path: github_output.to_path_buf(),
        });
    }

    let file_name = artifact.file_name().ok_or_else(|| CliError::PublicationPathNotFile {
        purpose: "artifact destination",
        path: artifact.to_path_buf(),
    })?;
    let parent = artifact
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let resolved_parent =
        parent.canonicalize().map_err(|source| CliError::ResolvePublicationPath {
            purpose: "artifact parent",
            path: parent.to_path_buf(),
            source,
        })?;
    let resolved_artifact = resolved_parent.join(file_name);
    if resolved_output == resolved_artifact {
        return Err(CliError::PublicationPathsAlias { path: resolved_output });
    }
    Ok(())
}

fn required_option(command: &str, option: &str, value: Option<String>) -> Result<String, CliError> {
    value.ok_or_else(|| CliError::MissingOption {
        command: command.to_owned(),
        option: option.to_owned(),
    })
}

fn parse_event(command: &str, args: impl IntoIterator<Item = String>) -> Result<String, CliError> {
    let mut args = args.into_iter();
    let mut event = None;

    while let Some(argument) = args.next() {
        if argument == "--event" {
            if event.is_some() {
                return Err(CliError::DuplicateEvent { command: command.to_owned() });
            }
            let value = args
                .next()
                .ok_or_else(|| CliError::MissingEventValue { command: command.to_owned() })?;
            if value.starts_with('-') {
                return Err(CliError::MissingEventValueBefore {
                    command: command.to_owned(),
                    argument: value,
                });
            }
            event = Some(value);
        } else if let Some(value) = argument.strip_prefix("--event=") {
            if event.is_some() {
                return Err(CliError::DuplicateEvent { command: command.to_owned() });
            }
            if value.is_empty() {
                return Err(CliError::MissingEventValue { command: command.to_owned() });
            }
            event = Some(value.to_owned());
        } else {
            return Err(CliError::UnknownArgument { command: command.to_owned(), argument });
        }
    }

    event.ok_or_else(|| CliError::MissingEvent { command: command.to_owned() })
}

fn audit(inputs: &CiInputs, output: &mut impl Write) -> Result<(), CliError> {
    // Enumerate policy rather than keeping a second event list in this command.
    // The planner also compares that policy with its independent legacy
    // event-class baseline. Adding or reclassifying an event therefore fails
    // until a reviewer updates the baseline deliberately.
    let events = inputs
        .policy()
        .events()
        .reduced()
        .iter()
        .chain(inputs.policy().events().full())
        .map(|event| event.as_str())
        .collect::<BTreeSet<_>>();
    let plans = events
        .into_iter()
        .map(|event| Plan::create(inputs, event))
        .collect::<Result<Vec<_>, _>>()?;

    writeln!(output, "CI audit passed")?;
    for plan in plans {
        writeln!(
            output,
            "{}: {} coverage; {} build cells; {} Miri cells",
            plan.event(),
            plan.class(),
            plan.builds().len(),
            plan.miri().len(),
        )?;
    }
    Ok(())
}

fn print_plan(inputs: &CiInputs, event: &str, output: &mut impl Write) -> Result<(), CliError> {
    let plan = Plan::create(inputs, event)?;
    writeln!(output, "event: {}", plan.event())?;
    writeln!(output, "coverage: {}", plan.class())?;
    writeln!(output, "build cells: {}", plan.builds().len())?;
    writeln!(output, "Miri cells: {}", plan.miri().len())?;
    for cell in plan.builds() {
        print_build_cell(output, cell)?;
    }
    for cell in plan.miri() {
        print_miri_cell(output, cell)?;
    }
    Ok(())
}

fn print_build_cell(output: &mut impl Write, cell: &BuildPlanCell) -> io::Result<()> {
    write!(
        output,
        "build: package={} manifest={} toolchain={} version={} profile={} features=",
        cell.package().id(),
        cell.package().manifest().display(),
        cell.toolchain().id(),
        cell.toolchain().version(),
        cell.features().profile(),
    )?;
    print_feature_selection(output, cell.features().selection())?;
    writeln!(
        output,
        " target={} mode={}",
        cell.target().triple(),
        execution_mode(cell.target().mode()),
    )
}

fn print_miri_cell(output: &mut impl Write, cell: &MiriPlanCell) -> io::Result<()> {
    write!(
        output,
        "miri: package={} manifest={} toolchain={} version={} profile={} features=",
        cell.package().id(),
        cell.package().manifest().display(),
        cell.toolchain().id(),
        cell.toolchain().version(),
        cell.features().profile(),
    )?;
    print_feature_selection(output, cell.features().selection())?;
    write!(output, " target={} model={} flags=[", cell.target().triple(), cell.model().id(),)?;
    for (index, flag) in cell.model().flags().iter().enumerate() {
        if index != 0 {
            write!(output, ",")?;
        }
        write!(output, "{flag}")?;
    }
    writeln!(output, "]")
}

fn print_feature_selection(
    output: &mut impl Write,
    selection: &FeatureSelection,
) -> io::Result<()> {
    match selection {
        FeatureSelection::Default => write!(output, "default"),
        FeatureSelection::NoDefault => write!(output, "no-default"),
        FeatureSelection::StableAggregate { feature } => {
            write!(output, "stable-aggregate:{feature}")
        }
        FeatureSelection::All => write!(output, "all"),
    }
}

fn execution_mode(mode: ExecutionMode) -> &'static str {
    match mode {
        ExecutionMode::Native => "native",
        ExecutionMode::Cross => "cross",
        ExecutionMode::Thumb => "thumb",
    }
}

fn explain(inputs: &CiInputs, event: &str, output: &mut impl Write) -> Result<(), CliError> {
    let explanation = PlanExplanation::create(inputs, event)?;
    write!(output, "{explanation}")?;
    Ok(())
}

fn write_github_plan(
    inputs: &CiInputs,
    event: &str,
    github_output: &Path,
    artifact: &Path,
    output: &mut impl Write,
) -> Result<(), CliError> {
    let projection = GitHubProjection::create(inputs, event)?;

    // Publish the diagnostic artifact first. If that create-only operation
    // fails, no matrix output can escape from this invocation. The workflow
    // also cannot consume outputs from a failed planning job, but this order
    // keeps the local command's observable state as small as possible.
    projection.write_artifact_atomically(artifact)?;
    projection.append_to_github_output(github_output)?;
    writeln!(
        output,
        "planned GitHub Actions work for {event:?}; wrote {} UTF-16 bytes of job outputs and artifact {:?}",
        projection.output_utf16_bytes(),
        artifact,
    )?;
    Ok(())
}

/// A command-line syntax, input, planning, or output failure.
#[derive(Debug, Error)]
pub enum CliError {
    /// No command followed the literal `ci` argument.
    #[error("missing CI command; expected `audit`, `plan`, `explain`, or `github-plan`")]
    MissingCommand,
    /// The command name is not part of the local CI interface.
    #[error(
        "unknown CI command {command:?}; expected `audit`, `plan`, `explain`, or `github-plan`"
    )]
    UnknownCommand {
        /// The rejected command.
        command: String,
    },
    /// The argument-free audit command received an argument.
    #[error("`ci {command}` does not accept argument {argument:?}")]
    UnexpectedArgument {
        /// The command being parsed.
        command: String,
        /// The rejected argument.
        argument: String,
    },
    /// A command which selects an event received no selector.
    #[error("`ci {command}` requires `--event EVENT`")]
    MissingEvent {
        /// The command being parsed.
        command: String,
    },
    /// The event selector was repeated.
    #[error("`ci {command}` received `--event` more than once")]
    DuplicateEvent {
        /// The command being parsed.
        command: String,
    },
    /// An event option ended before its value.
    #[error("`ci {command} --event` requires an event name")]
    MissingEventValue {
        /// The command being parsed.
        command: String,
    },
    /// Another option appeared where an event value was required.
    #[error("`ci {command} --event` requires an event name before {argument:?}")]
    MissingEventValueBefore {
        /// The command being parsed.
        command: String,
        /// The option which cannot serve as an event name.
        argument: String,
    },
    /// A plan or explanation command received an unsupported argument.
    #[error("unknown argument {argument:?} for `ci {command}`; expected `--event EVENT`")]
    UnknownArgument {
        /// The command being parsed.
        command: String,
        /// The rejected argument.
        argument: String,
    },
    /// A required named option was absent.
    #[error("`ci {command}` requires `{option} VALUE`")]
    MissingOption {
        /// The command being parsed.
        command: String,
        /// The absent long option.
        option: String,
    },
    /// A named option was repeated.
    #[error("`ci {command}` received `{option}` more than once")]
    DuplicateOption {
        /// The command being parsed.
        command: String,
        /// The repeated long option.
        option: String,
    },
    /// A named option ended before its value.
    #[error("`ci {command} {option}` requires a value")]
    MissingOptionValue {
        /// The command being parsed.
        command: String,
        /// The option whose value is absent.
        option: String,
    },
    /// Another option appeared where a value was required.
    #[error("`ci {command} {option}` requires a value before {argument:?}")]
    MissingOptionValueBefore {
        /// The command being parsed.
        command: String,
        /// The option whose value is absent.
        option: String,
        /// The option which cannot serve as its value.
        argument: String,
    },
    /// A workflow publication path could not be resolved safely.
    #[error("failed to resolve {purpose} path {path:?}: {source}")]
    ResolvePublicationPath {
        /// Plain-language role of the path.
        purpose: &'static str,
        /// Caller-supplied path.
        path: PathBuf,
        /// Underlying filesystem error.
        #[source]
        source: io::Error,
    },
    /// A publication path which must name a regular file did not.
    #[error("{purpose} path {path:?} must name a regular file")]
    PublicationPathNotFile {
        /// Plain-language role of the path.
        purpose: &'static str,
        /// Caller-supplied path.
        path: PathBuf,
    },
    /// The output and artifact destinations resolve to the same file.
    #[error("GitHub output and artifact destinations both resolve to {path:?}")]
    PublicationPathsAlias {
        /// Canonical destination shared by both arguments.
        path: PathBuf,
    },
    /// The repository's checked CI inputs could not be loaded.
    #[error(transparent)]
    LoadInputs(Box<LoadCiError>),
    /// A checked plan could not be constructed.
    #[error(transparent)]
    Plan(#[from] PlanError),
    /// A checked plan could not be serialized for GitHub Actions.
    #[error(transparent)]
    Projection(#[from] ProjectionError),
    /// A checked projection could not be published to its requested files.
    #[error(transparent)]
    ProjectionWrite(#[from] ProjectionWriteError),
    /// Human-readable output could not be written.
    #[error("failed to write CI command output: {0}")]
    Output(#[from] io::Error),
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        path::{Path, PathBuf},
        process,
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::{run, CliError, Command};

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_owned()).collect()
    }

    fn repository_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    #[test]
    fn parses_supported_commands() {
        assert_eq!(Command::parse(strings(&["audit"])).unwrap(), Command::Audit);
        assert_eq!(
            Command::parse(strings(&["plan", "--event", "pull_request"])).unwrap(),
            Command::Plan { event: "pull_request".to_owned() }
        );
        assert_eq!(
            Command::parse(strings(&["explain", "--event=merge_group"])).unwrap(),
            Command::Explain { event: "merge_group".to_owned() }
        );
        assert_eq!(
            Command::parse(strings(&[
                "github-plan",
                "--artifact=plan.json",
                "--event",
                "push",
                "--github-output",
                "output.txt",
            ]))
            .unwrap(),
            Command::GitHubPlan {
                event: "push".to_owned(),
                github_output: "output.txt".into(),
                artifact: "plan.json".into(),
            }
        );
    }

    #[test]
    fn rejects_missing_duplicate_and_unknown_arguments_clearly() {
        assert!(matches!(Command::parse(Vec::new()), Err(CliError::MissingCommand)));
        assert!(matches!(
            Command::parse(strings(&["unknown"])),
            Err(CliError::UnknownCommand { command }) if command == "unknown"
        ));
        assert!(matches!(
            Command::parse(strings(&["audit", "extra"])),
            Err(CliError::UnexpectedArgument { command, argument })
                if command == "audit" && argument == "extra"
        ));
        assert!(matches!(
            Command::parse(strings(&["plan"])),
            Err(CliError::MissingEvent { command }) if command == "plan"
        ));
        assert!(matches!(
            Command::parse(strings(&["plan", "--event"])),
            Err(CliError::MissingEventValue { command }) if command == "plan"
        ));
        assert!(matches!(
            Command::parse(strings(&[
                "explain",
                "--event",
                "pull_request",
                "--event=push",
            ])),
            Err(CliError::DuplicateEvent { command }) if command == "explain"
        ));
        assert!(matches!(
            Command::parse(strings(&["plan", "pull_request"])),
            Err(CliError::UnknownArgument { command, argument })
                if command == "plan" && argument == "pull_request"
        ));
        assert!(matches!(
            Command::parse(strings(&[
                "github-plan",
                "--event",
                "push",
                "--artifact",
                "plan.json",
            ])),
            Err(CliError::MissingOption { command, option })
                if command == "github-plan" && option == "--github-output"
        ));
        assert!(matches!(
            Command::parse(strings(&[
                "github-plan",
                "--event=push",
                "--event",
                "merge_group",
                "--github-output=output",
                "--artifact=artifact",
            ])),
            Err(CliError::DuplicateOption { command, option })
                if command == "github-plan" && option == "--event"
        ));
        assert!(matches!(
            Command::parse(strings(&[
                "github-plan",
                "--event",
                "--artifact",
                "plan.json",
                "--github-output",
                "output",
            ])),
            Err(CliError::MissingOptionValueBefore { command, option, argument })
                if command == "github-plan"
                    && option == "--event"
                    && argument == "--artifact"
        ));
        assert!(matches!(
            Command::parse(strings(&[
                "github-plan",
                "--event",
                "",
                "--github-output=output",
                "--artifact=artifact",
            ])),
            Err(CliError::MissingOptionValue { command, option })
                if command == "github-plan" && option == "--event"
        ));
    }

    #[test]
    fn audit_plans_every_configured_event_in_stable_order() {
        let mut output = Vec::new();
        run(repository_root(), strings(&["audit"]), &mut output).unwrap();
        assert_eq!(
            String::from_utf8(output).unwrap(),
            concat!(
                "CI audit passed\n",
                "merge_group: full coverage; 182 build cells; 64 Miri cells\n",
                "pull_request: reduced coverage; 60 build cells; 0 Miri cells\n",
                "push: full coverage; 182 build cells; 64 Miri cells\n",
                "workflow_dispatch: full coverage; 182 build cells; 64 Miri cells\n",
            )
        );
    }

    #[test]
    fn plan_prints_every_selected_cell() {
        let mut output = Vec::new();
        run(repository_root(), strings(&["plan", "--event", "pull_request"]), &mut output).unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.starts_with(
            "event: pull_request\ncoverage: reduced\nbuild cells: 60\nMiri cells: 0\n"
        ));
        assert_eq!(output.lines().filter(|line| line.starts_with("build: ")).count(), 60);
        assert!(!output.lines().any(|line| line.starts_with("miri: ")));
    }

    #[test]
    fn explain_prints_inclusion_and_exclusion_reasons() {
        let mut output = Vec::new();
        run(repository_root(), strings(&["explain", "--event", "pull_request"]), &mut output)
            .unwrap();
        let output = String::from_utf8(output).unwrap();
        assert!(output.starts_with("event `pull_request` has reduced coverage:\n"));
        assert!(output.contains("included because policy marks the target eligible"));
        assert!(output.contains("excluded because policy does not mark the target eligible"));
        assert!(output.contains("excluded because Miri runs in the other event category"));
    }

    #[test]
    fn bad_syntax_is_rejected_before_repository_io() {
        let error =
            run("this/repository/does/not/exist", strings(&["plan"]), Vec::new()).unwrap_err();
        assert!(matches!(error, CliError::MissingEvent { .. }));
    }

    #[test]
    fn github_plan_publishes_both_outputs_from_one_checked_projection() {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT.fetch_add(1, Ordering::Relaxed);
        let directory =
            std::env::temp_dir().join(format!("zerocopy-ci-cli-test-{}-{unique}", process::id()));
        fs::create_dir(&directory).unwrap();
        let github_output = directory.join("github-output");
        let artifact = directory.join("ci-plan.json");
        let mut output = Vec::new();
        fs::write(&github_output, "").unwrap();

        run(
            repository_root(),
            vec![
                "github-plan".to_owned(),
                "--event=pull_request".to_owned(),
                format!("--github-output={}", github_output.display()),
                format!("--artifact={}", artifact.display()),
            ],
            &mut output,
        )
        .unwrap();

        let job_outputs = fs::read_to_string(github_output).unwrap();
        assert!(job_outputs.starts_with("build_matrix={\"include\":["));
        assert!(job_outputs.ends_with("miri_matrix={\"include\":[]}\n"));
        let artifact_json: serde_json::Value =
            serde_json::from_slice(&fs::read(artifact).unwrap()).unwrap();
        assert_eq!(artifact_json["event"], "pull_request");
        assert!(String::from_utf8(output).unwrap().contains("planned GitHub Actions work"));

        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn github_plan_rejects_aliased_destinations_before_repository_io() {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let unique = NEXT.fetch_add(1, Ordering::Relaxed);
        let directory = std::env::temp_dir()
            .join(format!("zerocopy-ci-cli-alias-test-{}-{unique}", process::id()));
        fs::create_dir(&directory).unwrap();
        let destination = directory.join("same-file");
        fs::write(&destination, "").unwrap();

        let error = run(
            "this/repository/does/not/exist",
            vec![
                "github-plan".to_owned(),
                "--event=pull_request".to_owned(),
                format!("--github-output={}", destination.display()),
                format!("--artifact={}/./same-file", directory.display()),
            ],
            Vec::new(),
        )
        .unwrap_err();
        assert!(matches!(error, CliError::PublicationPathsAlias { .. }));

        fs::remove_dir_all(directory).unwrap();
    }
}
