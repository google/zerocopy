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
    io::{self, Write},
    path::Path,
};

use thiserror::Error;

use crate::{
    ci::{CiInputs, LoadCiError},
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
    let inputs =
        CiInputs::load(repository_root).map_err(|error| CliError::LoadInputs(Box::new(error)))?;

    match command {
        Command::Audit => audit(&inputs, &mut output),
        Command::Plan { event } => print_plan(&inputs, &event, &mut output),
        Command::Explain { event } => explain(&inputs, &event, &mut output),
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Command {
    Audit,
    Plan { event: String },
    Explain { event: String },
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
            _ => Err(CliError::UnknownCommand { command }),
        }
    }
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

/// A command-line syntax, input, planning, or output failure.
#[derive(Debug, Error)]
pub enum CliError {
    /// No command followed the literal `ci` argument.
    #[error("missing CI command; expected `audit`, `plan`, or `explain`")]
    MissingCommand,
    /// The command name is not part of the local CI interface.
    #[error("unknown CI command {command:?}; expected `audit`, `plan`, or `explain`")]
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
    /// The repository's checked CI inputs could not be loaded.
    #[error(transparent)]
    LoadInputs(Box<LoadCiError>),
    /// A checked plan could not be constructed.
    #[error(transparent)]
    Plan(#[from] PlanError),
    /// Human-readable output could not be written.
    #[error("failed to write CI command output: {0}")]
    Output(#[from] io::Error),
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

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
}
