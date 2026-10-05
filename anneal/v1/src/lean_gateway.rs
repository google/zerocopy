// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Batch CLI operations use the workspace's fixed SDK binding.
use std::{
    io::Write as _,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Context as _, Result, ensure};
use clap::{Parser, Subcommand};

use crate::lean_sdk::{LakeOperation, LeanOperation, Workspace};

#[derive(Parser, Debug)]
pub struct Args {
    /// Generated workspace containing .anneal-sdk.json.
    #[arg(long)]
    workspace: PathBuf,
    #[command(subcommand)]
    operation: Operation,
}

#[derive(Subcommand, Debug)]
enum Operation {
    /// Build only this workspace's incremental outputs.
    Build { targets: Vec<String> },
    /// Build saved local imports, then check a source against that state.
    Check {
        file: PathBuf,
        #[arg(long)]
        json: bool,
    },
    /// Return Lake setup metadata after building saved local imports.
    SetupFile { file: PathBuf },
    /// Serve through stock Lake with local dependency freshness coordination.
    Serve,
}

pub fn run(args: Args) -> Result<()> {
    if matches!(args.operation, Operation::Serve) {
        return crate::lean_server::run(&args.workspace);
    }
    let workspace = Workspace::from_root(&args.workspace)?;
    let _writer = if matches!(args.operation, Operation::Serve) {
        None
    } else {
        Some(workspace.writer_lock()?)
    };
    match args.operation {
        Operation::Build { targets } => {
            let preparation = workspace.prepare_local_outputs()?;
            let mut command = workspace.lake_command(LakeOperation::Build(&targets))?;
            run_status(&mut command)?;
            workspace.finish_local_outputs(&preparation)
        }
        Operation::Check { file, json } => {
            let stamp = workspace.source_stamp()?;
            setup_saved_imports(&workspace, &file)?;
            let output =
                workspace.lean_command(LeanOperation::Check { file: &file, json })?.output()?;
            ensure_current(&workspace, stamp)?;
            // Obsolete output must not be presented as current verification.
            std::io::stdout().write_all(&output.stdout)?;
            std::io::stderr().write_all(&output.stderr)?;
            ensure!(output.status.success(), "Lean check failed ({})", output.status);
            Ok(())
        }
        Operation::SetupFile { file } => {
            let preparation = workspace.prepare_local_outputs()?;
            let output = workspace.lake_command(LakeOperation::SetupFile(&file))?.output()?;
            if output.status.success() {
                workspace.finish_local_outputs(&preparation)?;
            } else {
                ensure_current(&workspace, preparation.stamp())?;
            }
            std::io::stdout().write_all(&output.stdout)?;
            std::io::stderr().write_all(&output.stderr)?;
            ensure!(output.status.success(), "Lake setup failed ({})", output.status);
            Ok(())
        }
        Operation::Serve => unreachable!("Serve was dispatched before workspace admission"),
    }
}

pub fn setup_saved_imports(workspace: &Workspace<'_>, file: &Path) -> Result<()> {
    let preparation = workspace.prepare_local_outputs()?;
    let output = workspace.lake_command(LakeOperation::SetupFile(file))?.output()?;
    if !output.status.success() {
        ensure_current(workspace, preparation.stamp())?;
    }
    ensure!(
        output.status.success(),
        "Local import build failed\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let setup: serde_json::Value =
        serde_json::from_slice(&output.stdout).context("Lake returned malformed setup metadata")?;
    ensure!(setup.is_object(), "Lake setup metadata is not an object");
    workspace.finish_local_outputs(&preparation)
}

fn ensure_current(workspace: &Workspace<'_>, stamp: [u8; 32]) -> Result<()> {
    ensure!(workspace.source_stamp()? == stamp, "Saved Lean inputs changed; result is obsolete");
    Ok(())
}

fn run_status(command: &mut Command) -> Result<()> {
    let status = command.status()?;
    ensure!(status.success(), "Lean operation failed ({status})");
    Ok(())
}

pub(crate) fn shell_quote(value: &str) -> String {
    format!("'{}'", value.replace('\'', "'\\''"))
}

pub(crate) fn build_guidance(workspace: &Path) -> Result<String> {
    #[cfg(unix)]
    {
        let path = workspace.to_str().context("Workspace path is not UTF-8")?;
        Ok(format!("Build with: cargo anneal lean --workspace {} build", shell_quote(path)))
    }
    #[cfg(not(unix))]
    {
        // Windows has several incompatible command shells. Show the exact
        // argument order without presenting POSIX quoting as pasteable syntax.
        Ok(format!(
            "To build, run cargo anneal lean with arguments --workspace, the path below, then build.\nWorkspace path: {workspace:?}"
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(unix)]
    #[test]
    fn gateway_quotes_paths_without_shell_interpolation() {
        let value = "spaces and 'quotes' $(exit 2) `exit 3`";
        let output = Command::new("/bin/sh")
            .arg("-c")
            .arg(format!("printf '%s' {}", shell_quote(value)))
            .output()
            .unwrap();
        assert!(output.status.success());
        assert_eq!(String::from_utf8(output.stdout).unwrap(), value);
    }

    #[test]
    fn generated_build_guidance_matches_the_host_shell_contract() {
        let path = Path::new("workspace with 'apostrophe'");
        let guidance = build_guidance(path).unwrap();
        #[cfg(unix)]
        assert_eq!(
            guidance,
            format!(
                "Build with: cargo anneal lean --workspace {} build",
                shell_quote(path.to_str().unwrap())
            )
        );
        #[cfg(not(unix))]
        {
            assert!(guidance.contains("--workspace"));
            assert!(guidance.contains(&format!("{path:?}")));
            assert!(!guidance.contains("Build with:"));
            assert!(!guidance.contains("'\\''"));
        }
    }
}
