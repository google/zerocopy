// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The CLI and stock editor enter through the workspace's fixed SDK binding.
use crate::lean_sdk::{LakeOperation, LeanOperation, Workspace};
use anyhow::{Context as _, Result, bail, ensure};
use clap::{Parser, Subcommand, ValueEnum};
use std::{
    ffi::OsString,
    fs,
    io::Write as _,
    path::{Path, PathBuf},
    process::Command,
};

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
    /// Start the bound server with local dependency freshness coordination.
    Serve,
    /// Open a fresh private VS Code instance with pinned local extensions.
    Editor {
        #[arg(long)]
        code: PathBuf,
        #[arg(long = "extension", required = true)]
        extensions: Vec<PathBuf>,
        /// Existing parent for fresh editor state; use a short path on macOS.
        #[arg(long)]
        state_dir: Option<PathBuf>,
    },
}

#[derive(ValueEnum, Clone, Debug)]
pub enum Tool {
    Lean,
    Lake,
}

#[derive(Parser, Debug)]
pub struct EditorArgs {
    #[arg(long)]
    workspace: PathBuf,
    #[arg(long, value_enum)]
    tool: Tool,
    #[arg(last = true, allow_hyphen_values = true)]
    arguments: Vec<OsString>,
}

pub fn run(args: Args) -> Result<()> {
    let workspace = Workspace::from_root(&args.workspace)?;
    let _writer = if matches!(args.operation, Operation::Serve | Operation::Editor { .. }) {
        None
    } else {
        Some(workspace.writer_lock()?)
    };
    match args.operation {
        Operation::Build { targets } => {
            let stamp = workspace.source_stamp()?;
            let mut command = workspace.lake_command(LakeOperation::Build(&targets))?;
            run_status(&mut command)?;
            ensure_current(&workspace, stamp)
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
            let stamp = workspace.source_stamp()?;
            let output = workspace.lake_command(LakeOperation::SetupFile(&file))?.output()?;
            ensure_current(&workspace, stamp)?;
            std::io::stdout().write_all(&output.stdout)?;
            std::io::stderr().write_all(&output.stderr)?;
            ensure!(output.status.success(), "Lake setup failed ({})", output.status);
            Ok(())
        }
        Operation::Serve => crate::lean_server::run(&workspace),
        Operation::Editor { code, extensions, state_dir } => {
            let host = crate::editor_host::EditorHost::prepare(
                &workspace,
                &code,
                &extensions,
                state_dir.as_deref(),
            )?;
            eprintln!("Anneal editor state: {}", host.profile_root().display());
            run_status(&mut host.version_command()?)?;
            for mut command in host.install_commands()? {
                run_status(&mut command)?;
            }
            run_status(&mut host.launch_command()?)
        }
    }
}

pub fn setup_saved_imports(workspace: &Workspace<'_>, file: &Path) -> Result<()> {
    let stamp = workspace.source_stamp()?;
    let output = workspace.lake_command(LakeOperation::SetupFile(file))?.output()?;
    ensure_current(workspace, stamp)?;
    ensure!(
        output.status.success(),
        "Local import build failed\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let setup: serde_json::Value =
        serde_json::from_slice(&output.stdout).context("Lake returned malformed setup metadata")?;
    ensure!(setup.is_object(), "Lake setup metadata is not an object");
    Ok(())
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

pub fn editor(args: EditorArgs) -> Result<()> {
    let workspace = Workspace::from_root(&args.workspace)?;
    let operation = editor_operation(&workspace, &args.tool, &args.arguments)?;
    match operation {
        EditorOperation::Serve => crate::lean_server::run(&workspace),
        EditorOperation::SdkSource(root) => crate::sdk_source_server::run(&workspace, &root),
        EditorOperation::Command(mut command) => {
            #[cfg(unix)]
            {
                use std::os::unix::process::CommandExt as _;
                Err(command.exec().into())
            }
            #[cfg(not(unix))]
            {
                run_status(&mut command)
            }
        }
    }
}

enum EditorOperation {
    Serve,
    SdkSource(PathBuf),
    Command(Command),
}

fn editor_operation(
    workspace: &Workspace<'_>,
    tool: &Tool,
    raw: &[OsString],
) -> Result<EditorOperation> {
    let mut args = raw
        .iter()
        .map(|s| s.to_str().context("Non-UTF8 editor argument"))
        .collect::<Result<Vec<_>>>()?;
    if args.first().is_some_and(|a| a.starts_with('+')) {
        let selector = args.remove(0).strip_prefix('+').unwrap();
        ensure!(
            Path::new(selector) == workspace.sdk().root()
                || selector == workspace.sdk().lean_toolchain(),
            "Editor requested a different SDK"
        );
    }
    let command = match (tool, args.as_slice()) {
        (Tool::Lean, ["--version"]) => workspace.lean_command(LeanOperation::Version)?,
        (Tool::Lean, ["--print-prefix"]) => workspace.lean_command(LeanOperation::PrintPrefix)?,
        (Tool::Lean, ["--githash"]) => workspace.lean_command(LeanOperation::GitHash)?,
        (Tool::Lake, ["--version"]) => workspace.lake_command(LakeOperation::Version)?,
        (Tool::Lake, ["serve"]) => return Ok(EditorOperation::Serve),
        (Tool::Lake, ["serve", "--", root]) => {
            let root = fs::canonicalize(root)?;
            if root == workspace.root() {
                return Ok(EditorOperation::Serve);
            }
            ensure!(
                workspace.admit_sdk_source_project(&root)?,
                "Editor selected a foreign source project"
            );
            return Ok(EditorOperation::SdkSource(root));
        }
        (Tool::Lean, ["--server", root]) => {
            let root = fs::canonicalize(root)?;
            ensure!(
                workspace.admit_sdk_source_project(&root)?,
                "Editor selected a foreign source project"
            );
            return Ok(EditorOperation::SdkSource(root));
        }
        _ => bail!(
            "Unsupported Anneal editor invocation; use the generated settings and empty lean4.serverArgs"
        ),
    };
    Ok(EditorOperation::Command(command))
}

/// Gateways live outside SDK/bin; the actual copied Lean/Lake launchers retain
/// their coherent installation prefix. Every gateway reopens the fixed binding.
pub fn write_editor_gateway(stage: &Path, final_root: &Path) -> Result<()> {
    let executable = fs::canonicalize(std::env::current_exe()?)?;
    let executable =
        shell_quote(executable.to_str().context("Anneal executable path is not UTF-8")?);
    let root = shell_quote(final_root.to_str().context("Workspace path is not UTF-8")?);
    fs::create_dir(stage.join(".anneal-bin"))?;
    for tool in ["lean", "lake"] {
        let path = stage.join(".anneal-bin").join(tool);
        fs::write(
            &path,
            format!(
                "#!/bin/sh\nexec {executable} editor-gateway --workspace {root} --tool {tool} -- \"$@\"\n"
            ),
        )?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(path, fs::Permissions::from_mode(0o755))?;
        }
    }
    fs::create_dir(stage.join(".vscode"))?;
    fs::write(
        stage.join(".vscode/settings.json"),
        serde_json::to_vec_pretty(&serde_json::json!({
            "lean4.envPathExtensions": [".anneal-bin"],
            "lean4.serverArgs": [],
            "lean4.automaticallyBuildDependencies": false,
            "lean4.logging.enabled": false,
            "lean4.showSetupWarnings": false
        }))?,
    )?;
    Ok(())
}

pub(crate) fn shell_quote(value: &str) -> String {
    format!("'{}'", value.replace('\'', "'\\''"))
}

#[cfg(test)]
mod tests {
    use super::*;
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
}
