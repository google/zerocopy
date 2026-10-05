// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The CLI and stock editor enter through the workspace's fixed SDK binding.
use std::{
    ffi::OsString,
    fs,
    io::Write as _,
    path::{Path, PathBuf},
    process::Command,
};

use anyhow::{Context as _, Result, bail, ensure};
use clap::{Parser, Subcommand, ValueEnum};

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
    if matches!(args.operation, Operation::Serve) {
        return crate::lean_server::run(&args.workspace);
    }
    #[cfg(unix)]
    let _signals = matches!(args.operation, Operation::Editor { .. })
        .then(crate::lean_server::SignalGuard::install)
        .transpose()?;
    let (workspace, editor_startup) = if matches!(args.operation, Operation::Editor { .. }) {
        let (workspace, startup, _) = crate::lean_server::startup_workspace(&args.workspace)?;
        (workspace, Some(startup))
    } else {
        (Workspace::from_root(&args.workspace)?, None)
    };
    // Restore prior handlers before checking cancellation latched during
    // admission, then retain prior signal behavior for blocking Code commands.
    #[cfg(unix)]
    {
        drop(_signals);
        if matches!(args.operation, Operation::Editor { .. }) {
            ensure!(!crate::lean_server::interrupted(), "Editor launch interrupted");
        }
    }
    let _writer = if matches!(args.operation, Operation::Serve | Operation::Editor { .. }) {
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
        Operation::Editor { code, extensions, state_dir } => {
            let host = crate::editor_host::EditorHost::prepare(
                &workspace,
                &code,
                &extensions,
                state_dir.as_deref(),
            )?;
            eprintln!("Anneal editor state: {}", host.profile_root().display());
            let mut version = host.version_command()?;
            host.validate_before_command()?;
            let output = version.output().context("Read selected Code version")?;
            std::io::stdout().write_all(&output.stdout)?;
            std::io::stderr().write_all(&output.stderr)?;
            host.accept_version_output(&output)?;
            for mut command in host.install_commands()? {
                run_editor_status(&host, &mut command)?;
            }
            let mut launch = host.launch_command()?;
            host.validate_before_command()?;
            // Code's consuming gateway performs its own fenced admission.
            // Release after profile/command initialization, before Code can
            // start a gateway needing this same exclusive lease.
            drop(editor_startup);
            run_status(&mut launch)
        }
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

fn run_editor_status(
    host: &crate::editor_host::EditorHost<'_, '_>,
    command: &mut Command,
) -> Result<()> {
    host.validate_before_command()?;
    run_status(command)
}

pub fn editor(args: EditorArgs) -> Result<()> {
    #[cfg(unix)]
    let _signals = crate::lean_server::SignalGuard::install()?;
    let (workspace, startup, deadline) = crate::lean_server::startup_workspace(&args.workspace)?;
    validate_editor_gateway(workspace.root())?;
    let operation = editor_operation(&workspace, &args.tool, &args.arguments)?;
    match operation {
        EditorOperation::Serve => {
            crate::lean_server::run_with_startup(&workspace, startup, deadline)
        }
        EditorOperation::SdkSource(root) => {
            crate::sdk_source_server::run(&workspace, &root, startup)
        }
        EditorOperation::Command(mut command) => {
            // The finite version/prefix/hash command was prepared under the
            // fence and consumes only the immutable SDK, not mutable outputs.
            drop(startup);
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
    create_editor_directory(&stage.join(".anneal-bin"))?;
    for tool in ["lean", "lake"] {
        let path = stage.join(".anneal-bin").join(tool);
        write_editor_file(&path, gateway_script(final_root, tool)?.as_bytes(), 0o755)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            // validate_editor_gateway requires the exact wrapper mode even
            // when the caller has a restrictive umask.
            fs::set_permissions(path, fs::Permissions::from_mode(0o755))?;
        }
    }
    create_editor_directory(&stage.join(".vscode"))?;
    write_editor_file(&stage.join(".vscode/settings.json"), &gateway_settings()?, 0o600)?;
    Ok(())
}

fn create_editor_directory(path: &Path) -> Result<()> {
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt as _;
        builder.mode(0o700);
    }
    builder.create(path)?;
    Ok(())
}

fn write_editor_file(path: &Path, bytes: &[u8], mode: u32) -> Result<()> {
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        options.mode(mode);
    }
    #[cfg(not(unix))]
    let _ = mode;
    let mut file = options.open(path)?;
    file.write_all(bytes)?;
    Ok(())
}

fn gateway_script(workspace: &Path, tool: &str) -> Result<String> {
    let executable = fs::canonicalize(std::env::current_exe()?)?;
    let executable =
        shell_quote(executable.to_str().context("Anneal executable path is not UTF-8")?);
    let root = shell_quote(workspace.to_str().context("Workspace path is not UTF-8")?);
    Ok(format!(
        "#!/bin/sh\nexec {executable} editor-gateway --workspace {root} --tool {tool} -- \"$@\"\n"
    ))
}

fn gateway_settings() -> Result<Vec<u8>> {
    Ok(serde_json::to_vec_pretty(&serde_json::json!({
        "lean4.envPathExtensions": [".anneal-bin"],
        "lean4.serverArgs": [],
        "lean4.automaticallyBuildDependencies": false,
        "lean4.logging.enabled": false,
        "lean4.showSetupWarnings": false
    }))?)
}

/// The stock extension can select tools through both PATH and folder settings.
/// Admit the exact generated artifacts before launching Code or a bound gateway.
pub(crate) fn validate_editor_gateway(workspace: &Path) -> Result<()> {
    let bin = workspace.join(".anneal-bin");
    ensure!(fs::symlink_metadata(&bin)?.is_dir(), "Editor gateway directory is not physical");
    let mut names = fs::read_dir(&bin)?
        .map(|entry| entry.map(|entry| entry.file_name()))
        .collect::<std::io::Result<Vec<_>>>()?;
    names.sort();
    ensure!(
        names == [OsString::from("lake"), OsString::from("lean")],
        "Editor gateway directory contains unexpected tools"
    );
    for tool in ["lean", "lake"] {
        let path = bin.join(tool);
        let metadata = fs::symlink_metadata(&path)?;
        ensure!(metadata.is_file(), "Editor gateway is not a physical regular file");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            ensure!(
                metadata.permissions().mode() & 0o7777 == 0o755,
                "Editor gateway executable mode changed"
            );
        }
        ensure!(
            fs::read(&path)? == gateway_script(workspace, tool)?.as_bytes(),
            "Editor gateway content or binding changed"
        );
    }
    let settings_root = workspace.join(".vscode");
    ensure!(
        fs::symlink_metadata(&settings_root)?.is_dir(),
        "Editor folder settings directory is not physical"
    );
    let settings = settings_root.join("settings.json");
    ensure!(
        fs::symlink_metadata(&settings)?.is_file(),
        "Editor folder settings are not a physical regular file"
    );
    ensure!(fs::read(settings)? == gateway_settings()?, "Editor folder settings changed");
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
    fn generated_gateway_modes_are_protected_under_group_umask() {
        use std::os::unix::fs::PermissionsExt;

        const CHILD: &str = "ANNEAL_GATEWAY_GROUP_UMASK_CHILD";
        if std::env::var_os(CHILD).is_none() {
            // umask is process-wide. Run the actual producer in a separate
            // test process rather than changing parallel tests' umask.
            let output = std::process::Command::new(std::env::current_exe().unwrap())
                .arg("generated_gateway_modes_are_protected_under_group_umask")
                .arg("--test-threads=1")
                .env(CHILD, "1")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }

        unsafe extern "C" {
            fn umask(mode: u32) -> u32;
        }
        // SAFETY: this isolated child runs one filtered test and restores its
        // original umask before exiting.
        let previous = unsafe { umask(0o002) };
        #[cfg(target_os = "macos")]
        let temp = tempfile::tempdir_in("/private/tmp").unwrap();
        #[cfg(not(target_os = "macos"))]
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        write_editor_gateway(root, root).unwrap();
        for relative in [".anneal-bin", ".vscode"] {
            assert_eq!(
                fs::metadata(root.join(relative)).unwrap().permissions().mode() & 0o777,
                0o700
            );
        }
        for relative in [".anneal-bin/lean", ".anneal-bin/lake"] {
            assert_eq!(
                fs::metadata(root.join(relative)).unwrap().permissions().mode() & 0o777,
                0o755
            );
        }
        assert_eq!(
            fs::metadata(root.join(".vscode/settings.json")).unwrap().permissions().mode() & 0o777,
            0o600
        );
        validate_editor_gateway(root).unwrap();
        // SAFETY: restore this child's prior process-wide umask.
        unsafe { umask(previous) };
    }

    #[test]
    fn generated_gateway_rejects_changed_tools_and_folder_overrides() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        write_editor_gateway(root, root).unwrap();
        validate_editor_gateway(root).unwrap();
        for tool in ["lean", "lake"] {
            let path = root.join(".anneal-bin").join(tool);
            let original = fs::read(&path).unwrap();
            // These inert bytes are never passed to a command.
            fs::write(&path, "changed fixture").unwrap();
            assert!(validate_editor_gateway(root).is_err());
            fs::write(&path, original).unwrap();
            validate_editor_gateway(root).unwrap();
        }
        let extra = root.join(".anneal-bin/elan");
        fs::write(&extra, "unexpected fixture").unwrap();
        assert!(validate_editor_gateway(root).is_err());
        fs::remove_file(extra).unwrap();
        let settings = root.join(".vscode/settings.json");
        let mut changed: serde_json::Value =
            serde_json::from_slice(&fs::read(&settings).unwrap()).unwrap();
        changed["lean4.executablePath"] = serde_json::json!("/unused/fixture");
        fs::write(settings, serde_json::to_vec_pretty(&changed).unwrap()).unwrap();
        assert!(validate_editor_gateway(root).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn generated_gateway_rejects_changed_modes_and_symlink_routes() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        write_editor_gateway(root, root).unwrap();
        let lean = root.join(".anneal-bin/lean");
        fs::set_permissions(&lean, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(validate_editor_gateway(root).is_err());
        fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();
        let copy = root.join("lean-copy");
        fs::rename(&lean, &copy).unwrap();
        symlink(&copy, &lean).unwrap();
        assert!(validate_editor_gateway(root).is_err());
        fs::remove_file(&lean).unwrap();
        fs::rename(copy, &lean).unwrap();
        validate_editor_gateway(root).unwrap();

        let bin = root.join(".anneal-bin");
        let bin_copy = root.join("bin-copy");
        fs::rename(&bin, &bin_copy).unwrap();
        symlink(&bin_copy, &bin).unwrap();
        assert!(validate_editor_gateway(root).is_err());
        fs::remove_file(&bin).unwrap();
        fs::rename(bin_copy, &bin).unwrap();
        validate_editor_gateway(root).unwrap();

        let settings = root.join(".vscode/settings.json");
        let settings_copy = root.join("settings-copy");
        fs::rename(&settings, &settings_copy).unwrap();
        symlink(&settings_copy, &settings).unwrap();
        assert!(validate_editor_gateway(root).is_err());
        fs::remove_file(&settings).unwrap();
        fs::rename(settings_copy, &settings).unwrap();
        validate_editor_gateway(root).unwrap();

        let settings_dir = root.join(".vscode");
        let settings_dir_copy = root.join("settings-dir-copy");
        fs::rename(&settings_dir, &settings_dir_copy).unwrap();
        symlink(&settings_dir_copy, &settings_dir).unwrap();
        assert!(validate_editor_gateway(root).is_err());
    }

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
