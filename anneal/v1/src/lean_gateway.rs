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
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use anyhow::{Context as _, Result, bail, ensure};
use clap::{Parser, Subcommand, ValueEnum};

use crate::lean_preparation::{self, Request, Setup};
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
    #[cfg(unix)]
    if let Some(signals) = _signals {
        finish_startup_interruption(signals, "Editor launch")?;
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
            forward_current_output(
                &workspace,
                stamp,
                &output,
                "Lean check",
                &mut std::io::stdout(),
                &mut std::io::stderr(),
            )
        }
        Operation::SetupFile { file } => {
            let preparation = workspace.prepare_local_outputs()?;
            let output = workspace.lake_command(LakeOperation::SetupFile(&file))?.output()?;
            if output.status.success() {
                workspace.finish_local_outputs(&preparation)?;
            }
            forward_current_output(
                &workspace,
                preparation.stamp(),
                &output,
                "Lake setup",
                &mut std::io::stdout(),
                &mut std::io::stderr(),
            )
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
    let path = if file.is_absolute() { file.to_owned() } else { workspace.root().join(file) };
    let request = Request {
        request_id: "check".into(),
        targets: vec![],
        setup: Some(Setup {
            file_name: path.to_str().context("Lean source path must be UTF-8")?.to_owned(),
            path,
            header: None,
        }),
    };
    let result = lean_preparation::run(workspace, &[], &[request], preparation.stamp())?;
    if let Some(error) = &result.roots[0].error {
        bail!("{error}");
    }
    ensure!(!result.failed(), "Local import preparation failed");
    workspace.finish_local_outputs(&preparation)
}

// Refuse already-obsolete output before forwarding it, then recheck at the
// success boundary: a direct editor save need not honor the caller's writer
// lease and either output stream can block. Bytes already written cannot be
// retracted, but they must not acquire a successful current-result status.
fn forward_current_output(
    workspace: &Workspace<'_>,
    stamp: [u8; 32],
    output: &Output,
    operation: &str,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> Result<()> {
    ensure_current(workspace, stamp)?;
    stdout.write_all(&output.stdout)?;
    stderr.write_all(&output.stderr)?;
    stdout.flush()?;
    stderr.flush()?;
    ensure!(output.status.success(), "{operation} failed ({})", output.status);
    ensure_current(workspace, stamp)
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

#[cfg(unix)]
fn finish_startup_interruption(
    signals: crate::lean_server::SignalGuard,
    operation: &str,
) -> Result<()> {
    // End temporary catch-and-poll handling before observing its latch, so
    // later finite commands retain the caller's original signal behavior.
    drop(signals);
    ensure!(!crate::lean_server::interrupted(), "{operation} interrupted");
    Ok(())
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
            #[cfg(unix)]
            finish_startup_interruption(_signals, "Editor gateway")?;
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
    const SIGNAL_CHILD: &str = "ANNEAL_GATEWAY_STARTUP_HANDOFF_CHILD";
    #[cfg(unix)]
    const SIGNAL_ROOT: &str = "ANNEAL_GATEWAY_STARTUP_HANDOFF_ROOT";

    #[cfg(unix)]
    unsafe extern "C" {
        fn raise(number: i32) -> i32;
        fn signal(number: i32, handler: usize) -> usize;
    }

    #[cfg(unix)]
    fn isolated_signal_output(test: &str, case: &str, root: Option<&Path>) -> Output {
        assert!(std::env::var_os(SIGNAL_CHILD).is_none());
        assert!(std::env::var_os(SIGNAL_ROOT).is_none());
        let mut command = Command::new(std::env::current_exe().unwrap());
        command.arg(test).args(["--exact", "--test-threads=1"]).env(SIGNAL_CHILD, case);
        if let Some(root) = root {
            command.env(SIGNAL_ROOT, root);
        }
        let output = command.output().unwrap();
        assert!(
            output.status.success(),
            "Isolated signal case {case}: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        output
    }

    #[cfg(unix)]
    fn signal_test_completed(status_success: bool, stdout: &str) -> bool {
        if !status_success {
            return false;
        }
        let mut summaries = stdout.lines().filter(|line| line.contains("test result:"));
        let Some(summary) = summaries.next() else {
            return false;
        };
        if summaries.next().is_some() {
            return false;
        }
        let Some(counts) =
            summary.strip_prefix("test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; ")
        else {
            return false;
        };
        let Some((filtered, elapsed)) = counts.split_once(" filtered out; finished in ") else {
            return false;
        };
        if filtered.is_empty()
            || !filtered.bytes().all(|byte| byte.is_ascii_digit())
            || filtered.parse::<usize>().is_err()
        {
            return false;
        }
        let Some(seconds) = elapsed.strip_suffix('s') else {
            return false;
        };
        let Some((whole, fraction)) = seconds.split_once('.') else {
            return false;
        };
        !whole.is_empty()
            && whole.bytes().all(|byte| byte.is_ascii_digit())
            && fraction.len() == 2
            && fraction.bytes().all(|byte| byte.is_ascii_digit())
    }

    #[cfg(unix)]
    fn assert_one_signal_test(output: &Output) {
        let stdout = std::str::from_utf8(&output.stdout).expect("Signal child stdout is UTF-8");
        assert!(
            signal_test_completed(output.status.success(), stdout),
            "Incomplete signal child: {stdout}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn startup_handoff_rejects_real_interrupts_before_finite_invocation() {
        const TEST: &str =
            "lean_gateway::tests::startup_handoff_rejects_real_interrupts_before_finite_invocation";
        if std::env::var_os(SIGNAL_CHILD).is_none() {
            let summary = "test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 13 filtered out; finished in 0.00s\n";
            assert!(signal_test_completed(true, summary));
            assert!(signal_test_completed(true, &summary.replace("13 filtered", "0 filtered")));
            assert!(signal_test_completed(
                true,
                &format!("running 1 test\ntest selected ... ok\n{summary}\n")
            ));
            assert!(!signal_test_completed(false, summary));
            assert!(!signal_test_completed(true, "running 0 tests\n"));
            assert!(!signal_test_completed(true, &format!("{summary}{summary}")));
            for (before, after) in [
                ("1 passed", "0 passed"),
                ("0 failed", "1 failed"),
                ("0 ignored", "1 ignored"),
                ("0 measured", "1 measured"),
                ("result: ok.", "result: FAILED."),
                ("13 filtered", "-1 filtered"),
                ("13 filtered", "+1 filtered"),
                ("13 filtered", " filtered"),
                ("13 filtered", "1x filtered"),
                ("13 filtered", "1.0 filtered"),
                ("13 filtered", "１３ filtered"),
                ("13 filtered", "999999999999999999999999999999999999 filtered"),
                ("finished in 0.00s", ""),
                ("finished in 0.00s", "finished in NaNs"),
                ("finished in 0.00s", "finished in 0.00s extra"),
                ("test result:", "prefix test result:"),
            ] {
                assert!(
                    !signal_test_completed(true, &summary.replace(before, after)),
                    "Accepted malformed summary {after}"
                );
            }
            assert_one_signal_test(&isolated_signal_output(TEST, "cancel", None));
            return;
        }
        assert_eq!(std::env::var(SIGNAL_CHILD).unwrap(), "cancel");
        assert!(std::env::var_os(SIGNAL_ROOT).is_none());

        for operation in ["Editor launch", "Editor gateway"] {
            for number in [2, 15] {
                let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
                let temp = tempfile::tempdir().unwrap();
                let marker = temp.path().join("finite-command-was-invoked");
                fs::write(
                    fixture.sdk.root().join("bin/lean"),
                    format!(
                        "#!/bin/sh\nprintf invoked > {}\n",
                        shell_quote(marker.to_str().unwrap())
                    ),
                )
                .unwrap();
                let workspace = saved_workspace(&fixture, &temp.path().join("workspace"));
                write_editor_gateway(workspace.root(), workspace.root()).unwrap();
                drop(workspace.writer_lock().unwrap());
                let signals = crate::lean_server::SignalGuard::install().unwrap();
                let (admitted, startup, _) =
                    crate::lean_server::startup_workspace(workspace.root()).unwrap();
                validate_editor_gateway(admitted.root()).unwrap();
                let EditorOperation::Command(mut command) =
                    editor_operation(&admitted, &Tool::Lean, &["--version".into()]).unwrap()
                else {
                    panic!("Expected the finite probe");
                };
                assert!(workspace.try_writer_lock().unwrap().is_none());
                // raise delivers to this isolated calling thread and returns
                // only after the real installed handler has latched the signal.
                assert_eq!(unsafe { raise(number) }, 0);
                assert!(crate::lean_server::interrupted());
                let result: Result<()> = (|| {
                    finish_startup_interruption(signals, operation)?;
                    drop(startup);
                    run_status(&mut command)
                })();
                assert_eq!(result.unwrap_err().to_string(), format!("{operation} interrupted"));
                assert!(!marker.exists());
                assert!(workspace.try_writer_lock().unwrap().is_some());
            }
        }
    }

    #[cfg(unix)]
    static RESTORED_SIGNAL_CALLS: std::sync::atomic::AtomicUsize =
        std::sync::atomic::AtomicUsize::new(0);

    #[cfg(unix)]
    extern "C" fn restored_signal(_number: i32) {
        RESTORED_SIGNAL_CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    #[cfg(unix)]
    #[test]
    fn startup_handoff_restores_prior_handlers_before_returning() {
        const TEST: &str =
            "lean_gateway::tests::startup_handoff_restores_prior_handlers_before_returning";
        if std::env::var_os(SIGNAL_CHILD).is_none() {
            assert_one_signal_test(&isolated_signal_output(TEST, "restore", None));
            return;
        }
        assert_eq!(std::env::var(SIGNAL_CHILD).unwrap(), "restore");
        assert!(std::env::var_os(SIGNAL_ROOT).is_none());

        for number in [2, 15] {
            // Each harmless prior handler is confined to this single-test child.
            let previous = unsafe { signal(number, restored_signal as *const () as usize) };
            assert_ne!(previous, usize::MAX);
            RESTORED_SIGNAL_CALLS.store(0, std::sync::atomic::Ordering::Relaxed);
            let signals = crate::lean_server::SignalGuard::install().unwrap();
            assert_eq!(unsafe { raise(number) }, 0);
            assert_eq!(RESTORED_SIGNAL_CALLS.load(std::sync::atomic::Ordering::Relaxed), 0);
            let error = finish_startup_interruption(signals, "Editor gateway").unwrap_err();
            assert_eq!(error.to_string(), "Editor gateway interrupted");
            assert_eq!(unsafe { raise(number) }, 0);
            assert_eq!(RESTORED_SIGNAL_CALLS.load(std::sync::atomic::Ordering::Relaxed), 1);
            assert!(
                crate::lean_server::interrupted(),
                "Handoff must not clear captured cancellation"
            );

            let signals = crate::lean_server::SignalGuard::install().unwrap();
            finish_startup_interruption(signals, "Editor launch").unwrap();
            assert_eq!(unsafe { raise(number) }, 0);
            assert_eq!(RESTORED_SIGNAL_CALLS.load(std::sync::atomic::Ordering::Relaxed), 2);
            assert!(!crate::lean_server::interrupted());
            assert_ne!(unsafe { signal(number, previous) }, usize::MAX);
        }
    }

    #[cfg(all(unix, any(target_os = "macos", target_os = "linux")))]
    #[test]
    fn finite_editor_handoff_exec_preserves_ignored_signals_for_inert_probes() {
        const TEST: &str = "lean_gateway::tests::finite_editor_handoff_exec_preserves_ignored_signals_for_inert_probes";
        let cases = [
            ("lean-version", Tool::Lean, "--version"),
            ("lean-prefix", Tool::Lean, "--print-prefix"),
            ("lean-githash", Tool::Lean, "--githash"),
            ("lake-version", Tool::Lake, "--version"),
        ];
        if std::env::var_os(SIGNAL_CHILD).is_none() {
            for (case, tool, argument) in cases {
                // The parent owns these temporary trees: successful exec does
                // not run child Rust destructors, so parent teardown removes them.
                let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
                let temp = tempfile::tempdir().unwrap();
                let root = fs::canonicalize(temp.path()).unwrap().join("workspace");
                let expected = match tool {
                    Tool::Lean => format!(
                        "test \"$#\" -eq 2 && test \"$1\" = {} && test \"$2\" = {}",
                        shell_quote(&format!("--root={}", root.display())),
                        shell_quote(argument)
                    ),
                    Tool::Lake => {
                        format!("test \"$#\" -eq 1 && test \"$1\" = {}", shell_quote(argument))
                    }
                };
                let binary = match tool {
                    Tool::Lean => "lean",
                    Tool::Lake => "lake",
                };
                let marker = format!("ANNEAL_R22_INERT_EXEC:{case}");
                fs::write(
                    fixture.sdk.root().join("bin").join(binary),
                    format!(
                        "#!/bin/sh\n{expected} || exit 71\nkill -s INT \"$$\" || exit 72\nkill -s TERM \"$$\" || exit 73\nprintf '\\n%s\\n' {}\n",
                        shell_quote(&marker)
                    ),
                )
                .unwrap();
                let workspace = saved_workspace(&fixture, &root);
                write_editor_gateway(workspace.root(), workspace.root()).unwrap();
                drop(workspace.writer_lock().unwrap());
                let output = isolated_signal_output(TEST, case, Some(workspace.root()));
                let stdout = String::from_utf8_lossy(&output.stdout);
                assert_eq!(stdout.lines().filter(|line| *line == marker).count(), 1);
                assert!(!stdout.contains("test result:"), "The finite route must actually exec");
                assert!(workspace.try_writer_lock().unwrap().is_some());
            }
            return;
        }

        let selected = std::env::var(SIGNAL_CHILD).unwrap();
        let (_, tool, argument) = cases.into_iter().find(|(case, _, _)| *case == selected).unwrap();
        let root = PathBuf::from(std::env::var_os(SIGNAL_ROOT).unwrap());
        // SIG_IGN is 1 on the supported macOS/Linux ABIs. A caught handler
        // remaining through exec would reset to default, and this inert script's
        // directed self-signals would terminate it before its success marker.
        for number in [2, 15] {
            assert_ne!(unsafe { signal(number, 1) }, usize::MAX);
        }
        let result = editor(EditorArgs { workspace: root, tool, arguments: vec![argument.into()] });
        panic!("Finite editor exec unexpectedly returned: {result:?}");
    }

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
    fn saved_workspace<'a>(
        fixture: &'a crate::lean_sdk::tests::Fixture,
        root: &Path,
    ) -> Workspace<'a> {
        let workspace = Workspace::create(&fixture.sdk, root, &["user"]).unwrap();
        Workspace::write_lakefile(
            &fixture.sdk,
            workspace.root(),
            &[crate::lean_sdk::LakeLibrary {
                name: "User",
                source_root: "user",
                modules: &["Proof".to_owned()],
            }],
        )
        .unwrap();
        std::fs::create_dir(workspace.root().join("user")).unwrap();
        std::fs::write(workspace.root().join("user/Proof.lean"), "def proof := 1\n").unwrap();
        workspace
    }

    #[cfg(unix)]
    fn successful_output() -> Output {
        use std::os::unix::process::ExitStatusExt as _;
        Output {
            status: std::process::ExitStatus::from_raw(0),
            stdout: b"checked or setup metadata\n".to_vec(),
            stderr: b"informational stderr\n".to_vec(),
        }
    }

    #[cfg(unix)]
    struct SavingWriter {
        source: PathBuf,
        bytes: Vec<u8>,
    }

    #[cfg(unix)]
    impl Write for SavingWriter {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            // This save occurs inside production's actual write_all call,
            // after the pre-output stamp check, without acquiring the lease.
            std::fs::write(&self.source, "def proof := unchecked\n")?;
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[cfg(unix)]
    struct FailingWriter;

    #[cfg(unix)]
    impl Write for FailingWriter {
        fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
            Err(std::io::Error::new(std::io::ErrorKind::BrokenPipe, "output consumer closed"))
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    #[cfg(unix)]
    #[test]
    fn current_batch_output_forwards_both_streams_under_the_writer_lease() {
        let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        for operation in ["Lean check", "Lake setup"] {
            let temp = tempfile::tempdir().unwrap();
            let workspace = saved_workspace(&fixture, &temp.path().join("workspace"));
            let _writer = workspace.writer_lock().unwrap();
            let preparation = workspace.prepare_local_outputs().unwrap();
            workspace.finish_local_outputs(&preparation).unwrap();
            let output = successful_output();
            let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
            forward_current_output(
                &workspace,
                preparation.stamp(),
                &output,
                operation,
                &mut stdout,
                &mut stderr,
            )
            .unwrap();
            assert_eq!(stdout, output.stdout);
            assert_eq!(stderr, output.stderr);
            assert_eq!(workspace.source_stamp().unwrap(), preparation.stamp());
            assert!(workspace.try_shared_lock().unwrap().is_none());
        }
    }

    #[cfg(unix)]
    #[test]
    fn batch_success_rejects_a_save_during_either_forwarded_stream() {
        let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        for operation in ["Lean check", "Lake setup"] {
            for save_on_stderr in [false, true] {
                let temp = tempfile::tempdir().unwrap();
                let workspace = saved_workspace(&fixture, &temp.path().join("workspace"));
                let _writer = workspace.writer_lock().unwrap();
                let preparation = workspace.prepare_local_outputs().unwrap();
                workspace.finish_local_outputs(&preparation).unwrap();
                let output = successful_output();
                let mut saving = SavingWriter {
                    source: workspace.root().join("user/Proof.lean"),
                    bytes: Vec::new(),
                };
                let mut other = Vec::new();
                let result = if save_on_stderr {
                    forward_current_output(
                        &workspace,
                        preparation.stamp(),
                        &output,
                        operation,
                        &mut other,
                        &mut saving,
                    )
                } else {
                    forward_current_output(
                        &workspace,
                        preparation.stamp(),
                        &output,
                        operation,
                        &mut saving,
                        &mut other,
                    )
                };
                assert!(result.unwrap_err().to_string().contains("result is obsolete"));
                let (stdout, stderr) =
                    if save_on_stderr { (other, saving.bytes) } else { (saving.bytes, other) };
                assert_eq!(stdout, output.stdout);
                assert_eq!(stderr, output.stderr);
                assert_eq!(
                    std::fs::read_to_string(workspace.root().join("user/Proof.lean")).unwrap(),
                    "def proof := unchecked\n"
                );
                assert_ne!(workspace.source_stamp().unwrap(), preparation.stamp());
                assert!(workspace.try_shared_lock().unwrap().is_none());
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn obsolete_batch_output_is_refused_before_either_stream_is_written() {
        let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        let temp = tempfile::tempdir().unwrap();
        let workspace = saved_workspace(&fixture, &temp.path().join("workspace"));
        let _writer = workspace.writer_lock().unwrap();
        let stamp = workspace.source_stamp().unwrap();
        std::fs::write(workspace.root().join("user/Proof.lean"), "def proof := changed\n").unwrap();
        for operation in ["Lean check", "Lake setup"] {
            let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
            let error = forward_current_output(
                &workspace,
                stamp,
                &successful_output(),
                operation,
                &mut stdout,
                &mut stderr,
            )
            .unwrap_err();
            assert!(error.to_string().contains("result is obsolete"));
            assert!(stdout.is_empty());
            assert!(stderr.is_empty());
        }
    }

    #[cfg(unix)]
    #[test]
    fn batch_output_errors_cannot_be_accepted_as_success() {
        let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        let temp = tempfile::tempdir().unwrap();
        let workspace = saved_workspace(&fixture, &temp.path().join("workspace"));
        let _writer = workspace.writer_lock().unwrap();
        let stamp = workspace.source_stamp().unwrap();
        for operation in ["Lean check", "Lake setup"] {
            for fail_on_stderr in [false, true] {
                let output = successful_output();
                let mut recorded = Vec::new();
                let result = if fail_on_stderr {
                    forward_current_output(
                        &workspace,
                        stamp,
                        &output,
                        operation,
                        &mut recorded,
                        &mut FailingWriter,
                    )
                } else {
                    forward_current_output(
                        &workspace,
                        stamp,
                        &output,
                        operation,
                        &mut FailingWriter,
                        &mut recorded,
                    )
                };
                let error = result.unwrap_err();
                assert_eq!(
                    error.downcast_ref::<std::io::Error>().unwrap().kind(),
                    std::io::ErrorKind::BrokenPipe
                );
                if fail_on_stderr {
                    assert_eq!(recorded, output.stdout);
                } else {
                    assert!(recorded.is_empty());
                }
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn failed_batch_status_stays_failed_after_informational_output() {
        use std::os::unix::process::ExitStatusExt as _;
        let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        let temp = tempfile::tempdir().unwrap();
        let workspace = saved_workspace(&fixture, &temp.path().join("workspace"));
        let _writer = workspace.writer_lock().unwrap();
        let stamp = workspace.source_stamp().unwrap();
        for operation in ["Lean check", "Lake setup"] {
            let mut output = successful_output();
            output.status = std::process::ExitStatus::from_raw(1 << 8);
            let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
            let error = forward_current_output(
                &workspace,
                stamp,
                &output,
                operation,
                &mut stdout,
                &mut stderr,
            )
            .unwrap_err();
            assert!(error.to_string().starts_with(&format!("{operation} failed (")));
            assert_eq!(stdout, output.stdout);
            assert_eq!(stderr, output.stderr);
        }
    }

    #[cfg(unix)]
    #[derive(Default)]
    struct FlushRecorder {
        bytes: Vec<u8>,
        flushes: usize,
        fail_write: bool,
        fail_flush: bool,
        save_on_flush: Option<PathBuf>,
    }

    #[cfg(unix)]
    impl Write for FlushRecorder {
        fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
            if self.fail_write {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::BrokenPipe,
                    "deferred write failed",
                ));
            }
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            self.flushes += 1;
            if self.fail_flush {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::BrokenPipe,
                    "deferred flush failed",
                ));
            }
            if let Some(source) = &self.save_on_flush {
                std::fs::write(source, "def proof := saved_on_flush\n")?;
            }
            Ok(())
        }
    }

    #[cfg(unix)]
    #[test]
    fn buffered_batch_output_flushes_short_payloads_before_success() {
        let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        for operation in ["Lean check", "Lake setup"] {
            let temp = tempfile::tempdir().unwrap();
            let workspace = saved_workspace(&fixture, &temp.path().join("workspace"));
            let _writer = workspace.writer_lock().unwrap();
            let stamp = workspace.source_stamp().unwrap();
            let mut output = successful_output();
            output.stdout = b"short stdout".to_vec();
            output.stderr = b"short stderr".to_vec();
            let mut stdout = std::io::BufWriter::with_capacity(1024, FlushRecorder::default());
            let mut stderr = std::io::BufWriter::with_capacity(1024, FlushRecorder::default());
            forward_current_output(&workspace, stamp, &output, operation, &mut stdout, &mut stderr)
                .unwrap();
            // Inspect before drop: destructor flushing cannot satisfy this oracle.
            assert_eq!(stdout.get_ref().bytes, output.stdout);
            assert_eq!(stderr.get_ref().bytes, output.stderr);
            assert_eq!(stdout.get_ref().flushes, 1);
            assert_eq!(stderr.get_ref().flushes, 1);
            assert!(stdout.buffer().is_empty() && stderr.buffer().is_empty());
            assert_eq!(workspace.source_stamp().unwrap(), stamp);
            assert!(workspace.try_shared_lock().unwrap().is_none());
        }
    }

    #[cfg(unix)]
    #[test]
    fn buffered_batch_output_rejects_deferred_write_and_flush_errors() {
        let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        let temp = tempfile::tempdir().unwrap();
        let workspace = saved_workspace(&fixture, &temp.path().join("workspace"));
        let _writer = workspace.writer_lock().unwrap();
        let stamp = workspace.source_stamp().unwrap();
        for operation in ["Lean check", "Lake setup"] {
            for fail_stderr in [false, true] {
                for fail_write in [false, true] {
                    let mut output = successful_output();
                    output.stdout = b"short stdout".to_vec();
                    output.stderr = b"short stderr".to_vec();
                    let mut failed = std::io::BufWriter::with_capacity(
                        1024,
                        FlushRecorder {
                            fail_write,
                            fail_flush: !fail_write,
                            ..FlushRecorder::default()
                        },
                    );
                    let mut other =
                        std::io::BufWriter::with_capacity(1024, FlushRecorder::default());
                    let result = if fail_stderr {
                        forward_current_output(
                            &workspace,
                            stamp,
                            &output,
                            operation,
                            &mut other,
                            &mut failed,
                        )
                    } else {
                        forward_current_output(
                            &workspace,
                            stamp,
                            &output,
                            operation,
                            &mut failed,
                            &mut other,
                        )
                    };
                    let error = result.unwrap_err();
                    assert_eq!(
                        error.downcast_ref::<std::io::Error>().unwrap().kind(),
                        std::io::ErrorKind::BrokenPipe
                    );
                    assert_eq!(failed.get_ref().flushes, if fail_write { 0 } else { 1 });
                    if fail_write {
                        assert!(failed.get_ref().bytes.is_empty());
                        assert!(!failed.buffer().is_empty());
                    } else {
                        assert_eq!(
                            failed.get_ref().bytes,
                            if fail_stderr { output.stderr } else { output.stdout }
                        );
                    }
                    assert_eq!(workspace.source_stamp().unwrap(), stamp);
                }
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn buffered_batch_success_rejects_a_save_on_either_flush() {
        let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        for operation in ["Lean check", "Lake setup"] {
            for save_stderr in [false, true] {
                let temp = tempfile::tempdir().unwrap();
                let workspace = saved_workspace(&fixture, &temp.path().join("workspace"));
                let _writer = workspace.writer_lock().unwrap();
                let stamp = workspace.source_stamp().unwrap();
                let mut output = successful_output();
                output.stdout = b"short stdout".to_vec();
                output.stderr = b"short stderr".to_vec();
                let mut saving = std::io::BufWriter::with_capacity(
                    1024,
                    FlushRecorder {
                        save_on_flush: Some(workspace.root().join("user/Proof.lean")),
                        ..FlushRecorder::default()
                    },
                );
                let mut other = std::io::BufWriter::with_capacity(1024, FlushRecorder::default());
                let result = if save_stderr {
                    forward_current_output(
                        &workspace,
                        stamp,
                        &output,
                        operation,
                        &mut other,
                        &mut saving,
                    )
                } else {
                    forward_current_output(
                        &workspace,
                        stamp,
                        &output,
                        operation,
                        &mut saving,
                        &mut other,
                    )
                };
                assert!(result.unwrap_err().to_string().contains("result is obsolete"));
                assert_eq!(saving.get_ref().flushes, 1);
                assert_eq!(other.get_ref().flushes, 1);
                let (stdout, stderr) =
                    if save_stderr { (&other, &saving) } else { (&saving, &other) };
                assert_eq!(stdout.get_ref().bytes, output.stdout);
                assert_eq!(stderr.get_ref().bytes, output.stderr);
                assert_ne!(workspace.source_stamp().unwrap(), stamp);
                assert!(workspace.try_shared_lock().unwrap().is_none());
            }
        }
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
