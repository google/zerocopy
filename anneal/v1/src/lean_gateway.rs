// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The CLI and stock editor enter through the workspace's fixed SDK binding.
use std::{
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use anyhow::{Context as _, Result, bail, ensure};
use clap::{Parser, Subcommand};

use crate::{
    lean_preparation::{self, Request, Setup},
    lean_sdk::{LakeOperation, LeanOperation, Workspace},
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
}

pub fn run(args: Args) -> Result<()> {
    #[cfg(unix)]
    let signals = crate::lean_server::SignalGuard::install()?;
    // Quiesce native producers before Complete admission of their outputs.
    let (workspace, _writer) = Workspace::startup_writer_until(
        &args.workspace,
        std::time::Instant::now() + std::time::Duration::from_secs(60),
        crate::lean_server::interrupted,
    )?;
    #[cfg(unix)]
    finish_startup_interruption(signals, "Lean operation")?;
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

#[cfg(test)]
mod tests {
    use super::*;

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
