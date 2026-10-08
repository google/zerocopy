// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Operation-owned Lean preparation. Status records never carry ModuleSetup
//! bodies. A completed producer remains provisional until its caller rechecks
//! saved inputs and output ownership under the already-held writer lease.

use std::{
    collections::BTreeSet,
    io::{self, BufRead, BufReader, Read, Write},
    path::PathBuf,
    process::{Command, ExitStatus, Output, Stdio},
    sync::{
        atomic::{AtomicU64, Ordering},
        mpsc::{self, Receiver, TryRecvError},
    },
    thread::{self, JoinHandle},
};

use anyhow::{Context as _, Result, bail, ensure};
use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::{
    lean_sdk::{FiniteProducerLease, LakeOperation, LeanSdk, Workspace},
    lean_server::Process,
};

pub(crate) const MAX_ROOTS: usize = 32;
pub(crate) const MAX_TARGETS: usize = 8;
pub(crate) const MAX_PLAN: usize = 1024 * 1024;
const MAX_RECORD: usize = 64 * 1024;
const MAX_ERROR: usize = 8 * 1024;
const ERROR_TRUNCATION_NOTICE: &str = " [truncated; full error on stderr]";

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Setup {
    pub(crate) file_name: String,
    pub(crate) path: PathBuf,
    pub(crate) header: Option<Value>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Request {
    pub(crate) request_id: String,
    pub(crate) targets: Vec<String>,
    pub(crate) setup: Option<Setup>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Plan<'a> {
    protocol: u32,
    op_id: &'a str,
    config_text: &'a str,
    manifest_text: &'a str,
    initial_targets: &'a [String],
    requests: &'a [Request],
}

/// Indices always address the caller's original request list. Stock steps run
/// the same requests using incumbent commands, under the same preparation.
pub(crate) enum Step {
    Native(Recipe),
    Stock { initial_targets: Vec<String>, request_indices: Vec<usize> },
}

pub(crate) struct Recipe {
    command: Command,
    producer_root: PathBuf,
    sdk: LeanSdk,
    bytes: Vec<u8>,
    op_id: String,
    requests: Vec<Request>,
    pub(crate) request_indices: Vec<usize>,
    initial: bool,
}

fn identity(value: &str) -> bool {
    (1..=64).contains(&value.len())
        && value.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-'))
}

/// Choose chunks from input size before launching anything. Large individual
/// requests/configurations use stock; result size never changes this choice.
pub(crate) fn recipe(
    workspace: &Workspace<'_>,
    op_id: &str,
    initial_targets: &[String],
    requests: &[Request],
) -> Result<Vec<Step>> {
    ensure!(identity(op_id), "Invalid preparation operation identity");
    let mut ids = BTreeSet::new();
    for request in requests {
        ensure!(identity(&request.request_id), "Invalid preparation request identity");
        ensure!(ids.insert(&request.request_id), "Duplicate preparation request identity");
        workspace.validate_preparation_request(
            &request.targets,
            request.setup.as_ref().map(|setup| (setup.file_name.as_str(), setup.path.as_path())),
        )?;
    }
    workspace.validate_preparation_request(initial_targets, None)?;
    let stock_all = || {
        vec![Step::Stock {
            initial_targets: initial_targets.to_vec(),
            request_indices: (0..requests.len()).collect(),
        }]
    };
    let Some((config, manifest)) = workspace.finite_inputs()? else { return Ok(stock_all()) };
    let encode = |initial: &[String], roots: &[Request]| {
        serde_json::to_vec(&Plan {
            protocol: 1,
            op_id,
            config_text: &config,
            manifest_text: &manifest,
            initial_targets: initial,
            requests: roots,
        })
    };
    if initial_targets.len() > MAX_TARGETS || encode(initial_targets, &[])?.len() > MAX_PLAN {
        return Ok(stock_all());
    }
    let mut result = Vec::new();
    let mut start = 0;
    let mut initial_pending = true;
    while start < requests.len() || initial_pending {
        let initial = if initial_pending { initial_targets } else { &[] };
        let mut end = start;
        while end < requests.len()
            && end - start < MAX_ROOTS
            && requests[end].targets.len() <= MAX_TARGETS
            && encode(initial, &requests[start..=end])?.len() <= MAX_PLAN
        {
            end += 1;
        }
        if end == start && start < requests.len() {
            // Execute the initial targets once even when the first root is
            // oversized; later native chunks do not repeat this build.
            result.push(Step::Stock {
                initial_targets: initial.to_vec(),
                request_indices: vec![start],
            });
            start += 1;
        } else {
            result.push(Step::Native(Recipe {
                command: workspace.finite_command()?.context("Finite helper disappeared")?,
                sdk: workspace.sdk().clone(),
                producer_root: workspace.root().to_owned(),
                bytes: encode(initial, &requests[start..end])?,
                op_id: op_id.to_owned(),
                requests: requests[start..end].to_vec(),
                request_indices: (start..end).collect(),
                initial: !initial.is_empty(),
            }));
            start = end;
        }
        initial_pending = false;
    }
    Ok(result)
}

/// CLI adapter for an already-held writer lease and one existing output
/// preparation. It neither prepares nor commits provenance itself. The editor
/// uses Recipe/Producer directly so its event loop need not block. CLI callers
/// supply saved headers only; live-header requests belong to the editor adapter.
pub(crate) fn run(
    workspace: &Workspace<'_>,
    initial_targets: &[String],
    requests: &[Request],
    stamp: [u8; 32],
) -> Result<Prepared> {
    ensure!(
        requests
            .iter()
            .all(|request| request.setup.as_ref().is_none_or(|setup| setup.header.is_none())),
        "CLI preparation does not accept live module headers"
    );
    static SEQUENCE: AtomicU64 = AtomicU64::new(0);
    let op_id = format!("prep-{}-{}", std::process::id(), SEQUENCE.fetch_add(1, Ordering::Relaxed));
    #[cfg(unix)]
    let signals = crate::lean_server::SignalGuard::install()?;
    current(workspace, stamp)?;
    let steps = recipe(workspace, &op_id, initial_targets, requests)?;
    let mut result = Prepared { initial_error: None, roots: vec![] };
    let mut roots = vec![None; requests.len()];
    for step in steps {
        current(workspace, stamp)?;
        ensure!(!crate::lean_server::interrupted(), "Lean preparation interrupted");
        match step {
            Step::Native(recipe) => {
                let indices = recipe.request_indices.clone();
                let mut producer = recipe.spawn()?;
                let prepared = loop {
                    if crate::lean_server::interrupted() {
                        producer.cancel();
                        bail!("Lean preparation interrupted");
                    }
                    if let Some(prepared) = producer.poll()? {
                        break prepared;
                    }
                    thread::sleep(std::time::Duration::from_millis(5));
                };
                current(workspace, stamp)?;
                if prepared.initial_error.is_some() {
                    result.initial_error = prepared.initial_error;
                }
                for (index, root) in indices.into_iter().zip(prepared.roots) {
                    roots[index] = Some(root);
                }
            }
            Step::Stock { initial_targets, request_indices } => {
                if !initial_targets.is_empty() {
                    let output = stock_output(
                        workspace.lake_command(LakeOperation::Build(&initial_targets))?,
                        workspace,
                    )?;
                    current(workspace, stamp)?;
                    if !output.status.success() {
                        result.initial_error = Some(stock_error("Lean build failed", &output));
                    }
                }
                for index in request_indices {
                    let request = &requests[index];
                    current(workspace, stamp)?;
                    let build_error = if request.targets.is_empty() {
                        None
                    } else {
                        let output = stock_output(
                            workspace.lake_command(LakeOperation::Build(&request.targets))?,
                            workspace,
                        )?;
                        current(workspace, stamp)?;
                        (!output.status.success())
                            .then(|| stock_error("Local import build failed", &output))
                    };
                    roots[index] = Some(if let Some(error) = build_error {
                        RootResult { outcome: Outcome::BuildFailed, error: Some(error) }
                    } else if let Some(setup) = &request.setup {
                        let output = stock_output(
                            workspace.lake_command(LakeOperation::SetupFile(&setup.path))?,
                            workspace,
                        )?;
                        current(workspace, stamp)?;
                        if output.status.success() {
                            let setup: Value = serde_json::from_slice(&output.stdout)
                                .context("Lake returned malformed setup metadata")?;
                            ensure!(setup.is_object(), "Lake setup metadata is not an object");
                            RootResult { outcome: Outcome::Prepared, error: None }
                        } else {
                            RootResult {
                                outcome: Outcome::SetupFailed,
                                error: Some(stock_error("Local import build failed", &output)),
                            }
                        }
                    } else {
                        RootResult { outcome: Outcome::BuildOnly, error: None }
                    });
                }
            }
        }
        current(workspace, stamp)?;
    }
    result.roots = roots
        .into_iter()
        .map(|root| root.context("Missing prepared root coverage"))
        .collect::<Result<_>>()?;
    #[cfg(unix)]
    drop(signals);
    ensure!(!crate::lean_server::interrupted(), "Lean preparation interrupted");
    current(workspace, stamp)?;
    Ok(result)
}

fn current(workspace: &Workspace<'_>, stamp: [u8; 32]) -> Result<()> {
    workspace.admit()?;
    ensure!(
        workspace.source_stamp()? == stamp,
        "Saved Lean inputs changed; preparation is obsolete"
    );
    Ok(())
}

fn stock_error(label: &str, output: &Output) -> String {
    format!(
        "{label}\nSTDOUT:\n{}\nSTDERR:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

// This adapter preserves live Build logs rather than capturing an unbounded
// body. The caller installs its own operation interruption guard.
pub(crate) fn stock_status(mut command: Command, workspace: &Workspace<'_>) -> Result<()> {
    ensure!(!crate::lean_server::interrupted(), "Lean preparation interrupted");
    command.stdin(Stdio::null()).stdout(Stdio::inherit()).stderr(Stdio::inherit());
    let lease = workspace.finite_producer_lease()?;
    let mut process = Process::spawn_finite(&mut command, lease)?;
    let status = wait_finite_exit(&mut process)?;
    ensure!(status.success(), "Lean operation failed ({status})");
    Ok(())
}

fn wait_finite_exit(process: &mut Process) -> Result<ExitStatus> {
    loop {
        ensure!(!crate::lean_server::interrupted(), "Lean preparation interrupted");
        if let Some(status) = process.child.try_wait()? {
            if process.poll_stopped()? {
                return Ok(status);
            }
        }
        thread::sleep(std::time::Duration::from_millis(5));
    }
}

// Stock metadata is a public, unbounded body and keeps incumbent capture
// semantics. Own its group and concurrently drain both pipes so cancellation
// and reaping precede every pipe-reader join, just as for the status producer.
pub(crate) fn stock_output(mut command: Command, workspace: &Workspace<'_>) -> Result<Output> {
    ensure!(!crate::lean_server::interrupted(), "Lean preparation interrupted");
    command.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    let lease = workspace.finite_producer_lease()?;
    let mut process = Process::spawn_finite(&mut command, lease)?;
    let stdout = process.child.stdout.take().context("Missing Lake stdout")?;
    let stderr = process.child.stderr.take().context("Missing Lake stderr")?;
    let read = |mut pipe: Box<dyn Read + Send>| {
        thread::spawn(move || {
            let mut bytes = vec![];
            pipe.read_to_end(&mut bytes).map(|_| bytes)
        })
    };
    let stdout = read(Box::new(stdout));
    let stderr = read(Box::new(stderr));
    let status = match wait_finite_exit(&mut process) {
        Ok(status) => status,
        Err(error) => {
            // A detached producer can retain a pipe. Do not block cancellation on
            // its reader: no output escapes and its inherited lease fences writers.
            drop(stdout);
            drop(stderr);
            return Err(error);
        }
    };
    let stdout = stdout
        .join()
        .map_err(|_| anyhow::anyhow!("Lake stdout reader panicked"))
        .and_then(|result| result.map_err(Into::into));
    let stderr = stderr
        .join()
        .map_err(|_| anyhow::anyhow!("Lake stderr reader panicked"))
        .and_then(|result| result.map_err(Into::into));
    Ok(Output { status, stdout: stdout?, stderr: stderr? })
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub(crate) enum Outcome {
    Prepared,
    BuildOnly,
    BuildFailed,
    SetupFailed,
}

#[derive(Clone, Debug)]
pub(crate) struct RootResult {
    pub(crate) outcome: Outcome,
    pub(crate) error: Option<String>,
}

#[derive(Debug)]
pub(crate) struct Prepared {
    pub(crate) initial_error: Option<String>,
    pub(crate) roots: Vec<RootResult>,
}

impl Prepared {
    pub(crate) fn failed(&self) -> bool {
        self.initial_error.is_some()
            || self
                .roots
                .iter()
                .any(|r| matches!(r.outcome, Outcome::BuildFailed | Outcome::SetupFailed))
    }
}

#[derive(Deserialize)]
#[serde(tag = "event", rename_all = "camelCase", deny_unknown_fields)]
enum Record {
    Load {
        protocol: u32,
        #[serde(rename = "opId")]
        op_id: String,
        outcome: String,
    },
    Initial {
        protocol: u32,
        #[serde(rename = "opId")]
        op_id: String,
        outcome: String,
        error: Option<String>,
        #[serde(rename = "errorTruncated")]
        error_truncated: Option<bool>,
    },
    Root {
        protocol: u32,
        #[serde(rename = "opId")]
        op_id: String,
        index: usize,
        #[serde(rename = "requestId")]
        request_id: String,
        outcome: Outcome,
        error: Option<String>,
        #[serde(rename = "errorTruncated")]
        error_truncated: Option<bool>,
    },
    Complete {
        protocol: u32,
        #[serde(rename = "opId")]
        op_id: String,
        count: usize,
        failed: bool,
    },
    Fatal {
        protocol: u32,
        #[serde(rename = "opId")]
        op_id: String,
        error: String,
        #[serde(rename = "errorTruncated")]
        error_truncated: bool,
    },
}

fn error_fields(error: &Option<String>, truncated: Option<bool>, failed: bool) -> Result<()> {
    if failed {
        let error = error.as_ref().context("Missing preparation failure summary")?;
        ensure!(
            !error.is_empty() && error.len() <= MAX_ERROR,
            "Invalid preparation failure summary"
        );
        let truncated = truncated.context("Missing preparation truncation flag")?;
        ensure!(
            !truncated || error.ends_with(ERROR_TRUNCATION_NOTICE),
            "Missing preparation truncation notice"
        );
        Ok(())
    } else {
        ensure!(error.is_none() && truncated.is_none(), "Unexpected preparation failure fields");
        Ok(())
    }
}

struct Decoder {
    op_id: String,
    requests: Vec<Request>,
    initial: bool,
    loaded: bool,
    initial_seen: bool,
    terminal: bool,
    fatal: Option<String>,
    result: Prepared,
}

impl Decoder {
    fn record(&mut self, bytes: &[u8]) -> Result<()> {
        ensure!(!self.terminal, "Preparation record after terminal event");
        ensure!(
            bytes.len() <= MAX_RECORD && bytes.last() == Some(&b'\n'),
            "Invalid preparation framing"
        );
        // Option<T> alone treats explicit null like an absent field. The wire
        // grammar requires omission on success and values on failure.
        let value: Value = serde_json::from_slice(bytes)?;
        let object = value.as_object().context("Preparation status must be an object")?;
        let failure = matches!(value["event"].as_str(), Some("fatal"))
            || matches!(value["outcome"].as_str(), Some("buildFailed" | "setupFailed"));
        ensure!(
            object.contains_key("error") == failure
                && object.contains_key("errorTruncated") == failure,
            "Preparation failure fields do not match outcome"
        );
        let record: Record =
            serde_json::from_slice(bytes).context("Invalid preparation status JSON")?;
        let (protocol, op_id) = match &record {
            Record::Load { protocol, op_id, .. }
            | Record::Initial { protocol, op_id, .. }
            | Record::Root { protocol, op_id, .. }
            | Record::Complete { protocol, op_id, .. }
            | Record::Fatal { protocol, op_id, .. } => (*protocol, op_id),
        };
        ensure!(protocol == 1 && op_id == &self.op_id, "Preparation status identity mismatch");
        match record {
            Record::Load { outcome, .. } => {
                ensure!(!self.loaded && outcome == "loaded", "Invalid preparation load event");
                self.loaded = true;
            }
            Record::Initial { outcome, error, error_truncated, .. } => {
                ensure!(
                    self.loaded
                        && self.initial
                        && !self.initial_seen
                        && self.result.roots.is_empty(),
                    "Unexpected preparation initial event"
                );
                ensure!(
                    matches!(outcome.as_str(), "built" | "buildFailed"),
                    "Invalid initial outcome"
                );
                error_fields(&error, error_truncated, outcome == "buildFailed")?;
                self.result.initial_error = error;
                self.initial_seen = true;
            }
            Record::Root { index, request_id, outcome, error, error_truncated, .. } => {
                ensure!(
                    self.loaded && (!self.initial || self.initial_seen),
                    "Root before preparation initial event"
                );
                ensure!(index == self.result.roots.len(), "Preparation root index out of order");
                let expected = self.requests.get(index).context("Too many preparation roots")?;
                ensure!(request_id == expected.request_id, "Preparation root identity mismatch");
                ensure!(
                    !matches!(outcome, Outcome::Prepared) || expected.setup.is_some(),
                    "Unexpected setup success"
                );
                ensure!(
                    !matches!(outcome, Outcome::BuildOnly) || expected.setup.is_none(),
                    "Missing requested setup"
                );
                ensure!(
                    !matches!(outcome, Outcome::SetupFailed) || expected.setup.is_some(),
                    "Unexpected setup failure"
                );
                let failed = matches!(outcome, Outcome::BuildFailed | Outcome::SetupFailed);
                error_fields(&error, error_truncated, failed)?;
                self.result.roots.push(RootResult { outcome, error });
            }
            Record::Complete { count, failed, .. } => {
                ensure!(
                    self.loaded
                        && (!self.initial || self.initial_seen)
                        && count == self.requests.len()
                        && count == self.result.roots.len(),
                    "Incomplete preparation coverage"
                );
                ensure!(failed == self.result.failed(), "Preparation aggregate outcome mismatch");
                self.terminal = true;
            }
            Record::Fatal { error, error_truncated, .. } => {
                error_fields(&Some(error.clone()), Some(error_truncated), true)?;
                self.fatal = Some(error);
                self.terminal = true;
            }
        }
        Ok(())
    }
}

enum Message {
    Record(Vec<u8>),
    Eof,
    Error(String),
}

pub(crate) struct Producer {
    sdk: LeanSdk,
    process: Option<Process>,
    input: Option<JoinHandle<io::Result<()>>>,
    output: Option<JoinHandle<()>>,
    receiver: Option<Receiver<Message>>,
    decoder: Decoder,
    eof: bool,
    exit_status: Option<ExitStatus>,
}

impl Recipe {
    pub(crate) fn spawn(mut self) -> Result<Producer> {
        self.sdk.check_finite_integrity()?;
        // Full build/progress logs use the caller's stderr. A blocked sink
        // blocks an owned child, which cancellation kills before pipe joins;
        // no parent pipe reader can become pinned writing to that sink.
        self.command.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit());
        let lease = FiniteProducerLease::acquire(&self.producer_root)?;
        let mut process = Process::spawn_finite(&mut self.command, lease)?;
        let mut stdin = process.child.stdin.take().context("Missing preparation stdin")?;
        let stdout = process.child.stdout.take().context("Missing preparation stdout")?;
        let (sender, receiver) = mpsc::sync_channel(4);
        let input = thread::spawn(move || stdin.write_all(&self.bytes));
        let output = thread::spawn(move || {
            let mut reader = BufReader::new(stdout);
            loop {
                let mut bytes = Vec::new();
                // Take caps allocation even when a producer never emits newline.
                let result =
                    (&mut reader).take((MAX_RECORD + 1) as u64).read_until(b'\n', &mut bytes);
                let message = match result {
                    Ok(0) => Message::Eof,
                    Ok(_) if bytes.len() <= MAX_RECORD && bytes.last() == Some(&b'\n') => {
                        Message::Record(bytes)
                    }
                    Ok(_) => {
                        Message::Error("Preparation status record exceeds framing limit".into())
                    }
                    Err(error) => Message::Error(error.to_string()),
                };
                let finished = !matches!(message, Message::Record(_));
                if sender.send(message).is_err() || finished {
                    break;
                }
            }
        });
        Ok(Producer {
            sdk: self.sdk,
            process: Some(process),
            input: Some(input),
            output: Some(output),
            receiver: Some(receiver),
            decoder: Decoder {
                op_id: self.op_id,
                requests: self.requests,
                initial: self.initial,
                loaded: false,
                initial_seen: false,
                terminal: false,
                fatal: None,
                result: Prepared { initial_error: None, roots: Vec::new() },
            },
            eof: false,
            exit_status: None,
        })
    }
}

impl Producer {
    #[cfg(test)]
    pub(crate) fn terminal_peer_exited(&self) -> bool {
        self.decoder.terminal && self.exit_status.is_some() && self.eof
    }

    /// None means pending. No root result escapes while the producer runs.
    pub(crate) fn poll(&mut self) -> Result<Option<Prepared>> {
        let result = self.poll_inner();
        if result.is_err() {
            self.cancel();
        }
        result
    }

    fn poll_inner(&mut self) -> Result<Option<Prepared>> {
        ensure!(self.process.is_some(), "Preparation producer already consumed");
        loop {
            match self.receiver.as_ref().context("Missing preparation reader")?.try_recv() {
                Ok(Message::Record(bytes)) => self.decoder.record(&bytes)?,
                Ok(Message::Eof) => {
                    self.eof = true;
                    break;
                }
                Ok(Message::Error(error)) => bail!(error),
                Err(TryRecvError::Empty) => break,
                Err(TryRecvError::Disconnected) if self.eof => break,
                Err(TryRecvError::Disconnected) => bail!("Preparation reader disappeared"),
            }
        }
        if self.exit_status.is_none() {
            self.exit_status = self.process.as_mut().unwrap().child.try_wait()?;
            if self.exit_status.is_some() {
                // An exited leader may leave workers holding stdout open.
                // Terminate the owned group, then keep draining bounded records
                // until EOF before joining pipe readers/writers.
                self.process.as_mut().unwrap().stop();
            }
        }
        let quiescent = if self.exit_status.is_some() {
            self.process.as_mut().unwrap().poll_stopped()?
        } else {
            false
        };
        if !self.eof || !quiescent {
            return Ok(None);
        }
        let Some(status) = self.exit_status else { return Ok(None) };
        // Cancel descendants/reap before waiting for the stdin writer/reader.
        // A descendant retaining a pipe cannot deadlock producer destruction.
        self.cleanup()?;
        self.sdk.check_finite_integrity()?;
        ensure!(self.decoder.terminal, "Preparation EOF before terminal event");
        if let Some(error) = &self.decoder.fatal {
            ensure!(status.code() == Some(2), "Invalid fatal preparation exit");
            bail!("Finite Lean preparation failed: {error}");
        }
        ensure!(
            status.code() == Some(if self.decoder.result.failed() { 1 } else { 0 }),
            "Preparation exit status contradicts coverage"
        );
        Ok(Some(std::mem::replace(
            &mut self.decoder.result,
            Prepared { initial_error: None, roots: Vec::new() },
        )))
    }

    fn cleanup(&mut self) -> Result<()> {
        let quiescent = if let Some(process) = &mut self.process {
            process.stop();
            process.poll_stopped().unwrap_or(false)
        } else {
            true
        };
        self.process.take();
        self.receiver.take();
        if !quiescent {
            // Cancellation/error publishes no result. Detached pipe holders
            // must not pin this caller; their global producer lease remains.
            self.output.take();
            self.input.take();
            return Ok(());
        }
        let output = self
            .output
            .take()
            .map(|thread| thread.join().map_err(|_| anyhow::anyhow!("Preparation reader panicked")))
            .transpose();
        let input = self
            .input
            .take()
            .map(|thread| {
                thread
                    .join()
                    .map_err(|_| anyhow::anyhow!("Preparation writer panicked"))
                    .and_then(|result| result.map_err(Into::into))
            })
            .transpose();
        output?;
        input?;
        Ok(())
    }

    pub(crate) fn cancel(&mut self) {
        let _ = self.cleanup();
    }
}

impl Drop for Producer {
    fn drop(&mut self) {
        self.cancel();
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;

    #[test]
    fn cli_adapter_rejects_live_headers_before_preparation() {
        let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        let directory = tempfile::tempdir().unwrap();
        let workspace =
            Workspace::create(&fixture.sdk, &directory.path().join("workspace"), &["."]).unwrap();
        let request = Request {
            request_id: "live".into(),
            targets: vec![],
            setup: Some(Setup {
                file_name: "New.lean".into(),
                path: workspace.root().join("New.lean"),
                header: Some(json!({})),
            }),
        };
        let error = run(&workspace, &[], &[request], [0; 32]).unwrap_err();
        assert!(error.to_string().contains("does not accept live module headers"));
        assert!(!workspace.root().join("New.lean").exists());
        assert!(!workspace.root().join(".lake/.anneal-local-inputs").exists());
    }

    #[cfg(unix)]
    fn finite_fixture() -> crate::lean_sdk::tests::Fixture {
        use std::{fs, os::unix::fs::PermissionsExt};
        let mut fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        let root = fixture.sdk.root();
        let path = root.join("bin/anneal-finite-lake");
        let bytes = b"#!/bin/sh\nexit 2\n";
        fs::write(&path, bytes).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
        use sha2::{Digest as _, Sha256};
        let mut descriptor: Value =
            serde_json::from_slice(&fs::read(root.join("sdk.json")).unwrap()).unwrap();
        descriptor["schema"] = json!(2);
        descriptor["finite_lake"] = json!({"path":"bin/anneal-finite-lake",
            "sha256": format!("{:x}", Sha256::digest(bytes)), "protocol":1});
        fs::write(root.join("sdk.json"), serde_json::to_vec(&descriptor).unwrap()).unwrap();
        fixture.sdk = LeanSdk::load(root).unwrap();
        fixture
    }

    #[cfg(unix)]
    #[test]
    fn request_chunks_and_individual_input_fallback() {
        use crate::lean_sdk::LakeLibrary;
        let fixture = finite_fixture();
        let temp = tempfile::tempdir().unwrap();
        let workspace =
            Workspace::create(&fixture.sdk, &temp.path().join("workspace"), &["."]).unwrap();
        Workspace::write_lakefile(
            &fixture.sdk,
            workspace.root(),
            &[LakeLibrary { name: "User", source_root: ".", modules: &[] }],
        )
        .unwrap();
        let roots = (0..33)
            .map(|index| Request { request_id: format!("r{index}"), targets: vec![], setup: None })
            .collect::<Vec<_>>();
        assert_eq!(recipe(&workspace, "op", &[], &roots[..32]).unwrap().len(), 1);
        let steps = recipe(&workspace, "op", &["User".into()], &roots).unwrap();
        assert_eq!(steps.len(), 2);
        let Step::Native(first) = &steps[0] else { panic!("Expected native chunk") };
        let Step::Native(second) = &steps[1] else { panic!("Expected native chunk") };
        assert_eq!(first.request_indices, (0..32).collect::<Vec<_>>());
        assert_eq!(second.request_indices, [32]);
        assert!(first.initial && !second.initial);
        assert!(first.bytes.len() <= MAX_PLAN && second.bytes.len() <= MAX_PLAN);
        assert!(matches!(&recipe(&workspace, "op", &vec!["User".into(); 9], &roots).unwrap()[..],
            [Step::Stock { request_indices, .. }] if request_indices.len() == 33));
        let mut roots = roots[..3].to_vec();
        roots[1].targets = vec!["User".into(); 9];
        let steps = recipe(&workspace, "op", &[], &roots).unwrap();
        assert!(
            matches!(&steps[..], [Step::Native(_), Step::Stock { request_indices, .. }, Step::Native(_)] if request_indices == &[1])
        );
        std::fs::write(workspace.root().join("A.lean"), "example : True := by trivial\n").unwrap();
        roots[1].targets.clear();
        roots[1].setup =
            Some(Setup { file_name: "x".repeat(MAX_PLAN), path: "A.lean".into(), header: None });
        let steps = recipe(&workspace, "op", &[], &roots).unwrap();
        assert!(
            matches!(&steps[1], Step::Stock { request_indices, .. } if request_indices == &[1])
        );
        assert!(recipe(&workspace, "op", &[], &[roots[0].clone(), roots[0].clone()]).is_err());
        let mut invalid = roots[0].clone();
        invalid.targets = vec!["--help".into()];
        assert!(recipe(&workspace, "op", &[], &[invalid]).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn descriptor_versions_helper_mutation_and_manifest_gates() {
        use std::fs;

        use crate::lean_sdk::LakeLibrary;
        let fixture = finite_fixture();
        let root = fixture.sdk.root();
        let mut descriptor: Value =
            serde_json::from_slice(&fs::read(root.join("sdk.json")).unwrap()).unwrap();
        descriptor["schema"] = json!(3);
        fs::write(root.join("sdk.json"), serde_json::to_vec(&descriptor).unwrap()).unwrap();
        assert!(LeanSdk::load(root).is_err());
        descriptor["schema"] = json!(2);
        descriptor["finite_lake"]["protocol"] = json!(2);
        fs::write(root.join("sdk.json"), serde_json::to_vec(&descriptor).unwrap()).unwrap();
        assert!(LeanSdk::load(root).is_err());
        descriptor["finite_lake"]["protocol"] = json!(1);
        fs::write(root.join("sdk.json"), serde_json::to_vec(&descriptor).unwrap()).unwrap();
        let sdk = LeanSdk::load(root).unwrap();
        let temp = tempfile::tempdir().unwrap();
        let workspace = Workspace::create(&sdk, &temp.path().join("workspace"), &["."]).unwrap();
        Workspace::write_lakefile(
            &sdk,
            workspace.root(),
            &[LakeLibrary { name: "User", source_root: ".", modules: &[] }],
        )
        .unwrap();
        assert!(workspace.finite_inputs().unwrap().is_some());
        let manifest = workspace.root().join("lake-manifest.json");
        let original_manifest = fs::read(&manifest).unwrap();
        fs::remove_file(&manifest).unwrap();
        assert!(workspace.finite_inputs().is_err());
        assert!(recipe(&workspace, "op", &[], &[]).is_err());
        assert!(!manifest.exists());
        fs::write(&manifest, original_manifest).unwrap();
        fs::write(
            workspace.root().join("lake-manifest.json"),
            b"{\"version\":\"1.2.0\",\"packages\":[{}]}",
        )
        .unwrap();
        assert!(workspace.finite_command().is_err());
        fs::write(root.join("bin/anneal-finite-lake"), b"#!/bin/sh\nexit 0\n").unwrap();
        assert!(sdk.check_finite_integrity().is_err());
        assert!(LeanSdk::load(root).is_err());
        descriptor["schema"] = json!(1);
        descriptor.as_object_mut().unwrap().remove("finite_lake");
        fs::write(root.join("sdk.json"), serde_json::to_vec(&descriptor).unwrap()).unwrap();
        assert!(LeanSdk::load(root).is_ok());
        descriptor["finite_lake"] = Value::Null;
        fs::write(root.join("sdk.json"), serde_json::to_vec(&descriptor).unwrap()).unwrap();
        assert!(LeanSdk::load(root).is_err());
        descriptor["finite_lake"] =
            json!({"path":"bin/anneal-finite-lake","sha256":"a".repeat(64),"protocol":1});
        fs::write(root.join("sdk.json"), serde_json::to_vec(&descriptor).unwrap()).unwrap();
        assert!(LeanSdk::load(root).is_err());
    }

    #[cfg(unix)]
    fn producer_root(fixture: &crate::lean_sdk::tests::Fixture) -> PathBuf {
        let root =
            fixture.sdk.root().parent().unwrap().parent().unwrap().join("producer-workspace");
        std::fs::create_dir(&root).unwrap();
        drop(Workspace::lock_root(&root).unwrap());
        root
    }

    #[cfg(unix)]
    fn producer(command_text: &str, bytes: Vec<u8>) -> (crate::lean_sdk::tests::Fixture, Producer) {
        let fixture = finite_fixture();
        let mut command = Command::new("/bin/sh");
        command.args(["-c", command_text]);
        let producer = Recipe {
            command,
            sdk: fixture.sdk.clone(),
            producer_root: producer_root(&fixture),
            bytes,
            op_id: "op".into(),
            requests: vec![],
            request_indices: vec![],
            initial: false,
        }
        .spawn()
        .unwrap();
        (fixture, producer)
    }

    #[cfg(unix)]
    fn finish(producer: &mut Producer) -> Result<Prepared> {
        use std::time::{Duration, Instant};
        let deadline = Instant::now() + Duration::from_secs(3);
        loop {
            if let Some(result) = producer.poll()? {
                return Ok(result);
            }
            ensure!(Instant::now() < deadline, "Test producer exceeded its deadline");
            thread::sleep(Duration::from_millis(2));
        }
    }

    #[cfg(unix)]
    #[test]
    fn stock_capture_waits_for_a_detached_holder_with_closed_standard_pipes() {
        use std::{
            sync::mpsc,
            time::{Duration, Instant},
        };
        struct ReleaseOnDrop(PathBuf);
        impl Drop for ReleaseOnDrop {
            fn drop(&mut self) {
                let _ = std::fs::write(&self.0, b"release");
            }
        }
        let fixture = finite_fixture();
        let root = fixture.sdk.root().parent().unwrap().parent().unwrap().join("stock-workspace");
        let workspace = Workspace::create(&fixture.sdk, &root, &["."]).unwrap();
        Workspace::write_lakefile(
            &fixture.sdk,
            workspace.root(),
            &[crate::lean_sdk::LakeLibrary { name: "User", source_root: ".", modules: &[] }],
        )
        .unwrap();
        let _writer = workspace.writer_lock().unwrap();
        let preparation = workspace.prepare_local_outputs().unwrap();
        let ready = root.join(".lake/stock-descendant-ready");
        let release = root.join(".lake/stock-descendant-release");
        let leader_exiting = root.join(".lake/stock-leader-exiting");
        thread::scope(|scope| {
            // Drop this release control before scoped joining, including panic.
            let release_on_drop = ReleaseOnDrop(release.clone());
            let (send, result) = mpsc::channel();
            let mut command = Command::new("/usr/bin/python3");
            command
                .args([
                    "-I",
                    "-B",
                    "-c",
                    r#"
import os, pathlib, sys, time
ready, release, exiting = map(pathlib.Path, sys.argv[1:])
if os.fork() == 0:
    os.setsid()
    null = os.open('/dev/null', os.O_RDWR)
    for stream in (0, 1, 2):
        os.dup2(null, stream)
    os.close(null)
    ready.write_text('ready')
    deadline = time.monotonic() + 10
    while not release.exists() and time.monotonic() < deadline:
        time.sleep(0.005)
    os._exit(0)
deadline = time.monotonic() + 3
while not ready.exists():
    if time.monotonic() >= deadline:
        os._exit(2)
    time.sleep(0.005)
print('owned-result', flush=True)
exiting.write_text('exiting')
os._exit(0)
"#,
                ])
                .arg(&ready)
                .arg(&release)
                .arg(&leader_exiting);
            let workspace_ref = &workspace;
            scope.spawn(move || {
                send.send(stock_output(command, workspace_ref)).unwrap();
            });
            let deadline = Instant::now() + Duration::from_secs(3);
            while !leader_exiting.exists() {
                assert!(Instant::now() < deadline, "Stock leader did not finish its public output");
                thread::sleep(Duration::from_millis(5));
            }
            assert!(matches!(
                result.recv_timeout(Duration::from_millis(100)),
                Err(mpsc::RecvTimeoutError::Timeout)
            ));
            assert!(!root.join(".lake/.anneal-local-inputs").exists());
            std::fs::write(&release, b"release").unwrap();
            let output = result.recv_timeout(Duration::from_secs(3)).unwrap().unwrap();
            assert!(output.status.success());
            assert_eq!(output.stdout, b"owned-result\n");
            assert!(output.stderr.is_empty());
            workspace.finish_local_outputs(&preparation).unwrap();
            assert!(root.join(".lake/.anneal-local-inputs").exists());
            drop(release_on_drop);
        });
    }

    #[cfg(unix)]
    #[test]
    fn producer_requires_eof_consistent_exit_and_complete_status() {
        let load = r#"'{"event":"load","protocol":1,"opId":"op","outcome":"loaded"}'"#;
        let complete =
            r#"'{"event":"complete","protocol":1,"opId":"op","count":0,"failed":false}'"#;
        let (_fixture, mut process) =
            producer(&format!("printf '%s\\n' {load} {complete}; exit 0"), vec![]);
        assert!(!finish(&mut process).unwrap().failed());
        for command in [
            format!("printf '%s\\n' {load} {complete}; exit 1"),
            format!("printf '%s\\n' {load}; exit 0"),
            format!("printf '%s\\n' {load} {complete}; kill -TERM $$"),
            format!("printf '%s\\n' {load} {complete} {load}; exit 0"),
            format!("printf '%s' {load}; exit 0"),
        ] {
            let (_fixture, mut process) = producer(&command, vec![]);
            assert!(finish(&mut process).is_err());
            assert!(process.process.is_none());
        }
    }

    #[cfg(unix)]
    #[test]
    fn malformed_reader_cancels_before_blocked_stdin_writer_join() {
        use std::time::{Duration, Instant};
        let start = Instant::now();
        let (_fixture, mut process) =
            producer("printf 'invalid\\n'; sleep 30", vec![b' '; MAX_PLAN]);
        assert!(finish(&mut process).is_err());
        assert!(process.process.is_none() && process.input.is_none() && process.output.is_none());
        assert!(start.elapsed() < Duration::from_secs(3));
        let (_fixture, mut process) = producer("printf '%65537s' x; sleep 30", vec![]);
        assert!(finish(&mut process).is_err());
    }

    // Run this exact probe in a separate unit binary. Descriptor manipulation
    // is confined to that subprocess, never the shared Cargo test runner.
    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn inherited_stderr_probe_child() {
        use std::{
            fs,
            time::{Duration, Instant},
        };
        let Some(directory) = std::env::var_os("ANNEAL_STDERR_PROBE_DIR") else { return };
        let directory = PathBuf::from(directory);
        let blocked = std::env::var("ANNEAL_STDERR_PROBE_MODE").unwrap() == "blocked";
        if blocked {
            unsafe extern "C" {
                fn fcntl(fd: i32, command: i32, ...) -> i32;
            }
            #[cfg(target_os = "macos")]
            let nonblocking = 0x0004;
            #[cfg(target_os = "linux")]
            let nonblocking = 0x0800;
            // F_GETFL/F_SETFL are 3/4 on the two supported test platforms.
            // SAFETY: only this isolated subprocess's inherited fd2 is changed.
            let flags = unsafe { fcntl(2, 3) };
            assert!(flags >= 0);
            assert_eq!(unsafe { fcntl(2, 4, flags | nonblocking) }, 0);
            let mut full = false;
            let mut failure = None;
            for _ in 0..4096 {
                match io::stderr().write(&[b'x'; 4096]) {
                    Ok(_) => {}
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                        full = true;
                        break;
                    }
                    Err(error) => {
                        failure = Some(error);
                        break;
                    }
                }
            }
            assert_eq!(unsafe { fcntl(2, 4, flags) }, 0);
            assert!(failure.is_none(), "Fill inherited stderr: {failure:?}");
            assert!(full, "Inherited stderr never reached actual backpressure");
        }
        let fixture = finite_fixture();
        let mut command = Command::new("/bin/sh");
        let script = if blocked {
            // No descendants are launched in this case. The entry marker
            // precedes the write; closing the sink also ends a delayed shell.
            r#"set -eu; : > "$ANNEAL_BEFORE_WRITE"; printf 'blocked helper log\n' >&2; : > "$ANNEAL_AFTER_WRITE""#
        } else {
            r#"set -eu; printf 'λ useful full log\nsecond line\n' >&2; printf '%s\n' '{"event":"load","protocol":1,"opId":"op","outcome":"loaded"}' '{"event":"root","protocol":1,"opId":"op","index":0,"requestId":"r","outcome":"buildOnly"}' '{"event":"complete","protocol":1,"opId":"op","count":1,"failed":false}'"#
        };
        command
            .args(["-c", script])
            .env("ANNEAL_BEFORE_WRITE", directory.join("before-write"))
            .env("ANNEAL_AFTER_WRITE", directory.join("after-write"));
        let mut process = Recipe {
            command,
            sdk: fixture.sdk.clone(),
            producer_root: producer_root(&fixture),
            bytes: vec![],
            op_id: "op".into(),
            requests: vec![Request { request_id: "r".into(), targets: vec![], setup: None }],
            request_indices: vec![0],
            initial: false,
        }
        .spawn()
        .unwrap();
        // Atomically publish the exact owned group returned by Process::spawn;
        // readers never parse a partially written PID or shell text.
        let pid = process.process.as_ref().unwrap().child.id();
        fs::write(directory.join("helper.pid.tmp"), format!("{pid}:{}\n", !pid)).unwrap();
        fs::rename(directory.join("helper.pid.tmp"), directory.join("helper.pid")).unwrap();
        if blocked {
            let deadline = Instant::now() + Duration::from_secs(3);
            while !directory.join("before-write").exists() {
                assert!(Instant::now() < deadline, "Helper never entered its stderr write");
                thread::sleep(Duration::from_millis(2));
            }
            thread::sleep(Duration::from_millis(30));
            assert!(!directory.join("after-write").exists());
            let cancel = Instant::now();
            process.cancel();
            assert!(
                process.process.is_none() && process.input.is_none() && process.output.is_none()
            );
            assert!(cancel.elapsed() < Duration::from_secs(2));
            fs::write(directory.join("result"), b"cancelled-and-cleaned\n").unwrap();
        } else {
            let prepared = finish(&mut process).unwrap();
            assert!(!prepared.failed() && prepared.initial_error.is_none());
            assert_eq!(prepared.roots.len(), 1);
            assert_eq!(prepared.roots[0].outcome, Outcome::BuildOnly);
            assert!(process.process.is_none());
            fs::write(directory.join("result"), b"buildOnly-complete-and-cleaned\n").unwrap();
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    struct StderrProbe {
        child: std::process::Child,
        directory: PathBuf,
        stderr: Option<std::process::ChildStderr>,
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    impl Drop for StderrProbe {
        fn drop(&mut self) {
            use std::{
                fs,
                time::{Duration, Instant},
            };
            unsafe extern "C" {
                fn kill(pid: i32, signal: i32) -> i32;
            }
            // Stop the coordinator first so it cannot start another producer.
            let _ = self.child.kill();
            let _ = self.child.wait();
            if !self.directory.join("result").exists() {
                // The coordinator atomically publishes its exact owned group.
                // Retain the open sink while admitting a delayed witness; it is
                // closed after this guard, also ending a delayed blocked shell.
                let deadline = Instant::now() + Duration::from_secs(1);
                loop {
                    if let Ok(text) = fs::read_to_string(self.directory.join("helper.pid")) {
                        if let Some((pid, complement)) = text.trim().split_once(':') {
                            if let (Ok(pid), Ok(complement)) =
                                (pid.parse::<u32>(), complement.parse::<u32>())
                            {
                                if pid > 1 && pid <= i32::MAX as u32 && complement == !pid {
                                    // SAFETY: exact group witnessed by the helper
                                    // owner in this isolated test subprocess.
                                    unsafe {
                                        kill(-(pid as i32), 9);
                                    }
                                    break;
                                }
                            }
                        }
                    }
                    if Instant::now() >= deadline {
                        break;
                    }
                    thread::sleep(Duration::from_millis(2));
                }
            }
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    fn stderr_probe(blocked: bool) {
        use std::{
            fs,
            os::unix::process::CommandExt as _,
            time::{Duration, Instant},
        };
        let directory = tempfile::tempdir().unwrap();
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .args([
                "--exact",
                "lean_preparation::tests::inherited_stderr_probe_child",
                "--nocapture",
            ])
            .env("ANNEAL_STDERR_PROBE_DIR", directory.path())
            .env("ANNEAL_STDERR_PROBE_MODE", if blocked { "blocked" } else { "success" })
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::piped())
            .process_group(0);
        let mut child = command.spawn().unwrap();
        let stderr = child.stderr.take().unwrap();
        // The guard owns the read end, so unwinding stops/reaps the coordinator
        // and helper group BEFORE closing this external log sink.
        let mut probe =
            StderrProbe { child, directory: directory.path().into(), stderr: Some(stderr) };
        // Keep this read descriptor OPEN and UNREAD until the coordinator exits.
        // Closing it would test EPIPE rather than a blocked external log sink.
        let deadline = Instant::now() + Duration::from_secs(8);
        let status = loop {
            if let Some(status) = probe.child.try_wait().unwrap() {
                break status;
            }
            assert!(Instant::now() < deadline, "Stderr probe coordinator timed out");
            thread::sleep(Duration::from_millis(2));
        };
        assert!(status.success(), "Stderr probe failed: {status}");
        let result = fs::read(directory.path().join("result")).unwrap();
        if blocked {
            assert_eq!(result, b"cancelled-and-cleaned\n");
            assert!(!directory.path().join("after-write").exists());
        } else {
            assert_eq!(result, b"buildOnly-complete-and-cleaned\n");
            let mut bytes = Vec::new();
            probe.stderr.as_mut().unwrap().read_to_end(&mut bytes).unwrap();
            assert_eq!(bytes, "λ useful full log\nsecond line\n".as_bytes());
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn blocked_inherited_stderr_cancels_and_cleans_up_before_deadline() {
        stderr_probe(true);
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn inherited_stderr_preserves_full_unicode_logs_and_prepared_outcome() {
        stderr_probe(false);
    }

    fn decoder(setup: bool) -> Decoder {
        Decoder {
            op_id: "op".into(),
            requests: vec![Request {
                request_id: "r".into(),
                targets: vec![],
                setup: setup.then(|| Setup {
                    file_name: "A.lean".into(),
                    path: "A.lean".into(),
                    header: None,
                }),
            }],
            initial: true,
            loaded: false,
            initial_seen: false,
            terminal: false,
            fatal: None,
            result: Prepared { initial_error: None, roots: vec![] },
        }
    }
    fn feed(d: &mut Decoder, value: Value) -> Result<()> {
        let mut bytes = serde_json::to_vec(&value)?;
        bytes.push(b'\n');
        d.record(&bytes)
    }
    fn prefix(d: &mut Decoder) {
        feed(d, json!({"event":"load","protocol":1,"opId":"op","outcome":"loaded"})).unwrap();
        feed(d, json!({"event":"initial","protocol":1,"opId":"op","outcome":"built"})).unwrap();
    }
    #[test]
    fn ordinary_failure_retains_complete_coverage() {
        let mut d = decoder(true);
        prefix(&mut d);
        feed(
            &mut d,
            json!({"event":"root","protocol":1,"opId":"op","index":0,"requestId":"r",
            "outcome":"setupFailed","error":"λ\n\"","errorTruncated":false}),
        )
        .unwrap();
        feed(&mut d, json!({"event":"complete","protocol":1,"opId":"op","count":1,"failed":true}))
            .unwrap();
        assert!(d.result.failed());
        assert!(d.terminal);
        assert!(
            feed(&mut d, json!({"event":"load","protocol":1,"opId":"op","outcome":"loaded"}))
                .is_err()
        );
    }
    #[test]
    fn malformed_global_identity_order_and_fields_reject() {
        for value in [
            json!({"event":"load","protocol":2,"opId":"op","outcome":"loaded"}),
            json!({"event":"load","protocol":1,"opId":"other","outcome":"loaded"}),
            json!({"event":"load","protocol":1,"opId":"op","outcome":"loaded","extra":0}),
            json!({"event":"load","protocol":1,"opId":"op","outcome":"loaded","error":null,"errorTruncated":null}),
            json!({"event":"complete","protocol":1,"opId":"op","count":0,"failed":false}),
        ] {
            assert!(feed(&mut decoder(false), value).is_err());
        }
        let mut d = decoder(false);
        prefix(&mut d);
        assert!(
            feed(
                &mut d,
                json!({"event":"root","protocol":1,"opId":"op","index":0,
            "requestId":"r","outcome":"prepared"})
            )
            .is_err()
        );
    }
    #[test]
    fn encoded_and_utf8_error_limits() {
        assert!(error_fields(&Some("λ".repeat(4096)), Some(false), true).is_ok());
        assert!(error_fields(&Some("λ".repeat(4097)), Some(false), true).is_err());
        assert!(error_fields(&Some("missing notice".into()), Some(true), true).is_err());
        let summary = format!(
            "{}{}",
            "λ".repeat((MAX_ERROR - ERROR_TRUNCATION_NOTICE.len()) / 2),
            ERROR_TRUNCATION_NOTICE
        );
        assert!(error_fields(&Some(summary.clone()), Some(true), true).is_ok());
        assert!(error_fields(&Some(summary), Some(false), true).is_ok());
        let oversized = format!("{}{}", "λ".repeat(MAX_ERROR / 2), ERROR_TRUNCATION_NOTICE);
        assert!(error_fields(&Some(oversized), Some(true), true).is_err());
        let mut d = decoder(true);
        prefix(&mut d);
        feed(
            &mut d,
            json!({"event":"root","protocol":1,"opId":"op","index":0,"requestId":"r",
            "outcome":"setupFailed","error":format!("{}{}",
                "\0".repeat(MAX_ERROR - ERROR_TRUNCATION_NOTICE.len()), ERROR_TRUNCATION_NOTICE),
            "errorTruncated":true}),
        )
        .unwrap();
        assert!(d.record(&vec![b' '; MAX_RECORD + 1]).is_err());
        assert!(!identity(""));
        assert!(!identity("non ascii λ"));
        assert!(identity(&"x".repeat(64)));
        assert!(!identity(&"x".repeat(65)));
    }
}
