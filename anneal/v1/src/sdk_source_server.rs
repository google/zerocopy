// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Separate read-only client for an admitted SDK source project. It uses the
//! same consumer binding, never launches a build, and ends on context changes.
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::{self, BufReader, Read},
    path::Path,
    process::Stdio,
    sync::mpsc::{self, SyncSender},
    thread,
    time::{Duration, Instant},
};

use anyhow::{Context, Result, ensure};
use serde_json::{Value, json};

use crate::{
    lean_sdk::{LakeOperation, Workspace},
    lean_server::{self, Process, file_uri, read_message, write_message},
};

fn uri(path: &Path) -> Result<String> {
    let mut uri = String::from("file://");
    for byte in path.to_str().context("Non-UTF8 editor path")?.bytes() {
        if byte.is_ascii_alphanumeric() || b"/._-~".contains(&byte) {
            uri.push(byte as char);
        } else {
            uri.push_str(&format!("%{byte:02X}"));
        }
    }
    Ok(uri)
}

fn admit_consumer_context(workspace: &Workspace<'_>, stamp: [u8; 32]) -> Result<()> {
    workspace.admit()?;
    // The full source stamp includes the root's physical identity as well as
    // saved inputs. Replacing a workspace ends this client even if its bytes
    // and binding are unchanged; its Lake process still owns the original cwd.
    ensure!(
        workspace.source_stamp()? == stamp,
        "Consumer context changed; restart the read-only SDK source client"
    );
    Ok(())
}

fn remap_initialize(message: &mut Value, source_project: &Path, consumer: &Path) -> Result<()> {
    let params = &mut message["params"];
    ensure!(
        params["initializationOptions"]["logCfg"].is_null(),
        "SDK source client logging overrides are unsupported"
    );
    let mut identified = false;
    if let Some(root) = params["rootUri"].as_str() {
        ensure!(
            file_uri(root)?.canonicalize()? == source_project,
            "Foreign SDK source initialization root"
        );
        identified = true;
    }
    if let Some(root) = params["rootPath"].as_str() {
        ensure!(
            Path::new(root).canonicalize()? == source_project,
            "Foreign SDK source initialization path"
        );
        identified = true;
    }
    if let Some(folders) = params["workspaceFolders"].as_array() {
        ensure!(folders.len() <= 1, "Multiple source projects are unsupported");
        for folder in folders {
            ensure!(
                file_uri(folder["uri"].as_str().context("Missing source folder URI")?)?
                    .canonicalize()?
                    == source_project,
                "Foreign SDK source workspace folder"
            );
            identified = true;
        }
    }
    ensure!(identified, "SDK source initialization must identify its admitted project");
    let root = uri(consumer)?;
    params["rootUri"] = json!(root);
    params["rootPath"] = json!(consumer);
    params["workspaceFolders"] = json!([{"uri": root, "name": "Anneal bound consumer"}]);
    Ok(())
}

fn readonly_method(method: &str) -> bool {
    matches!(
        method,
        "initialize"
            | "shutdown"
            | "textDocument/hover"
            | "textDocument/definition"
            | "textDocument/typeDefinition"
            | "textDocument/declaration"
            | "textDocument/references"
            | "textDocument/documentSymbol"
            | "textDocument/semanticTokens/full"
            | "textDocument/semanticTokens/full/delta"
            | "textDocument/semanticTokens/range"
            | "$/lean/plainGoal"
            | "$/lean/plainTermGoal"
            | "$/lean/rpc/connect"
            | "$/lean/rpc/call"
    )
}

fn disabled_probe_method(method: &str) -> bool {
    matches!(
        method,
        "textDocument/codeAction"
            | "textDocument/completion"
            | "textDocument/signatureHelp"
            | "textDocument/documentHighlight"
            | "textDocument/foldingRange"
            | "textDocument/documentColor"
            | "textDocument/colorPresentation"
            | "textDocument/inlayHint"
            | "textDocument/prepareCallHierarchy"
            | "textDocument/prepareRename"
            | "textDocument/rename"
            | "textDocument/formatting"
            | "textDocument/rangeFormatting"
    )
}

fn closed_request(message: &Value, closed: &BTreeSet<String>) -> Option<Value> {
    let method = message["method"].as_str()?;
    let id = message.get("id")?;
    let document_method = (readonly_method(method) && !matches!(method, "initialize" | "shutdown"))
        || disabled_probe_method(method);
    if document_method && closed.contains(document_uri(message)?) {
        Some(
            json!({"jsonrpc":"2.0","id":id,"error":{"code":-32801,"message":"SDK source document closed"}}),
        )
    } else {
        None
    }
}

fn document_uri(message: &Value) -> Option<&str> {
    message["params"]["textDocument"]["uri"].as_str().or_else(|| message["params"]["uri"].as_str())
}

// Match the primary coordinator's four versioned notification classes. The
// URI/version pair scopes an open document; identical versions reused after a
// close/reopen are not distinguished by this gate alone.
fn current_versioned_notification(documents: &BTreeMap<String, i64>, message: &Value) -> bool {
    let method = message["method"].as_str().unwrap_or("");
    if ![
        "textDocument/publishDiagnostics",
        "$/lean/fileProgress",
        "$/lean/ileanInfoUpdate",
        "$/lean/ileanInfoFinal",
    ]
    .contains(&method)
    {
        return true;
    }
    let uri = message["params"]["uri"].as_str().or_else(|| document_uri(message));
    let version = message["params"]["version"]
        .as_i64()
        .or_else(|| message["params"]["textDocument"]["version"].as_i64());
    version.is_some() && uri.and_then(|uri| documents.get(uri)).copied() == version
}

/// Stock clients can still issue disabled UI probes. Decline them without
/// forwarding any editing operation or killing useful read-only sessions.
fn decline_probe(
    message: &Value,
    initialized: bool,
    documents: &BTreeMap<String, i64>,
) -> Result<Option<Value>> {
    if !message["method"].as_str().is_some_and(disabled_probe_method) {
        return Ok(None);
    }
    ensure!(initialized, "Initialization is required");
    let id = message.get("id").context("Source probe must be a request")?;
    let uri = document_uri(message).context("Missing source probe URI")?;
    ensure!(documents.contains_key(uri), "Source probe for an unopened SDK document");
    Ok(Some(json!({"jsonrpc":"2.0", "id":id,
        "error":{"code":-32601,"message":"Unsupported operation in immutable SDK source view"}})))
}

fn readonly_capabilities(message: &mut Value) {
    let Some(capabilities) = message
        .get_mut("result")
        .and_then(|result| result.get_mut("capabilities"))
        .and_then(Value::as_object_mut)
    else {
        return;
    };
    capabilities.retain(|key, _| {
        matches!(
            key.as_str(),
            "textDocumentSync"
                | "hoverProvider"
                | "definitionProvider"
                | "typeDefinitionProvider"
                | "declarationProvider"
                | "referencesProvider"
                | "documentSymbolProvider"
                | "semanticTokensProvider"
                | "experimental"
        )
    });
    if let Some(sync) = capabilities.get_mut("textDocumentSync").and_then(Value::as_object_mut) {
        sync.insert("save".into(), json!(false));
    }
    if let Some(experimental) = capabilities.get_mut("experimental").and_then(Value::as_object_mut)
    {
        experimental.retain(|key, _| key == "rpcProvider");
    }
}

fn admit_buffer(path: &Path, text: &str, published: bool) -> Result<()> {
    ensure!(published, "Only exact published SDK source documents are supported");
    ensure!(
        fs::read_to_string(path)? == text,
        "SDK source buffers must equal immutable published bytes"
    );
    Ok(())
}

fn forward_housekeeping(
    message: &Value,
    documents: &BTreeMap<String, i64>,
    closed: &BTreeSet<String>,
) -> Result<bool> {
    let uri = document_uri(message).context("Missing RPC housekeeping source URI")?;
    if documents.contains_key(uri) {
        return Ok(true);
    }
    // Lean's RPC client may release references after didClose. These releases
    // belong to a former worker and should not terminate another open SDK tab.
    ensure!(closed.contains(uri), "RPC housekeeping for an unopened SDK source document");
    Ok(false)
}

enum Event {
    Client(Result<Option<Value>>),
    Server(Result<Option<Value>>),
}

struct Request {
    original: Value,
    document: Option<(String, i64)>,
    initialize: bool,
}

fn admit_request_id(message: &Value, requests: &BTreeMap<String, Request>) -> Result<()> {
    if let Some(id) = message.get("id") {
        ensure!(
            requests.values().all(|request| &request.original != id),
            "Duplicate source request ID"
        );
    }
    Ok(())
}

fn restore_response(message: &mut Value, request: Request) {
    message["id"] = request.original;
    if request.initialize {
        readonly_capabilities(message);
    }
}
fn reader(input: impl Read + Send + 'static, server: bool, sender: SyncSender<Event>) {
    thread::spawn(move || {
        let mut input = BufReader::new(input);
        loop {
            let value = read_message(&mut input);
            let done = !matches!(value, Ok(Some(_)));
            if sender
                .send(if server { Event::Server(value) } else { Event::Client(value) })
                .is_err()
                || done
            {
                break;
            }
        }
    });
}

/// The finite gateway supplies an admitted stock source-project argument.
/// Caller options, shared cwd execution, SDK builds and local edits are absent.
pub fn run(workspace: &Workspace<'_>, source_project: &Path, startup: fs::File) -> Result<()> {
    // The editor gateway installs cancellation and carries the same writer
    // through constructor, argument/project admission and this initialization.
    ensure!(workspace.admit_sdk_source_project(source_project)?, "Unadmitted SDK source project");
    let source_project = source_project.canonicalize()?;
    let mut startup = Some(startup);
    let initialization_deadline = Instant::now() + Duration::from_secs(60);
    let stamp = workspace.source_stamp()?;
    let mut command = workspace.lake_command(LakeOperation::Serve)?;
    command.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit());
    let mut server = Process::spawn(&mut command)?;
    let mut input = server.child.stdin.take().context("Missing source server stdin")?;
    let (sender, events) = mpsc::sync_channel(256);
    reader(
        server.child.stdout.take().context("Missing source server stdout")?,
        true,
        sender.clone(),
    );
    reader(io::stdin(), false, sender);
    let mut output = io::stdout().lock();
    let mut documents = BTreeMap::<String, i64>::new();
    let mut closed_documents = BTreeSet::<String>::new();
    let mut requests = BTreeMap::<String, Request>::new();
    let mut sequence = 0u64;
    let mut initialized = false;
    loop {
        if lean_server::interrupted() {
            return Ok(());
        }
        ensure!(
            startup.is_none() || Instant::now() < initialization_deadline,
            "SDK source client initialization timed out; close it before retrying"
        );
        let event = match events.recv_timeout(Duration::from_millis(100)) {
            Ok(event) => event,
            Err(mpsc::RecvTimeoutError::Timeout) => continue,
            Err(error) => return Err(error.into()),
        };
        if matches!(&event, Event::Client(Ok(None))) {
            return Ok(());
        }
        if let Event::Client(Ok(Some(message))) = &event {
            if message["method"] == "exit" {
                write_message(&mut input, message)?;
                return Ok(());
            }
        }
        let _shared = if startup.is_none() {
            // The source client's own startup writer can cause the primary
            // coordinator to refresh. Wait for that private-output cycle,
            // then require the captured saved context to remain identical.
            // A changed context still ends this client instead of reusing it.
            let deadline = Instant::now() + Duration::from_secs(60);
            Some(loop {
                ensure!(!lean_server::interrupted(), "SDK source client interrupted");
                if let Some(lock) = workspace.try_shared_lock()? {
                    break lock;
                }
                ensure!(
                    Instant::now() < deadline,
                    "Workspace writer is busy; restart the SDK source client after it completes"
                );
                thread::sleep(Duration::from_millis(100));
            })
        } else {
            None
        };
        admit_consumer_context(workspace, stamp)?;
        let mut release_startup = false;
        match event {
            Event::Client(Ok(None)) => return Ok(()),
            Event::Server(Ok(None)) => anyhow::bail!(
                "Bound SDK source server exited unexpectedly: {:?}",
                server.child.try_wait()?
            ),
            Event::Client(Err(error)) | Event::Server(Err(error)) => return Err(error),
            Event::Client(Ok(Some(mut message))) => {
                let method =
                    message["method"].as_str().context("Unexpected client response")?.to_owned();
                admit_request_id(&message, &requests)?;
                if let Some(response) = closed_request(&message, &closed_documents) {
                    write_message(&mut output, &response)?;
                    continue;
                }
                if let Some(response) = decline_probe(&message, initialized, &documents)? {
                    write_message(&mut output, &response)?;
                    continue;
                }
                match method.as_str() {
                    "initialize" => {
                        ensure!(!initialized, "Duplicate initialization");
                        remap_initialize(&mut message, &source_project, workspace.root())?;
                        initialized = true;
                    }
                    "initialized" => {
                        ensure!(initialized, "Initialization is required");
                        release_startup = true;
                    }
                    "textDocument/didOpen" => {
                        let uri = document_uri(&message).context("Missing source URI")?.to_owned();
                        let path = file_uri(&uri)?;
                        admit_buffer(
                            &path,
                            message["params"]["textDocument"]["text"]
                                .as_str()
                                .context("Missing source buffer")?,
                            workspace.contains_sdk_source(&path)?,
                        )?;
                        let version = message["params"]["textDocument"]["version"]
                            .as_i64()
                            .context("Missing source version")?;
                        closed_documents.remove(&uri);
                        ensure!(
                            documents.insert(uri, version).is_none(),
                            "Duplicate source document"
                        );
                        message["params"]["dependencyBuildMode"] = json!("never");
                    }
                    "textDocument/didClose" => {
                        let uri = document_uri(&message).context("Missing close URI")?;
                        ensure!(documents.remove(uri).is_some(), "Unknown source document");
                        closed_documents.insert(uri.to_owned());
                        let closed: Vec<_> = requests
                            .iter()
                            .filter(|(_, request)| {
                                request.document.as_ref().is_some_and(|(path, _)| path == uri)
                            })
                            .map(|(key, _)| key.clone())
                            .collect();
                        for key in closed {
                            let id = requests.remove(&key).unwrap().original;
                            write_message(
                                &mut output,
                                &json!({"jsonrpc":"2.0","id":id,"error":{"code":-32801,"message":"SDK source document closed"}}),
                            )?;
                            write_message(
                                &mut input,
                                &json!({"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":key}}),
                            )?;
                        }
                    }
                    "textDocument/didChange" | "textDocument/didSave" | "workspace/applyEdit" => {
                        anyhow::bail!("SDK source documents are read-only")
                    }
                    "workspace/didChangeConfiguration" | "workspace/didChangeWatchedFiles" => {
                        continue;
                    }
                    "$/setTrace" => {
                        ensure!(
                            message["params"]["value"] == "off",
                            "Source server tracing overrides are unsupported"
                        );
                    }
                    "exit" => {
                        write_message(&mut input, &message)?;
                        let end = Instant::now() + Duration::from_millis(500);
                        while server.child.try_wait()?.is_none() && Instant::now() < end {
                            thread::sleep(Duration::from_millis(10));
                        }
                        return Ok(());
                    }
                    "$/cancelRequest" => {
                        let Some(key) = requests
                            .iter()
                            .find(|(_, request)| request.original == message["params"]["id"])
                            .map(|(key, _)| key.clone())
                        else {
                            continue;
                        };
                        message["params"]["id"] = json!(key);
                    }
                    "$/lean/rpc/keepAlive" | "$/lean/rpc/release" => {
                        if !forward_housekeeping(&message, &documents, &closed_documents)? {
                            continue;
                        }
                    }
                    _ => ensure!(
                        readonly_method(&method),
                        "Unsupported writable or foreign source-client method: {method}"
                    ),
                }
                if let Some(id) = message.get("id") {
                    let document = document_uri(&message)
                        .map(|uri| {
                            documents
                                .get(uri)
                                .map(|version| (uri.to_owned(), *version))
                                .context("Request for an unopened source document")
                        })
                        .transpose()?;
                    ensure!(
                        method == "initialize" || method == "shutdown" || document.is_some(),
                        "Source request must identify an open SDK document"
                    );
                    sequence += 1;
                    let key = format!("anneal-sdk-source-{sequence}");
                    requests.insert(
                        key.clone(),
                        Request {
                            original: id.clone(),
                            document,
                            initialize: method == "initialize",
                        },
                    );
                    message["id"] = json!(key);
                }
                write_message(&mut input, &message)?;
            }
            Event::Server(Ok(Some(mut message))) => {
                if message["method"].is_string() && message.get("id").is_some() {
                    let id = &message["id"];
                    let response = if message["method"] == "workspace/applyEdit" {
                        json!({"jsonrpc":"2.0","id":id,"result":{"applied":false,"failureReason":"Immutable SDK source client"}})
                    } else {
                        json!({"jsonrpc":"2.0","id":id,"error":{"code":-32601,"message":"Unsupported source-client request"}})
                    };
                    write_message(&mut input, &response)?;
                    continue;
                }
                if let Some(id) = message.get("id") {
                    let Some(request) = requests.remove(id.as_str().unwrap_or("")) else {
                        continue;
                    };
                    if request
                        .document
                        .as_ref()
                        .is_some_and(|(uri, version)| documents.get(uri) != Some(version))
                    {
                        continue;
                    }
                    restore_response(&mut message, request);
                } else if !current_versioned_notification(&documents, &message) {
                    continue;
                }
                ensure!(
                    !matches!(
                        message["method"].as_str(),
                        Some("workspace/applyEdit" | "workspace/executeCommand")
                    ),
                    "Writable source-server notification rejected"
                );
                write_message(&mut output, &message)?;
            }
        }
        if release_startup {
            startup.take();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn identical_saved_inputs_in_a_replaced_workspace_end_the_source_context() {
        use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _};

        let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path().join("workspace");
        let workspace = Workspace::create(&fixture.sdk, &root, &["user"]).unwrap();
        fs::create_dir(root.join("user")).unwrap();
        fs::write(root.join("user/Proof.lean"), "example : True := by trivial\n").unwrap();
        let stamp = workspace.source_stamp().unwrap();
        admit_consumer_context(&workspace, stamp).unwrap();
        let before = fs::metadata(&root).unwrap();
        let retired = temp.path().join("retired-workspace");
        fs::rename(&root, &retired).unwrap();
        fs::create_dir(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        // Preserve every entry, including the original saved files and output
        // owner, while replacing only the root directory they are housed in.
        for entry in fs::read_dir(&retired).unwrap() {
            let entry = entry.unwrap();
            fs::rename(entry.path(), root.join(entry.file_name())).unwrap();
        }
        fs::remove_dir(&retired).unwrap();
        workspace.admit().unwrap();
        assert_ne!(fs::metadata(&root).unwrap().ino(), before.ino());
        assert_eq!(
            fs::read_to_string(root.join("user/Proof.lean")).unwrap(),
            "example : True := by trivial\n"
        );
        let error = admit_consumer_context(&workspace, stamp).unwrap_err();
        assert!(error.to_string().contains("Consumer context changed"));
        admit_consumer_context(&workspace, workspace.source_stamp().unwrap()).unwrap();
    }
    #[test]
    fn all_versioned_notifications_require_the_current_open_source_document() {
        const URI: &str = "file:///SDK/Open.lean";
        const OTHER: &str = "file:///SDK/Other.lean";
        for method in [
            "textDocument/publishDiagnostics",
            "$/lean/fileProgress",
            "$/lean/ileanInfoUpdate",
            "$/lean/ileanInfoFinal",
        ] {
            for nested in [false, true] {
                let message = |uri: &str, version: i64| {
                    let params = if nested {
                        json!({"textDocument":{"uri":uri,"version":version}})
                    } else {
                        json!({"uri":uri,"version":version})
                    };
                    json!({"jsonrpc":"2.0","method":method,"params":params})
                };
                let mut documents = BTreeMap::from([(URI.to_owned(), 7), (OTHER.to_owned(), 11)]);
                let old = message(URI, 7);
                assert!(
                    current_versioned_notification(&documents, &old),
                    "{method}, nested={nested}"
                );
                assert!(!current_versioned_notification(&documents, &message(URI, 6)));
                assert!(!current_versioned_notification(
                    &documents,
                    &message("file:///Foreign.lean", 7)
                ));
                // didClose removes ownership; other open documents remain valid.
                documents.remove(URI);
                assert!(!current_versioned_notification(&documents, &old));
                assert!(current_versioned_notification(&documents, &message(OTHER, 11)));
                // A reopened document has its newly supplied client version.
                documents.insert(URI.to_owned(), 9);
                assert!(!current_versioned_notification(&documents, &old));
                assert!(current_versioned_notification(&documents, &message(URI, 9)));
                assert_eq!(
                    documents,
                    BTreeMap::from([(URI.to_owned(), 9), (OTHER.to_owned(), 11)])
                );
            }
        }
    }

    #[test]
    fn versioned_notifications_reject_missing_scope_without_filtering_other_notifications() {
        const URI: &str = "file:///SDK/Open.lean";
        let documents = BTreeMap::from([(URI.to_owned(), 7)]);
        for method in [
            "textDocument/publishDiagnostics",
            "$/lean/fileProgress",
            "$/lean/ileanInfoUpdate",
            "$/lean/ileanInfoFinal",
        ] {
            for params in [
                json!({}),
                json!({"uri":URI}),
                json!({"version":7}),
                json!({"uri":URI,"version":"7"}),
                json!({"uri":URI,"version":7.5}),
                json!({"uri":17,"version":7}),
                json!({"textDocument":{"uri":URI}}),
                json!({"textDocument":{"version":7}}),
                json!({"textDocument":{"uri":URI,"version":null}}),
            ] {
                let message = json!({"method":method,"params":params});
                assert!(!current_versioned_notification(&documents, &message), "{message}");
            }
        }
        for message in [
            json!({"method":"window/logMessage","params":{"type":3,"message":"ready"}}),
            json!({"method":"telemetry/event","params":{"version":"arbitrary data"}}),
            json!({"method":"$/lean/serverStatus","params":{"uri":"file:///Foreign.lean"}}),
        ] {
            assert!(current_versioned_notification(&documents, &message));
            assert!(current_versioned_notification(&BTreeMap::new(), &message));
        }
    }

    #[test]
    fn disabled_editor_probe_preserves_readonly_transport_and_document_state() {
        let documents = BTreeMap::from([("file:///SDK/Open.lean".to_owned(), 1)]);
        let probe = json!({"jsonrpc":"2.0", "id":17, "method":"textDocument/codeAction",
            "params":{"textDocument":{"uri":"file:///SDK/Open.lean"}}});
        let mut output = Vec::new();
        write_message(&mut output, &decline_probe(&probe, true, &documents).unwrap().unwrap())
            .unwrap();
        let reply = read_message(&mut BufReader::new(output.as_slice())).unwrap().unwrap();
        assert_eq!(reply["id"], 17);
        assert_eq!(reply["error"]["code"], -32601);
        for method in ["textDocument/hover", "$/lean/rpc/connect", "$/lean/rpc/call"] {
            let next = json!({"id":18,"method":method,"params":{"textDocument":{"uri":"file:///SDK/Open.lean"}}});
            assert!(decline_probe(&next, true, &documents).unwrap().is_none());
            assert!(readonly_method(method));
        }
        assert_eq!(documents.get("file:///SDK/Open.lean"), Some(&1));
        assert!(decline_probe(&probe, false, &documents).is_err());
        assert!(decline_probe(&probe, true, &BTreeMap::new()).is_err());
        let mut notification = probe;
        notification.as_object_mut().unwrap().remove("id");
        assert!(decline_probe(&notification, true, &documents).is_err());
    }
    #[test]
    fn source_capabilities_keep_navigation_and_rpc_without_editing_providers() {
        let mut response = json!({"result":{"capabilities":{
            "textDocumentSync":{"openClose":true,"change":2,"save":true},
            "hoverProvider":true,"definitionProvider":true,"codeActionProvider":true,
            "completionProvider":{"triggerCharacters":["."]},"renameProvider":true,
            "semanticTokensProvider":{"legend":{"tokenTypes":["variable"]}},
            "experimental":{"rpcProvider":true,"moduleHierarchyProvider":true}
        }}});
        readonly_capabilities(&mut response);
        let caps = &response["result"]["capabilities"];
        assert_eq!(caps["hoverProvider"], true);
        assert_eq!(caps["definitionProvider"], true);
        assert_eq!(caps["experimental"], json!({"rpcProvider":true}));
        assert_eq!(caps["semanticTokensProvider"]["legend"]["tokenTypes"][0], "variable");
        assert_eq!(caps["textDocumentSync"]["change"], 2);
        assert_eq!(caps["textDocumentSync"]["save"], false);
        for key in ["codeActionProvider", "completionProvider", "renameProvider"] {
            assert!(caps.get(key).is_none());
        }
    }
    #[test]
    fn arbitrary_rpc_capabilities_payload_and_pending_request_ids_are_preserved() {
        let payload = json!({"capabilities":{"codeActionProvider":"RPC application data"}});
        let mut response = json!({"id":"backend-id", "result":payload});
        restore_response(
            &mut response,
            Request { original: json!(17), document: None, initialize: false },
        );
        assert_eq!(response["id"], 17);
        assert_eq!(response["result"], payload);
        let requests = BTreeMap::from([(
            "backend-id".to_owned(),
            Request { original: json!(17), document: None, initialize: false },
        )]);
        let probe = json!({"id":17,"method":"textDocument/codeAction"});
        assert!(admit_request_id(&probe, &requests).is_err());
        assert!(
            admit_request_id(&json!({"id":18,"method":"textDocument/hover"}), &requests).is_ok()
        );
        assert_eq!(requests.len(), 1);
    }
    #[test]
    fn finite_readonly_methods_exclude_edits_commands_and_unknown_extensions() {
        for method in
            ["textDocument/definition", "textDocument/hover", "$/lean/rpc/call", "shutdown"]
        {
            assert!(readonly_method(method));
        }
        for method in [
            "workspace/executeCommand",
            "workspace/applyEdit",
            "textDocument/rename",
            "textDocument/formatting",
            "textDocument/codeAction",
            "unknown",
        ] {
            assert!(!readonly_method(method));
        }
    }
    #[test]
    fn source_initialization_is_checked_before_remapping_and_rejects_logging() {
        let temp = tempfile::tempdir().unwrap();
        let project = temp.path().canonicalize().unwrap();
        let consumer = project.join("consumer with spaces");
        let mut initialize = json!({"params":{"rootUri":uri(&project).unwrap(),"rootPath":project,"workspaceFolders":[{"uri":uri(&project).unwrap()}]}});
        remap_initialize(&mut initialize, &project, &consumer).unwrap();
        assert_eq!(file_uri(initialize["params"]["rootUri"].as_str().unwrap()).unwrap(), consumer);
        assert_eq!(initialize["params"]["rootPath"], json!(consumer));
        let mut foreign = json!({"params":{"rootUri":"file:///"}});
        assert!(remap_initialize(&mut foreign, &project, &consumer).is_err());
        let mut logged = json!({"params":{"rootUri":uri(&project).unwrap(),"initializationOptions":{"logCfg":{"logDir":"/tmp"}}}});
        assert!(remap_initialize(&mut logged, &project, &consumer).is_err());
        assert!(remap_initialize(&mut json!({"params":{}}), &project, &consumer).is_err());
        let mut multiple = json!({"params":{"rootUri":uri(&project).unwrap(),"workspaceFolders":[{"uri":uri(&project).unwrap()},{"uri":uri(&project).unwrap()}]}});
        assert!(remap_initialize(&mut multiple, &project, &consumer).is_err());
        let mut wrong_path = json!({"params":{"rootUri":uri(&project).unwrap(),"rootPath":"/"}});
        assert!(remap_initialize(&mut wrong_path, &project, &consumer).is_err());
    }
    #[test]
    fn source_buffer_requires_exact_published_membership_and_bytes() {
        let temp = tempfile::tempdir().unwrap();
        let file = temp.path().join("Source.lean");
        fs::write(&file, "example : True := by trivial\n").unwrap();
        admit_buffer(&file, "example : True := by trivial\n", true).unwrap();
        assert!(admit_buffer(&file, "example : False := by trivial\n", true).is_err());
        assert!(admit_buffer(&file, "example : True := by trivial\n", false).is_err());
        assert_eq!(fs::read_to_string(file).unwrap(), "example : True := by trivial\n");
    }

    #[test]
    fn late_rpc_release_for_closed_admitted_document_does_not_end_other_tabs() {
        let mut documents = BTreeMap::from([("file:///SDK/Open.lean".to_owned(), 1)]);
        let mut closed = BTreeSet::new();
        let release =
            json!({"method":"$/lean/rpc/release", "params":{"uri":"file:///SDK/Open.lean"}});
        assert!(forward_housekeeping(&release, &documents, &closed).unwrap());
        documents.remove("file:///SDK/Open.lean");
        closed.insert("file:///SDK/Open.lean".to_owned());
        documents.insert("file:///SDK/Other.lean".to_owned(), 1);
        assert!(!forward_housekeeping(&release, &documents, &closed).unwrap());
        assert!(documents.contains_key("file:///SDK/Other.lean"));
        let foreign =
            json!({"method":"$/lean/rpc/keepAlive", "params":{"uri":"file:///Foreign.lean"}});
        assert!(forward_housekeeping(&foreign, &documents, &closed).is_err());
        assert!(forward_housekeeping(&json!({}), &documents, &closed).is_err());
    }

    #[test]
    fn late_readonly_requests_for_closed_admitted_document_are_obsolete() {
        let closed = BTreeSet::from(["file:///SDK/Closed.lean".to_owned()]);
        for method in ["textDocument/hover", "$/lean/rpc/call", "textDocument/codeAction"] {
            let request = json!({"id":17,"method":method,"params":{"textDocument":{"uri":"file:///SDK/Closed.lean"}}});
            let response = closed_request(&request, &closed).unwrap();
            assert_eq!(response["id"], 17);
            assert_eq!(response["error"]["code"], -32801);
        }
        for request in [
            json!({"id":18,"method":"textDocument/hover","params":{"uri":"file:///Foreign.lean"}}),
            json!({"method":"textDocument/didChange","params":{"uri":"file:///SDK/Closed.lean"}}),
            json!({"id":18,"method":"unknown","params":{"uri":"file:///SDK/Closed.lean"}}),
        ] {
            assert!(closed_request(&request, &closed).is_none());
        }
    }

    #[test]
    fn open_sdk_navigation_is_not_rejected_as_a_closed_document() {
        let closed = BTreeSet::from(["file:///SDK/Closed.lean".to_owned()]);
        for method in [
            "textDocument/hover",
            "textDocument/definition",
            "textDocument/semanticTokens/full",
            "$/lean/rpc/connect",
            "$/lean/rpc/call",
            "textDocument/codeAction",
        ] {
            for uri_field in ["textDocument", "uri"] {
                let mut request = json!({"id":17,"method":method,"params":{}});
                for document in ["Open", "Closed", "Foreign"] {
                    let uri = format!("file:///SDK/{document}.lean");
                    request["params"] = if uri_field == "textDocument" {
                        json!({"textDocument":{"uri":uri}})
                    } else {
                        json!({"uri":uri})
                    };
                    let response = closed_request(&request, &closed);
                    if document == "Closed" {
                        let response = response.unwrap();
                        assert_eq!(response["id"], 17);
                        assert_eq!(response["error"]["code"], -32801);
                    } else {
                        assert!(response.is_none(), "{method} for {document} via {uri_field}");
                    }
                }
            }
        }
    }
}
