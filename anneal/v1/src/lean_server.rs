// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! A freshness coordinator in front of the stock Lake language server.
//!
//! The SDK and output ownership remain the responsibility of `lean_sdk`. This
//! module only coordinates saved local inputs, live document versions, and
//! server generations. It never writes an editor buffer to disk. A restart
//! replays the current buffer text, including incremental UTF-16 edits.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs,
    io::{self, BufRead, BufReader, Read, Write},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, Command, Stdio},
    sync::{
        atomic::{AtomicBool, Ordering},
        mpsc::{self, SyncSender},
    },
    thread,
    time::{Duration, Instant},
};

use anyhow::{Context, Result, bail, ensure};
use serde_json::{Value, json};

use crate::lean_sdk::{LakeOperation, Workspace};

const MAX_MESSAGE: usize = 16 * 1024 * 1024;
const MAX_QUEUED_EVENTS: usize = 2048;
const POLL: Duration = Duration::from_millis(100);
const IDLE_SAVED_POLL: Duration = Duration::from_secs(1);
const CONTENT_MODIFIED: i64 = -32801;
static INTERRUPTED: AtomicBool = AtomicBool::new(false);

pub(crate) fn interrupted() -> bool {
    INTERRUPTED.load(Ordering::Relaxed)
}

#[cfg(unix)]
pub(crate) struct SignalGuard(Vec<(i32, usize)>);

#[cfg(unix)]
unsafe extern "C" {
    fn signal(number: i32, handler: usize) -> usize;
}

#[cfg(unix)]
extern "C" fn interrupt_signal(_number: i32) {
    INTERRUPTED.store(true, Ordering::Relaxed);
}

#[cfg(unix)]
impl SignalGuard {
    pub(crate) fn install() -> Result<Self> {
        INTERRUPTED.store(false, Ordering::Relaxed);
        let mut guard = Self(Vec::new());
        for number in [2, 15] {
            // SAFETY: SIGINT/SIGTERM use a process-local, allocation-free
            // handler. The prior handlers are restored when run returns.
            let previous = unsafe { signal(number, interrupt_signal as *const () as usize) };
            ensure!(previous != usize::MAX, "Installing editor interruption handler failed");
            guard.0.push((number, previous));
        }
        Ok(guard)
    }
}

#[cfg(unix)]
impl Drop for SignalGuard {
    fn drop(&mut self) {
        for &(number, previous) in &self.0 {
            // SAFETY: restore the original handler for the same signal.
            unsafe {
                signal(number, previous);
            }
        }
    }
}

trait Host {
    fn root(&self) -> &Path;
    fn source_roots(&self) -> Vec<PathBuf>;
    fn source_stamp(&self) -> Result<[u8; 32]>;
    fn lake_command(&self, operation: LakeOperation<'_>) -> Result<Command>;
    fn contains_source(&self, path: &Path) -> Result<bool>;
    fn try_writer_lock(&self) -> Result<Option<fs::File>>;
    fn try_shared_lock(&self) -> Result<Option<fs::File>>;
}

impl Host for Workspace<'_> {
    fn root(&self) -> &Path {
        Workspace::root(self)
    }
    fn source_roots(&self) -> Vec<PathBuf> {
        Workspace::source_roots(self)
    }
    fn source_stamp(&self) -> Result<[u8; 32]> {
        Workspace::source_stamp(self)
    }
    fn lake_command(&self, operation: LakeOperation<'_>) -> Result<Command> {
        Workspace::lake_command(self, operation)
    }
    fn contains_source(&self, path: &Path) -> Result<bool> {
        Workspace::contains_source(self, path)
    }
    fn try_writer_lock(&self) -> Result<Option<fs::File>> {
        Workspace::try_writer_lock(self)
    }
    fn try_shared_lock(&self) -> Result<Option<fs::File>> {
        Workspace::try_shared_lock(self)
    }
}

#[derive(Clone, Debug)]
struct Document {
    path: PathBuf,
    local: bool,
    language: String,
    version: i64,
    text: String,
}

#[derive(Default, Clone, Debug)]
struct Inputs {
    texts: BTreeMap<PathBuf, String>,
    modules: BTreeMap<String, PathBuf>,
    edges: BTreeMap<PathBuf, BTreeSet<PathBuf>>,
    uncertain: BTreeSet<PathBuf>,
}

impl Inputs {
    fn read(
        workspace_root: &Path,
        roots: &[PathBuf],
        documents: &BTreeMap<String, Document>,
    ) -> Result<Self> {
        let mut result = Self::default();
        for root in roots {
            if !root.exists() {
                continue;
            }
            for entry in
                walkdir::WalkDir::new(root).follow_links(false).into_iter().filter_entry(|e| {
                    ![".lake", ".git", ".runtime", ".anneal-bin"]
                        .iter()
                        .any(|name| e.file_name() == *name)
                })
            {
                let entry = entry?;
                ensure!(!entry.file_type().is_symlink(), "Local editor source contains a symlink");
                if !entry.file_type().is_file()
                    || entry.path().extension().is_none_or(|e| e != "lean")
                {
                    continue;
                }
                let path = entry.path().to_path_buf();
                let module = path
                    .strip_prefix(root)?
                    .with_extension("")
                    .components()
                    .map(|c| c.as_os_str().to_str().context("Non-UTF8 local module path"))
                    .collect::<Result<Vec<_>>>()?
                    .join(".");
                ensure!(
                    result.modules.insert(module, path.clone()).is_none(),
                    "Ambiguous local module provider"
                );
                result.texts.insert(path.clone(), fs::read_to_string(path)?);
            }
        }
        for document in documents.values().filter(|d| d.local) {
            if let Some(root) = roots.iter().find(|root| document.path.starts_with(root)) {
                let module = document
                    .path
                    .strip_prefix(root)?
                    .with_extension("")
                    .components()
                    .map(|c| c.as_os_str().to_str().context("Non-UTF8 local module path"))
                    .collect::<Result<Vec<_>>>()?
                    .join(".");
                if let Some(old) = result.modules.insert(module, document.path.clone()) {
                    ensure!(old == document.path, "Ambiguous live local module provider");
                }
            }
        }
        result.rebuild_edges(documents, workspace_root);
        Ok(result)
    }

    fn rebuild_edges(&mut self, documents: &BTreeMap<String, Document>, workspace_root: &Path) {
        self.edges.clear();
        self.uncertain.clear();
        let mut texts = self.texts.clone();
        for document in documents.values() {
            if document.path.starts_with(workspace_root) {
                texts.insert(document.path.clone(), document.text.clone());
            }
        }
        for (path, text) in texts {
            match imports(&text) {
                Some(names) => {
                    for name in &names {
                        if !self.modules.contains_key(name) {
                            let relative = PathBuf::from(name.replace('.', "/"));
                            // At startup an orphaned private output is already a
                            // missing local provider, not a shared SDK module.
                            if workspace_root
                                .join(".lake/build/lib/lean")
                                .join(relative.with_extension("olean"))
                                .exists()
                            {
                                self.modules.insert(
                                    name.clone(),
                                    workspace_root.join(relative.with_extension("lean")),
                                );
                            }
                        }
                    }
                    let edges =
                        names.iter().filter_map(|name| self.modules.get(name).cloned()).collect();
                    self.edges.insert(path, edges);
                }
                None => {
                    self.uncertain.insert(path);
                }
            }
        }
    }

    fn dependencies(&self, path: &Path) -> BTreeSet<PathBuf> {
        let mut result = BTreeSet::new();
        let mut work = vec![path.to_path_buf()];
        while let Some(next) = work.pop() {
            if self.uncertain.contains(&next) {
                // Unrecognized headers fail closed. Exclude the document itself
                // so an ordinary proof edit can still produce its own diagnostics.
                result.extend(
                    self.texts
                        .keys()
                        .chain(self.edges.keys())
                        .filter(|p| p.as_path() != path)
                        .cloned(),
                );
            }
            if let Some(edges) = self.edges.get(&next) {
                for edge in edges {
                    if result.insert(edge.clone()) {
                        work.push(edge.clone());
                    }
                }
            }
        }
        result
    }

    fn dirty(&self, document: &Document) -> bool {
        self.texts.get(&document.path) != Some(&document.text)
    }
}

/// Recognize only ordinary import headers, including nested comments and Lean
/// quoted identifiers. Unknown syntax is conservative, never an empty graph.
fn imports(text: &str) -> Option<BTreeSet<String>> {
    let header = module_header(text)?;
    Some(
        header["imports"]
            .as_array()?
            .iter()
            .filter_map(|import| import["module"].as_str().map(str::to_owned))
            .collect(),
    )
}

/// RC2 Lean.Setup.ModuleHeader JSON for the recognized header subset. Keep
/// order, import flags, module mode, and both implicit Init imports. Unknown
/// syntax never produces fabricated metadata.
fn module_header(text: &str) -> Option<Value> {
    // Match RC2 Shell.lean's initial #lang line handling before interpreting
    // the Lean header. Other processors cannot use this dependency parser.
    let text = if let Some(directive) = text.strip_prefix("#lang") {
        let (language, remainder) = directive.split_once('\n').unwrap_or((directive, ""));
        if language.trim_ascii() != "lean4" {
            return None;
        }
        remainder
    } else {
        text
    };
    let mut cleaned = String::new();
    let mut chars = text.chars().peekable();
    let mut depth = 0usize;
    while let Some(c) = chars.next() {
        if depth > 0 {
            if c == '/' && chars.peek() == Some(&'-') {
                chars.next();
                depth += 1;
            } else if c == '-' && chars.peek() == Some(&'/') {
                chars.next();
                depth -= 1;
            }
            if c == '\n' {
                cleaned.push('\n');
            }
            continue;
        }
        if c == '«' {
            cleaned.push(c);
            for c in chars.by_ref() {
                cleaned.push(c);
                if c == '»' {
                    break;
                }
            }
        } else if c == '"' {
            cleaned.push(c);
            let mut escaped = false;
            for c in chars.by_ref() {
                cleaned.push(c);
                if c == '"' && !escaped {
                    break;
                }
                escaped = c == '\\' && !escaped;
            }
        } else if c == '/' && chars.peek() == Some(&'-') {
            chars.next();
            depth = 1;
            cleaned.push(' ');
        } else if c == '-' && chars.peek() == Some(&'-') {
            for c in chars.by_ref() {
                if c == '\n' {
                    cleaned.push('\n');
                    break;
                }
            }
        } else {
            cleaned.push(c);
        }
    }
    // RC2 Module/Syntax.lean: optional module, optional prelude, then
    // repeated (optional public, optional meta, import, optional all, ONE ident).
    // Whitespace, including line breaks and comments, does not delimit a
    // directive. A non-import token begins the body; stock Lean diagnoses it.
    let tokens: Vec<_> = cleaned.split_whitespace().collect();
    let mut index = 0;
    let is_module = tokens.get(index) == Some(&"module");
    if is_module {
        index += 1;
    }
    let prelude = tokens.get(index) == Some(&"prelude");
    if prelude {
        index += 1;
    }
    let mut entries = Vec::new();
    loop {
        let mut next = index;
        let exported = tokens.get(next) == Some(&"public");
        if exported {
            next += 1;
        }
        let meta = tokens.get(next) == Some(&"meta");
        if meta {
            next += 1;
        }
        // The prefix is atomic in RC2. For example `public def` is a body
        // command, not an incomplete import. Never scan the body for imports.
        if tokens.get(next) != Some(&"import") {
            if tokens.get(next).is_some_and(|token| token.starts_with("#lang")) {
                return None;
            }
            break;
        }
        next += 1;
        let all = tokens.get(next) == Some(&"all");
        if all {
            next += 1;
        }
        let name = header_module_name(tokens.get(next)?)?;
        entries.push(json!({"module":name,"importAll":all,"isExported":exported || !is_module,"isMeta":meta}));
        index = next + 1;
    }
    if !prelude {
        entries
            .insert(0, json!({"module":"Init","importAll":false,"isExported":true,"isMeta":true}));
        entries
            .insert(0, json!({"module":"Init","importAll":false,"isExported":true,"isMeta":false}));
    }
    Some(json!({"imports":entries,"isModule":is_module}))
}

/// Supported dependency names are ASCII Lean identifier components and quoted
/// versions of those components. Other quoted/unicode forms remain pending.
fn header_module_name(token: &str) -> Option<String> {
    let mut result = Vec::new();
    for part in token.split('.') {
        let (part, quoted) = if part.starts_with('«') && part.ends_with('»') {
            (&part['«'.len_utf8()..part.len() - '»'.len_utf8()], true)
        } else {
            (part, false)
        };
        let mut chars = part.chars();
        let first = chars.next()?;
        if !(first.is_ascii_alphabetic() || first == '_')
            || part == "_"
            || !chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, '_' | '\''))
        {
            return None;
        }
        // Keyword tokens cannot be unquoted identifiers in the header grammar.
        if !quoted
            && [
                "module",
                "prelude",
                "public",
                "meta",
                "import",
                "all",
                "def",
                "theorem",
                "lemma",
                "example",
                "namespace",
                "section",
                "open",
                "end",
                "variable",
                "universe",
                "universes",
                "set_option",
                "attribute",
                "abbrev",
                "opaque",
                "axiom",
                "constant",
                "inductive",
                "structure",
                "class",
                "instance",
                "private",
                "protected",
                "noncomputable",
                "unsafe",
                "mutual",
                "syntax",
                "macro",
                "elab",
                "notation",
                "infix",
                "infixl",
                "infixr",
                "prefix",
                "postfix",
                "by",
                "let",
                "match",
                "with",
                "do",
                "where",
                "if",
                "then",
                "else",
            ]
            .contains(&part)
            && result.is_empty()
        {
            return None;
        }
        result.push(part);
    }
    Some(result.join("."))
}

#[derive(Clone)]
struct Request {
    original: Value,
    epoch: u64,
    uri: Option<String>,
    version: Option<i64>,
    method: String,
}

struct State {
    root: PathBuf,
    roots: Vec<PathBuf>,
    documents: BTreeMap<String, Document>,
    closed: BTreeMap<String, (u64, i64)>,
    opened: BTreeSet<String>,
    inputs: Inputs,
    stamp: [u8; 32],
    epoch: u64,
    generation: u64,
    serial: u64,
    invalid: BTreeSet<PathBuf>,
    refreshing: bool,
    initialized: Option<Value>,
    initialize: Option<Value>,
    notifications: Vec<Value>,
    notification_bytes: usize,
    requests: BTreeMap<String, Request>,
    server_requests: BTreeMap<String, Value>,
    published_pending: BTreeMap<String, i64>,
}

impl State {
    fn new(root: PathBuf, roots: Vec<PathBuf>, stamp: [u8; 32]) -> Result<Self> {
        let documents = BTreeMap::new();
        let inputs = Inputs::read(&root, &roots, &documents)?;
        Ok(Self {
            root,
            roots,
            documents,
            closed: BTreeMap::new(),
            opened: BTreeSet::new(),
            inputs,
            stamp,
            epoch: 0,
            generation: 0,
            serial: 0,
            invalid: BTreeSet::new(),
            refreshing: false,
            initialized: None,
            initialize: None,
            notifications: Vec::new(),
            notification_bytes: 0,
            requests: BTreeMap::new(),
            server_requests: BTreeMap::new(),
            published_pending: BTreeMap::new(),
        })
    }

    fn remember_notification(&mut self, message: &Value) -> Result<()> {
        let method = message["method"].as_str().context("Missing notification method")?;
        // These refer to progress or RPC objects belonging to one process.
        // Replaying their IDs into a replacement cannot restore session state.
        if ["$/lean/rpc/keepAlive", "$/lean/rpc/release", "window/workDoneProgress/cancel"]
            .contains(&method)
        {
            return Ok(());
        }
        // Standard settings notifications contain the complete current value.
        // Other notifications may be cumulative, so retain their original order.
        if ["workspace/didChangeConfiguration", "$/setTrace"].contains(&method) {
            if let Some(index) = self.notifications.iter().position(|m| m["method"] == method) {
                let previous = self.notifications.remove(index);
                self.notification_bytes -= serde_json::to_vec(&previous)?.len();
            }
        }
        self.notification_bytes += serde_json::to_vec(message)?.len();
        ensure!(
            self.notification_bytes <= MAX_MESSAGE,
            "Editor session notification history exceeded its bound"
        );
        self.notifications.push(message.clone());
        Ok(())
    }

    fn blocked(&self, uri: &str) -> bool {
        let Some(doc) = self.documents.get(uri) else {
            return self.refreshing;
        };
        if self.refreshing || self.invalid.contains(&doc.path) {
            return true;
        }
        if self.inputs.uncertain.contains(&doc.path) {
            return true;
        }
        let deps = self.inputs.dependencies(&doc.path);
        if deps.iter().any(|path| self.inputs.uncertain.contains(path)) {
            return true;
        }
        if deps.iter().any(|path| !self.inputs.texts.contains_key(path)) {
            return true;
        }
        self.documents
            .values()
            .any(|dependency| deps.contains(&dependency.path) && self.inputs.dirty(dependency))
    }

    fn take_closed_diagnostics(&mut self, message: &Value) -> bool {
        let Some(uri) = uri_of(message) else { return false };
        let Some(version) = message["params"]["version"].as_i64() else { return false };
        if message["method"] != "textDocument/publishDiagnostics"
            || message["params"]["diagnostics"].as_array().is_none_or(|d| !d.is_empty())
            || message["params"]["isIncremental"] == true
            || self.documents.contains_key(&uri)
            || self.closed.get(&uri) != Some(&(self.generation, version))
        {
            return false;
        }
        self.closed.remove(&uri);
        true
    }

    fn request_current(&self, request: &Request) -> bool {
        request.epoch == self.epoch
            && !self.refreshing
            && match &request.uri {
                Some(uri) => {
                    !self.blocked(uri)
                        && self.documents.get(uri).map(|d| d.version) == request.version
                }
                None => !self.documents.keys().any(|uri| self.blocked(uri)),
            }
    }

    fn changed_inputs(&mut self, stamp: [u8; 32]) -> Result<bool> {
        if self.stamp == stamp {
            return Ok(false);
        }
        let previous = self.inputs.clone();
        self.inputs = Inputs::read(&self.root, &self.roots, &self.documents)?;
        // Remember deleted local providers: an old private .olean must not
        // silently turn a missing source into an apparently shared import.
        for (module, path) in &previous.modules {
            self.inputs.modules.entry(module.clone()).or_insert_with(|| path.clone());
        }
        self.inputs.rebuild_edges(&self.documents, &self.root);
        let changed: BTreeSet<_> = previous
            .texts
            .keys()
            .chain(self.inputs.texts.keys())
            .filter(|path| previous.texts.get(*path) != self.inputs.texts.get(*path))
            .cloned()
            .collect();
        // A same-byte metadata change, or Lake configuration change, cannot be
        // assigned to a precise local module; conservatively refresh all imports.
        let unknown = changed.is_empty();
        for doc in self.documents.values() {
            let old = previous.dependencies(&doc.path);
            let new = self.inputs.dependencies(&doc.path);
            if unknown || !old.is_disjoint(&changed) || !new.is_disjoint(&changed) {
                self.invalid.insert(doc.path.clone());
            }
        }
        self.stamp = stamp;
        self.epoch += 1;
        Ok(!self.invalid.is_empty())
    }

    fn update_document(&mut self, message: &Value, allow_shared: bool) -> Result<bool> {
        let method = message["method"].as_str().unwrap_or("");
        let params = &message["params"];
        let uri = params["textDocument"]["uri"].as_str().context("Document URI missing")?;
        let known_modules = self.inputs.modules.clone();
        let old_dependencies = self.documents.get(uri).map(|d| self.inputs.dependencies(&d.path));
        match method {
            "textDocument/didOpen" => {
                self.closed.remove(uri);
                let path = file_uri(uri)?;
                let local = path.starts_with(&self.root);
                ensure!(
                    local || allow_shared,
                    "Editor document is outside the bound source providers"
                );
                if !local {
                    ensure!(
                        fs::read_to_string(&path)?
                            == params["textDocument"]["text"].as_str().unwrap_or(""),
                        "Immutable SDK source was opened with a modified buffer"
                    );
                }
                ensure!(
                    path.extension().is_some_and(|e| e == "lean"),
                    "Editor document is not a Lean source"
                );
                ensure!(
                    !self.documents.iter().any(|(other, d)| other != uri && d.path == path),
                    "Two buffers alias the same Lean source"
                );
                if !self.opened.insert(uri.to_owned()) {
                    // A close/reopen may reuse exactly the old document version.
                    // Diagnostics have no worker incarnation field, so require a
                    // server-generation boundary before accepting those results.
                    if local {
                        self.invalid.insert(path.clone());
                    }
                }
                self.documents.insert(
                    uri.to_owned(),
                    Document {
                        path,
                        local,
                        language: params["textDocument"]["languageId"]
                            .as_str()
                            .unwrap_or("lean4")
                            .to_owned(),
                        version: params["textDocument"]["version"]
                            .as_i64()
                            .context("Document version missing")?,
                        text: params["textDocument"]["text"]
                            .as_str()
                            .context("Document text missing")?
                            .to_owned(),
                    },
                );
            }
            "textDocument/didChange" => {
                let doc = self.documents.get_mut(uri).context("Change for an unopened document")?;
                ensure!(
                    doc.local,
                    "SDK source documents are read-only; close the modified tab and reopen the immutable source"
                );
                let version = params["textDocument"]["version"]
                    .as_i64()
                    .context("Document version missing")?;
                ensure!(version > doc.version, "Non-increasing document version");
                for change in
                    params["contentChanges"].as_array().context("Document changes missing")?
                {
                    apply_change(&mut doc.text, change)?;
                }
                doc.version = version;
            }
            "textDocument/didClose" => {
                if let Some(document) = self.documents.remove(uri) {
                    self.closed.insert(uri.to_owned(), (self.generation, document.version));
                    self.published_pending.remove(uri);
                }
            }
            "textDocument/didSave" => { /* Disk bytes, not notification text, are the saved state. */
            }
            _ => return Ok(false),
        }
        self.inputs = Inputs::read(&self.root, &self.roots, &self.documents)?;
        for (module, path) in known_modules {
            self.inputs.modules.entry(module).or_insert(path);
        }
        self.inputs.rebuild_edges(&self.documents, &self.root);
        // Reverting/discarding an imported unsaved edit must refresh workers
        // whose results were hidden while it was dirty, even if disk is unchanged.
        if let Some(candidate) = self.documents.get(uri) {
            if old_dependencies.is_some_and(|old| old != self.inputs.dependencies(&candidate.path))
            {
                self.invalid.insert(candidate.path.clone());
            }
        }
        // A dirty dependency invalidates dependent workers, but never its own
        // ordinary incremental proof diagnostics.
        let dirty: BTreeSet<_> = self
            .documents
            .values()
            .filter(|d| d.local && self.inputs.dirty(d))
            .map(|d| d.path.clone())
            .collect();
        for doc in self.documents.values() {
            if !self.inputs.dependencies(&doc.path).is_disjoint(&dirty) {
                self.invalid.insert(doc.path.clone());
            }
        }
        self.epoch += 1;
        Ok(!self.invalid.is_empty())
    }

    fn pending_notifications(&mut self) -> Vec<Value> {
        let mut result = Vec::new();
        let blocked: Vec<_> = self
            .documents
            .iter()
            .filter(|(uri, _)| self.blocked(uri))
            .map(|(uri, d)| (uri.clone(), d.version))
            .collect();
        for (uri, version) in blocked {
            if self.published_pending.get(&uri) == Some(&version) {
                continue;
            }
            // Replacing, rather than incrementally appending, explicitly removes
            // previous successful diagnostics when their inputs cease to be current.
            result.push(json!({"jsonrpc":"2.0", "method":"textDocument/publishDiagnostics", "params": {
                "uri":uri, "version":version, "isIncremental":false, "diagnostics":[{
                    "range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}},
                    "severity":2, "source":"Anneal", "message":"Local imported inputs are pending: save or discard dependency edits; a successful build and worker refresh are required."}]}}));
            self.published_pending.insert(uri, version);
        }
        result
    }
}

fn apply_change(text: &mut String, change: &Value) -> Result<()> {
    let replacement = change["text"].as_str().context("Missing changed text")?;
    if let Some(range) = change.get("range") {
        let start = offset(text, &range["start"])?;
        let end = offset(text, &range["end"])?;
        ensure!(start <= end, "Reversed document edit");
        text.replace_range(start..end, replacement);
    } else {
        *text = replacement.to_owned();
    }
    Ok(())
}

fn offset(text: &str, position: &Value) -> Result<usize> {
    let line = position["line"].as_u64().context("Missing edit line")? as usize;
    let character = position["character"].as_u64().context("Missing edit character")? as usize;
    let mut start = 0;
    for _ in 0..line {
        start += text[start..].find('\n').context("Edit line outside document")? + 1;
    }
    let mut units = 0;
    for (byte, c) in text[start..].char_indices() {
        if units == character {
            return Ok(start + byte);
        }
        ensure!(c != '\n', "Edit character outside line");
        units += c.len_utf16();
        ensure!(units <= character, "Edit splits a UTF-16 surrogate pair");
    }
    ensure!(units == character, "Edit character outside document");
    Ok(text.len())
}

pub(crate) fn file_uri(uri: &str) -> Result<PathBuf> {
    let rest = uri.strip_prefix("file://").context("Only file documents are supported")?;
    let rest =
        rest.strip_prefix("localhost/").map(|s| format!("/{s}")).unwrap_or_else(|| rest.to_owned());
    ensure!(rest.starts_with('/') && !rest.contains(['?', '#']), "Invalid local file URI");
    let mut bytes = Vec::new();
    let mut iter = rest.bytes();
    while let Some(c) = iter.next() {
        if c == b'%' {
            let high = (iter.next().context("Truncated URI escape")? as char)
                .to_digit(16)
                .context("Invalid URI escape")?;
            let low = (iter.next().context("Truncated URI escape")? as char)
                .to_digit(16)
                .context("Invalid URI escape")?;
            bytes.push((high * 16 + low) as u8);
        } else {
            bytes.push(c);
        }
    }
    let path = PathBuf::from(String::from_utf8(bytes).context("Non-UTF8 file URI")?);
    ensure!(
        !path.components().any(|c| matches!(c, std::path::Component::ParentDir)),
        "URI contains parent traversal"
    );
    Ok(path.components().filter(|c| !matches!(c, std::path::Component::CurDir)).collect())
}

fn uri_of(message: &Value) -> Option<String> {
    let params = &message["params"];
    params["textDocument"]["uri"].as_str().or_else(|| params["uri"].as_str()).map(str::to_owned)
}

fn error(id: Value, reason: &str) -> Value {
    json!({"jsonrpc":"2.0", "id":id, "error":{"code":CONTENT_MODIFIED, "message":reason}})
}

pub(crate) fn read_message(reader: &mut impl BufRead) -> Result<Option<Value>> {
    let mut length = None;
    let mut total = 0;
    loop {
        let mut line = String::new();
        let count = (&mut *reader).take(8193).read_line(&mut line)?;
        if count == 0 && total == 0 {
            return Ok(None);
        }
        ensure!(count > 0 && count <= 8192, "Truncated or oversized LSP header");
        total += count;
        ensure!(total <= 8192, "Oversized LSP headers");
        if line == "\r\n" || line == "\n" {
            break;
        }
        if let Some((key, value)) = line.split_once(':') {
            if key.eq_ignore_ascii_case("Content-Length") {
                ensure!(length.is_none(), "Duplicate LSP Content-Length");
                length = Some(value.trim().parse::<usize>()?);
            }
        }
    }
    let length = length.context("Missing LSP Content-Length")?;
    ensure!(length <= MAX_MESSAGE, "Oversized LSP body");
    let mut bytes = vec![0; length];
    reader.read_exact(&mut bytes)?;
    let message: Value = serde_json::from_slice(&bytes)?;
    ensure!(message.is_object(), "JSON-RPC batch is unsupported");
    Ok(Some(message))
}

pub(crate) fn write_message(writer: &mut impl Write, message: &Value) -> Result<()> {
    let bytes = serde_json::to_vec(message)?;
    write!(writer, "Content-Length: {}\r\n\r\n", bytes.len())?;
    writer.write_all(&bytes)?;
    writer.flush()?;
    Ok(())
}

enum Event {
    Client(Result<Option<Value>>),
    Server(u64, Result<Option<Value>>),
}

fn queue_events(
    first: Option<Event>,
    events: &mpsc::Receiver<Event>,
    clients: &mut VecDeque<Event>,
    servers: &mut VecDeque<Event>,
) {
    let remaining = MAX_QUEUED_EVENTS.saturating_sub(clients.len() + servers.len());
    // Leaving channel events unread makes sync_channel apply backpressure
    // until a local event is consumed, including while an external writer waits.
    for event in first.into_iter().chain(events.try_iter()).take(remaining.min(256)) {
        match event {
            Event::Client(_) => clients.push_back(event),
            Event::Server(_, _) => servers.push_back(event),
        }
    }
}

fn reader_thread(
    reader: impl Read + Send + 'static,
    generation: Option<u64>,
    sender: SyncSender<Event>,
) {
    thread::spawn(move || {
        let mut reader = BufReader::new(reader);
        loop {
            let message = read_message(&mut reader);
            let finished = !matches!(message, Ok(Some(_)));
            let event = match generation {
                Some(g) => Event::Server(g, message),
                None => Event::Client(message),
            };
            if sender.send(event).is_err() || finished {
                break;
            }
        }
    });
}

pub(crate) struct Process {
    pub(crate) child: Child,
    stopped: bool,
}

impl Process {
    pub(crate) fn spawn(command: &mut Command) -> Result<Self> {
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
        }
        Ok(Self { child: command.spawn().context("Launching bound Lake process")?, stopped: false })
    }
    pub(crate) fn stop(&mut self) {
        self.stop_with_grace(|| thread::sleep(Duration::from_millis(50)));
    }
    fn stop_with_grace(&mut self, grace: impl FnOnce()) {
        if self.stopped {
            return;
        }
        self.stopped = true;
        // Kill the known group even if its leader has exited. Lake workers must
        // not survive a refresh, broken pipe, protocol error, or client EOF.
        #[cfg(unix)]
        {
            unsafe extern "C" {
                fn kill(pid: i32, signal: i32) -> i32;
            }
            let group = -(self.child.id() as i32);
            // SAFETY: kill only receives the numeric group created above.
            let signaled = unsafe { kill(group, 15) };
            if signaled == 0 {
                // Only a group that received SIGTERM needs time to exit.
                grace();
                unsafe {
                    kill(group, 9);
                }
            } else {
                let error = io::Error::last_os_error();
                // ESRCH is 3 on the supported Unix platforms: the exited
                // leader left no descendants, so there is nothing to await.
                if error.raw_os_error() != Some(3) {
                    eprintln!("Anneal: terminating Lake process group failed: {error}");
                    // Other errors do not establish an absent group. Attempt
                    // immediate forced cleanup, then reap the known child below.
                    unsafe {
                        kill(group, 9);
                    }
                }
            }
        }
        #[cfg(not(unix))]
        let _ = grace;
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

impl Drop for Process {
    fn drop(&mut self) {
        self.stop();
    }
}

struct Server {
    process: Process,
    input: ChildStdin,
}

impl Server {
    fn start(workspace: &dyn Host, generation: u64, sender: SyncSender<Event>) -> Result<Self> {
        let mut command = workspace.lake_command(LakeOperation::Serve)?;
        command.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit());
        let mut process = Process::spawn(&mut command)?;
        let input = process.child.stdin.take().context("Missing server stdin")?;
        let output = process.child.stdout.take().context("Missing server stdout")?;
        reader_thread(output, Some(generation), sender);
        Ok(Self { process, input })
    }
    fn send(&mut self, message: &Value) -> Result<()> {
        if self.process.stopped {
            return Ok(());
        }
        write_message(&mut self.input, message)
    }
}

struct PreparedCommand {
    command: Command,
    input: Option<Vec<u8>>,
}

struct Build {
    process: Option<Process>,
    input_result: Option<mpsc::Receiver<io::Result<()>>>,
    commands: VecDeque<PreparedCommand>,
    stamp: [u8; 32],
    epoch: u64,
    _writer: fs::File,
}

impl Build {
    fn spawn(
        mut commands: VecDeque<PreparedCommand>,
        stamp: [u8; 32],
        epoch: u64,
        writer: fs::File,
    ) -> Result<Self> {
        let (process, input_result) = match commands.pop_front() {
            Some(command) => {
                let (process, input) = Self::child(command)?;
                (Some(process), input)
            }
            None => (None, None),
        };
        Ok(Self { process, input_result, commands, stamp, epoch, _writer: writer })
    }
    fn child(
        mut prepared: PreparedCommand,
    ) -> Result<(Process, Option<mpsc::Receiver<io::Result<()>>>)> {
        let command = &mut prepared.command;
        command
            .stdin(if prepared.input.is_some() { Stdio::piped() } else { Stdio::null() })
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        let mut process = Process::spawn(command)?;
        let input_result = if let Some(bytes) = prepared.input {
            let mut input = process.child.stdin.take().context("Missing setup-file stdin")?;
            let (send, result) = mpsc::channel();
            thread::spawn(move || {
                let written = input.write_all(&bytes).and_then(|_| input.flush());
                drop(input);
                let _ = send.send(written);
            });
            Some(result)
        } else {
            None
        };
        let mut output = process.child.stdout.take().context("Missing build output")?;
        thread::spawn(move || {
            let _ = io::copy(&mut output, &mut io::stderr());
        });
        Ok((process, input_result))
    }
    fn poll(&mut self) -> Result<Option<bool>> {
        let Some(process) = self.process.as_mut() else {
            return Ok(Some(true));
        };
        let Some(status) = process.child.try_wait()? else {
            return Ok(None);
        };
        if let Some(input) = &self.input_result {
            match input.try_recv() {
                Ok(Ok(())) => self.input_result = None,
                Err(mpsc::TryRecvError::Empty) => return Ok(None),
                _ => {
                    process.stop();
                    return Ok(Some(false));
                }
            }
        }
        process.stop();
        if !status.success() {
            return Ok(Some(false));
        }
        if let Some(command) = self.commands.pop_front() {
            let (process, input) = Self::child(command)?;
            self.process = Some(process);
            self.input_result = input;
            Ok(None)
        } else {
            Ok(Some(true))
        }
    }
}

fn build_commands(workspace: &dyn Host, state: &State) -> Result<VecDeque<PreparedCommand>> {
    let mut commands = VecDeque::new();
    let paths: BTreeSet<_> = state
        .documents
        .values()
        .filter(|d| d.local)
        .flat_map(|d| state.inputs.dependencies(&d.path))
        .collect();
    let targets: Vec<_> = state
        .inputs
        .modules
        .iter()
        .filter(|(_, path)| paths.contains(*path))
        .map(|(module, _)| format!("+{module}:olean"))
        .collect();
    if !targets.is_empty() {
        commands.push_back(PreparedCommand {
            command: workspace.lake_command(LakeOperation::Build(&targets))?,
            input: None,
        });
    }
    for doc in state.documents.values().filter(|d| d.local) {
        // setup-file requires a saved path. A newly created unsaved document
        // still reaches the server with its live header and complete buffer.
        if !doc.path.try_exists()? {
            continue;
        }
        let Some(header) = module_header(&doc.text) else {
            continue;
        };
        let mut command = workspace.lake_command(LakeOperation::SetupFile(&doc.path))?;
        command.arg("-");
        let mut input = serde_json::to_vec(&header)?;
        input.push(b'\n');
        ensure!(input.len() <= MAX_MESSAGE, "Oversized live module header");
        commands.push_back(PreparedCommand { command, input: Some(input) });
    }
    Ok(commands)
}

fn cancel_requests(state: &mut State, output: &mut impl Write) -> Result<()> {
    for (_, request) in std::mem::take(&mut state.requests) {
        write_message(
            output,
            &error(request.original, "Document or imported input state changed"),
        )?;
    }
    Ok(())
}

/// Run over standard input/output. Only JSON-RPC frames are written to stdout.
/// Each build/restart is freshly admitted. Build cycles hold the workspace's
/// exclusive lease; results are reconciled under a shared lease. An external
/// writer suspends results and triggers a fresh server rather than holding an
/// exclusive lease for the entire editor lifetime.
pub fn run(workspace: &Workspace<'_>) -> Result<()> {
    let _session = workspace.server_lock()?;
    #[cfg(unix)]
    let _signals = SignalGuard::install()?;
    let mut output = io::stdout().lock();
    run_session(workspace, io::stdin(), &mut output)
}

fn run_session(
    workspace: &dyn Host,
    input: impl Read + Send + 'static,
    mut output: &mut impl Write,
) -> Result<()> {
    let deadline = Instant::now() + Duration::from_secs(60);
    let startup = loop {
        ensure!(!interrupted(), "Editor coordinator interrupted");
        if let Some(lock) = workspace.try_writer_lock()? {
            break lock;
        }
        ensure!(
            Instant::now() < deadline,
            "Workspace writer is busy; retry editor startup after it completes"
        );
        thread::sleep(POLL);
    };
    let roots = workspace.source_roots();
    let mut state = State::new(workspace.root().to_path_buf(), roots, workspace.source_stamp()?)?;
    let (sender, events) = mpsc::sync_channel(256);
    reader_thread(input, None, sender.clone());
    let mut server = Server::start(workspace, state.generation, sender.clone())?;
    let mut build: Option<Build> = None;
    let mut want_build = false;
    let mut hidden_initialize: Option<String> = None;
    let mut checked_initial = false;
    let mut shutdown = false;
    let mut shutdown_id = None;
    let mut last_poll = Instant::now();
    let mut last_saved_poll = Instant::now();
    let mut client_events = VecDeque::new();
    let mut server_events = VecDeque::new();
    let mut external_writer = false;
    let mut initializing_writer = Some(startup);
    let mut initialization_deadline = Instant::now() + Duration::from_secs(60);
    loop {
        ensure!(!interrupted(), "Editor coordinator interrupted");
        ensure!(
            initializing_writer.is_none() || Instant::now() < initialization_deadline,
            "Editor/server initialization timed out; close this session before retrying"
        );
        let first = if client_events.is_empty() && server_events.is_empty() {
            match events.recv_timeout(POLL) {
                Ok(event) => Some(event),
                Err(mpsc::RecvTimeoutError::Timeout) => None,
                Err(mpsc::RecvTimeoutError::Disconnected) => break,
            }
        } else {
            None
        };
        queue_events(first, &events, &mut client_events, &mut server_events);
        // An idle session need not repeatedly admit and hash every saved input.
        // Incoming events, active builds and initialization still run promptly;
        // a quiet session checks external changes at the coarser interval.
        if client_events.is_empty()
            && server_events.is_empty()
            && build.is_none()
            && initializing_writer.is_none()
            && !external_writer
            && !want_build
            && last_saved_poll.elapsed() < IDLE_SAVED_POLL
        {
            continue;
        }
        let owns_writer = build.is_some() || initializing_writer.is_some();
        let read_lock = if !owns_writer { workspace.try_shared_lock()? } else { None };
        if !owns_writer && read_lock.is_none() {
            if !external_writer {
                external_writer = true;
                state.refreshing = true;
                want_build = true;
                cancel_requests(&mut state, &mut output)?;
                server.process.stop();
                state.generation += 1;
                state.closed.clear();
                hidden_initialize = None;
                state.server_requests.clear();
                for notification in state.pending_notifications() {
                    write_message(&mut output, &notification)?;
                }
            }
            // Live buffers remain queued and bounded until the external writer
            // finishes. Never read a partially regenerated tree or credit a
            // server result while that writer owns the workspace.
            thread::sleep(POLL);
            continue;
        }
        if external_writer {
            external_writer = false;
            state
                .invalid
                .extend(state.documents.values().filter(|d| d.local).map(|d| d.path.clone()));
            want_build = true;
        }
        // Already received document updates precede server results and refresh
        // completion. Otherwise a queued didChange could race an accepted goal.
        let event = client_events.pop_front().or_else(|| server_events.pop_front());
        // Reconcile saved state before *every* forwarded result, not merely on
        // didSave. Unopened/transitive edits and same-client-version races count.
        if event.is_some() || last_saved_poll.elapsed() >= IDLE_SAVED_POLL {
            let stamp = workspace.source_stamp()?;
            last_saved_poll = Instant::now();
            if state.changed_inputs(stamp)? {
                want_build = true;
            }
        }
        if let Some(event) = event {
            match event {
                Event::Client(message) => {
                    let Some(mut message) = message? else {
                        break;
                    };
                    let method = message["method"].as_str().unwrap_or("").to_owned();
                    if method == "exit" {
                        server.send(&message)?;
                        let deadline = Instant::now() + Duration::from_millis(500);
                        while !server.process.stopped
                            && server.process.child.try_wait()?.is_none()
                            && Instant::now() < deadline
                        {
                            thread::sleep(Duration::from_millis(10));
                        }
                        break;
                    }
                    if method == "shutdown" {
                        shutdown = true;
                        build = None;
                        initializing_writer = None;
                        cancel_requests(&mut state, &mut output)?;
                        if server.process.stopped {
                            write_message(
                                &mut output,
                                &json!({"jsonrpc":"2.0","id":message["id"],"result":null}),
                            )?;
                        } else {
                            shutdown_id = Some(message["id"].clone());
                            message["id"] = json!("anneal-shutdown");
                            server.send(&message)?;
                        }
                        continue;
                    }
                    if shutdown {
                        continue;
                    }
                    if [
                        "textDocument/didOpen",
                        "textDocument/didChange",
                        "textDocument/didClose",
                        "textDocument/didSave",
                    ]
                    .contains(&method.as_str())
                    {
                        let allow_shared = if method == "textDocument/didOpen" {
                            let path =
                                file_uri(uri_of(&message).as_deref().context("Missing open URI")?)?;
                            !path.starts_with(workspace.root())
                                && workspace.contains_source(&path)?
                        } else {
                            false
                        };
                        want_build |= state.update_document(&message, allow_shared)?;
                        if method == "textDocument/didOpen" {
                            message["params"]["dependencyBuildMode"] = json!("never");
                            let uri = uri_of(&message).context("Missing open URI")?;
                            if !state.inputs.dependencies(&state.documents[&uri].path).is_empty() {
                                state.invalid.insert(state.documents[&uri].path.clone());
                                want_build = true;
                            }
                            want_build |= !checked_initial;
                        }
                        if method == "textDocument/didClose"
                            && (server.process.stopped || hidden_initialize.is_some())
                        {
                            // No live file worker can send the close clear.
                            // Withdraw only the recorded current close, through
                            // the same one-shot filter as a stock server clear.
                            let uri = uri_of(&message).context("Missing close URI")?;
                            if let Some(&(_, version)) = state.closed.get(&uri) {
                                let clear = json!({"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{
                                    "uri":uri,"version":version,"isIncremental":false,"diagnostics":[]}});
                                if state.take_closed_diagnostics(&clear) {
                                    write_message(&mut output, &clear)?;
                                }
                            }
                        }
                        // During hidden initialization the eventual didOpen
                        // replay includes these live updates; never send them early.
                        if hidden_initialize.is_none() {
                            server.send(&message)?;
                        }
                    } else if method == "initialized" {
                        state.initialized = Some(message.clone());
                        server.send(&message)?;
                        initializing_writer = None;
                    } else if method == "$/cancelRequest" {
                        let original = &message["params"]["id"];
                        if let Some((key, _)) =
                            state.requests.iter().find(|(_, r)| &r.original == original)
                        {
                            message["params"]["id"] = json!(key);
                            server.send(&message)?;
                        }
                    } else if method.is_empty() {
                        if let Some(id) = message["id"].as_str() {
                            if let Some(original) = state.server_requests.remove(id) {
                                message["id"] = original;
                                server.send(&message)?;
                            }
                        }
                    } else if let Some(id) = message.get("id").cloned() {
                        if method == "initialize" {
                            ensure!(state.initialize.is_none(), "Duplicate editor initialization");
                            if let Some(root) = message["params"]["rootUri"].as_str() {
                                ensure!(
                                    file_uri(root)? == state.root,
                                    "Editor initialization selects another workspace"
                                );
                            }
                            if let Some(folders) = message["params"]["workspaceFolders"].as_array()
                            {
                                ensure!(
                                    folders.iter().all(|folder| folder["uri"]
                                        .as_str()
                                        .and_then(|uri| file_uri(uri).ok())
                                        .as_deref()
                                        == Some(state.root.as_path())),
                                    "Multiple or foreign editor workspaces are unsupported"
                                );
                            }
                            ensure!(
                                message["params"]["initializationOptions"]["logCfg"].is_null(),
                                "Server logging overrides are unsupported by the bound editor gateway"
                            );
                            state.initialize = Some(message.clone());
                        }
                        let uri = uri_of(&message);
                        let version = uri
                            .as_ref()
                            .and_then(|uri| state.documents.get(uri).map(|d| d.version));
                        let request = Request {
                            original: id.clone(),
                            epoch: state.epoch,
                            uri,
                            version,
                            method: method.clone(),
                        };
                        if method != "initialize"
                            && (!state.request_current(&request) || hidden_initialize.is_some())
                        {
                            write_message(
                                &mut output,
                                &error(id, "Local imported inputs are pending"),
                            )?;
                        } else {
                            state.serial += 1;
                            let key =
                                format!("anneal-client-{}-{}", state.generation, state.serial);
                            message["id"] = json!(key);
                            state.requests.insert(key, request);
                            server.send(&message)?;
                        }
                    } else {
                        state.remember_notification(&message)?;
                        if hidden_initialize.is_none() {
                            server.send(&message)?;
                        }
                    }
                }
                Event::Server(generation, message) => {
                    if generation != state.generation {
                        continue;
                    }
                    let Some(mut message) = message? else {
                        bail!("Bound Lean server exited unexpectedly");
                    };
                    // Recheck at the server-result boundary as well as the
                    // event boundary. User saves need not participate in the
                    // cooperative Anneal writer lease.
                    want_build |= state.changed_inputs(workspace.source_stamp()?)?;
                    if message["id"] == json!("anneal-shutdown") {
                        if let Some(id) = shutdown_id.take() {
                            message["id"] = id;
                            write_message(&mut output, &message)?;
                        }
                        continue;
                    }
                    if message["id"]
                        .as_str()
                        .is_some_and(|id| hidden_initialize.as_deref() == Some(id))
                    {
                        ensure!(
                            message.get("error").is_none(),
                            "Lean server reinitialization failed: {message}"
                        );
                        hidden_initialize = None;
                        // A source/buffer edit during initialization obsoletes
                        // this refresh before replay, even at the same version.
                        let obsolete =
                            workspace.source_stamp()? != state.stamp || !state.invalid.is_empty();
                        want_build |= obsolete;
                        if let Some(initialized) = &state.initialized {
                            server.send(initialized)?;
                        }
                        for notification in &state.notifications {
                            server.send(notification)?;
                        }
                        for (uri, doc) in &state.documents {
                            server.send(&json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{
                                "textDocument":{"uri":uri,"languageId":doc.language,"version":doc.version,"text":doc.text},
                                "dependencyBuildMode":"never"}}))?;
                        }
                        state.refreshing = false;
                        if !obsolete {
                            state.published_pending.clear();
                        }
                        initializing_writer = None;
                        continue;
                    }
                    if message.get("method").is_none() {
                        let Some(key) = message["id"].as_str() else {
                            continue;
                        };
                        let Some(request) = state.requests.remove(key) else {
                            continue;
                        };
                        message["id"] = request.original.clone();
                        if request.method != "initialize" && !state.request_current(&request) {
                            message = error(
                                request.original,
                                "Obsolete document or imported input response",
                            );
                        }
                        write_message(&mut output, &message)?;
                    } else if message.get("id").is_some() {
                        // Server request IDs are generation-scoped too. Replies
                        // to a dead generation are ignored after its map is cleared.
                        state.serial += 1;
                        let key = format!("anneal-server-{}-{}", state.generation, state.serial);
                        state.server_requests.insert(key.clone(), message["id"].clone());
                        message["id"] = json!(key);
                        write_message(&mut output, &message)?;
                    } else {
                        let uri = uri_of(&message);
                        let method = message["method"].as_str().unwrap_or("");
                        let closed_clear = state.take_closed_diagnostics(&message);
                        if let Some(uri) = &uri {
                            if !closed_clear && state.blocked(uri) {
                                continue;
                            }
                            if !closed_clear
                                && ["textDocument/publishDiagnostics", "$/lean/fileProgress"]
                                    .contains(&method)
                            {
                                let version = message["params"]["version"].as_i64().or_else(|| {
                                    message["params"]["textDocument"]["version"].as_i64()
                                });
                                if state
                                    .documents
                                    .get(uri)
                                    .is_none_or(|d| Some(d.version) != version)
                                {
                                    continue;
                                }
                            }
                        } else if state.refreshing && method != "window/logMessage" {
                            continue;
                        }
                        write_message(&mut output, &message)?;
                    }
                }
            }
        }
        // Cancel obsolete requests immediately rather than leaving infoview
        // requests waiting for workers that can no longer be accepted.
        let obsolete: Vec<_> = state
            .requests
            .iter()
            .filter(|(_, r)| r.method != "initialize" && !state.request_current(r))
            .map(|(key, _)| key.clone())
            .collect();
        for key in obsolete {
            let request = state.requests.remove(&key).unwrap();
            write_message(
                &mut output,
                &error(request.original, "Document or imported inputs changed"),
            )?;
            server
                .send(&json!({"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":key}}))?;
        }
        if last_poll.elapsed() >= POLL {
            for notification in state.pending_notifications() {
                write_message(&mut output, &notification)?;
            }
            last_poll = Instant::now();
        }
        if let Some(active) = build.as_mut().filter(|_| client_events.is_empty()) {
            if let Some(success) = active.poll()? {
                let stamp = workspace.source_stamp()?;
                last_saved_poll = Instant::now();
                state.changed_inputs(stamp)?;
                let obsolete = active.stamp != stamp || active.epoch != state.epoch;
                let current = success && !obsolete;
                let finished = build.take().unwrap();
                if current && state.initialize.is_some() && state.initialized.is_some() {
                    initializing_writer = Some(finished._writer);
                    initialization_deadline = Instant::now() + Duration::from_secs(60);
                    drop(finished.process);
                    checked_initial = true;
                    state.invalid.clear();
                    state.refreshing = true;
                    cancel_requests(&mut state, &mut output)?;
                    state.server_requests.clear();
                    state.generation += 1;
                    state.closed.clear();
                    server.process.stop();
                    server = Server::start(workspace, state.generation, sender.clone())?;
                    let key = format!("anneal-initialize-{}", state.generation);
                    let mut initialize = state.initialize.clone().unwrap();
                    initialize["id"] = json!(key);
                    server.send(&initialize)?;
                    hidden_initialize = Some(key);
                    want_build = false;
                } else if !success {
                    // A current failure waits for a new edit instead of retrying
                    // in a hot loop. An obsolete failure cannot erase the cycle
                    // already requested by a newer saved/buffer state.
                    eprintln!(
                        "Anneal: local build failed; dependent editor results remain pending"
                    );
                    want_build = obsolete;
                } else {
                    want_build = true;
                }
            }
        }
        drop(read_lock);
        if want_build
            && build.is_none()
            && state.initialized.is_some()
            && hidden_initialize.is_none()
        {
            let dirty_import = state.documents.iter().any(|(_, d)| {
                state.inputs.dependencies(&d.path).iter().any(|path| {
                    state.documents.values().any(|dependency| {
                        &dependency.path == path && state.inputs.dirty(dependency)
                    })
                })
            });
            if !dirty_import {
                if let Some(writer) = workspace.try_writer_lock()? {
                    let commands = build_commands(workspace, &state)?;
                    build = Some(Build::spawn(
                        commands,
                        workspace.source_stamp()?,
                        state.epoch,
                        writer,
                    )?);
                    want_build = false;
                }
            }
        }
    }
    // RAII terminates both known process groups on every exit path.
    drop(build);
    drop(server);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn headers_comments_quoted_names_and_unsupported_syntax() {
        assert_eq!(
            imports(
                "/- import Nope /- nested -/ -/\nimport «foo_bar».Types\nimport Mathlib.Data.Nat\n-- import Nope\ndef x := 1"
            ),
            Some(BTreeSet::from([
                "Init".into(),
                "foo_bar.Types".into(),
                "Mathlib.Data.Nat".into()
            ]))
        );
        assert!(imports("import\n  Local").unwrap().contains("Local"));
        // RC2 takes one identifier per directive: Other begins the body.
        assert_eq!(imports("import Local Other"), imports("import Local\ndef x := 1"));
        assert!(imports("public\nimport Local").unwrap().contains("Local"));
        assert!(imports("import").is_none());
        assert!(imports("import all\n").is_none());
        assert!(imports("import Δ.Local").is_none());
        assert!(imports("import Local.").is_none());
        assert!(imports("import «../Other»").is_none());
        assert!(imports("public import Local").unwrap().contains("Local"));
        assert_eq!(
            imports("import Local\nexample : True := by /- unfinished body"),
            imports("import Local\nexample : True := by trivial")
        );
    }

    #[test]
    fn rc2_module_header_keeps_order_flags_and_implicit_init_imports() {
        let header =
            module_header("module\npublic meta import all Local\nimport Other\ndef x := 1")
                .unwrap();
        assert_eq!(header["isModule"], true);
        assert_eq!(
            header["imports"][0],
            json!({"module":"Init","importAll":false,"isExported":true,"isMeta":false})
        );
        assert_eq!(header["imports"][1]["isMeta"], true);
        assert_eq!(
            header["imports"][2],
            json!({"module":"Local","importAll":true,"isExported":true,"isMeta":true})
        );
        assert_eq!(
            header["imports"][3],
            json!({"module":"Other","importAll":false,"isExported":false,"isMeta":false})
        );
        assert_eq!(
            module_header("prelude\nimport Local\ndef x := 1").unwrap()["imports"]
                .as_array()
                .unwrap()
                .len(),
            1
        );
    }

    #[test]
    fn rc2_headers_accept_multiline_directives_without_inventing_multi_import_syntax() {
        let header = module_header("module /- outer /- nested -/ -/ prelude\npublic\nmeta import\n Local\nmeta /- gap -/ import all\n Other\nimport Third\npublic def x := 1").unwrap();
        assert_eq!(
            header,
            json!({"isModule": true, "imports": [
                {"module":"Local", "importAll":false, "isExported":true, "isMeta":true},
                {"module":"Other", "importAll":true, "isExported":false, "isMeta":true},
                {"module":"Third", "importAll":false, "isExported":false, "isMeta":false}
            ]})
        );
        let header =
            module_header("import Local import Other\nexample : True := by trivial").unwrap();
        assert_eq!(header["imports"].as_array().unwrap().len(), 4);
        assert_eq!(header["imports"][2]["module"], "Local");
        assert_eq!(header["imports"][3]["module"], "Other");
        let single = module_header("import Local Other\nimport Hidden\n").unwrap();
        assert_eq!(single["imports"].as_array().unwrap().len(), 3);
        assert_eq!(single["imports"][2]["module"], "Local");
        assert_eq!(
            imports("custom_command import Hidden"),
            imports("example : True := by trivial")
        );
        assert!(module_header("module\npublic meta import\n").is_none());
    }

    #[test]
    fn rc2_language_directive_preserves_imports_or_fails_conservatively() {
        let body = "module\npublic meta import all Local\nimport Middle\ndef x := 1\n";
        assert_eq!(module_header(&format!("#lang lean4\n{body}")), module_header(body));
        assert_eq!(module_header(&format!("#lang\tlean4\r\n{body}")), module_header(body));
        assert!(imports("#lang lean4\nimport Local\n").unwrap().contains("Local"));
        for directive in ["#lang lean4md\n", "#lang\n", " #lang lean4\n", "module\n#lang lean4\n"] {
            assert!(module_header(&format!("{directive}import Local\n")).is_none());
        }
        let (dir, mut state, _local, client) = fixture();
        open(
            &mut state,
            &client,
            "#lang unsupported\nimport Local\nexample : True := by trivial\n",
        );
        assert!(state.blocked(&client));
        assert!(
            state
                .inputs
                .dependencies(&state.documents[&client].path)
                .contains(&dir.path().join("Local.lean"))
        );
        assert!(!state.request_current(&Request {
            original: json!(70),
            epoch: state.epoch,
            uri: Some(client),
            version: Some(1),
            method: "$/lean/plainGoal".into(),
        }));
    }

    #[test]
    fn event_bursts_preserve_order_and_backpressure_at_local_capacity() {
        let (sender, events) = mpsc::sync_channel(256);
        let mut clients = VecDeque::new();
        let mut servers = VecDeque::new();
        for index in 0..MAX_QUEUED_EVENTS {
            clients.push_back(Event::Client(Ok(Some(json!(index)))));
        }
        for index in MAX_QUEUED_EVENTS..MAX_QUEUED_EVENTS + 256 {
            sender.send(Event::Client(Ok(Some(json!(index))))).unwrap();
        }
        queue_events(None, &events, &mut clients, &mut servers);
        assert_eq!(clients.len(), MAX_QUEUED_EVENTS);
        let extra = Event::Client(Ok(Some(json!(MAX_QUEUED_EVENTS + 256))));
        assert!(matches!(sender.try_send(extra), Err(mpsc::TrySendError::Full(_))));
        // A sustained producer outpaces one-event processing. The queues must
        // remain bounded while every event is eventually processed in order.
        let count = MAX_QUEUED_EVENTS + 4096;
        let producer = thread::spawn(move || {
            for index in MAX_QUEUED_EVENTS + 256..count {
                sender.send(Event::Client(Ok(Some(json!(index))))).unwrap();
            }
        });
        let deadline = Instant::now() + Duration::from_secs(10);
        for index in 0..count {
            let event = loop {
                assert!(Instant::now() < deadline, "Event burst stopped making progress");
                queue_events(None, &events, &mut clients, &mut servers);
                assert!(clients.len() + servers.len() <= MAX_QUEUED_EVENTS);
                if let Some(event) = clients.pop_front() {
                    break event;
                }
                thread::yield_now();
            };
            assert!(matches!(event, Event::Client(Ok(Some(value))) if value == json!(index)));
        }
        producer.join().unwrap();
        assert!(clients.is_empty() && servers.is_empty());
    }

    #[test]
    fn unsaved_header_replaces_saved_import_metadata_without_saving_buffer() {
        let (_dir, mut state, _local, client) = fixture();
        open(&mut state, &client, "import Middle\nexample : True := by trivial\n");
        state.update_document(&json!({"method":"textDocument/didChange","params":{"textDocument":{"uri":client,"version":2},
            "contentChanges":[{"text":"import Local\nexample : True := by trivial\n"}]}}), false).unwrap();
        let header = module_header(&state.documents[&client].text).unwrap();
        assert!(
            header["imports"].as_array().unwrap().iter().any(|entry| entry["module"] == "Local")
        );
        assert!(
            header["imports"].as_array().unwrap().iter().all(|entry| entry["module"] != "Middle")
        );
        assert!(
            fs::read_to_string(&state.documents[&client].path).unwrap().contains("import Middle")
        );
    }

    #[test]
    fn incremental_utf16_edits_preserve_unsaved_unicode() {
        let mut text = "import Local\nexample : True := by\n  -- 😀\n  trivial\n".to_owned();
        apply_change(&mut text, &json!({"range":{"start":{"line":1,"character":10},"end":{"line":1,"character":14}},"text":"False"})).unwrap();
        assert!(text.contains("example : False := by"));
        let before = text.clone();
        assert!(apply_change(&mut text, &json!({"range":{"start":{"line":2,"character":6},"end":{"line":2,"character":6}},"text":"x"})).is_err());
        assert_eq!(text, before);
    }

    #[test]
    fn framing_is_bounded_and_round_trips() {
        let value = json!({"id":1,"jsonrpc":"2.0","result":"é"});
        let mut bytes = Vec::new();
        write_message(&mut bytes, &value).unwrap();
        assert_eq!(read_message(&mut BufReader::new(bytes.as_slice())).unwrap(), Some(value));
        assert!(
            read_message(&mut BufReader::new(b"Content-Length: 999999999\r\n\r\n".as_slice()))
                .is_err()
        );
        assert!(
            read_message(&mut BufReader::new(
                b"Content-Length: 1\r\nContent-Length: 1\r\n\r\n{}".as_slice()
            ))
            .is_err()
        );
    }

    #[test]
    fn file_uri_rejects_escapes_and_preserves_spaces() {
        assert_eq!(file_uri("file:///tmp/a%20b.lean").unwrap(), PathBuf::from("/tmp/a b.lean"));
        assert!(file_uri("file:///tmp/%2e%2e/other.lean").is_err());
        assert!(file_uri("file://remote/tmp/a.lean").is_err());
    }

    #[cfg(unix)]
    #[test]
    fn exited_process_without_descendants_skips_termination_grace() {
        let mut command = Command::new("/usr/bin/true");
        let mut process = Process::spawn(&mut command).unwrap();
        assert!(process.child.wait().unwrap().success());
        process.stop_with_grace(|| panic!("An absent process group must not incur a grace delay"));
        assert!(process.stopped);
    }

    #[cfg(unix)]
    #[test]
    fn live_process_group_receives_termination_grace() {
        let mut command = Command::new("/bin/sleep");
        command.arg("30");
        let mut process = Process::spawn(&mut command).unwrap();
        let mut waited = false;
        process.stop_with_grace(|| waited = true);
        assert!(waited);
        assert!(process.child.try_wait().unwrap().is_some());
    }

    fn fixture() -> (tempfile::TempDir, State, String, String) {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().to_path_buf();
        fs::write(root.join("Local.lean"), "def value := 10\n").unwrap();
        fs::write(root.join("Middle.lean"), "import Local\ndef middle := value\n").unwrap();
        fs::write(root.join("Client.lean"), "import Middle\nexample : middle = 10 := by decide\n")
            .unwrap();
        let state = State::new(root.clone(), vec![root.clone()], [0; 32]).unwrap();
        (
            dir,
            state,
            format!("file://{}", root.join("Local.lean").display()),
            format!("file://{}", root.join("Client.lean").display()),
        )
    }

    fn open(state: &mut State, uri: &str, text: &str) {
        state.update_document(&json!({"method":"textDocument/didOpen","params":{"textDocument":{"uri":uri,"languageId":"lean4","version":1,"text":text}}}), false).unwrap();
    }

    #[test]
    fn dirty_transitive_dependency_blocks_client_but_not_own_document() {
        let (_dir, mut state, local, client) = fixture();
        open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
        open(&mut state, &local, "def value := 20\n");
        assert!(state.blocked(&client));
        assert!(!state.blocked(&local));
        state.invalid.clear(); // Even a successful saved build cannot clear dirty-buffer pending.
        assert!(state.blocked(&client));
    }

    #[test]
    fn ordinary_own_edit_is_incremental_and_obsolete_goal_is_rejected() {
        let (_dir, mut state, _local, client) = fixture();
        open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
        let request = Request {
            original: json!(7),
            epoch: state.epoch,
            uri: Some(client.clone()),
            version: Some(1),
            method: "$/lean/plainGoal".into(),
        };
        assert!(state.request_current(&request));
        state.update_document(&json!({"method":"textDocument/didChange","params":{"textDocument":{"uri":client,"version":2},"contentChanges":[{"text":"import Middle\nexample : False := by trivial\n"}]}}), false).unwrap();
        assert!(!state.request_current(&request));
        assert!(!state.blocked(&client));
        assert!(state.invalid.is_empty());
    }

    #[test]
    fn saved_transitive_change_invalidates_same_document_version_and_failure_stays_pending() {
        let (dir, mut state, _local, client) = fixture();
        open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
        let request = Request {
            original: json!(1),
            epoch: state.epoch,
            uri: Some(client.clone()),
            version: Some(1),
            method: "$/lean/rpc/call".into(),
        };
        fs::write(dir.path().join("Local.lean"), "def value := 20\n").unwrap();
        assert!(state.changed_inputs([1; 32]).unwrap());
        assert!(state.blocked(&client));
        assert!(!state.request_current(&request));
        // A failed cycle leaves the invalid set intact.
        assert!(!state.pending_notifications().is_empty());
        assert!(state.blocked(&client));
    }

    #[test]
    fn unsaved_new_dependency_is_not_omitted_by_conservative_mapping() {
        let (dir, mut state, _local, client) = fixture();
        open(&mut state, &client, "module\nimport New\nexample : True := by trivial\n");
        let new_uri = format!("file://{}", dir.path().join("New.lean").display());
        open(&mut state, &new_uri, "def newValue := 1\n");
        assert!(state.blocked(&client));
        assert!(!state.blocked(&new_uri));
    }

    #[test]
    fn deleted_provider_with_old_private_output_stays_pending() {
        let (dir, mut state, _local, client) = fixture();
        open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
        fs::remove_file(dir.path().join("Local.lean")).unwrap();
        state.changed_inputs([1; 32]).unwrap();
        state.invalid.clear();
        assert!(state.blocked(&client));
        let output = dir.path().join(".lake/build/lib/lean");
        fs::create_dir_all(&output).unwrap();
        fs::write(output.join("Local.olean"), b"old compiled artifact").unwrap();
        let mut fresh =
            State::new(dir.path().to_owned(), vec![dir.path().to_owned()], [2; 32]).unwrap();
        open(&mut fresh, &client, "import Middle\nexample : middle = 10 := by decide\n");
        assert!(fresh.blocked(&client));
    }

    #[test]
    fn close_reopen_same_version_requires_new_worker_generation() {
        let (_dir, mut state, local, _client) = fixture();
        open(&mut state, &local, "def value := 10\n");
        assert!(!state.blocked(&local));
        state
            .update_document(
                &json!({"method":"textDocument/didClose","params":{"textDocument":{"uri":local}}}),
                false,
            )
            .unwrap();
        open(&mut state, &local, "def value := 10\n");
        assert!(state.blocked(&local));
    }

    #[test]
    fn only_matching_current_closed_document_can_clear_diagnostics_once() {
        let (_dir, mut state, local, _) = fixture();
        open(&mut state, &local, "def value := 10\n");
        state
            .update_document(
                &json!({"method":"textDocument/didClose","params":{"textDocument":{"uri":local}}}),
                false,
            )
            .unwrap();
        let clear = json!({"method":"textDocument/publishDiagnostics","params":{"uri":local,"version":1,"diagnostics":[]}});
        let mut wrong = clear.clone();
        wrong["params"]["version"] = json!(2);
        assert!(!state.take_closed_diagnostics(&wrong));
        wrong = clear.clone();
        wrong["params"]["uri"] = json!("file:///unknown.lean");
        assert!(!state.take_closed_diagnostics(&wrong));
        wrong = clear.clone();
        wrong["params"]["diagnostics"] = json!([{"message":"late positive"}]);
        assert!(!state.take_closed_diagnostics(&wrong));
        wrong = clear.clone();
        wrong["params"]["isIncremental"] = json!(true);
        assert!(!state.take_closed_diagnostics(&wrong));
        state.generation += 1;
        assert!(!state.take_closed_diagnostics(&clear));
        state.generation -= 1;
        assert!(state.take_closed_diagnostics(&clear));
        assert!(!state.take_closed_diagnostics(&clear));
        open(&mut state, &local, "def value := 10\n");
        state
            .update_document(
                &json!({"method":"textDocument/didClose","params":{"textDocument":{"uri":local}}}),
                false,
            )
            .unwrap();
        open(&mut state, &local, "def value := 10\n");
        assert!(!state.take_closed_diagnostics(&clear));
    }

    #[test]
    fn admitted_shared_source_is_view_only() {
        let (_dir, mut state, _local, _client) = fixture();
        let shared = tempfile::tempdir().unwrap();
        let file = shared.path().join("Shared.lean");
        fs::write(&file, "def shared := 1\n").unwrap();
        let uri = format!("file://{}", file.display());
        state
            .update_document(
                &json!({"method":"textDocument/didOpen","params":{"textDocument":{
            "uri":uri,"languageId":"lean4","version":1,"text":"def shared := 1\n"}}}),
                true,
            )
            .unwrap();
        assert!(!state.blocked(&uri));
        assert!(!state.documents[&uri].local);
        assert!(state.update_document(&json!({"method":"textDocument/didChange","params":{"textDocument":{"uri":uri,"version":2},
            "contentChanges":[{"text":"def shared := 2\n"}]}}), false).is_err());
        assert_eq!(fs::read_to_string(file).unwrap(), "def shared := 1\n");
    }

    #[cfg(unix)]
    mod protocol {
        use std::{
            os::unix::net::UnixStream,
            sync::{Arc, atomic::AtomicUsize},
        };

        use sha2::{Digest, Sha256};

        use super::*;

        struct FakeHost {
            root: PathBuf,
            source_stamps: Arc<AtomicUsize>,
        }
        impl Host for FakeHost {
            fn root(&self) -> &Path {
                &self.root
            }
            fn source_roots(&self) -> Vec<PathBuf> {
                vec![self.root.clone()]
            }
            fn source_stamp(&self) -> Result<[u8; 32]> {
                self.source_stamps.fetch_add(1, Ordering::Relaxed);
                let mut hash = Sha256::new();
                for name in ["Client.lean", "Local.lean", "Middle.lean"] {
                    hash.update(fs::read(self.root.join(name))?);
                    hash.update(
                        fs::metadata(self.root.join(name))?
                            .modified()?
                            .duration_since(std::time::UNIX_EPOCH)?
                            .as_nanos()
                            .to_le_bytes(),
                    );
                }
                Ok(hash.finalize().into())
            }
            fn lake_command(&self, operation: LakeOperation<'_>) -> Result<Command> {
                let mut command = Command::new("/usr/bin/python3");
                command
                    .args(["-I", "-B"])
                    .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/editor_fake_peer.py"));
                command.arg(&self.root).env_clear().env("PATH", "/usr/bin:/bin");
                match operation {
                    LakeOperation::Serve => {
                        command.arg("serve");
                    }
                    LakeOperation::Build(targets) => {
                        command.arg("build").args(targets);
                    }
                    LakeOperation::SetupFile(path) => {
                        ensure!(path.is_file(), "setup-file requires a saved local source");
                        command.arg("setup").arg(path);
                    }
                    LakeOperation::Version => {
                        command.arg("version");
                    }
                }
                Ok(command)
            }
            fn contains_source(&self, _path: &Path) -> Result<bool> {
                Ok(false)
            }
            fn try_writer_lock(&self) -> Result<Option<fs::File>> {
                Ok(if self.root.join("busy-writer").exists() {
                    None
                } else {
                    Some(fs::File::open(&self.root)?)
                })
            }
            fn try_shared_lock(&self) -> Result<Option<fs::File>> {
                Ok(if self.root.join("busy-writer").exists() {
                    None
                } else {
                    Some(fs::File::open(&self.root)?)
                })
            }
        }

        struct Session {
            dir: tempfile::TempDir,
            input: UnixStream,
            output: BufReader<UnixStream>,
            join: Option<thread::JoinHandle<Result<()>>>,
            client: String,
            local: String,
            seen: Vec<Value>,
            source_stamps: Arc<AtomicUsize>,
        }
        impl Session {
            fn start() -> Self {
                Self::start_document("Client.lean")
            }
            fn start_document(name: &str) -> Self {
                let (dir, _state, local, client) = fixture();
                let client = if name == "Client.lean" {
                    client
                } else {
                    format!("file://{}", dir.path().join(name).display())
                };
                let (input, server_input) = UnixStream::pair().unwrap();
                let (output, mut server_output) = UnixStream::pair().unwrap();
                output.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
                let source_stamps = Arc::new(AtomicUsize::new(0));
                let host =
                    FakeHost { root: dir.path().to_owned(), source_stamps: source_stamps.clone() };
                let join =
                    thread::spawn(move || run_session(&host, server_input, &mut server_output));
                let mut session = Self {
                    dir,
                    input,
                    output: BufReader::new(output),
                    join: Some(join),
                    client,
                    local,
                    seen: Vec::new(),
                    source_stamps,
                };
                session.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}));
                session.until(|message| message["id"] == 1);
                session.send(json!({"jsonrpc":"2.0","method":"initialized","params":{}}));
                let text =
                    "import Middle\nexample : middle = 10 := by decide\n-- unsaved client note\n";
                session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                    "uri":session.client,"languageId":"lean4","version":1,"text":text}}}));
                let client = session.client.clone();
                session.until(|m| {
                    m["method"] == "textDocument/publishDiagnostics"
                        && m["params"]["uri"] == client
                        && m["params"]["diagnostics"] == json!([])
                });
                session
            }
            fn send(&mut self, message: Value) {
                write_message(&mut self.input, &message).unwrap();
            }
            fn session_state(&mut self, id: i64) -> Value {
                self.send(json!({"jsonrpc":"2.0","id":id,"method":"$/test/sessionState"}));
                self.until(|message| message["id"] == id)
            }
            fn until(&mut self, predicate: impl Fn(&Value) -> bool) -> Value {
                let deadline = Instant::now() + Duration::from_secs(10);
                loop {
                    assert!(
                        Instant::now() < deadline,
                        "Timed out waiting for a fake-peer message: {:?}",
                        self.seen
                    );
                    let message = read_message(&mut self.output)
                        .unwrap()
                        .expect("Proxy closed before expected message");
                    self.seen.push(message.clone());
                    if predicate(&message) {
                        return message;
                    }
                }
            }
            fn wait_file(&self, name: &str) {
                let deadline = Instant::now() + Duration::from_secs(5);
                while !self.dir.path().join(name).exists() {
                    assert!(Instant::now() < deadline, "Fake peer did not create {name}");
                    thread::sleep(Duration::from_millis(10));
                }
            }
            fn finish(mut self) {
                self.send(json!({"jsonrpc":"2.0","id":999,"method":"shutdown"}));
                self.until(|m| m["id"] == 999);
                self.send(json!({"jsonrpc":"2.0","method":"exit"}));
                self.join.take().unwrap().join().unwrap().unwrap();
                assert!(self.dir.path().join("graceful-exit").exists());
            }
        }
        impl Drop for Session {
            fn drop(&mut self) {
                let _ = write_message(&mut self.input, &json!({"jsonrpc":"2.0","method":"exit"}));
                if let Some(join) = self.join.take() {
                    let _ = join.join();
                }
            }
        }

        #[test]
        fn closing_document_clears_errors_and_discards_late_closed_diagnostics() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 20"
            });
            let before = session.seen.len();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":session.client}}}));
            let client = session.client.clone();
            session.until(|m| {
                m["method"] == "textDocument/publishDiagnostics"
                    && m["params"]["uri"] == client
                    && m["params"]["version"] == 1
                    && m["params"]["diagnostics"] == json!([])
            });
            assert!(session.session_state(71).get("result").is_some());
            let diagnostics: Vec<_> = session.seen[before..]
                .iter()
                .filter(|m| m["method"] == "textDocument/publishDiagnostics")
                .collect();
            assert_eq!(diagnostics.len(), 1);
            assert_eq!(diagnostics[0]["params"]["diagnostics"], json!([]));
            session.finish();
        }

        #[test]
        fn close_during_hidden_initialization_clears_once_without_replaying_closed_buffer() {
            let mut session = Session::start();
            let before = session.seen.len();
            let replays_before = fs::read_to_string(session.dir.path().join("replays.jsonl"))
                .unwrap()
                .lines()
                .count();
            fs::remove_file(session.dir.path().join("initialized-entered")).unwrap();
            fs::write(session.dir.path().join("hold-initialize"), "hold").unwrap();
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            session.wait_file("initialize-entered");
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":session.client}}}));
            let client = session.client.clone();
            let clear = session.until(|m| {
                m["method"] == "textDocument/publishDiagnostics"
                    && m["params"]["uri"] == client
                    && m["params"]["diagnostics"] == json!([])
            });
            assert_eq!(clear["params"]["version"], 1);
            assert_eq!(clear["params"]["isIncremental"], false);
            assert_eq!(session.session_state(72)["error"]["code"], CONTENT_MODIFIED);
            fs::remove_file(session.dir.path().join("hold-initialize")).unwrap();
            session.wait_file("initialized-entered");
            assert!(session.session_state(73).get("result").is_some());
            let clears = session.seen[before..]
                .iter()
                .filter(|m| {
                    m["method"] == "textDocument/publishDiagnostics"
                        && m["params"]["uri"] == client
                        && m["params"]["diagnostics"] == json!([])
                })
                .count();
            assert_eq!(clears, 1);
            let replays = fs::read_to_string(session.dir.path().join("replays.jsonl")).unwrap();
            assert_eq!(replays.lines().count(), replays_before);
            session.finish();
        }

        #[test]
        fn language_directive_live_header_rebuilds_imports_and_refreshes_same_version() {
            let mut session = Session::start();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":session.client,"version":2},
                "contentChanges":[{"text":"#lang lean4\nimport Local\nexample : value = 10 := by decide\n-- unsaved language header\n"}]}}));
            let client = session.client.clone();
            session.until(|m| {
                m["params"]["uri"] == client
                    && m["params"]["version"] == 2
                    && m["params"]["diagnostics"] == json!([])
            });
            let headers = fs::read_to_string(session.dir.path().join("headers.jsonl")).unwrap();
            let header: Value = serde_json::from_str(headers.lines().last().unwrap()).unwrap();
            assert!(header["imports"].as_array().unwrap().iter().any(|i| i["module"] == "Local"));
            assert!(header["imports"].as_array().unwrap().iter().all(|i| i["module"] != "Middle"));
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            let diagnostic = session.until(|m| {
                m["params"]["uri"] == client
                    && m["params"]["diagnostics"][0]["message"]
                        == "current fake imported value is 20"
            });
            assert_eq!(diagnostic["params"]["version"], 2);
            let replays = fs::read_to_string(session.dir.path().join("replays.jsonl")).unwrap();
            let replay: Value = serde_json::from_str(replays.lines().last().unwrap()).unwrap();
            assert!(replay["text"].as_str().unwrap().starts_with("#lang lean4\n"));
            assert!(
                fs::read_to_string(session.dir.path().join("Client.lean"))
                    .unwrap()
                    .starts_with("import Middle\n")
            );
            session.finish();
        }

        #[test]
        fn idle_saved_input_poll_is_coarse_but_each_result_rechecks_sources() {
            let mut session = Session::start();
            assert!(session.session_state(50).get("result").is_some());
            let before = session.source_stamps.load(Ordering::Relaxed);
            thread::sleep(Duration::from_millis(550));
            let idle = session.source_stamps.load(Ordering::Relaxed);
            assert!(idle - before <= 1, "Idle session repeatedly fingerprinted saved sources");
            assert!(session.session_state(51).get("result").is_some());
            assert!(
                session.source_stamps.load(Ordering::Relaxed) >= idle + 2,
                "Both the new request and its result must check saved inputs"
            );
            // A request arriving before the next idle poll must still notice a
            // saved dependency change and reject a same-version current claim.
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":52,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":session.client}}}));
            assert_eq!(session.until(|m| m["id"] == 52)["error"]["code"], CONTENT_MODIFIED);
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 20"
            });
            session.finish();
        }

        #[test]
        fn initial_unsaved_document_survives_setup_and_later_import_refresh() {
            let mut session = Session::start_document("New.lean");
            assert!(!session.dir.path().join("New.lean").exists());
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            let client = session.client.clone();
            let diagnostic = session.until(|m| {
                m["params"]["uri"] == client
                    && m["params"]["diagnostics"][0]["message"]
                        == "current fake imported value is 20"
            });
            assert_eq!(diagnostic["params"]["version"], 1);
            assert!(!session.dir.path().join("New.lean").exists());
            let calls = fs::read_to_string(session.dir.path().join("calls.jsonl")).unwrap();
            assert!(calls.lines().all(|line| {
                let call: Value = serde_json::from_str(line).unwrap();
                call["mode"] != "setup"
            }));
            let replays = fs::read_to_string(session.dir.path().join("replays.jsonl")).unwrap();
            let replay: Value = serde_json::from_str(replays.lines().last().unwrap()).unwrap();
            assert_eq!(replay["uri"], client);
            assert!(replay["text"].as_str().unwrap().contains("unsaved client note"));
            session.finish();
        }

        #[test]
        fn session_notifications_replay_in_order_including_updates_during_initialization() {
            let mut session = Session::start();
            session.send(json!({"jsonrpc":"2.0","method":"workspace/didChangeConfiguration","params":{"settings":{"test":1}}}));
            session.send(json!({"jsonrpc":"2.0","method":"workspace/didChangeConfiguration","params":{"settings":{"test":2}}}));
            session
                .send(json!({"jsonrpc":"2.0","method":"$/setTrace","params":{"value":"messages"}}));
            session
                .send(json!({"jsonrpc":"2.0","method":"$/test/appendState","params":{"value":1}}));
            assert!(session.session_state(53).get("result").is_some());
            fs::write(session.dir.path().join("hold-initialize"), "hold").unwrap();
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            session.wait_file("initialize-entered");
            session
                .send(json!({"jsonrpc":"2.0","method":"$/test/appendState","params":{"value":2}}));
            session
                .send(json!({"jsonrpc":"2.0","method":"$/setTrace","params":{"value":"verbose"}}));
            // This response fences the preceding client notifications while the
            // replacement is waiting for initialize, before replay is possible.
            assert_eq!(session.session_state(54)["error"]["code"], CONTENT_MODIFIED);
            fs::remove_file(session.dir.path().join("hold-initialize")).unwrap();
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 20"
            });
            assert_eq!(
                session.session_state(55)["result"],
                json!([
                    {"jsonrpc":"2.0","method":"workspace/didChangeConfiguration","params":{"settings":{"test":2}}},
                    {"jsonrpc":"2.0","method":"$/test/appendState","params":{"value":1}},
                    {"jsonrpc":"2.0","method":"$/test/appendState","params":{"value":2}},
                    {"jsonrpc":"2.0","method":"$/setTrace","params":{"value":"verbose"}}
                ])
            );
            session.finish();
        }

        #[test]
        fn successful_import_rebuild_refreshes_invalid_client_proof_and_preserves_buffer() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            let message = session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 20"
            });
            assert_eq!(message["params"]["version"], 1);
            let replays = fs::read_to_string(session.dir.path().join("replays.jsonl")).unwrap();
            let replay: Value = serde_json::from_str(replays.lines().last().unwrap()).unwrap();
            assert!(replay["text"].as_str().unwrap().contains("unsaved client note"));
            let calls = fs::read_to_string(session.dir.path().join("calls.jsonl")).unwrap();
            for line in calls.lines() {
                let call: Value = serde_json::from_str(line).unwrap();
                if call["mode"] == "build" {
                    let args = call["args"].as_array().unwrap();
                    assert!(
                        !args.is_empty(),
                        "Default build must not compile the live Client proof"
                    );
                    assert!(args.iter().all(|a| !a.as_str().unwrap().contains("Client")));
                }
            }
            session.finish();
        }

        #[test]
        fn dirty_dependency_blocks_goals_but_its_own_diagnostics_remain_interactive() {
            let mut session = Session::start();
            session.send(
                json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":session.local,"languageId":"lean4","version":1,"text":"def value := 10\n"}}}),
            );
            let local = session.local.clone();
            session
                .until(|m| m["params"]["uri"] == local && m["params"]["diagnostics"] == json!([]));
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":session.local,"version":2},
                "contentChanges":[{"text":"def value := 20\n"}]}}));
            let local = session.local.clone();
            session.until(|m| {
                m["params"]["uri"] == local
                    && m["params"]["version"] == 2
                    && m["params"]["diagnostics"] == json!([])
            });
            session.send(json!({"jsonrpc":"2.0","id":42,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":session.client},"position":{"line":1,"character":0}}}));
            let response = session.until(|m| m["id"] == 42);
            assert_eq!(response["error"]["code"], CONTENT_MODIFIED);
            assert_eq!(
                fs::read_to_string(session.dir.path().join("Local.lean")).unwrap(),
                "def value := 10\n"
            );
            session.finish();
        }

        #[test]
        fn failed_import_build_never_recredits_old_success() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("fail-build"), "fail").unwrap();
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            let client = session.client.clone();
            session.until(|m| {
                m["params"]["uri"] == client && m["params"]["diagnostics"][0]["source"] == "Anneal"
            });
            session.wait_file("build-failed");
            session.send(json!({"jsonrpc":"2.0","id":43,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":session.client}}}));
            assert_eq!(session.until(|m| m["id"] == 43)["error"]["code"], CONTENT_MODIFIED);
            assert_eq!(fs::read_to_string(session.dir.path().join("built-value")).unwrap(), "10");
            session.finish();
        }

        #[test]
        fn dependency_change_during_build_discards_cycle_and_late_same_version_goal() {
            let mut session = Session::start();
            let _ = fs::remove_file(session.dir.path().join("build-entered"));
            fs::write(session.dir.path().join("hold-build"), "hold").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":44,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":session.client}}}));
            session.wait_file("goal-entered");
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            session.wait_file("build-entered");
            fs::write(session.dir.path().join("Local.lean"), "def value := 30\n").unwrap();
            fs::remove_file(session.dir.path().join("hold-build")).unwrap();
            assert_eq!(session.until(|m| m["id"] == 44)["error"]["code"], CONTENT_MODIFIED);
            let fresh = session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 30"
            });
            assert_eq!(fresh["params"]["version"], 1);
            assert!(
                session.seen.iter().all(|m| m["params"]["diagnostics"][0]["message"]
                    != "current fake imported value is 20")
            );
            assert!(session.seen.iter().all(|m| m["id"] != 44 || m.get("result").is_none()));
            session.finish();
        }

        #[test]
        fn obsolete_failed_build_retries_new_saved_dependency_without_another_edit() {
            let mut session = Session::start();
            fs::remove_file(session.dir.path().join("build-entered")).unwrap();
            fs::write(session.dir.path().join("hold-build"), "hold").unwrap();
            // The peer captures this invalid state before waiting. Its failure
            // therefore belongs to the old cycle even after the source is fixed.
            fs::write(session.dir.path().join("Local.lean"), "def value := by unknown\n").unwrap();
            session.wait_file("build-entered");
            fs::write(session.dir.path().join("Local.lean"), "def value := 30\n").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":45,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":session.client}}}));
            assert_eq!(session.until(|m| m["id"] == 45)["error"]["code"], CONTENT_MODIFIED);
            // The response establishes that the coordinator has reconciled the
            // newer saved state before the old child is released to fail.
            fs::remove_file(session.dir.path().join("hold-build")).unwrap();
            session.wait_file("build-failed");
            let fresh = session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 30"
            });
            assert_eq!(fresh["params"]["version"], 1);
            assert_eq!(fs::read_to_string(session.dir.path().join("built-value")).unwrap(), "30");
            session.finish();
        }

        #[test]
        fn external_writer_suspends_results_and_replays_queued_unsaved_edits() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("busy-writer"), "writer active").unwrap();
            let client = session.client.clone();
            session.until(|m| {
                m["params"]["uri"] == client && m["params"]["diagnostics"][0]["source"] == "Anneal"
            });
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":session.client,"version":2},
                "contentChanges":[{"text":"import Middle\nexample : middle = 10 := by decide\n-- queued unsaved edit\n"}]}}));
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            fs::remove_file(session.dir.path().join("busy-writer")).unwrap();
            let fresh = session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 20"
            });
            assert_eq!(fresh["params"]["version"], 2);
            let replays = fs::read_to_string(session.dir.path().join("replays.jsonl")).unwrap();
            let replay: Value = serde_json::from_str(replays.lines().last().unwrap()).unwrap();
            assert!(replay["text"].as_str().unwrap().contains("queued unsaved edit"));
            session.finish();
        }

        #[test]
        fn unsaved_import_change_uses_live_setup_header_without_overwriting_source() {
            let mut session = Session::start();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":session.client,"version":2},
                "contentChanges":[{"text":"import Local\nexample : True := by trivial\n-- unsaved new header\n"}]}}));
            let client = session.client.clone();
            session.until(|m| {
                m["params"]["uri"] == client
                    && m["params"]["version"] == 2
                    && m["params"]["diagnostics"] == json!([])
            });
            let headers = fs::read_to_string(session.dir.path().join("headers.jsonl")).unwrap();
            let header: Value = serde_json::from_str(headers.lines().last().unwrap()).unwrap();
            assert!(header["imports"].as_array().unwrap().iter().any(|i| i["module"] == "Local"));
            assert!(header["imports"].as_array().unwrap().iter().all(|i| i["module"] != "Middle"));
            assert!(
                fs::read_to_string(session.dir.path().join("Client.lean"))
                    .unwrap()
                    .contains("import Middle")
            );
            session.finish();
        }
    }
}
