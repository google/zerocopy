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

use crate::lean_sdk::{LakeOperation, LocalOutputPreparation, SourceStampChanged, Workspace};

const MAX_MESSAGE: usize = 16 * 1024 * 1024;
const MAX_QUEUED_EVENTS: usize = 2048;
const MAX_CLIENT_TURNS: usize = 16;
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
    fn folds_ascii_case(&self) -> Result<bool>;
    fn prepare_local_outputs(&self) -> Result<Option<LocalOutputPreparation>>;
    fn finish_local_outputs(&self, prepared: &LocalOutputPreparation) -> Result<()>;
    fn lake_command(&self, operation: LakeOperation<'_>) -> Result<Command>;
    fn contains_source(&self, path: &Path) -> Result<bool>;
    fn contains_immutable_sdk_source(&self, path: &Path) -> Result<bool>;
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
    fn folds_ascii_case(&self) -> Result<bool> {
        Workspace::folds_ascii_case(self)
    }
    fn prepare_local_outputs(&self) -> Result<Option<LocalOutputPreparation>> {
        Workspace::prepare_local_outputs(self).map(Some)
    }
    fn finish_local_outputs(&self, prepared: &LocalOutputPreparation) -> Result<()> {
        Workspace::finish_local_outputs(self, prepared)
    }
    fn lake_command(&self, operation: LakeOperation<'_>) -> Result<Command> {
        Workspace::lake_command(self, operation)
    }
    fn contains_source(&self, path: &Path) -> Result<bool> {
        Workspace::contains_source(self, path)
    }
    fn contains_immutable_sdk_source(&self, path: &Path) -> Result<bool> {
        Workspace::contains_immutable_sdk_source(self, path)
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

/// Only a disappearing local source is an expected save race. Permission,
/// malformed text, provider ambiguity, and admission failures remain fatal.
fn local_read<T>(result: io::Result<T>, path: &Path) -> Result<T> {
    result.map_err(|error| {
        if error.kind() == io::ErrorKind::NotFound {
            SourceStampChanged::new(format!(
                "Local editor source disappeared while reading: {}",
                path.display()
            ))
            .into()
        } else {
            error.into()
        }
    })
}

fn private_source_name(name: &std::ffi::OsStr, folds_case: bool) -> bool {
    [".lake", ".git", ".runtime", ".anneal-bin"].iter().any(|private| {
        if folds_case {
            name.as_encoded_bytes().eq_ignore_ascii_case(private.as_bytes())
        } else {
            name.as_encoded_bytes() == private.as_bytes()
        }
    })
}

fn same_source_path(left: &Path, right: &Path, folds_case: bool) -> bool {
    left == right
        || (folds_case
            && left
                .as_os_str()
                .as_encoded_bytes()
                .eq_ignore_ascii_case(right.as_os_str().as_encoded_bytes()))
}

fn same_bound_root(path: &Path, root: &Path, folds_case: bool) -> bool {
    source_relative_path(path, root, folds_case)
        .is_some_and(|relative| relative.as_os_str().is_empty())
}

fn source_relative_path<'a>(path: &'a Path, root: &Path, folds_case: bool) -> Option<&'a Path> {
    let mut components = path.components();
    for expected in root.components() {
        let component = components.next()?;
        if component != expected
            && !(folds_case
                && component
                    .as_os_str()
                    .as_encoded_bytes()
                    .eq_ignore_ascii_case(expected.as_os_str().as_encoded_bytes()))
        {
            return None;
        }
    }
    Some(components.as_path())
}

fn process_scoped_notification(method: &str) -> bool {
    [
        "$/lean/rpc/keepAlive",
        "$/lean/rpc/release",
        "window/workDoneProgress/cancel",
        "workspace/didChangeWatchedFiles",
    ]
    .contains(&method)
}

#[derive(Default, Clone, Debug)]
struct Inputs {
    texts: BTreeMap<PathBuf, String>,
    retained: BTreeMap<String, RetainedProvider>,
    modules: BTreeMap<String, PathBuf>,
    module_names: BTreeMap<String, String>,
    folds_case: bool,
    edges: BTreeMap<PathBuf, BTreeMap<String, PathBuf>>,
    uncertain: BTreeSet<PathBuf>,
}

#[derive(Clone, Debug)]
struct RetainedProvider {
    path: PathBuf,
    name: String,
    saved: bool,
}

impl Inputs {
    fn read(
        workspace_root: &Path,
        roots: &[PathBuf],
        documents: &BTreeMap<String, Document>,
        folds_case: bool,
    ) -> Result<Self> {
        let mut result = Self { folds_case, ..Self::default() };
        let physical_workspace =
            fs::canonicalize(workspace_root).context("Unknown editor workspace")?;
        for root in roots {
            if !root.exists() {
                continue;
            }
            for entry in walkdir::WalkDir::new(root)
                .follow_links(false)
                .into_iter()
                .filter_entry(|e| !private_source_name(e.file_name(), folds_case))
            {
                let entry = entry.map_err(|error| {
                    if error.io_error().is_some_and(|e| e.kind() == io::ErrorKind::NotFound) {
                        anyhow::Error::new(SourceStampChanged::new(format!(
                            "Local editor source disappeared during traversal: {error}"
                        )))
                    } else {
                        error.into()
                    }
                })?;
                ensure!(!entry.file_type().is_symlink(), "Local editor source contains a symlink");
                if !entry.file_type().is_file()
                    || entry.path().extension().and_then(|e| e.to_str()).is_none_or(|e| {
                        e != "lean" && !(folds_case && e.eq_ignore_ascii_case("lean"))
                    })
                {
                    continue;
                }
                // Overlapping roots can spell the same directory differently.
                // Keep one stored path spelling, relative to the bound workspace.
                let physical = local_read(fs::canonicalize(entry.path()), entry.path())?;
                let path = workspace_root.join(
                    physical
                        .strip_prefix(&physical_workspace)
                        .context("Local editor source resolves outside the workspace")?,
                );
                ensure!(
                    same_source_path(entry.path(), &path, folds_case),
                    "Local editor source resolves through an alias other than the bound case policy"
                );
                let module = source_relative_path(&path, root, folds_case)
                    .context("Local editor source is outside its bound source root")?
                    .with_extension("")
                    .components()
                    .map(|c| c.as_os_str().to_str().context("Non-UTF8 local module path"))
                    .collect::<Result<Vec<_>>>()?
                    .join(".");
                let key = result.module_key(&module);
                result.module_names.entry(key.clone()).or_insert(module.clone());
                if let Some(old) = result.modules.get(&key) {
                    ensure!(old == &path, "Ambiguous local module provider");
                } else {
                    result.modules.insert(key.clone(), path.clone());
                }
                result.retained.insert(
                    key,
                    RetainedProvider { path: path.clone(), name: module, saved: true },
                );
                if !result.texts.contains_key(&path) {
                    result
                        .texts
                        .insert(path.clone(), local_read(fs::read_to_string(&path), &path)?);
                }
            }
        }
        result.add_documents(roots, documents)?;
        result.rebuild_edges(documents, workspace_root, true);
        Ok(result)
    }

    fn module_key(&self, name: &str) -> String {
        if self.folds_case { name.to_ascii_lowercase() } else { name.to_owned() }
    }

    fn saved_path(&self, path: &Path) -> Option<&PathBuf> {
        self.texts.get_key_value(path).map(|(path, _)| path).or_else(|| {
            self.folds_case
                .then(|| self.texts.keys().find(|saved| same_source_path(saved, path, true)))
                .flatten()
        })
    }

    fn add_documents(
        &mut self,
        roots: &[PathBuf],
        documents: &BTreeMap<String, Document>,
    ) -> Result<()> {
        // Only saved history and orphan-output evidence survive a live update.
        // Rebuild live providers so closing a never-saved buffer discards every
        // root alias without turning it into a deleted-source tombstone.
        self.modules = self
            .retained
            .iter()
            .map(|(key, provider)| (key.clone(), provider.path.clone()))
            .collect();
        self.module_names = self
            .retained
            .iter()
            .map(|(key, provider)| (key.clone(), provider.name.clone()))
            .collect();
        let mut live = BTreeSet::new();
        for document in documents.values().filter(|d| d.local) {
            for relative in roots
                .iter()
                .filter_map(|root| source_relative_path(&document.path, root, self.folds_case))
            {
                let module = relative
                    .with_extension("")
                    .components()
                    .map(|c| c.as_os_str().to_str().context("Non-UTF8 local module path"))
                    .collect::<Result<Vec<_>>>()?
                    .join(".");
                let key = self.module_key(&module);
                let inferred = !live.contains(&key)
                    && self.retained.get(&key).is_some_and(|provider| !provider.saved);
                if let Some(old) = self.modules.get(&key) {
                    ensure!(
                        same_source_path(old, &document.path, self.folds_case) || inferred,
                        "Ambiguous live local module provider"
                    );
                }
                if inferred || !self.modules.contains_key(&key) {
                    self.modules.insert(key.clone(), document.path.clone());
                    self.module_names.insert(key.clone(), module);
                }
                live.insert(key);
            }
        }
        Ok(())
    }

    fn rebuild_edges(
        &mut self,
        documents: &BTreeMap<String, Document>,
        workspace_root: &Path,
        probe_outputs: bool,
    ) {
        self.edges.clear();
        self.uncertain.clear();
        let mut texts = self.texts.clone();
        for document in documents.values() {
            if source_relative_path(&document.path, workspace_root, self.folds_case).is_some() {
                texts.insert(document.path.clone(), document.text.clone());
            }
        }
        for (path, text) in texts {
            match imports(&text) {
                Some(names) => {
                    for name in &names {
                        let key = self.module_key(name);
                        if !self.modules.contains_key(&key) {
                            let relative = PathBuf::from(name.replace('.', "/"));
                            // At startup an orphaned private output is already a
                            // missing local provider, not a shared SDK module.
                            if probe_outputs
                                && workspace_root
                                    .join(".lake/build/lib/lean")
                                    .join(relative.with_extension("olean"))
                                    .exists()
                            {
                                let path = workspace_root.join(relative.with_extension("lean"));
                                self.retained.insert(
                                    key.clone(),
                                    RetainedProvider {
                                        path: path.clone(),
                                        name: name.clone(),
                                        saved: false,
                                    },
                                );
                                self.modules.insert(key.clone(), path);
                                self.module_names.insert(key, name.clone());
                            }
                        }
                    }
                    // Retain the imported name, not just its physical provider:
                    // overlapping roots can assign several aliases to one file.
                    let edges = names
                        .iter()
                        .filter_map(|name| {
                            let key = self.module_key(name);
                            self.modules.get(&key).map(|path| (key, path.clone()))
                        })
                        .collect();
                    self.edges.insert(path, edges);
                }
                None => {
                    self.uncertain.insert(path);
                }
            }
        }
    }

    fn dependency_closure(&self, path: &Path) -> (BTreeSet<PathBuf>, BTreeSet<String>) {
        let mut result = BTreeSet::new();
        let mut targets = BTreeSet::new();
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
                for (module, edge) in edges {
                    targets.insert(module.clone());
                    if edge != path && result.insert(edge.clone()) {
                        work.push(edge.clone());
                    }
                }
            }
        }
        (result, targets)
    }

    fn dependencies(&self, path: &Path) -> BTreeSet<PathBuf> {
        self.dependency_closure(path).0
    }

    fn in_import_cycle(&self, path: &Path) -> bool {
        let mut seen = BTreeSet::new();
        let mut work = vec![path.to_path_buf()];
        while let Some(next) = work.pop() {
            if let Some(edges) = self.edges.get(&next) {
                for edge in edges.values() {
                    if edge == path {
                        return true;
                    }
                    if seen.insert(edge.clone()) {
                        work.push(edge.clone());
                    }
                }
            }
        }
        false
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
    wait: Option<VersionWait>,
    snapshot: Option<WaitSnapshot>,
}

#[derive(Clone)]
struct ServerRequest {
    original: Value,
    generation: u64,
    watcher: Option<Value>,
}

#[derive(Clone)]
struct WaitSnapshot {
    stamp: [u8; 32],
    generation: u64,
    input: RefreshInput,
}

#[derive(Clone)]
struct VersionWait {
    minimum: i64,
    message: Value,
    snapshot: Option<WaitSnapshot>,
    ileans: bool,
    diagnostics_barrier: bool,
}

#[derive(Clone, PartialEq)]
struct RefreshInput {
    header: Value,
    dependencies: BTreeSet<PathBuf>,
    targets: BTreeSet<String>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum PendingReason {
    ImportedInputs,
    ImportCycle,
}

#[derive(Clone)]
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
    failed_inputs: BTreeMap<PathBuf, RefreshInput>,
    outputs_uncommitted: bool,
    refreshing: bool,
    snapshot_pending: bool,
    initialized: Option<Value>,
    initialize: Option<Value>,
    notifications: Vec<Value>,
    notification_bytes: usize,
    notifications_sent: usize,
    requests: BTreeMap<String, Request>,
    server_requests: BTreeMap<String, ServerRequest>,
    registered_watcher: Option<Value>,
    published_pending: BTreeMap<String, (i64, PendingReason)>,
}

impl State {
    fn new(root: PathBuf, roots: Vec<PathBuf>, stamp: [u8; 32], folds_case: bool) -> Result<Self> {
        let documents = BTreeMap::new();
        let inputs = Inputs::read(&root, &roots, &documents, folds_case)?;
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
            failed_inputs: BTreeMap::new(),
            outputs_uncommitted: false,
            refreshing: false,
            snapshot_pending: false,
            initialized: None,
            initialize: None,
            notifications: Vec::new(),
            notification_bytes: 0,
            notifications_sent: 0,
            requests: BTreeMap::new(),
            server_requests: BTreeMap::new(),
            registered_watcher: None,
            published_pending: BTreeMap::new(),
        })
    }

    fn remember_notification(&mut self, message: &Value) -> Result<()> {
        let method = message["method"].as_str().context("Missing notification method")?;
        // Process RPC/progress IDs and watched-file event hints belong to the
        // live worker. A replacement rereads saved Lean inputs and its .ilean
        // search path; replaying old events cannot restore current state.
        if process_scoped_notification(method) {
            return Ok(());
        }
        // Standard settings notifications contain the complete current value.
        // Other notifications may be cumulative, so retain their original order.
        if ["workspace/didChangeConfiguration", "$/setTrace"].contains(&method) {
            if let Some(index) = self.notifications.iter().position(|m| m["method"] == method) {
                let previous = self.notifications.remove(index);
                self.notification_bytes -= serde_json::to_vec(&previous)?.len();
                if index < self.notifications_sent {
                    self.notifications_sent -= 1;
                }
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
            return self.refreshing || self.snapshot_pending;
        };
        if self.refreshing || self.snapshot_pending || self.invalid.contains(&doc.path) {
            return true;
        }
        if self.inputs.in_import_cycle(&doc.path) {
            return true;
        }
        if self.inputs.uncertain.contains(&doc.path) {
            return true;
        }
        let deps = self.inputs.dependencies(&doc.path);
        if deps.iter().any(|path| self.inputs.in_import_cycle(path)) {
            return true;
        }
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
        if let Some(wait) = &request.wait {
            let Some(uri) = &request.uri else { return false };
            let Some(document) = self.documents.get(uri) else { return false };
            // An undispatched synchronization request names a future version,
            // not the current buffer or imports. Its expected save/header edits
            // and the builds they require are progress toward that version.
            let Some(snapshot) = &wait.snapshot else { return true };
            return snapshot.stamp == self.stamp
                && snapshot.generation == self.generation
                && document.version >= wait.minimum
                && !self.blocked(uri)
                && self.refresh_input(document).as_ref() == Some(&snapshot.input);
        }
        !self.refreshing
            && !self.snapshot_pending
            && match &request.uri {
                Some(uri) => {
                    let Some(snapshot) = &request.snapshot else { return false };
                    snapshot.stamp == self.stamp
                        && snapshot.generation == self.generation
                        && !self.blocked(uri)
                        && self.documents.get(uri).map(|d| d.version) == request.version
                        && self.request_snapshot(uri).as_ref().map(|s| &s.input)
                            == Some(&snapshot.input)
                }
                None => {
                    request.epoch == self.epoch
                        && !self.documents.keys().any(|uri| self.blocked(uri))
                }
            }
    }

    fn request_snapshot(&self, uri: &str) -> Option<WaitSnapshot> {
        let input = self.refresh_input(self.documents.get(uri)?)?;
        Some(WaitSnapshot { stamp: self.stamp, generation: self.generation, input })
    }

    fn changed_inputs(&mut self, stamp: [u8; 32]) -> Result<bool> {
        self.changed_inputs_with_refresh(stamp, false)
    }

    fn changed_inputs_with_refresh(
        &mut self,
        stamp: [u8; 32],
        refresh_graph: bool,
    ) -> Result<bool> {
        if self.stamp == stamp && !refresh_graph {
            return Ok(false);
        }
        let previous = self.inputs.clone();
        self.inputs =
            Inputs::read(&self.root, &self.roots, &self.documents, self.inputs.folds_case)?;
        // An unsaved buffer may first reach disk with another ASCII spelling.
        // Use the admitted saved path for its overlay, dirty checks and closure
        // membership. The outer snapshot transaction commits both together.
        for document in self.documents.values_mut().filter(|document| document.local) {
            if let Some(saved) = self.inputs.saved_path(&document.path) {
                if &document.path != saved {
                    self.invalid.remove(&document.path);
                    document.path = saved.clone();
                }
            }
        }
        // Remember deleted local providers: an old private .olean must not
        // silently turn a missing source into an apparently shared import.
        for (module, provider) in &previous.retained {
            if self
                .inputs
                .retained
                .get(module)
                .is_none_or(|current| !current.saved && provider.saved)
            {
                // A real saved path also outranks a freshly inferred orphan
                // path, which may not know this library's nested source root.
                self.inputs.retained.insert(module.clone(), provider.clone());
            }
        }
        self.inputs.add_documents(&self.roots, &self.documents)?;
        self.inputs.rebuild_edges(&self.documents, &self.root, true);
        // The full stamp can include configuration and auxiliary inputs along
        // with Lean edits. A Lean text difference never proves those other
        // inputs stayed fixed; conservatively refresh every open document.
        self.invalid.extend(self.documents.values().map(|doc| doc.path.clone()));
        self.failed_inputs.clear();
        self.published_pending.clear();
        self.stamp = stamp;
        self.epoch += 1;
        Ok(!self.invalid.is_empty())
    }

    fn refresh_input(&self, document: &Document) -> Option<RefreshInput> {
        let header = module_header(&document.text)?;
        let (dependencies, targets) = self.inputs.dependency_closure(&document.path);
        if dependencies.iter().any(|path| {
            !self.inputs.texts.contains_key(path)
                || self.inputs.uncertain.contains(path)
                || self.documents.values().any(|d| &d.path == path && self.inputs.dirty(d))
        }) {
            return None;
        }
        Some(RefreshInput { header, dependencies, targets })
    }

    fn build_documents(&self, initial: bool) -> BTreeMap<PathBuf, RefreshInput> {
        self.documents
            .values()
            .filter(|doc| initial || self.invalid.contains(&doc.path))
            .filter_map(|doc| self.refresh_input(doc).map(|input| (doc.path.clone(), input)))
            .filter(|(path, input)| self.failed_inputs.get(path) != Some(input))
            .collect()
    }

    fn matching_documents(&self, inputs: &BTreeMap<PathBuf, RefreshInput>) -> BTreeSet<PathBuf> {
        self.documents
            .values()
            .filter_map(|doc| {
                let input = inputs.get(&doc.path)?;
                (self.refresh_input(doc).as_ref() == Some(input)).then(|| doc.path.clone())
            })
            .collect()
    }

    fn own_diagnostic_documents(&self) -> BTreeSet<PathBuf> {
        self.documents
            .values()
            .filter_map(|doc| {
                let input = self.refresh_input(doc)?;
                (input.dependencies.is_empty() && !self.inputs.in_import_cycle(&doc.path))
                    .then(|| doc.path.clone())
            })
            .collect()
    }

    fn update_document(&mut self, message: &Value, allow_shared: bool) -> Result<bool> {
        self.update_document_with_outputs(message, allow_shared, true)
    }

    fn update_document_with_outputs(
        &mut self,
        message: &Value,
        allow_shared: bool,
        probe_outputs: bool,
    ) -> Result<bool> {
        let method = message["method"].as_str().unwrap_or("");
        let params = &message["params"];
        let uri = params["textDocument"]["uri"].as_str().context("Document URI missing")?;
        let old_dependencies = self.documents.get(uri).map(|d| self.inputs.dependencies(&d.path));
        match method {
            "textDocument/didOpen" => {
                self.closed.remove(uri);
                let mut path = file_uri(uri)?;
                if let Some(saved) = self.inputs.saved_path(&path) {
                    path = saved.clone();
                }
                let relative = source_relative_path(&path, &self.root, self.inputs.folds_case);
                let local = relative.is_some();
                ensure!(
                    local || allow_shared,
                    "Editor document is outside the bound source providers"
                );
                if local {
                    ensure!(
                        !relative.unwrap().components().any(|component| {
                            private_source_name(component.as_os_str(), self.inputs.folds_case)
                        }),
                        "Editor document is inside a private workspace directory"
                    );
                }
                if !local {
                    ensure!(
                        fs::read_to_string(&path)?
                            == params["textDocument"]["text"].as_str().unwrap_or(""),
                        "Immutable SDK source was opened with a modified buffer"
                    );
                }
                ensure!(
                    path.extension().and_then(|e| e.to_str()).is_some_and(|e| {
                        e == "lean" || (self.inputs.folds_case && e.eq_ignore_ascii_case("lean"))
                    }),
                    "Editor document is not a Lean source"
                );
                ensure!(
                    !self.documents.iter().any(|(other, d)| {
                        other != uri && same_source_path(&d.path, &path, self.inputs.folds_case)
                    }),
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
        // Saved bytes were reconciled before this event. A live edit only
        // overlays the in-memory graph, so it cannot be partially applied by a
        // concurrent file-read race or write the unsaved buffer to disk.
        self.inputs.add_documents(&self.roots, &self.documents)?;
        self.inputs.rebuild_edges(&self.documents, &self.root, probe_outputs);
        self.published_pending.remove(uri);
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
            let cycle = self.inputs.in_import_cycle(&self.documents[&uri].path);
            let reason =
                if cycle { PendingReason::ImportCycle } else { PendingReason::ImportedInputs };
            if self.published_pending.get(&uri) == Some(&(version, reason)) {
                continue;
            }
            // Replacing, rather than incrementally appending, explicitly removes
            // previous successful diagnostics when their inputs cease to be current.
            result.push(json!({"jsonrpc":"2.0", "method":"textDocument/publishDiagnostics", "params": {
                "uri":uri, "version":version, "isIncremental":false, "diagnostics":[{
                    "range":{"start":{"line":0,"character":0},"end":{"line":0,"character":0}},
                    "severity":if cycle { 1 } else { 2 }, "source":"Anneal",
                    "message":if cycle {
                        "Local import cycle: this source is reachable through its own imports. Break the cycle before dependent results can refresh."
                    } else {
                        "Local imported inputs are pending: save or discard dependency edits; a successful build and worker refresh are required."
                    }}]}}));
            self.published_pending.insert(uri, (version, reason));
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

fn current_versioned_notification(state: &State, message: &Value) -> bool {
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
    let Some(uri) = uri_of(message) else { return false };
    let version = message["params"]["version"]
        .as_i64()
        .or_else(|| message["params"]["textDocument"]["version"].as_i64());
    state.documents.get(&uri).is_some_and(|document| Some(document.version) == version)
}

fn lean_watcher_registration(message: &Value) -> Option<Value> {
    if message["method"] != "client/registerCapability" {
        return None;
    }
    let registrations = message["params"]["registrations"].as_array()?;
    (registrations.len() == 1 && registrations[0]["id"] == "lean_watcher")
        .then(|| registrations[0].clone())
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

/// A bounded client batch cannot starve server replies. Document updates still
/// get lookahead validation before accepting any result from the server turn.
fn next_event(
    clients: &mut VecDeque<Event>,
    servers: &mut VecDeque<Event>,
    client_turns: &mut usize,
    terminating: bool,
) -> Option<Event> {
    let server_index = (!servers.is_empty()).then_some(0);
    next_event_at(clients, servers, client_turns, terminating, server_index)
}

fn next_event_at(
    clients: &mut VecDeque<Event>,
    servers: &mut VecDeque<Event>,
    client_turns: &mut usize,
    terminating: bool,
    server_index: Option<usize>,
) -> Option<Event> {
    if !terminating
        && server_index.is_some()
        && (clients.is_empty() || *client_turns >= MAX_CLIENT_TURNS)
    {
        *client_turns = 0;
        servers.remove(server_index.unwrap())
    } else if let Some(event) = clients.pop_front() {
        *client_turns = client_turns.saturating_add(1).min(MAX_CLIENT_TURNS);
        Some(event)
    } else {
        *client_turns = 0;
        server_index.and_then(|index| servers.remove(index))
    }
}

fn queued_document_update(events: &VecDeque<Event>, state: &State, uri: Option<&str>) -> bool {
    let scope = uri.and_then(|uri| state.documents.get(uri)).map(|doc| {
        let mut paths = state.inputs.dependencies(&doc.path);
        paths.insert(doc.path.clone());
        paths
    });
    events.iter().any(|event| {
        let Event::Client(Ok(Some(message))) = event else { return false };
        if !matches!(
            message["method"].as_str(),
            Some(
                "textDocument/didOpen"
                    | "textDocument/didChange"
                    | "textDocument/didClose"
                    | "textDocument/didSave"
            )
        ) {
            return false;
        }
        // Opening a previously unresolved local provider can create a new
        // dependency edge. Until this queued open is applied, the current
        // graph cannot safely narrow its affected documents by path.
        if message["method"] == "textDocument/didOpen" {
            return true;
        }
        let Some(changed_uri) = uri_of(message) else { return true };
        if uri == Some(changed_uri.as_str()) {
            return true;
        }
        let changed_path = state
            .documents
            .get(&changed_uri)
            .map(|doc| doc.path.clone())
            .or_else(|| file_uri(&changed_uri).ok());
        let Some(changed_path) = changed_path else { return true };
        scope.as_ref().is_none_or(|paths| {
            paths.iter().any(|path| {
                path == &changed_path
                    || (state.inputs.folds_case
                        && path
                            .as_os_str()
                            .as_encoded_bytes()
                            .eq_ignore_ascii_case(changed_path.as_os_str().as_encoded_bytes()))
            })
        })
    })
}

fn stale_workspace_edit(events: &VecDeque<Event>, state: &State) -> bool {
    // A WorkspaceEdit may omit document versions and name several documents.
    // Unknown resource operations also have no safe narrow dependency scope.
    // Withhold the whole edit while any pending client update or tracked input
    // could make its ranges obsolete.
    queued_document_update(events, state, None)
        || state.refreshing
        || state.snapshot_pending
        || !state.invalid.is_empty()
        || state.documents.keys().any(|uri| state.blocked(uri))
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

struct BuildBatch {
    commands: VecDeque<PreparedCommand>,
    documents: BTreeMap<PathBuf, RefreshInput>,
}

struct BuildOutcome {
    covered: BTreeMap<PathBuf, RefreshInput>,
    attempted: BTreeMap<PathBuf, RefreshInput>,
    failed: bool,
}

struct Build {
    process: Option<Process>,
    input_result: Option<mpsc::Receiver<io::Result<()>>>,
    commands: VecDeque<PreparedCommand>,
    batch_documents: BTreeMap<PathBuf, RefreshInput>,
    batches: VecDeque<BuildBatch>,
    covered: BTreeMap<PathBuf, RefreshInput>,
    attempted: BTreeMap<PathBuf, RefreshInput>,
    failed: bool,
    had_commands: bool,
    stamp: [u8; 32],
    preparation: Option<LocalOutputPreparation>,
    _writer: fs::File,
}

impl Build {
    fn stop(&mut self) {
        if let Some(process) = &mut self.process {
            process.stop();
        }
        self.process = None;
        self.input_result = None;
        self.commands.clear();
        self.batches.clear();
    }

    fn spawn(
        batches: VecDeque<BuildBatch>,
        attempted: BTreeMap<PathBuf, RefreshInput>,
        stamp: [u8; 32],
        preparation: Option<LocalOutputPreparation>,
        writer: fs::File,
    ) -> Result<Self> {
        let had_commands = batches.iter().any(|batch| !batch.commands.is_empty());
        let mut build = Self {
            process: None,
            input_result: None,
            commands: VecDeque::new(),
            batch_documents: BTreeMap::new(),
            batches,
            covered: BTreeMap::new(),
            attempted,
            failed: false,
            had_commands,
            stamp,
            preparation,
            _writer: writer,
        };
        build.start_next_batch()?;
        Ok(build)
    }
    fn start_next_batch(&mut self) -> Result<()> {
        while let Some(batch) = self.batches.pop_front() {
            self.commands = batch.commands;
            self.batch_documents = batch.documents;
            if let Some(command) = self.commands.pop_front() {
                let (process, input) = Self::child(command)?;
                self.process = Some(process);
                self.input_result = input;
                return Ok(());
            }
            self.covered.append(&mut self.batch_documents);
        }
        self.process = None;
        self.input_result = None;
        Ok(())
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
    fn poll(&mut self) -> Result<Option<BuildOutcome>> {
        let Some(process) = self.process.as_mut() else {
            return Ok(Some(BuildOutcome {
                covered: self.covered.clone(),
                attempted: self.attempted.clone(),
                failed: self.failed,
            }));
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
                    self.failed = true;
                    self.commands.clear();
                    self.start_next_batch()?;
                    return Ok(None);
                }
            }
        }
        process.stop();
        if !status.success() {
            self.failed = true;
            self.commands.clear();
            self.start_next_batch()?;
            return Ok(None);
        }
        if let Some(command) = self.commands.pop_front() {
            let (process, input) = Self::child(command)?;
            self.process = Some(process);
            self.input_result = input;
            Ok(None)
        } else {
            self.covered.append(&mut self.batch_documents);
            self.start_next_batch()?;
            Ok(None)
        }
    }
}

fn partition_documents(
    documents: &BTreeMap<PathBuf, RefreshInput>,
) -> Vec<(BTreeSet<String>, BTreeMap<PathBuf, RefreshInput>)> {
    // A compile or setup failure belongs to one document. A failed
    // {Broken, Shared} closure must not hold an independent {Shared} importer.
    // Repeated shared targets cost another warm Lake invocation, bounded by
    // the number of selected documents in this saved-input generation.
    documents
        .iter()
        .map(|(path, input)| {
            (input.targets.clone(), BTreeMap::from([(path.clone(), input.clone())]))
        })
        .collect()
}

fn build_commands(
    workspace: &dyn Host,
    state: &State,
    documents: &BTreeMap<PathBuf, RefreshInput>,
) -> Result<VecDeque<BuildBatch>> {
    let mut batches = VecDeque::new();
    for (modules, members) in partition_documents(documents) {
        let mut commands = VecDeque::new();
        let targets: Vec<_> = modules
            .iter()
            .map(|module| format!("+{}:olean", state.inputs.module_names[module]))
            .collect();
        if !targets.is_empty() {
            commands.push_back(PreparedCommand {
                command: workspace.lake_command(LakeOperation::Build(&targets))?,
                input: None,
            });
        }
        for doc in state.documents.values().filter(|d| d.local && members.contains_key(&d.path)) {
            // setup-file requires a saved path. A newly created unsaved document
            // still reaches the server with its live header and complete buffer.
            if !doc.path.try_exists()? {
                continue;
            }
            let header = &members[&doc.path].header;
            let mut command = match workspace.lake_command(LakeOperation::SetupFile(&doc.path)) {
                Ok(command) => command,
                Err(error) => {
                    if !doc.path.try_exists()? {
                        return Err(SourceStampChanged::new(format!(
                            "Local editor source disappeared during setup: {}",
                            doc.path.display()
                        ))
                        .into());
                    }
                    return Err(error);
                }
            };
            command.arg("-");
            let mut input = serde_json::to_vec(header)?;
            input.push(b'\n');
            ensure!(input.len() <= MAX_MESSAGE, "Oversized live module header");
            commands.push_back(PreparedCommand { command, input: Some(input) });
        }
        batches.push_back(BuildBatch { commands, documents: members });
    }
    Ok(batches)
}

fn cancel_requests(state: &mut State, output: &mut impl Write) -> Result<()> {
    cancel_requests_with_waiters(state, output, false)
}

fn clear_closed_diagnostics(state: &mut State, output: &mut impl Write) -> Result<()> {
    let closed = state.closed.clone();
    for (uri, (_, version)) in closed {
        let clear = json!({"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{
            "uri":uri,"version":version,"isIncremental":false,"diagnostics":[]}});
        if state.take_closed_diagnostics(&clear) {
            write_message(output, &clear)?;
        }
    }
    Ok(())
}

fn cancel_requests_with_waiters(
    state: &mut State,
    output: &mut impl Write,
    retain_waiters: bool,
) -> Result<()> {
    for (key, request) in std::mem::take(&mut state.requests) {
        if retain_waiters && request.wait.as_ref().is_some_and(|w| w.snapshot.is_none()) {
            state.requests.insert(key, request);
            continue;
        }
        write_message(
            output,
            &error(request.original, "Document or imported input state changed"),
        )?;
    }
    Ok(())
}

fn dispatch_version_waits(state: &mut State, server: &mut Server) -> Result<()> {
    let ready: Vec<_> = state
        .requests
        .iter()
        .filter_map(|(key, request)| {
            let wait = request.wait.as_ref()?;
            if wait.snapshot.is_some() {
                return None;
            }
            let uri = request.uri.as_ref()?;
            let document = state.documents.get(uri)?;
            if document.version < wait.minimum || state.blocked(uri) {
                return None;
            }
            let input = state.refresh_input(document)?;
            Some((key.clone(), input, document.version))
        })
        .collect();
    for (key, input, version) in ready {
        let request = state.requests.get_mut(&key).unwrap();
        let wait = request.wait.as_mut().unwrap();
        wait.snapshot =
            Some(WaitSnapshot { stamp: state.stamp, generation: state.generation, input });
        let mut message = wait.message.clone();
        message["id"] = json!(key);
        if wait.ileans {
            // RC2's reporter emits ileanInfoFinal before its task completes;
            // waitForDiagnostics waits that task, and the watchdog processes
            // the final notification before forwarding the response. This
            // avoids its removal of an unsatisfied ILean wait on an older final.
            wait.diagnostics_barrier = true;
            message["method"] = json!("textDocument/waitForDiagnostics");
            message["params"] = json!({"uri":request.uri,"version":version});
        }
        server.send(&message)?;
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

fn validate_initialize(message: &Value, root: &Path, folds_case: bool) -> Result<()> {
    if let Some(uri) = message["params"]["rootUri"].as_str() {
        ensure!(
            same_bound_root(&file_uri(uri)?, root, folds_case),
            "Editor initialization selects another workspace"
        );
    }
    if !message["params"]["rootPath"].is_null() {
        let path = Path::new(
            message["params"]["rootPath"]
                .as_str()
                .context("Editor initialization rootPath is not a path")?,
        );
        ensure!(
            path.is_absolute()
                && !path.components().any(|c| matches!(c, std::path::Component::ParentDir))
                && same_bound_root(
                    &path
                        .components()
                        .filter(|c| !matches!(c, std::path::Component::CurDir))
                        .collect::<PathBuf>(),
                    root,
                    folds_case,
                ),
            "Editor initialization selects another workspace"
        );
    }
    if let Some(folders) = message["params"]["workspaceFolders"].as_array() {
        ensure!(
            folders.iter().all(|folder| {
                folder["uri"]
                    .as_str()
                    .and_then(|uri| file_uri(uri).ok())
                    .is_some_and(|path| same_bound_root(&path, root, folds_case))
            }),
            "Multiple or foreign editor workspaces are unsupported"
        );
    }
    ensure!(
        message["params"]["initializationOptions"]["logCfg"].is_null(),
        "Server logging overrides are unsupported by the bound editor gateway"
    );
    Ok(())
}

/// Commit a dependency graph only when its read is fenced by the same saved
/// fingerprint. A failed or obsolete read cannot partly replace live state.
fn reconcile_saved_inputs(workspace: &dyn Host, state: &mut State) -> Result<bool> {
    reconcile_saved_inputs_with_refresh(workspace, state, false)
}

fn reconcile_saved_inputs_with_refresh(
    workspace: &dyn Host,
    state: &mut State,
    refresh_graph: bool,
) -> Result<bool> {
    let stamp = workspace.source_stamp()?;
    if stamp == state.stamp && !refresh_graph {
        state.snapshot_pending = false;
        return Ok(false);
    }
    let mut next = state.clone();
    let changed = if refresh_graph {
        next.changed_inputs_with_refresh(stamp, true)?
    } else {
        next.changed_inputs(stamp)?
    };
    ensure_snapshot(stamp, workspace.source_stamp()?)?;
    next.snapshot_pending = false;
    *state = next;
    Ok(changed)
}

fn ensure_snapshot(before: [u8; 32], after: [u8; 32]) -> Result<()> {
    if before != after {
        return Err(SourceStampChanged::new(
            "Saved inputs changed while reading the editor dependency graph",
        )
        .into());
    }
    Ok(())
}

fn snapshot_or_pending<T>(
    result: Result<T>,
    state: &mut State,
    output: &mut impl Write,
) -> Result<Option<T>> {
    match result {
        Ok(value) => Ok(Some(value)),
        Err(error) if error.downcast_ref::<SourceStampChanged>().is_some() => {
            if !state.snapshot_pending {
                state.epoch += 1;
                state
                    .invalid
                    .extend(state.documents.values().filter(|d| d.local).map(|d| d.path.clone()));
            }
            state.snapshot_pending = true;
            for notification in state.pending_notifications() {
                write_message(output, &notification)?;
            }
            Ok(None)
        }
        Err(error) => Err(error),
    }
}

/// Session termination must remain responsive even while direct saves prevent
/// a stable snapshot. No proof or goal result is credited on this path.
fn prioritize_termination(events: &mut VecDeque<Event>) -> bool {
    let index = events.iter().position(|event| match event {
        Event::Client(Ok(Some(message))) => {
            matches!(message["method"].as_str(), Some("shutdown" | "exit"))
        }
        Event::Client(Ok(None) | Err(_)) => true,
        Event::Server(..) => false,
    });
    if let Some(index) = index {
        let event = events.remove(index).unwrap();
        events.push_front(event);
        true
    } else {
        false
    }
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
    let folds_case = workspace.folds_ascii_case()?;
    let mut state = loop {
        ensure!(!interrupted(), "Editor coordinator interrupted");
        let result: Result<State> = (|| {
            let stamp = workspace.source_stamp()?;
            let state =
                State::new(workspace.root().to_path_buf(), roots.clone(), stamp, folds_case)?;
            ensure_snapshot(stamp, workspace.source_stamp()?)?;
            Ok(state)
        })();
        match result {
            Ok(state) => break state,
            Err(error) if error.downcast_ref::<SourceStampChanged>().is_some() => {
                ensure!(
                    Instant::now() < deadline,
                    "Saved inputs kept changing; retry editor startup after saving completes"
                );
                thread::sleep(POLL);
            }
            Err(error) => return Err(error),
        }
    };
    let (sender, events) = mpsc::sync_channel(256);
    reader_thread(input, None, sender.clone());
    let mut server = Server::start(workspace, state.generation, sender.clone())?;
    let mut build: Option<Build> = None;
    let mut want_build = false;
    let mut hidden_initialize: Option<String> = None;
    let mut refreshing_documents = BTreeSet::new();
    let mut client_turns = 0;
    let mut checked_initial = false;
    let mut shutdown = false;
    let mut shutdown_id = None;
    let mut last_poll = Instant::now();
    let mut last_saved_poll = Instant::now();
    let mut last_snapshot_attempt = Instant::now();
    let mut client_events = VecDeque::new();
    let mut server_events = VecDeque::new();
    let mut external_writer = false;
    let mut initializing_writer = Some(startup);
    let mut initialization_deadline = Instant::now() + Duration::from_secs(60);
    'session: loop {
        ensure!(!interrupted(), "Editor coordinator interrupted");
        ensure!(
            shutdown
                || (state.initialized.is_some() && hidden_initialize.is_none())
                || Instant::now() < initialization_deadline,
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
            && !state.snapshot_pending
            && last_saved_poll.elapsed() < IDLE_SAVED_POLL
        {
            continue;
        }
        let terminating = prioritize_termination(&mut client_events);
        let owns_writer = build.is_some() || initializing_writer.is_some();
        let read_lock = if !owns_writer && !terminating && !shutdown {
            workspace.try_shared_lock()?
        } else {
            None
        };
        let writer_blocked = !owns_writer && !terminating && !shutdown && read_lock.is_none();
        if writer_blocked {
            if !external_writer {
                external_writer = true;
                state.refreshing = true;
                want_build = true;
                cancel_requests_with_waiters(&mut state, &mut output, true)?;
                server.process.stop();
                state.notifications_sent = 0;
                clear_closed_diagnostics(&mut state, &mut output)?;
                state.generation += 1;
                state.closed.clear();
                hidden_initialize = None;
                // A client registration can outlive this worker. Keep its
                // pending client reply so a replacement does not register the
                // same stable watcher ID a second time.
                state.server_requests.retain(|_, request| request.watcher.is_some());
                for notification in state.pending_notifications() {
                    write_message(&mut output, &notification)?;
                }
            }
            // Consume bounded turns against the retained live graph, without
            // reading mutable saved inputs or forwarding stopped-server claims.
            // Otherwise backpressure can hide shutdown behind a full queue.
        }
        if external_writer && !writer_blocked {
            state
                .invalid
                .extend(state.documents.values().filter(|d| d.local).map(|d| d.path.clone()));
            want_build = true;
        }
        // Live updates get bounded client turns. Before a server turn, queued
        // updates are checked too, so an unapplied didChange cannot credit an
        // old result while server and build work continue to make progress.
        // A failed snapshot still consumes safe bounded live turns. Retry the
        // disk read with backoff while withholding every unadmitted claim.
        if !terminating
            && !shutdown
            && !writer_blocked
            && (!client_events.is_empty()
                || !server_events.is_empty()
                || state.snapshot_pending
                || build.is_some()
                || external_writer
                || last_saved_poll.elapsed() >= IDLE_SAVED_POLL)
            && (!state.snapshot_pending || last_snapshot_attempt.elapsed() >= POLL)
        {
            // Suspended live overlays did not probe private outputs. Re-read
            // their graph under this lease even if saved source is unchanged.
            // Keep this obligation across typed races until a snapshot commits.
            last_snapshot_attempt = Instant::now();
            let refresh_graph = external_writer || state.snapshot_pending;
            let result = reconcile_saved_inputs_with_refresh(workspace, &mut state, refresh_graph);
            if let Some(changed) = snapshot_or_pending(result, &mut state, &mut output)? {
                last_saved_poll = Instant::now();
                external_writer = false;
                want_build |= changed;
            } else {
                want_build = true;
            }
        }
        // A fingerprint read can outlast new client traffic. Refresh this
        // bounded queue before dequeue so shutdown/exit/EOF that arrived during
        // the read can still overtake an ordinary turn or mapped server reply.
        queue_events(None, &events, &mut client_events, &mut server_events);
        let terminating = prioritize_termination(&mut client_events);
        if build.as_ref().is_some_and(|active| active.stamp != state.stamp) {
            // A saved edit preempts compilation even if its child never exits.
            // Stop/reap the entire process group before releasing its writer;
            // aborted preparations deliberately never receive a finish marker.
            let mut obsolete = build.take().unwrap();
            obsolete.stop();
            drop(obsolete);
            want_build = true;
            // Reacquire a lease after releasing this writer before any event
            // can use the snapshot or a replacement build starts.
            continue;
        }
        let event = if state.snapshot_pending {
            // Keep initialization replies bounded in the same queue. They must
            // not release their writer/replay buffers against an unstable graph.
            let index = server_events.iter().position(|event| {
                let Event::Server(generation, Ok(Some(message))) = event else { return true };
                if *generation != state.generation || message.get("method").is_some() {
                    return true;
                }
                let Some(id) = message["id"].as_str() else { return true };
                hidden_initialize.as_deref() != Some(id)
                    && state.requests.get(id).is_none_or(|r| r.method != "initialize")
            });
            next_event_at(
                &mut client_events,
                &mut server_events,
                &mut client_turns,
                terminating,
                index,
            )
        } else {
            next_event(&mut client_events, &mut server_events, &mut client_turns, terminating)
        };
        let progressed = event.is_some();
        'handle_event: {
            let Some(event) = event else {
                break 'handle_event;
            };
            match event {
                Event::Client(message) => {
                    let Some(mut message) = message? else {
                        break 'session;
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
                        break 'session;
                    }
                    if method == "shutdown" {
                        shutdown = true;
                        build = None;
                        let uninitialized =
                            hidden_initialize.is_some() || state.initialized.is_none();
                        if uninitialized {
                            server.process.stop();
                            hidden_initialize = None;
                        }
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
                        break 'handle_event;
                    }
                    // A prioritized shutdown may overtake a reply to an already
                    // issued server request. The live server still needs those
                    // mapped replies to finish shutdown; no new work is admitted.
                    if method.is_empty() {
                        if let Some(id) = message["id"].as_str() {
                            if let Some(request) = state.server_requests.remove(id) {
                                if let Some(watcher) = request.watcher {
                                    if message.get("result").is_some()
                                        && message.get("error").is_none()
                                    {
                                        state.registered_watcher = Some(watcher);
                                    }
                                }
                                if request.generation == state.generation && !server.process.stopped
                                {
                                    message["id"] = request.original;
                                    server.send(&message)?;
                                }
                            }
                        }
                        break 'handle_event;
                    }
                    if shutdown {
                        break 'handle_event;
                    }
                    ensure!(
                        method != "workspace/didChangeWorkspaceFolders",
                        "Dynamic editor workspace folders are unsupported by the bound root"
                    );
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
                            if source_relative_path(&path, workspace.root(), folds_case).is_some() {
                                false
                            } else if writer_blocked || state.snapshot_pending {
                                workspace.contains_immutable_sdk_source(&path)?
                            } else {
                                workspace.contains_source(&path)?
                            }
                        } else {
                            false
                        };
                        want_build |= if writer_blocked || state.snapshot_pending {
                            state.update_document_with_outputs(&message, allow_shared, false)?
                        } else {
                            state.update_document(&message, allow_shared)?
                        };
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
                            && (server.process.stopped
                                || hidden_initialize.is_some()
                                || state.snapshot_pending)
                        {
                            // This close will be retained for replay, so no live
                            // file worker will receive it to send the clear.
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
                        // Hidden initialization or a pending snapshot retains
                        // these live updates for the coherent didOpen replay.
                        if hidden_initialize.is_none() && !state.snapshot_pending {
                            server.send(&message)?;
                        }
                    } else if method == "initialized" {
                        state.initialized = Some(message.clone());
                        server.send(&message)?;
                        initializing_writer = None;
                    } else if method == "$/cancelRequest" {
                        let original = &message["params"]["id"];
                        if let Some((key, request)) =
                            state.requests.iter().find(|(_, r)| &r.original == original)
                        {
                            let key = key.clone();
                            if request.wait.as_ref().is_some_and(|w| w.snapshot.is_none()) {
                                let request = state.requests.remove(&key).unwrap();
                                write_message(
                                    &mut output,
                                    &json!({"jsonrpc":"2.0","id":request.original,
                                    "error":{"code":-32800,"message":"Synchronization request cancelled"}}),
                                )?;
                            } else {
                                message["params"]["id"] = json!(key);
                                server.send(&message)?;
                            }
                        }
                    } else if let Some(id) = message.get("id").cloned() {
                        if method == "initialize" {
                            ensure!(state.initialize.is_none(), "Duplicate editor initialization");
                            validate_initialize(&message, &state.root, state.inputs.folds_case)?;
                            state.initialize = Some(message.clone());
                        }
                        let uri = uri_of(&message);
                        let version = uri
                            .as_ref()
                            .and_then(|uri| state.documents.get(uri).map(|d| d.version));
                        let wait = if matches!(
                            method.as_str(),
                            "textDocument/waitForDiagnostics" | "$/lean/waitForILeans"
                        ) {
                            uri.as_ref().filter(|uri| state.documents.contains_key(*uri)).and_then(
                                |_| {
                                    message["params"]["version"]
                                        .as_i64()
                                        .filter(|version| *version >= 0)
                                        .map(|minimum| VersionWait {
                                            minimum,
                                            message: message.clone(),
                                            snapshot: None,
                                            ileans: method == "$/lean/waitForILeans",
                                            diagnostics_barrier: false,
                                        })
                                },
                            )
                        } else {
                            None
                        };
                        let snapshot = uri.as_deref().and_then(|uri| state.request_snapshot(uri));
                        let request = Request {
                            original: id.clone(),
                            epoch: state.epoch,
                            uri,
                            version,
                            method: method.clone(),
                            wait,
                            snapshot,
                        };
                        if method != "initialize"
                            && (!state.request_current(&request)
                                || (request.wait.is_none() && hidden_initialize.is_some()))
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
                            let waiting = request.wait.is_some();
                            state.requests.insert(key, request);
                            if !waiting {
                                server.send(&message)?;
                            }
                        }
                    } else {
                        if process_scoped_notification(&method) {
                            // Forward live RPC/progress notifications and file
                            // watcher hints without retaining them for another
                            // generation. A replacement reads current files.
                            if hidden_initialize.is_none() && !server.process.stopped {
                                server.send(&message)?;
                            }
                        } else {
                            state.remember_notification(&message)?;
                            if hidden_initialize.is_none()
                                && !state.snapshot_pending
                                && !server.process.stopped
                            {
                                for notification in &state.notifications[state.notifications_sent..]
                                {
                                    server.send(notification)?;
                                }
                                state.notifications_sent = state.notifications.len();
                            }
                        }
                    }
                }
                Event::Server(generation, message) => {
                    if generation != state.generation || (shutdown && server.process.stopped) {
                        break 'handle_event;
                    }
                    let Some(mut message) = message? else {
                        bail!("Bound Lean server exited unexpectedly");
                    };
                    // Ordinary claims consumed during a snapshot race remain
                    // ineligible below. Initialization replies are held in the
                    // bounded queue until their saved-state check succeeds.
                    if message["id"] == json!("anneal-shutdown") {
                        if let Some(id) = shutdown_id.take() {
                            message["id"] = id;
                            write_message(&mut output, &message)?;
                        }
                        break 'handle_event;
                    }
                    if shutdown && !(message["method"].is_string() && message.get("id").is_some()) {
                        break 'handle_event;
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
                        let obsolete = !refreshing_documents.is_disjoint(&state.invalid);
                        want_build |= obsolete;
                        if let Some(initialized) = &state.initialized {
                            server.send(initialized)?;
                        }
                        for notification in &state.notifications {
                            server.send(notification)?;
                        }
                        state.notifications_sent = state.notifications.len();
                        for (uri, doc) in &state.documents {
                            server.send(&json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{
                                "textDocument":{"uri":uri,"languageId":doc.language,"version":doc.version,"text":doc.text},
                                "dependencyBuildMode":"never"}}))?;
                        }
                        state.refreshing = false;
                        let blocked: BTreeSet<_> = state
                            .documents
                            .keys()
                            .filter(|uri| state.blocked(uri))
                            .cloned()
                            .collect();
                        state.published_pending.retain(|uri, _| blocked.contains(uri));
                        refreshing_documents.clear();
                        initializing_writer = None;
                        break 'handle_event;
                    }
                    if message.get("method").is_none() {
                        let Some(key) = message["id"].as_str() else {
                            break 'handle_event;
                        };
                        let Some(mut request) = state.requests.remove(key) else {
                            break 'handle_event;
                        };
                        let current = state.request_current(&request)
                            && !queued_document_update(
                                &client_events,
                                &state,
                                request.uri.as_deref(),
                            );
                        if current
                            && message.get("error").is_none()
                            && request.wait.as_ref().is_some_and(|w| w.diagnostics_barrier)
                        {
                            let wait = request.wait.as_mut().unwrap();
                            wait.diagnostics_barrier = false;
                            state.serial += 1;
                            let key =
                                format!("anneal-client-{}-{}", state.generation, state.serial);
                            let mut ileans = wait.message.clone();
                            ileans["id"] = json!(key);
                            state.requests.insert(key, request);
                            server.send(&ileans)?;
                            break 'handle_event;
                        }
                        message["id"] = request.original.clone();
                        if request.method != "initialize" && !current {
                            message = error(
                                request.original,
                                "Obsolete document or imported input response",
                            );
                        }
                        write_message(&mut output, &message)?;
                    } else if message.get("id").is_some() {
                        if message["method"] == "workspace/applyEdit"
                            && (shutdown || stale_workspace_edit(&client_events, &state))
                        {
                            server.send(&json!({"jsonrpc":"2.0","id":message["id"],
                                "result":{"applied":false,"failureReason":"Document or imported inputs changed"}}))?;
                            break 'handle_event;
                        }
                        let watcher = lean_watcher_registration(&message);
                        if let Some(registration) = &watcher {
                            let accepted = state.registered_watcher.as_ref();
                            let pending = state
                                .server_requests
                                .values_mut()
                                .find(|request| request.watcher.is_some());
                            if accepted.is_some_and(|current| current == registration) {
                                server.send(&json!({"jsonrpc":"2.0","id":message["id"],
                                    "result":null}))?;
                                break 'handle_event;
                            }
                            if let Some(request) = pending {
                                if request.watcher.as_ref() == Some(registration) {
                                    request.original = message["id"].clone();
                                    request.generation = state.generation;
                                    break 'handle_event;
                                }
                            }
                            if accepted.is_some()
                                || state
                                    .server_requests
                                    .values()
                                    .any(|request| request.watcher.is_some())
                            {
                                server.send(&json!({"jsonrpc":"2.0","id":message["id"],
                                    "error":{"code":-32602,"message":"Conflicting Lean watcher registration"}}))?;
                                break 'handle_event;
                            }
                        }
                        // Server request IDs are generation-scoped too. Replies
                        // to a dead generation are ignored; the watcher has
                        // client-scoped identity and retains its pending reply.
                        state.serial += 1;
                        let key = format!("anneal-server-{}-{}", state.generation, state.serial);
                        state.server_requests.insert(
                            key.clone(),
                            ServerRequest {
                                original: message["id"].clone(),
                                generation: state.generation,
                                watcher,
                            },
                        );
                        message["id"] = json!(key);
                        write_message(&mut output, &message)?;
                    } else {
                        let uri = uri_of(&message);
                        let method = message["method"].as_str().unwrap_or("");
                        let closed_clear = state.take_closed_diagnostics(&message);
                        if !closed_clear
                            && method != "window/logMessage"
                            && queued_document_update(&client_events, &state, uri.as_deref())
                        {
                            break 'handle_event;
                        }
                        if !closed_clear && !current_versioned_notification(&state, &message) {
                            break 'handle_event;
                        }
                        if let Some(uri) = &uri {
                            if !closed_clear && state.blocked(uri) {
                                break 'handle_event;
                            }
                        } else if (state.refreshing || state.snapshot_pending)
                            && method != "window/logMessage"
                        {
                            break 'handle_event;
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
            let dispatched = request.wait.as_ref().is_none_or(|wait| wait.snapshot.is_some());
            write_message(
                &mut output,
                &error(request.original, "Document or imported inputs changed"),
            )?;
            if dispatched {
                server.send(
                    &json!({"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":key}}),
                )?;
            }
        }
        if !shutdown && last_poll.elapsed() >= POLL {
            for notification in state.pending_notifications() {
                write_message(&mut output, &notification)?;
            }
            last_poll = Instant::now();
        }
        if let Some(active) = build.as_mut().filter(|_| !state.snapshot_pending) {
            if let Some(outcome) = active.poll()? {
                let result = reconcile_saved_inputs(workspace, &mut state);
                let Some(_) = snapshot_or_pending(result, &mut state, &mut output)? else {
                    want_build = true;
                    thread::sleep(POLL);
                    continue;
                };
                let stamp = state.stamp;
                last_saved_poll = Instant::now();
                let obsolete = active.stamp != stamp;
                let complete = !outcome.failed && !obsolete;
                if complete {
                    let result = active
                        .preparation
                        .as_ref()
                        .map_or(Ok(()), |prepared| workspace.finish_local_outputs(prepared));
                    let Some(()) = snapshot_or_pending(result, &mut state, &mut output)? else {
                        want_build = true;
                        thread::sleep(POLL);
                        continue;
                    };
                    if active.had_commands {
                        state.outputs_uncommitted = false;
                    }
                }
                let covered = if !obsolete {
                    state.matching_documents(&outcome.covered)
                } else {
                    BTreeSet::new()
                };
                if !obsolete {
                    for path in &covered {
                        state.failed_inputs.remove(path);
                    }
                    if outcome.failed {
                        for (path, input) in &outcome.attempted {
                            if !covered.contains(path)
                                && state.documents.values().any(|doc| {
                                    &doc.path == path
                                        && state.refresh_input(doc).as_ref() == Some(input)
                                })
                            {
                                state.failed_inputs.insert(path.clone(), input.clone());
                            }
                        }
                    }
                }
                let finished = build.take().unwrap();
                if outcome.failed && !obsolete {
                    eprintln!(
                        "Anneal: local build failed; dependent editor results remain pending"
                    );
                }
                if !obsolete && state.initialize.is_some() && state.initialized.is_some() {
                    // A failed batch leaves its importers pending. Independently
                    // compiled documents and source-only diagnostics still get
                    // a fresh worker in this generation. Cycles stay blocked;
                    // their graph-derived error is published by the coordinator.
                    let mut refreshed = covered.clone();
                    if outcome.failed {
                        refreshed.extend(state.own_diagnostic_documents());
                    }
                    initializing_writer = Some(finished._writer);
                    initialization_deadline = Instant::now() + Duration::from_secs(60);
                    drop(finished.process);
                    checked_initial = true;
                    state.invalid.retain(|path| !refreshed.contains(path));
                    refreshing_documents = refreshed;
                    state.refreshing = true;
                    cancel_requests_with_waiters(&mut state, &mut output, true)?;
                    state.server_requests.retain(|_, request| request.watcher.is_some());
                    clear_closed_diagnostics(&mut state, &mut output)?;
                    state.generation += 1;
                    state.notifications_sent = 0;
                    state.closed.clear();
                    server.process.stop();
                    server = Server::start(workspace, state.generation, sender.clone())?;
                    let key = format!("anneal-initialize-{}", state.generation);
                    let mut initialize = state.initialize.clone().unwrap();
                    initialize["id"] = json!(key);
                    server.send(&initialize)?;
                    hidden_initialize = Some(key);
                    want_build = !state.build_documents(false).is_empty();
                } else {
                    // The obsolete build cannot credit any coverage or output
                    // provenance. Retry only against a newly admitted stamp.
                    want_build = true;
                }
            }
        }
        drop(read_lock);
        if want_build
            && !shutdown
            && !writer_blocked
            && !state.snapshot_pending
            && build.is_none()
            && state.initialized.is_some()
            && hidden_initialize.is_none()
        {
            let mut documents = state.build_documents(!checked_initial);
            if state.outputs_uncommitted && (!documents.is_empty() || server.process.stopped) {
                // The next nonempty preparation will discard every unmarked
                // private output. Rebuild all eligible open consumers before
                // replaying any of them into the replacement worker.
                documents = state.build_documents(true);
            }
            if !documents.is_empty() || server.process.stopped {
                if let Some(writer) = workspace.try_writer_lock()? {
                    let result = (|| {
                        let batches = build_commands(workspace, &state, &documents)?;
                        let has_commands = batches.iter().any(|batch| !batch.commands.is_empty());
                        let preparation = if has_commands {
                            // A failed or interrupted preparation cannot
                            // certify any outputs until a complete later build.
                            state.outputs_uncommitted = true;
                            workspace.prepare_local_outputs()?
                        } else {
                            None
                        };
                        if let Some(prepared) = &preparation {
                            ensure_snapshot(state.stamp, prepared.stamp())?;
                        }
                        let stamp = workspace.source_stamp()?;
                        ensure_snapshot(state.stamp, stamp)?;
                        Ok((batches, stamp, preparation))
                    })();
                    let Some((batches, stamp, preparation)) =
                        snapshot_or_pending(result, &mut state, &mut output)?
                    else {
                        thread::sleep(POLL);
                        continue;
                    };
                    build = Some(Build::spawn(batches, documents, stamp, preparation, writer)?);
                    want_build = false;
                }
            } else {
                // A live worker can remain pending for dirty/missing closures.
                // A stopped worker takes the lease-held zero-command refresh
                // above, including an idle session with no open documents.
                want_build = false;
            }
        }
        if state.notifications_sent < state.notifications.len()
            && !shutdown
            && !writer_blocked
            && !state.snapshot_pending
            && !state.refreshing
            && !want_build
            && build.is_none()
            && hidden_initialize.is_none()
            && !server.process.stopped
        {
            for notification in &state.notifications[state.notifications_sent..] {
                server.send(notification)?;
            }
            state.notifications_sent = state.notifications.len();
        }
        if !shutdown && !writer_blocked && !state.snapshot_pending {
            dispatch_version_waits(&mut state, &mut server)?;
        }
        if state.snapshot_pending && !progressed {
            thread::sleep(POLL);
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
            snapshot: state.request_snapshot(&client),
            uri: Some(client),
            version: Some(1),
            method: "$/lean/plainGoal".into(),
            wait: None,
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

    #[test]
    fn bounded_client_turns_preserve_server_progress_and_termination_priority() {
        let mut clients = VecDeque::new();
        let mut servers = VecDeque::new();
        for index in 0..64 {
            clients.push_back(Event::Client(Ok(Some(json!({"index":index})))));
        }
        for index in 0..3 {
            servers.push_back(Event::Server(0, Ok(Some(json!({"index":index})))));
        }
        let mut turns = 0;
        let mut server_index = 0;
        let mut client_count = 0;
        for _ in 0..3 * (MAX_CLIENT_TURNS + 1) {
            match next_event(&mut clients, &mut servers, &mut turns, false).unwrap() {
                Event::Client(_) => client_count += 1,
                Event::Server(_, Ok(Some(message))) => {
                    assert_eq!(client_count, MAX_CLIENT_TURNS);
                    assert_eq!(message["index"], server_index);
                    server_index += 1;
                    client_count = 0;
                }
                _ => panic!("Unexpected scheduler event"),
            }
            // A sustained producer replenishes each consumed client event.
            clients.push_back(Event::Client(Ok(Some(json!({"method":"$/setTrace"})))));
        }
        assert_eq!(server_index, 3);
        assert!(!clients.is_empty());
        clients.push_back(Event::Client(Ok(Some(json!({"method":"shutdown"})))));
        servers.push_back(Event::Server(0, Ok(Some(json!({"result":true})))));
        assert!(prioritize_termination(&mut clients));
        turns = MAX_CLIENT_TURNS;
        assert!(matches!(next_event(&mut clients, &mut servers, &mut turns, true),
            Some(Event::Client(Ok(Some(message)))) if message["method"] == "shutdown"));
    }

    #[test]
    fn held_initialization_reply_does_not_block_live_or_termination_turns() {
        let mut clients =
            VecDeque::from([Event::Client(Ok(Some(json!({"method":"textDocument/didChange"}))))]);
        let mut servers = VecDeque::from([
            Event::Server(2, Ok(Some(json!({"id":"anneal-initialize-2","result":{}})))),
            Event::Server(2, Ok(Some(json!({"method":"textDocument/publishDiagnostics"})))),
        ]);
        let mut turns = MAX_CLIENT_TURNS;
        assert!(matches!(next_event_at(&mut clients, &mut servers, &mut turns, false, Some(1)),
            Some(Event::Server(_, Ok(Some(message)))) if message["method"] == "textDocument/publishDiagnostics"));
        assert_eq!(servers.len(), 1, "Deferred initialize response left its bounded queue");
        assert!(matches!(
            next_event_at(&mut clients, &mut servers, &mut turns, false, None),
            Some(Event::Client(_))
        ));
        clients.push_back(Event::Client(Ok(Some(json!({"method":"shutdown"})))));
        assert!(prioritize_termination(&mut clients));
        assert!(matches!(next_event_at(&mut clients, &mut servers, &mut turns, true, None),
            Some(Event::Client(Ok(Some(message)))) if message["method"] == "shutdown"));
        assert_eq!(servers.len(), 1);
    }

    #[test]
    fn traffic_arriving_during_snapshot_read_refreshes_termination_priority() {
        let reply = json!({"jsonrpc":"2.0","id":"anneal-server-2-7","result":[]});
        let mut clients = VecDeque::from([Event::Client(Ok(Some(reply.clone())))]);
        let mut servers = VecDeque::new();
        let (sender, events) = mpsc::sync_channel(1);
        assert!(!prioritize_termination(&mut clients));
        // The completed send establishes that shutdown arrived after the first
        // priority check, as it can during an in-flight snapshot read.
        sender.send(Event::Client(Ok(Some(json!({"method":"shutdown"}))))).unwrap();
        queue_events(None, &events, &mut clients, &mut servers);
        let terminating = prioritize_termination(&mut clients);
        assert!(terminating);
        let mut turns = 0;
        assert!(matches!(next_event_at(&mut clients, &mut servers, &mut turns, terminating, None),
            Some(Event::Client(Ok(Some(message)))) if message["method"] == "shutdown"));
        assert!(
            matches!(clients.pop_front(), Some(Event::Client(Ok(Some(message)))) if message == reply),
            "Termination priority dropped the outstanding server-request reply"
        );
    }

    #[test]
    fn queued_dependency_edits_withhold_affected_claims_but_allow_independent_turns() {
        let (dir, mut state, local, client) = fixture();
        open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
        open(&mut state, &local, "def value := 10\n");
        let independent = format!("file://{}", dir.path().join("Independent.lean").display());
        open(&mut state, &independent, "example : True := by trivial\n");
        let events = VecDeque::from([Event::Client(Ok(Some(
            json!({"method":"textDocument/didChange",
            "params":{"textDocument":{"uri":local,"version":2},"contentChanges":[{"text":"def value := 20\n"}]}}),
        )))]);
        assert!(queued_document_update(&events, &state, Some(&client)));
        assert!(queued_document_update(&events, &state, Some(&local)));
        assert!(!queued_document_update(&events, &state, Some(&independent)));
        assert!(queued_document_update(&events, &state, None));
        assert_eq!(state.documents[&local].version, 1);
        for unopened in [
            format!("file://{}", dir.path().join("Unrelated.lean").display()),
            "file:///immutable-sdk/Unrelated.lean".into(),
        ] {
            let events = VecDeque::from([Event::Client(Ok(Some(
                json!({"method":"textDocument/didOpen",
                "params":{"textDocument":{"uri":unopened,"version":1,"text":"example : True := by trivial\n"}}}),
            )))]);
            assert!(
                queued_document_update(&events, &state, Some(&client)),
                "A queued open may add a currently unknown provider"
            );
        }
        state.documents.remove(&local);
        assert!(
            queued_document_update(&events, &state, Some(&client)),
            "An unopened known provider still belongs to the importer's dependency scope"
        );
        let malformed =
            VecDeque::from([Event::Client(Ok(Some(json!({"method":"textDocument/didOpen",
            "params":{"textDocument":{"uri":"untargetable","version":1}}}))))]);
        assert!(queued_document_update(&malformed, &state, Some(&client)));
    }

    #[test]
    fn queued_unsaved_provider_open_withholds_claim_at_fairness_boundary() {
        let (dir, mut state, _, client) = fixture();
        open(&mut state, &client, "import Foo\nexample : True := by trivial\n");
        let foo_path = dir.path().join("Foo.lean");
        assert!(!state.inputs.dependencies(&state.documents[&client].path).contains(&foo_path));
        assert!(!state.blocked(&client));

        let foo = format!("file://{}", foo_path.display());
        let open_foo = json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{
            "textDocument":{"uri":foo,"languageId":"lean4","version":1,"text":"def foo := 1\n"}}});
        let mut clients = (0..MAX_CLIENT_TURNS)
            .map(|_| Event::Client(Ok(Some(json!({"method":"$/setTrace"})))))
            .collect::<VecDeque<_>>();
        clients.push_back(Event::Client(Ok(Some(open_foo))));
        let mut servers = VecDeque::from([Event::Server(
            state.generation,
            Ok(Some(json!({"jsonrpc":"2.0","id":"old-goal","result":"stale"}))),
        )]);
        let mut turns = 0;
        for _ in 0..MAX_CLIENT_TURNS {
            assert!(matches!(
                next_event(&mut clients, &mut servers, &mut turns, false),
                Some(Event::Client(_))
            ));
        }
        assert!(matches!(
            next_event(&mut clients, &mut servers, &mut turns, false),
            Some(Event::Server(_, _))
        ));
        assert!(
            queued_document_update(&clients, &state, Some(&client)),
            "A fairness turn must not forward the old goal or diagnostics"
        );
        let Some(Event::Client(Ok(Some(open_foo)))) = clients.pop_front() else {
            panic!("Queued provider open was lost");
        };
        state.update_document(&open_foo, false).unwrap();
        assert!(state.blocked(&client));
    }

    #[test]
    fn workspace_edit_fence_uses_queued_updates_and_blocked_inputs() {
        let (_dir, mut state, _, client) = fixture();
        open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
        let ordinary = VecDeque::from([Event::Client(Ok(Some(json!({
            "method":"$/setTrace","params":{"value":"messages"}
        }))))]);
        assert!(!stale_workspace_edit(&ordinary, &state));
        let queued = VecDeque::from([Event::Client(Ok(Some(json!({
            "method":"textDocument/didChange","params":{"textDocument":{"uri":client,"version":2},
            "contentChanges":[{"text":"import Middle\nexample : True := by trivial\n"}]}
        }))))]);
        assert!(stale_workspace_edit(&queued, &state));
        let empty = VecDeque::new();
        state.invalid.insert(state.documents[&client].path.clone());
        assert!(stale_workspace_edit(&empty, &state));
    }

    #[test]
    fn independent_refresh_coverage_ignores_unrelated_typing_and_preserves_dirty_pending() {
        let (dir, mut state, local, client) = fixture();
        fs::write(dir.path().join("Other.lean"), "def other := 10\n").unwrap();
        fs::write(
            dir.path().join("OtherClient.lean"),
            "import Other\nexample : other = 10 := by decide\n",
        )
        .unwrap();
        open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
        open(&mut state, &local, "def value := 20\n");
        let other = format!("file://{}", dir.path().join("OtherClient.lean").display());
        open(&mut state, &other, "import Other\nexample : other = 10 := by decide\n");
        state.changed_inputs([1; 32]).unwrap();
        let covered = state.build_documents(false);
        assert!(!covered.contains_key(&state.documents[&client].path));
        assert!(covered.contains_key(&state.documents[&other].path));
        state.update_document(&json!({"method":"textDocument/didChange","params":{"textDocument":{"uri":local,"version":2},
            "contentChanges":[{"text":"def value := 30\n-- still unsaved\n"}]}}), false).unwrap();
        let matching = state.matching_documents(&covered);
        assert!(matching.contains(&state.documents[&other].path));
        state.invalid.retain(|path| !matching.contains(path));
        assert!(state.blocked(&client));
        assert!(!state.blocked(&other));
        assert!(state.build_documents(false).is_empty());
    }

    #[test]
    fn simultaneous_lean_and_configuration_stamp_change_invalidates_independent_documents() {
        let (dir, mut state, _, client) = fixture();
        open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
        let independent = format!("file://{}", dir.path().join("Independent.lean").display());
        open(&mut state, &independent, "example : True := by trivial\n");
        let request = Request {
            original: json!(90),
            epoch: state.epoch,
            snapshot: state.request_snapshot(&independent),
            uri: Some(independent.clone()),
            version: Some(1),
            method: "$/lean/plainGoal".into(),
            wait: None,
        };
        assert!(state.request_current(&request));
        fs::write(dir.path().join("Local.lean"), "def value := 20\n").unwrap();
        fs::write(dir.path().join(".anneal-lake.json"), "{\"libraries\":[\"Changed\"]}\n").unwrap();
        state.changed_inputs([1; 32]).unwrap();
        assert!(state.blocked(&client));
        assert!(state.blocked(&independent));
        assert!(!state.request_current(&request));
        assert_eq!(state.documents[&independent].version, 1);
    }

    #[test]
    fn document_requests_scope_live_edits_but_keep_saved_and_generation_fences() {
        let (dir, mut state, local, client) = fixture();
        open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
        let request = Request {
            original: json!(91),
            epoch: state.epoch,
            snapshot: state.request_snapshot(&client),
            uri: Some(client.clone()),
            version: Some(1),
            method: "$/lean/plainGoal".into(),
            wait: None,
        };
        let session_request =
            Request { uri: None, version: None, snapshot: None, ..request.clone() };
        let independent = format!("file://{}", dir.path().join("Independent.lean").display());
        open(&mut state, &independent, "example : True := by trivial\n");
        state.update_document(&json!({"method":"textDocument/didChange","params":{"textDocument":{"uri":independent,"version":2},
            "contentChanges":[{"text":"example : True := by trivial\n-- live edit\n"}]}}), false).unwrap();
        state.update_document(&json!({"method":"textDocument/didSave","params":{"textDocument":{"uri":independent}}}), false).unwrap();
        state.update_document(&json!({"method":"textDocument/didClose","params":{"textDocument":{"uri":independent}}}), false).unwrap();
        assert!(state.epoch > request.epoch);
        assert!(
            state.request_current(&request),
            "Unrelated live edits invalidated the importer's request"
        );
        assert!(
            !state.request_current(&session_request),
            "No-URI request lost its conservative epoch fence"
        );
        let clean = state.clone();
        open(&mut state, &local, "def value := 20\n");
        assert!(state.blocked(&client));
        assert!(
            !state.request_current(&request),
            "Dirty transitive input kept an old request current"
        );
        state = clean.clone();
        state.generation += 1;
        assert!(!state.request_current(&request));
        state = clean.clone();
        state.stamp = [1; 32];
        assert!(!state.request_current(&request));
        state = clean;
        state.update_document(&json!({"method":"textDocument/didChange","params":{"textDocument":{"uri":client,"version":2},
            "contentChanges":[{"text":"import Middle\nexample : True := by trivial\n"}]}}), false).unwrap();
        assert!(!state.request_current(&request), "Own version change kept an old request current");
    }

    #[test]
    fn initialization_root_paths_remain_bound_for_legacy_and_modern_clients() {
        let root = Path::new("/tmp/bound workspace");
        for params in [
            json!({"rootPath":"/tmp/bound workspace"}),
            json!({"rootPath":"/tmp/bound workspace/.","rootUri":null,"workspaceFolders":null}),
            json!({"rootPath":null,"rootUri":"file:///tmp/bound%20workspace"}),
            json!({}),
        ] {
            assert!(validate_initialize(&json!({"params":params}), root, false).is_ok());
        }
        for params in [
            json!({"rootPath":"/tmp/foreign"}),
            json!({"rootPath":"relative"}),
            json!({"rootPath":"/tmp/foreign","rootUri":"file:///tmp/bound%20workspace"}),
            json!({"rootPath":"/tmp/bound workspace/../foreign"}),
            json!({"rootPath":42}),
        ] {
            assert!(validate_initialize(&json!({"params":params}), root, false).is_err());
        }
        for params in [
            json!({"rootUri":"file:///TMP/BOUND%20WORKSPACE"}),
            json!({"rootPath":"/TMP/Bound Workspace/.",
                "workspaceFolders":[{"uri":"file:///tmp/BOUND%20workspace","name":"bound"}]}),
        ] {
            assert!(validate_initialize(&json!({"params":params}), root, true).is_ok());
            assert!(validate_initialize(&json!({"params":params}), root, false).is_err());
        }
        for params in [
            json!({"rootUri":"file:///TMP/BOUND%20WORKSPACE/other"}),
            json!({"rootUri":"file:///TMP/BOUND%20WORKSPACE-other"}),
            json!({"workspaceFolders":[{"uri":"file:///tmp/foreign","name":"foreign"}]}),
        ] {
            assert!(validate_initialize(&json!({"params":params}), root, true).is_err());
        }
    }

    #[test]
    fn ilean_notifications_need_an_identified_current_document_version() {
        for method in ["$/lean/ileanInfoUpdate", "$/lean/ileanInfoFinal"] {
            let (_dir, mut state, local, _) = fixture();
            open(&mut state, &local, "def value := 10\n");
            let current = json!({"method":method,"params":{"uri":local,"version":1}});
            assert!(current_versioned_notification(&state, &current));
            let unscoped = json!({"method":method,"params":{"version":1}});
            assert!(!current_versioned_notification(&state, &unscoped));
            state
                .update_document(
                    &json!({"method":"textDocument/didChange","params":{
                "textDocument":{"uri":local,"version":2},
                "contentChanges":[{"text":"def value := 11\n"}]}}),
                    false,
                )
                .unwrap();
            assert!(!current_versioned_notification(&state, &current));
            let new = json!({"method":method,"params":{"uri":local,"version":2}});
            assert!(current_versioned_notification(&state, &new));
        }
    }

    #[test]
    fn module_keys_follow_case_probe_and_keep_provider_spelling_for_builds() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().to_path_buf();
        fs::write(root.join("foo.lean"), "def value := 10\n").unwrap();
        fs::write(root.join("Client.lean"), "import Foo\nexample : value = 10 := by decide\n")
            .unwrap();
        let client = format!("file://{}", root.join("Client.lean").display());
        let mut folded = State::new(root.clone(), vec![root.clone()], [0; 32], true).unwrap();
        open(&mut folded, &client, "import Foo\nexample : value = 10 := by decide\n");
        assert_eq!(folded.inputs.modules["foo"], root.join("foo.lean"));
        assert_eq!(folded.inputs.module_names["foo"], "foo");
        assert!(
            folded.inputs.dependencies(&root.join("Client.lean")).contains(&root.join("foo.lean"))
        );
        fs::write(root.join("foo.lean"), "def value := 20\n").unwrap();
        assert!(folded.changed_inputs([1; 32]).unwrap());
        assert!(folded.blocked(&client));
        let exact = State::new(root.clone(), vec![root.clone()], [0; 32], false).unwrap();
        assert!(exact.inputs.dependencies(&root.join("Client.lean")).is_empty());
        assert!(exact.inputs.modules.contains_key("foo"));
        assert!(!exact.inputs.modules.contains_key("Foo"));
    }

    #[test]
    fn live_only_providers_cover_all_overlapping_roots_and_reject_ambiguity() {
        for reversed in [false, true] {
            let dir = tempfile::tempdir().unwrap();
            let root = dir.path().to_owned();
            fs::create_dir(root.join("src")).unwrap();
            let mut roots = vec![root.clone(), root.join("src")];
            if reversed {
                roots.reverse();
            }
            let mut state = State::new(root.clone(), roots.clone(), [0; 32], false).unwrap();
            let provider = root.join("src/Foo.lean");
            let uri = format!("file://{}", provider.display());
            open(&mut state, &uri, "def foo := 10\n");
            for module in ["Foo", "src.Foo"] {
                assert_eq!(state.inputs.modules[module], provider);
                let path = root.join(format!("Client{}.lean", module.replace('.', "_")));
                let client = format!("file://{}", path.display());
                open(
                    &mut state,
                    &client,
                    &format!("import {module}\nexample : True := by trivial\n"),
                );
                assert!(state.inputs.dependencies(&path).contains(&provider));
                assert!(state.blocked(&client), "Missing live provider {module} was accepted");
                assert!(state.refresh_input(&state.documents[&client]).is_none());
            }
            let mut repeated = roots;
            repeated.push(root.join("src"));
            state.inputs.add_documents(&repeated, &state.documents).unwrap();
            fs::write(&provider, "def foo := 10\n").unwrap();
            let saved = Inputs::read(&root, &repeated, &state.documents, false).unwrap();
            assert_eq!(
                saved.texts.len(),
                1,
                "Overlapping traversal duplicated physical saved source"
            );
            assert_eq!(saved.modules["Foo"], saved.modules["src.Foo"]);
            fs::write(root.join("Foo.lean"), "def other := 20\n").unwrap();
            assert!(
                Inputs::read(&root, &repeated, &state.documents, false)
                    .unwrap_err()
                    .to_string()
                    .contains("Ambiguous local module provider")
            );
            let other = format!("file://{}", root.join("Foo.lean").display());
            assert!(
                state
                    .update_document(
                        &json!({"method":"textDocument/didOpen","params":{"textDocument":{
                "uri":other,"languageId":"lean4","version":1,"text":"def other := 20\n"}}}),
                        false
                    )
                    .unwrap_err()
                    .to_string()
                    .contains("Ambiguous live local module provider")
            );
        }
    }

    #[test]
    fn live_root_containment_observes_ascii_case_and_component_boundaries() {
        for reversed in [false, true] {
            let dir = tempfile::tempdir().unwrap();
            let root = dir.path().to_owned();
            fs::create_dir(root.join("src")).unwrap();
            let mut roots = vec![root.clone(), root.join("Src")];
            if reversed {
                roots.reverse();
            }
            let provider = root.join("src/Foo.lean");
            let uri = format!("file://{}", provider.display());
            let mut folded = State::new(root.clone(), roots.clone(), [0; 32], true).unwrap();
            open(&mut folded, &uri, "def foo := 10\n");
            assert_eq!(folded.inputs.modules["foo"], provider);
            assert_eq!(folded.inputs.modules["src.foo"], provider);
            let mut exact = State::new(root.clone(), roots.clone(), [0; 32], false).unwrap();
            open(&mut exact, &uri, "def foo := 10\n");
            assert!(!exact.inputs.modules.contains_key("Foo"));
            assert_eq!(
                source_relative_path(&root.join("srcOther/Foo.lean"), &root.join("Src"), true),
                None
            );
            fs::write(&provider, "def foo := 10\n").unwrap();
            folded.changed_inputs([1; 32]).unwrap();
            assert_eq!(folded.documents[&uri].path, provider);
            assert_eq!(folded.inputs.modules["foo"], provider);
            assert!(!folded.inputs.dirty(&folded.documents[&uri]));
            if root.join("Src").exists() {
                // On an actually folding filesystem, the saved traversal must
                // find both aliases without help from an open live document.
                let saved = Inputs::read(&root, &roots, &BTreeMap::new(), true).unwrap();
                assert_eq!(saved.modules["foo"], provider);
                assert_eq!(saved.modules["src.foo"], provider);
                assert_eq!(saved.texts.len(), 1);
            }
        }
    }

    #[test]
    fn unsaved_buffer_alias_rejection_uses_only_the_probed_case_rule() {
        for folds_case in [false, true] {
            let dir = tempfile::tempdir().unwrap();
            let root = dir.path().to_owned();
            let mut state =
                State::new(root.clone(), vec![root.clone()], [0; 32], folds_case).unwrap();
            let upper = format!("file://{}", root.join("New.lean").display());
            let lower = format!("file://{}", root.join("new.lean").display());
            open(&mut state, &upper, "def upper := 10\n");
            let result = state.update_document(
                &json!({"method":"textDocument/didOpen","params":{"textDocument":{
                "uri":lower,"languageId":"lean4","version":1,"text":"def lower := 20\n"}}}),
                false,
            );
            assert_eq!(result.is_err(), folds_case);
            if folds_case {
                assert!(result.unwrap_err().to_string().contains("Two buffers alias"));
                assert_eq!(state.documents.len(), 1);
                assert_eq!(state.documents[&upper].text, "def upper := 10\n");
            } else {
                assert_eq!(state.documents.len(), 2);
                assert_ne!(state.documents[&upper].path, state.documents[&lower].path);
            }
        }
    }

    #[test]
    fn private_source_filter_uses_the_bound_filesystem_case_rule() {
        let dir = tempfile::tempdir().unwrap();
        for private in [".LAKE", ".GIT", ".RUNTIME", ".ANNEAL-BIN"] {
            let path = dir.path().join("nested").join(private);
            fs::create_dir_all(&path).unwrap();
            fs::write(path.join("Ignored.lean"), "def ignored := 1\n").unwrap();
            assert!(private_source_name(std::ffi::OsStr::new(private), true));
            assert!(!private_source_name(std::ffi::OsStr::new(private), false));
            assert!(private_source_name(
                std::ffi::OsStr::new(&private.to_ascii_lowercase()),
                false
            ));
        }
        for normal in [".lake-note", "runtime", "New.lean"] {
            assert!(!private_source_name(std::ffi::OsStr::new(normal), true));
        }
        let documents = BTreeMap::new();
        let roots = [dir.path().to_owned()];
        let folded = Inputs::read(dir.path(), &roots, &documents, true).unwrap();
        assert!(folded.texts.is_empty());
        assert!(folded.modules.is_empty());
        let exact = Inputs::read(dir.path(), &roots, &documents, false).unwrap();
        assert_eq!(exact.texts.len(), 4);
    }

    #[test]
    fn local_private_document_opens_reject_saved_and_unsaved_aliases() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().to_owned();
        let mut state = State::new(root.clone(), vec![root.clone()], [0; 32], true).unwrap();
        for private in
            [".lake", ".git", ".runtime", ".anneal-bin", ".LaKe", ".GiT", ".RuNtImE", ".AnNeAl-BiN"]
        {
            let path = root.join("nested").join(private);
            fs::create_dir_all(&path).unwrap();
            fs::write(path.join("Saved.lean"), "def saved := 1\n").unwrap();
            for leaf in ["Saved.lean", "Unsaved.lean"] {
                let uri = format!("file://{}", path.join(leaf).display());
                let open = json!({"method":"textDocument/didOpen","params":{"textDocument":{
                    "uri":uri,"languageId":"lean4","version":1,"text":"def saved := 1\n"}}});
                let error = state.update_document(&open, false).unwrap_err();
                assert!(error.to_string().contains("private workspace directory"));
                assert!(state.documents.is_empty());
            }
        }
        let new_path = root.join("normal").join("New.lean");
        let uri = format!("file://{}", new_path.display());
        open(&mut state, &uri, "def newValue := 1\n");
        assert!(state.documents.contains_key(&uri));
        assert!(!new_path.exists());
    }

    #[test]
    fn snapshot_races_publish_pending_and_permanent_errors_still_fail() {
        let (_dir, mut state, _, client) = fixture();
        open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
        let mut output = Vec::new();
        let epoch = state.epoch;
        assert!(
            snapshot_or_pending::<()>(
                Err(SourceStampChanged::new("save race").into()),
                &mut state,
                &mut output
            )
            .unwrap()
            .is_none()
        );
        assert!(state.snapshot_pending);
        assert!(state.blocked(&client));
        assert_eq!(state.epoch, epoch + 1);
        let pending = read_message(&mut BufReader::new(output.as_slice())).unwrap().unwrap();
        assert_eq!(pending["params"]["diagnostics"][0]["source"], "Anneal");
        assert!(
            snapshot_or_pending::<()>(
                Err(anyhow::anyhow!("Permission denied")),
                &mut state,
                &mut output
            )
            .is_err()
        );
        assert!(
            local_read::<()>(
                Err(io::Error::from(io::ErrorKind::NotFound)),
                Path::new("source.lean")
            )
            .unwrap_err()
            .downcast_ref::<SourceStampChanged>()
            .is_some()
        );
        assert!(
            local_read::<()>(
                Err(io::Error::from(io::ErrorKind::PermissionDenied)),
                Path::new("source.lean")
            )
            .unwrap_err()
            .downcast_ref::<SourceStampChanged>()
            .is_none()
        );
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
        let state = State::new(root.clone(), vec![root.clone()], [0; 32], false).unwrap();
        (
            dir,
            state,
            format!("file://{}", root.join("Local.lean").display()),
            format!("file://{}", root.join("Client.lean").display()),
        )
    }

    #[test]
    fn imported_alias_survives_physical_provider_deduplication() {
        let (dir, _, _, client) = fixture();
        fs::create_dir(dir.path().join("src")).unwrap();
        fs::write(dir.path().join("src/Foo.lean"), "def foo := 10\n").unwrap();
        let root = dir.path().to_path_buf();
        let mut state =
            State::new(root.clone(), vec![root.clone(), root.join("src")], [0; 32], false).unwrap();
        open(&mut state, &client, "import Foo\nexample : True := by trivial\n");
        let input = state.refresh_input(&state.documents[&client]).unwrap();
        assert_eq!(input.targets, BTreeSet::from(["Foo".to_owned()]));
        assert_eq!(input.dependencies, BTreeSet::from([root.join("src/Foo.lean")]));
        assert!(state.inputs.modules.contains_key("src.Foo"));
    }

    #[test]
    fn document_batches_isolate_shared_and_disjoint_failures() {
        let (dir, _, _, client) = fixture();
        fs::write(dir.path().join("Other.lean"), "def other := 10\n").unwrap();
        let root = dir.path().to_path_buf();
        let mut state = State::new(root.clone(), vec![root.clone()], [0; 32], false).unwrap();
        open(&mut state, &client, "import Middle\nimport Other\nexample : True := by trivial\n");
        let shared = format!("file://{}", root.join("SharedClient.lean").display());
        open(&mut state, &shared, "import Other\nexample : True := by trivial\n");
        let disjoint = format!("file://{}", root.join("DisjointClient.lean").display());
        open(&mut state, &disjoint, "import Local\nexample : True := by trivial\n");
        let docs = state.build_documents(true);
        let groups = partition_documents(&docs);
        let target_sets: Vec<_> = groups.iter().map(|(targets, _)| targets.clone()).collect();
        assert!(target_sets.contains(&BTreeSet::from([
            "Local".to_owned(),
            "Middle".to_owned(),
            "Other".to_owned()
        ])));
        assert!(target_sets.contains(&BTreeSet::from(["Other".to_owned()])));
        assert!(target_sets.contains(&BTreeSet::from(["Local".to_owned()])));
        assert_eq!(groups.len(), 3);
        let failed = docs[&state.documents[&client].path].clone();
        state.failed_inputs.insert(state.documents[&client].path.clone(), failed);
        assert!(!state.build_documents(true).contains_key(&state.documents[&client].path));
        state.changed_inputs([1; 32]).unwrap();
        assert!(state.build_documents(true).contains_key(&state.documents[&client].path));
    }

    #[test]
    fn self_and_two_file_cycles_report_sources_while_dependent_claims_wait() {
        for two_file in [false, true] {
            let (dir, _, local, client) = fixture();
            let root = dir.path().to_path_buf();
            fs::write(
                root.join("Local.lean"),
                if two_file {
                    "import Middle\ndef value := 10\n"
                } else {
                    "import Local\ndef value := 10\n"
                },
            )
            .unwrap();
            let mut state = State::new(root.clone(), vec![root.clone()], [0; 32], false).unwrap();
            open(&mut state, &local, &fs::read_to_string(root.join("Local.lean")).unwrap());
            let middle = format!("file://{}", root.join("Middle.lean").display());
            if two_file {
                open(&mut state, &middle, "import Local\ndef middle := value\n");
            }
            open(&mut state, &client, "import Middle\nexample : True := by trivial\n");
            assert!(
                !state
                    .inputs
                    .dependencies(&root.join("Local.lean"))
                    .contains(&root.join("Local.lean"))
            );
            assert!(state.blocked(&local));
            assert!(state.blocked(&client));
            let messages = state.pending_notifications();
            for uri in if two_file { vec![&local, &middle] } else { vec![&local] } {
                assert!(messages.iter().any(|m| {
                    m["params"]["uri"] == *uri
                        && m["params"]["diagnostics"][0]["severity"] == 1
                        && m["params"]["diagnostics"][0]["message"]
                            .as_str()
                            .unwrap()
                            .contains("Local import cycle")
                }));
            }
            assert!(
                messages.iter().any(|m| m["params"]["uri"] == client
                    && m["params"]["diagnostics"][0]["severity"] == 2)
            );
        }
    }

    #[test]
    fn unchanged_source_version_replaces_pending_reason_as_live_cycle_appears_and_clears() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().to_path_buf();
        fs::write(root.join("A.lean"), "import B\ndef a := b\n").unwrap();
        fs::write(root.join("B.lean"), "def b := 0\n").unwrap();
        let mut state = State::new(root.clone(), vec![root.clone()], [0; 32], false).unwrap();
        let a = format!("file://{}", root.join("A.lean").display());
        let b = format!("file://{}", root.join("B.lean").display());
        open(&mut state, &a, "import B\ndef a := b\n");
        open(&mut state, &b, "def b := 1\n");
        let pending = state.pending_notifications();
        assert!(pending.iter().any(|m| m["params"]["uri"] == a
            && m["params"]["version"] == 1
            && m["params"]["diagnostics"][0]["severity"] == 2));

        state
            .update_document(
                &json!({"method":"textDocument/didChange","params":{
                    "textDocument":{"uri":b,"version":2},
                    "contentChanges":[{"text":"import A\ndef b := 1\n"}]
                }}),
                false,
            )
            .unwrap();
        let cycle = state.pending_notifications();
        assert!(cycle.iter().any(|m| {
            m["params"]["uri"] == a
                && m["params"]["version"] == 1
                && m["params"]["diagnostics"][0]["severity"] == 1
                && m["params"]["diagnostics"][0]["message"]
                    .as_str()
                    .unwrap()
                    .contains("Local import cycle")
        }));
        assert!(state.pending_notifications().iter().all(|m| m["params"]["uri"] != a));

        state
            .update_document(
                &json!({"method":"textDocument/didChange","params":{
                    "textDocument":{"uri":b,"version":3},
                    "contentChanges":[{"text":"def b := 1\n-- still unsaved\n"}]
                }}),
                false,
            )
            .unwrap();
        let pending_again = state.pending_notifications();
        assert!(pending_again.iter().any(|m| m["params"]["uri"] == a
            && m["params"]["version"] == 1
            && m["params"]["diagnostics"][0]["severity"] == 2));
        assert!(state.blocked(&a));
        assert_eq!(state.documents[&a].version, 1);
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
            snapshot: state.request_snapshot(&client),
            uri: Some(client.clone()),
            version: Some(1),
            method: "$/lean/plainGoal".into(),
            wait: None,
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
            snapshot: state.request_snapshot(&client),
            uri: Some(client.clone()),
            version: Some(1),
            method: "$/lean/rpc/call".into(),
            wait: None,
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
            State::new(dir.path().to_owned(), vec![dir.path().to_owned()], [2; 32], false).unwrap();
        open(&mut fresh, &client, "import Middle\nexample : middle = 10 := by decide\n");
        assert!(fresh.blocked(&client));
    }

    #[test]
    fn discarded_live_only_aliases_do_not_become_saved_tombstones() {
        for folds_case in [false, true] {
            let (dir, _, _, client) = fixture();
            let root = dir.path().to_owned();
            fs::create_dir(root.join("src")).unwrap();
            fs::write(root.join("Middle.lean"), "import Foo\ndef middle := foo\n").unwrap();
            let mut state =
                State::new(root.clone(), vec![root.clone(), root.join("src")], [0; 32], folds_case)
                    .unwrap();
            let path = root.join("src/Foo.lean");
            let foo = format!("file://{}", path.display());
            open(&mut state, &foo, "def foo := 10\n");
            open(&mut state, &client, "import Middle\nexample : True := by trivial\n");
            let aliases = [state.inputs.module_key("Foo"), state.inputs.module_key("src.Foo")];
            assert!(state.blocked(&client));
            state.changed_inputs([1; 32]).unwrap();
            for alias in &aliases {
                assert_eq!(state.inputs.modules[alias], path);
                assert!(!state.inputs.retained.contains_key(alias));
            }
            for cycle in 0..2 {
                state.update_document(&json!({"method":"textDocument/didClose","params":{"textDocument":{"uri":foo}}}), false).unwrap();
                state.update_document(&json!({"method":"textDocument/didSave","params":{"textDocument":{"uri":client}}}), false).unwrap();
                state.changed_inputs([2 + cycle; 32]).unwrap();
                for alias in &aliases {
                    assert!(!state.inputs.modules.contains_key(alias));
                    assert!(!state.inputs.module_names.contains_key(alias));
                    assert!(!state.inputs.retained.contains_key(alias));
                }
                assert!(!state.inputs.dependencies(&state.documents[&client].path).contains(&path));
                assert!(
                    state.build_documents(false).contains_key(&state.documents[&client].path),
                    "Discarded provider kept transitive refresh permanently pending"
                );
                state.invalid.clear(); // Model completion of the eligible refresh.
                assert!(!state.blocked(&client));
                if cycle == 0 {
                    open(&mut state, &foo, "def foo := 20\n");
                    assert!(
                        state.blocked(&client),
                        "Reopened live provider escaped transitive scope"
                    );
                }
            }
        }
    }

    #[test]
    fn observed_saved_nested_provider_survives_close_delete_and_orphan_guess() {
        let (dir, _, _, client) = fixture();
        let root = dir.path().to_owned();
        fs::create_dir(root.join("src")).unwrap();
        let path = root.join("src/Foo.lean");
        fs::write(&path, "def foo := 10\n").unwrap();
        fs::write(root.join("Middle.lean"), "import Foo\ndef middle := foo\n").unwrap();
        let mut state =
            State::new(root.clone(), vec![root.clone(), root.join("src")], [0; 32], false).unwrap();
        open(&mut state, &client, "import Middle\nexample : True := by trivial\n");
        let foo = format!("file://{}", path.display());
        open(&mut state, &foo, "def foo := 10\n");
        fs::remove_file(&path).unwrap();
        let output = root.join(".lake/build/lib/lean");
        fs::create_dir_all(&output).unwrap();
        fs::write(output.join("Foo.olean"), "old local output").unwrap();
        state
            .update_document(
                &json!({"method":"textDocument/didClose","params":{"textDocument":{"uri":foo}}}),
                false,
            )
            .unwrap();
        state.changed_inputs([1; 32]).unwrap();
        for alias in ["Foo", "src.Foo"] {
            assert_eq!(
                state.inputs.modules[alias], path,
                "Orphan guess replaced the observed nested path"
            );
            assert!(state.inputs.retained[alias].saved);
        }
        state.invalid.clear();
        assert!(state.blocked(&client));
        assert!(state.refresh_input(&state.documents[&client]).is_none());
        open(&mut state, &foo, "def foo := 10\n");
        assert!(
            state.blocked(&client),
            "Reopening a deleted saved provider certified missing disk bytes"
        );
        fs::write(&path, "def foo := 10\n").unwrap();
        state.changed_inputs([2; 32]).unwrap();
        assert!(state.build_documents(false).contains_key(&state.documents[&client].path));
        state.invalid.clear();
        assert!(!state.blocked(&client));
    }

    #[test]
    fn inferred_orphan_remains_retained_beneath_a_discarded_live_overlay() {
        let (dir, _, _, client) = fixture();
        let root = dir.path().to_owned();
        fs::create_dir(root.join("src")).unwrap();
        fs::write(root.join("Middle.lean"), "import Foo\ndef middle := foo\n").unwrap();
        let output = root.join(".lake/build/lib/lean");
        fs::create_dir_all(&output).unwrap();
        fs::write(output.join("Foo.olean"), "old local output").unwrap();
        let mut state =
            State::new(root.clone(), vec![root.clone(), root.join("src")], [0; 32], false).unwrap();
        open(&mut state, &client, "import Middle\nexample : True := by trivial\n");
        let path = root.join("src/Foo.lean");
        let foo = format!("file://{}", path.display());
        open(&mut state, &foo, "def foo := 10\n");
        assert_eq!(state.inputs.modules["Foo"], path);
        assert!(!state.inputs.retained["Foo"].saved);
        let mut ambiguous = state.clone();
        let conflict = format!("file://{}", root.join("Foo.lean").display());
        assert!(
            ambiguous
                .update_document(
                    &json!({"method":"textDocument/didOpen","params":{"textDocument":{
            "uri":conflict,"languageId":"lean4","version":1,"text":"def conflict := 20\n"}}}),
                    false
                )
                .unwrap_err()
                .to_string()
                .contains("Ambiguous live local module provider")
        );
        state
            .update_document(
                &json!({"method":"textDocument/didClose","params":{"textDocument":{"uri":foo}}}),
                false,
            )
            .unwrap();
        assert_eq!(state.inputs.modules["Foo"], root.join("Foo.lean"));
        assert!(!state.inputs.modules.contains_key("src.Foo"));
        state.invalid.clear();
        assert!(state.blocked(&client));
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
    fn generation_reset_clears_only_remaining_closed_diagnostics_once() {
        let (_dir, mut state, local, client) = fixture();
        open(&mut state, &local, "def value := 10\n");
        open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
        for uri in [&local, &client] {
            state
                .update_document(
                    &json!({"method":"textDocument/didClose","params":{"textDocument":{"uri":uri}}}),
                    false,
                )
                .unwrap();
        }
        let already_cleared = json!({"method":"textDocument/publishDiagnostics","params":{
            "uri":local,"version":1,"diagnostics":[]}});
        assert!(state.take_closed_diagnostics(&already_cleared));
        let mut output = Vec::new();
        clear_closed_diagnostics(&mut state, &mut output).unwrap();
        let clear = read_message(&mut io::BufReader::new(output.as_slice())).unwrap().unwrap();
        assert_eq!(clear["params"]["uri"], client);
        assert_eq!(clear["params"]["version"], 1);
        assert_eq!(clear["params"]["diagnostics"], json!([]));
        assert!(state.closed.is_empty());
        let mut second = Vec::new();
        clear_closed_diagnostics(&mut state, &mut second).unwrap();
        assert!(second.is_empty());
    }

    #[test]
    fn case_folded_workspace_root_admits_unsaved_local_buffers_and_private_filter() {
        let (dir, _, _, _) = fixture();
        let root = dir.path().to_path_buf();
        let mut state = State::new(root.clone(), vec![root.clone()], [0; 32], true).unwrap();
        let client = format!("file://{}", root.join("NewImporter.lean").display());
        open(&mut state, &client, "import New\nexample : True := by trivial\n");
        assert!(!state.blocked(&client), "The unresolved import has no local provider yet");
        let alias_root = PathBuf::from(root.to_string_lossy().to_ascii_uppercase());
        let unsaved = format!("file://{}", alias_root.join("New.lean").display());
        assert!(!alias_root.join("New.lean").exists());
        assert!(source_relative_path(&alias_root.join("New.lean"), &root, true).is_some());
        open(&mut state, &unsaved, "def new := 1\n");
        assert!(state.documents[&unsaved].local);
        assert!(
            state
                .inputs
                .dependencies(&state.documents[&client].path)
                .contains(&state.documents[&unsaved].path)
        );
        assert!(state.blocked(&client), "Unsaved aliased provider must block its importer");
        let private = format!("file://{}", alias_root.join(".LAKE/Hidden.lean").display());
        assert!(state.update_document(&json!({"method":"textDocument/didOpen","params":{
            "textDocument":{"uri":private,"languageId":"lean4","version":1,"text":"def hidden := 1\n"}}}), false).is_err());
        let mut strict = State::new(root.clone(), vec![root], [0; 32], false).unwrap();
        assert!(strict.update_document(&json!({"method":"textDocument/didOpen","params":{
            "textDocument":{"uri":unsaved,"languageId":"lean4","version":1,"text":"def new := 1\n"}}}), false).is_err());
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
            sdk_source: Option<PathBuf>,
            source_admissions: Arc<AtomicUsize>,
            immutable_lookups: Arc<AtomicUsize>,
        }
        impl FakeHost {
            fn try_lock(&self, shared: bool) -> Result<Option<fs::File>> {
                if self.root.join("busy-writer").exists() {
                    return Ok(None);
                }
                let file = fs::OpenOptions::new()
                    .read(true)
                    .write(true)
                    .create(true)
                    .truncate(false)
                    .open(self.root.join(".fake-writer.lock"))?;
                let result = if shared {
                    fs2::FileExt::try_lock_shared(&file)
                } else {
                    fs2::FileExt::try_lock_exclusive(&file)
                };
                match result {
                    Ok(()) => Ok(Some(file)),
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => Ok(None),
                    Err(error) => Err(error.into()),
                }
            }
        }
        impl Host for FakeHost {
            fn root(&self) -> &Path {
                &self.root
            }
            fn source_roots(&self) -> Vec<PathBuf> {
                if self.root.join("overlapping-roots").exists() {
                    vec![self.root.clone(), self.root.join("src")]
                } else {
                    vec![self.root.clone()]
                }
            }
            fn source_stamp(&self) -> Result<[u8; 32]> {
                let call = self.source_stamps.fetch_add(1, Ordering::Relaxed) + 1;
                if self.root.join("stamp-mutate-always").exists() {
                    fs::write(
                        self.root.join("Local.lean"),
                        format!("def value := {}\n", 100 + call),
                    )?;
                    fs::write(self.root.join("stamp-mutated"), "changed")?;
                    return Err(SourceStampChanged::new(
                        "Injected continuously changing saved source",
                    )
                    .into());
                }
                if self.root.join("stamp-block-race").exists() {
                    fs::write(self.root.join("stamp-block-entered"), "entered")?;
                    let deadline = Instant::now() + Duration::from_secs(3);
                    while self.root.join("stamp-block-race").exists() {
                        ensure!(Instant::now() < deadline, "Fake snapshot gate was not released");
                        thread::sleep(Duration::from_millis(5));
                    }
                    return Err(SourceStampChanged::new("Injected gated snapshot race").into());
                }
                if self.root.join("slow-stamp").exists() {
                    thread::sleep(Duration::from_millis(2));
                }
                if let Ok(at) = fs::read_to_string(self.root.join("stamp-mutate-at")) {
                    if at.trim().parse::<usize>()? == call {
                        fs::remove_file(self.root.join("stamp-mutate-at"))?;
                        fs::write(self.root.join("Local.lean"), "def value := 30\n")?;
                    }
                }
                if self.root.join("stamp-fatal").exists() {
                    bail!("Permanent workspace admission failure");
                }
                if let Ok(races) = fs::read_to_string(self.root.join("stamp-races")) {
                    let races: usize = races.trim().parse()?;
                    if races > 0 {
                        fs::write(self.root.join("stamp-races"), (races - 1).to_string())?;
                        return Err(SourceStampChanged::new("Injected direct-save race").into());
                    }
                }
                let mut hash = Sha256::new();
                let mut paths = walkdir::WalkDir::new(&self.root)
                    .into_iter()
                    .filter_entry(|entry| !private_source_name(entry.file_name(), false))
                    .filter_map(|entry| entry.ok())
                    .filter(|entry| {
                        entry.file_type().is_file()
                            && (entry.path().extension().is_some_and(|e| e == "lean")
                                || entry.path() == self.root.join(".anneal-lake.json"))
                    })
                    .map(|entry| entry.into_path())
                    .collect::<Vec<_>>();
                paths.sort();
                for path in paths {
                    hash.update(path.strip_prefix(&self.root)?.as_os_str().as_encoded_bytes());
                    hash.update(fs::read(&path)?);
                    hash.update(
                        fs::metadata(&path)?
                            .modified()?
                            .duration_since(std::time::UNIX_EPOCH)?
                            .as_nanos()
                            .to_le_bytes(),
                    );
                }
                Ok(hash.finalize().into())
            }
            fn folds_ascii_case(&self) -> Result<bool> {
                Ok(self.root.join("fold-ascii-case").exists())
            }
            fn prepare_local_outputs(&self) -> Result<Option<LocalOutputPreparation>> {
                fs::write(self.root.join("prepare-called"), "called")?;
                Ok(None)
            }
            fn finish_local_outputs(&self, _prepared: &LocalOutputPreparation) -> Result<()> {
                bail!("Fake host never issues an SDK output preparation")
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
                        if self.root.join("fatal-setup-file").exists() {
                            bail!("Injected permanent setup admission failure");
                        }
                        let race = self.root.join("race-setup-file");
                        if race.exists() {
                            fs::remove_file(&race)?;
                            fs::remove_file(path)?;
                            fs::write(self.root.join("setup-file-disappeared"), "raced")?;
                        }
                        ensure!(path.is_file(), "setup-file requires a saved local source");
                        command.arg("setup").arg(path);
                    }
                    LakeOperation::Version => {
                        command.arg("version");
                    }
                }
                Ok(command)
            }
            fn contains_source(&self, path: &Path) -> Result<bool> {
                self.source_admissions.fetch_add(1, Ordering::Relaxed);
                ensure!(
                    !self.root.join("busy-writer").exists(),
                    "Workspace admission during external writer"
                );
                Ok(self.sdk_source.as_deref() == Some(path))
            }
            fn contains_immutable_sdk_source(&self, path: &Path) -> Result<bool> {
                self.immutable_lookups.fetch_add(1, Ordering::Relaxed);
                Ok(self.sdk_source.as_deref() == Some(path))
            }
            fn try_writer_lock(&self) -> Result<Option<fs::File>> {
                self.try_lock(false)
            }
            fn try_shared_lock(&self) -> Result<Option<fs::File>> {
                self.try_lock(true)
            }
        }

        struct Session {
            dir: tempfile::TempDir,
            sdk_dir: tempfile::TempDir,
            input: UnixStream,
            output: BufReader<UnixStream>,
            join: Option<thread::JoinHandle<Result<()>>>,
            client: String,
            local: String,
            seen: Vec<Value>,
            source_stamps: Arc<AtomicUsize>,
            source_admissions: Arc<AtomicUsize>,
            immutable_lookups: Arc<AtomicUsize>,
        }
        impl Session {
            fn start() -> Self {
                Self::start_document("Client.lean")
            }
            fn start_document(name: &str) -> Self {
                Self::start_document_with_races(name, 0)
            }
            fn start_document_with_races(name: &str, races: usize) -> Self {
                Self::start_document_with(name, races, None)
            }
            fn start_document_with(name: &str, races: usize, text: Option<&str>) -> Self {
                Self::start_document_with_roots(name, races, text, false)
            }
            fn start_document_with_roots(
                name: &str,
                races: usize,
                text: Option<&str>,
                overlapping: bool,
            ) -> Self {
                Self::start_document_with_policy(name, races, text, overlapping, false)
            }
            fn start_document_with_policy(
                name: &str,
                races: usize,
                text: Option<&str>,
                overlapping: bool,
                folds_case: bool,
            ) -> Self {
                let (dir, _state, local, client) = fixture();
                if overlapping {
                    fs::create_dir(dir.path().join("src")).unwrap();
                    fs::write(dir.path().join("overlapping-roots"), "bound roots . and src")
                        .unwrap();
                }
                if folds_case {
                    fs::write(dir.path().join("fold-ascii-case"), "probe result").unwrap();
                }
                let sdk_dir = tempfile::tempdir().unwrap();
                let sdk_source = sdk_dir.path().join("Shared.lean");
                fs::write(&sdk_source, "example : True := by trivial\n").unwrap();
                if races > 0 {
                    fs::write(dir.path().join("stamp-races"), races.to_string()).unwrap();
                }
                let client = if name == "Client.lean" {
                    client
                } else {
                    format!("file://{}", dir.path().join(name).display())
                };
                let (input, server_input) = UnixStream::pair().unwrap();
                let (output, mut server_output) = UnixStream::pair().unwrap();
                output.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
                let source_stamps = Arc::new(AtomicUsize::new(0));
                let source_admissions = Arc::new(AtomicUsize::new(0));
                let immutable_lookups = Arc::new(AtomicUsize::new(0));
                let host = FakeHost {
                    root: dir.path().to_owned(),
                    source_stamps: source_stamps.clone(),
                    sdk_source: Some(sdk_source),
                    source_admissions: source_admissions.clone(),
                    immutable_lookups: immutable_lookups.clone(),
                };
                let join =
                    thread::spawn(move || run_session(&host, server_input, &mut server_output));
                let mut session = Self {
                    dir,
                    sdk_dir,
                    input,
                    output: BufReader::new(output),
                    join: Some(join),
                    client,
                    local,
                    seen: Vec::new(),
                    source_stamps,
                    source_admissions,
                    immutable_lookups,
                };
                session.send(json!({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"capabilities":{}}}));
                session.until(|message| message["id"] == 1);
                session.send(json!({"jsonrpc":"2.0","method":"initialized","params":{}}));
                let text = text.unwrap_or(
                    "import Middle\nexample : middle = 10 := by decide\n-- unsaved client note\n",
                );
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
        fn setup_file_disappearance_is_retryable_but_other_setup_errors_remain_fatal() {
            let (dir, mut state, _, client) = fixture();
            open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
            let documents = state.build_documents(true);
            assert!(documents.contains_key(&state.documents[&client].path));
            let host = FakeHost {
                root: dir.path().to_owned(),
                source_stamps: Arc::new(AtomicUsize::new(0)),
                sdk_source: None,
                source_admissions: Arc::new(AtomicUsize::new(0)),
                immutable_lookups: Arc::new(AtomicUsize::new(0)),
            };
            fs::write(dir.path().join("race-setup-file"), "remove after first existence check")
                .unwrap();
            let race = build_commands(&host, &state, &documents).err().unwrap();
            assert!(race.downcast_ref::<SourceStampChanged>().is_some());
            assert!(dir.path().join("setup-file-disappeared").exists());
            fs::write(
                dir.path().join("Client.lean"),
                "import Middle\nexample : middle = 10 := by decide\n",
            )
            .unwrap();
            fs::write(dir.path().join("fatal-setup-file"), "permanent").unwrap();
            let fatal = build_commands(&host, &state, &documents).err().unwrap();
            assert!(fatal.downcast_ref::<SourceStampChanged>().is_none());
            assert!(fatal.to_string().contains("permanent setup admission failure"));
        }

        #[test]
        fn case_folded_root_uri_opens_unsaved_local_document_without_sdk_admission() {
            let mut session =
                Session::start_document_with_policy("Client.lean", 0, None, false, true);
            let before = session.source_admissions.load(Ordering::Relaxed);
            let alias_root = session.dir.path().to_string_lossy().to_ascii_uppercase();
            let uri = format!("file://{alias_root}/New.lean");
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{
                "textDocument":{"uri":uri,"languageId":"lean4","version":1,
                    "text":"def new := 1\n"}}}));
            let diagnostics = session.until(|m| {
                m["method"] == "textDocument/publishDiagnostics" && m["params"]["uri"] == uri
            });
            assert_eq!(diagnostics["params"]["version"], 1);
            assert_eq!(session.source_admissions.load(Ordering::Relaxed), before);
            session.finish();
        }

        #[test]
        fn dynamic_workspace_folder_changes_fail_closed() {
            for change in ["add-foreign", "remove-bound", "empty"] {
                let mut session = Session::start();
                let root = format!("file://{}", session.dir.path().display());
                let folders = match change {
                    "add-foreign" => {
                        json!({"added":[{"uri":"file:///foreign/project","name":"foreign"}],"removed":[]})
                    }
                    "remove-bound" => json!({"added":[],"removed":[{"uri":root,"name":"bound"}]}),
                    "empty" => json!({"added":[],"removed":[]}),
                    _ => unreachable!(),
                };
                session
                    .send(json!({"jsonrpc":"2.0","method":"workspace/didChangeWorkspaceFolders",
                    "params":{"event":folders}}));
                let deadline = Instant::now() + Duration::from_secs(3);
                while !session.join.as_ref().unwrap().is_finished() {
                    assert!(Instant::now() < deadline, "{change} was forwarded or retained");
                    thread::sleep(Duration::from_millis(5));
                }
                let failure = session.join.take().unwrap().join().unwrap().unwrap_err();
                assert!(failure.to_string().contains("Dynamic editor workspace folders"));
            }
        }

        fn wait_lifetime_released(root: &Path, name: &str) {
            // The cancellation fixtures hold for up to twenty seconds. This
            // shorter bound cannot accept their natural exit as cancellation.
            let deadline = Instant::now() + Duration::from_secs(1);
            loop {
                let path = root.join(name);
                let lifetime = fs::OpenOptions::new().read(true).write(true).open(&path).unwrap();
                match fs2::FileExt::try_lock_exclusive(&lifetime) {
                    Ok(()) => return,
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => {}
                    Err(error) => panic!("Could not check {}: {error}", path.display()),
                }
                assert!(Instant::now() < deadline, "{name} retained its process lifetime lease");
                thread::sleep(Duration::from_millis(10));
            }
        }

        #[test]
        fn build_group_grace_and_force_release_parent_and_descendant_lifetimes() {
            for forced in [false, true] {
                let dir = tempfile::tempdir().unwrap();
                let root = dir.path();
                fs::write(root.join("Local.lean"), "def value := 20\n").unwrap();
                fs::write(root.join("hold-build-value"), "20").unwrap();
                fs::write(root.join("hold-build-cancel-required"), "hold through lifetime check")
                    .unwrap();
                fs::write(root.join("spawn-build-child"), "child").unwrap();
                if forced {
                    fs::write(root.join("ignore-build-term"), "force group cleanup").unwrap();
                }
                let mut command = Command::new("/usr/bin/python3");
                command
                    .args(["-I", "-B"])
                    .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/editor_fake_peer.py"))
                    .arg(root)
                    .arg("build")
                    .arg("+Local:olean")
                    .env_clear()
                    .env("PATH", "/usr/bin:/bin");
                let mut process = Process::spawn(&mut command).unwrap();
                let wait_file = |name: &str| {
                    let deadline = Instant::now() + Duration::from_secs(5);
                    while !root.join(name).exists() {
                        assert!(Instant::now() < deadline, "Fake build did not create {name}");
                        thread::sleep(Duration::from_millis(10));
                    }
                };
                wait_file("child-ready-20");
                wait_file("build-held-20");
                process.stop_with_grace(|| {
                    if !forced {
                        // Let the parent actually exit after its callback
                        // before Process sends SIGKILL. Production still
                        // uses its fixed 50 ms bound.
                        wait_lifetime_released(root, "build-lifetime-20");
                    }
                });
                assert!(process.child.try_wait().unwrap().is_some());
                wait_lifetime_released(root, "build-lifetime-20");
                wait_lifetime_released(root, "child-lifetime-20");
                if forced {
                    assert!(!root.join("build-stopped-20").exists());
                    assert!(!root.join("child-stopped-20").exists());
                } else {
                    assert!(root.join("build-stopped-20").exists());
                }
            }
        }

        #[test]
        fn discarded_provider_retries_reopen_and_release_importers_to_backend_resolution() {
            for missing in [false, true] {
                let mut session = Session::start_document_with_roots("Client.lean", 0, None, true);
                if missing {
                    fs::write(session.dir.path().join("missing-foo"), "diagnose missing import")
                        .unwrap();
                }
                // The peer otherwise treats this unknown namespace as a shared
                // import; neither case has a saved local Foo provider.
                let foo = format!("file://{}", session.dir.path().join("src/Foo.lean").display());
                session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                    "uri":foo,"languageId":"lean4","version":1,"text":"def foo := 10\n"}}}));
                session.until(|m| {
                    m["params"]["uri"] == foo && m["params"]["diagnostics"] == json!([])
                });
                let client =
                    format!("file://{}", session.dir.path().join("FooClient.lean").display());
                session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                    "uri":client,"languageId":"lean4","version":1,"text":"import Foo\nexample : True := by trivial\n"}}}));
                session.until(|m| {
                    m["params"]["uri"] == client
                        && m["params"]["diagnostics"][0]["source"] == "Anneal"
                });
                session.send(json!({"jsonrpc":"2.0","id":170,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":client}}}));
                assert_eq!(session.until(|m| m["id"] == 170)["error"]["code"], CONTENT_MODIFIED);
                for cycle in 0..2 {
                    if cycle == 0 {
                        fs::write(session.dir.path().join("stamp-races"), "2").unwrap();
                    }
                    session.send(json!({"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":foo}}}));
                    session.until(|m| {
                        m["method"] == "textDocument/publishDiagnostics"
                            && m["params"]["uri"] == client
                            && if missing {
                                m["params"]["diagnostics"][0]["message"]
                                    == "fake unresolved module Foo"
                            } else {
                                m["params"]["diagnostics"] == json!([])
                            }
                    });
                    session.send(json!({"jsonrpc":"2.0","id":171,"method":"$/test/documentState","params":{"textDocument":{"uri":client}}}));
                    assert_eq!(session.until(|m| m["id"] == 171)["result"]["version"], 1);
                    assert!(
                        !session.dir.path().join("src/Foo.lean").exists(),
                        "Coordinator saved a discarded buffer"
                    );
                    if cycle == 0 {
                        session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                            "uri":foo,"languageId":"lean4","version":1,"text":"def foo := 20\n"}}}));
                        session.send(json!({"jsonrpc":"2.0","id":172,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":client}}}));
                        assert_eq!(
                            session.until(|m| m["id"] == 172)["error"]["code"],
                            CONTENT_MODIFIED
                        );
                    }
                }
                session.finish();
            }
        }

        #[test]
        fn unsaved_nested_provider_blocks_each_alias_until_saved_refresh() {
            let mut session = Session::start_document_with_roots("Client.lean", 0, None, true);
            let provider = session.dir.path().join("src/Foo.lean");
            let foo = format!("file://{}", provider.display());
            session.send(
                json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":foo,"languageId":"lean4","version":1,"text":"def foo := 10\n"}}}),
            );
            session.until(|m| m["params"]["uri"] == foo && m["params"]["diagnostics"] == json!([]));
            let mut clients = Vec::new();
            for (index, module) in ["Foo", "src.Foo"].into_iter().enumerate() {
                let uri = format!(
                    "file://{}",
                    session.dir.path().join(format!("NestedClient{index}.lean")).display()
                );
                session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                    "uri":uri,"languageId":"lean4","version":1,"text":format!("import {module}\nexample : True := by trivial\n")}}}));
                session.until(|m| {
                    m["params"]["uri"] == uri && m["params"]["diagnostics"][0]["source"] == "Anneal"
                });
                let id = 160 + index;
                session.send(json!({"jsonrpc":"2.0","id":id,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":uri}}}));
                assert_eq!(session.until(|m| m["id"] == id)["error"]["code"], CONTENT_MODIFIED);
                clients.push(uri);
            }
            assert!(
                session.seen.iter().all(|m| !(clients
                    .contains(&m["params"]["uri"].as_str().unwrap_or("").to_owned())
                    && m["params"]["diagnostics"] == json!([]))),
                "Live-only nested import was credited before save/build"
            );
            fs::write(&provider, "def foo := 10\n").unwrap();
            for uri in &clients {
                session.until(|m| {
                    m["params"]["uri"] == *uri && m["params"]["diagnostics"] == json!([])
                });
            }
            let calls = fs::read_to_string(session.dir.path().join("calls.jsonl")).unwrap();
            let built: BTreeSet<_> = calls
                .lines()
                .map(|line| serde_json::from_str::<Value>(line).unwrap())
                .filter(|call| call["mode"] == "build")
                .flat_map(|call| call["args"].as_array().unwrap().clone())
                .filter_map(|target| target.as_str().map(str::to_owned))
                .collect();
            assert!(
                built.contains("+Foo:olean") && built.contains("+src.Foo:olean"),
                "Saved refresh omitted a declared imported alias"
            );
            session.finish();
        }

        #[test]
        fn save_spelling_normalization_commits_with_the_snapshot_and_preserves_dirty_checks() {
            let (dir, _, _, client) = fixture();
            let root = dir.path().to_owned();
            let host = FakeHost {
                root: root.clone(),
                source_stamps: Arc::new(AtomicUsize::new(0)),
                sdk_source: None,
                source_admissions: Arc::new(AtomicUsize::new(0)),
                immutable_lookups: Arc::new(AtomicUsize::new(0)),
            };
            let mut state = State::new(root.clone(), vec![root.clone()], [0; 32], true).unwrap();
            let unsaved = root.join("New.lean");
            let actual = root.join("new.lean");
            let uri = format!("file://{}", unsaved.display());
            open(&mut state, &uri, "def newValue := 10\n");
            open(&mut state, &client, "import New\nexample : True := by trivial\n");
            assert!(state.blocked(&client));
            fs::write(&actual, "def newValue := 10\n").unwrap();
            fs::write(root.join("stamp-mutate-at"), "2").unwrap();
            let race = reconcile_saved_inputs(&host, &mut state).unwrap_err();
            assert!(race.downcast_ref::<SourceStampChanged>().is_some());
            assert_eq!(
                state.documents[&uri].path, unsaved,
                "Raced graph read partly normalized the live buffer"
            );
            assert_eq!(state.inputs.modules["new"], unsaved);
            assert!(
                !state.inputs.retained.contains_key("new"),
                "Raced read promoted a live-only provider to saved history"
            );
            reconcile_saved_inputs(&host, &mut state).unwrap();
            assert_eq!(state.documents[&uri].path, actual);
            assert_eq!(state.documents[&uri].version, 1);
            assert_eq!(state.documents[&uri].text, "def newValue := 10\n");
            assert_eq!(state.inputs.modules["new"], actual);
            assert_eq!(state.inputs.module_names["new"], "new");
            assert!(state.inputs.retained["new"].saved);
            assert!(!state.inputs.dirty(&state.documents[&uri]));
            assert!(state.inputs.dependencies(&state.documents[&client].path).contains(&actual));
            assert!(!state.invalid.contains(&unsaved));
            state.invalid.clear(); // Model completion of this current saved refresh.
            assert!(!state.blocked(&client));
            state.update_document(&json!({"method":"textDocument/didChange","params":{"textDocument":{"uri":uri,"version":2},
                "contentChanges":[{"text":"def newValue := 20\n"}]}}), false).unwrap();
            assert!(state.inputs.dirty(&state.documents[&uri]));
            assert!(state.blocked(&client), "Normalized dependency stopped observing live edits");
            assert!(state.refresh_input(&state.documents[&client]).is_none());
        }

        #[test]
        fn slow_document_request_survives_independent_live_edits_and_noop_saves() {
            let mut session = Session::start();
            let client = session.client.clone();
            let independent =
                format!("file://{}", session.dir.path().join("Independent.lean").display());
            fs::write(session.dir.path().join("hold-goal"), "hold").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":130,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":client}}}));
            session.wait_file("goal-entered");
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":independent,"languageId":"lean4","version":1,"text":"example : True := by trivial\n"}}}));
            for version in 2..=8 {
                session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":independent,"version":version},
                    "contentChanges":[{"text":format!("example : True := by trivial\n-- {version}\n")}]} }));
                session.send(json!({"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":independent}}}));
            }
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":independent}}}));
            session.until(|m| {
                m["params"]["uri"] == independent
                    && m["params"]["version"] == 8
                    && m["params"]["diagnostics"] == json!([])
            });
            fs::remove_file(session.dir.path().join("hold-goal")).unwrap();
            assert_eq!(
                session.until(|m| m["id"] == 130)["result"]["goals"],
                json!(["old value 10"])
            );

            session.wait_file("goal-completed");
            fs::remove_file(session.dir.path().join("goal-entered")).unwrap();
            fs::remove_file(session.dir.path().join("goal-completed")).unwrap();
            fs::write(session.dir.path().join("hold-goal"), "hold").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":131,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":client}}}));
            session.wait_file("goal-entered");
            let local = session.local.clone();
            session.send(
                json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":local,"languageId":"lean4","version":1,"text":"def value := 20\n"}}}),
            );
            assert_eq!(session.until(|m| m["id"] == 131)["error"]["code"], CONTENT_MODIFIED);
            fs::remove_file(session.dir.path().join("hold-goal")).unwrap();
            session.wait_file("goal-completed");
            session.send(json!({"jsonrpc":"2.0","id":132,"method":"$/test/documentState","params":{"textDocument":{"uri":local}}}));
            assert_eq!(session.until(|m| m["id"] == 132)["result"]["text"], "def value := 20\n");
            assert_eq!(
                session.seen.iter().filter(|m| m["id"] == 131).count(),
                1,
                "Late dependent result escaped cancellation"
            );
            session.finish();
        }

        #[test]
        fn empty_external_writer_recovery_serves_new_docs_then_builds_local_imports() {
            let mut session = Session::start();
            let client = session.client.clone();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":client}}}));
            session
                .until(|m| m["params"]["uri"] == client && m["params"]["diagnostics"] == json!([]));
            fs::remove_file(session.dir.path().join("initialized-entered")).unwrap();
            fs::remove_file(session.dir.path().join("prepare-called")).unwrap();
            let busy = session.dir.path().join("busy-writer");
            fs::write(&busy, "writer").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":133,"method":"$/test/sessionState"}));
            assert_eq!(session.until(|m| m["id"] == 133)["error"]["code"], CONTENT_MODIFIED);
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            fs::remove_file(busy).unwrap();
            session.wait_file("initialized-entered");
            assert!(!session.dir.path().join("prepare-called").exists());
            assert_eq!(fs::read_to_string(session.dir.path().join("built-value")).unwrap(), "10");
            for uri in [
                format!("file://{}", session.dir.path().join("New.lean").display()),
                format!("file://{}", session.sdk_dir.path().join("Shared.lean").display()),
            ] {
                session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                    "uri":uri,"languageId":"lean4","version":1,"text":"example : True := by trivial\n"}}}));
                session.until(|m| {
                    m["params"]["uri"] == uri && m["params"]["diagnostics"] == json!([])
                });
            }
            assert!(
                !session.dir.path().join("prepare-called").exists(),
                "Import-free recovery prepared stale local outputs"
            );
            let imported = format!("file://{}", session.dir.path().join("Later.lean").display());
            let before = session.seen.len();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":imported,"languageId":"lean4","version":1,"text":"import Local\nexample : value = 10 := by decide\n"}}}));
            session.until(|m| {
                m["params"]["uri"] == imported
                    && m["params"]["diagnostics"][0]["message"]
                        == "current fake imported value is 20"
            });
            assert!(session.dir.path().join("prepare-called").exists());
            assert_eq!(fs::read_to_string(session.dir.path().join("built-value")).unwrap(), "20");
            assert!(
                session.seen[before..].iter().all(|m| !(m["params"]["uri"] == imported
                    && m["params"]["diagnostics"] == json!([]))),
                "New import consumed stale private output"
            );
            session.finish();
        }

        #[test]
        fn ordinary_saved_failure_recovers_already_open_source_diagnostics() {
            let mut session = Session::start();
            let local = session.local.clone();
            session.send(
                json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":local,"languageId":"lean4","version":1,"text":"def value := 10\n"}}}),
            );
            session
                .until(|m| m["params"]["uri"] == local && m["params"]["diagnostics"] == json!([]));
            fs::remove_file(session.dir.path().join("initialized-entered")).unwrap();
            let before = session.seen.len();
            fs::write(session.dir.path().join("stamp-block-race"), "hold").unwrap();
            fs::write(session.dir.path().join("Local.lean"), "def value := broken\n").unwrap();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":local,"version":2},
                "contentChanges":[{"text":"def value := broken\n"}]}}));
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":local}}}));
            session.wait_file("stamp-block-entered");
            fs::remove_file(session.dir.path().join("stamp-block-race")).unwrap();
            session.wait_file("build-failed");
            let own = session.until(|m| {
                m["params"]["uri"] == local
                    && m["params"]["version"] == 2
                    && m["params"]["diagnostics"][0]["message"] == "fake local source parse error"
            });
            assert_eq!(own["params"]["diagnostics"][0]["severity"], 1);
            session.wait_file("initialized-entered");
            session.send(json!({"jsonrpc":"2.0","id":110,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":session.client}}}));
            assert_eq!(session.until(|m| m["id"] == 110)["error"]["code"], CONTENT_MODIFIED);
            assert!(session.seen[before..].iter().all(|m| !(m["params"]["uri"] == session.client
                && m["method"] == "textDocument/publishDiagnostics"
                && m["params"]["diagnostics"] == json!([]))));
            session.finish();
        }

        #[test]
        fn external_writer_full_queue_progresses_to_shutdown_without_saved_reads() {
            let mut session = Session::start();
            let busy = session.dir.path().join("busy-writer");
            fs::write(&busy, "writer").unwrap();
            let client = session.client.clone();
            session.until(|m| {
                m["params"]["uri"] == client && m["params"]["diagnostics"][0]["source"] == "Anneal"
            });
            let stamps = session.source_stamps.load(Ordering::Relaxed);
            let mut input = session.input.try_clone().unwrap();
            let producer = thread::spawn(move || {
                for version in 2..=4097 {
                    write_message(&mut input, &json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":client,"version":version},
                        "contentChanges":[{"text":format!("import Middle\nexample : True := by trivial\n-- {version}\n")}]}})).unwrap();
                }
                write_message(&mut input, &json!({"jsonrpc":"2.0","id":111,"method":"shutdown"}))
                    .unwrap();
            });
            // A broken coordinator must not hang the test's socket/reader on
            // failure. Releasing this fallback gate makes its failure bounded.
            let fallback_busy = busy.clone();
            let fallback = thread::spawn(move || {
                thread::sleep(Duration::from_secs(3));
                let _ = fs::remove_file(fallback_busy);
            });
            let before = Instant::now();
            assert_eq!(session.until(|m| m["id"] == 111)["result"], Value::Null);
            let before_fallback = busy.exists();
            let elapsed = before.elapsed();
            let after_stamps = session.source_stamps.load(Ordering::Relaxed);
            session.send(json!({"jsonrpc":"2.0","method":"exit"}));
            producer.join().unwrap();
            session.join.take().unwrap().join().unwrap().unwrap();
            fallback.join().unwrap();
            assert!(before_fallback && elapsed < Duration::from_secs(3));
            assert_eq!(stamps, after_stamps, "Writer-suspended turns read saved inputs");
        }

        #[test]
        fn continuously_changing_saves_drain_full_queue_to_shutdown_exit_and_eof() {
            for termination in ["shutdown", "exit", "eof"] {
                let mut session = Session::start();
                let root = session.dir.path();
                fs::write(root.join("hold-build-value"), "20").unwrap();
                fs::write(root.join("hold-build-cancel-required"), "hold through lifetime check")
                    .unwrap();
                fs::write(root.join("spawn-build-child"), "child").unwrap();
                fs::write(root.join("Local.lean"), "def value := 20\n").unwrap();
                session.wait_file("child-ready-20");
                // Child readiness can precede the parent's SIGTERM handler.
                // The hold marker establishes that both handlers are ready.
                session.wait_file("build-held-20");
                let race = session.dir.path().join("stamp-mutate-always");
                fs::write(&race, "mutate each snapshot").unwrap();
                session.wait_file("stamp-mutated");
                let client = session.client.clone();
                let before_seen = session.seen.len();
                let mut input = session.input.try_clone().unwrap();
                let producer = thread::spawn(move || {
                    for version in 2..=4097 {
                        write_message(&mut input, &json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":client,"version":version},
                            "contentChanges":[{"text":format!("import Middle\nexample : True := by trivial\n-- {version}\n")}]} })).unwrap();
                    }
                    match termination {
                        "shutdown" => write_message(
                            &mut input,
                            &json!({"jsonrpc":"2.0","id":134,"method":"shutdown"}),
                        )
                        .unwrap(),
                        "exit" => {
                            write_message(&mut input, &json!({"jsonrpc":"2.0","method":"exit"}))
                                .unwrap()
                        }
                        "eof" => input.shutdown(std::net::Shutdown::Write).unwrap(),
                        _ => unreachable!(),
                    }
                });
                // Bound a failing scheduler without allowing its fallback to
                // satisfy the liveness oracle. Successful runs cancel the gate.
                let (release, gate) = mpsc::channel();
                let fallback_race = race.clone();
                let fallback = thread::spawn(move || {
                    if gate.recv_timeout(Duration::from_secs(3)).is_err() {
                        let _ = fs::remove_file(fallback_race);
                    }
                });
                let before = Instant::now();
                if termination == "shutdown" {
                    assert_eq!(session.until(|m| m["id"] == 134)["result"], Value::Null);
                    session.send(json!({"jsonrpc":"2.0","method":"exit"}));
                }
                let deadline = Instant::now() + Duration::from_secs(4);
                while !session.join.as_ref().unwrap().is_finished() {
                    assert!(
                        Instant::now() < deadline,
                        "{termination} did not end the save-racing session"
                    );
                    thread::sleep(Duration::from_millis(5));
                }
                session.join.take().unwrap().join().unwrap().unwrap();
                // SIGKILL is delivered to the group before the leader is
                // reaped, but a descendant may release its fd slightly later.
                // Include that bounded wait in the original three-second
                // no-fallback liveness requirement.
                wait_lifetime_released(session.dir.path(), "build-lifetime-20");
                wait_lifetime_released(session.dir.path(), "child-lifetime-20");
                let before_fallback = race.exists();
                let elapsed = before.elapsed();
                let _ = release.send(());
                fallback.join().unwrap();
                producer.join().unwrap();
                while let Some(message) = read_message(&mut session.output).unwrap() {
                    session.seen.push(message);
                }
                assert!(
                    before_fallback && elapsed < Duration::from_secs(3),
                    "{termination} depended on stable saved inputs"
                );
                let writer = fs::OpenOptions::new()
                    .read(true)
                    .write(true)
                    .open(session.dir.path().join(".fake-writer.lock"))
                    .unwrap();
                fs2::FileExt::try_lock_exclusive(&writer)
                    .expect("Terminated build retained its writer lease");
                assert!(
                    session.seen[before_seen..]
                        .iter()
                        .all(|m| !(m["method"] == "textDocument/publishDiagnostics"
                            && m["params"]["version"].as_i64().is_some_and(|v| v >= 2)
                            && m["params"]["diagnostics"] == json!([])))
                );
            }
        }

        #[test]
        fn suspended_sdk_open_uses_immutable_lookup_and_preserves_live_replay() {
            let mut session = Session::start();
            let sdk = format!("file://{}", session.sdk_dir.path().join("Shared.lean").display());
            let open_sdk = json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":sdk,"languageId":"lean4","version":1,"text":"example : True := by trivial\n"}}});
            session.send(open_sdk.clone());
            session.until(|m| m["params"]["uri"] == sdk && m["params"]["diagnostics"] == json!([]));
            assert_eq!(session.source_admissions.load(Ordering::Relaxed), 1);
            fs::write(session.dir.path().join("busy-writer"), "writer").unwrap();
            let client = session.client.clone();
            session.until(|m| {
                m["params"]["uri"] == client && m["params"]["diagnostics"][0]["source"] == "Anneal"
            });
            let before = session.seen.len();
            let stamps = session.source_stamps.load(Ordering::Relaxed);
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":sdk}}}));
            session.send(open_sdk);
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":client,"version":2},
                "contentChanges":[{"text":"import Middle\nexample : middle = 10 := by decide\n-- suspended live edit\n"}]}}));
            session.send(json!({"jsonrpc":"2.0","id":122,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":client}}}));
            assert_eq!(session.until(|m| m["id"] == 122)["error"]["code"], CONTENT_MODIFIED);
            assert_eq!(
                session.source_admissions.load(Ordering::Relaxed),
                1,
                "Suspended SDK open ran workspace admission"
            );
            assert_eq!(session.immutable_lookups.load(Ordering::Relaxed), 1);
            assert_eq!(session.source_stamps.load(Ordering::Relaxed), stamps);
            assert!(
                session.seen[before..]
                    .iter()
                    .all(|m| m["method"] != "textDocument/publishDiagnostics"
                        || m["params"]["diagnostics"] != json!([])
                        || m["params"]["uri"] == sdk)
            );
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            fs::remove_file(session.dir.path().join("busy-writer")).unwrap();
            session.until(|m| m["params"]["uri"] == sdk && m["params"]["diagnostics"] == json!([]));
            if !session.seen.iter().any(|m| {
                m["params"]["uri"] == client
                    && m["params"]["version"] == 2
                    && m["params"]["diagnostics"][0]["message"]
                        == "current fake imported value is 20"
            }) {
                session.until(|m| {
                    m["params"]["uri"] == client
                        && m["params"]["version"] == 2
                        && m["params"]["diagnostics"][0]["message"]
                            == "current fake imported value is 20"
                });
            }
            let replays = fs::read_to_string(session.dir.path().join("replays.jsonl")).unwrap();
            assert!(replays.lines().map(|line| serde_json::from_str::<Value>(line).unwrap()).any(
                |doc| doc["uri"] == client
                    && doc["version"] == 2
                    && doc["text"].as_str().unwrap().contains("suspended live edit")
            ));
            session.finish();
        }

        #[test]
        fn prioritized_shutdown_still_forwards_outstanding_server_request_reply() {
            let mut session = Session::start();
            session.send(json!({"jsonrpc":"2.0","id":112,"method":"$/test/requestConfiguration"}));
            let configuration = session.until(|m| m["method"] == "workspace/configuration");
            session.until(|m| m["id"] == 112);
            fs::write(session.dir.path().join("stamp-block-race"), "hold").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":configuration["id"],"result":[]}));
            session.wait_file("stamp-block-entered");
            session.send(json!({"jsonrpc":"2.0","id":113,"method":"shutdown"}));
            fs::remove_file(session.dir.path().join("stamp-block-race")).unwrap();
            assert_eq!(session.until(|m| m["id"] == 113)["result"], Value::Null);
            session.wait_file("shutdown-before-configuration-reply");
            session.wait_file("configuration-replied");
            session.send(json!({"jsonrpc":"2.0","method":"exit"}));
            session.join.take().unwrap().join().unwrap().unwrap();
        }

        #[test]
        fn prioritized_shutdown_forwards_queued_live_server_request_then_its_reply() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("hold-configuration"), "hold").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":123,"method":"$/test/requestConfiguration"}));
            session.wait_file("configuration-entered");
            fs::write(session.dir.path().join("stamp-block-race"), "hold").unwrap();
            fs::remove_file(session.dir.path().join("hold-configuration")).unwrap();
            // The incoming server request is retained at its snapshot check.
            // A gated race lets shutdown overtake it before client remapping.
            session.wait_file("stamp-block-entered");
            session.send(json!({"jsonrpc":"2.0","id":124,"method":"shutdown"}));
            fs::remove_file(session.dir.path().join("stamp-block-race")).unwrap();
            let configuration = session.until(|m| m["method"] == "workspace/configuration");
            session.wait_file("shutdown-before-configuration-reply");
            session.send(json!({"jsonrpc":"2.0","id":configuration["id"],"result":[]}));
            assert_eq!(session.until(|m| m["id"] == 124)["result"], Value::Null);
            session.wait_file("configuration-replied");
            assert!(
                session.seen.iter().filter(|m| m["id"] == 123).all(|m| m.get("result").is_none())
            );
            session.send(json!({"jsonrpc":"2.0","method":"exit"}));
            session.join.take().unwrap().join().unwrap().unwrap();
        }

        #[test]
        fn blocked_import_rejects_stale_server_apply_edit_with_backend_response() {
            let mut session = Session::start();
            let root = session.dir.path().to_path_buf();
            let local = session.local.clone();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{
                "textDocument":{"uri":local,"languageId":"lean4","version":1,
                    "text":"def value := 10\n"}}}));
            session.until(|m| {
                m["method"] == "textDocument/publishDiagnostics"
                    && m["params"]["uri"] == local
                    && m["params"]["version"] == 1
            });
            fs::write(root.join("apply-edit-on-change"), &session.client).unwrap();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                "textDocument":{"uri":local,"version":2},"contentChanges":[{
                    "text":"def value := 20\n"}]}}));
            session.wait_file("apply-edit-replied");
            let response: Value =
                serde_json::from_slice(&fs::read(root.join("apply-edit-replied")).unwrap())
                    .unwrap();
            assert_eq!(response["id"], "fake-apply-edit");
            assert_eq!(response["result"]["applied"], false);
            session.send(json!({"jsonrpc":"2.0","id":202,"method":"$/test/sessionState"}));
            session.until(|m| m["id"] == 202);
            assert!(session.seen.iter().all(|m| m["method"] != "workspace/applyEdit"));
            session.finish();
        }

        #[test]
        fn current_server_apply_edit_still_maps_client_reply_to_backend() {
            let mut session = Session::start_document_with(
                "Client.lean",
                0,
                Some("example : True := by trivial\n"),
            );
            let local = session.local.clone();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{
                "textDocument":{"uri":local,"languageId":"lean4","version":1,
                    "text":"def value := 10\n"}}}));
            session.until(|m| {
                m["method"] == "textDocument/publishDiagnostics"
                    && m["params"]["uri"] == local
                    && m["params"]["version"] == 1
            });
            fs::write(session.dir.path().join("apply-edit-on-change"), &session.client).unwrap();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                "textDocument":{"uri":local,"version":2},"contentChanges":[{
                    "text":"def value := 20\n"}]}}));
            let edit = session.until(|m| m["method"] == "workspace/applyEdit");
            assert!(edit["id"].as_str().is_some_and(|id| id.starts_with("anneal-server-")));
            session.send(json!({"jsonrpc":"2.0","id":edit["id"],"result":{"applied":true}}));
            session.wait_file("apply-edit-replied");
            let response: Value = serde_json::from_slice(
                &fs::read(session.dir.path().join("apply-edit-replied")).unwrap(),
            )
            .unwrap();
            assert_eq!(response["id"], "fake-apply-edit");
            assert_eq!(response["result"]["applied"], true);
            session.finish();
        }

        #[test]
        fn obsolete_held_build_cleans_child_group_before_replacement() {
            let mut session = Session::start();
            let root = session.dir.path();
            fs::write(root.join("hold-build-value"), "20").unwrap();
            fs::write(root.join("hold-build-cancel-required"), "hold through lifetime check")
                .unwrap();
            fs::write(root.join("spawn-build-child"), "child").unwrap();
            fs::write(root.join("Local.lean"), "def value := 20\n").unwrap();
            session.wait_file("child-ready-20");
            // Observe parent handler readiness before triggering cancellation.
            session.wait_file("build-held-20");
            fs::write(session.dir.path().join("Local.lean"), "def value := 30\n").unwrap();
            let before = Instant::now();
            let fresh = session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 30"
            });
            assert!(before.elapsed() < Duration::from_secs(3));
            assert_eq!(fresh["params"]["version"], 1);
            assert!(session.dir.path().join("hold-build-value").exists(), "Old hold was released");
            let cleanup: Value = serde_json::from_slice(
                &fs::read(session.dir.path().join("replacement-saw-cleanup")).unwrap(),
            )
            .unwrap();
            assert_eq!(cleanup, json!({"parent":true,"child":true}));
            assert!(
                session.seen.iter().all(|m| m["params"]["diagnostics"][0]["message"]
                    != "current fake imported value is 20")
            );
            session.finish();
        }

        #[test]
        fn future_version_barriers_survive_expected_saved_import_change_and_restart() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("hold-diagnostics-wait"), "hold").unwrap();
            for (id, method) in
                [(114, "textDocument/waitForDiagnostics"), (115, "$/lean/waitForILeans")]
            {
                session.send(json!({"jsonrpc":"2.0","id":id,"method":method,"params":{"uri":session.client,"version":2}}));
            }
            session.session_state(116);
            assert!(
                !session.dir.path().join("waits.jsonl").exists(),
                "Future wait reached captured-version backend early"
            );
            let text = "import Local\nexample : True := by trivial\n";
            fs::write(session.dir.path().join("Client.lean"), text).unwrap();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":session.client,"version":2},
                "contentChanges":[{"text":text}]}}));
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":session.client}}}));
            session.wait_file("diagnostics-wait-entered");
            // Wait for both diagnostic barriers to enter before releasing the
            // reporter; no ILean request may yet be vulnerable to an old final.
            let deadline = Instant::now() + Duration::from_secs(3);
            loop {
                let log = fs::read_to_string(session.dir.path().join("waits.jsonl")).unwrap();
                if log.lines().count() == 2 {
                    for row in log.lines().map(|line| serde_json::from_str::<Value>(line).unwrap())
                    {
                        assert_eq!(row["method"], "textDocument/waitForDiagnostics");
                        assert_eq!(row["captured"], 2);
                    }
                    break;
                }
                assert!(Instant::now() < deadline);
                thread::sleep(Duration::from_millis(10));
            }
            session.wait_file("older-finalization");
            fs::remove_file(session.dir.path().join("hold-diagnostics-wait")).unwrap();
            let mut replies = BTreeSet::new();
            while replies.len() < 2 {
                let reply = session.until(|m| m["id"] == 114 || m["id"] == 115);
                assert_eq!(reply["result"], json!({}));
                assert!(reply.get("error").is_none());
                replies.insert(reply["id"].as_i64().unwrap());
            }
            let log = fs::read_to_string(session.dir.path().join("waits.jsonl")).unwrap();
            let ileans = log
                .lines()
                .map(|line| serde_json::from_str::<Value>(line).unwrap())
                .find(|row| row["method"] == "$/lean/waitForILeans")
                .unwrap();
            assert_eq!(ileans["finalized"], 2, "ILean barrier skipped target finalization");
            session.finish();
        }

        #[test]
        fn future_wait_cancel_close_and_hidden_barrier_shutdown_retire_client_ids_once() {
            let mut session = Session::start();
            session.send(json!({"jsonrpc":"2.0","id":117,"method":"textDocument/waitForDiagnostics","params":{"uri":session.client,"version":100}}));
            session.send(json!({"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":117}}));
            assert_eq!(session.until(|m| m["id"] == 117)["error"]["code"], -32800);
            fs::write(session.dir.path().join("hold-diagnostics-wait"), "hold").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":118,"method":"$/lean/waitForILeans","params":{"uri":session.client,"version":1}}));
            session.wait_file("diagnostics-wait-entered");
            session.send(json!({"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":118}}));
            assert_eq!(session.until(|m| m["id"] == 118)["error"]["code"], -32800);
            fs::remove_file(session.dir.path().join("diagnostics-wait-entered")).unwrap();
            session.send(json!({"jsonrpc":"2.0","id":119,"method":"$/lean/waitForILeans","params":{"uri":session.client,"version":1}}));
            session.wait_file("diagnostics-wait-entered");
            session.send(json!({"jsonrpc":"2.0","id":120,"method":"shutdown"}));
            assert_eq!(session.until(|m| m["id"] == 119)["error"]["code"], CONTENT_MODIFIED);
            session.until(|m| m["id"] == 120);
            fs::remove_file(session.dir.path().join("hold-diagnostics-wait")).unwrap();
            session.send(json!({"jsonrpc":"2.0","method":"exit"}));
            session.join.take().unwrap().join().unwrap().unwrap();
            for id in [117, 118, 119] {
                assert_eq!(session.seen.iter().filter(|m| m["id"] == id).count(), 1);
            }
            assert!(
                session
                    .seen
                    .iter()
                    .all(|m| !m["id"].as_str().is_some_and(|id| id.starts_with("anneal-client-")))
            );

            let mut session = Session::start();
            session.send(json!({"jsonrpc":"2.0","id":121,"method":"textDocument/waitForDiagnostics","params":{"uri":session.client,"version":100}}));
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":session.client}}}));
            assert_eq!(session.until(|m| m["id"] == 121)["error"]["code"], CONTENT_MODIFIED);
            assert!(!session.dir.path().join("waits.jsonl").exists());
            session.finish();
        }

        #[test]
        fn zero_command_unsaved_refresh_keeps_output_preparation_untouched() {
            let text = "example : True := by trivial\n";
            let mut session = Session::start_document_with("New.lean", 0, Some(text));
            let deadline = Instant::now() + Duration::from_secs(3);
            for id in 101.. {
                assert!(Instant::now() < deadline, "No-command refresh did not become ready");
                session.send(json!({"jsonrpc":"2.0","id":id,"method":"$/test/documentState",
                    "params":{"textDocument":{"uri":session.client}}}));
                if session.until(|m| m["id"] == id)["result"]["text"] == text {
                    break;
                }
                thread::sleep(Duration::from_millis(10));
            }
            assert!(!session.dir.path().join("prepare-called").exists());
            assert!(!session.dir.path().join("New.lean").exists());
            session.finish();
        }

        #[test]
        fn independent_dirty_closure_does_not_starve_build_or_worker_refresh_during_typing() {
            let mut session = Session::start();
            let root = session.dir.path();
            fs::write(root.join("Other.lean"), "def other := 10\n").unwrap();
            fs::write(
                root.join("OtherClient.lean"),
                "import Other\nexample : other = 10 := by decide\n",
            )
            .unwrap();
            let other = format!("file://{}", root.join("OtherClient.lean").display());
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":other,"languageId":"lean4","version":1,"text":"import Other\nexample : other = 10 := by decide\n"}}}));
            session
                .until(|m| m["params"]["uri"] == other && m["params"]["diagnostics"] == json!([]));
            session.send(
                json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":session.local,"languageId":"lean4","version":1,"text":"def value := 10\n"}}}),
            );
            let local = session.local.clone();
            session
                .until(|m| m["params"]["uri"] == local && m["params"]["diagnostics"] == json!([]));
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":local,"version":2},
                "contentChanges":[{"text":"def value := 20\n"}]}}));
            let client = session.client.clone();
            session.until(|m| {
                m["params"]["uri"] == client && m["params"]["diagnostics"][0]["source"] == "Anneal"
            });
            let _ = fs::remove_file(session.dir.path().join("build-entered"));
            fs::write(session.dir.path().join("hold-build"), "hold").unwrap();
            fs::write(session.dir.path().join("Other.lean"), "def other := 20\n").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":91,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":other}}}));
            assert_eq!(session.until(|m| m["id"] == 91)["error"]["code"], CONTENT_MODIFIED);
            session.wait_file("build-entered");
            fs::write(session.dir.path().join("slow-stamp"), "slow").unwrap();
            for version in 3..=1026 {
                session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":local,"version":version},
                    "contentChanges":[{"text":format!("def value := {}\n-- unrelated typing\n", 20+version)}]}}));
            }
            fs::remove_file(session.dir.path().join("hold-build")).unwrap();
            let fresh = session.until(|m| {
                m["params"]["uri"] == other
                    && m["params"]["diagnostics"][0]["message"]
                        == "current fake independent value is 20"
            });
            assert_eq!(fresh["params"]["version"], 1);
            let applied: i64 = fs::read_to_string(session.dir.path().join("last-local-version"))
                .unwrap()
                .parse()
                .unwrap();
            assert!(applied < 1026, "Build/worker refresh waited for total client quiescence");
            fs::remove_file(session.dir.path().join("slow-stamp")).unwrap();
            session.send(json!({"jsonrpc":"2.0","id":92,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":session.client}}}));
            assert_eq!(session.until(|m| m["id"] == 92)["error"]["code"], CONTENT_MODIFIED);
            session.send(json!({"jsonrpc":"2.0","id":93,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":other}}}));
            assert_eq!(
                session.until(|m| m["id"] == 93)["result"]["goals"],
                json!(["old value 20"])
            );
            assert_eq!(
                fs::read_to_string(session.dir.path().join("Local.lean")).unwrap(),
                "def value := 10\n"
            );
            session.finish();
        }

        #[test]
        fn failed_external_writer_build_restores_own_errors_without_import_credit() {
            let mut session = Session::start();
            fs::remove_file(session.dir.path().join("initialized-entered")).unwrap();
            fs::write(session.dir.path().join("busy-writer"), "writer").unwrap();
            let client = session.client.clone();
            session.until(|m| {
                m["params"]["uri"] == client && m["params"]["diagnostics"][0]["source"] == "Anneal"
            });
            let before = session.seen.len();
            fs::write(session.dir.path().join("Local.lean"), "def value := broken\n").unwrap();
            fs::remove_file(session.dir.path().join("busy-writer")).unwrap();
            session.wait_file("build-failed");
            // The failed cycle must restore a worker without another saved
            // edit or successful build. It can explain a newly opened source.
            session.wait_file("initialized-entered");
            let local = session.local.clone();
            session.send(
                json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":local,"languageId":"lean4","version":1,"text":"def value := broken\n"}}}),
            );
            let own_error = session.until(|m| {
                m["params"]["uri"] == local
                    && m["params"]["diagnostics"][0]["message"] == "fake local source parse error"
            });
            assert_eq!(own_error["params"]["version"], 1);
            session.send(json!({"jsonrpc":"2.0","id":94,"method":"$/test/documentState","params":{"textDocument":{"uri":local}}}));
            assert_eq!(session.until(|m| m["id"] == 94)["result"]["text"], "def value := broken\n");
            session.send(json!({"jsonrpc":"2.0","id":95,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":session.client}}}));
            assert_eq!(session.until(|m| m["id"] == 95)["error"]["code"], CONTENT_MODIFIED);
            assert!(session.seen[before..].iter().all(|m| !(m["params"]["uri"] == client
                && m["method"] == "textDocument/publishDiagnostics"
                && m["params"]["diagnostics"] == json!([]))));
            session.finish();
        }

        #[test]
        fn shutdown_stops_wedged_hidden_initialization_and_responds_without_waiting() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("hold-initialize"), "hold").unwrap();
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            session.wait_file("initialize-entered");
            session.output.get_ref().set_read_timeout(Some(Duration::from_secs(2))).unwrap();
            let before = Instant::now();
            session.send(json!({"jsonrpc":"2.0","id":96,"method":"shutdown"}));
            assert_eq!(session.until(|m| m["id"] == 96)["result"], Value::Null);
            assert!(before.elapsed() < Duration::from_secs(1));
            session.send(json!({"jsonrpc":"2.0","method":"exit"}));
            session.join.take().unwrap().join().unwrap().unwrap();
            assert!(before.elapsed() < Duration::from_secs(2));
        }

        #[test]
        fn dependency_graph_is_not_committed_if_its_snapshot_changes_during_read() {
            let (dir, _, _, client) = fixture();
            let host = FakeHost {
                root: dir.path().to_owned(),
                source_stamps: Arc::new(AtomicUsize::new(0)),
                sdk_source: None,
                source_admissions: Arc::new(AtomicUsize::new(0)),
                immutable_lookups: Arc::new(AtomicUsize::new(0)),
            };
            let stamp = host.source_stamp().unwrap();
            let mut state =
                State::new(host.root.clone(), vec![host.root.clone()], stamp, false).unwrap();
            open(&mut state, &client, "import Middle\nexample : middle = 10 := by decide\n");
            let epoch = state.epoch;
            fs::write(host.root.join("Local.lean"), "def value := 20\n").unwrap();
            // The post-graph fingerprint observes a second save after the
            // first fingerprint and graph read. Neither partial graph is current.
            fs::write(host.root.join("stamp-mutate-at"), "3").unwrap();
            let race = reconcile_saved_inputs(&host, &mut state).unwrap_err();
            assert!(race.downcast_ref::<SourceStampChanged>().is_some());
            assert_eq!(state.stamp, stamp);
            assert_eq!(state.epoch, epoch);
            assert_eq!(state.inputs.texts[&host.root.join("Local.lean")], "def value := 10\n");
            assert!(reconcile_saved_inputs(&host, &mut state).unwrap());
            assert_eq!(state.inputs.texts[&host.root.join("Local.lean")], "def value := 30\n");
            assert!(state.blocked(&client));
        }

        #[test]
        fn startup_snapshot_retries_only_typed_direct_save_races() {
            let session = Session::start_document_with_races("Client.lean", 3);
            assert!(session.source_stamps.load(Ordering::Relaxed) >= 5);
            assert_eq!(fs::read_to_string(session.dir.path().join("stamp-races")).unwrap(), "0");
            session.finish();
        }

        #[test]
        fn snapshot_races_retain_queued_buffer_edits_and_reject_obsolete_goals() {
            let mut session = Session::start();
            session.send(json!({"jsonrpc":"2.0","id":81,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":session.client}}}));
            session.wait_file("goal-entered");
            fs::write(session.dir.path().join("stamp-races"), "3").unwrap();
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":session.client,"version":2},
                "contentChanges":[{"text":"import Middle\nexample : middle = 10 := by decide\n-- retained during save race\n"}]}}));
            assert_eq!(session.until(|m| m["id"] == 81)["error"]["code"], CONTENT_MODIFIED);
            let diagnostic = session.until(|m| {
                m["params"]["version"] == 2
                    && m["params"]["diagnostics"][0]["message"]
                        == "current fake imported value is 20"
            });
            assert_eq!(diagnostic["params"]["uri"], session.client);
            let replay: Value = serde_json::from_str(
                fs::read_to_string(session.dir.path().join("replays.jsonl"))
                    .unwrap()
                    .lines()
                    .last()
                    .unwrap(),
            )
            .unwrap();
            assert_eq!(replay["version"], 2);
            assert!(replay["text"].as_str().unwrap().contains("retained during save race"));
            assert!(session.session_state(82).get("result").is_some());
            session.finish();
        }

        #[test]
        fn build_and_hidden_initialize_results_retry_snapshot_races() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("race-build-finish"), "race").unwrap();
            fs::write(session.dir.path().join("race-initialize-result"), "race").unwrap();
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 20"
            });
            assert!(!session.dir.path().join("race-build-finish").exists());
            assert!(!session.dir.path().join("race-initialize-result").exists());
            assert_eq!(fs::read_to_string(session.dir.path().join("stamp-races")).unwrap(), "0");
            assert!(session.session_state(83).get("result").is_some());
            session.finish();
        }

        #[test]
        fn shutdown_preempts_queued_edits_when_snapshots_keep_racing() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("stamp-races"), "1000").unwrap();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":session.client,"version":2},
                "contentChanges":[{"text":"import Middle\nexample : True := by trivial\n"}]}}));
            session.until(|m| m["params"]["diagnostics"][0]["source"] == "Anneal");
            let before = Instant::now();
            session.finish();
            assert!(before.elapsed() < Duration::from_secs(3));
        }

        #[test]
        fn permanent_stamp_failure_terminates_instead_of_retrying() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("stamp-fatal"), "fatal").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":84,"method":"$/test/sessionState"}));
            let failure = session.join.take().unwrap().join().unwrap().unwrap_err();
            assert!(failure.to_string().contains("Permanent workspace admission failure"));
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
        fn process_scoped_notifications_reach_live_worker_without_replacement_replay() {
            let mut session = Session::start();
            let messages = [
                json!({"jsonrpc":"2.0","method":"$/lean/rpc/keepAlive","params":{
                    "uri":session.client,"sessionId":7}}),
                json!({"jsonrpc":"2.0","method":"$/lean/rpc/release","params":{
                    "uri":session.client,"sessionId":7,"refs":[]}}),
                json!({"jsonrpc":"2.0","method":"window/workDoneProgress/cancel","params":{
                    "token":"old-worker-progress"}}),
            ];
            for message in &messages {
                session.send(message.clone());
            }
            assert_eq!(session.session_state(151)["result"], json!(messages));
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 20"
            });
            assert_eq!(session.session_state(152)["result"], json!([]));
            session.finish();
        }

        #[test]
        fn stable_lean_watcher_registration_survives_replacements_and_late_client_reply() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("emit-watcher-registration"), "enabled").unwrap();
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            let registration = session.until(|m| m["method"] == "client/registerCapability");
            assert_eq!(registration["params"]["registrations"][0]["id"], "lean_watcher");
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 20"
            });
            fs::write(session.dir.path().join("Local.lean"), "def value := 30\n").unwrap();
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 30"
            });
            assert_eq!(
                session.seen.iter().filter(|m| m["method"] == "client/registerCapability").count(),
                1,
                "A pending client registration was duplicated across generations"
            );
            session.send(json!({"jsonrpc":"2.0","id":registration["id"],"result":null}));
            session.send(json!({"jsonrpc":"2.0","id":161,"method":"$/test/watcherReplyCount"}));
            assert_eq!(session.until(|m| m["id"] == 161)["result"], 1);
            fs::write(session.dir.path().join("Local.lean"), "def value := 40\n").unwrap();
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 40"
            });
            assert_eq!(
                session.seen.iter().filter(|m| m["method"] == "client/registerCapability").count(),
                1,
                "An accepted client registration was duplicated across generations"
            );
            session.send(json!({"jsonrpc":"2.0","id":162,"method":"$/test/watcherReplyCount"}));
            assert_eq!(session.until(|m| m["id"] == 162)["result"], 1);
            let requests =
                fs::read_to_string(session.dir.path().join("watcher-requests.jsonl")).unwrap();
            assert_eq!(requests.lines().count(), 3);
            session.finish();
        }

        #[test]
        fn rejected_lean_watcher_registration_can_retry_on_next_worker() {
            let mut session = Session::start();
            fs::write(session.dir.path().join("emit-watcher-registration"), "enabled").unwrap();
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            let first = session.until(|m| m["method"] == "client/registerCapability");
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 20"
            });
            session.send(json!({"jsonrpc":"2.0","id":first["id"],
                "error":{"code":-32603,"message":"watcher registration refused"}}));
            session.send(json!({"jsonrpc":"2.0","id":165,"method":"$/test/watcherReplyCount"}));
            assert_eq!(session.until(|m| m["id"] == 165)["result"], 1);
            fs::write(session.dir.path().join("Local.lean"), "def value := 30\n").unwrap();
            let second = session.until(|m| m["method"] == "client/registerCapability");
            assert_ne!(second["id"], first["id"]);
            session.send(json!({"jsonrpc":"2.0","id":second["id"],"result":null}));
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 30"
            });
            session.finish();
        }

        #[test]
        fn repeated_watched_file_events_do_not_accumulate_or_replay() {
            let mut session = Session::start();
            let changes = vec![json!({"uri":session.local,"type":2}); 384];
            let event = json!({"jsonrpc":"2.0","method":"workspace/didChangeWatchedFiles",
                "params":{"changes":changes}});
            let event_bytes = serde_json::to_vec(&event).unwrap().len();
            assert!(event_bytes < MAX_MESSAGE);
            let count = MAX_MESSAGE / event_bytes + 2;
            assert!(count * event_bytes > MAX_MESSAGE);
            for _ in 0..count {
                session.send(event.clone());
            }
            session.send(json!({"jsonrpc":"2.0","id":163,"method":"$/test/watchedEventCount"}));
            assert_eq!(session.until(|m| m["id"] == 163)["result"], json!(count));
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 20"
            });
            session.send(json!({"jsonrpc":"2.0","id":164,"method":"$/test/watchedEventCount"}));
            assert_eq!(session.until(|m| m["id"] == 164)["result"], 0);
            session.finish();
        }

        #[test]
        fn generation_reset_clears_closed_document_when_old_worker_holds_clear() {
            let mut session = Session::start();
            let root = session.dir.path().to_path_buf();
            fs::write(root.join("hold-build-value"), "20").unwrap();
            fs::write(root.join("hold-close-clear"), "hold").unwrap();
            fs::write(root.join("Local.lean"), "def value := 20\n").unwrap();
            session.wait_file("build-held-20");
            let client = session.client.clone();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didClose","params":{
                "textDocument":{"uri":client}}}));
            session.wait_file("close-clear-held");
            fs::remove_file(root.join("hold-build-value")).unwrap();
            let clear = session.until(|m| {
                m["method"] == "textDocument/publishDiagnostics"
                    && m["params"]["uri"] == client
                    && m["params"]["diagnostics"] == json!([])
            });
            assert_eq!(clear["params"]["version"], 1);
            // The coordinator clears the closed URI before the replacement
            // finishes hidden initialization. A fresh independent open reaches
            // only that replacement, so its diagnostics fence graceful shutdown.
            let local = session.local.clone();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{
                "textDocument":{"uri":local,"languageId":"lean4","version":1,
                    "text":"def value := 20\n"}}}));
            session.until(|m| {
                m["method"] == "textDocument/publishDiagnostics"
                    && m["params"]["uri"] == local
                    && m["params"]["version"] == 1
                    && m["params"]["diagnostics"] == json!([])
            });
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
            fs::remove_file(session.dir.path().join("initialized-entered")).unwrap();
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
            // This test exercises failed-build freshness, so complete recovery
            // before asking the live peer to perform a graceful shutdown/exit.
            session.wait_file("initialized-entered");
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
        fn obsolete_invalid_build_is_cancelled_for_new_saved_dependency_without_another_edit() {
            let mut session = Session::start();
            fs::remove_file(session.dir.path().join("build-entered")).unwrap();
            fs::write(session.dir.path().join("hold-build"), "hold").unwrap();
            fs::write(
                session.dir.path().join("hold-build-cancel-required"),
                "hold through lifetime check",
            )
            .unwrap();
            // The peer captures invalid source before waiting. A new save must
            // preempt this cycle instead of waiting for its obsolete failure.
            fs::write(session.dir.path().join("Local.lean"), "def value := by unknown\n").unwrap();
            session.wait_file("build-held-None");
            fs::write(session.dir.path().join("Local.lean"), "def value := 30\n").unwrap();
            session.send(json!({"jsonrpc":"2.0","id":45,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":session.client}}}));
            assert_eq!(session.until(|m| m["id"] == 45)["error"]["code"], CONTENT_MODIFIED);
            // Keep the old build held until cancellation releases its lifetime
            // lease. Only then let the replacement use the writer.
            wait_lifetime_released(session.dir.path(), "build-lifetime-None");
            fs::remove_file(session.dir.path().join("hold-build")).unwrap();
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

        #[test]
        fn failed_import_closure_does_not_hold_independent_or_shared_subset() {
            for shared in [false, true] {
                let mut session = Session::start();
                let root = session.dir.path().to_path_buf();
                fs::write(root.join("Other.lean"), "def other := 10\n").unwrap();
                let other = format!("file://{}", root.join("OtherClient.lean").display());
                session.send(json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                    "uri":other,"languageId":"lean4","version":1,
                    "text":"import Other\nexample : other = 10 := by decide\n"}}}));
                session.until(|m| {
                    m["params"]["uri"] == other && m["params"]["diagnostics"] == json!([])
                });
                if shared {
                    session.send(json!({"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                        "textDocument":{"uri":session.client,"version":2},"contentChanges":[{
                            "text":"import Middle\nimport Other\nexample : middle = 10 := by decide\n"}]}}));
                    let client = session.client.clone();
                    session.until(|m| {
                        m["params"]["uri"] == client
                            && m["params"]["version"] == 2
                            && m["params"]["diagnostics"] == json!([])
                    });
                }
                fs::write(root.join("fail-build-targets"), "+Local:olean\n").unwrap();
                fs::write(root.join("Local.lean"), "def value := 20\n").unwrap();
                fs::write(root.join("Other.lean"), "def other := 20\n").unwrap();
                let diagnostic = session.until(|m| {
                    m["params"]["uri"] == other
                        && m["params"]["diagnostics"][0]["message"]
                            == "current fake independent value is 20"
                });
                assert_eq!(diagnostic["params"]["version"], 1);
                session.send(json!({"jsonrpc":"2.0","id":190,"method":"$/lean/plainGoal",
                    "params":{"textDocument":{"uri":session.client}}}));
                assert_eq!(session.until(|m| m["id"] == 190)["error"]["code"], CONTENT_MODIFIED);
                let calls: Vec<Value> = fs::read_to_string(root.join("calls.jsonl"))
                    .unwrap()
                    .lines()
                    .map(|line| serde_json::from_str(line).unwrap())
                    .collect();
                assert!(
                    calls
                        .iter()
                        .any(|call| call["mode"] == "build"
                            && call["args"] == json!(["+Other:olean"]))
                );
                assert!(root.join("build-failed").exists());
                session.finish();
            }
        }

        #[test]
        fn later_build_reselects_successful_consumers_after_partial_output_failure() {
            let mut session = Session::start();
            let root = session.dir.path().to_path_buf();
            fs::write(root.join("Other.lean"), "def other := 10\n").unwrap();
            fs::write(root.join("D.lean"), "def d := 10\n").unwrap();
            let other = format!("file://{}", root.join("OtherClient.lean").display());
            session.send(
                json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":other,"languageId":"lean4","version":1,
                "text":"import Other\nexample : other = 10 := by decide\n"}}}),
            );
            session
                .until(|m| m["params"]["uri"] == other && m["params"]["diagnostics"] == json!([]));

            fs::write(root.join("fail-build-targets"), "+Local:olean\n").unwrap();
            fs::write(root.join("Local.lean"), "def value := 20\n").unwrap();
            fs::write(root.join("Other.lean"), "def other := 20\n").unwrap();
            session.until(|m| {
                m["params"]["uri"] == other
                    && m["params"]["diagnostics"][0]["message"]
                        == "current fake independent value is 20"
            });
            assert!(root.join("build-failed").exists());
            let prior_calls = fs::read_to_string(root.join("calls.jsonl")).unwrap().lines().count();

            // C is a new unsaved buffer; no saved source/stamp changes here.
            let c = format!("file://{}", root.join("CClient.lean").display());
            session.send(
                json!({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":c,"languageId":"lean4","version":1,
                "text":"import D\nexample : True := by trivial\n"}}}),
            );
            session.until(|m| m["params"]["uri"] == c && m["params"]["diagnostics"] == json!([]));
            let calls: Vec<Value> = fs::read_to_string(root.join("calls.jsonl"))
                .unwrap()
                .lines()
                .skip(prior_calls)
                .map(|line| serde_json::from_str(line).unwrap())
                .collect();
            let builds: Vec<_> = calls.iter().filter(|call| call["mode"] == "build").collect();
            assert_eq!(builds.len(), 2, "Later refresh retried or omitted a document closure");
            assert!(builds.iter().any(|call| call["args"] == json!(["+D:olean"])));
            assert!(builds.iter().any(|call| call["args"] == json!(["+Other:olean"])));
            assert!(
                builds
                    .iter()
                    .all(|call| !call["args"].as_array().unwrap().contains(&json!("+Local:olean")))
            );
            session.send(json!({"jsonrpc":"2.0","id":195,"method":"$/test/documentState",
                "params":{"textDocument":{"uri":other}}}));
            assert_eq!(session.until(|m| m["id"] == 195)["result"]["version"], 1);
            session.send(json!({"jsonrpc":"2.0","id":196,"method":"$/test/documentState",
                "params":{"textDocument":{"uri":session.client}}}));
            assert_eq!(session.until(|m| m["id"] == 196)["error"]["code"], CONTENT_MODIFIED);
            session.finish();
        }

        #[test]
        fn overlapping_roots_build_only_the_imported_alias() {
            let mut session = Session::start_document_with_roots(
                "Client.lean",
                0,
                Some("import Foo\nexample : True := by trivial\n"),
                true,
            );
            let root = session.dir.path().to_path_buf();
            fs::write(root.join("declared-targets"), "+Foo:olean\n").unwrap();
            fs::write(root.join("src/Foo.lean"), "def foo := 10\n").unwrap();
            let client = session.client.clone();
            session
                .until(|m| m["params"]["uri"] == client && m["params"]["diagnostics"] == json!([]));
            let calls: Vec<Value> = fs::read_to_string(root.join("calls.jsonl"))
                .unwrap()
                .lines()
                .map(|line| serde_json::from_str(line).unwrap())
                .collect();
            assert!(
                calls
                    .iter()
                    .any(|call| call["mode"] == "build" && call["args"] == json!(["+Foo:olean"]))
            );
            assert!(!root.join("build-failed").exists());
            session.finish();
        }

        #[test]
        fn deferred_notifications_reach_surviving_worker_once() {
            let mut session = Session::start();
            let client = session.client.clone();
            session.send(json!({"jsonrpc":"2.0","method":"textDocument/didClose",
                "params":{"textDocument":{"uri":client}}}));
            session
                .until(|m| m["params"]["uri"] == client && m["params"]["diagnostics"] == json!([]));
            session.send(json!({"jsonrpc":"2.0","method":"$/test/appendState",
                "params":{"value":"before"}}));
            assert_eq!(session.session_state(191)["result"].as_array().unwrap().len(), 1);
            let before = fs::read_to_string(session.dir.path().join("calls.jsonl"))
                .unwrap()
                .lines()
                .filter(|line| line.contains("\"serve\""))
                .count();
            fs::write(session.dir.path().join("stamp-races"), "2").unwrap();
            session.send(json!({"jsonrpc":"2.0","method":"workspace/didChangeConfiguration",
                "params":{"settings":{"test":9}}}));
            session.send(json!({"jsonrpc":"2.0","method":"$/test/appendState",
                "params":{"value":"during"}}));
            // A stable zero-document snapshot leaves this worker running.
            session.wait_file("deferred-during-received");
            let result = session.session_state(192)["result"].clone();
            assert_eq!(
                result,
                json!([
                    {"jsonrpc":"2.0","method":"$/test/appendState","params":{"value":"before"}},
                    {"jsonrpc":"2.0","method":"workspace/didChangeConfiguration","params":{"settings":{"test":9}}},
                    {"jsonrpc":"2.0","method":"$/test/appendState","params":{"value":"during"}}
                ])
            );
            let after = fs::read_to_string(session.dir.path().join("calls.jsonl"))
                .unwrap()
                .lines()
                .filter(|line| line.contains("\"serve\""))
                .count();
            assert_eq!(after, before);
            session.finish();
        }

        #[test]
        fn deferred_notifications_replay_to_replacement_once() {
            let mut session = Session::start();
            session.send(json!({"jsonrpc":"2.0","method":"$/test/appendState",
                "params":{"value":"before"}}));
            assert_eq!(session.session_state(193)["result"].as_array().unwrap().len(), 1);
            fs::write(session.dir.path().join("stamp-races"), "2").unwrap();
            session.send(json!({"jsonrpc":"2.0","method":"workspace/didChangeConfiguration",
                "params":{"settings":{"test":11}}}));
            fs::write(session.dir.path().join("Local.lean"), "def value := 20\n").unwrap();
            session.until(|m| {
                m["params"]["diagnostics"][0]["message"] == "current fake imported value is 20"
            });
            assert_eq!(
                session.session_state(194)["result"],
                json!([
                    {"jsonrpc":"2.0","method":"$/test/appendState","params":{"value":"before"}},
                    {"jsonrpc":"2.0","method":"workspace/didChangeConfiguration","params":{"settings":{"test":11}}}
                ])
            );
            let serves = fs::read_to_string(session.dir.path().join("calls.jsonl"))
                .unwrap()
                .lines()
                .filter(|line| line.contains("\"serve\""))
                .count();
            assert!(serves >= 2);
            session.finish();
        }
    }
}
