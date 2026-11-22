// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Manages the private `0o700` staging directory, sanitized child `lean`
//! process invocation, toolchain and foundation-lock admission, `--setup`
//! compilation, and `TrustedBoundary.lean` JSON IPC transport.

#[cfg(unix)]
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    ffi::OsStr,
    fs, io,
    path::{Component, Path, PathBuf},
    process::{Command, Output},
    sync::{
        Arc, Mutex, OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
    time::Duration,
};

use serde::Deserialize;
use serde_json::json;

use crate::sandbox::{
    ActiveSandbox, DEFAULT_CHILD_TIMEOUT, MountSpec, PathMapper, SandboxMode, SandboxPolicy,
    SandboxRuntime, copy_readonly_file, create_dir_mode, make_tree_writable, set_mode,
    validate_and_promote_olean, validate_and_promote_olean_set, validate_inspector_result,
};
use crate::target::{TargetRole, is_bundled_theory_module};
use crate::toolchain::{
    AdmittedToolchain, FOUNDATION_AXIOMS, Failure, FoundationLock, ImportEdge, Json,
    LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256, LibraryLock, ModuleArtifacts, PARTS,
    ParallelDagPlan, TOOLCHAIN, default_lean_path, is_sha256_hex, regular, run_parallel_dag,
    scan_sysroot_package_roots, sha256_bytes, sha256_file, sha256_file_deref, stage_regular_file,
    transitive_import_closure, verify_installed_module_record, verify_sysroot_foundation_dir,
};

/// Cache key for precompiled `TrustedBoundary.olean` artifacts held in process
/// memory: `(lean_binary_sha256, canonical_sysroot_prefix, inspector_sha256)`.
type InspectorCacheKey = (String, PathBuf, String);

/// In-memory bytes and verified SHA-256 of Door-1-promoted
/// `TrustedBoundary.olean`.
#[derive(Debug)]
struct CompiledInspectorArtifacts {
    bytes: Vec<u8>,
    sha256: String,
}

type InspectorCacheSlot = Arc<Mutex<Option<Arc<CompiledInspectorArtifacts>>>>;
type InspectorCacheMap = BTreeMap<InspectorCacheKey, InspectorCacheSlot>;

/// Process-wide cache of compiled `TrustedBoundary` `.olean*` parts keyed by
/// admitted toolchain + inspector source digest. Each [`Checker`] materializes
/// the bytes into its own private `0o700` stage directory so no `/tmp`
/// directories outlive a run and concurrent callers never share writable paths.
fn compiled_inspector_cache() -> &'static Mutex<InspectorCacheMap> {
    static CACHE: OnceLock<Mutex<InspectorCacheMap>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(BTreeMap::new()))
}

/// Fields needed from Lean's JSON diagnostic stream, not inspector JSON IPC.
#[derive(Deserialize)]
struct LeanCompileDiagnostic {
    severity: LeanDiagnosticSeverity,
    kind: String,
    data: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum LeanDiagnosticSeverity {
    Information,
    Warning,
    Error,
}

// Exit 1 alone is ambiguous: the pinned runtime prints "INTERNAL PANIC" to
// stderr and then calls std::exit(1), including on native allocation failure.
// https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/runtime/object.cpp
// Lean's --json option instead reports frontend messages as JSON, "one per
// line". Require a complete diagnostic stream with an error and no stderr;
// an earlier type error must not hide a later native failure on stderr.
// https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Shell.lean#L172
//
// This is a conservative UX classification, not proof that a claim is false
// or a complete taxonomy of compiler defects. Both failure classes reject
// the run. Unknown output remains operational. Lean tags frontend resource
// limits as runtime.*, but kernel exceptions become anonymous messages with
// a "(kernel)" prefix; conservatively classify every kernel diagnostic as
// operational, including kernel type errors, rather than infer its cause.
// https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/CoreM.lean#L479-L485
// https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Message.lean#L867-L893
fn reports_frontend_rejection(output: &Output) -> bool {
    if output.status.code() != Some(1) || !output.stderr.is_empty() {
        return false;
    }
    let Ok(stdout) = std::str::from_utf8(&output.stdout) else {
        return false;
    };
    let mut has_error = false;
    for line in stdout.lines() {
        let Ok(diagnostic) = serde_json::from_str::<LeanCompileDiagnostic>(line) else {
            return false;
        };
        if diagnostic.kind.is_empty()
            || diagnostic.kind.trim_start_matches("nested.").starts_with("runtime.")
            || diagnostic.data.starts_with("(kernel)")
        {
            return false;
        }
        has_error |= matches!(diagnostic.severity, LeanDiagnosticSeverity::Error);
    }
    has_error
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InspectorErrResponse {
    ok: bool,
    category: String,
    message: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InspectorOkResponse {
    ok: bool,
    result: serde_json::Map<String, Json>,
}

fn check_lean_output(
    label: &str,
    output: Output,
    ordinary_rejection: bool,
) -> Result<String, Failure> {
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        // Keep both streams: a frontend error can precede a runtime failure,
        // and dropping either stream hides that distinction.
        let detail = format!("stdout:\n{}\nstderr:\n{}", stdout.trim(), stderr.trim());
        let code =
            if ordinary_rejection && reports_frontend_rejection(&output) { 1 } else { 2 };
        return Err(Failure::new(
            code,
            label,
            format!("Lean exited {:?}: {detail}", output.status.code()),
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|e| Failure::new(2, label, format!("invalid UTF-8 from Lean: {e}")))
}

fn write_setup_json_to_path(
    setup_path: &Path,
    adm: &AdmittedToolchain,
    module: &str,
    imports: &[ImportEdge],
    mapper: Option<&PathMapper>,
) -> Result<(), Failure> {
    let closure = transitive_import_closure(&adm.graph, imports);
    let mut import_arts: BTreeMap<&str, [Vec<String>; 2]> = BTreeMap::new();
    for dep in &closure {
        let (key, arts) = adm.artifacts.get_key_value(dep.as_str()).ok_or_else(|| {
            Failure::operational("setup", format!("missing artifact for import {dep}"))
        })?;
        let [oleans, irs] = arts.to_wire();
        let map_list = |list: &[String]| -> Result<Vec<String>, Failure> {
            match mapper {
                Some(m) => list.iter().map(|p| m.map_str(Path::new(p))).collect(),
                None => Ok(list.to_vec()),
            }
        };
        import_arts.insert(key.as_str(), [map_list(oleans)?, map_list(irs)?]);
    }
    let setup_obj = json!({
        "name": module,
        "isModule": false,
        "imports": imports,
        "importArts": import_arts,
        "dynlibs": [],
        "plugins": [],
        "options": {},
    });
    let bytes =
        serde_json::to_vec(&setup_obj).map_err(|e| Failure::new(2, "setup", e.to_string()))?;
    if setup_path.symlink_metadata().is_ok() {
        fs::remove_file(setup_path).map_err(|e| Failure::new(2, "setup", e.to_string()))?;
    }
    fs::write(setup_path, bytes).map_err(|e| Failure::new(2, "setup", e.to_string()))?;
    set_mode(setup_path, 0o444)?;
    Ok(())
}

fn build_lean_compile_args(
    setup_path: &Path,
    output: &Path,
    src_path: &Path,
    mem_limit_mb: u32,
    warn_as_err: bool,
    target_rejection: bool,
) -> Vec<String> {
    let mut compile_args = vec![
        "-j1".to_string(),
        format!("-M{mem_limit_mb}"),
        "-t0".to_string(),
        "-DElab.async=false".to_string(),
        "-Ddebug.skipKernelTC=false".to_string(),
    ];
    if target_rejection {
        // Only compilation uses the diagnostic protocol. Inspector modes
        // have their own explicit JSON response and failure categories.
        compile_args.push("--json".to_string());
    }
    if warn_as_err {
        compile_args.push("-DwarningAsError=true".to_string());
    }
    compile_args.extend([
        "--setup".to_string(),
        setup_path.to_string_lossy().into_owned(),
        "-o".to_string(),
        output.to_string_lossy().into_owned(),
        src_path.to_string_lossy().into_owned(),
    ]);
    compile_args
}

fn collect_compiled_artifacts(module: &str, output: &Path) -> Result<ModuleArtifacts, Failure> {
    let stem = output
        .file_name()
        .unwrap()
        .to_string_lossy()
        .strip_suffix("olean")
        .unwrap()
        .to_string();
    let parent = output.parent().unwrap();
    let mut available: BTreeMap<&str, String> = BTreeMap::new();
    for part in PARTS {
        let artifact = parent.join(format!("{stem}{part}"));
        if fs::symlink_metadata(&artifact).is_ok() {
            regular(&artifact, "compile")?;
            available.insert(part, artifact.to_string_lossy().into_owned());
        }
    }
    ModuleArtifacts::from_available(&available, "compile", || {
        format!("compiler omitted output for {module}")
    })
}

fn is_retained_environment_key(key: &str) -> bool {
    matches!(key, "HOME" | "TMPDIR" | "LANG" | "LC_ALL")
}

/// Extract top-level `default_toolchain = "..."` from an `elan` `settings.toml`
/// file without external TOML dependencies.
fn parse_elan_default_toolchain(contents: &str) -> Option<String> {
    for raw_line in contents.lines() {
        let mut cut = raw_line.len();
        let mut in_double = false;
        let mut in_single = false;
        let mut escaped = false;
        for (idx, ch) in raw_line.char_indices() {
            if escaped {
                escaped = false;
                continue;
            }
            if in_double && ch == '\\' {
                escaped = true;
                continue;
            }
            if !in_single && ch == '"' {
                in_double = !in_double;
            } else if !in_double && ch == '\'' {
                in_single = !in_single;
            } else if !in_double && !in_single && ch == '#' {
                cut = idx;
                break;
            }
        }
        let line = raw_line[..cut].trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') {
            break;
        }
        let Some((key, val_raw)) = line.split_once('=') else {
            continue;
        };
        if key.trim() != "default_toolchain" {
            continue;
        }
        let val = val_raw.trim();
        let parsed = if let Some(inner) = val.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
            let mut out = String::with_capacity(inner.len());
            let mut chars = inner.chars();
            while let Some(c) = chars.next() {
                if c == '\\' {
                    match chars.next()? {
                        '"' => out.push('"'),
                        '\\' => out.push('\\'),
                        _ => return None,
                    }
                } else if c == '"' {
                    return None;
                } else {
                    out.push(c);
                }
            }
            out
        } else {
            let inner = val.strip_prefix('\'').and_then(|s| s.strip_suffix('\''))?;
            if inner.contains('\'') {
                return None;
            }
            inner.to_string()
        };
        let trimmed = parsed.trim();
        return (!trimmed.is_empty()).then(|| trimmed.to_string());
    }
    None
}

/// Candidate directory names under `<elan_home>/toolchains/` for a validated
/// `default_toolchain` identifier.
fn elan_toolchain_dir_candidates(spec: &str) -> Result<Vec<String>, Failure> {
    let spec = spec.trim();
    if spec.is_empty()
        || spec.starts_with('-')
        || spec.contains('\0')
        || spec.contains('\\')
        || spec == "."
        || spec == ".."
        || spec.contains("..")
    {
        return Err(Failure::new(
            2,
            "toolchain",
            format!("invalid elan default_toolchain identifier: {spec:?}"),
        ));
    }
    let encoded = spec.replace('/', "--").replace(':', "---");
    let mut comps = Path::new(&encoded).components();
    if !matches!(comps.next(), Some(Component::Normal(_))) || comps.next().is_some() {
        return Err(Failure::new(
            2,
            "toolchain",
            format!("invalid elan toolchain directory name: {encoded:?}"),
        ));
    }
    let mut out = vec![encoded];
    if !spec.contains('/') && !spec.contains(':') {
        if spec.starts_with(|c: char| c.is_ascii_digit()) {
            let v_prefixed = format!("leanprover--lean4---v{spec}");
            if !out.contains(&v_prefixed) {
                out.push(v_prefixed);
            }
        }
        let full = format!("leanprover--lean4---{spec}");
        if !out.contains(&full) {
            out.push(full);
        }
    }
    Ok(out)
}

fn try_resolve_sysroot_candidate(cand_bin: &Path) -> Result<Option<(PathBuf, PathBuf)>, Failure> {
    let Some(bin_dir) = cand_bin.parent() else {
        return Ok(None);
    };
    if bin_dir.file_name() != Some(OsStr::new("bin")) {
        return Ok(None);
    }
    let Some(cand_prefix) = bin_dir.parent() else {
        return Ok(None);
    };
    let prefix_lean = cand_prefix.join("bin/lean");
    if !fs::metadata(&prefix_lean).is_ok_and(|m| m.is_file())
        || !fs::metadata(cand_prefix.join("lib/lean")).is_ok_and(|m| m.is_dir())
    {
        return Ok(None);
    }
    let canon_cand = fs::canonicalize(cand_bin).map_err(|e| {
        Failure::new(
            2,
            "toolchain",
            format!("cannot canonicalize {}: {e}", cand_bin.display()),
        )
    })?;
    let canon_prefix_lean = fs::canonicalize(&prefix_lean).map_err(|e| {
        Failure::new(
            2,
            "toolchain",
            format!("cannot canonicalize {}: {e}", prefix_lean.display()),
        )
    })?;
    if canon_cand != canon_prefix_lean {
        return Ok(None);
    }
    let prefix = fs::canonicalize(cand_prefix).map_err(|e| {
        Failure::new(
            2,
            "toolchain",
            format!("cannot resolve prefix {}: {e}", cand_prefix.display()),
        )
    })?;
    Ok(Some((prefix, canon_prefix_lean)))
}

fn try_resolve_elan_proxy_candidate(
    self_lean: &Path,
    cand_bin: &Path,
) -> Result<Option<(PathBuf, PathBuf)>, Failure> {
    if self_lean.file_name() != Some(OsStr::new("lean")) {
        return Ok(None);
    }
    if !matches!(
        cand_bin.file_name().and_then(OsStr::to_str),
        Some("lean" | "elan")
    ) {
        return Ok(None);
    }
    let Some(bin_dir) = cand_bin.parent() else {
        return Ok(None);
    };
    if bin_dir.file_name() != Some(OsStr::new("bin")) {
        return Ok(None);
    }
    let Some(elan_home) = bin_dir.parent() else {
        return Ok(None);
    };
    let toolchains_dir = elan_home.join("toolchains");
    let settings_path = elan_home.join("settings.toml");
    if !fs::metadata(&toolchains_dir).is_ok_and(|m| m.is_dir())
        || !fs::metadata(&settings_path).is_ok_and(|m| m.is_file())
    {
        return Ok(None);
    }
    let settings = fs::read_to_string(&settings_path).map_err(|e| {
        Failure::new(
            2,
            "toolchain",
            format!("cannot read {}: {e}", settings_path.display()),
        )
    })?;
    let Some(default_tc) = parse_elan_default_toolchain(&settings) else {
        return Err(Failure::new(
            2,
            "toolchain",
            format!(
                "elan proxy {} has no default_toolchain in {}; pass <toolchain>/bin/lean directly",
                self_lean.display(),
                settings_path.display()
            ),
        ));
    };
    for dir_name in elan_toolchain_dir_candidates(&default_tc)? {
        let tc_dir = toolchains_dir.join(&dir_name);
        let tc_lean = tc_dir.join("bin/lean");
        if fs::metadata(&tc_lean).is_ok_and(|m| m.is_file())
            && fs::metadata(tc_dir.join("lib/lean")).is_ok_and(|m| m.is_dir())
        {
            let prefix = fs::canonicalize(&tc_dir).map_err(|e| {
                Failure::new(
                    2,
                    "toolchain",
                    format!("cannot resolve prefix {}: {e}", tc_dir.display()),
                )
            })?;
            let exec_lean = fs::canonicalize(&tc_lean).map_err(|e| {
                Failure::new(
                    2,
                    "toolchain",
                    format!("cannot canonicalize {}: {e}", tc_lean.display()),
                )
            })?;
            return Ok(Some((prefix, exec_lean)));
        }
    }
    Err(Failure::new(
        2,
        "toolchain",
        format!(
            "elan default_toolchain {default_tc:?} from {} is not installed under {}",
            settings_path.display(),
            toolchains_dir.display()
        ),
    ))
}

/// Resolve `(canon_prefix, canon_exec_lean)` statically on disk without
/// executing any child process so unpinned admission under `ExecSeal` never
/// runs an untrusted launcher unsandboxed on the host.
fn resolve_static_unpinned_toolchain(lean: &Path) -> Result<(PathBuf, PathBuf), Failure> {
    let meta = fs::metadata(lean).map_err(|e| {
        Failure::new(
            2,
            "toolchain",
            format!("could not inspect Lean binary {}: {e}", lean.display()),
        )
    })?;
    if !meta.is_file() {
        return Err(Failure::new(
            2,
            "toolchain",
            format!("Lean path {} is not a regular file", lean.display()),
        ));
    }
    #[cfg(unix)]
    if (meta.permissions().mode() & 0o111) == 0 {
        return Err(Failure::new(
            2,
            "toolchain",
            format!("Lean binary {} is not executable", lean.display()),
        ));
    }
    let canon_lean = fs::canonicalize(lean).map_err(|e| {
        Failure::new(
            2,
            "toolchain",
            format!("cannot canonicalize {}: {e}", lean.display()),
        )
    })?;
    if let Some(resolved) = try_resolve_sysroot_candidate(lean)? {
        return Ok(resolved);
    }
    if canon_lean != lean
        && let Some(resolved) = try_resolve_sysroot_candidate(&canon_lean)?
    {
        return Ok(resolved);
    }
    if let Some(resolved) = try_resolve_elan_proxy_candidate(lean, lean)? {
        return Ok(resolved);
    }
    if canon_lean != lean
        && let Some(resolved) = try_resolve_elan_proxy_candidate(lean, &canon_lean)?
    {
        return Ok(resolved);
    }
    Err(Failure::new(
        2,
        "toolchain",
        format!(
            "cannot statically resolve unpinned Lean sysroot from {} under ExecSeal containment; \
             pass <prefix>/bin/lean directly or opt out of containment with \
             --allow-unsandboxed-elaboration",
            lean.display()
        ),
    ))
}

/// Executes Lean 4.34.1 compilation and `TrustedBoundary.lean` inspection
/// inside a private `0o700` staging directory with optional OS containment
/// (`ExecSeal`).
pub struct Checker {
    _stage_dir: tempfile::TempDir,
    root: PathBuf,
    lean: PathBuf,
    pub(crate) stage: PathBuf,
    pub(crate) execution_began: bool,
    environment: BTreeMap<String, String>,
    counter: AtomicUsize,
    admitted: Option<AdmittedToolchain>,
    allow_unpinned_lean: bool,
    lean_memory_mb: Option<u32>,
    #[cfg(test)]
    expected_sysroot_manifest_sha256_for_test: Option<String>,
    sandbox_mode: SandboxMode,
    sandbox_runtime: Option<SandboxRuntime>,
    probed_backend: Option<ActiveSandbox>,
    child_timeout: Duration,
    pub(crate) olean_ledger: BTreeMap<PathBuf, String>,
    pub(crate) compiled_roles: BTreeMap<String, TargetRole>,
}

impl Drop for Checker {
    fn drop(&mut self) {
        // Restore write bits on `0o500`/`0o444` staging subtrees so
        // `TempDir::drop` always cleans up cleanly on Unix.
        make_tree_writable(&self.stage);
    }
}

impl Checker {
    /// Create a new [`Checker`] with a fresh private `0o700` staging directory.
    ///
    /// Discard unlisted environment entries before decoding their values. A
    /// retained value that is not valid UTF-8 returns an `InvalidInput` error.
    pub fn new(root: &Path, lean: Option<&Path>) -> io::Result<Self> {
        let environment = env::vars_os()
            .filter_map(|(key, value)| {
                let key = key.to_str()?;
                is_retained_environment_key(key).then(|| (key.to_owned(), value))
            })
            .map(|(key, value)| {
                let value = value.into_string().map_err(|_| {
                    io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("environment variable {key} is not valid UTF-8"),
                    )
                })?;
                Ok((key, value))
            })
            .collect::<io::Result<Vec<_>>>()?;
        Self::new_with_env(root, lean, environment)
    }

    /// Create a new [`Checker`] using a closed environment allowlist.
    ///
    /// Retains only `HOME`, `TMPDIR`, `LANG`, and `LC_ALL` from `ambient_env`
    /// and pins `PATH` to `/usr/bin:/bin` so ambient search paths (`LEAN_PATH`,
    /// `LEAN_SRC_PATH`), toolchain overrides (`ELAN_TOOLCHAIN`), or dynamic
    /// linker preloading (`LD_PRELOAD`, `LD_LIBRARY_PATH`,
    /// `DYLD_INSERT_LIBRARIES`) cannot influence child `lean` invocations.
    pub fn new_with_env<I>(root: &Path, lean: Option<&Path>, ambient_env: I) -> io::Result<Self>
    where
        I: IntoIterator<Item = (String, String)>,
    {
        let root = fs::canonicalize(root)?;
        let lean_raw = match lean {
            Some(p) => p.to_path_buf(),
            None => default_lean_path(),
        };
        let lean =
            if lean_raw.is_absolute() { lean_raw } else { env::current_dir()?.join(lean_raw) };
        let mut stage_builder = tempfile::Builder::new();
        stage_builder.prefix("anneal-trusted-");
        // Staged sources and proofs must not be readable by other Unix users.
        // Set permissions at creation, before any inputs reach the directory.
        #[cfg(unix)]
        stage_builder.permissions(fs::Permissions::from_mode(0o700));
        let stage_dir = stage_builder.tempdir()?;
        let stage =
            fs::canonicalize(stage_dir.path()).unwrap_or_else(|_| stage_dir.path().to_path_buf());

        let mut environment: BTreeMap<String, String> =
            ambient_env.into_iter().filter(|(k, _)| is_retained_environment_key(k)).collect();
        environment.insert("PATH".to_string(), "/usr/bin:/bin".to_string());

        Ok(Self {
            _stage_dir: stage_dir,
            root,
            lean,
            stage,
            execution_began: false,
            environment,
            counter: AtomicUsize::new(0),
            admitted: None,
            allow_unpinned_lean: false,
            lean_memory_mb: None,
            #[cfg(test)]
            expected_sysroot_manifest_sha256_for_test: None,
            sandbox_mode: SandboxMode::PreferBwrapOrLandlock,
            sandbox_runtime: None,
            probed_backend: None,
            child_timeout: DEFAULT_CHILD_TIMEOUT,
            olean_ledger: BTreeMap::new(),
            compiled_roles: BTreeMap::new(),
        })
    }

    #[cfg(test)]
    pub(crate) fn set_expected_sysroot_manifest_sha256_for_test(&mut self, sha: impl Into<String>) {
        self.expected_sysroot_manifest_sha256_for_test = Some(sha.into());
    }

    /// Configure OS-level elaborator containment mode (`ExecSeal`).
    pub fn set_sandbox_mode(&mut self, mode: SandboxMode) {
        if self.sandbox_mode != mode {
            self.sandbox_mode = mode;
            self.sandbox_runtime = None;
            self.probed_backend = None;
            if self.allow_unpinned_lean {
                self.admitted = None;
            }
        }
    }

    /// Return the configured [`SandboxMode`].
    pub fn sandbox_mode(&self) -> SandboxMode {
        self.sandbox_mode
    }

    /// Return the active [`ActiveSandbox`] once probed (or `Some(None)` when
    /// `SandboxMode::Unsandboxed` is configured).
    pub fn active_sandbox(&self) -> Option<ActiveSandbox> {
        if self.sandbox_mode == SandboxMode::Unsandboxed {
            Some(ActiveSandbox::None)
        } else {
            self.sandbox_runtime
                .as_ref()
                .map(|r| r.backend)
                .or(self.probed_backend)
        }
    }

    /// Configure the per-invocation wall-clock child timeout.
    pub fn set_child_timeout(&mut self, timeout: Duration) {
        assert!(!timeout.is_zero(), "child timeout must be positive");
        self.child_timeout = timeout;
    }

    /// Return the configured per-invocation wall-clock child timeout.
    #[doc(hidden)]
    pub fn child_timeout(&self) -> Duration {
        self.child_timeout
    }

    /// Configure an explicit Lean `-M` memory limit in MiB.
    ///
    /// Correspondence modes (`correspondence-preflight`,
    /// `correspondence-audit`) enforce an 8192 MiB floor, and unpinned
    /// `resolve-imports` enforces a 4096 MiB floor; module compilation and
    /// `target-audit` use the explicit override directly when set.
    pub fn set_lean_memory_limit_mb(&mut self, mb: Option<u32>) {
        assert!(mb.is_none_or(|m| m > 0), "Lean memory limit must be positive");
        self.lean_memory_mb = mb;
    }

    /// Configure whether unpinned Lean toolchain admission (`resolve-imports`,
    /// 6-module `{Init.Prelude, Init.Core}` foundation closure, nullable
    /// sysroot `sourceSha256`, and 4096 MB `resolve-imports` / `Std`-closure
    /// default memory caps) is permitted.
    pub fn set_allow_unpinned_lean(&mut self, allow: bool) {
        assert!(
            self.admitted.is_none() || self.allow_unpinned_lean == allow,
            "cannot change unpinned Lean admission policy after tool admission"
        );
        self.allow_unpinned_lean = allow;
    }

    /// Return whether unpinned Lean toolchain admission is enabled.
    pub fn allow_unpinned_lean(&self) -> bool {
        self.allow_unpinned_lean
    }

    /// Return the effective Lean memory cap in MiB for `mode`, combining the
    /// configured override with mode-specific floors and closure defaults.
    pub fn effective_lean_memory_limit_mb(&self, mode: Option<&str>) -> u32 {
        if matches!(mode, Some("correspondence-preflight" | "correspondence-audit")) {
            self.lean_memory_mb.map_or(8192, |mb| mb.max(8192))
        } else if matches!(mode, Some("resolve-imports" | "compile-inspector"))
            && self.allow_unpinned_lean
        {
            self.lean_memory_mb.map_or(4096, |mb| mb.max(4096))
        } else if let Some(mb) = self.lean_memory_mb {
            mb
        } else {
            self.default_lean_memory_limit_mb(mode)
        }
    }

    /// Return the default Lean memory cap in MiB for the active host policy,
    /// admitted library closure, and optional inspector mode.
    ///
    /// - Correspondence modes (`correspondence-preflight`,
    ///   `correspondence-audit`) default to 8192 MiB.
    /// - Unpinned `resolve-imports` runs before the library closure is known
    ///   and defaults to 4096 MiB so `Init`+`Std` import graphs do not OOM.
    /// - Compilation (`None`) and `target-audit` default to 4096 MiB whenever
    ///   the admitted library closure contains any `Std` module, and 2048 MiB
    ///   for `Init`-only runs.
    pub fn default_lean_memory_limit_mb(&self, mode: Option<&str>) -> u32 {
        if matches!(mode, Some("correspondence-preflight" | "correspondence-audit")) {
            8192
        } else if (mode == Some("resolve-imports") && self.allow_unpinned_lean)
            || self.admitted.as_ref().is_some_and(|adm| {
                adm.library_modules.iter().any(|m| m == "Std" || m.starts_with("Std."))
            })
        {
            4096
        } else {
            2048
        }
    }

    /// Return the canonicalized bundle or repository root directory.
    #[doc(hidden)]
    pub fn root(&self) -> &Path {
        &self.root
    }

    /// Return the path to the private `0o700` staging directory.
    #[doc(hidden)]
    pub fn stage(&self) -> &Path {
        &self.stage
    }

    /// Return the configured Lean executable path.
    #[doc(hidden)]
    pub fn lean(&self) -> &Path {
        &self.lean
    }

    /// Advance and return the monotonic atomic request/process counter.
    #[doc(hidden)]
    pub fn next_counter(&self) -> usize {
        self.counter.fetch_add(1, Ordering::Relaxed) + 1
    }

    /// Copy compiled `.olean`, `.olean.server`, and `.olean.private` files
    /// from `self.stage/lib` into `dest`, preserving subdirectories.
    ///
    /// Returns `Ok(false)` when `lib` does not exist (for example after an
    /// early preflight failure before compilation produced any artifacts).
    pub fn export_target_oleans(&self, dest: &Path) -> Result<bool, Failure> {
        self.export_target_oleans_gated(dest, true)
    }

    fn is_gated_authored_proof(&self, rel: &Path, include_authored_proofs: bool) -> bool {
        if include_authored_proofs {
            return false;
        }
        let Some(mod_name) = olean_rel_path_to_module_name(rel) else {
            return true;
        };
        self.compiled_roles.get(&mod_name) == Some(&TargetRole::Proof)
            && !is_bundled_theory_module(&mod_name)
    }

    /// Copy compiled target `.olean` artifacts from `self.stage/lib` into
    /// `dest`. When `include_authored_proofs` is `false` (for example on a
    /// `proof_failed` exit `1`), authored `Proof` modules (non-`Anneal.*`
    /// `TargetRole::Proof`) are omitted while `Model`, `Capture`,
    /// `Specification`, `Expected`, and bundled `Anneal.*` modules remain
    /// exported for interactive proof inspection.
    ///
    /// Export is atomic with respect to `dest`: any pre-existing directory at
    /// `dest` is removed upfront, every candidate and ledger entry is validated
    /// before copying, files are written into a sibling temporary staging
    /// directory (automatically removed on error), and `dest` is promoted via
    /// `fs::rename` only after all validations and copies succeed. On `Err`,
    /// `dest` is never left populated (and a pre-existing directory at `dest`
    /// is removed).
    pub fn export_target_oleans_gated(
        &self,
        dest: &Path,
        include_authored_proofs: bool,
    ) -> Result<bool, Failure> {
        // Validate `dest` path shape upfront before touching the filesystem:
        // trailing separators or `.` / `..` leaf components can cause POSIX
        // `lstat` and `remove_dir_all` to follow symlinks or target `/` / `.`.
        let raw_bytes = dest.as_os_str().as_encoded_bytes();
        let invalid_leaf = raw_bytes.is_empty()
            || raw_bytes
                .last()
                .is_some_and(|&b| std::path::is_separator(b as char))
            || raw_bytes == b"."
            || raw_bytes == b".."
            || raw_bytes.ends_with(b"/.")
            || raw_bytes.ends_with(b"/..")
            || raw_bytes.ends_with(b"\\.")
            || raw_bytes.ends_with(b"\\..")
            || !matches!(
                dest.components().next_back(),
                Some(std::path::Component::Normal(_))
            )
            || dest.file_name().is_none();
        let parent = match dest.parent() {
            Some(p) if !invalid_leaf => {
                if p.as_os_str().is_empty() {
                    Path::new(".")
                } else {
                    p
                }
            }
            _ => {
                return Err(Failure::operational(
                    "export-lean-lib",
                    format!("invalid export destination path {}", dest.display()),
                ));
            }
        };

        // Clear any stale export directory upfront so a subsequent validation
        // or copy failure cannot leave stale artifacts behind. Non-directory
        // destinations (such as a pre-existing regular file or symlink) fail
        // closed without modifying them.
        match fs::symlink_metadata(dest) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Err(e) => {
                return Err(Failure::operational(
                    "export-lean-lib",
                    format!("cannot inspect {}: {e}", dest.display()),
                ));
            }
            Ok(meta) if meta.file_type().is_symlink() || !meta.file_type().is_dir() => {
                return Err(Failure::operational(
                    "export-lean-lib",
                    format!("unexpected non-directory destination {}", dest.display()),
                ));
            }
            Ok(_) => {
                fs::remove_dir_all(dest).map_err(|e| {
                    Failure::operational(
                        "export-lean-lib",
                        format!("cannot clear existing {}: {e}", dest.display()),
                    )
                })?;
            }
        }

        let src = self.stage.join("lib");
        let expected_ledger_paths: BTreeSet<&Path> = self
            .olean_ledger
            .keys()
            .filter(|path| {
                path.strip_prefix(&src)
                    .map(|rel| !self.is_gated_authored_proof(rel, include_authored_proofs))
                    .unwrap_or(true)
            })
            .map(PathBuf::as_path)
            .collect();

        match fs::symlink_metadata(&src) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => {
                if let Some(missing) = expected_ledger_paths.iter().next() {
                    return Err(Failure::operational(
                        "export-lean-lib",
                        format!(
                            "promoted artifact {} missing before export",
                            missing.display()
                        ),
                    ));
                }
                return Ok(false);
            }
            Err(e) => {
                return Err(Failure::operational(
                    "export-lean-lib",
                    format!("cannot inspect {}: {e}", src.display()),
                ));
            }
            Ok(meta) if meta.file_type().is_symlink() || !meta.file_type().is_dir() => {
                return Err(Failure::operational(
                    "export-lean-lib",
                    format!("unexpected non-directory {}", src.display()),
                ));
            }
            Ok(_) => {}
        }

        // Phase 1: walk and validate every export candidate before staging or
        // copying any file. Every `.olean*` artifact in `lib` must carry a
        // Door-1 `olean_ledger` entry.
        let mut candidates: Vec<(PathBuf, PathBuf, &str)> = Vec::new();
        let mut validated_ledger: BTreeSet<PathBuf> = BTreeSet::new();
        for entry in walkdir::WalkDir::new(&src)
            .min_depth(1)
            .follow_links(false)
            .sort_by_file_name()
        {
            let entry =
                entry.map_err(|e| Failure::operational("export-lean-lib", e.to_string()))?;
            if entry.file_type().is_symlink() {
                return Err(Failure::operational(
                    "export-lean-lib",
                    format!("unexpected symlink in lib: {}", entry.path().display()),
                ));
            }
            if entry.file_type().is_dir() {
                continue;
            }
            if !entry.file_type().is_file() {
                return Err(Failure::operational(
                    "export-lean-lib",
                    format!(
                        "unexpected non-regular file in lib: {}",
                        entry.path().display()
                    ),
                ));
            }
            let Some(name) = entry.file_name().to_str() else {
                continue;
            };
            if !(name.ends_with(".olean")
                || name.ends_with(".olean.server")
                || name.ends_with(".olean.private"))
            {
                continue;
            }
            let rel = entry
                .path()
                .strip_prefix(&src)
                .map_err(|e| Failure::operational("export-lean-lib", e.to_string()))?;
            let Some(expected_sha) = self.olean_ledger.get(entry.path()).map(String::as_str) else {
                return Err(Failure::operational(
                    "export-lean-lib",
                    format!(
                        "unexpected unledgered artifact in lib: {}",
                        entry.path().display()
                    ),
                ));
            };
            if self.is_gated_authored_proof(rel, include_authored_proofs) {
                continue;
            }
            let actual_sha = sha256_file(entry.path(), "export-lean-lib")
                .map_err(|e| Failure::operational("export-lean-lib", e.message))?;
            if !actual_sha.eq_ignore_ascii_case(expected_sha) {
                return Err(Failure::operational(
                    "export-lean-lib",
                    format!(
                        "promoted artifact {} changed before export",
                        entry.path().display()
                    ),
                ));
            }
            validated_ledger.insert(entry.path().to_path_buf());
            candidates.push((entry.path().to_path_buf(), rel.to_path_buf(), expected_sha));
        }
        for ledger_path in expected_ledger_paths {
            if !validated_ledger.contains(ledger_path) {
                return Err(Failure::operational(
                    "export-lean-lib",
                    format!(
                        "promoted artifact {} missing before export",
                        ledger_path.display()
                    ),
                ));
            }
        }
        if candidates.is_empty() {
            return Ok(false);
        }

        // Phase 2: populate a sibling temporary staging directory on the same
        // filesystem, re-verify copied ledger hashes, and atomically rename to
        // `dest`. Dropping `staging` on any error deletes partial copies.
        fs::create_dir_all(parent).map_err(|e| {
            Failure::operational(
                "export-lean-lib",
                format!("cannot create {}: {e}", parent.display()),
            )
        })?;
        let staging = tempfile::Builder::new()
            .prefix(".lean-lib-stage-")
            .tempdir_in(parent)
            .map_err(|e| {
                Failure::operational(
                    "export-lean-lib",
                    format!(
                        "cannot create staging directory in {}: {e}",
                        parent.display()
                    ),
                )
            })?;
        for (src_path, rel, expected_sha) in candidates {
            let target = staging.path().join(&rel);
            let copied_sha = stage_regular_file(&src_path, &target, "export-lean-lib")
                .map_err(|e| Failure::operational("export-lean-lib", e.message))?;
            // Exported artifacts live outside the sealed stage; restore owner
            // write permission (`0o644`) so callers can overwrite/remove them.
            set_mode(&target, 0o644)
                .map_err(|e| Failure::operational("export-lean-lib", e.message))?;
            if !copied_sha.eq_ignore_ascii_case(expected_sha) {
                return Err(Failure::operational(
                    "export-lean-lib",
                    format!(
                        "promoted artifact {} changed during export",
                        src_path.display()
                    ),
                ));
            }
        }
        fs::rename(staging.path(), dest).map_err(|e| {
            Failure::operational(
                "export-lean-lib",
                format!("cannot promote staged lean-lib to {}: {e}", dest.display()),
            )
        })?;
        // Ownership of the staged directory transferred to `dest`; disarm
        // `TempDir` cleanup so drop does not remove the renamed path.
        let _ = staging.keep();
        Ok(true)
    }

    /// Return `true` if Lean compilation has started on the current stage.
    #[doc(hidden)]
    pub fn execution_began(&self) -> bool {
        self.execution_began
    }

    /// Record that Lean compilation has started on the current stage.
    #[doc(hidden)]
    pub fn mark_execution_began(&mut self) {
        self.execution_began = true;
    }

    /// Return the sanitized child-process environment allowlist.
    #[doc(hidden)]
    pub fn environment(&self) -> &BTreeMap<String, String> {
        &self.environment
    }

    /// Return a shared reference to the [`AdmittedToolchain`], or an
    /// operational [`Failure`] if [`Checker::tool_admission`] has not run.
    #[doc(hidden)]
    pub fn admitted(&self) -> Result<&AdmittedToolchain, Failure> {
        self.admitted.as_ref().ok_or_else(|| {
            Failure::new(
                2,
                "admission",
                "tool_admission must succeed before inspecting or compiling modules",
            )
        })
    }

    /// Return a mutable reference to the [`AdmittedToolchain`], or an
    /// operational [`Failure`] if [`Checker::tool_admission`] has not run.
    #[doc(hidden)]
    pub fn admitted_mut(&mut self) -> Result<&mut AdmittedToolchain, Failure> {
        self.admitted.as_mut().ok_or_else(|| {
            Failure::new(
                2,
                "admission",
                "tool_admission must succeed before inspecting or compiling modules",
            )
        })
    }

    /// Wipe and recreate `self.stage` with `0o700` owner-only permissions and
    /// clear any prior admission state.
    #[doc(hidden)]
    pub fn reset_stage(&mut self) -> Result<(), Failure> {
        if self.stage.exists() {
            make_tree_writable(&self.stage);
            fs::remove_dir_all(&self.stage).map_err(|e| {
                Failure::new(2, "snapshot", format!("cannot clean {}: {e}", self.stage.display()))
            })?;
        }
        let mut stage_builder = fs::DirBuilder::new();
        // Recreating the stage must preserve its owner-only Unix permissions.
        // A pre-existing replacement directory must cause creation to fail.
        #[cfg(unix)]
        stage_builder.mode(0o700);
        stage_builder.create(&self.stage).map_err(|e| {
            Failure::new(2, "snapshot", format!("cannot recreate {}: {e}", self.stage.display()))
        })?;
        self.admitted = None;
        self.execution_began = false;
        self.sandbox_runtime = None;
        self.probed_backend = None;
        self.olean_ledger.clear();
        self.compiled_roles.clear();
        Ok(())
    }

    /// Stage `TrustedBoundary.lean` inside `control/` (`0o500`, file `0o444`,
    /// never mounted directly into child processes), validate `lean-toolchain`,
    /// `foundation-lock.json`, and the `library-lock.json` catalog when
    /// present, and compare the `lean` executable, every
    /// `foundation-lock.json` source and `.olean`/`.ir` artifact, and the
    /// sysroot `{Init,Std,Lean}*` `.olean` manifest against their locked
    /// SHA-256 digests.
    ///
    /// Authenticating the sysroot `{Init,Std,Lean}*` `.olean`, `.olean.server`,
    /// and `.olean.private` manifest here covers the compiled `.olean*` modules
    /// loaded by the standalone inspector (`TrustedBoundary.lean`) before any
    /// inspector mode executes. Sysroot `.ir`/`.ir.sig` companions outside
    /// `foundation-lock.json` and `library-lock.json`, as well as the Lean
    /// shared libraries that the executable loads (which contain the kernel and
    /// elaborator), remain unhashed and identified only by `lean --version`, so
    /// their integrity rests on the uncompromised execution environment that
    /// `THREAT_MODEL.md` assumes. Library source/`.ir` digests are checked
    /// later, when target imports reach them.
    #[doc(hidden)]
    pub fn tool_admission(&mut self) -> Result<&mut AdmittedToolchain, Failure> {
        let inspector_src = self.root.join("trusted/audit/TrustedBoundary.lean");
        let control_dir = self.stage.join("control");
        if control_dir.exists() {
            make_tree_writable(&control_dir);
        }
        create_dir_mode(&control_dir, 0o700)?;
        let inspector = control_dir.join("TrustedBoundary.lean");
        let inspector_sha256 = stage_regular_file(&inspector_src, &inspector, "tool-snapshot")?;
        set_mode(&inspector, 0o444)?;
        set_mode(&control_dir, 0o500)?;
        if self.allow_unpinned_lean {
            return self.tool_admission_unpinned(inspector, inspector_sha256);
        }

        let source = self.root.join("trusted/lean");
        let lock_path = source.join("foundation-lock.json");
        let toolchain_path = source.join("lean-toolchain");
        regular(&lock_path, "lock")?;
        regular(&toolchain_path, "lock")?;

        let lock_text = fs::read_to_string(&lock_path)
            .map_err(|e| Failure::new(2, "lock", format!("cannot read foundation lock: {e}")))?;
        let parsed_lock: FoundationLock = serde_json::from_str(&lock_text)
            .map_err(|e| Failure::new(2, "lock", format!("cannot read foundation lock: {e}")))?;
        if parsed_lock.schema != 1
            || parsed_lock.toolchain != TOOLCHAIN
            || parsed_lock.distributions.is_empty()
            || !parsed_lock.distributions.values().all(|s| is_sha256_hex(s))
            || parsed_lock.modules.is_empty()
            || !parsed_lock.modules.keys().eq(parsed_lock.graph.keys())
        {
            return Err(Failure::new(2, "lock", "unsupported lock/toolchain schema"));
        }
        for (module, record) in &parsed_lock.modules {
            record.validate_schema(module, "lock")?;
        }

        let toolchain_text = fs::read_to_string(&toolchain_path)
            .map_err(|e| Failure::new(2, "lock", format!("cannot read lean-toolchain: {e}")))?;
        if toolchain_text.trim() != TOOLCHAIN {
            return Err(Failure::new(1, "lock", "lean-toolchain differs from lock"));
        }

        // Preserve zero-unhashed-exec: hash `self.lean` against
        // `foundation-lock.json` before invoking `--version` or
        // `--print-prefix`.
        let lean_sha = sha256_file_deref(&self.lean, "toolchain")?;
        if !parsed_lock.distributions.values().any(|s| s.eq_ignore_ascii_case(&lean_sha)) {
            return Err(Failure::new(
                2,
                "toolchain",
                format!("Lean binary SHA-256 differs from lock: {lean_sha}"),
            ));
        }

        let actual_version =
            self.process("version", &["--version".to_string()])?.trim().to_string();
        let Some(expected_lean_sha) = parsed_lock.distributions.get(&actual_version) else {
            return Err(Failure::new(
                2,
                "toolchain",
                format!("Lean version/commit differs from lock: {actual_version}"),
            ));
        };
        if !expected_lean_sha.eq_ignore_ascii_case(&lean_sha) {
            return Err(Failure::new(
                2,
                "toolchain",
                format!(
                    "Lean binary SHA-256 mismatch for {actual_version}: expected {expected_lean_sha}, got {lean_sha}"
                ),
            ));
        }

        let prefix_raw =
            self.process("prefix", &["--print-prefix".to_string()])?.trim().to_string();
        let prefix = fs::canonicalize(&prefix_raw)
            .map_err(|e| Failure::new(2, "toolchain", format!("cannot resolve prefix: {e}")))?;
        let prefix_lean = prefix.join("bin/lean");
        let canon_self_lean = fs::canonicalize(&self.lean).unwrap_or_else(|_| self.lean.clone());
        let exec_lean = if prefix_lean.exists() {
            let resolved = fs::canonicalize(&prefix_lean).map_err(|e| {
                Failure::new(
                    2,
                    "toolchain",
                    format!("cannot canonicalize {}: {e}", prefix_lean.display()),
                )
            })?;
            // Re-authenticate `exec_lean` against `foundation-lock.json`
            // whenever `prefix/bin/lean` resolves to a different binary than
            // `self.lean` (covers both sandboxed and unsandboxed pinned runs).
            if resolved != canon_self_lean {
                let exec_sha = sha256_file_deref(&resolved, "toolchain")?;
                if !expected_lean_sha.eq_ignore_ascii_case(&exec_sha) {
                    return Err(Failure::new(
                        2,
                        "toolchain",
                        format!(
                            "resolved Lean binary {} SHA-256 differs from lock: \
                             expected {expected_lean_sha}, got {exec_sha}",
                            resolved.display()
                        ),
                    ));
                }
            }
            resolved
        } else {
            canon_self_lean
        };

        let mut artifacts = BTreeMap::new();
        for (module, record) in &parsed_lock.modules {
            let mod_arts = verify_installed_module_record(&prefix, module, record, "foundation")?;
            artifacts.insert(module.clone(), mod_arts);
        }

        let foundation_modules: BTreeSet<String> = parsed_lock.modules.keys().cloned().collect();
        #[cfg(test)]
        let expected_sysroot_sha = self
            .expected_sysroot_manifest_sha256_for_test
            .as_deref()
            .unwrap_or(LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256);
        #[cfg(not(test))]
        let expected_sysroot_sha = LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256;
        verify_sysroot_foundation_dir(
            &prefix.join("lib/lean"),
            &foundation_modules,
            expected_sysroot_sha,
        )
        .map_err(|err| Failure::new(err.code, "toolchain", err.message))?;

        let library_lock_path = self.root.join("trusted/audit/library-lock.json");
        let library_lock = if fs::symlink_metadata(&library_lock_path).is_ok() {
            regular(&library_lock_path, "library-lock")?;
            let lock: LibraryLock = serde_json::from_slice(
                &fs::read(&library_lock_path)
                    .map_err(|e| Failure::operational("library-lock", e.to_string()))?,
            )
            .map_err(|e| Failure::operational("library-lock", e.to_string()))?;
            if lock.schema != 1
                || lock.toolchain != TOOLCHAIN
                || !lock.modules.keys().eq(lock.graph.keys())
                || lock.modules.keys().any(|m| parsed_lock.modules.contains_key(m))
                || lock.graph.values().flatten().any(|e| {
                    !lock.modules.contains_key(&e.module)
                        && !parsed_lock.modules.contains_key(&e.module)
                })
            {
                return Err(Failure::operational(
                    "library-lock",
                    "invalid checked-library catalog",
                ));
            }
            for (module, record) in &lock.modules {
                record.validate_schema(module, "library-lock")?;
            }
            Some(lock)
        } else {
            None
        };

        self.admitted = Some(AdmittedToolchain {
            inspector,
            inspector_sha256,
            lean_sha256: lean_sha,
            version: actual_version,
            prefix,
            axioms: parsed_lock.axioms,
            foundation_graph: parsed_lock.graph.clone(),
            graph: parsed_lock.graph,
            artifacts,
            library_lock,
            library_modules: BTreeSet::new(),
            unpinned: false,
            sysroot_package_roots: BTreeSet::new(),
            unpinned_records: BTreeMap::new(),
            lean_binary_sha256: None,
            exec_lean,
            expected_lean_sha: Some(expected_lean_sha.clone()),
            inspector_olean: None,
        });
        Ok(self.admitted.as_mut().unwrap())
    }

    fn tool_admission_unpinned(
        &mut self,
        inspector: PathBuf,
        inspector_sha256: String,
    ) -> Result<&mut AdmittedToolchain, Failure> {
        let (version, prefix, exec_lean) = if self.sandbox_mode == SandboxMode::Unsandboxed {
            let version = self
                .process("version", &["--version".to_string()])?
                .trim()
                .to_string();
            let prefix_raw = self
                .process("prefix", &["--print-prefix".to_string()])?
                .trim()
                .to_string();
            let prefix = fs::canonicalize(&prefix_raw).map_err(|e| {
                Failure::new(2, "toolchain", format!("cannot resolve prefix: {e}"))
            })?;
            let prefix_lean = prefix.join("bin/lean");
            let exec_lean = if prefix_lean.exists() {
                fs::canonicalize(&prefix_lean).map_err(|e| {
                    Failure::new(
                        2,
                        "toolchain",
                        format!("cannot canonicalize {}: {e}", prefix_lean.display()),
                    )
                })?
            } else {
                fs::canonicalize(&self.lean).unwrap_or_else(|_| self.lean.clone())
            };
            (version, prefix, exec_lean)
        } else {
            let (prefix, exec_lean) = resolve_static_unpinned_toolchain(&self.lean)?;
            let pre_probe_sha = sha256_file_deref(&exec_lean, "toolchain")
                .map_err(|e| Failure::operational("toolchain", e.message))?;
            let runtime =
                SandboxRuntime::probe(self.sandbox_mode, &exec_lean, &prefix, &self.stage)?;
            self.probed_backend = Some(runtime.backend);
            let version = self
                .run_sandboxed_lean_query(&runtime, "version", &["--version".to_string()])?
                .trim()
                .to_string();
            let printed_prefix = self
                .run_sandboxed_lean_query(&runtime, "prefix", &["--print-prefix".to_string()])?
                .trim()
                .to_string();
            let printed_path = Path::new(&printed_prefix);
            let prefix_matches = if runtime.backend == ActiveSandbox::LinuxBwrap {
                printed_path == Path::new("/toolchain")
            } else {
                printed_path == prefix.as_path()
                    || exec_lean.parent().and_then(Path::parent) == Some(printed_path)
            };
            if !prefix_matches {
                return Err(Failure::new(
                    2,
                    "toolchain",
                    format!(
                        "sandboxed --print-prefix ({printed_prefix}) disagrees with resolved \
                         unpinned sysroot {}",
                        prefix.display()
                    ),
                ));
            }
            let post_probe_sha = sha256_file_deref(&exec_lean, "toolchain")
                .map_err(|e| Failure::operational("toolchain", e.message))?;
            if pre_probe_sha != post_probe_sha {
                return Err(Failure::operational(
                    "toolchain",
                    format!(
                        "unpinned Lean binary {} changed during admission",
                        exec_lean.display()
                    ),
                ));
            }
            self.sandbox_runtime = Some(runtime);
            (version, prefix, exec_lean)
        };
        let lean_binary_sha256 = sha256_file_deref(&exec_lean, "toolchain")
            .map_err(|e| Failure::operational("toolchain", e.message))?;
        let sysroot_package_roots = scan_sysroot_package_roots(&prefix, "toolchain")?;
        let axioms = FOUNDATION_AXIOMS
            .iter()
            .map(|(name, module)| ((*name).to_string(), (*module).to_string()))
            .collect();
        self.admitted = Some(AdmittedToolchain {
            inspector,
            inspector_sha256,
            lean_sha256: lean_binary_sha256.clone(),
            version,
            prefix,
            axioms,
            foundation_graph: BTreeMap::new(),
            graph: BTreeMap::new(),
            artifacts: BTreeMap::new(),
            library_lock: None,
            library_modules: BTreeSet::new(),
            unpinned: true,
            sysroot_package_roots,
            unpinned_records: BTreeMap::new(),
            lean_binary_sha256: Some(lean_binary_sha256),
            exec_lean,
            expected_lean_sha: None,
            inspector_olean: None,
        });
        Ok(self.admitted.as_mut().unwrap())
    }

    /// Execute a read-only Lean metadata query (`--version` or
    /// `--print-prefix`) strictly inside `runtime` (`ExecSeal`), enforcing Door
    /// 1 empty-`out/` hygiene so unpinned toolchain admission never executes an
    /// untrusted binary on the host.
    fn run_sandboxed_lean_query(
        &self,
        runtime: &SandboxRuntime,
        label: &str,
        arguments: &[String],
    ) -> Result<String, Failure> {
        let (run_dir, in_dir, out_dir, tmp_dir) = self.prepare_run_dirs()?;
        set_mode(&in_dir, 0o500)?;
        let ro_mounts = vec![MountSpec {
            host: in_dir,
            child: PathBuf::from("/work/in"),
        }];
        let rw_out = MountSpec {
            host: out_dir.clone(),
            child: PathBuf::from("/work/out"),
        };
        let rw_tmp = MountSpec {
            host: tmp_dir,
            child: PathBuf::from("/work/tmp"),
        };
        let policy = SandboxPolicy {
            exec_bin: runtime.exec_lean.clone(),
            args: arguments.to_vec(),
            ro_mounts,
            rw_out,
            rw_tmp,
            child_cwd: None,
            extra_env: BTreeMap::new(),
            timeout: self.child_timeout,
        };
        let exec_res = runtime.execute(&policy);
        let out_nonempty = fs::read_dir(&out_dir)
            .map(|mut entries| entries.next().is_some())
            .unwrap_or(true);
        make_tree_writable(&run_dir);
        let _ = fs::remove_dir_all(&run_dir);
        let output = exec_res?;
        if out_nonempty {
            return Err(Failure::operational(
                "door1",
                format!("unexpected output files from Lean {label} query"),
            ));
        }
        check_lean_output(label, output, false)
    }

    /// Lazily probe and cache [`SandboxRuntime`] on the first sandboxed Lean
    /// invocation, re-confirming `exec_lean` against the locked digest in
    /// pinned mode.
    #[doc(hidden)]
    pub fn ensure_sandbox_ready(&mut self) -> Result<SandboxRuntime, Failure> {
        if let Some(rt) = &self.sandbox_runtime {
            return Ok(rt.clone());
        }
        let adm = self.admitted()?;
        let exec_lean = adm.exec_lean.clone();
        let prefix = adm.prefix.clone();
        if self.sandbox_mode != SandboxMode::Unsandboxed
            && let Some(expected_sha) = &adm.expected_lean_sha
        {
            let actual_sha = sha256_file_deref(&exec_lean, "toolchain")?;
            if !actual_sha.eq_ignore_ascii_case(expected_sha) {
                return Err(Failure::operational(
                    "toolchain",
                    format!(
                        "resolved exec_lean {} SHA-256 differs from lock: expected {expected_sha}, got {actual_sha}",
                        exec_lean.display()
                    ),
                ));
            }
        }
        let rt = SandboxRuntime::probe(self.sandbox_mode, &exec_lean, &prefix, &self.stage)?;
        self.probed_backend = Some(rt.backend);
        self.sandbox_runtime = Some(rt.clone());
        Ok(rt)
    }

    /// Capture a Lean child in the stage with only the selected environment.
    pub(crate) fn launch_lean(&self, arguments: &[String]) -> io::Result<Output> {
        self.launch_lean_with_path(arguments, None)
    }

    /// Capture a Lean child in the stage with an optional hermetic `LEAN_PATH`
    /// override pointing exclusively at staged `.olean` directories.
    fn launch_lean_with_path(
        &self,
        arguments: &[String],
        lean_path: Option<&OsStr>,
    ) -> io::Result<Output> {
        let lean_bin =
            self.admitted.as_ref().map_or(self.lean.as_path(), |a| a.exec_lean.as_path());
        let mut cmd = Command::new(lean_bin);
        cmd.args(arguments).current_dir(&self.stage).env_clear().envs(&self.environment);
        if let Some(lp) = lean_path {
            cmd.env("LEAN_PATH", lp);
        }
        cmd.output()
    }

    /// Execute `self.lean` with `arguments` in the sanitized `self.environment`
    /// with `self.stage` as the working directory.
    #[doc(hidden)]
    pub fn process(&mut self, label: &str, arguments: &[String]) -> Result<String, Failure> {
        self.process_with_path_and_exit_policy(label, arguments, None, false)
    }

    /// Execute `self.lean` with `arguments` and an optional hermetic
    /// `LEAN_PATH` override.
    #[doc(hidden)]
    pub fn process_with_path(
        &mut self,
        label: &str,
        arguments: &[String],
        lean_path: Option<&OsStr>,
    ) -> Result<String, Failure> {
        self.process_with_path_and_exit_policy(label, arguments, lean_path, false)
    }

    /// Target compilation recognizes a reported frontend/source rejection from
    /// JSON diagnostics. Unknown output and resource/kernel reports remain
    /// operational; this classification does not establish proof falsity.
    /// Repository invocations preserve their existing all-operational policy.
    pub(crate) fn process_with_exit_policy(
        &mut self,
        label: &str,
        arguments: &[String],
        ordinary_rejection: bool,
    ) -> Result<String, Failure> {
        self.process_with_path_and_exit_policy(label, arguments, None, ordinary_rejection)
    }

    fn process_with_path_and_exit_policy(
        &mut self,
        label: &str,
        arguments: &[String],
        lean_path: Option<&OsStr>,
        ordinary_rejection: bool,
    ) -> Result<String, Failure> {
        let _ = self.next_counter();
        let output = self
            .launch_lean_with_path(arguments, lean_path)
            .map_err(|e| Failure::new(2, label, format!("could not execute Lean: {e}")))?;
        check_lean_output(label, output, ordinary_rejection)
    }

    /// Write a `<module>.setup.json` descriptor for `lean --setup`, filtering
    /// `importArts` strictly to the transitive import closure in both pinned
    /// and unpinned modes.
    #[doc(hidden)]
    pub fn write_setup_json(
        &self,
        module: &str,
        imports: &[ImportEdge],
    ) -> Result<PathBuf, Failure> {
        let setup_path = self.stage.join(format!("{module}.setup.json"));
        self.write_setup_json_at(&setup_path, module, imports, None)?;
        Ok(setup_path)
    }

    fn write_setup_json_at(
        &self,
        setup_path: &Path,
        module: &str,
        imports: &[ImportEdge],
        mapper: Option<&PathMapper>,
    ) -> Result<(), Failure> {
        let adm = self.admitted()?;
        write_setup_json_to_path(setup_path, adm, module, imports, mapper)
    }

    /// Create fresh per-invocation `runs/<counter>/{in,out,tmp}` directories.
    fn prepare_run_dirs(&self) -> Result<(PathBuf, PathBuf, PathBuf, PathBuf), Failure> {
        prepare_run_dirs_at(&self.stage, self.next_counter())
    }

    /// Compile a single staged `.lean` source file into
    /// `self.stage/<lib_subdir>` using `--setup` and strict synchronous kernel
    /// flags, and register its compiled [`ModuleArtifacts`].
    #[doc(hidden)]
    pub fn compile_lean_module(
        &mut self,
        module: &str,
        src_path: &Path,
        edge_list: Vec<ImportEdge>,
        lib_subdir: &str,
        warn_as_err: bool,
        target_rejection: bool,
    ) -> Result<(), Failure> {
        if !target_rejection && self.sandbox_mode == SandboxMode::Unsandboxed {
            return self.compile_lean_module_direct(
                module,
                src_path,
                edge_list,
                lib_subdir,
                warn_as_err,
            );
        }

        let runtime = self.ensure_sandbox_ready()?;
        let (_run_dir, in_dir, out_dir, tmp_dir) = self.prepare_run_dirs()?;
        let lib_dir = self.stage.join(lib_subdir);
        create_dir_mode(&lib_dir, 0o700)?;

        let leaf_name = format!("{}.lean", module.rsplit('.').next().unwrap_or(module));
        let in_src = in_dir.join(&leaf_name);
        copy_readonly_file(src_path, &in_src, "compile")?;

        let ro_mounts = vec![
            MountSpec {
                host: in_dir.clone(),
                child: PathBuf::from("/work/in"),
            },
            MountSpec {
                host: lib_dir.clone(),
                child: PathBuf::from("/work/lib"),
            },
        ];
        let rw_out = MountSpec {
            host: out_dir.clone(),
            child: PathBuf::from("/work/out"),
        };
        let rw_tmp = MountSpec {
            host: tmp_dir.clone(),
            child: PathBuf::from("/work/tmp"),
        };
        let mapper = PathMapper::new(&runtime, &ro_mounts, &rw_out, &rw_tmp);

        let setup_host = in_dir.join(format!("{module}.setup.json"));
        self.write_setup_json_at(&setup_host, module, &edge_list, Some(&mapper))?;
        set_mode(&in_dir, 0o500)?;

        let out_filename = format!("{}.olean", module.rsplit('.').next().unwrap_or(module));
        let out_host = out_dir.join(&out_filename);
        let mut compile_args = vec![
            "-j1".to_string(),
            format!("-M{}", self.effective_lean_memory_limit_mb(None)),
            "-t0".to_string(),
            "-DElab.async=false".to_string(),
            "-Ddebug.skipKernelTC=false".to_string(),
        ];
        if target_rejection {
            compile_args.push("--json".to_string());
        }
        if warn_as_err {
            compile_args.push("-DwarningAsError=true".to_string());
        }
        compile_args.extend([
            "--setup".to_string(),
            mapper.map_str(&setup_host)?,
            "-o".to_string(),
            mapper.map_str(&out_host)?,
            mapper.map_str(&in_src)?,
        ]);

        let policy = SandboxPolicy {
            exec_bin: runtime.exec_lean.clone(),
            args: compile_args,
            ro_mounts,
            rw_out,
            rw_tmp,
            child_cwd: None,
            extra_env: BTreeMap::new(),
            timeout: self.child_timeout,
        };
        let output = runtime.execute(&policy);
        let _ = fs::remove_dir_all(&tmp_dir);
        let output = output?;

        let label = format!("compile-{module}");
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            let detail = format!("stdout:\n{}\nstderr:\n{}", stdout.trim(), stderr.trim());
            let code = if target_rejection && reports_frontend_rejection(&output) {
                1
            } else {
                2
            };
            return Err(Failure::new(
                code,
                label,
                format!("Lean exited {:?}: {detail}", output.status.code()),
            ));
        }

        let dest_olean = lib_dir.join(format!("{}.olean", module.replace('.', "/")));
        let sha = validate_and_promote_olean(&out_dir, &out_filename, &dest_olean)?;
        self.olean_ledger.insert(dest_olean.clone(), sha);

        let mod_arts = ModuleArtifacts {
            olean_parts: vec![dest_olean.to_string_lossy().into_owned()],
            ir_parts: Vec::new(),
        };
        let adm = self.admitted_mut()?;
        adm.artifacts.insert(module.to_string(), mod_arts);
        adm.graph.insert(module.to_string(), edge_list);
        Ok(())
    }

    fn compile_lean_module_direct(
        &mut self,
        module: &str,
        src_path: &Path,
        edge_list: Vec<ImportEdge>,
        lib_subdir: &str,
        warn_as_err: bool,
    ) -> Result<(), Failure> {
        let setup_path = self.write_setup_json(module, &edge_list)?;
        let output =
            self.stage.join(lib_subdir).join(format!("{}.olean", module.replace('.', "/")));
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| Failure::operational("compile", e.to_string()))?;
        }
        let compile_args = build_lean_compile_args(
            &setup_path,
            &output,
            src_path,
            self.effective_lean_memory_limit_mb(None),
            warn_as_err,
            false,
        );
        self.process_with_exit_policy(&format!("compile-{module}"), &compile_args, false)?;
        let mod_arts = collect_compiled_artifacts(module, &output)?;
        let adm = self.admitted_mut()?;
        adm.artifacts.insert(module.to_string(), mod_arts);
        adm.graph.insert(module.to_string(), edge_list);
        Ok(())
    }

    /// Compile a topologically ordered batch of staged `.lean` modules in
    /// parallel along their verified import DAG across at most `max_workers`
    /// workers, preserving deterministic earliest-order failure reporting,
    /// `ExecSeal` + Door 1 single-file promotion (when active), and serialized
    /// registration into `self.admitted` and `self.olean_ledger`.
    #[doc(hidden)]
    #[allow(clippy::too_many_arguments)]
    pub fn compile_lean_modules_parallel(
        &mut self,
        order: &[String],
        sources: &BTreeMap<String, PathBuf>,
        imports: &BTreeMap<String, Vec<ImportEdge>>,
        lib_subdir: &str,
        warn_as_err: bool,
        target_rejection: bool,
        max_workers: usize,
    ) -> Result<(), Failure> {
        if order.is_empty() {
            return Ok(());
        }
        let _ = self.admitted()?;
        for module in order {
            if !sources.contains_key(module) {
                return Err(Failure::operational(
                    "compile",
                    format!("missing staged source for {module}"),
                ));
            }
        }
        let plan =
            ParallelDagPlan::from_module_order(order, imports, "preflight", "module import cycle")?;
        self.execution_began = true;

        if !target_rejection && self.sandbox_mode == SandboxMode::Unsandboxed {
            let mem_limit_mb = self.effective_lean_memory_limit_mb(None);
            let lib_dir = self.stage.join(lib_subdir);
            fs::create_dir_all(&lib_dir)
                .map_err(|e| Failure::operational("compile", e.to_string()))?;
            self.counter.fetch_add(order.len(), Ordering::Relaxed);
            let stage = &self.stage;
            let environment = &self.environment;
            let adm = self
                .admitted
                .as_mut()
                .expect("toolchain admission verified above");
            let exec_lean = adm.exec_lean.clone();

            return run_parallel_dag(
                &plan,
                max_workers,
                "compile",
                "worker panicked during Lean compilation",
                adm,
                |adm, idx| {
                    let module = &order[idx];
                    let edge_list = &imports[module];
                    let src_path = &sources[module];
                    let setup_path = stage.join(format!("{module}.setup.json"));
                    write_setup_json_to_path(&setup_path, adm, module, edge_list, None)?;
                    let output = lib_dir.join(format!("{}.olean", module.replace('.', "/")));
                    if let Some(parent) = output.parent() {
                        fs::create_dir_all(parent)
                            .map_err(|e| Failure::operational("compile", e.to_string()))?;
                    }
                    let compile_args = build_lean_compile_args(
                        &setup_path,
                        &output,
                        src_path,
                        mem_limit_mb,
                        warn_as_err,
                        false,
                    );
                    Ok((output, compile_args))
                },
                |idx, (output_path, compile_args)| {
                    let module = &order[idx];
                    let label = format!("compile-{module}");
                    let output = Command::new(&exec_lean)
                        .args(&compile_args)
                        .current_dir(stage)
                        .env_clear()
                        .envs(environment)
                        .output()
                        .map_err(|e| {
                            Failure::new(2, &label, format!("could not execute Lean: {e}"))
                        })?;
                    check_lean_output(&label, output, false)?;
                    collect_compiled_artifacts(module, &output_path)
                },
                |adm, idx, mod_arts| {
                    let module = &order[idx];
                    adm.artifacts.insert(module.clone(), mod_arts);
                    adm.graph.insert(module.clone(), imports[module].clone());
                    Ok(())
                },
            );
        }

        let runtime = self.ensure_sandbox_ready()?;
        let mem_limit_mb = self.effective_lean_memory_limit_mb(None);
        let runs_dir = self.stage.join("runs");
        create_dir_mode(&runs_dir, 0o700)?;
        let lib_dir = self.stage.join(lib_subdir);
        create_dir_mode(&lib_dir, 0o700)?;

        let Self {
            stage,
            counter,
            admitted,
            child_timeout,
            olean_ledger,
            ..
        } = self;
        let child_timeout = *child_timeout;
        let adm = admitted.as_mut().expect("toolchain admission verified above");
        let mut shared = (adm, olean_ledger);

        run_parallel_dag(
            &plan,
            max_workers,
            "compile",
            "worker panicked during Lean compilation",
            &mut shared,
            |(adm, _), idx| {
                let module = &order[idx];
                let edge_list = &imports[module];
                let src_path = &sources[module];
                let run_id = counter.fetch_add(1, Ordering::Relaxed) + 1;
                let (_run_dir, in_dir, out_dir, tmp_dir) = prepare_run_dirs_at(stage, run_id)?;
                let leaf = module.rsplit('.').next().unwrap_or(module);
                let in_src = in_dir.join(format!("{leaf}.lean"));
                copy_readonly_file(src_path, &in_src, "compile")?;

                let ro_mounts = vec![
                    MountSpec {
                        host: in_dir.clone(),
                        child: PathBuf::from("/work/in"),
                    },
                    MountSpec {
                        host: lib_dir.clone(),
                        child: PathBuf::from("/work/lib"),
                    },
                ];
                let rw_out = MountSpec {
                    host: out_dir.clone(),
                    child: PathBuf::from("/work/out"),
                };
                let rw_tmp = MountSpec {
                    host: tmp_dir.clone(),
                    child: PathBuf::from("/work/tmp"),
                };
                let mapper = PathMapper::new(&runtime, &ro_mounts, &rw_out, &rw_tmp);

                let setup_host = in_dir.join(format!("{module}.setup.json"));
                write_setup_json_to_path(&setup_host, adm, module, edge_list, Some(&mapper))?;
                set_mode(&in_dir, 0o500)?;

                let out_filename = format!("{leaf}.olean");
                let out_host = out_dir.join(&out_filename);
                let mapped_setup = PathBuf::from(mapper.map_str(&setup_host)?);
                let mapped_out = PathBuf::from(mapper.map_str(&out_host)?);
                let mapped_src = PathBuf::from(mapper.map_str(&in_src)?);
                let compile_args = build_lean_compile_args(
                    &mapped_setup,
                    &mapped_out,
                    &mapped_src,
                    mem_limit_mb,
                    warn_as_err,
                    target_rejection,
                );
                let policy = SandboxPolicy {
                    exec_bin: runtime.exec_lean.clone(),
                    args: compile_args,
                    ro_mounts,
                    rw_out,
                    rw_tmp,
                    child_cwd: None,
                    extra_env: BTreeMap::new(),
                    timeout: child_timeout,
                };
                Ok((policy, out_dir, tmp_dir, out_filename))
            },
            |idx, (policy, out_dir, tmp_dir, out_filename)| {
                let module = &order[idx];
                let label = format!("compile-{module}");
                let output = runtime.execute(&policy);
                let _ = fs::remove_dir_all(&tmp_dir);
                let output = output?;
                check_lean_output(&label, output, target_rejection)?;
                Ok((out_dir, out_filename))
            },
            |(adm, olean_ledger), idx, (out_dir, out_filename)| {
                let module = &order[idx];
                let dest_olean = lib_dir.join(format!("{}.olean", module.replace('.', "/")));
                let sha = validate_and_promote_olean(&out_dir, &out_filename, &dest_olean)?;
                olean_ledger.insert(dest_olean.clone(), sha);
                let mod_arts = ModuleArtifacts {
                    olean_parts: vec![dest_olean.to_string_lossy().into_owned()],
                    ir_parts: Vec::new(),
                };
                adm.artifacts.insert(module.clone(), mod_arts);
                adm.graph.insert(module.clone(), imports[module].clone());
                Ok(())
            },
        )
    }

    /// Compile a `-R <src_root>` module under `ExecSeal` (used by repository
    /// Pass 2 under `SandboxMode::RequireBwrap` for `vendor/lean-miri/`,
    /// `trusted/correspondence/`, and `correspondence/`) and promote validated
    /// Door 1 outputs into `dest_olean.parent()`.
    #[doc(hidden)]
    #[allow(clippy::too_many_arguments)]
    pub fn compile_lean_module_with_root(
        &mut self,
        module: &str,
        src_root: &Path,
        src_file: &Path,
        dest_olean: &Path,
        lean_path_dirs: &[PathBuf],
        mem_mb: u32,
        warn_as_err: bool,
        allowed_extra_parts: &[&str],
        discarded_extra_parts: &[&str],
    ) -> Result<(), Failure> {
        let runtime = self.ensure_sandbox_ready()?;
        for lp in lean_path_dirs {
            create_dir_mode(lp, 0o700)?;
        }
        let run_id = self.next_counter();
        Self::compile_lean_module_with_root_in_runtime(
            &runtime,
            &self.stage,
            run_id,
            self.child_timeout,
            module,
            src_root,
            src_file,
            dest_olean,
            lean_path_dirs,
            mem_mb,
            warn_as_err,
            allowed_extra_parts,
            discarded_extra_parts,
        )
    }

    /// Stateless worker entry point for [`Self::compile_lean_module_with_root`]
    /// using a pre-probed [`SandboxRuntime`] and caller-reserved `run_id`
    /// under `stage/runs/`. Callers invoking this concurrently across threads
    /// must pre-create `stage/runs` and every directory in `lean_path_dirs`
    /// and pass distinct `run_id` values.
    #[doc(hidden)]
    #[allow(clippy::too_many_arguments)]
    pub fn compile_lean_module_with_root_in_runtime(
        runtime: &SandboxRuntime,
        stage: &Path,
        run_id: usize,
        child_timeout: Duration,
        module: &str,
        src_root: &Path,
        src_file: &Path,
        dest_olean: &Path,
        lean_path_dirs: &[PathBuf],
        mem_mb: u32,
        warn_as_err: bool,
        allowed_extra_parts: &[&str],
        discarded_extra_parts: &[&str],
    ) -> Result<(), Failure> {
        let (_run_dir, in_dir, out_dir, tmp_dir) = prepare_run_dirs_at(stage, run_id)?;
        set_mode(&in_dir, 0o500)?;

        // Preserve canonical `stage`-relative source paths (`src/...`) so
        // Lean's embedded source-path strings match pinned `.olean` SHA-256
        // digests (`UPSTREAM_PIN.json`) under both Tier 1 `bwrap` and direct
        // builds.
        let rel_src = src_root
            .strip_prefix(stage)
            .ok()
            .filter(|rel| rel.starts_with("src"))
            .and_then(|rel_root| {
                src_file
                    .strip_prefix(stage)
                    .ok()
                    .map(|rel_file| (rel_root.to_path_buf(), rel_file.to_path_buf()))
            });
        let src_child_mount = match &rel_src {
            Some((rel_root, _)) => PathBuf::from("/work").join(rel_root),
            None => PathBuf::from("/work/src"),
        };

        let mut ro_mounts = vec![
            MountSpec {
                host: in_dir,
                child: PathBuf::from("/work/in"),
            },
            MountSpec {
                host: src_root.to_path_buf(),
                child: src_child_mount,
            },
        ];
        for (idx, lp) in lean_path_dirs.iter().enumerate() {
            if !lp.is_dir() {
                create_dir_mode(lp, 0o700)?;
            }
            ro_mounts.push(MountSpec {
                host: lp.clone(),
                child: PathBuf::from(format!("/work/lp{idx}")),
            });
        }
        let rw_out = MountSpec {
            host: out_dir.clone(),
            child: PathBuf::from("/work/out"),
        };
        let rw_tmp = MountSpec {
            host: tmp_dir.clone(),
            child: PathBuf::from("/work/tmp"),
        };
        let mapper = PathMapper::new(runtime, &ro_mounts, &rw_out, &rw_tmp);

        let leaf_stem = dest_olean
            .file_name()
            .and_then(OsStr::to_str)
            .and_then(|s| s.strip_suffix(".olean"))
            .ok_or_else(|| {
                Failure::operational("compile", format!("invalid dest {}", dest_olean.display()))
            })?
            .to_string();
        let out_filename = format!("{leaf_stem}.olean");
        let out_host = out_dir.join(&out_filename);

        let mut mapped_lp = Vec::with_capacity(lean_path_dirs.len());
        for lp in lean_path_dirs {
            mapped_lp.push(mapper.map_path(lp)?);
        }
        let lean_path_str = env::join_paths(&mapped_lp)
            .map_err(|e| Failure::operational("compile", e.to_string()))?
            .into_string()
            .map_err(|_| Failure::operational("compile", "non-UTF-8 mapped LEAN_PATH"))?;
        let mut extra_env = BTreeMap::new();
        extra_env.insert("LEAN_PATH".to_string(), lean_path_str);

        let mut compile_args = vec![
            "-j1".to_string(),
            format!("-M{mem_mb}"),
            "-t0".to_string(),
            "-DElab.async=false".to_string(),
            "-Ddebug.skipKernelTC=false".to_string(),
        ];
        if warn_as_err {
            compile_args.push("-DwarningAsError=true".to_string());
        }
        let (root_arg, file_arg, child_cwd) = match &rel_src {
            Some((rel_root, rel_file)) => (
                rel_root.to_string_lossy().into_owned(),
                rel_file.to_string_lossy().into_owned(),
                Some(MountSpec {
                    host: stage.to_path_buf(),
                    child: PathBuf::from("/work"),
                }),
            ),
            None => (mapper.map_str(src_root)?, mapper.map_str(src_file)?, None),
        };
        compile_args.extend([
            "-R".to_string(),
            root_arg,
            "-o".to_string(),
            mapper.map_str(&out_host)?,
            file_arg,
        ]);

        let policy = SandboxPolicy {
            exec_bin: runtime.exec_lean.clone(),
            args: compile_args,
            ro_mounts,
            rw_out,
            rw_tmp,
            child_cwd,
            extra_env,
            timeout: child_timeout,
        };
        let output = runtime.execute(&policy);
        let _ = fs::remove_dir_all(&tmp_dir);
        let output = output?;

        let label = format!("compile-{module}");
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            return Err(Failure::new(
                2,
                label,
                format!(
                    "Lean exited {:?}: stdout:\n{}\nstderr:\n{}",
                    output.status.code(),
                    stdout.trim(),
                    stderr.trim()
                ),
            ));
        }

        if allowed_extra_parts.is_empty() && discarded_extra_parts.is_empty() {
            validate_and_promote_olean(&out_dir, &out_filename, dest_olean)?;
        } else {
            let mut allowed_promote = BTreeSet::from([out_filename.clone()]);
            for part in allowed_extra_parts {
                allowed_promote.insert(format!("{leaf_stem}.{part}"));
            }
            let mut allowed_discard = BTreeSet::new();
            for part in discarded_extra_parts {
                allowed_discard.insert(format!("{leaf_stem}.{part}"));
            }
            let dest_dir = dest_olean.parent().ok_or_else(|| {
                Failure::operational("door1", "missing destination parent directory")
            })?;
            validate_and_promote_olean_set(
                &out_dir,
                &allowed_promote,
                &allowed_discard,
                &out_filename,
                dest_dir,
            )?;
        }
        Ok(())
    }

    /// Re-hash `stage/control/TrustedBoundary.lean`, any precompiled
    /// `stage/control/TrustedBoundary.olean`, every staged target source in
    /// `staged_sources`, and every Door-1-promoted `.olean` in
    /// `self.olean_ledger` right before `"target-audit"` (`ArtifactLedger`).
    pub(crate) fn verify_artifact_ledger(
        &self,
        staged_sources: &[(PathBuf, &str)],
    ) -> Result<(), Failure> {
        let adm = self.admitted()?;
        let inspector_now = sha256_file(&adm.inspector, "artifact-ledger")?;
        if !inspector_now.eq_ignore_ascii_case(&adm.inspector_sha256) {
            return Err(Failure::operational(
                "artifact-ledger",
                "staged TrustedBoundary.lean changed during elaboration",
            ));
        }
        if let Some((olean_path, expected_olean_sha)) = &adm.inspector_olean {
            let actual = sha256_file(olean_path, "artifact-ledger")?;
            if !actual.eq_ignore_ascii_case(expected_olean_sha) {
                return Err(Failure::operational(
                    "artifact-ledger",
                    "staged TrustedBoundary.olean changed during elaboration",
                ));
            }
        }
        for (path, expected_sha) in staged_sources {
            let actual = sha256_file(path, "artifact-ledger")?;
            if !actual.eq_ignore_ascii_case(expected_sha) {
                return Err(Failure::operational(
                    "artifact-ledger",
                    "staged source changed during elaboration",
                ));
            }
        }
        for (olean_path, expected_sha) in &self.olean_ledger {
            let actual = sha256_file(olean_path, "artifact-ledger")?;
            if !actual.eq_ignore_ascii_case(expected_sha) {
                return Err(Failure::operational(
                    "artifact-ledger",
                    format!(
                        "promoted artifact {} changed during elaboration",
                        olean_path.display()
                    ),
                ));
            }
        }
        Ok(())
    }

    /// Compile staged `control/TrustedBoundary.lean` once per
    /// `(lean_sha256, sysroot_prefix, inspector_sha256)` into
    /// `control/TrustedBoundary.olean` (validated through Door 1 and pinned by
    /// SHA-256 in [`AdmittedToolchain`]) so repeated inspector invocations
    /// (`headers`, `spec-preflight`, `target-audit`, `preflight`, `audit`) load
    /// the precompiled `.olean` instead of re-elaborating the full inspector
    /// source on every call.
    fn ensure_inspector_compiled(&mut self, mode: &str, direct: bool) -> Result<PathBuf, Failure> {
        if let Some((olean_path, _)) = &self.admitted()?.inspector_olean {
            return Ok(olean_path.clone());
        }
        let compile_phase = if direct { "compile-inspector" } else { mode };
        let (inspector_host, expected_sha, lean_sha, prefix) = {
            let adm = self.admitted()?;
            (
                adm.inspector.clone(),
                adm.inspector_sha256.clone(),
                adm.lean_sha256.clone(),
                adm.prefix.clone(),
            )
        };
        let actual_sha = sha256_file(&inspector_host, compile_phase)?;
        if !actual_sha.eq_ignore_ascii_case(&expected_sha) {
            return Err(Failure::operational(
                compile_phase,
                "staged TrustedBoundary.lean changed before compilation",
            ));
        }
        let runtime_opt = if direct {
            None
        } else {
            Some(self.ensure_sandbox_ready()?)
        };
        let cache_key = (lean_sha, prefix, actual_sha);
        let slot = {
            let mut map = compiled_inspector_cache().lock().unwrap_or_else(|e| e.into_inner());
            map.entry(cache_key).or_insert_with(|| Arc::new(Mutex::new(None))).clone()
        };
        let control_dir = self.stage.join("control");
        let mem_limit =
            format!("-M{}", self.effective_lean_memory_limit_mb(Some("compile-inspector")));

        let mut guard = slot.lock().unwrap_or_else(|e| e.into_inner());
        let (olean_dest, olean_sha) = if let Some(cached) = guard.as_ref() {
            materialize_cached_inspector_olean(
                &control_dir,
                &cached.bytes,
                &cached.sha256,
                compile_phase,
            )?
        } else {
            let (olean_dest, olean_sha) = if direct {
                let run_id = self.next_counter();
                let out_dir = self
                    .stage
                    .join(format!("inspector-compile-{run_id:03}"));
                create_dir_mode(&out_dir, 0o700)?;
                let out_olean = out_dir.join("TrustedBoundary.olean");
                let args = vec![
                    "-j1".to_string(),
                    mem_limit,
                    "-t0".to_string(),
                    "-DElab.async=false".to_string(),
                    "-Ddebug.skipKernelTC=false".to_string(),
                    "-R".to_string(),
                    control_dir.to_string_lossy().into_owned(),
                    "-o".to_string(),
                    out_olean.to_string_lossy().into_owned(),
                    inspector_host.to_string_lossy().into_owned(),
                ];
                let output = self.launch_lean(&args).map_err(|e| {
                    Failure::new(2, compile_phase, format!("could not execute Lean: {e}"))
                });
                let output = match output {
                    Ok(out) => out,
                    Err(err) => {
                        let _ = fs::remove_dir_all(&out_dir);
                        return Err(err);
                    }
                };
                if !output.status.success() {
                    let _ = fs::remove_dir_all(&out_dir);
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    return Err(Failure::new(
                        2,
                        compile_phase,
                        format!("Lean exited {:?}: {}", output.status.code(), stderr.trim()),
                    ));
                }
                let promoted = promote_inspector_olean(&control_dir, &out_dir, compile_phase);
                let _ = fs::remove_dir_all(&out_dir);
                promoted?
            } else {
                let runtime = runtime_opt.expect("sandbox runtime initialized");
                let (_run_dir, in_dir, out_dir, tmp_dir) = self.prepare_run_dirs()?;
                let in_inspector = in_dir.join("TrustedBoundary.lean");
                copy_readonly_file(&inspector_host, &in_inspector, compile_phase)?;
                set_mode(&in_dir, 0o500)?;

                let ro_mounts = vec![MountSpec {
                    host: in_dir.clone(),
                    child: PathBuf::from("/work/in"),
                }];
                let rw_out = MountSpec {
                    host: out_dir.clone(),
                    child: PathBuf::from("/work/out"),
                };
                let rw_tmp = MountSpec {
                    host: tmp_dir.clone(),
                    child: PathBuf::from("/work/tmp"),
                };
                let mapper = PathMapper::new(&runtime, &ro_mounts, &rw_out, &rw_tmp);
                let out_olean = out_dir.join("TrustedBoundary.olean");
                let args = vec![
                    "-j1".to_string(),
                    mem_limit,
                    "-t0".to_string(),
                    "-DElab.async=false".to_string(),
                    "-Ddebug.skipKernelTC=false".to_string(),
                    "-R".to_string(),
                    mapper.map_str(&in_dir)?,
                    "-o".to_string(),
                    mapper.map_str(&out_olean)?,
                    mapper.map_str(&in_inspector)?,
                ];
                let policy = SandboxPolicy {
                    exec_bin: runtime.exec_lean.clone(),
                    args,
                    ro_mounts,
                    rw_out,
                    rw_tmp,
                    child_cwd: None,
                    extra_env: BTreeMap::new(),
                    timeout: self.child_timeout,
                };
                let output = runtime.execute(&policy);
                let _ = fs::remove_dir_all(&tmp_dir);
                let output = output?;
                if !output.status.success() {
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    return Err(Failure::new(
                        2,
                        compile_phase,
                        format!("Lean exited {:?}: {}", output.status.code(), stderr.trim()),
                    ));
                }
                promote_inspector_olean(&control_dir, &out_dir, compile_phase)?
            };
            let bytes = fs::read(&olean_dest)
                .map_err(|e| Failure::operational(compile_phase, e.to_string()))?;
            *guard = Some(Arc::new(CompiledInspectorArtifacts {
                bytes,
                sha256: olean_sha.clone(),
            }));
            (olean_dest, olean_sha)
        };
        drop(guard);

        self.admitted.as_mut().unwrap().inspector_olean = Some((olean_dest.clone(), olean_sha));
        Ok(olean_dest)
    }

    /// Invoke staged `TrustedBoundary.lean` with a serialized JSON request and
    /// validate its structured response envelope (`policy:` -> code `1`,
    /// operational -> code `2`).
    #[doc(hidden)]
    pub fn invoke_inspector(&mut self, mode: &str, req: &Json) -> Result<Json, Failure> {
        if self.sandbox_mode == SandboxMode::Unsandboxed && matches!(mode, "preflight" | "audit") {
            return self.invoke_inspector_direct(mode, req);
        }

        let olean_host = self.ensure_inspector_compiled(mode, false)?;
        let runtime = self.ensure_sandbox_ready()?;
        let (_run_dir, in_dir, out_dir, tmp_dir) = self.prepare_run_dirs()?;

        copy_readonly_file(&olean_host, &in_dir.join("TrustedBoundary.olean"), mode)?;
        let in_entry = in_dir.join("TrustedBoundaryEntry.lean");
        fs::write(&in_entry, INSPECTOR_ENTRY_SOURCE).map_err(|e| {
            Failure::new(
                2,
                mode,
                format!("cannot write inspector entry {}: {e}", in_entry.display()),
            )
        })?;
        set_mode(&in_entry, 0o444)?;

        let mut ro_mounts = vec![MountSpec {
            host: in_dir.clone(),
            child: PathBuf::from("/work/in"),
        }];
        if mode == "target-audit" {
            let lib_dir = self.stage.join("lib");
            create_dir_mode(&lib_dir, 0o700)?;
            ro_mounts.push(MountSpec {
                host: lib_dir,
                child: PathBuf::from("/work/lib"),
            });
        }
        if let Some(sp_arr) = req.get("searchPath").and_then(Json::as_array) {
            let mut seen = BTreeSet::new();
            for (idx, val) in sp_arr.iter().enumerate() {
                if let Some(s) = val.as_str() {
                    let host_dir = PathBuf::from(s);
                    if seen.insert(host_dir.clone()) {
                        ro_mounts.push(MountSpec {
                            host: host_dir,
                            child: PathBuf::from(format!("/work/sp{idx}")),
                        });
                    }
                }
            }
        }
        let rw_out = MountSpec {
            host: out_dir.clone(),
            child: PathBuf::from("/work/out"),
        };
        let rw_tmp = MountSpec {
            host: tmp_dir.clone(),
            child: PathBuf::from("/work/tmp"),
        };
        let mapper = PathMapper::new(&runtime, &ro_mounts, &rw_out, &rw_tmp);

        let mut mapped_req = req.clone();
        if let Some(obj) = mapped_req.as_object_mut() {
            if let Some(sys) = obj.get("sysroot").and_then(Json::as_str) {
                let mapped = mapper.map_str(Path::new(sys))?;
                obj.insert("sysroot".to_string(), Json::String(mapped));
            }
            for key in ["sources", "baseSources"] {
                if let Some(sources) = obj.get_mut(key).and_then(Json::as_array_mut) {
                    let sources_dir = in_dir.join(key);
                    create_dir_mode(&sources_dir, 0o700)?;
                    for (idx, pair) in sources.iter_mut().enumerate() {
                        if let Some(arr) = pair.as_array_mut()
                            && arr.len() == 2
                            && let Some(host_src) = arr[1].as_str()
                        {
                            let copy_dest = sources_dir.join(format!("{idx:04}.lean"));
                            copy_readonly_file(Path::new(host_src), &copy_dest, mode)?;
                            arr[1] = Json::String(mapper.map_str(&copy_dest)?);
                        }
                    }
                    set_mode(&sources_dir, 0o500)?;
                }
            }
            if let Some(sp_arr) = obj.get_mut("searchPath").and_then(Json::as_array_mut) {
                for item in sp_arr.iter_mut() {
                    if let Some(s) = item.as_str() {
                        *item = Json::String(mapper.map_str(Path::new(s))?);
                    }
                }
            }
            if let Some(arts_arr) = obj.get_mut("artifacts").and_then(Json::as_array_mut) {
                for entry in arts_arr.iter_mut() {
                    if let Some(pair) = entry.as_array_mut()
                        && pair.len() == 2
                        && let Some(groups) = pair[1].as_array_mut()
                    {
                        for group in groups.iter_mut() {
                            if let Some(paths) = group.as_array_mut() {
                                for p in paths.iter_mut() {
                                    if let Some(s) = p.as_str() {
                                        *p = Json::String(mapper.map_str(Path::new(s))?);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        let request_host = in_dir.join("request.json");
        let result_host = out_dir.join("result.json");
        let req_bytes = serde_json::to_vec(&mapped_req)
            .map_err(|e| Failure::new(2, mode, format!("cannot serialize request: {e}")))?;
        fs::write(&request_host, req_bytes)
            .map_err(|e| Failure::new(2, mode, format!("cannot write request: {e}")))?;
        set_mode(&request_host, 0o444)?;
        set_mode(&in_dir, 0o500)?;

        let mem_limit = format!("-M{}", self.effective_lean_memory_limit_mb(Some(mode)));
        let args = vec![
            "-j1".to_string(),
            mem_limit,
            "--run".to_string(),
            mapper.map_str(&in_entry)?,
            mapper.map_str(&request_host)?,
            mapper.map_str(&result_host)?,
        ];
        let mut extra_env = BTreeMap::new();
        // Use the delimiter-free relative path `"../in"` (resolved from
        // `child_cwd` = `/work/tmp` in Tier 1 or `<run_dir>/tmp` in Tier 2 and
        // `Unsandboxed`) so colons in `TMPDIR` never split `LEAN_PATH` or
        // expose a decoy `<prefix>/TrustedBoundary.olean` before
        // `initHermeticSearchPath` resets `Lean.searchPathRef`.
        extra_env.insert("LEAN_PATH".to_string(), "../in".to_string());
        let policy = SandboxPolicy {
            exec_bin: runtime.exec_lean.clone(),
            args,
            ro_mounts,
            rw_out,
            rw_tmp,
            child_cwd: None,
            extra_env,
            timeout: self.child_timeout,
        };
        let output = runtime.execute(&policy);
        let _ = fs::remove_dir_all(&tmp_dir);
        let output = output?;

        // Door 1 validates `runs/<n>/out` on BOTH exit 0 and exit 1.
        let door1_bytes = validate_inspector_result(&out_dir, "result.json")?;
        if !output.status.success() {
            if output.status.code() == Some(1)
                && let Some(bytes) = door1_bytes
                && let Ok(text) = String::from_utf8(bytes)
                && let Ok(resp) = serde_json::from_str::<InspectorErrResponse>(&text)
                && !resp.ok
                && resp.category == "policy"
                && resp.message.starts_with("policy:")
            {
                return Err(Failure::new(1, mode, resp.message));
            }
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(Failure::new(
                2,
                mode,
                format!("Lean exited {:?}: {}", output.status.code(), stderr.trim()),
            ));
        }

        let resp_bytes =
            door1_bytes.ok_or_else(|| Failure::new(2, mode, "missing inspector result.json"))?;
        let resp_text = String::from_utf8(resp_bytes)
            .map_err(|e| Failure::new(2, mode, format!("invalid UTF-8 inspector result: {e}")))?;
        let resp: InspectorOkResponse = serde_json::from_str(&resp_text)
            .map_err(|_| Failure::new(2, mode, "unexpected inspector protocol response"))?;
        if !resp.ok {
            return Err(Failure::new(
                2,
                mode,
                "unexpected inspector protocol response",
            ));
        }
        Ok(Json::Object(resp.result))
    }

    fn invoke_inspector_direct(&mut self, mode: &str, req: &Json) -> Result<Json, Failure> {
        let _olean_host = self.ensure_inspector_compiled(mode, true)?;
        let control_dir = self.stage.join("control");
        let entry = control_dir.join("TrustedBoundaryEntry.lean");
        let run_id = self.next_counter();
        let stem = self.stage.join(format!("request-{run_id:03}-{mode}"));
        let request_path = PathBuf::from(format!("{}.json", stem.display()));
        let result_path = PathBuf::from(format!("{}.result.json", stem.display()));
        let req_bytes = serde_json::to_vec(req)
            .map_err(|e| Failure::new(2, mode, format!("cannot serialize request: {e}")))?;
        fs::write(&request_path, req_bytes)
            .map_err(|e| Failure::new(2, mode, format!("cannot write request: {e}")))?;

        let mem_limit = format!("-M{}", self.effective_lean_memory_limit_mb(Some(mode)));
        let args = vec![
            "-j1".to_string(),
            mem_limit,
            "--run".to_string(),
            entry.to_string_lossy().into_owned(),
            request_path.to_string_lossy().into_owned(),
            result_path.to_string_lossy().into_owned(),
        ];
        // `LEAN_PATH` uses the delimiter-free relative path `"control"`
        // (resolved against `current_dir(&self.stage)`) so host `TMPDIR`
        // characters such as `:` cannot split `LEAN_PATH` or leak external
        // directories. `TrustedBoundary.run` immediately calls
        // `initHermeticSearchPath`, which resets `Lean.searchPathRef` from
        // `sysroot` (and explicit staged `searchPath` entries) without reading
        // `LEAN_PATH` before loading any foundation, repo, or vendor module.
        let output = self
            .launch_lean_with_path(&args, Some(OsStr::new("control")))
            .map_err(|e| Failure::new(2, mode, format!("could not execute Lean: {e}")))?;

        if !output.status.success() {
            if output.status.code() == Some(1)
                && result_path.is_file()
                && let Ok(text) = fs::read_to_string(&result_path)
                && let Ok(resp) = serde_json::from_str::<InspectorErrResponse>(&text)
                && !resp.ok
                && resp.category == "policy"
                && resp.message.starts_with("policy:")
            {
                return Err(Failure::new(1, mode, resp.message));
            }
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(Failure::new(
                2,
                mode,
                format!("Lean exited {:?}: {}", output.status.code(), stderr.trim()),
            ));
        }

        let resp_text = fs::read_to_string(&result_path).map_err(|e| {
            Failure::new(2, mode, format!("missing/malformed inspector result: {e}"))
        })?;
        let resp: InspectorOkResponse = serde_json::from_str(&resp_text)
            .map_err(|_| Failure::new(2, mode, "unexpected inspector protocol response"))?;
        if !resp.ok {
            return Err(Failure::new(2, mode, "unexpected inspector protocol response"));
        }
        Ok(Json::Object(resp.result))
    }
}

/// Derive a dotted Lean module name from a relative `.olean` (or
/// `.olean.server` / `.olean.private`) path, normalizing both platform path
/// components and `/` / `\` separators across POSIX and Windows hosts.
fn olean_rel_path_to_module_name(rel: &Path) -> Option<String> {
    let mut parts = Vec::new();
    for comp in rel.components() {
        let Component::Normal(seg) = comp else {
            return None;
        };
        let seg = seg.to_str()?;
        for sub in seg.split(['/', '\\']) {
            if sub.is_empty() {
                return None;
            }
            parts.push(sub);
        }
    }
    let last = parts.last_mut()?;
    *last = last
        .strip_suffix(".olean.server")
        .or_else(|| last.strip_suffix(".olean.private"))
        .or_else(|| last.strip_suffix(".olean"))
        .unwrap_or(last);
    if last.is_empty() {
        return None;
    }
    Some(parts.join("."))
}

/// Create fresh per-invocation `runs/<run_id>/{in,out,tmp}` directories under
/// `stage`.
fn prepare_run_dirs_at(
    stage: &Path,
    run_id: usize,
) -> Result<(PathBuf, PathBuf, PathBuf, PathBuf), Failure> {
    let run_dir = stage.join("runs").join(format!("{run_id:04}"));
    let in_dir = run_dir.join("in");
    let out_dir = run_dir.join("out");
    let tmp_dir = run_dir.join("tmp");
    create_dir_mode(&run_dir, 0o700)?;
    create_dir_mode(&in_dir, 0o700)?;
    create_dir_mode(&out_dir, 0o700)?;
    create_dir_mode(&tmp_dir, 0o700)?;
    Ok((run_dir, in_dir, out_dir, tmp_dir))
}

/// Minimal one-line Lean entrypoint executed by `lean --run` once staged
/// `TrustedBoundary.lean` has been precompiled to `TrustedBoundary.olean`.
const INSPECTOR_ENTRY_SOURCE: &str = "import TrustedBoundary\n";

/// Materialize an already Door-1-validated in-memory `TrustedBoundary.olean`
/// into `control_dir` (`0o444`), verify its SHA-256 digest, emit
/// `TrustedBoundaryEntry.lean` (`0o444`), and re-lock `control_dir` (`0o500`).
fn materialize_cached_inspector_olean(
    control_dir: &Path,
    bytes: &[u8],
    expected_sha: &str,
    mode: &str,
) -> Result<(PathBuf, String), Failure> {
    if !sha256_bytes(bytes).eq_ignore_ascii_case(expected_sha) {
        return Err(Failure::operational(
            mode,
            "in-memory precompiled TrustedBoundary.olean digest mismatch",
        ));
    }
    set_mode(control_dir, 0o700)?;
    let written = (|| {
        let olean_dest = control_dir.join("TrustedBoundary.olean");
        if fs::symlink_metadata(&olean_dest).is_ok() {
            let _ = fs::remove_file(&olean_dest);
        }
        fs::write(&olean_dest, bytes).map_err(|e| {
            Failure::new(
                2,
                mode,
                format!("cannot write cached inspector olean {}: {e}", olean_dest.display()),
            )
        })?;
        set_mode(&olean_dest, 0o444)?;
        let entry_dest = control_dir.join("TrustedBoundaryEntry.lean");
        if fs::symlink_metadata(&entry_dest).is_ok() {
            let _ = fs::remove_file(&entry_dest);
        }
        fs::write(&entry_dest, INSPECTOR_ENTRY_SOURCE).map_err(|e| {
            Failure::new(
                2,
                mode,
                format!("cannot write inspector entry {}: {e}", entry_dest.display()),
            )
        })?;
        set_mode(&entry_dest, 0o444)?;
        Ok((olean_dest, expected_sha.to_string()))
    })();
    let relock = set_mode(control_dir, 0o500);
    written.and_then(|pair| relock.map(|()| pair))
}

/// Promote a Door-1-validated `TrustedBoundary.olean` into `control_dir`
/// (`0o444`), emit the static `TrustedBoundaryEntry.lean` (`0o444`), and
/// unconditionally re-lock `control_dir` to `0o500`.
fn promote_inspector_olean(
    control_dir: &Path,
    out_dir: &Path,
    mode: &str,
) -> Result<(PathBuf, String), Failure> {
    set_mode(control_dir, 0o700)?;
    let promoted = (|| {
        let olean_dest = control_dir.join("TrustedBoundary.olean");
        if fs::symlink_metadata(&olean_dest).is_ok() {
            let _ = fs::remove_file(&olean_dest);
        }
        let sha = validate_and_promote_olean(out_dir, "TrustedBoundary.olean", &olean_dest)?;
        let entry_dest = control_dir.join("TrustedBoundaryEntry.lean");
        if fs::symlink_metadata(&entry_dest).is_ok() {
            let _ = fs::remove_file(&entry_dest);
        }
        fs::write(&entry_dest, INSPECTOR_ENTRY_SOURCE).map_err(|e| {
            Failure::new(
                2,
                mode,
                format!("cannot write inspector entry {}: {e}", entry_dest.display()),
            )
        })?;
        set_mode(&entry_dest, 0o444)?;
        Ok((olean_dest, sha))
    })();
    let relock = set_mode(control_dir, 0o500);
    promoted.and_then(|pair| relock.map(|()| pair))
}

#[cfg(all(test, unix))]
mod process_tests {
    use super::*;

    fn shell_checker(checkout: &Path) -> Checker {
        let mut checker = Checker::new_with_env(checkout, Some(Path::new("/bin/sh")), []).unwrap();
        checker.set_sandbox_mode(SandboxMode::Unsandboxed);
        checker
    }

    #[test]
    fn keeps_staging_private_at_creation_and_after_reset() {
        const PROBE: &str = "ANNEAL_AUDIT_STAGE_PERMISSION_PROBE";
        if env::var_os(PROBE).is_some() {
            use std::os::unix::fs::PermissionsExt;

            let checkout = tempfile::tempdir().unwrap();
            let mut checker = shell_checker(checkout.path());
            assert_eq!(
                fs::metadata(&checker.stage).unwrap().permissions().mode() & 0o777,
                0o700,
                "initial staging directory exposes its contents to other users"
            );
            fs::write(checker.stage.join("input"), b"private source bytes").unwrap();
            checker.reset_stage().unwrap();
            assert_eq!(
                fs::metadata(&checker.stage).unwrap().permissions().mode() & 0o777,
                0o700,
                "reset staging directory exposes its contents to other users"
            );
            assert!(!checker.stage.join("input").exists());
            return;
        }

        // Change only the child's umask; other tests may run concurrently.
        let output = Command::new("/bin/sh")
            .args(["-c", "umask 022 && exec \"$@\"", "stage-permissions"])
            .arg(env::current_exe().unwrap())
            .args([
                "--exact",
                "stage::process_tests::keeps_staging_private_at_creation_and_after_reset",
                "--nocapture",
            ])
            .env(PROBE, "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "permission probe failed:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed"));
    }

    #[test]
    fn captures_successful_child_output() {
        let checkout = tempfile::tempdir().unwrap();
        let checker = shell_checker(checkout.path());
        let output = checker
            .launch_lean(&[
                "-c".to_string(),
                "printf 'stdout\\000\\377'; printf 'stderr\\000\\376' >&2".to_string(),
            ])
            .unwrap();

        assert!(output.status.success());
        assert_eq!(output.stdout, b"stdout\0\xff");
        assert_eq!(output.stderr, b"stderr\0\xfe");
    }

    #[test]
    fn preserves_failed_child_status_and_raw_streams() {
        let checkout = tempfile::tempdir().unwrap();
        let checker = shell_checker(checkout.path());
        let output = checker
            .launch_lean(&[
                "-c".to_string(),
                "printf 'stdout\\000\\377'; printf 'stderr\\000\\376' >&2; exit 37".to_string(),
            ])
            .unwrap();

        assert_eq!(output.status.code(), Some(37));
        assert_eq!(output.stdout, b"stdout\0\xff");
        assert_eq!(output.stderr, b"stderr\0\xfe");
    }

    #[test]
    fn returns_io_error_when_child_cannot_launch() {
        let checkout = tempfile::tempdir().unwrap();
        let missing = checkout.path().join("missing-lean");
        let checker = Checker::new_with_env(checkout.path(), Some(&missing), []).unwrap();

        let error = checker.launch_lean(&[]).unwrap_err();

        assert_eq!(error.kind(), io::ErrorKind::NotFound);
    }

    #[test]
    fn classifies_only_reported_frontend_rejection_as_policy_failure() {
        let checkout = tempfile::tempdir().unwrap();
        let mut checker = shell_checker(checkout.path());
        let diagnostic = serde_json::json!({
            "severity": "error", "kind": "[anonymous]", "data": "Type mismatch"
        })
        .to_string();
        fs::write(checker.stage.join("diagnostic"), &diagnostic).unwrap();
        for (script, target_rejection, expected_code) in [
            ("cat diagnostic; exit 1", true, 1),
            ("cat diagnostic; exit 1", false, 2),
            ("printf 'INTERNAL PANIC: out of memory' >&2; exit 1", true, 2),
            ("cat diagnostic; printf 'INTERNAL PANIC: out of memory' >&2; exit 1", true, 2),
            ("printf rejected >&2; exit 1", true, 2),
            ("printf 'unexpected output'; exit 1", true, 2),
            ("cat diagnostic; printf 'unexpected output'; exit 1", true, 2),
            ("exit 1", true, 2),
            ("cat diagnostic; exit 2", true, 2),
            ("cat diagnostic; exit 37", true, 2),
            ("kill -TERM $$", true, 2),
        ] {
            let error = checker
                .process_with_exit_policy(
                    "fixture",
                    &["-c".to_string(), script.to_string()],
                    target_rejection,
                )
                .unwrap_err();
            assert_eq!(error.code, expected_code, "{script}: {error}");
            assert_eq!(error.phase, "fixture");
            if script.contains("cat diagnostic") {
                assert!(error.message.contains(&diagnostic), "{error}");
            }
            if script.contains("INTERNAL PANIC") {
                assert!(error.message.contains("INTERNAL PANIC"), "{error}");
            }
        }
    }

    #[test]
    fn unknown_and_resource_diagnostics_remain_operational() {
        let checkout = tempfile::tempdir().unwrap();
        let mut checker = shell_checker(checkout.path());
        let ordinary = serde_json::json!({
            "severity": "error", "kind": "[anonymous]", "data": "Type mismatch"
        });
        let warning = serde_json::json!({
            "severity": "warning", "kind": "[anonymous]", "data": "warning"
        });
        for (stream, expected) in [
            (warning.to_string(), 2),
            (format!("{warning}\n{ordinary}"), 1),
            (format!("{ordinary}\n{warning}"), 1),
        ] {
            fs::write(checker.stage.join("diagnostic"), &stream).unwrap();
            let error = checker
                .process_with_exit_policy(
                    "fixture",
                    &["-c".into(), "cat diagnostic; exit 1".into()],
                    true,
                )
                .unwrap_err();
            assert_eq!(error.code, expected, "{stream}: {error}");
        }
        for diagnostic in [
            serde_json::json!({"severity": "unknown", "kind": "[anonymous]", "data": "new severity"}),
            serde_json::json!({"severity": "error", "kind": "runtime.maxHeartbeats", "data": "timeout"}),
            serde_json::json!({"severity": "error", "kind": "nested.runtime.maxRecDepth", "data": "depth"}),
            serde_json::json!({"severity": "error", "kind": "[anonymous]", "data": "(kernel) excessive memory consumption detected"}),
            serde_json::json!({"severity": "error", "data": "missing kind"}),
            serde_json::json!({"severity": "error", "kind": "", "data": "missing category"}),
        ] {
            for prefix in [String::new(), format!("{ordinary}\n")] {
                fs::write(checker.stage.join("diagnostic"), format!("{prefix}{diagnostic}\n"))
                    .unwrap();
                let error = checker
                    .process_with_exit_policy(
                        "fixture",
                        &["-c".into(), "cat diagnostic; exit 1".into()],
                        true,
                    )
                    .unwrap_err();
                assert_eq!(error.code, 2, "{diagnostic}: {error}");
            }
        }
        for script in [
            "printf '\\377'; exit 1",
            "cat diagnostic; printf '\\377' >&2; exit 1",
            "printf '{}'; exit 1",
        ] {
            let error = checker
                .process_with_exit_policy("fixture", &["-c".into(), script.into()], true)
                .unwrap_err();
            assert_eq!(error.code, 2, "{script}: {error}");
        }
    }

    #[test]
    fn target_launch_and_output_errors_remain_operational() {
        let checkout = tempfile::tempdir().unwrap();
        let missing = checkout.path().join("missing-lean");
        let mut checker = Checker::new_with_env(checkout.path(), Some(&missing), []).unwrap();
        let error = checker.process_with_exit_policy("fixture", &[], true).unwrap_err();
        assert_eq!(error.code, 2);
        assert!(error.message.contains("could not execute Lean"));

        let mut checker = shell_checker(checkout.path());
        let error = checker
            .process_with_exit_policy(
                "fixture",
                &["-c".to_string(), "printf '\\377'".to_string()],
                true,
            )
            .unwrap_err();
        assert_eq!(error.code, 2);
        assert!(error.message.contains("invalid UTF-8 from Lean"));
    }

    #[test]
    fn preserves_arguments_and_stage_working_directory() {
        let checkout = tempfile::tempdir().unwrap();
        let checker = shell_checker(checkout.path());
        fs::write(checker.stage.join("marker"), b"from-stage\n").unwrap();
        let output = checker
            .launch_lean(&[
                "-c".to_string(),
                "IFS= read -r marker < marker; printf '%s\\000' \"$marker\" \"$@\"".to_string(),
                "fixture".to_string(),
                "space separated".to_string(),
                String::new(),
                "$HOME;*".to_string(),
                "line\nbreak".to_string(),
            ])
            .unwrap();

        assert!(output.status.success());
        assert_eq!(output.stdout, b"from-stage\0space separated\0\0$HOME;*\0line\nbreak\0");
        assert!(output.stderr.is_empty());
    }

    #[test]
    fn launches_with_only_the_filtered_environment() {
        let checkout = tempfile::tempdir().unwrap();
        let checker = Checker::new_with_env(
            checkout.path(),
            Some(Path::new("/usr/bin/env")),
            [
                ("HOME".to_string(), "/selected/home".to_string()),
                ("TMPDIR".to_string(), "/selected/tmp".to_string()),
                ("LANG".to_string(), "C".to_string()),
                ("LC_ALL".to_string(), "C".to_string()),
                ("PATH".to_string(), "/unselected/bin".to_string()),
                ("LEAN_PATH".to_string(), "/unselected/lean".to_string()),
                ("ELAN_TOOLCHAIN".to_string(), "unselected".to_string()),
                ("LD_PRELOAD".to_string(), "/unselected.so".to_string()),
            ],
        )
        .unwrap();
        let output = checker.launch_lean(&[]).unwrap();

        assert!(output.status.success());
        let environment = String::from_utf8(output.stdout).unwrap();
        assert_eq!(
            environment.lines().collect::<BTreeSet<_>>(),
            BTreeSet::from([
                "HOME=/selected/home",
                "LANG=C",
                "LC_ALL=C",
                "PATH=/usr/bin:/bin",
                "TMPDIR=/selected/tmp",
            ])
        );
        assert!(output.stderr.is_empty());
    }

    #[test]
    fn default_memory_limits_match_pinned_unpinned_and_correspondence_policies() {
        let checkout = tempfile::tempdir().unwrap();
        let mut checker = shell_checker(checkout.path());
        assert!(!checker.allow_unpinned_lean());
        assert_eq!(checker.default_lean_memory_limit_mb(None), 2048);
        assert_eq!(checker.default_lean_memory_limit_mb(Some("target-audit")), 2048);
        assert_eq!(checker.default_lean_memory_limit_mb(Some("correspondence-preflight")), 8192);
        assert_eq!(checker.default_lean_memory_limit_mb(Some("correspondence-audit")), 8192);

        checker.set_allow_unpinned_lean(true);
        assert!(checker.allow_unpinned_lean());
        assert_eq!(checker.default_lean_memory_limit_mb(Some("resolve-imports")), 4096);
        // Before admitting any `Std` library module (or for `Init`-only runs),
        // compile and `target-audit` stay capped at 2048 MiB.
        assert_eq!(checker.default_lean_memory_limit_mb(None), 2048);
        assert_eq!(checker.default_lean_memory_limit_mb(Some("target-audit")), 2048);

        // Once the admitted library closure includes a `Std` module, both
        // compilation and `target-audit` rise to 4096 MiB.
        checker.admitted = Some(AdmittedToolchain {
            inspector: checkout.path().join("TrustedBoundary.lean"),
            inspector_sha256: "0".repeat(64),
            lean_sha256: "0".repeat(64),
            version: "Lean 4.35".to_string(),
            prefix: checkout.path().to_path_buf(),
            axioms: Vec::new(),
            foundation_graph: BTreeMap::new(),
            graph: BTreeMap::new(),
            artifacts: BTreeMap::new(),
            library_lock: None,
            library_modules: BTreeSet::from(["Init.Data.BitVec.Basic".to_string()]),
            unpinned: true,
            sysroot_package_roots: BTreeSet::new(),
            unpinned_records: BTreeMap::new(),
            lean_binary_sha256: None,
            exec_lean: checkout.path().join("lean"),
            expected_lean_sha: None,
            inspector_olean: None,
        });
        assert_eq!(checker.default_lean_memory_limit_mb(None), 2048);
        assert_eq!(checker.default_lean_memory_limit_mb(Some("target-audit")), 2048);

        checker.admitted.as_mut().unwrap().library_modules.insert("Std.Data.HashMap".to_string());
        assert_eq!(checker.default_lean_memory_limit_mb(None), 4096);
        assert_eq!(checker.default_lean_memory_limit_mb(Some("target-audit")), 4096);
        assert_eq!(checker.default_lean_memory_limit_mb(Some("correspondence-preflight")), 8192);
        assert_eq!(checker.default_lean_memory_limit_mb(Some("correspondence-audit")), 8192);
    }

    #[test]
    fn unpinned_setup_json_filters_import_arts_to_transitive_closure() {
        let dir = tempfile::tempdir().unwrap();
        let root = fs::canonicalize(dir.path()).unwrap();
        let prefix = root.join("sysroot");
        fs::create_dir_all(prefix.join("lib/lean")).unwrap();
        for name in ["A", "B", "C", "D", "Unrelated"] {
            fs::write(prefix.join("lib/lean").join(format!("{name}.olean")), name).unwrap();
        }
        let lean = root.join("lean");
        fs::write(
            &lean,
            format!(
                "#!/bin/sh\ncase \"$1\" in\n--version) printf 'Lean 4.35\\n' ;;\n\
                 --print-prefix) printf '%s\\n' '{}' ;;\n*) exit 0 ;;\nesac\n",
                prefix.display()
            ),
        )
        .unwrap();
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();
        let inspector = root.join("trusted/audit/TrustedBoundary.lean");
        fs::create_dir_all(inspector.parent().unwrap()).unwrap();
        fs::write(&inspector, "-- stub\n").unwrap();

        let mut checker = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        checker.set_allow_unpinned_lean(true);
        checker.set_sandbox_mode(SandboxMode::Unsandboxed);
        let adm = checker.tool_admission().unwrap();
        for name in ["A", "B", "C", "D", "Unrelated"] {
            let p = prefix
                .join("lib/lean")
                .join(format!("{name}.olean"))
                .to_string_lossy()
                .into_owned();
            adm.artifacts.insert(
                name.to_string(),
                ModuleArtifacts { olean_parts: vec![p], ir_parts: Vec::new() },
            );
        }
        adm.graph.insert(
            "A".to_string(),
            vec![
                ImportEdge {
                    module: "B".to_string(),
                    import_all: false,
                    is_exported: false,
                    is_meta: false,
                },
                ImportEdge {
                    module: "C".to_string(),
                    import_all: false,
                    is_exported: true,
                    is_meta: true,
                },
            ],
        );
        adm.graph.insert(
            "B".to_string(),
            vec![ImportEdge {
                module: "D".to_string(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            }],
        );
        adm.graph.insert("C".to_string(), Vec::new());
        adm.graph.insert("D".to_string(), Vec::new());
        adm.graph.insert("Unrelated".to_string(), Vec::new());

        let setup_path = checker
            .write_setup_json(
                "Target",
                &[ImportEdge {
                    module: "A".to_string(),
                    import_all: false,
                    is_exported: true,
                    is_meta: false,
                }],
            )
            .unwrap();
        let setup: Json = serde_json::from_slice(&fs::read(setup_path).unwrap()).unwrap();
        let keys: BTreeSet<String> =
            setup["importArts"].as_object().unwrap().keys().cloned().collect();
        assert_eq!(
            keys,
            BTreeSet::from(["A".to_string(), "B".to_string(), "C".to_string(), "D".to_string(),])
        );
    }

    #[test]
    fn effective_memory_limits_respect_floors_and_explicit_overrides() {
        let checkout = tempfile::tempdir().unwrap();
        let mut checker = shell_checker(checkout.path());
        checker.set_allow_unpinned_lean(true);
        checker.set_lean_memory_limit_mb(Some(1024));
        assert_eq!(checker.effective_lean_memory_limit_mb(None), 1024);
        assert_eq!(checker.effective_lean_memory_limit_mb(Some("target-audit")), 1024);
        // Floors hold for resolve-imports (4096) and correspondence (8192).
        assert_eq!(checker.effective_lean_memory_limit_mb(Some("resolve-imports")), 4096);
        assert_eq!(checker.effective_lean_memory_limit_mb(Some("correspondence-preflight")), 8192);
        assert_eq!(checker.effective_lean_memory_limit_mb(Some("correspondence-audit")), 8192);

        checker.set_lean_memory_limit_mb(Some(12288));
        assert_eq!(checker.effective_lean_memory_limit_mb(None), 12288);
        assert_eq!(checker.effective_lean_memory_limit_mb(Some("resolve-imports")), 12288);
        assert_eq!(checker.effective_lean_memory_limit_mb(Some("correspondence-audit")), 12288);
    }

    #[test]
    fn export_target_oleans_handles_absent_dir_and_filters_non_olean_artifacts() {
        let checkout = tempfile::tempdir().unwrap();
        let mut checker = shell_checker(checkout.path());
        let dest = checkout.path().join("lean-lib");

        // Absent lib returns Ok(false) without ENOENT.
        assert!(!checker.export_target_oleans(&dest).unwrap());
        assert!(!dest.exists());

        let target_lib = checker.stage.join("lib");
        fs::create_dir_all(target_lib.join("Trusted")).unwrap();
        fs::create_dir_all(target_lib.join("Anneal")).unwrap();
        fs::write(target_lib.join("Trusted/MirAst.olean"), b"olean").unwrap();
        fs::write(target_lib.join("Trusted/MirAst.olean.server"), b"server").unwrap();
        fs::write(target_lib.join("Trusted/MirAst.olean.private"), b"priv").unwrap();
        fs::write(target_lib.join("Trusted/MirAst.ir"), b"ir").unwrap();
        fs::write(target_lib.join("Trusted/MirAst.ir.sig"), b"irsig").unwrap();
        fs::write(target_lib.join("lean-toolchain"), b"lean4:v4.34.1").unwrap();
        fs::write(target_lib.join("Anneal/MirWp.olean"), b"wp").unwrap();
        fs::write(target_lib.join("Proof.olean"), b"proof").unwrap();
        for rel in [
            "Trusted/MirAst.olean",
            "Trusted/MirAst.olean.server",
            "Trusted/MirAst.olean.private",
            "Anneal/MirWp.olean",
            "Proof.olean",
        ] {
            let p = target_lib.join(rel);
            let sha = sha256_file(&p, "test").unwrap();
            checker.olean_ledger.insert(p, sha);
        }
        checker
            .compiled_roles
            .insert("Trusted.MirAst".to_string(), TargetRole::Model);
        checker
            .compiled_roles
            .insert("Anneal.MirWp".to_string(), TargetRole::Proof);
        checker
            .compiled_roles
            .insert("Proof".to_string(), TargetRole::Proof);

        // When `include_authored_proofs == false`, Model and bundled Anneal.*
        // export while authored Proof.olean is gated out.
        let gated_dest = checkout.path().join("lean-lib-gated");
        assert!(
            checker
                .export_target_oleans_gated(&gated_dest, false)
                .unwrap()
        );
        assert!(gated_dest.join("Trusted/MirAst.olean").is_file());
        assert!(gated_dest.join("Anneal/MirWp.olean").is_file());
        assert!(!gated_dest.join("Proof.olean").exists());

        assert!(checker.export_target_oleans(&dest).unwrap());
        assert_eq!(fs::read(dest.join("Trusted/MirAst.olean")).unwrap(), b"olean");
        assert_eq!(fs::read(dest.join("Trusted/MirAst.olean.server")).unwrap(), b"server");
        assert_eq!(fs::read(dest.join("Trusted/MirAst.olean.private")).unwrap(), b"priv");
        assert_eq!(fs::read(dest.join("Proof.olean")).unwrap(), b"proof");
        assert!(!dest.join("Trusted/MirAst.ir").exists());
        assert!(!dest.join("Trusted/MirAst.ir.sig").exists());
        assert!(!dest.join("lean-toolchain").exists());

        // Any unledgered `.olean*` file in `lib` (for example written directly
        // by an unsandboxed elaborator) must fail closed on both passing and
        // `proof_failed` exports without creating `dest`.
        let rogue = target_lib.join("Rogue.olean");
        fs::write(&rogue, b"rogue").unwrap();
        for include_authored in [true, false] {
            let rogue_dest = checkout.path().join("lean-lib-rogue");
            let err = checker
                .export_target_oleans_gated(&rogue_dest, include_authored)
                .unwrap_err();
            assert_eq!(err.code, 2);
            assert_eq!(err.phase, "export-lean-lib");
            assert!(
                err.message.contains("unledgered artifact"),
                "{}",
                err.message
            );
            assert!(!rogue_dest.exists());
        }
        fs::remove_file(&rogue).unwrap();

        // An `olean_ledger` mismatch on a non-Proof module must fail closed
        // during `export_target_oleans_gated(_, false)` with exit code 2.
        checker.olean_ledger.insert(
            target_lib.join("Trusted/MirAst.olean"),
            "0".repeat(64),
        );
        let tampered_dest = checkout.path().join("lean-lib-tampered");
        let err = checker
            .export_target_oleans_gated(&tampered_dest, false)
            .unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "export-lean-lib");
        assert!(
            err.message.contains("changed before export"),
            "{}",
            err.message
        );
        assert!(
            !tampered_dest.exists(),
            "failed export must not leave partial lean-lib directory"
        );
    }

    #[test]
    fn export_target_oleans_gated_is_atomic_on_validation_failure() {
        let checkout = tempfile::tempdir().unwrap();
        let mut checker = shell_checker(checkout.path());
        let target_lib = checker.stage.join("lib");
        fs::create_dir_all(target_lib.join("Anneal")).unwrap();
        fs::create_dir_all(target_lib.join("Trusted")).unwrap();

        let first = target_lib.join("Anneal/MirWp.olean");
        let second = target_lib.join("Trusted/MirAst.olean");
        fs::write(&first, b"valid-first-olean").unwrap();
        fs::write(&second, b"tampered-second-olean").unwrap();
        checker
            .compiled_roles
            .insert("Anneal.MirWp".to_string(), TargetRole::Proof);
        checker
            .compiled_roles
            .insert("Trusted.MirAst".to_string(), TargetRole::Model);

        // Artifact #1 passes ledger validation (`Anneal/MirWp.olean` sorts
        // before `Trusted/MirAst.olean`), while artifact #2 fails ledger
        // validation. `export_target_oleans_gated` must return `Err` and leave
        // neither `dest` nor any sibling `.lean-lib-stage-*` directory behind.
        checker
            .olean_ledger
            .insert(first.clone(), sha256_file(&first, "test").unwrap());
        checker
            .olean_ledger
            .insert(second.clone(), "0".repeat(64));

        let work = tempfile::tempdir().unwrap();
        let lean_lib_dir = work.path().join("lean-lib");
        let err = checker
            .export_target_oleans_gated(&lean_lib_dir, false)
            .unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "export-lean-lib");
        assert!(
            err.message.contains("changed before export"),
            "{}",
            err.message
        );
        assert!(
            !lean_lib_dir.exists(),
            "work/lean-lib must not exist when a later artifact fails validation"
        );
        assert_eq!(
            fs::read_dir(work.path()).unwrap().count(),
            0,
            "no temporary staging directory may remain after failed export"
        );

        // Even when a stale `lean-lib` directory already existed before the
        // call, a validation failure must leave `!lean_lib_dir.exists()`.
        fs::create_dir_all(&lean_lib_dir).unwrap();
        fs::write(lean_lib_dir.join("Stale.olean"), b"stale").unwrap();
        let err_stale = checker
            .export_target_oleans_gated(&lean_lib_dir, false)
            .unwrap_err();
        assert_eq!(err_stale.code, 2);
        assert_eq!(err_stale.phase, "export-lean-lib");
        assert!(
            !lean_lib_dir.exists(),
            "stale work/lean-lib directory must be removed on validation failure"
        );

        // A missing ledgered artifact (deleted after promotion) must also fail
        // closed without leaving `work/lean-lib`.
        checker
            .olean_ledger
            .insert(second.clone(), sha256_file(&second, "test").unwrap());
        fs::remove_file(&second).unwrap();
        let err_missing = checker
            .export_target_oleans_gated(&lean_lib_dir, false)
            .unwrap_err();
        assert_eq!(err_missing.code, 2);
        assert_eq!(err_missing.phase, "export-lean-lib");
        assert!(
            err_missing.message.contains("missing before export"),
            "{}",
            err_missing.message
        );
        assert!(!lean_lib_dir.exists());
    }

    #[test]
    fn export_target_oleans_gated_rejects_invalid_and_trailing_slash_symlink_dests() {
        let checkout = tempfile::tempdir().unwrap();
        let checker = shell_checker(checkout.path());

        for bad in ["", "/", ".", "..", "foo/.", "foo/.."] {
            let err = checker
                .export_target_oleans_gated(Path::new(bad), false)
                .unwrap_err();
            assert_eq!(err.code, 2, "path {bad:?}");
            assert_eq!(err.phase, "export-lean-lib", "path {bad:?}");
            assert!(
                err.message.contains("invalid export destination path"),
                "path {bad:?}: {}",
                err.message
            );
        }

        #[cfg(unix)]
        {
            let dir = tempfile::tempdir().unwrap();
            let victim = dir.path().join("victim");
            fs::create_dir_all(&victim).unwrap();
            let sentinel = victim.join("keep.txt");
            fs::write(&sentinel, b"untouched").unwrap();
            let link = dir.path().join("link");
            std::os::unix::fs::symlink(&victim, &link).unwrap();

            for suffix in ["/", "/."] {
                let mut raw = link.as_os_str().to_os_string();
                raw.push(suffix);
                let err = checker
                    .export_target_oleans_gated(Path::new(&raw), false)
                    .unwrap_err();
                assert_eq!(err.code, 2, "suffix {suffix:?}");
                assert_eq!(err.phase, "export-lean-lib", "suffix {suffix:?}");
                assert!(
                    err.message.contains("invalid export destination path"),
                    "suffix {suffix:?}: {}",
                    err.message
                );
                assert!(
                    sentinel.exists(),
                    "symlink target file must survive rejected dest with suffix {suffix:?}"
                );
            }

            let err_plain = checker
                .export_target_oleans_gated(&link, false)
                .unwrap_err();
            assert_eq!(err_plain.code, 2);
            assert_eq!(err_plain.phase, "export-lean-lib");
            assert!(sentinel.exists());
        }
    }

    #[test]
    fn artifact_ledger_catches_tampered_inspector_olean() {
        let dir = tempfile::tempdir().unwrap();
        let root = fs::canonicalize(dir.path()).unwrap();
        let inspector = root.join("TrustedBoundary.lean");
        let olean = root.join("TrustedBoundary.olean");
        fs::write(&inspector, b"-- inspector\n").unwrap();
        fs::write(&olean, b"initial olean bytes").unwrap();

        let mut checker = shell_checker(&root);
        checker.admitted = Some(AdmittedToolchain {
            inspector: inspector.clone(),
            inspector_sha256: sha256_file(&inspector, "test").unwrap(),
            lean_sha256: String::new(),
            version: "Lean 4.34.1".to_string(),
            prefix: root.clone(),
            axioms: Vec::new(),
            foundation_graph: BTreeMap::new(),
            graph: BTreeMap::new(),
            artifacts: BTreeMap::new(),
            library_lock: None,
            library_modules: BTreeSet::new(),
            unpinned: false,
            sysroot_package_roots: BTreeSet::new(),
            unpinned_records: BTreeMap::new(),
            lean_binary_sha256: None,
            exec_lean: PathBuf::from("/bin/sh"),
            expected_lean_sha: None,
            inspector_olean: Some((olean.clone(), sha256_file(&olean, "test").unwrap())),
        });

        checker.verify_artifact_ledger(&[]).unwrap();

        fs::write(&olean, b"tampered olean bytes").unwrap();
        let err = checker.verify_artifact_ledger(&[]).unwrap_err();
        assert_eq!(err.code, 2);
        assert_eq!(err.phase, "artifact-ledger");
        assert!(
            err.message.contains("TrustedBoundary.olean"),
            "{}",
            err.message
        );
    }

    #[cfg(unix)]
    #[test]
    fn colon_in_stage_dir_succeeds_across_tier2_tier1_and_unsandboxed_with_decoy() {
        use crate::target::{TargetAuditRequest, TargetBindings, TargetModule};

        let lean_bin = default_lean_path();
        if !lean_bin.is_file() {
            return;
        }
        let anneal_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap();

        // Place a corrupt decoy `TrustedBoundary.olean` at `<outer>/evil/` and
        // construct each `Checker`'s stage inside `<outer>/evil:sub/...` so any
        // host-path `LEAN_PATH` split on `:` either crashes Tier 2 module
        // lookup or hijacks `Unsandboxed` runs with the corrupt decoy.
        let outer = tempfile::Builder::new()
            .prefix("anneal-colon-target-")
            .tempdir()
            .unwrap();
        let split_prefix = outer.path().join("evil");
        fs::create_dir_all(&split_prefix).unwrap();
        fs::write(split_prefix.join("TrustedBoundary.olean"), b"corrupt-decoy").unwrap();
        let colon_parent = outer.path().join("evil:sub");
        fs::create_dir_all(&colon_parent).unwrap();

        let src_dir = tempfile::tempdir().unwrap();
        let sources = [
            (
                "Model",
                TargetRole::Model,
                "prelude\nimport Init.Prelude\nimport Init.Core\n\
                 namespace Trusted.MirSemantics\n\
                 structure Crate where\n  program : Nat\n  specs : Nat → Prop\n\
                 def UnitTheorem (c : Crate) : Prop := c.specs c.program\n\
                 end Trusted.MirSemantics\n",
            ),
            (
                "Captured",
                TargetRole::Capture,
                "prelude\nimport Model\ndef Captured.program : Nat := 0\n",
            ),
            (
                "Spec",
                TargetRole::Specification,
                "prelude\nimport Model\ndef Spec.specs (_ : Nat) : Prop := True\n",
            ),
            (
                "Expected",
                TargetRole::Expected,
                "prelude\nimport Captured\nimport Spec\n\
                 def Expected.claim : Prop := Trusted.MirSemantics.UnitTheorem \
                 (Trusted.MirSemantics.Crate.mk Captured.program Spec.specs)\n",
            ),
            (
                "Proof",
                TargetRole::Proof,
                "prelude\nimport Expected\n\
                 theorem Proof.verify : Expected.claim := True.intro\n",
            ),
        ];
        let modules: Vec<TargetModule> = sources
            .iter()
            .map(|(name, role, text)| {
                let path = src_dir.path().join(format!("{name}.lean"));
                fs::write(&path, text.as_bytes()).unwrap();
                TargetModule {
                    module: (*name).to_owned(),
                    source: path,
                    expected_sha256: sha256_bytes(text.as_bytes()),
                    role: *role,
                }
            })
            .collect();
        let digest = modules[0].expected_sha256.clone();
        let req = TargetAuditRequest {
            modules,
            theorem_module: "Proof".to_owned(),
            theorem_name: "Proof.verify".to_owned(),
            expected_module: "Expected".to_owned(),
            expected_declaration: "Expected.claim".to_owned(),
            canonical_root: "Trusted.MirSemantics.UnitTheorem".to_owned(),
            subject_declaration: "Captured.program".to_owned(),
            specification_declaration: "Spec.specs".to_owned(),
            allow_sorry_in_proof: false,
            bindings: TargetBindings {
                request_sha256: digest.clone(),
                capture_sha256: digest.clone(),
                model_manifest_sha256: digest.clone(),
                specification_manifest_sha256: digest,
            },
        };

        let make_colon_checker = || -> Checker {
            let mut checker = Checker::new(anneal_root, Some(&lean_bin)).unwrap();
            let mut builder = tempfile::Builder::new();
            builder.prefix("stage-");
            builder.permissions(fs::Permissions::from_mode(0o700));
            let stage_dir = builder.tempdir_in(&colon_parent).unwrap();
            let stage_canon = fs::canonicalize(stage_dir.path()).unwrap();
            assert!(
                stage_canon.to_string_lossy().contains(':'),
                "expected colon in stage path: {}",
                stage_canon.display()
            );
            checker._stage_dir = stage_dir;
            checker.stage = stage_canon;
            checker
        };

        // 1. `SandboxMode::Unsandboxed`: must not read the corrupt decoy at
        //    `<outer>/evil/TrustedBoundary.olean`.
        let mut unsandboxed = make_colon_checker();
        unsandboxed.set_sandbox_mode(SandboxMode::Unsandboxed);
        let rep_unsandboxed = unsandboxed.run_target(&req).unwrap();
        assert_eq!(unsandboxed.active_sandbox(), Some(ActiveSandbox::None));
        assert_eq!(rep_unsandboxed["replay"], json!(true));

        // 2. Default Tier 1 (`linux_bwrap`) and forced Tier 2
        //    (`linux_landlock_seccomp`) on Linux. (`run_target` resets
        //    `sandbox_runtime`, so after verifying `run_target` under the
        //    default runtime we pin `sandbox_runtime` to `force_tier2_runtime`
        //    and run both `inspect_headers` and `inspect_target` directly.)
        #[cfg(target_os = "linux")]
        {
            let mut default_sb = make_colon_checker();
            let rep_default = default_sb.run_target(&req).unwrap();
            assert_ne!(default_sb.active_sandbox(), Some(ActiveSandbox::None));
            assert_eq!(rep_default["replay"], json!(true));

            let (exec_lean, prefix) = {
                let adm = default_sb.admitted().unwrap();
                (adm.exec_lean.clone(), adm.prefix.clone())
            };
            if let Ok(rt) = crate::sandbox::force_tier2_runtime(&exec_lean, &prefix) {
                default_sb.sandbox_runtime = Some(rt);
                let hdrs = default_sb
                    .inspect_headers(&[("Spec".to_string(), req.modules[2].source.clone())])
                    .unwrap();
                assert_eq!(
                    default_sb.active_sandbox(),
                    Some(ActiveSandbox::LinuxLandlockSeccomp)
                );
                assert!(hdrs.get("headers").and_then(|v| v.as_array()).is_some());

                let rep_tier2 = default_sb.inspect_target(&req).unwrap();
                assert_eq!(
                    default_sb.active_sandbox(),
                    Some(ActiveSandbox::LinuxLandlockSeccomp)
                );
                assert_eq!(rep_tier2["replay"], json!(true));
            }
        }
    }

    #[test]
    fn olean_rel_path_to_module_name_and_proof_gate_normalize_separators() {
        assert_eq!(
            olean_rel_path_to_module_name(Path::new("Proof.olean")).as_deref(),
            Some("Proof")
        );
        assert_eq!(
            olean_rel_path_to_module_name(Path::new("My/Nested/Proof.olean")).as_deref(),
            Some("My.Nested.Proof")
        );
        assert_eq!(
            olean_rel_path_to_module_name(Path::new(r"My\Nested\Proof.olean")).as_deref(),
            Some("My.Nested.Proof")
        );
        assert_eq!(
            olean_rel_path_to_module_name(Path::new(r"My\Nested/Proof.olean.server")).as_deref(),
            Some("My.Nested.Proof")
        );
        assert_eq!(
            olean_rel_path_to_module_name(Path::new(r"My\Nested\Proof.olean.private")).as_deref(),
            Some("My.Nested.Proof")
        );
        assert_eq!(
            olean_rel_path_to_module_name(Path::new(r"Anneal\MirWp\Scalars.olean")).as_deref(),
            Some("Anneal.MirWp.Scalars")
        );
        assert!(olean_rel_path_to_module_name(Path::new("")).is_none());
        assert!(olean_rel_path_to_module_name(Path::new(".olean")).is_none());
        assert!(olean_rel_path_to_module_name(Path::new("../Proof.olean")).is_none());
        assert!(olean_rel_path_to_module_name(Path::new("/Proof.olean")).is_none());

        let dir = tempfile::tempdir().unwrap();
        let mut checker = Checker::new(dir.path(), Some(Path::new("/nonexistent/lean"))).unwrap();
        checker.compiled_roles.insert("My.Nested.Proof".to_owned(), TargetRole::Proof);
        checker.compiled_roles.insert("My.Nested.Spec".to_owned(), TargetRole::Specification);
        checker.compiled_roles.insert("Anneal.MirWp.Scalars".to_owned(), TargetRole::Proof);

        for rel in [
            "My/Nested/Proof.olean",
            "My/Nested/Proof.olean.server",
            "My/Nested/Proof.olean.private",
            r"My\Nested\Proof.olean",
            r"My\Nested\Proof.olean.server",
            r"My\Nested\Proof.olean.private",
        ] {
            assert!(
                checker.is_gated_authored_proof(Path::new(rel), false),
                "{rel} must be gated out on proof_failed"
            );
            assert!(
                !checker.is_gated_authored_proof(Path::new(rel), true),
                "{rel} must be allowed when include_authored_proofs is true"
            );
        }
        for rel in [
            "My/Nested/Spec.olean",
            r"My\Nested\Spec.olean",
            "Anneal/MirWp/Scalars.olean",
            r"Anneal\MirWp\Scalars.olean",
        ] {
            assert!(
                !checker.is_gated_authored_proof(Path::new(rel), false),
                "{rel} must remain exported on proof_failed"
            );
        }
        assert!(
            checker.is_gated_authored_proof(Path::new("../Escape.olean"), false),
            "non-normal relative paths must fail closed when gating authored proofs"
        );
    }

    #[test]
    fn elan_settings_and_toolchain_candidates_parse_and_reject_traversal() {
        assert_eq!(
            parse_elan_default_toolchain(
                "# header comment\n\
                 telemetry = false\n\
                 default_toolchain = \"leanprover/lean4:v4.34.1\" # inline\n\
                 [overrides]\n\
                 default_toolchain = \"ignored\"\n"
            )
            .as_deref(),
            Some("leanprover/lean4:v4.34.1")
        );
        assert_eq!(
            parse_elan_default_toolchain("default_toolchain = 'v4.35.0'\n").as_deref(),
            Some("v4.35.0")
        );
        assert_eq!(
            parse_elan_default_toolchain("[overrides]\ndefault_toolchain = \"late\"\n"),
            None
        );

        assert_eq!(
            elan_toolchain_dir_candidates("leanprover/lean4:v4.34.1").unwrap(),
            vec!["leanprover--lean4---v4.34.1"]
        );
        assert_eq!(
            elan_toolchain_dir_candidates("4.34.1").unwrap(),
            vec![
                "4.34.1",
                "leanprover--lean4---v4.34.1",
                "leanprover--lean4---4.34.1",
            ]
        );
        for bad in ["", "-flag", "../evil", "foo/../bar", r"foo\bar", "a\0b"] {
            assert!(
                elan_toolchain_dir_candidates(bad).is_err(),
                "expected {bad:?} to fail closed"
            );
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn unpinned_admission_failure_after_probe_preserves_active_sandbox() {
        let lean = crate::default_lean_path();
        if !lean.is_file() {
            return;
        }
        let anneal_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap();
        let mut checker = Checker::new(anneal_root, Some(&lean)).unwrap();
        checker.set_allow_unpinned_lean(true);
        // `SandboxRuntime::probe` uses `DEFAULT_CHILD_TIMEOUT`, whereas the
        // subsequent sandboxed `--version` query uses `self.child_timeout`, so a
        // 1ns `child_timeout` exercises post-probe admission failure deterministically.
        checker.set_child_timeout(Duration::from_nanos(1));
        let err = checker
            .tool_admission()
            .expect_err("1ns query timeout must fail unpinned admission after probe");
        assert_eq!(err.phase, "sandbox-timeout", "{err}");
        assert!(
            matches!(
                checker.active_sandbox(),
                Some(ActiveSandbox::LinuxBwrap | ActiveSandbox::LinuxLandlockSeccomp)
            ),
            "expected probed active_sandbox after post-probe query failure, got {:?}",
            checker.active_sandbox()
        );
        assert!(
            checker.sandbox_runtime.is_none(),
            "failed admission must not cache unverified sandbox_runtime"
        );
    }
}
