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
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::{Arc, Mutex, OnceLock},
};

use serde::Deserialize;
use serde_json::json;

use crate::toolchain::{
    AdmittedToolchain, CompiledInspectorPaths, Failure, FoundationLock, ImportEdge, Json,
    LibraryLock, ModuleArtifacts, OLEAN_PARTS, PARTS, ParallelDagPlan, TOOLCHAIN,
    default_lean_path, is_sha256_hex, regular, run_parallel_dag, sha256_file, stage_regular_file,
    verify_installed_module_record,
};

/// Cache key for precompiled `TrustedBoundary.olean` artifacts held in process
/// memory: `(lean_binary_sha256, canonical_sysroot_prefix, inspector_sha256)`.
type InspectorCacheKey = (String, PathBuf, String);

/// In-memory bytes of the compiled `TrustedBoundary` `.olean*` parts.
#[derive(Debug)]
struct CompiledInspectorArtifacts {
    files: Vec<(String, Vec<u8>)>,
}

/// Process-wide cache of compiled `TrustedBoundary` `.olean*` parts keyed by
/// admitted toolchain + inspector source digest. Each [`Checker`] materializes
/// the bytes into its own private `0o700` stage directory so no `/tmp`
/// directories outlive a run and concurrent callers never share writable paths.
fn compiled_inspector_cache()
-> &'static Mutex<BTreeMap<InspectorCacheKey, Arc<Mutex<Option<Arc<CompiledInspectorArtifacts>>>>>>
{
    static CACHE: OnceLock<
        Mutex<BTreeMap<InspectorCacheKey, Arc<Mutex<Option<Arc<CompiledInspectorArtifacts>>>>>>,
    > = OnceLock::new();
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

fn write_setup_json_to_stage(
    stage: &Path,
    artifacts: &BTreeMap<String, ModuleArtifacts>,
    module: &str,
    imports: &[ImportEdge],
) -> Result<PathBuf, Failure> {
    let import_arts: BTreeMap<&str, [&[String]; 2]> =
        artifacts.iter().map(|(k, v)| (k.as_str(), v.to_wire())).collect();
    let setup_obj = json!({
        "name": module,
        "isModule": false,
        "imports": imports,
        "importArts": import_arts,
        "dynlibs": [],
        "plugins": [],
        "options": {},
    });
    let setup_path = stage.join(format!("{module}.setup.json"));
    let bytes =
        serde_json::to_vec(&setup_obj).map_err(|e| Failure::new(2, "setup", e.to_string()))?;
    fs::write(&setup_path, bytes).map_err(|e| Failure::new(2, "setup", e.to_string()))?;
    Ok(setup_path)
}

fn build_lean_compile_args(
    setup_path: &Path,
    output: &Path,
    src_path: &Path,
    warn_as_err: bool,
    target_rejection: bool,
) -> Vec<String> {
    let mut compile_args = vec![
        "-j1".to_string(),
        "-M2048".to_string(),
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

/// Executes Lean 4.34.1 compilation and `TrustedBoundary.lean` inspection
/// inside a private `0o700` staging directory.
pub struct Checker {
    _stage_dir: tempfile::TempDir,
    root: PathBuf,
    lean: PathBuf,
    pub(crate) stage: PathBuf,
    pub(crate) execution_began: bool,
    environment: BTreeMap<String, String>,
    counter: usize,
    admitted: Option<AdmittedToolchain>,
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
        let stage = stage_dir.path().to_path_buf();

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
            counter: 0,
            admitted: None,
        })
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

    /// Advance and return the monotonic request/process counter.
    #[doc(hidden)]
    pub fn next_counter(&mut self) -> usize {
        self.counter += 1;
        self.counter
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
        Ok(())
    }

    /// Stage `TrustedBoundary.lean`, validate `lean-toolchain`,
    /// `foundation-lock.json`, and the `library-lock.json` catalog when
    /// present, and compare the `lean` executable and every
    /// `foundation-lock.json` source and `.olean`/`.ir` artifact with its
    /// locked SHA-256 digest.
    ///
    /// The Lean shared libraries that the executable loads, which contain the
    /// kernel and elaborator, and the sysroot modules outside the locks are
    /// not hashed. Only `lean --version` identifies them, so their integrity
    /// rests on the uncompromised execution environment that
    /// `THREAT_MODEL.md` assumes. Library digests are checked later, when
    /// target imports reach them.
    #[doc(hidden)]
    pub fn tool_admission(&mut self) -> Result<&mut AdmittedToolchain, Failure> {
        let inspector_src = self.root.join("trusted/audit/TrustedBoundary.lean");
        let inspector = self.stage.join("src/TrustedBoundary.lean");
        let inspector_sha256 = stage_regular_file(&inspector_src, &inspector, "tool-snapshot")?;

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

        // This digest covers only the executable. The pinned build links it
        // from "${LIB}/temp/libleanmain.a" against `libleanshared`, which
        // links "-lInit -lStd -lLean -lleancpp" on Linux and macOS: the
        // compiled `Lean` package, including the elaborator, and C++ objects
        // that include the kernel.
        // https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/stdlib.make.in#L188-L190
        // https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/stdlib.make.in#L157-L163
        // https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/CMakeLists.txt#L859-L872
        let lean_sha = sha256_file(&self.lean, "toolchain")?;
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

        let mut artifacts = BTreeMap::new();
        for (module, record) in &parsed_lock.modules {
            let mod_arts = verify_installed_module_record(&prefix, module, record, "foundation")?;
            artifacts.insert(module.clone(), mod_arts);
        }

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
            compiled_inspector: None,
            version: actual_version,
            prefix,
            axioms: parsed_lock.axioms,
            foundation_graph: parsed_lock.graph.clone(),
            graph: parsed_lock.graph,
            artifacts,
            library_lock,
            library_modules: BTreeSet::new(),
        });
        Ok(self.admitted.as_mut().unwrap())
    }

    /// Capture a Lean child in the stage with only the selected environment.
    #[cfg(test)]
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
        let mut cmd = Command::new(&self.lean);
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
        self.counter += 1;
        let output = self
            .launch_lean_with_path(arguments, lean_path)
            .map_err(|e| Failure::new(2, label, format!("could not execute Lean: {e}")))?;
        check_lean_output(label, output, ordinary_rejection)
    }

    /// Write a `<module>.setup.json` descriptor for `lean --setup`.
    #[doc(hidden)]
    pub fn write_setup_json(
        &self,
        module: &str,
        imports: &[ImportEdge],
    ) -> Result<PathBuf, Failure> {
        let adm = self.admitted()?;
        write_setup_json_to_stage(&self.stage, &adm.artifacts, module, imports)
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
            warn_as_err,
            target_rejection,
        );
        self.process_with_exit_policy(
            &format!("compile-{module}"),
            &compile_args,
            target_rejection,
        )?;
        let mod_arts = collect_compiled_artifacts(module, &output)?;
        let adm = self.admitted_mut()?;
        adm.artifacts.insert(module.to_string(), mod_arts);
        adm.graph.insert(module.to_string(), edge_list);
        Ok(())
    }

    /// Compile a topologically ordered batch of staged `.lean` modules in
    /// parallel along their verified import DAG across at most `max_workers`
    /// workers, preserving deterministic earliest-order failure reporting and
    /// serialized registration into `self.admitted`.
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
        self.counter += order.len();

        let lean = &self.lean;
        let stage = &self.stage;
        let environment = &self.environment;
        let adm = self
            .admitted
            .as_mut()
            .expect("toolchain admission verified above");

        run_parallel_dag(
            &plan,
            max_workers,
            "compile",
            "worker panicked during Lean compilation",
            adm,
            |adm, idx| {
                let module = &order[idx];
                let edge_list = &imports[module];
                let src_path = &sources[module];
                let setup_path =
                    write_setup_json_to_stage(stage, &adm.artifacts, module, edge_list)?;
                let output =
                    stage.join(lib_subdir).join(format!("{}.olean", module.replace('.', "/")));
                if let Some(parent) = output.parent() {
                    fs::create_dir_all(parent)
                        .map_err(|e| Failure::operational("compile", e.to_string()))?;
                }
                let compile_args = build_lean_compile_args(
                    &setup_path,
                    &output,
                    src_path,
                    warn_as_err,
                    target_rejection,
                );
                Ok((output, compile_args))
            },
            |idx, (output_path, compile_args)| {
                let module = &order[idx];
                let label = format!("compile-{module}");
                let output = Command::new(lean)
                    .args(&compile_args)
                    .current_dir(stage)
                    .env_clear()
                    .envs(environment)
                    .output()
                    .map_err(|e| {
                        Failure::new(2, &label, format!("could not execute Lean: {e}"))
                    })?;
                check_lean_output(&label, output, target_rejection)?;
                collect_compiled_artifacts(module, &output_path)
            },
            |adm, idx, mod_arts| {
                let module = &order[idx];
                adm.artifacts.insert(module.clone(), mod_arts);
                adm.graph.insert(module.clone(), imports[module].clone());
                Ok(())
            },
        )
    }

    /// Compile `TrustedBoundary.lean` once per
    /// `(lean_sha256, sysroot_prefix, inspector_sha256)` using the admitted
    /// pinned `lean` binary and materialize the `.olean` plus a 1-line
    /// `import TrustedBoundary` runner in `<stage>/inspector-lib`.
    fn ensure_compiled_inspector(&mut self) -> Result<CompiledInspectorPaths, Failure> {
        let (key, inspector) = {
            let adm = self.admitted()?;
            if let Some(paths) = &adm.compiled_inspector {
                return Ok(paths.clone());
            }
            (
                (adm.lean_sha256.clone(), adm.prefix.clone(), adm.inspector_sha256.clone()),
                adm.inspector.clone(),
            )
        };

        let slot = {
            let mut map = compiled_inspector_cache().lock().unwrap_or_else(|e| e.into_inner());
            map.entry(key).or_insert_with(|| Arc::new(Mutex::new(None))).clone()
        };

        let lib_dir = self.stage.join("inspector-lib");
        let mut dir_builder = fs::DirBuilder::new();
        #[cfg(unix)]
        dir_builder.mode(0o700);
        dir_builder
            .create(&lib_dir)
            .map_err(|e| Failure::operational("compile-inspector", e.to_string()))?;

        let mut populate = || -> Result<PathBuf, Failure> {
            let cached = {
                let mut guard = slot.lock().unwrap_or_else(|e| e.into_inner());
                if let Some(arts) = guard.as_ref() {
                    Some(Arc::clone(arts))
                } else {
                    let root_dir = inspector.parent().ok_or_else(|| {
                        Failure::operational(
                            "compile-inspector",
                            "staged inspector missing parent dir",
                        )
                    })?;
                    let olean_out = lib_dir.join("TrustedBoundary.olean");
                    self.process(
                        "compile-inspector",
                        &[
                            "-j1".to_string(),
                            "-M2048".to_string(),
                            "-t0".to_string(),
                            "-DElab.async=false".to_string(),
                            "-Ddebug.skipKernelTC=false".to_string(),
                            "-R".to_string(),
                            root_dir.to_string_lossy().into_owned(),
                            "-o".to_string(),
                            olean_out.to_string_lossy().into_owned(),
                            inspector.to_string_lossy().into_owned(),
                        ],
                    )?;
                    let expected_names: BTreeSet<String> =
                        OLEAN_PARTS.iter().map(|part| format!("TrustedBoundary.{part}")).collect();
                    for entry in fs::read_dir(&lib_dir)
                        .map_err(|e| Failure::operational("compile-inspector", e.to_string()))?
                    {
                        let entry = entry.map_err(|e| {
                            Failure::operational("compile-inspector", e.to_string())
                        })?;
                        let name = entry.file_name().to_string_lossy().into_owned();
                        if !expected_names.contains(&name) {
                            return Err(Failure::policy(
                                "compile-inspector",
                                format!(
                                    "unexpected file emitted while compiling inspector: {name}"
                                ),
                            ));
                        }
                    }
                    let mut files = Vec::new();
                    for part in OLEAN_PARTS {
                        let name = format!("TrustedBoundary.{part}");
                        let path = lib_dir.join(&name);
                        if fs::symlink_metadata(&path).is_ok() {
                            regular(&path, "compile-inspector")?;
                            let bytes = fs::read(&path).map_err(|e| {
                                Failure::operational("compile-inspector", e.to_string())
                            })?;
                            files.push((name, bytes));
                        }
                    }
                    if !files.iter().any(|(n, _)| n == "TrustedBoundary.olean") {
                        return Err(Failure::operational(
                            "compile-inspector",
                            "compiler omitted TrustedBoundary.olean",
                        ));
                    }
                    *guard = Some(Arc::new(CompiledInspectorArtifacts { files }));
                    None
                }
            };
            if let Some(arts) = cached {
                for (name, bytes) in &arts.files {
                    fs::write(lib_dir.join(name), bytes)
                        .map_err(|e| Failure::operational("compile-inspector", e.to_string()))?;
                }
            }

            let runner = lib_dir.join("Runner.lean");
            fs::write(&runner, "import TrustedBoundary\n")
                .map_err(|e| Failure::operational("compile-inspector", e.to_string()))?;
            Ok(runner)
        };

        let runner = match populate() {
            Ok(runner) => runner,
            Err(err) => {
                let _ = fs::remove_dir_all(&lib_dir);
                return Err(err);
            }
        };

        let paths = CompiledInspectorPaths { lib_dir, runner };
        self.admitted_mut()?.compiled_inspector = Some(paths.clone());
        Ok(paths)
    }

    /// Materialize the compiled inspector directory for a sandboxed invocation.
    #[doc(hidden)]
    pub fn compiled_inspector_lib(&mut self) -> Result<PathBuf, Failure> {
        Ok(self.ensure_compiled_inspector()?.lib_dir)
    }

    /// Invoke the staged inspector with a serialized JSON request and
    /// validate its structured response envelope (`policy:` -> code `1`,
    /// operational -> code `2`).
    #[doc(hidden)]
    pub fn invoke_inspector(&mut self, mode: &str, req: &Json) -> Result<Json, Failure> {
        let compiled = self.ensure_compiled_inspector()?;
        self.counter += 1;
        let stem = self.stage.join(format!("request-{:03}-{mode}", self.counter));
        let request_path = PathBuf::from(format!("{}.json", stem.display()));
        let result_path = PathBuf::from(format!("{}.result.json", stem.display()));
        let req_bytes = serde_json::to_vec(req)
            .map_err(|e| Failure::new(2, mode, format!("cannot serialize request: {e}")))?;
        fs::write(&request_path, req_bytes)
            .map_err(|e| Failure::new(2, mode, format!("cannot write request: {e}")))?;

        // Keep Pass 1 (`preflight`, `audit`) and target modes (`headers`,
        // `target-audit`) capped at `-M2048` over untrusted code, raising the
        // limit to `-M8192` only for Pass 2 (`correspondence-preflight`,
        // `correspondence-audit`) when loading the 160-module `lean-miri` and
        // `Lean.*` closure environment.
        let mem_limit = match mode {
            "correspondence-preflight" | "correspondence-audit" => "-M8192",
            _ => "-M2048",
        };
        let args = vec![
            "-j1".to_string(),
            mem_limit.to_string(),
            "--run".to_string(),
            compiled.runner.to_string_lossy().into_owned(),
            request_path.to_string_lossy().into_owned(),
            result_path.to_string_lossy().into_owned(),
        ];
        // Bootstrap only from the stage. The inspector resets Lean's search
        // path before loading modules described by the request.
        let output = self
            .launch_lean_with_path(&args, Some(OsStr::new("inspector-lib")))
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

#[cfg(all(test, unix))]
mod process_tests {
    use super::*;

    fn shell_checker(checkout: &Path) -> Checker {
        Checker::new_with_env(checkout, Some(Path::new("/bin/sh")), []).unwrap()
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

        // Passing an explicit hermetic `LEAN_PATH` exposes only that path while
        // keeping ambient `LEAN_PATH`, `ELAN_TOOLCHAIN`, and `LD_PRELOAD`
        // stripped.
        let with_path = checker
            .launch_lean_with_path(&[], Some(std::ffi::OsStr::new("/staged/inspector-lib")))
            .unwrap();
        assert!(with_path.status.success());
        let env_with_path = String::from_utf8(with_path.stdout).unwrap();
        assert_eq!(
            env_with_path.lines().collect::<BTreeSet<_>>(),
            BTreeSet::from([
                "HOME=/selected/home",
                "LANG=C",
                "LC_ALL=C",
                "LEAN_PATH=/staged/inspector-lib",
                "PATH=/usr/bin:/bin",
                "TMPDIR=/selected/tmp",
            ])
        );
        assert!(with_path.stderr.is_empty());
    }
}
