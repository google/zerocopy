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

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::OsStr;
use std::fs;
use std::io;
#[cfg(unix)]
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde::Deserialize;
use serde_json::json;

use crate::toolchain::{
    AdmittedToolchain, FOUNDATION_AXIOMS, Failure, FoundationLock, ImportEdge, Json, LibraryLock,
    ModuleArtifacts, PARTS, TOOLCHAIN, default_lean_path, is_sha256_hex, regular,
    scan_sysroot_package_roots, sha256_file, stage_regular_file, transitive_import_closure,
    verify_installed_module_record,
};

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
            || diagnostic
                .kind
                .trim_start_matches("nested.")
                .starts_with("runtime.")
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
    allow_unpinned_lean: bool,
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
        let lean = if lean_raw.is_absolute() {
            lean_raw
        } else {
            env::current_dir()?.join(lean_raw)
        };
        let mut stage_builder = tempfile::Builder::new();
        stage_builder.prefix("anneal-trusted-");
        // Staged sources and proofs must not be readable by other Unix users.
        // Set permissions at creation, before any inputs reach the directory.
        #[cfg(unix)]
        stage_builder.permissions(fs::Permissions::from_mode(0o700));
        let stage_dir = stage_builder.tempdir()?;
        let stage = stage_dir.path().to_path_buf();

        let mut environment: BTreeMap<String, String> = ambient_env
            .into_iter()
            .filter(|(k, _)| is_retained_environment_key(k))
            .collect();
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
            allow_unpinned_lean: false,
        })
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
        if matches!(
            mode,
            Some("correspondence-preflight" | "correspondence-audit")
        ) {
            8192
        } else if (mode == Some("resolve-imports") && self.allow_unpinned_lean)
            || self.admitted.as_ref().is_some_and(|adm| {
                adm.library_modules
                    .iter()
                    .any(|m| m == "Std" || m.starts_with("Std."))
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
                Failure::new(
                    2,
                    "snapshot",
                    format!("cannot clean {}: {e}", self.stage.display()),
                )
            })?;
        }
        let mut stage_builder = fs::DirBuilder::new();
        // Recreating the stage must preserve its owner-only Unix permissions.
        // A pre-existing replacement directory must cause creation to fail.
        #[cfg(unix)]
        stage_builder.mode(0o700);
        stage_builder.create(&self.stage).map_err(|e| {
            Failure::new(
                2,
                "snapshot",
                format!("cannot recreate {}: {e}", self.stage.display()),
            )
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
        stage_regular_file(&inspector_src, &inspector, "tool-snapshot")?;
        if self.allow_unpinned_lean {
            return self.tool_admission_unpinned(inspector);
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

        // This digest covers only the executable. The pinned build links it
        // from "${LIB}/temp/libleanmain.a" against `libleanshared`, which
        // links "-lInit -lStd -lLean -lleancpp" on Linux and macOS: the
        // compiled `Lean` package, including the elaborator, and C++ objects
        // that include the kernel.
        // https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/stdlib.make.in#L188-L190
        // https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/stdlib.make.in#L157-L163
        // https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/CMakeLists.txt#L859-L872
        let lean_sha = sha256_file(&self.lean, "toolchain")?;
        if !parsed_lock
            .distributions
            .values()
            .any(|s| s.eq_ignore_ascii_case(&lean_sha))
        {
            return Err(Failure::new(
                2,
                "toolchain",
                format!("Lean binary SHA-256 differs from lock: {lean_sha}"),
            ));
        }

        let actual_version = self
            .process("version", &["--version".to_string()])?
            .trim()
            .to_string();
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

        let prefix_raw = self
            .process("prefix", &["--print-prefix".to_string()])?
            .trim()
            .to_string();
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
                || lock
                    .modules
                    .keys()
                    .any(|m| parsed_lock.modules.contains_key(m))
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
        });
        Ok(self.admitted.as_mut().unwrap())
    }

    fn tool_admission_unpinned(
        &mut self,
        inspector: PathBuf,
    ) -> Result<&mut AdmittedToolchain, Failure> {
        let version = self
            .process("version", &["--version".to_string()])?
            .trim()
            .to_string();
        let prefix_raw = self
            .process("prefix", &["--print-prefix".to_string()])?
            .trim()
            .to_string();
        let prefix = fs::canonicalize(&prefix_raw)
            .map_err(|e| Failure::new(2, "toolchain", format!("cannot resolve prefix: {e}")))?;
        let sysroot_package_roots = scan_sysroot_package_roots(&prefix, "toolchain")?;
        let axioms = FOUNDATION_AXIOMS
            .iter()
            .map(|(name, module)| ((*name).to_string(), (*module).to_string()))
            .collect();
        self.admitted = Some(AdmittedToolchain {
            inspector,
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
        });
        Ok(self.admitted.as_mut().unwrap())
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
        let mut cmd = Command::new(&self.lean);
        cmd.args(arguments)
            .current_dir(&self.stage)
            .env_clear()
            .envs(&self.environment);
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
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            // Keep both streams: a frontend error can precede a runtime
            // failure, and dropping either stream hides that distinction.
            let detail = format!("stdout:\n{}\nstderr:\n{}", stdout.trim(), stderr.trim());
            let code = if ordinary_rejection && reports_frontend_rejection(&output) {
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
        String::from_utf8(output.stdout)
            .map_err(|e| Failure::new(2, label, format!("invalid UTF-8 from Lean: {e}")))
    }

    /// Write a `<module>.setup.json` descriptor for `lean --setup`.
    #[doc(hidden)]
    pub fn write_setup_json(
        &self,
        module: &str,
        imports: &[ImportEdge],
    ) -> Result<PathBuf, Failure> {
        let adm = self.admitted()?;
        let import_arts: BTreeMap<&str, [&[String]; 2]> = if adm.unpinned {
            let closure = transitive_import_closure(&adm.graph, imports);
            let mut filtered = BTreeMap::new();
            for dep in &closure {
                let (key, arts) = adm.artifacts.get_key_value(dep.as_str()).ok_or_else(|| {
                    Failure::operational("setup", format!("missing artifact for import {dep}"))
                })?;
                filtered.insert(key.as_str(), arts.to_wire());
            }
            filtered
        } else {
            adm.artifacts
                .iter()
                .map(|(k, v)| (k.as_str(), v.to_wire()))
                .collect()
        };
        let setup_obj = json!({
            "name": module,
            "isModule": false,
            "imports": imports,
            "importArts": import_arts,
            "dynlibs": [],
            "plugins": [],
            "options": {},
        });
        let setup_path = self.stage.join(format!("{module}.setup.json"));
        let bytes =
            serde_json::to_vec(&setup_obj).map_err(|e| Failure::new(2, "setup", e.to_string()))?;
        fs::write(&setup_path, bytes).map_err(|e| Failure::new(2, "setup", e.to_string()))?;
        Ok(setup_path)
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
        let output = self
            .stage
            .join(lib_subdir)
            .join(format!("{}.olean", module.replace('.', "/")));
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| Failure::operational("compile", e.to_string()))?;
        }
        let mut compile_args = vec![
            "-j1".to_string(),
            format!("-M{}", self.default_lean_memory_limit_mb(None)),
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
        self.process_with_exit_policy(
            &format!("compile-{module}"),
            &compile_args,
            target_rejection,
        )?;

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
        let mod_arts = ModuleArtifacts::from_available(&available, "compile", || {
            format!("compiler omitted output for {module}")
        })?;
        let adm = self.admitted_mut()?;
        adm.artifacts.insert(module.to_string(), mod_arts);
        adm.graph.insert(module.to_string(), edge_list);
        Ok(())
    }

    /// Invoke staged `TrustedBoundary.lean` with a serialized JSON request and
    /// validate its structured response envelope (`policy:` -> code `1`,
    /// operational -> code `2`).
    #[doc(hidden)]
    pub fn invoke_inspector(&mut self, mode: &str, req: &Json) -> Result<Json, Failure> {
        let inspector = self.admitted()?.inspector.clone();
        self.counter += 1;
        let stem = self
            .stage
            .join(format!("request-{:03}-{mode}", self.counter));
        let request_path = PathBuf::from(format!("{}.json", stem.display()));
        let result_path = PathBuf::from(format!("{}.result.json", stem.display()));
        let req_bytes = serde_json::to_vec(req)
            .map_err(|e| Failure::new(2, mode, format!("cannot serialize request: {e}")))?;
        fs::write(&request_path, req_bytes)
            .map_err(|e| Failure::new(2, mode, format!("cannot write request: {e}")))?;

        // Keep Pass 1 (`preflight`, `audit`) and `Init`-only target runs capped
        // at `-M2048` over untrusted code, unpinned `resolve-imports` and
        // `Std`-importing target runs at `-M4096`, and Pass 2
        // (`correspondence-preflight`, `correspondence-audit`) at `-M8192` for
        // the 160-module `lean-miri` and `Lean.*` closure.
        let mem_limit = format!("-M{}", self.default_lean_memory_limit_mb(Some(mode)));
        let args = vec![
            "-j1".to_string(),
            mem_limit,
            "--run".to_string(),
            inspector.to_string_lossy().into_owned(),
            request_path.to_string_lossy().into_owned(),
            result_path.to_string_lossy().into_owned(),
        ];
        let output = self
            .launch_lean(&args)
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
            return Err(Failure::new(
                2,
                mode,
                "unexpected inspector protocol response",
            ));
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
            (
                "printf 'INTERNAL PANIC: out of memory' >&2; exit 1",
                true,
                2,
            ),
            (
                "cat diagnostic; printf 'INTERNAL PANIC: out of memory' >&2; exit 1",
                true,
                2,
            ),
            ("printf rejected >&2; exit 1", true, 2),
            ("printf 'unexpected output'; exit 1", true, 2),
            (
                "cat diagnostic; printf 'unexpected output'; exit 1",
                true,
                2,
            ),
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
                fs::write(
                    checker.stage.join("diagnostic"),
                    format!("{prefix}{diagnostic}\n"),
                )
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
        let error = checker
            .process_with_exit_policy("fixture", &[], true)
            .unwrap_err();
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
        assert_eq!(
            output.stdout,
            b"from-stage\0space separated\0\0$HOME;*\0line\nbreak\0"
        );
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
        assert_eq!(
            checker.default_lean_memory_limit_mb(Some("target-audit")),
            2048
        );
        assert_eq!(
            checker.default_lean_memory_limit_mb(Some("correspondence-preflight")),
            8192
        );
        assert_eq!(
            checker.default_lean_memory_limit_mb(Some("correspondence-audit")),
            8192
        );

        checker.set_allow_unpinned_lean(true);
        assert!(checker.allow_unpinned_lean());
        assert_eq!(
            checker.default_lean_memory_limit_mb(Some("resolve-imports")),
            4096
        );
        // Before admitting any `Std` library module (or for `Init`-only runs),
        // compile and `target-audit` stay capped at 2048 MiB.
        assert_eq!(checker.default_lean_memory_limit_mb(None), 2048);
        assert_eq!(
            checker.default_lean_memory_limit_mb(Some("target-audit")),
            2048
        );

        // Once the admitted library closure includes a `Std` module, both
        // compilation and `target-audit` rise to 4096 MiB.
        checker.admitted = Some(AdmittedToolchain {
            inspector: checkout.path().join("TrustedBoundary.lean"),
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
        });
        assert_eq!(checker.default_lean_memory_limit_mb(None), 2048);
        assert_eq!(
            checker.default_lean_memory_limit_mb(Some("target-audit")),
            2048
        );

        checker
            .admitted
            .as_mut()
            .unwrap()
            .library_modules
            .insert("Std.Data.HashMap".to_string());
        assert_eq!(checker.default_lean_memory_limit_mb(None), 4096);
        assert_eq!(
            checker.default_lean_memory_limit_mb(Some("target-audit")),
            4096
        );
        assert_eq!(
            checker.default_lean_memory_limit_mb(Some("correspondence-preflight")),
            8192
        );
        assert_eq!(
            checker.default_lean_memory_limit_mb(Some("correspondence-audit")),
            8192
        );
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
        let adm = checker.tool_admission().unwrap();
        for name in ["A", "B", "C", "D", "Unrelated"] {
            let p = prefix
                .join("lib/lean")
                .join(format!("{name}.olean"))
                .to_string_lossy()
                .into_owned();
            adm.artifacts.insert(
                name.to_string(),
                ModuleArtifacts {
                    olean_parts: vec![p],
                    ir_parts: Vec::new(),
                },
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
        let keys: BTreeSet<String> = setup["importArts"]
            .as_object()
            .unwrap()
            .keys()
            .cloned()
            .collect();
        assert_eq!(
            keys,
            BTreeSet::from([
                "A".to_string(),
                "B".to_string(),
                "C".to_string(),
                "D".to_string(),
            ])
        );
    }
}
