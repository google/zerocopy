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
    collections::{BTreeMap, BTreeSet, HashMap},
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

use crate::ndjson_comparator::{
    ExportPlan, MAX_NDJSON_BYTES, PINNED_INIT_PRIMITIVES, PINNED_SYSTEM_PLATFORM_DECLS,
    STANDARD_PERMITTED_AXIOMS, build_nanoda_config_json,
};
use crate::olean_cache::{
    CacheKind, OleanCache, OleanCacheKeyInput, build_import_bindings, canonical_compile_flags,
    canonical_inspector_flags, is_cacheable_bundled_module, is_cacheable_target_shard_module,
};
use crate::sandbox::{
    ActiveSandbox, DEFAULT_CHILD_TIMEOUT, MountSpec, PathMapper, SandboxMode, SandboxPolicy,
    SandboxRuntime, copy_readonly_file, create_dir_mode, make_tree_writable, set_mode,
    validate_and_promote_olean, validate_and_promote_olean_set,
    validate_and_promote_olean_set_with_digests, validate_inspector_result,
};
use crate::target::{TargetRole, is_bundled_theory_module};
use crate::toolchain::{
    AdmittedToolchain, FOUNDATION_AXIOMS, Failure, FoundationLock, ImportEdge, Json,
    LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256, LibraryLock, ModuleArtifacts, OLEAN_PARTS, PARTS,
    ParallelDagPlan, TOOLCHAIN, compute_sysroot_manifest_sha256,
    compute_unpinned_sysroot_manifest_sha256, default_lean_path, discover_ndjson_comparator_tools,
    is_sha256_hex, regular, run_parallel_dag, scan_sysroot_package_roots, sha256_bytes,
    sha256_file, sha256_file_deref, stage_regular_file, transitive_import_closure,
    verify_installed_module_record, verify_sysroot_foundation_dir,
};

/// Cache key for precompiled `TrustedBoundary.olean` / `SpecPreflight.olean`
/// artifacts held in process memory:
/// `(lean_binary_sha256, canonical_sysroot_prefix, inspector_sha256)`.
type InspectorCacheKey = (String, PathBuf, String);

/// In-memory bytes and verified SHA-256 of Door-1-promoted inspector `.olean`.
#[derive(Debug)]
struct CompiledInspectorArtifacts {
    bytes: Vec<u8>,
    sha256: String,
}

type InspectorCacheSlot = Arc<Mutex<Option<Arc<CompiledInspectorArtifacts>>>>;
type InspectorCacheMap = BTreeMap<InspectorCacheKey, InspectorCacheSlot>;

/// Process-wide cache of compiled `TrustedBoundary` / `SpecPreflight` `.olean`
/// parts keyed by admitted toolchain + inspector source digest. Each
/// [`Checker`] materializes the bytes into its own private `0o700` stage
/// directory so no `/tmp` directories outlive a run and concurrent callers
/// never share writable paths.
fn compiled_inspector_cache() -> &'static Mutex<InspectorCacheMap> {
    static CACHE: OnceLock<Mutex<InspectorCacheMap>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(BTreeMap::new()))
}

/// Cached clean-sysroot `init_primitives_cone.ndjson` bytes and SHA-256 digest
/// keyed by `(canonical_sysroot_prefix, leanexport_sha256, sysroot_key)`.
#[derive(Debug)]
pub(crate) struct CachedInitPrimitives {
    pub bytes: Vec<u8>,
    pub sha256: String,
}

type InitPrimitivesCacheKey = (PathBuf, String, String);
type InitPrimitivesCacheSlot = Arc<Mutex<Option<Arc<CachedInitPrimitives>>>>;
type InitPrimitivesCacheMap = BTreeMap<InitPrimitivesCacheKey, InitPrimitivesCacheSlot>;

fn init_primitives_cache() -> &'static Mutex<InitPrimitivesCacheMap> {
    static CACHE: OnceLock<Mutex<InitPrimitivesCacheMap>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(BTreeMap::new()))
}

type SysrootConstsCacheKey = (PathBuf, String, String, Vec<String>, Vec<String>);
type SysrootConstsMap = Arc<HashMap<String, String>>;
type SysrootConstsCacheSlot = Arc<Mutex<Option<SysrootConstsMap>>>;
type SysrootConstsCacheMap = BTreeMap<SysrootConstsCacheKey, SysrootConstsCacheSlot>;

fn sysroot_consts_cache() -> &'static Mutex<SysrootConstsCacheMap> {
    static CACHE: OnceLock<Mutex<SysrootConstsCacheMap>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(BTreeMap::new()))
}

/// Digest binding a process-cache entry to the admitted sysroot's content:
/// the pinned foundation manifest digest when one was verified, and
/// otherwise the Lean binary digest together with every admitted unpinned
/// module's `.olean*`/`.ir` part digests and source digest. Re-admitting a
/// sysroot whose artifacts changed therefore misses both sysroot caches.
fn sysroot_content_key(adm: &AdmittedToolchain) -> String {
    if let Some(manifest) = &adm.sysroot_manifest_sha256 {
        return manifest.clone();
    }
    let mut acc = format!("lean={}", adm.lean_sha256);
    for (module, rec) in &adm.unpinned_records {
        acc.push_str("\nmodule=");
        acc.push_str(module);
        let mut parts: Vec<&(String, String)> = rec.part_hashes.iter().collect();
        parts.sort();
        for (part, sha) in parts {
            acc.push_str("\npart=");
            acc.push_str(part);
            acc.push('=');
            acc.push_str(sha);
        }
        acc.push_str("\nsource=");
        acc.push_str(rec.source_sha256.as_deref().unwrap_or("-"));
    }
    sha256_bytes(acc.as_bytes())
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
struct InspectorOkTypedResponse<T> {
    ok: bool,
    result: T,
}

/// Upper bound on the summed byte length of one `leanexport` argument vector.
///
/// Linux bounds a single `execve` by `ARG_MAX` (commonly 2 MiB including the
/// environment), so oversized `5a` / `5-pin` root lists fail closed here with
/// a clear diagnostic rather than as an opaque `E2BIG` inside the sandbox.
const MAX_LEANEXPORT_ARG_BYTES: usize = 1 << 20;

/// Copy the comparator-verified `proof_full.ndjson` into a kernel's sandbox
/// input directory read-only and re-hash the copy, so every kernel checks
/// exactly the bytes whose SHA-256 the Rust comparator verified.
fn copy_verified_kernel_input(
    src: &Path,
    dest: &Path,
    expected_sha256: &str,
    phase: &str,
) -> Result<(), Failure> {
    copy_readonly_file(src, dest, phase)?;
    let actual = sha256_file(dest, phase)?;
    if !actual.eq_ignore_ascii_case(expected_sha256) {
        return Err(Failure::operational(
            phase,
            "kernel input proof_full.ndjson differs from the comparator-verified export",
        ));
    }
    Ok(())
}

const LEAN_STDERR_PANIC_MARKERS: &[&str] = &[
    "PANIC at ",
    "INTERNAL PANIC:",
    "PANIC: ",
    "lean_internal_panic",
    "internal exception #",
    "internal exception:",
    "internal exception ",
];

fn detect_lean_stderr_panic(stderr: &str) -> Option<&'static str> {
    stderr
        .lines()
        .find_map(|line| LEAN_STDERR_PANIC_MARKERS.iter().copied().find(|m| line.contains(m)))
}

fn check_lean_stderr_panic(label: &str, output: &Output) -> Result<(), Failure> {
    let stderr = String::from_utf8_lossy(&output.stderr);
    if let Some(marker) = detect_lean_stderr_panic(&stderr) {
        let stdout = String::from_utf8_lossy(&output.stdout);
        return Err(Failure::new(
            2,
            label,
            format!(
                "Lean runtime panic marker `{marker}` on stderr (exit {:?}): stdout:\n{}\nstderr:\n{}",
                output.status.code(),
                stdout.trim(),
                stderr.trim()
            ),
        ));
    }
    Ok(())
}

fn check_lean_output(
    label: &str,
    output: Output,
    ordinary_rejection: bool,
) -> Result<String, Failure> {
    check_lean_stderr_panic(label, &output)?;
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
    is_module: bool,
    mapper: Option<&PathMapper>,
) -> Result<(), Failure> {
    let closure = transitive_import_closure(&adm.graph, imports);
    // Lean 4 `module`-system units read only `.olean`/`.olean.server` (and
    // `.ir` where present) for standard/public imports unless `import all`
    // explicitly opens an upstream private body. Omit `.olean.private` from
    // `importArts` whenever `!import_all` holds across all direct imports so
    // module targets compile with zero upstream `.olean.private` exposure.
    let strip_privates = is_module && imports.iter().all(|imp| !imp.import_all);
    let mut import_arts: BTreeMap<&str, [Vec<String>; 2]> = BTreeMap::new();
    for dep in &closure {
        let (key, arts) = adm.artifacts.get_key_value(dep.as_str()).ok_or_else(|| {
            Failure::operational("setup", format!("missing artifact for import {dep}"))
        })?;
        let [oleans, irs] = arts.to_wire();
        let filtered_oleans: Vec<String>;
        let effective_oleans: &[String] = if strip_privates {
            filtered_oleans =
                oleans.iter().filter(|p| !p.ends_with(".olean.private")).cloned().collect();
            &filtered_oleans
        } else {
            oleans
        };
        let map_list = |list: &[String]| -> Result<Vec<String>, Failure> {
            match mapper {
                Some(m) => list.iter().map(|p| m.map_str(Path::new(p))).collect(),
                None => Ok(list.to_vec()),
            }
        };
        import_arts.insert(key.as_str(), [map_list(effective_oleans)?, map_list(irs)?]);
    }
    let setup_obj = json!({
        "name": module,
        "isModule": is_module,
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
    disable_auto_implicit: bool,
) -> Vec<String> {
    let mut compile_args = vec![
        "-j1".to_string(),
        format!("-M{mem_limit_mb}"),
        "-t0".to_string(),
        "-DElab.async=false".to_string(),
        "-Ddebug.skipKernelTC=false".to_string(),
    ];
    if disable_auto_implicit {
        // Prevent undeclared typos in `TargetRole::Specification` signatures
        // from silently binding universally quantified auto-implicit variables.
        compile_args.push("-DautoImplicit=false".to_string());
        compile_args.push("-DrelaxedAutoImplicit=false".to_string());
    }
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

/// Promote Door 1 outputs from a sandboxed module compilation into
/// `dest_olean.parent()`, recording every promoted `.olean*` file in
/// `olean_ledger` and returning the ordered [`ModuleArtifacts`].
///
/// Non-module compilations keep the strict singleton `.olean` check via
/// [`validate_and_promote_olean`]. Lean 4 `module` compilations promote only
/// `.olean`, `.olean.server`, and `.olean.private` while validating and
/// discarding `.ir` and `.ir.sig` outputs (which downstream pure Lean
/// elaboration does not read and `"target-audit"` excludes).
fn promote_compiled_module_parts(
    out_dir: &Path,
    leaf: &str,
    dest_olean: &Path,
    is_module: bool,
) -> Result<Vec<(String, PathBuf, String)>, Failure> {
    let out_filename = format!("{leaf}.olean");
    if !is_module {
        let sha = validate_and_promote_olean(out_dir, &out_filename, dest_olean)?;
        return Ok(vec![("olean".to_owned(), dest_olean.to_path_buf(), sha)]);
    }
    let allowed_promote = BTreeSet::from([
        out_filename.clone(),
        format!("{leaf}.olean.server"),
        format!("{leaf}.olean.private"),
    ]);
    let allowed_discard = BTreeSet::from([format!("{leaf}.ir"), format!("{leaf}.ir.sig")]);
    let dest_dir = dest_olean
        .parent()
        .ok_or_else(|| Failure::operational("door1", "missing destination parent directory"))?;
    let promoted = validate_and_promote_olean_set_with_digests(
        out_dir,
        &allowed_promote,
        &allowed_discard,
        &out_filename,
        dest_dir,
    )?;
    let mut parts_with_sha = Vec::new();
    for suffix in OLEAN_PARTS {
        let candidate = dest_dir.join(format!("{leaf}.{suffix}"));
        if let Some(sha) = promoted.get(&candidate) {
            parts_with_sha.push(((*suffix).to_owned(), candidate, sha.clone()));
        }
    }
    Ok(parts_with_sha)
}

fn promote_compiled_module_outputs(
    out_dir: &Path,
    leaf: &str,
    dest_olean: &Path,
    is_module: bool,
    olean_ledger: &mut BTreeMap<PathBuf, String>,
) -> Result<ModuleArtifacts, Failure> {
    let parts_with_sha = promote_compiled_module_parts(out_dir, leaf, dest_olean, is_module)?;
    let mut olean_parts = Vec::with_capacity(parts_with_sha.len());
    for (_, path, sha) in parts_with_sha {
        olean_parts.push(path.to_string_lossy().into_owned());
        olean_ledger.insert(path, sha);
    }
    Ok(ModuleArtifacts { olean_parts, ir_parts: Vec::new() })
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

enum ModuleCachePrep {
    Cached(Vec<(String, PathBuf, String)>),
    CompileNeeded(Option<OleanCacheKeyInput>),
}

enum PreparedModuleCompile<W> {
    Cached(Vec<(String, PathBuf, String)>),
    Compile {
        work: W,
        cache_key: Option<OleanCacheKeyInput>,
    },
}

enum ExecutedModuleCompile<D> {
    Cached(Vec<(String, PathBuf, String)>),
    Compiled {
        done: D,
        cache_key: Option<OleanCacheKeyInput>,
    },
}

/// Skip Lean whitespace and comments (`--` line comments and nested `/- ... -/`)
/// to determine whether a source file begins with the Lean 4 `module` header.
#[doc(hidden)]
pub fn source_starts_with_module_keyword(bytes: &[u8]) -> bool {
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if bytes[i..].starts_with(b"--") {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if bytes[i..].starts_with(b"/-") {
            i += 2;
            let mut depth = 1usize;
            while i < bytes.len() && depth > 0 {
                if bytes[i..].starts_with(b"/-") {
                    depth += 1;
                    i += 2;
                } else if bytes[i..].starts_with(b"-/") {
                    depth -= 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            continue;
        }
        break;
    }
    let Some(rest) = bytes[i..].strip_prefix(b"module") else {
        return false;
    };
    rest.first().is_none_or(|b| b.is_ascii_whitespace())
        || rest.starts_with(b"--")
        || rest.starts_with(b"/-")
}

fn olean_part_suffix(path: &str) -> Result<&'static str, Failure> {
    if path.ends_with(".olean.server") {
        Ok("olean.server")
    } else if path.ends_with(".olean.private") {
        Ok("olean.private")
    } else if path.ends_with(".olean") {
        Ok("olean")
    } else {
        Err(Failure::operational(
            "olean-cache",
            format!("unexpected compiled artifact extension in {path}"),
        ))
    }
}

fn is_cacheable_module(module: &str, allow_target_shard_cache: bool) -> bool {
    is_cacheable_bundled_module(module)
        || (allow_target_shard_cache && is_cacheable_target_shard_module(module))
}

#[allow(clippy::too_many_arguments)]
fn prepare_module_cache(
    olean_cache: &mut OleanCache,
    adm: &AdmittedToolchain,
    module: &str,
    edge_list: &[ImportEdge],
    mod_is_module: bool,
    src_path: &Path,
    lib_dir: &Path,
    warn_as_err: bool,
    disable_auto_implicit: bool,
    allow_target_shard_cache: bool,
    cache_ctx: Option<&(String, String)>,
    path_sha_cache: &mut BTreeMap<String, String>,
    transitive_memo: &mut BTreeMap<String, String>,
) -> Result<ModuleCachePrep, Failure> {
    let Some((lean_sha, sysroot_sha)) = cache_ctx else {
        return Ok(ModuleCachePrep::CompileNeeded(None));
    };
    if disable_auto_implicit || !is_cacheable_module(module, allow_target_shard_cache) {
        return Ok(ModuleCachePrep::CompileNeeded(None));
    }
    let src_bytes =
        fs::read(src_path).map_err(|e| Failure::operational("olean-cache", e.to_string()))?;
    let key_input = OleanCacheKeyInput {
        kind: CacheKind::Module,
        module: module.to_owned(),
        lean_sha256: lean_sha.clone(),
        sysroot_manifest_sha256: sysroot_sha.clone(),
        source_sha256: sha256_bytes(&src_bytes),
        is_module: mod_is_module,
        flags: canonical_compile_flags(warn_as_err),
        imports: build_import_bindings(
            edge_list,
            &adm.artifacts,
            &adm.graph,
            path_sha_cache,
            transitive_memo,
        )?,
    };
    if let Some(hit) =
        olean_cache.lookup_and_materialize(&key_input, lib_dir, &module.replace('.', "/"))?
    {
        return Ok(ModuleCachePrep::Cached(hit.materialized_parts));
    }
    Ok(ModuleCachePrep::CompileNeeded(Some(key_input)))
}

#[allow(clippy::too_many_arguments)]
fn finish_module_artifacts(
    adm: &mut AdmittedToolchain,
    olean_cache: &OleanCache,
    olean_ledger: &mut BTreeMap<PathBuf, String>,
    path_sha_cache: &mut BTreeMap<String, String>,
    module: &str,
    edge_list: &[ImportEdge],
    parts_with_sha: &[(String, PathBuf, String)],
    record_ledger: bool,
    cache_key: Option<OleanCacheKeyInput>,
) -> Result<(), Failure> {
    let mut available: BTreeMap<&str, String> = BTreeMap::new();
    for (suffix, dest_path, sha) in parts_with_sha {
        let dest_str = dest_path.to_string_lossy().into_owned();
        path_sha_cache.insert(dest_str.clone(), sha.clone());
        if record_ledger {
            olean_ledger.insert(dest_path.clone(), sha.clone());
        }
        available.insert(suffix.as_str(), dest_str);
    }
    let mod_arts = ModuleArtifacts::from_available(&available, "compile", || {
        format!("compiler omitted primary .olean for {module}")
    })?;
    adm.artifacts.insert(module.to_owned(), mod_arts);
    adm.graph.insert(module.to_owned(), edge_list.to_vec());
    if let Some(ref key_input) = cache_key {
        let part_refs: Vec<(&str, &Path, &str)> = parts_with_sha
            .iter()
            .map(|(suffix, path, sha)| (suffix.as_str(), path.as_path(), sha.as_str()))
            .collect();
        olean_cache.store_compiled(key_input, &part_refs)?;
    }
    Ok(())
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
/// executing any child process so toolchain admission under `ExecSeal` (in
/// both pinned and unpinned modes) never runs an unsandboxed launcher on the
/// host.
fn resolve_static_toolchain(lean: &Path) -> Result<(PathBuf, PathBuf), Failure> {
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

/// Resolve `(prefix, canon_exec_lean)` statically on disk for unpinned
/// `ExecSeal` admission, canonicalizing a Bazel-style runfiles wrapper
/// sysroot to its target sysroot when safe.
///
/// When `lean` resolves through a logical `<prefix>/bin/lean` symlink
/// into a distinct canonical `<canon_prefix>/bin/lean` sysroot whose
/// `<prefix>/lib` is purely a symlink forest (or direct symlink) staying
/// strictly within `<canon_prefix>/lib`, return `(canon_prefix, exec_lean)`.
///
/// Security invariant: promoting `prefix` to `canon_prefix` preserves
/// `ExecSeal` containment and sysroot hashing (`pre_probe_sha` still
/// hashes the identical `exec_lean` binary, every leaf under
/// `<prefix>/lib` is verified to point inside `<canon_prefix>/lib` with
/// zero regular or special files, and `SandboxRuntime::probe` plus
/// `tool_admission_unpinned` then validate, probe, and hash
/// `canon_prefix` end-to-end). Zero-symlink directories and internal-only
/// overlays fall back to `(prefix, exec_lean)` so `SandboxRuntime::probe`
/// preserves standalone layouts while failing closed on broken, looping,
/// escaping, or mixed invalid trees.
fn resolve_unpinned_static_toolchain(lean: &Path) -> Result<(PathBuf, PathBuf), Failure> {
    let (prefix, exec_lean) = resolve_static_toolchain(lean)?;
    let Some(exec_prefix) = exec_lean.parent().and_then(Path::parent) else {
        return Ok((prefix, exec_lean));
    };
    if prefix == exec_prefix {
        return Ok((prefix, exec_lean));
    }
    let Some((canon_prefix, _)) = try_resolve_sysroot_candidate(&exec_lean)? else {
        return Ok((prefix, exec_lean));
    };
    let logical_lib = prefix.join("lib");
    let canon_lib = canon_prefix.join("lib");
    if logical_lib_symlinks_stay_within(&logical_lib, &canon_lib) {
        Ok((canon_prefix, exec_lean))
    } else {
        Ok((prefix, exec_lean))
    }
}

/// Return `true` only when `logical_lib` resolves to `canon_lib` itself
/// or is a non-empty symlink forest whose every leaf entry is a valid
/// symlink resolving strictly inside `canon_lib`'s canonical path.
fn logical_lib_symlinks_stay_within(logical_lib: &Path, canon_lib: &Path) -> bool {
    let Ok(canon_lib_resolved) = fs::canonicalize(canon_lib) else {
        return false;
    };
    let Ok(root_meta) = fs::symlink_metadata(logical_lib) else {
        return false;
    };
    if root_meta.file_type().is_symlink() {
        return fs::canonicalize(logical_lib).is_ok_and(|target| target == canon_lib_resolved);
    }
    if !root_meta.file_type().is_dir() {
        return false;
    }
    let mut stack = vec![logical_lib.to_path_buf()];
    let mut saw_symlink = false;
    while let Some(dir) = stack.pop() {
        let Ok(entries) = fs::read_dir(&dir) else {
            return false;
        };
        for entry in entries {
            let Ok(entry) = entry else {
                return false;
            };
            let path = entry.path();
            let Ok(ft) = entry.file_type() else {
                return false;
            };
            if ft.is_symlink() {
                saw_symlink = true;
                let Ok(target) = fs::canonicalize(&path) else {
                    return false;
                };
                if target == canon_lib_resolved || !target.starts_with(&canon_lib_resolved) {
                    return false;
                }
            } else if ft.is_dir() {
                stack.push(path);
            } else {
                // Mixed regular or special files mean `logical_lib` is
                // not a pure symlink forest mirroring `canon_lib`.
                return false;
            }
        }
    }
    saw_symlink
}

/// Require a canonical pinned `x86_64` Linux Lean executable to reside under
/// `<prefix>/bin/<name>` so its ELF `$ORIGIN/..` `DT_RUNPATH` resolves to a
/// known sysroot prefix rather than an arbitrary sibling directory.
fn require_pinned_lean_bin_prefix(canon_lean: &Path) -> Result<&Path, Failure> {
    let Some(bin_dir) = canon_lean.parent() else {
        return Err(Failure::new(
            2,
            "toolchain",
            format!(
                "pinned x86_64 Linux Lean binary {} must reside under <prefix>/bin/",
                canon_lean.display()
            ),
        ));
    };
    if bin_dir.file_name() != Some(OsStr::new("bin")) {
        return Err(Failure::new(
            2,
            "toolchain",
            format!(
                "pinned x86_64 Linux Lean binary {} must reside under <prefix>/bin/",
                canon_lean.display()
            ),
        ));
    }
    bin_dir.parent().ok_or_else(|| {
        Failure::new(
            2,
            "toolchain",
            format!(
                "pinned x86_64 Linux Lean binary {} must reside under <prefix>/bin/",
                canon_lean.display()
            ),
        )
    })
}

/// Verify Lean runtime shared libraries for `prefix` and, when `exec_lean`
/// canonicalizes outside `prefix`, also for `exec_lean`'s `$ORIGIN/..`
/// directory. Fails closed if a pinned `x86_64` Linux executable is not under
/// `<dir>/bin/<name>`.
fn verify_pinned_exec_and_prefix_runtime_libs(
    prefix: &Path,
    exec_lean: &Path,
    lean_sha: &str,
) -> Result<bool, Failure> {
    let prefix_verified =
        crate::toolchain::verify_sysroot_runtime_libs_for_sha(prefix, lean_sha)?;
    if !prefix_verified {
        return Ok(false);
    }
    let exec_prefix = require_pinned_lean_bin_prefix(exec_lean)?;
    if exec_prefix != prefix {
        let exec_verified =
            crate::toolchain::verify_sysroot_runtime_libs_for_sha(exec_prefix, lean_sha)?;
        if !exec_verified {
            return Err(Failure::new(
                2,
                "toolchain",
                "runtime shared-library verification state differs across sysroot paths",
            ));
        }
    }
    Ok(true)
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
    paranoid_quorum: bool,
    spec_preflight_mode_via_spec_preflight: bool,
    lean_memory_mb: Option<u32>,
    #[cfg(test)]
    expected_sysroot_manifest_sha256_for_test: Option<String>,
    sandbox_mode: SandboxMode,
    sandbox_runtime: Option<SandboxRuntime>,
    probed_backend: Option<ActiveSandbox>,
    child_timeout: Duration,
    olean_cache: OleanCache,
    prebuilt_olean_dir: Option<PathBuf>,
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
        let mut checker = Self::new_with_env(root, lean, environment)?;
        let home = checker.environment.get("HOME").cloned();
        let xdg = env::var_os("XDG_CACHE_HOME");
        checker.olean_cache =
            OleanCache::with_env_vars(home.as_deref().map(OsStr::new), xdg.as_deref());
        Ok(checker)
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
        let olean_cache =
            OleanCache::with_env_vars(environment.get("HOME").map(OsStr::new), None);

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
            paranoid_quorum: false,
            spec_preflight_mode_via_spec_preflight: false,
            lean_memory_mb: None,
            #[cfg(test)]
            expected_sysroot_manifest_sha256_for_test: None,
            sandbox_mode: SandboxMode::PreferBwrapOrLandlock,
            sandbox_runtime: None,
            probed_backend: None,
            child_timeout: DEFAULT_CHILD_TIMEOUT,
            olean_cache,
            prebuilt_olean_dir: None,
            olean_ledger: BTreeMap::new(),
            compiled_roles: BTreeMap::new(),
        })
    }

    #[cfg(test)]
    pub(crate) fn set_expected_sysroot_manifest_sha256_for_test(&mut self, sha: impl Into<String>) {
        self.expected_sysroot_manifest_sha256_for_test = Some(sha.into());
    }

    /// Configure whether Action `5c` additionally executes `con-leche` and
    /// `lean4lean --import` directly inside `ExecSeal` alongside default
    /// `nanoda_bin` + `con-ron` for a four-independent-kernel quorum.
    pub fn set_paranoid_quorum(&mut self, enabled: bool) {
        self.paranoid_quorum = enabled;
    }

    /// Return whether `--paranoid-quorum` is enabled.
    pub fn paranoid_quorum(&self) -> bool {
        self.paranoid_quorum
    }

    /// Test hook: serve `"spec-preflight"` from `SpecPreflight.lean` even
    /// without the NDJSON comparator tools, so tests on the pinned toolchain
    /// exercise the comparator route's specification preflight.
    #[doc(hidden)]
    pub fn set_spec_preflight_mode_via_spec_preflight(&mut self, enabled: bool) {
        self.spec_preflight_mode_via_spec_preflight = enabled;
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

    /// Enable or disable prebuilt and user-local `.olean` cache lookup and population.
    pub fn set_use_olean_cache(&mut self, enabled: bool) {
        self.olean_cache.set_enabled(enabled);
    }

    /// Require every cacheable `Trusted.*`/`Anneal.*` module and `TrustedBoundary`
    /// to resolve from prebuilt or local `.olean` caches rather than recompiling.
    pub fn set_no_rebuild_bundled(&mut self, no_rebuild: bool) {
        self.olean_cache.set_no_rebuild_bundled(no_rebuild);
    }

    /// Override the read-only `share/anneal/prebuilt` directory checked before the
    /// user-local disk `.olean` cache.
    pub fn set_prebuilt_olean_dir(&mut self, dir: Option<PathBuf>) {
        self.prebuilt_olean_dir = dir;
    }

    #[cfg(test)]
    pub(crate) fn set_olean_disk_cache_dir_for_test(&mut self, dir: Option<PathBuf>) {
        self.olean_cache.set_disk_dir(dir);
    }

    fn effective_prebuilt_dir(&self, prefix: &Path) -> Option<PathBuf> {
        self.prebuilt_olean_dir.clone().or_else(|| {
            prefix
                .parent()
                .map(|root| root.join("share/anneal/prebuilt"))
                .filter(|dir| dir.join("manifest.json").is_file())
        })
    }

    fn ensure_sysroot_manifest_sha256(&mut self) -> Result<String, Failure> {
        let (existing, prefix, unpinned) = {
            let adm = self.admitted()?;
            (adm.sysroot_manifest_sha256.clone(), adm.prefix.clone(), adm.unpinned)
        };
        if let Some(sha) = existing {
            return Ok(sha);
        }
        let lib_dir = prefix.join("lib/lean");
        let sha = if unpinned {
            compute_unpinned_sysroot_manifest_sha256(&lib_dir, "olean-cache")?
        } else {
            compute_sysroot_manifest_sha256(&lib_dir, "olean-cache")?
        };
        self.admitted_mut()?.sysroot_manifest_sha256 = Some(sha.clone());
        Ok(sha)
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
        let stage_builder = {
            #[cfg(unix)]
            let mut builder = fs::DirBuilder::new();
            #[cfg(not(unix))]
            let builder = fs::DirBuilder::new();
            // Recreating the stage must keep its owner-only Unix permissions.
            // Pre-existing replacement directories must fail creation.
            #[cfg(unix)]
            builder.mode(0o700);
            builder
        };
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
    /// sysroot `{Init,Std,Lean}*` `.olean`/`.ir` manifest against their locked
    /// SHA-256 digests.
    ///
    /// Authenticating the sysroot `{Init,Std,Lean}*` `.olean`, `.olean.server`,
    /// `.olean.private`, `.ir`, and `.ir.sig` manifest here covers the compiled
    /// `.olean*` and IR artifacts loaded by the standalone inspector
    /// (`TrustedBoundary.lean`) before any inspector mode executes. For
    /// `x86_64-unknown-linux-gnu`, pinned admission also authenticates Lean's
    /// runtime shared libraries and linker scripts under `<prefix>/lib` and
    /// `<prefix>/lib/lean` against `LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS`
    /// (both before probing and after `--print-prefix`). Lean shared
    /// libraries on uncatalogued triples remain unhashed and identified only
    /// by `lean --version`, so their integrity rests on the uncompromised
    /// execution environment that `THREAT_MODEL.md` assumes. Library
    /// source/`.ir` digests are checked later, when target imports reach them.
    #[doc(hidden)]
    pub fn tool_admission(&mut self) -> Result<&mut AdmittedToolchain, Failure> {
        let inspector_src = self.root.join("trusted/audit/TrustedBoundary.lean");
        let spec_preflight_src = self.root.join("trusted/audit/SpecPreflight.lean");
        let control_dir = self.stage.join("control");
        if control_dir.exists() {
            make_tree_writable(&control_dir);
        }
        create_dir_mode(&control_dir, 0o700)?;
        let inspector = control_dir.join("TrustedBoundary.lean");
        let inspector_sha256 = stage_regular_file(&inspector_src, &inspector, "tool-snapshot")?;
        set_mode(&inspector, 0o444)?;
        let (spec_preflight, spec_preflight_sha256) =
            match fs::symlink_metadata(&spec_preflight_src) {
                Ok(_) => {
                    let sp_dest = control_dir.join("SpecPreflight.lean");
                    let sp_sha =
                        stage_regular_file(&spec_preflight_src, &sp_dest, "tool-snapshot")?;
                    set_mode(&sp_dest, 0o444)?;
                    (Some(sp_dest), Some(sp_sha))
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => (None, None),
                Err(e) => {
                    return Err(Failure::operational(
                        "tool-snapshot",
                        format!("cannot inspect {}: {e}", spec_preflight_src.display()),
                    ));
                }
            };
        set_mode(&control_dir, 0o500)?;
        if self.allow_unpinned_lean {
            return self.tool_admission_unpinned(
                inspector,
                inspector_sha256,
                spec_preflight,
                spec_preflight_sha256,
            );
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
        // `--print-prefix`. When `ExecSeal` containment is active, resolve the
        // sysroot statically and run both `--version` and `--print-prefix`
        // inside the sandbox (matching unpinned mode) so no Lean binary or
        // unhashed shared library executes directly on the host.
        let lean_sha = sha256_file_deref(&self.lean, "toolchain")?;
        if !parsed_lock.distributions.values().any(|s| s.eq_ignore_ascii_case(&lean_sha)) {
            return Err(Failure::new(
                2,
                "toolchain",
                format!("Lean binary SHA-256 differs from lock: {lean_sha}"),
            ));
        }

        let foundation_modules: BTreeSet<String> = parsed_lock.modules.keys().cloned().collect();
        #[cfg(test)]
        let expected_sysroot_sha: String = self
            .expected_sysroot_manifest_sha256_for_test
            .clone()
            .unwrap_or_else(|| LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256.to_owned());
        #[cfg(not(test))]
        let expected_sysroot_sha: String = LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256.to_owned();

        let (
            actual_version,
            expected_lean_sha,
            prefix,
            exec_lean,
            artifacts,
            runtime_libs_verified,
        ) = if self.sandbox_mode == SandboxMode::Unsandboxed {
            let canon_self_lean = fs::canonicalize(&self.lean).map_err(|e| {
                Failure::new(
                    2,
                    "toolchain",
                    format!("cannot canonicalize {}: {e}", self.lean.display()),
                )
            })?;
            // Verify the executable's `$ORIGIN/..` runtime DSOs before
            // running `--version` or `--print-prefix` even in unsandboxed
            // pinned mode (e.g., `anneal-audit` Pass 1 or
            // `--allow-unsandboxed-elaboration`), failing closed if the pinned
            // `x86_64` Linux binary does not reside under `<prefix>/bin/`.
            let pre_exec_libs_verified = if lean_sha
                .eq_ignore_ascii_case(crate::toolchain::LOCKED_LEAN_X86_64_LINUX_SHA256)
            {
                let self_prefix = require_pinned_lean_bin_prefix(&canon_self_lean)?;
                crate::toolchain::verify_sysroot_runtime_libs_for_sha(self_prefix, &lean_sha)?
            } else {
                false
            };
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
                        "Lean binary SHA-256 mismatch for {actual_version}: expected \
                         {expected_lean_sha}, got {lean_sha}"
                    ),
                ));
            }

            let prefix_raw =
                self.process("prefix", &["--print-prefix".to_string()])?.trim().to_string();
            let prefix = fs::canonicalize(&prefix_raw).map_err(|e| {
                Failure::new(2, "toolchain", format!("cannot resolve prefix: {e}"))
            })?;
            let prefix_lean = prefix.join("bin/lean");
            let exec_lean = if prefix_lean.exists() {
                let resolved = fs::canonicalize(&prefix_lean).map_err(|e| {
                    Failure::new(
                        2,
                        "toolchain",
                        format!("cannot canonicalize {}: {e}", prefix_lean.display()),
                    )
                })?;
                // Re-authenticate `exec_lean` against `foundation-lock.json`
                // whenever `prefix/bin/lean` resolves to a different binary
                // than `self.lean`.
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
                let mod_arts =
                    verify_installed_module_record(&prefix, module, record, "foundation")?;
                artifacts.insert(module.clone(), mod_arts);
            }
            verify_sysroot_foundation_dir(
                &prefix.join("lib/lean"),
                &foundation_modules,
                &expected_sysroot_sha,
            )
            .map_err(|err| Failure::new(err.code, "toolchain", err.message))?;
            let runtime_libs_verified = verify_pinned_exec_and_prefix_runtime_libs(
                &prefix,
                &exec_lean,
                expected_lean_sha,
            )?;
            if pre_exec_libs_verified != runtime_libs_verified {
                return Err(Failure::new(
                    2,
                    "toolchain",
                    "runtime shared-library verification state differs across sysroot paths",
                ));
            }
            (
                actual_version,
                expected_lean_sha.clone(),
                prefix,
                exec_lean,
                artifacts,
                runtime_libs_verified,
            )
        } else {
                let (prefix, exec_lean) = resolve_static_toolchain(&self.lean)?;
                let exec_sha = sha256_file_deref(&exec_lean, "toolchain")?;
                if !parsed_lock.distributions.values().any(|s| s.eq_ignore_ascii_case(&exec_sha)) {
                    return Err(Failure::new(
                        2,
                        "toolchain",
                        format!(
                            "resolved Lean binary {} SHA-256 differs from lock: {exec_sha}",
                            exec_lean.display()
                        ),
                    ));
                }
                // Authenticate foundation modules and the full `Init`/`Std`/
                // `Lean` sysroot manifest BEFORE launching even the sandboxed
                // probe or `--version`/`--print-prefix` queries.
                let mut artifacts = BTreeMap::new();
                for (module, record) in &parsed_lock.modules {
                    let mod_arts =
                        verify_installed_module_record(&prefix, module, record, "foundation")?;
                    artifacts.insert(module.clone(), mod_arts);
                }
                verify_sysroot_foundation_dir(
                    &prefix.join("lib/lean"),
                    &foundation_modules,
                    &expected_sysroot_sha,
                )
                .map_err(|err| Failure::new(err.code, "toolchain", err.message))?;
                let pre_libs_verified = verify_pinned_exec_and_prefix_runtime_libs(
                    &prefix,
                    &exec_lean,
                    &exec_sha,
                )?;
                let runtime =
                    SandboxRuntime::probe(self.sandbox_mode, &exec_lean, &prefix, &self.stage)?;
                self.probed_backend = Some(runtime.backend);
                let actual_version = self
                    .run_sandboxed_lean_query(&runtime, "version", &["--version".to_string()])?
                    .trim()
                    .to_string();
                let Some(expected_lean_sha) = parsed_lock.distributions.get(&actual_version) else {
                    return Err(Failure::new(
                        2,
                        "toolchain",
                        format!("Lean version/commit differs from lock: {actual_version}"),
                    ));
                };
                if !expected_lean_sha.eq_ignore_ascii_case(&lean_sha)
                    || !expected_lean_sha.eq_ignore_ascii_case(&exec_sha)
                {
                    return Err(Failure::new(
                        2,
                        "toolchain",
                        format!(
                            "Lean binary SHA-256 mismatch for {actual_version}: expected \
                             {expected_lean_sha}, got launcher={lean_sha}, resolved={exec_sha}"
                        ),
                    ));
                }
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
                             pinned sysroot {}",
                            prefix.display()
                        ),
                    ));
                }
                let post_probe_sha = sha256_file_deref(&exec_lean, "toolchain")?;
                if !expected_lean_sha.eq_ignore_ascii_case(&post_probe_sha) {
                    return Err(Failure::new(
                        2,
                        "toolchain",
                        format!(
                            "resolved Lean binary {} changed during pinned admission",
                            exec_lean.display()
                        ),
                    ));
                }
                let post_libs_verified = verify_pinned_exec_and_prefix_runtime_libs(
                    &prefix,
                    &exec_lean,
                    expected_lean_sha,
                )?;
                if pre_libs_verified != post_libs_verified {
                    return Err(Failure::new(
                        2,
                        "toolchain",
                        "runtime shared-library verification state changed during pinned admission",
                    ));
                }
                self.sandbox_runtime = Some(runtime);
                (
                    actual_version,
                    expected_lean_sha.clone(),
                    prefix,
                    exec_lean,
                    artifacts,
                    post_libs_verified,
                )
            };

        let library_lock_path = self.root.join("trusted/audit/library-lock.json");
        let library_lock = if fs::symlink_metadata(&library_lock_path).is_ok() {
            regular(&library_lock_path, "library-lock")?;
            let raw = fs::read_to_string(&library_lock_path)
                .map_err(|e| Failure::operational("library-lock", e.to_string()))?;
            let lock = LibraryLock::parse(&raw)?;
            lock.verify_prefix(&prefix, "library-lock")?;
            Some(lock)
        } else {
            None
        };

        self.admitted = Some(AdmittedToolchain {
            inspector,
            inspector_sha256,
            spec_preflight,
            spec_preflight_sha256,
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
            sysroot_manifest_sha256: Some(expected_sysroot_sha.to_owned()),
            inspector_olean: None,
            runtime_libs_verified,
            spec_preflight_olean: None,
            ndjson_tools: None,
        });
        Ok(self.admitted.as_mut().unwrap())
    }

    fn tool_admission_unpinned(
        &mut self,
        inspector: PathBuf,
        inspector_sha256: String,
        spec_preflight: Option<PathBuf>,
        spec_preflight_sha256: Option<String>,
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
            // Resolve logical runfiles symlink forests into `canon_prefix`
            // before `pre_probe_sha` and `SandboxRuntime::probe` so
            // `exec_lean` hashing, sysroot root/module hashing, and
            // `ExecSeal` mounts share one consistent `canon_prefix`.
            // Pinned `tool_admission` keeps `resolve_static_toolchain` so
            // locked sysroot paths reject symlinks directly.
            let (prefix, exec_lean) = resolve_unpinned_static_toolchain(&self.lean)?;
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
        let ndjson_tools = discover_ndjson_comparator_tools(&prefix)?;
        self.admitted = Some(AdmittedToolchain {
            inspector,
            inspector_sha256,
            spec_preflight,
            spec_preflight_sha256,
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
            sysroot_manifest_sha256: None,
            inspector_olean: None,
            runtime_libs_verified: false,
            spec_preflight_olean: None,
            ndjson_tools,
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
        let adm_runtime_libs_verified = adm.runtime_libs_verified;
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
            let ready_libs_verified = verify_pinned_exec_and_prefix_runtime_libs(
                &prefix,
                &exec_lean,
                expected_sha,
            )?;
            if ready_libs_verified != adm_runtime_libs_verified {
                return Err(Failure::new(
                    2,
                    "toolchain",
                    "runtime shared-library verification state changed before sandbox readiness",
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
        self.write_setup_json_at(&setup_path, module, imports, false, None)?;
        Ok(setup_path)
    }

    fn write_setup_json_at(
        &self,
        setup_path: &Path,
        module: &str,
        imports: &[ImportEdge],
        is_module: bool,
        mapper: Option<&PathMapper>,
    ) -> Result<(), Failure> {
        let adm = self.admitted()?;
        write_setup_json_to_path(setup_path, adm, module, imports, is_module, mapper)
    }

    /// Create fresh per-invocation `runs/<counter>/{in,out,tmp}` directories.
    fn prepare_run_dirs(&self) -> Result<(PathBuf, PathBuf, PathBuf, PathBuf), Failure> {
        prepare_run_dirs_at(&self.stage, self.next_counter())
    }

    /// Compile a single staged `.lean` source file into
    /// `self.stage/<lib_subdir>` using `--setup` and strict synchronous kernel
    /// flags, and register its compiled [`ModuleArtifacts`].
    #[doc(hidden)]
    #[allow(clippy::too_many_arguments)]
    pub fn compile_lean_module(
        &mut self,
        module: &str,
        src_path: &Path,
        edge_list: Vec<ImportEdge>,
        is_module: bool,
        lib_subdir: &str,
        warn_as_err: bool,
        target_rejection: bool,
    ) -> Result<(), Failure> {
        if !target_rejection && self.sandbox_mode == SandboxMode::Unsandboxed {
            return self.compile_lean_module_direct(
                module,
                src_path,
                edge_list,
                is_module,
                lib_subdir,
                warn_as_err,
            );
        }

        let runtime = self.ensure_sandbox_ready()?;
        let (_run_dir, in_dir, out_dir, tmp_dir) = self.prepare_run_dirs()?;
        let lib_dir = self.stage.join(lib_subdir);
        create_dir_mode(&lib_dir, 0o700)?;

        let leaf = module.rsplit('.').next().unwrap_or(module);
        let leaf_name = format!("{leaf}.lean");
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
        self.write_setup_json_at(&setup_host, module, &edge_list, is_module, Some(&mapper))?;
        set_mode(&in_dir, 0o500)?;

        let out_filename = format!("{leaf}.olean");
        let out_host = out_dir.join(&out_filename);
        let mapped_setup = PathBuf::from(mapper.map_str(&setup_host)?);
        let mapped_out = PathBuf::from(mapper.map_str(&out_host)?);
        let mapped_src = PathBuf::from(mapper.map_str(&in_src)?);
        let disable_auto_implicit =
            self.compiled_roles.get(module) == Some(&TargetRole::Specification);
        let compile_args = build_lean_compile_args(
            &mapped_setup,
            &mapped_out,
            &mapped_src,
            self.effective_lean_memory_limit_mb(None),
            warn_as_err,
            target_rejection,
            disable_auto_implicit,
        );

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
        check_lean_stderr_panic(&label, &output)?;
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
        let mod_arts = promote_compiled_module_outputs(
            &out_dir,
            leaf,
            &dest_olean,
            is_module,
            &mut self.olean_ledger,
        )?;
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
        is_module: bool,
        lib_subdir: &str,
        warn_as_err: bool,
    ) -> Result<(), Failure> {
        let setup_path = self.stage.join(format!("{module}.setup.json"));
        self.write_setup_json_at(&setup_path, module, &edge_list, is_module, None)?;
        let output =
            self.stage.join(lib_subdir).join(format!("{}.olean", module.replace('.', "/")));
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| Failure::operational("compile", e.to_string()))?;
        }
        let disable_auto_implicit =
            self.compiled_roles.get(module) == Some(&TargetRole::Specification);
        let compile_args = build_lean_compile_args(
            &setup_path,
            &output,
            src_path,
            self.effective_lean_memory_limit_mb(None),
            warn_as_err,
            false,
            disable_auto_implicit,
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
    /// `ExecSeal` + Door 1 artifact promotion (when active), and serialized
    /// registration into `self.admitted` and `self.olean_ledger`.
    #[doc(hidden)]
    #[allow(clippy::too_many_arguments)]
    pub fn compile_lean_modules_parallel(
        &mut self,
        order: &[String],
        sources: &BTreeMap<String, PathBuf>,
        imports: &BTreeMap<String, Vec<ImportEdge>>,
        is_module: &BTreeMap<String, bool>,
        lib_subdir: &str,
        warn_as_err: bool,
        target_rejection: bool,
        max_workers: usize,
    ) -> Result<(), Failure> {
        self.compile_lean_modules_parallel_with_progress(
            order,
            sources,
            imports,
            is_module,
            lib_subdir,
            warn_as_err,
            target_rejection,
            max_workers,
            |_, _, _| {},
        )
    }

    #[doc(hidden)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn compile_lean_modules_parallel_with_progress(
        &mut self,
        order: &[String],
        sources: &BTreeMap<String, PathBuf>,
        imports: &BTreeMap<String, Vec<ImportEdge>>,
        is_module: &BTreeMap<String, bool>,
        lib_subdir: &str,
        warn_as_err: bool,
        target_rejection: bool,
        max_workers: usize,
        mut on_module_done: impl FnMut(usize, usize, usize) + Send,
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

        let allow_target_cache_context =
            target_rejection && self.sandbox_mode != SandboxMode::Unsandboxed;
        let has_cacheable = order
            .iter()
            .any(|m| is_cacheable_module(m, allow_target_cache_context));
        let cache_ctx = if self.olean_cache.is_enabled() && has_cacheable {
            let sysroot_sha = self.ensure_sysroot_manifest_sha256()?;
            let (lean_sha, prefix) = {
                let adm = self.admitted()?;
                (adm.lean_sha256.clone(), adm.prefix.clone())
            };
            let prebuilt = self.effective_prebuilt_dir(&prefix);
            self.olean_cache.set_prebuilt_dir(prebuilt);
            self.olean_cache.preload_prebuilt()?;
            Some((lean_sha, sysroot_sha))
        } else {
            None
        };

        if !target_rejection && self.sandbox_mode == SandboxMode::Unsandboxed {
            let mem_limit_mb = self.effective_lean_memory_limit_mb(None);
            let lib_dir = self.stage.join(lib_subdir);
            fs::create_dir_all(&lib_dir)
                .map_err(|e| Failure::operational("compile", e.to_string()))?;
            self.counter.fetch_add(order.len(), Ordering::Relaxed);
            let Self {
                stage,
                environment,
                admitted,
                compiled_roles,
                olean_cache,
                olean_ledger,
                ..
            } = self;
            let stage: &Path = stage;
            let environment: &BTreeMap<String, String> = environment;
            let compiled_roles: &BTreeMap<String, TargetRole> = compiled_roles;
            let adm = admitted
                .as_mut()
                .expect("toolchain admission verified above");
            let exec_lean = adm.exec_lean.clone();
            let total = order.len();
            let mut path_sha_cache = BTreeMap::new();
            let mut transitive_memo = BTreeMap::new();
            let mut shared = (
                adm,
                olean_cache,
                olean_ledger,
                &mut path_sha_cache,
                &mut transitive_memo,
                0usize,
                0usize,
                &mut on_module_done,
            );

            return run_parallel_dag(
                &plan,
                max_workers,
                "compile",
                "worker panicked during Lean compilation",
                &mut shared,
                |(adm, olean_cache, _, path_sha_cache, transitive_memo, ..), idx| {
                    let module = &order[idx];
                    let edge_list = &imports[module];
                    let mod_is_module = is_module.get(module).copied().unwrap_or(false);
                    let src_path = &sources[module];
                    let disable_auto_implicit =
                        compiled_roles.get(module) == Some(&TargetRole::Specification);
                    match prepare_module_cache(
                        olean_cache,
                        adm,
                        module,
                        edge_list,
                        mod_is_module,
                        src_path,
                        &lib_dir,
                        warn_as_err,
                        disable_auto_implicit,
                        target_rejection,
                        cache_ctx.as_ref(),
                        path_sha_cache,
                        transitive_memo,
                    )? {
                        ModuleCachePrep::Cached(parts) => Ok(PreparedModuleCompile::Cached(parts)),
                        ModuleCachePrep::CompileNeeded(cache_key) => {
                            let setup_path = stage.join(format!("{module}.setup.json"));
                            write_setup_json_to_path(
                                &setup_path,
                                adm,
                                module,
                                edge_list,
                                mod_is_module,
                                None,
                            )?;
                            let output =
                                lib_dir.join(format!("{}.olean", module.replace('.', "/")));
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
                                disable_auto_implicit,
                            );
                            Ok(PreparedModuleCompile::Compile {
                                work: (output, compile_args),
                                cache_key,
                            })
                        }
                    }
                },
                |idx, prep| match prep {
                    PreparedModuleCompile::Cached(parts) => {
                        Ok(ExecutedModuleCompile::Cached(parts))
                    }
                    PreparedModuleCompile::Compile {
                        work: (output_path, compile_args),
                        cache_key,
                    } => {
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
                        let mod_arts = collect_compiled_artifacts(module, &output_path)?;
                        let mut parts_with_sha = Vec::with_capacity(mod_arts.olean_parts.len());
                        for part_path in mod_arts.olean_parts {
                            let suffix = olean_part_suffix(&part_path)?.to_owned();
                            let path = PathBuf::from(&part_path);
                            let sha = sha256_file(&path, "olean-cache")?;
                            parts_with_sha.push((suffix, path, sha));
                        }
                        Ok(ExecutedModuleCompile::Compiled {
                            done: parts_with_sha,
                            cache_key,
                        })
                    }
                },
                |(adm, olean_cache, olean_ledger, path_sha_cache, _, completed, cached_count, cb),
                 idx,
                 exec_res| {
                    let module = &order[idx];
                    let is_cached = matches!(exec_res, ExecutedModuleCompile::Cached(_));
                    let res = match exec_res {
                        ExecutedModuleCompile::Cached(parts_with_sha) => {
                            finish_module_artifacts(
                                adm,
                                olean_cache,
                                olean_ledger,
                                path_sha_cache,
                                module,
                                &imports[module],
                                &parts_with_sha,
                                false,
                                None,
                            )
                        }
                        ExecutedModuleCompile::Compiled { done: parts_with_sha, cache_key } => {
                            finish_module_artifacts(
                                adm,
                                olean_cache,
                                olean_ledger,
                                path_sha_cache,
                                module,
                                &imports[module],
                                &parts_with_sha,
                                false,
                                cache_key,
                            )
                        }
                    };
                    if res.is_ok() {
                        if is_cached {
                            *cached_count += 1;
                        }
                        *completed += 1;
                        cb(*completed, total, *cached_count);
                    }
                    res
                },
            );
        }

        let runtime = self.ensure_sandbox_ready()?;
        // Never share disk-cached target shard artifacts across unsandboxed and
        // sandboxed elaboration modes (`THREAT_MODEL.md` taint separation).
        let allow_target_shard_cache = target_rejection
            && self.sandbox_mode != SandboxMode::Unsandboxed
            && runtime.backend != ActiveSandbox::None;
        let mem_limit_mb = self.effective_lean_memory_limit_mb(None);
        let runs_dir = self.stage.join("runs");
        create_dir_mode(&runs_dir, 0o700)?;
        let lib_dir = self.stage.join(lib_subdir);
        create_dir_mode(&lib_dir, 0o700)?;

        let Self {
            stage,
            counter,
            admitted,
            compiled_roles,
            child_timeout,
            olean_cache,
            olean_ledger,
            ..
        } = self;
        let child_timeout = *child_timeout;
        let compiled_roles: &BTreeMap<String, TargetRole> = compiled_roles;
        let adm = admitted.as_mut().expect("toolchain admission verified above");
        let total = order.len();
        let mut path_sha_cache = BTreeMap::new();
        let mut transitive_memo = BTreeMap::new();
        let mut shared = (
            adm,
            olean_cache,
            olean_ledger,
            &mut path_sha_cache,
            &mut transitive_memo,
            0usize,
            0usize,
            &mut on_module_done,
        );

        run_parallel_dag(
            &plan,
            max_workers,
            "compile",
            "worker panicked during Lean compilation",
            &mut shared,
            |(adm, olean_cache, _, path_sha_cache, transitive_memo, ..), idx| {
                let module = &order[idx];
                let edge_list = &imports[module];
                let mod_is_module = is_module.get(module).copied().unwrap_or(false);
                let src_path = &sources[module];
                let disable_auto_implicit =
                    compiled_roles.get(module) == Some(&TargetRole::Specification);
                match prepare_module_cache(
                    olean_cache,
                    adm,
                    module,
                    edge_list,
                    mod_is_module,
                    src_path,
                    &lib_dir,
                    warn_as_err,
                    disable_auto_implicit,
                    allow_target_shard_cache,
                    cache_ctx.as_ref(),
                    path_sha_cache,
                    transitive_memo,
                )? {
                    ModuleCachePrep::Cached(parts) => Ok(PreparedModuleCompile::Cached(parts)),
                    ModuleCachePrep::CompileNeeded(cache_key) => {
                        let run_id = counter.fetch_add(1, Ordering::Relaxed) + 1;
                        let (_run_dir, in_dir, out_dir, tmp_dir) =
                            prepare_run_dirs_at(stage, run_id)?;
                        let leaf = module.rsplit('.').next().unwrap_or(module).to_owned();
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
                        write_setup_json_to_path(
                            &setup_host,
                            adm,
                            module,
                            edge_list,
                            mod_is_module,
                            Some(&mapper),
                        )?;
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
                            disable_auto_implicit,
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
                        Ok(PreparedModuleCompile::Compile {
                            work: (policy, out_dir, tmp_dir, leaf, mod_is_module),
                            cache_key,
                        })
                    }
                }
            },
            |idx, prep| match prep {
                PreparedModuleCompile::Cached(parts) => Ok(ExecutedModuleCompile::Cached(parts)),
                PreparedModuleCompile::Compile {
                    work: (policy, out_dir, tmp_dir, leaf, mod_is_module),
                    cache_key,
                } => {
                    let module = &order[idx];
                    let label = format!("compile-{module}");
                    let output = runtime.execute(&policy);
                    let _ = fs::remove_dir_all(&tmp_dir);
                    let output = output?;
                    check_lean_output(&label, output, target_rejection)?;
                    Ok(ExecutedModuleCompile::Compiled {
                        done: (out_dir, leaf, mod_is_module),
                        cache_key,
                    })
                }
            },
            |(adm, olean_cache, olean_ledger, path_sha_cache, _, completed, cached_count, cb),
             idx,
             exec_res| {
                let module = &order[idx];
                let is_cached = matches!(exec_res, ExecutedModuleCompile::Cached(_));
                let res = match exec_res {
                    ExecutedModuleCompile::Cached(parts_with_sha) => {
                        finish_module_artifacts(
                            adm,
                            olean_cache,
                            olean_ledger,
                            path_sha_cache,
                            module,
                            &imports[module],
                            &parts_with_sha,
                            true,
                            None,
                        )
                    }
                    ExecutedModuleCompile::Compiled {
                        done: (out_dir, leaf, mod_is_module),
                        cache_key,
                    } => {
                        let dest_olean =
                            lib_dir.join(format!("{}.olean", module.replace('.', "/")));
                        let parts_with_sha = promote_compiled_module_parts(
                            &out_dir,
                            &leaf,
                            &dest_olean,
                            mod_is_module,
                        )?;
                        finish_module_artifacts(
                            adm,
                            olean_cache,
                            olean_ledger,
                            path_sha_cache,
                            module,
                            &imports[module],
                            &parts_with_sha,
                            true,
                            cache_key,
                        )
                    }
                };
                if res.is_ok() {
                    if is_cached {
                        *cached_count += 1;
                    }
                    *completed += 1;
                    cb(*completed, total, *cached_count);
                }
                res
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
        check_lean_stderr_panic(&label, &output)?;
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
        if let (Some(sp_path), Some(sp_sha)) = (&adm.spec_preflight, &adm.spec_preflight_sha256) {
            let actual = sha256_file(sp_path, "artifact-ledger")?;
            if !actual.eq_ignore_ascii_case(sp_sha) {
                return Err(Failure::operational(
                    "artifact-ledger",
                    "staged SpecPreflight.lean changed during elaboration",
                ));
            }
        }
        if let Some((olean_path, expected_olean_sha)) = &adm.spec_preflight_olean {
            let actual = sha256_file(olean_path, "artifact-ledger")?;
            if !actual.eq_ignore_ascii_case(expected_olean_sha) {
                return Err(Failure::operational(
                    "artifact-ledger",
                    "staged SpecPreflight.olean changed during elaboration",
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

    /// Return whether `mode` should execute the minimal runtime
    /// `SpecPreflight.lean` inspector instead of `TrustedBoundary.lean`.
    ///
    /// `"sysroot-consts"` and `"target-consts"` exist only in
    /// `SpecPreflight.lean`, so they use it whenever it is staged (letting
    /// pinned-toolchain tests exercise them); the shared preflight modes
    /// switch to it only on the NDJSON comparator route.
    fn uses_spec_preflight(&self, mode: &str) -> Result<bool, Failure> {
        let adm = self.admitted()?;
        if adm.spec_preflight.is_none() {
            return Ok(false);
        }
        Ok(match mode {
            "sysroot-consts" | "target-consts" => true,
            "spec-preflight" if self.spec_preflight_mode_via_spec_preflight => true,
            "headers" | "spec-preflight" | "resolve-imports" => adm.ndjson_tools.is_some(),
            _ => false,
        })
    }

    /// Compile staged `control/<stem>.lean` (`SpecPreflight.lean` for runtime
    /// preflight and module-index modes, or `TrustedBoundary.lean` for offline
    /// Pass 1/Pass 2 and transitional legacy `v4.34.1` `target-audit`) once per
    /// `(lean_sha256, sysroot_prefix, source_sha256)` into
    /// `control/<stem>.olean` (validated through Door 1 and pinned by SHA-256
    /// in [`AdmittedToolchain`]).
    fn ensure_inspector_compiled(
        &mut self,
        mode: &str,
        direct: bool,
        use_spec_preflight: bool,
    ) -> Result<PathBuf, Failure> {
        let stem = if use_spec_preflight { "SpecPreflight" } else { "TrustedBoundary" };
        {
            let adm = self.admitted()?;
            let existing = if use_spec_preflight {
                &adm.spec_preflight_olean
            } else {
                &adm.inspector_olean
            };
            if let Some((olean_path, _)) = existing {
                return Ok(olean_path.clone());
            }
        }
        let compile_phase = if direct { "compile-inspector" } else { mode };
        let (inspector_host, expected_sha, lean_sha, prefix) = {
            let adm = self.admitted()?;
            if use_spec_preflight {
                (
                    adm.spec_preflight.clone().ok_or_else(|| {
                        Failure::operational(compile_phase, "missing staged SpecPreflight.lean")
                    })?,
                    adm.spec_preflight_sha256.clone().ok_or_else(|| {
                        Failure::operational(compile_phase, "missing SpecPreflight.lean digest")
                    })?,
                    adm.lean_sha256.clone(),
                    adm.prefix.clone(),
                )
            } else {
                (
                    adm.inspector.clone(),
                    adm.inspector_sha256.clone(),
                    adm.lean_sha256.clone(),
                    adm.prefix.clone(),
                )
            }
        };
        let actual_sha = sha256_file(&inspector_host, compile_phase)?;
        if !actual_sha.eq_ignore_ascii_case(&expected_sha) {
            return Err(Failure::operational(
                compile_phase,
                format!("staged {stem}.lean changed before compilation"),
            ));
        }
        let runtime_opt = if direct {
            None
        } else {
            Some(self.ensure_sandbox_ready()?)
        };
        let inspector_cache_key = if self.olean_cache.is_enabled() {
            let sysroot_manifest_sha256 = self.ensure_sysroot_manifest_sha256()?;
            let prebuilt_dir = self.effective_prebuilt_dir(&prefix);
            self.olean_cache.set_prebuilt_dir(prebuilt_dir);
            let src_bytes = fs::read(&inspector_host)
                .map_err(|e| Failure::operational(compile_phase, e.to_string()))?;
            Some(OleanCacheKeyInput {
                kind: CacheKind::Inspector,
                module: stem.to_owned(),
                lean_sha256: lean_sha.clone(),
                sysroot_manifest_sha256,
                source_sha256: actual_sha.clone(),
                is_module: source_starts_with_module_keyword(&src_bytes),
                flags: canonical_inspector_flags(),
                imports: Vec::new(),
            })
        } else {
            None
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
                stem,
                &cached.bytes,
                &cached.sha256,
                compile_phase,
            )?
        } else if let Some(ref key_input) = inspector_cache_key
            && let Some(parts) = self.olean_cache.lookup_bytes(key_input)?
        {
            let (bytes, sha) = parts
                .into_iter()
                .find(|(suffix, _, _)| suffix == "olean")
                .map(|(_, bytes, sha)| (bytes, sha))
                .ok_or_else(|| {
                    Failure::operational("olean-cache", "cached inspector missing primary olean")
                })?;
            let promoted =
                materialize_cached_inspector_olean(&control_dir, stem, &bytes, &sha, compile_phase)?;
            *guard =
                Some(Arc::new(CompiledInspectorArtifacts { bytes, sha256: promoted.1.clone() }));
            promoted
        } else {
            let (olean_dest, olean_sha) = if direct {
                let run_id = self.next_counter();
                let out_dir = self
                    .stage
                    .join(format!("inspector-compile-{run_id:03}"));
                create_dir_mode(&out_dir, 0o700)?;
                let out_olean = out_dir.join(format!("{stem}.olean"));
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
                check_lean_stderr_panic(compile_phase, &output)?;
                if !output.status.success() {
                    let _ = fs::remove_dir_all(&out_dir);
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    return Err(Failure::new(
                        2,
                        compile_phase,
                        format!("Lean exited {:?}: {}", output.status.code(), stderr.trim()),
                    ));
                }
                let promoted = promote_inspector_olean(&control_dir, stem, &out_dir, compile_phase);
                let _ = fs::remove_dir_all(&out_dir);
                promoted?
            } else {
                let runtime = runtime_opt.expect("sandbox runtime initialized");
                let (_run_dir, in_dir, out_dir, tmp_dir) = self.prepare_run_dirs()?;
                let in_inspector = in_dir.join(format!("{stem}.lean"));
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
                let out_olean = out_dir.join(format!("{stem}.olean"));
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
                check_lean_stderr_panic(compile_phase, &output)?;
                if !output.status.success() {
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    return Err(Failure::new(
                        2,
                        compile_phase,
                        format!("Lean exited {:?}: {}", output.status.code(), stderr.trim()),
                    ));
                }
                promote_inspector_olean(&control_dir, stem, &out_dir, compile_phase)?
            };
            if let Some(ref key_input) = inspector_cache_key {
                self.olean_cache.store_compiled(
                    key_input,
                    &[("olean", olean_dest.as_path(), olean_sha.as_str())],
                )?;
            }
            let bytes = fs::read(&olean_dest)
                .map_err(|e| Failure::operational(compile_phase, e.to_string()))?;
            *guard = Some(Arc::new(CompiledInspectorArtifacts {
                bytes,
                sha256: olean_sha.clone(),
            }));
            (olean_dest, olean_sha)
        };
        drop(guard);

        let adm = self.admitted.as_mut().unwrap();
        if use_spec_preflight {
            adm.spec_preflight_olean = Some((olean_dest.clone(), olean_sha));
        } else {
            adm.inspector_olean = Some((olean_dest.clone(), olean_sha));
        }
        Ok(olean_dest)
    }

    /// Invoke staged `TrustedBoundary.lean` with a serialized JSON request and
    /// validate its structured response envelope (`policy:` -> code `1`,
    /// operational -> code `2`).
    #[doc(hidden)]
    pub fn invoke_inspector(&mut self, mode: &str, req: &Json) -> Result<Json, Failure> {
        let map: serde_json::Map<String, Json> = self.invoke_inspector_typed(mode, req)?;
        Ok(Json::Object(map))
    }

    /// Invoke the staged Lean inspector (`SpecPreflight.lean` for runtime
    /// preflight and module-index modes, or `TrustedBoundary.lean` for offline
    /// Pass 1/Pass 2 and transitional legacy `v4.34.1` `target-audit`) and
    /// deserialize `"result"` directly into a strict caller-defined schema `T`.
    pub(crate) fn invoke_inspector_typed<T: serde::de::DeserializeOwned>(
        &mut self,
        mode: &str,
        req: &Json,
    ) -> Result<T, Failure> {
        let use_spec_preflight = self.uses_spec_preflight(mode)?;
        if self.sandbox_mode == SandboxMode::Unsandboxed && matches!(mode, "preflight" | "audit") {
            let text = self.invoke_inspector_direct_text(mode, req, use_spec_preflight)?;
            return parse_inspector_ok_typed(mode, &text);
        }

        let stem = if use_spec_preflight { "SpecPreflight" } else { "TrustedBoundary" };
        let olean_host = self.ensure_inspector_compiled(mode, false, use_spec_preflight)?;
        let runtime = self.ensure_sandbox_ready()?;
        let (_run_dir, in_dir, out_dir, tmp_dir) = self.prepare_run_dirs()?;

        copy_readonly_file(&olean_host, &in_dir.join(format!("{stem}.olean")), mode)?;
        let in_entry = in_dir.join(format!("{stem}Entry.lean"));
        fs::write(&in_entry, format!("import {stem}\n")).map_err(|e| {
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
        // Mount `stage/lib` (which holds compiled `Proof` `.olean`s) ONLY into
        // the isolated `"target-export"` child process, NEVER into the
        // verdict-producing `"target-audit"` process or the `"target-consts"`
        // module index. For those two modes, only explicitly listed non-proof
        // target `.olean`s are staged into `in_dir/lib` below so authored
        // `Proof` `.olean` bytes are physically absent from their mount
        // namespace and Landlock ruleset.
        let stage_lib_dir = self.stage.join("lib");
        if mode == "target-export" {
            create_dir_mode(&stage_lib_dir, 0o700)?;
            ro_mounts.push(MountSpec {
                host: stage_lib_dir.clone(),
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
            if let Some(export_path) = obj.get("proofExportPath").and_then(Json::as_str) {
                let copy_dest = in_dir.join("proof-export.json");
                copy_readonly_file(Path::new(export_path), &copy_dest, mode)?;
                obj.insert(
                    "proofExportPath".to_string(),
                    Json::String(mapper.map_str(&copy_dest)?),
                );
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
                let in_lib_dir = in_dir.join("lib");
                let mut staged_nonproof_dirs = BTreeSet::new();
                for entry in arts_arr.iter_mut() {
                    if let Some(pair) = entry.as_array_mut()
                        && pair.len() == 2
                        && let Some(groups) = pair[1].as_array_mut()
                    {
                        for group in groups.iter_mut() {
                            if let Some(paths) = group.as_array_mut() {
                                for p in paths.iter_mut() {
                                    if let Some(s) = p.as_str() {
                                        let host_path = Path::new(s);
                                        if matches!(mode, "target-audit" | "target-consts")
                                            && let Ok(rel) = host_path.strip_prefix(&stage_lib_dir)
                                        {
                                            let dest = in_lib_dir.join(rel);
                                            copy_readonly_file(host_path, &dest, mode)?;
                                            let mut dir = dest.parent();
                                            while let Some(d) = dir {
                                                if !d.starts_with(&in_lib_dir) {
                                                    break;
                                                }
                                                staged_nonproof_dirs.insert(d.to_path_buf());
                                                dir = d.parent();
                                            }
                                            *p = Json::String(mapper.map_str(&dest)?);
                                        } else {
                                            *p = Json::String(mapper.map_str(host_path)?);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                // Lock staged non-proof artifact directories read-only bottom-up
                // after all files have been copied into `in_dir/lib`.
                for d in staged_nonproof_dirs.into_iter().rev() {
                    set_mode(&d, 0o500)?;
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

        check_lean_stderr_panic(mode, &output)?;
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
        parse_inspector_ok_typed(mode, &resp_text)
    }

    fn invoke_inspector_direct_text(
        &mut self,
        mode: &str,
        req: &Json,
        use_spec_preflight: bool,
    ) -> Result<String, Failure> {
        let stem = if use_spec_preflight { "SpecPreflight" } else { "TrustedBoundary" };
        let _olean_host = self.ensure_inspector_compiled(mode, true, use_spec_preflight)?;
        let control_dir = self.stage.join("control");
        let entry = control_dir.join(format!("{stem}Entry.lean"));
        let run_id = self.next_counter();
        let req_stem = self.stage.join(format!("request-{run_id:03}-{mode}"));
        let request_path = PathBuf::from(format!("{}.json", req_stem.display()));
        let result_path = PathBuf::from(format!("{}.result.json", req_stem.display()));
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

        check_lean_stderr_panic(mode, &output)?;
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

        fs::read_to_string(&result_path)
            .map_err(|e| Failure::new(2, mode, format!("missing/malformed inspector result: {e}")))
    }

    /// Execute `leanexport` inside `ExecSeal` (`5-init`, `5a`, or `5b`),
    /// mounting only the explicitly listed read-only `.olean` root directory
    /// (if any) alongside the clean sysroot, verifying that `rw_out` stays
    /// empty, re-hashing the binary after exit, and streaming NDJSON stdout
    /// directly to `dest_ndjson`.
    fn run_sandboxed_leanexport(
        &mut self,
        phase: &str,
        extra_olean_root: Option<&Path>,
        args: &[String],
        dest_ndjson: &Path,
    ) -> Result<String, Failure> {
        let arg_bytes: usize = args.iter().map(|a| a.len() + 1).sum();
        if arg_bytes > MAX_LEANEXPORT_ARG_BYTES {
            return Err(Failure::operational(
                phase,
                format!(
                    "leanexport command line needs {arg_bytes} bytes, above the \
                     {MAX_LEANEXPORT_ARG_BYTES}-byte limit"
                ),
            ));
        }
        let (leanexport_host, expected_sha, sysroot_prefix, sysroot_lib_lean) = {
            let adm = self.admitted()?;
            let tools = adm.ndjson_tools.as_ref().ok_or_else(|| {
                Failure::operational(phase, "NDJSON comparator binaries unavailable in sysroot")
            })?;
            (
                tools.leanexport.clone(),
                tools.leanexport_sha256.clone(),
                adm.prefix.clone(),
                adm.prefix.join("lib/lean"),
            )
        };
        let actual_sha = sha256_file_deref(&leanexport_host, phase)?;
        if !actual_sha.eq_ignore_ascii_case(&expected_sha) {
            return Err(Failure::operational(
                phase,
                "leanexport binary changed before execution",
            ));
        }

        let runtime = self.ensure_sandbox_ready()?;
        let (_run_dir, in_dir, out_dir, tmp_dir) = self.prepare_run_dirs()?;
        set_mode(&in_dir, 0o500)?;

        let mut ro_mounts = vec![
            MountSpec { host: in_dir, child: PathBuf::from("/work/in") },
            MountSpec {
                host: leanexport_host.clone(),
                child: PathBuf::from("/toolchain/bin/leanexport"),
            },
        ];
        if let Some(root) = extra_olean_root {
            ro_mounts.push(MountSpec {
                host: root.to_path_buf(),
                child: PathBuf::from("/work/lib"),
            });
        }
        let rw_out = MountSpec { host: out_dir.clone(), child: PathBuf::from("/work/out") };
        let rw_tmp = MountSpec { host: tmp_dir.clone(), child: PathBuf::from("/work/tmp") };
        let mapper = PathMapper::new(&runtime, &ro_mounts, &rw_out, &rw_tmp);

        let sysroot_mapped = mapper.map_str(&sysroot_lib_lean)?;
        let lean_path = if let Some(root) = extra_olean_root {
            format!("{}:{sysroot_mapped}", mapper.map_str(root)?)
        } else {
            sysroot_mapped
        };
        let mut extra_env = BTreeMap::new();
        extra_env.insert("LEAN_ABORT_ON_PANIC".to_string(), "1".to_string());
        // Setting `LEAN_SYSROOT` lets `leanexport`'s `Lean.findSysroot` resolve
        // the mounted toolchain root directly without spawning `lean
        // --print-prefix` inside the sandbox.
        extra_env.insert("LEAN_SYSROOT".to_string(), mapper.map_str(&sysroot_prefix)?);
        extra_env.insert("LEAN_PATH".to_string(), lean_path);

        let policy = SandboxPolicy {
            exec_bin: leanexport_host.clone(),
            args: args.to_vec(),
            ro_mounts,
            rw_out,
            rw_tmp,
            child_cwd: None,
            extra_env,
            timeout: self.child_timeout,
        };
        let output = runtime.execute_stdout_to_file(&policy, dest_ndjson, MAX_NDJSON_BYTES);
        let out_nonempty = fs::read_dir(&out_dir)
            .map(|mut entries| entries.next().is_some())
            .unwrap_or(true);
        let _ = fs::remove_dir_all(&tmp_dir);
        let output = output?;
        check_lean_stderr_panic(phase, &output)?;
        let post_sha = sha256_file_deref(&leanexport_host, phase)?;
        if !post_sha.eq_ignore_ascii_case(&expected_sha) {
            return Err(Failure::operational(
                phase,
                "leanexport binary changed during verification",
            ));
        }
        if out_nonempty {
            return Err(Failure::operational(
                "door1",
                format!("unexpected output files from {phase} leanexport"),
            ));
        }
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(Failure::operational(
                phase,
                format!(
                    "leanexport exited {:?}: {}",
                    output.status.code(),
                    stderr.trim()
                ),
            ));
        }
        sha256_file(dest_ndjson, phase)
    }

    /// Export (or retrieve from the process-wide cache) the clean sysroot
    /// `init_primitives_cone.ndjson` pinning all 39 [`PINNED_INIT_PRIMITIVES`],
    /// the 3 [`STANDARD_PERMITTED_AXIOMS`], and
    /// [`PINNED_SYSTEM_PLATFORM_DECLS`].
    ///
    /// Mounting only the clean Lean sysroot (zero target `.olean`s) guarantees
    /// that `init_primitives_cone.ndjson` cannot be influenced by untrusted
    /// proof artifacts.
    pub(crate) fn export_ndjson_init_primitives(
        &mut self,
    ) -> Result<Arc<CachedInitPrimitives>, Failure> {
        let (prefix, leanexport_sha, sysroot_key) = {
            let adm = self.admitted()?;
            let tools = adm.ndjson_tools.as_ref().ok_or_else(|| {
                Failure::operational(
                    "ndjson-init-primitives",
                    "NDJSON comparator binaries unavailable in sysroot",
                )
            })?;
            let sysroot_key = sysroot_content_key(adm);
            (adm.prefix.clone(), tools.leanexport_sha256.clone(), sysroot_key)
        };
        let slot = {
            let mut map = init_primitives_cache().lock().unwrap_or_else(|e| e.into_inner());
            map.entry((prefix, leanexport_sha, sysroot_key))
                .or_insert_with(|| Arc::new(Mutex::new(None)))
                .clone()
        };
        let mut guard = slot.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cached) = guard.as_ref() {
            return Ok(cached.clone());
        }
        let ndjson_dir = self.stage.join("ndjson");
        create_dir_mode(&ndjson_dir, 0o700)?;
        let dest = ndjson_dir.join("init_primitives_cone.ndjson");
        let mut args = vec!["Init".to_string(), "--".to_string()];
        args.extend(PINNED_INIT_PRIMITIVES.iter().map(|s| (*s).to_owned()));
        args.extend(STANDARD_PERMITTED_AXIOMS.iter().map(|s| (*s).to_owned()));
        args.extend(PINNED_SYSTEM_PLATFORM_DECLS.iter().map(|s| (*s).to_owned()));
        let sha256 = self.run_sandboxed_leanexport("ndjson-init-primitives", None, &args, &dest)?;
        let bytes = fs::read(&dest)
            .map_err(|e| Failure::operational("ndjson-init-primitives", e.to_string()))?;
        let entry = Arc::new(CachedInitPrimitives { bytes, sha256 });
        *guard = Some(entry.clone());
        Ok(entry)
    }

    /// Collect (and cache in process memory) the authenticated sysroot
    /// `encodeCanonName -> moduleName` inventory via `SpecPreflight` mode
    /// `"sysroot-consts"` (`loadExts := false`, zero target `.olean`s loaded).
    pub(crate) fn collect_sysroot_consts_cached(
        &mut self,
    ) -> Result<Arc<HashMap<String, String>>, Failure> {
        let (cache_key, req) = {
            let adm = self.admitted()?;
            let mut sorted_fnd: Vec<String> = adm.foundation_graph.keys().cloned().collect();
            sorted_fnd.sort();
            let mut sorted_libs: Vec<String> = adm.library_modules.iter().cloned().collect();
            sorted_libs.sort();
            let spec_pf_sha = adm.spec_preflight_sha256.clone().unwrap_or_default();
            let sysroot_fp = sysroot_content_key(adm);
            let arts_arr: Vec<Json> = adm
                .artifacts
                .iter()
                .filter(|(k, _)| {
                    adm.foundation_graph.contains_key(*k) || adm.library_modules.contains(*k)
                })
                .map(|(k, parts)| json!([k, parts.to_wire()]))
                .collect();
            let graph: BTreeMap<&str, &[ImportEdge]> = adm
                .graph
                .iter()
                .filter(|(k, _)| {
                    adm.foundation_graph.contains_key(*k) || adm.library_modules.contains(*k)
                })
                .map(|(k, v)| (k.as_str(), v.as_slice()))
                .collect();
            let req = json!({
                "mode": "sysroot-consts",
                "sysroot": adm.prefix.to_string_lossy(),
                "artifacts": arts_arr,
                "foundation": sorted_fnd,
                "libraries": sorted_libs,
                "graph": graph,
            });
            let cache_key =
                (adm.prefix.clone(), spec_pf_sha, sysroot_fp, sorted_fnd, sorted_libs);
            (cache_key, req)
        };
        let slot = {
            let mut map = sysroot_consts_cache().lock().unwrap_or_else(|e| e.into_inner());
            map.entry(cache_key)
                .or_insert_with(|| Arc::new(Mutex::new(None)))
                .clone()
        };
        let mut guard = slot.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(cached) = guard.as_ref() {
            return Ok(cached.clone());
        }
        let resp = self.invoke_inspector("sysroot-consts", &req)?;
        let entries = resp
            .get("sysrootConsts")
            .and_then(Json::as_array)
            .ok_or_else(|| {
                Failure::operational("sysroot-consts", "missing sysrootConsts inventory")
            })?;
        let mut out = HashMap::new();
        for entry in entries {
            let pair = entry.as_array().ok_or_else(|| {
                Failure::operational("sysroot-consts", "malformed sysrootConsts entry")
            })?;
            if pair.len() != 2 {
                return Err(Failure::operational(
                    "sysroot-consts",
                    "malformed sysrootConsts pair",
                ));
            }
            let mod_name = pair[0].as_str().ok_or_else(|| {
                Failure::operational("sysroot-consts", "malformed sysrootConsts module name")
            })?;
            let consts = pair[1].as_array().ok_or_else(|| {
                Failure::operational("sysroot-consts", "malformed sysrootConsts constant array")
            })?;
            for c in consts {
                let encoded = c.as_str().ok_or_else(|| {
                    Failure::operational("sysroot-consts", "malformed sysrootConsts constant entry")
                })?;
                out.insert(encoded.to_owned(), mod_name.to_owned());
            }
        }
        let arc = Arc::new(out);
        *guard = Some(arc.clone());
        Ok(arc)
    }

    /// Action `5a` (`AnnealExportExpected`): materialize an isolated
    /// `stage/expected_lib/` containing strictly `{Model, Capture,
    /// Specification, Expected}` `.olean`s (zero `Proof.*` or `Anneal.*` files
    /// mounted) and export `plan.roots` with their dependencies to
    /// `expected_cone.ndjson` via sandboxed `leanexport`.
    ///
    /// `--ignore-missing` is never passed: `leanexport` aborts on any absent
    /// root or dependency instead of silently truncating the export.
    pub(crate) fn export_ndjson_expected(
        &mut self,
        trusted_modules: &[String],
        plan: &ExportPlan,
        filename: &str,
    ) -> Result<(PathBuf, String), Failure> {
        let phase = "ndjson-export-expected";
        let expected_lib = self.stage.join("expected_lib");
        if expected_lib.exists() {
            make_tree_writable(&expected_lib);
            let _ = fs::remove_dir_all(&expected_lib);
        }
        create_dir_mode(&expected_lib, 0o700)?;

        let lib_dir = self.stage.join("lib");
        for module in trusted_modules {
            let rel_base = module.replace('.', "/");
            for part in OLEAN_PARTS {
                let rel = format!("{rel_base}.{part}");
                let src = lib_dir.join(&rel);
                if *part == *"olean" || src.is_file() {
                    let dst = expected_lib.join(&rel);
                    copy_readonly_file(&src, &dst, phase)?;
                }
            }
        }
        let ndjson_dir = self.stage.join("ndjson");
        create_dir_mode(&ndjson_dir, 0o700)?;
        let dest = ndjson_dir.join(filename);

        let mut args = plan.modules.clone();
        args.push("--".to_string());
        args.extend(plan.roots.iter().cloned());
        let sha = self.run_sandboxed_leanexport(phase, Some(&expected_lib), &args, &dest)?;
        Ok((dest, sha))
    }

    /// Action `5-pin`: re-export `plan.roots` (every sysroot-named constant
    /// that `expected_cone` or `proof_full` uses) from the clean admitted
    /// sysroot alone, with zero target `.olean`s mounted, so Action `5c` can
    /// require each sysroot-named constant to equal its clean definition.
    pub(crate) fn export_ndjson_sysroot_pins(
        &mut self,
        plan: &ExportPlan,
        filename: &str,
    ) -> Result<(PathBuf, String), Failure> {
        let phase = "ndjson-sysroot-pins";
        let ndjson_dir = self.stage.join("ndjson");
        create_dir_mode(&ndjson_dir, 0o700)?;
        let dest = ndjson_dir.join(filename);
        let mut args = plan.modules.clone();
        args.push("--".to_string());
        args.extend(plan.roots.iter().cloned());
        let sha = self.run_sandboxed_leanexport(phase, None, &args, &dest)?;
        Ok((dest, sha))
    }

    /// Action `5b` (`AnnealExportProof`): export `proof_full.ndjson` from the
    /// full compiled target library strictly inside `ExecSeal`, with read-only
    /// `.olean` mounts, empty `rw_out`, and zero access to
    /// `expected_cone.ndjson` or `result.json`.
    pub(crate) fn export_ndjson_proof(
        &mut self,
        expected_module: &str,
        theorem_module: &str,
        expected_declaration: &str,
        theorem_name: &str,
        filename: &str,
    ) -> Result<(PathBuf, String), Failure> {
        let phase = "ndjson-export-proof";
        let lib_dir = self.stage.join("lib");
        let ndjson_dir = self.stage.join("ndjson");
        create_dir_mode(&ndjson_dir, 0o700)?;
        let dest = ndjson_dir.join(filename);

        let mut args = vec![expected_module.to_string()];
        if theorem_module != expected_module {
            args.push(theorem_module.to_string());
        }
        args.push("--".to_string());
        args.push(expected_declaration.to_string());
        args.push(theorem_name.to_string());
        let sha = self.run_sandboxed_leanexport(phase, Some(&lib_dir), &args, &dest)?;
        Ok((dest, sha))
    }

    /// Run `nanoda_bin` over `proof_ndjson_host` inside `ExecSeal` with
    /// `"unpermitted_axiom_hard_error": true` and `nat_extension` +
    /// `string_extension` enabled.
    pub(crate) fn run_ndjson_nanoda(
        &mut self,
        proof_ndjson_host: &Path,
        proof_ndjson_sha256: &str,
        allow_sorry_in_proof: bool,
    ) -> Result<(), Failure> {
        let phase = "ndjson-nanoda";
        let (nanoda_host, expected_sha) = {
            let adm = self.admitted()?;
            let tools = adm.ndjson_tools.as_ref().ok_or_else(|| {
                Failure::operational(phase, "nanoda_bin unavailable in sysroot")
            })?;
            (tools.nanoda_bin.clone(), tools.nanoda_bin_sha256.clone())
        };
        let actual_sha = sha256_file_deref(&nanoda_host, phase)?;
        if !actual_sha.eq_ignore_ascii_case(&expected_sha) {
            return Err(Failure::operational(
                phase,
                "nanoda_bin binary changed before execution",
            ));
        }

        let runtime = self.ensure_sandbox_ready()?;
        let (_run_dir, in_dir, out_dir, tmp_dir) = self.prepare_run_dirs()?;
        let in_ndjson = in_dir.join("proof_full.ndjson");
        copy_verified_kernel_input(proof_ndjson_host, &in_ndjson, proof_ndjson_sha256, phase)?;

        let ro_mounts = vec![
            MountSpec { host: in_dir.clone(), child: PathBuf::from("/work/in") },
            MountSpec {
                host: nanoda_host.clone(),
                child: PathBuf::from("/toolchain/bin/nanoda_bin"),
            },
        ];
        let rw_out = MountSpec { host: out_dir.clone(), child: PathBuf::from("/work/out") };
        let rw_tmp = MountSpec { host: tmp_dir.clone(), child: PathBuf::from("/work/tmp") };
        let mapper = PathMapper::new(&runtime, &ro_mounts, &rw_out, &rw_tmp);

        let mapped_ndjson = mapper.map_str(&in_ndjson)?;
        let cfg = build_nanoda_config_json(
            &mapped_ndjson,
            allow_sorry_in_proof,
            crate::toolchain::default_compile_workers(4),
        );
        let cfg_host = in_dir.join("nanoda_config.json");
        let cfg_bytes = serde_json::to_vec(&cfg)
            .map_err(|e| Failure::operational(phase, format!("serialize nanoda config: {e}")))?;
        fs::write(&cfg_host, cfg_bytes)
            .map_err(|e| Failure::operational(phase, format!("write nanoda config: {e}")))?;
        set_mode(&cfg_host, 0o444)?;
        set_mode(&in_dir, 0o500)?;

        let mut extra_env = BTreeMap::new();
        extra_env.insert("LEAN_ABORT_ON_PANIC".to_string(), "1".to_string());
        let policy = SandboxPolicy {
            exec_bin: nanoda_host.clone(),
            args: vec![mapper.map_str(&cfg_host)?],
            ro_mounts,
            rw_out,
            rw_tmp,
            child_cwd: None,
            extra_env,
            timeout: self.child_timeout,
        };
        let output = runtime.execute(&policy);
        let out_nonempty = fs::read_dir(&out_dir)
            .map(|mut entries| entries.next().is_some())
            .unwrap_or(true);
        let _ = fs::remove_dir_all(&tmp_dir);
        let output = output?;
        check_lean_stderr_panic(phase, &output)?;
        let post_sha = sha256_file_deref(&nanoda_host, phase)?;
        if !post_sha.eq_ignore_ascii_case(&expected_sha) {
            return Err(Failure::operational(
                phase,
                "nanoda_bin binary changed during verification",
            ));
        }
        if out_nonempty {
            return Err(Failure::operational("door1", "unexpected output files from nanoda_bin"));
        }
        if !output.status.success() {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(Failure::policy(
                phase,
                format!(
                    "nanoda_bin rejected proof export (exit {:?}): {} {}",
                    output.status.code(),
                    stdout.trim(),
                    stderr.trim()
                ),
            ));
        }
        Ok(())
    }

    /// Execute a standalone NDJSON kernel binary (`con-ron`, `con-leche`, or
    /// `lean4lean`) over `proof_ndjson_host` inside `ExecSeal`, verifying the
    /// binary SHA-256 against its admission digest before and after execution
    /// and enforcing empty `rw_out`.
    fn run_ndjson_standalone_kernel(
        &mut self,
        phase: &'static str,
        kernel: StandaloneNdjsonKernel,
        bin_host: PathBuf,
        expected_sha: &str,
        (proof_ndjson_host, proof_ndjson_sha256): (&Path, &str),
    ) -> Result<(), Failure> {
        let kernel_label = kernel.label();
        let actual_sha = sha256_file_deref(&bin_host, phase)?;
        if !actual_sha.eq_ignore_ascii_case(expected_sha) {
            return Err(Failure::operational(
                phase,
                format!("{kernel_label} binary changed before execution"),
            ));
        }

        let runtime = self.ensure_sandbox_ready()?;
        let (_run_dir, in_dir, out_dir, tmp_dir) = self.prepare_run_dirs()?;
        let in_ndjson = in_dir.join("proof_full.ndjson");
        copy_verified_kernel_input(proof_ndjson_host, &in_ndjson, proof_ndjson_sha256, phase)?;
        set_mode(&in_dir, 0o500)?;

        let ro_mounts = vec![
            MountSpec { host: in_dir, child: PathBuf::from("/work/in") },
            MountSpec {
                host: bin_host.clone(),
                child: PathBuf::from(format!("/toolchain/bin/{kernel_label}")),
            },
        ];
        let rw_out = MountSpec { host: out_dir.clone(), child: PathBuf::from("/work/out") };
        let rw_tmp = MountSpec { host: tmp_dir.clone(), child: PathBuf::from("/work/tmp") };
        let mapper = PathMapper::new(&runtime, &ro_mounts, &rw_out, &rw_tmp);

        let mut args = kernel.args();
        args.push(mapper.map_str(&in_ndjson)?);

        let mut extra_env = BTreeMap::new();
        extra_env.insert("LEAN_ABORT_ON_PANIC".to_string(), "1".to_string());
        let policy = SandboxPolicy {
            exec_bin: bin_host.clone(),
            args,
            ro_mounts,
            rw_out,
            rw_tmp,
            child_cwd: None,
            extra_env,
            timeout: self.child_timeout,
        };
        let output = runtime.execute(&policy);
        let out_nonempty = fs::read_dir(&out_dir)
            .map(|mut entries| entries.next().is_some())
            .unwrap_or(true);
        let _ = fs::remove_dir_all(&tmp_dir);
        let output = output?;
        check_lean_stderr_panic(phase, &output)?;
        let post_sha = sha256_file_deref(&bin_host, phase)?;
        if !post_sha.eq_ignore_ascii_case(expected_sha) {
            return Err(Failure::operational(
                phase,
                format!("{kernel_label} binary changed during verification"),
            ));
        }
        if out_nonempty {
            return Err(Failure::operational(
                "door1",
                format!("unexpected output files from {kernel_label}"),
            ));
        }
        if !output.status.success() {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(Failure::policy(
                phase,
                format!(
                    "{kernel_label} rejected proof export (exit {:?}): {} {}",
                    output.status.code(),
                    stdout.trim(),
                    stderr.trim()
                ),
            ));
        }
        Ok(())
    }

    /// Run `con-ron --verified` (the formally verified independent Rust arena
    /// kernel bundled in Lean `v4.35.0+`) over `proof_ndjson_host` inside
    /// `ExecSeal`.
    pub(crate) fn run_ndjson_con_ron(
        &mut self,
        proof_ndjson_host: &Path,
        proof_ndjson_sha256: &str,
    ) -> Result<(), Failure> {
        let phase = "ndjson-con-ron";
        let (bin_host, expected_sha) = {
            let adm = self.admitted()?;
            let tools = adm.ndjson_tools.as_ref().ok_or_else(|| {
                Failure::operational(phase, "con-ron unavailable in sysroot")
            })?;
            (tools.con_ron.clone(), tools.con_ron_sha256.clone())
        };
        self.run_ndjson_standalone_kernel(
            phase,
            StandaloneNdjsonKernel::ConRon,
            bin_host,
            &expected_sha,
            (proof_ndjson_host, proof_ndjson_sha256),
        )
    }

    /// Run `con-leche` (independent formally verified kernel bundled in Lean
    /// `v4.35.0+`) over `proof_ndjson_host` inside `ExecSeal` for
    /// `--paranoid-quorum`.
    ///
    /// Note on `lake comparator --paranoid`: Anneal executes the extra quorum
    /// kernels (`con-leche` and `lean4lean --import`) directly inside
    /// `ExecSeal` with SHA-256 pinning rather than delegating to `lake
    /// comparator --paranoid`, because (1) `lake comparator` invokes
    /// `nanoda_bin` with `"unpermitted_axiom_hard_error": false` and runs its
    /// own nested sandbox outside `ExecSeal`, and (2) Lean `v4.35.0`'s
    /// `Lean.Kernel.Environment.replay` (used by `leanchecker --from-export`
    /// and `leanchecker-paranoid --from-export`) iterates `NameSet` in hash
    /// order without pre-replaying implicit literal-reduction constants such as
    /// `String.ofList`, causing false rejections on targets that reduce string
    /// literals.
    pub(crate) fn run_ndjson_con_leche(
        &mut self,
        proof_ndjson_host: &Path,
        proof_ndjson_sha256: &str,
    ) -> Result<(), Failure> {
        let phase = "ndjson-con-leche";
        let (bin_host, expected_sha) = {
            let adm = self.admitted()?;
            let tools = adm.ndjson_tools.as_ref().ok_or_else(|| {
                Failure::operational(phase, "NDJSON comparator binaries unavailable in sysroot")
            })?;
            match (&tools.con_leche, &tools.con_leche_sha256) {
                (Some(bin), Some(sha)) => (bin.clone(), sha.clone()),
                _ => {
                    return Err(Failure::operational(
                        phase,
                        "con-leche binary unavailable in sysroot for --paranoid-quorum",
                    ));
                }
            }
        };
        self.run_ndjson_standalone_kernel(
            phase,
            StandaloneNdjsonKernel::ConLeche,
            bin_host,
            &expected_sha,
            (proof_ndjson_host, proof_ndjson_sha256),
        )
    }

    /// Run `lean4lean --import` (independent Lean 4 kernel implemented in Lean
    /// 4, bundled in Lean `v4.35.0+`) over `proof_ndjson_host` inside
    /// `ExecSeal` for `--paranoid-quorum`.
    pub(crate) fn run_ndjson_lean4lean(
        &mut self,
        proof_ndjson_host: &Path,
        proof_ndjson_sha256: &str,
    ) -> Result<(), Failure> {
        let phase = "ndjson-lean4lean";
        let (bin_host, expected_sha) = {
            let adm = self.admitted()?;
            let tools = adm.ndjson_tools.as_ref().ok_or_else(|| {
                Failure::operational(phase, "NDJSON comparator binaries unavailable in sysroot")
            })?;
            match (&tools.lean4lean, &tools.lean4lean_sha256) {
                (Some(bin), Some(sha)) => (bin.clone(), sha.clone()),
                _ => {
                    return Err(Failure::operational(
                        phase,
                        "lean4lean binary unavailable in sysroot for --paranoid-quorum",
                    ));
                }
            }
        };
        self.run_ndjson_standalone_kernel(
            phase,
            StandaloneNdjsonKernel::Lean4lean,
            bin_host,
            &expected_sha,
            (proof_ndjson_host, proof_ndjson_sha256),
        )
    }
}

/// A standalone NDJSON kernel run over `proof_full.ndjson` inside `ExecSeal`.
#[derive(Clone, Copy, Debug)]
enum StandaloneNdjsonKernel {
    ConRon,
    ConLeche,
    Lean4lean,
}

impl StandaloneNdjsonKernel {
    const fn label(self) -> &'static str {
        match self {
            Self::ConRon => "con-ron",
            Self::ConLeche => "con-leche",
            Self::Lean4lean => "lean4lean",
        }
    }

    /// Command-line arguments preceding the export path.
    ///
    /// `con-ron` and `con-leche` run in `--verified` mode with an explicitly
    /// capped `--jobs`: left unset, each starts one worker per hardware
    /// thread and reserves about 1 GiB of address space per worker, which
    /// exhausts an address-space limit on many-core hosts.
    fn args(self) -> Vec<String> {
        match self {
            Self::ConRon | Self::ConLeche => {
                let jobs = crate::toolchain::default_compile_workers(2);
                vec!["--verified".to_owned(), format!("--jobs={jobs}")]
            }
            Self::Lean4lean => vec!["--import".to_owned()],
        }
    }
}

fn parse_inspector_ok_typed<T: serde::de::DeserializeOwned>(
    mode: &str,
    resp_text: &str,
) -> Result<T, Failure> {
    let resp: InspectorOkTypedResponse<T> = serde_json::from_str(resp_text)
        .map_err(|_| Failure::new(2, mode, "unexpected inspector protocol response"))?;
    if !resp.ok {
        return Err(Failure::new(2, mode, "unexpected inspector protocol response"));
    }
    Ok(resp.result)
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

/// Materialize an already Door-1-validated in-memory inspector `.olean`
/// (`SpecPreflight.olean` or `TrustedBoundary.olean`) into `control_dir`
/// (`0o444`), emit `<stem>Entry.lean` (`0o444`), and re-lock `control_dir`
/// (`0o500`).
fn materialize_cached_inspector_olean(
    control_dir: &Path,
    stem: &str,
    bytes: &[u8],
    expected_sha: &str,
    mode: &str,
) -> Result<(PathBuf, String), Failure> {
    if !sha256_bytes(bytes).eq_ignore_ascii_case(expected_sha) {
        return Err(Failure::operational(
            mode,
            format!("in-memory precompiled {stem}.olean digest mismatch"),
        ));
    }
    set_mode(control_dir, 0o700)?;
    let written = (|| {
        let olean_dest = control_dir.join(format!("{stem}.olean"));
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
        let entry_dest = control_dir.join(format!("{stem}Entry.lean"));
        if fs::symlink_metadata(&entry_dest).is_ok() {
            let _ = fs::remove_file(&entry_dest);
        }
        fs::write(&entry_dest, format!("import {stem}\n")).map_err(|e| {
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

/// Promote a Door-1-validated `<stem>.olean` into `control_dir` (`0o444`), emit
/// `<stem>Entry.lean` (`0o444`), and unconditionally re-lock `control_dir` to
/// `0o500`.
fn promote_inspector_olean(
    control_dir: &Path,
    stem: &str,
    out_dir: &Path,
    mode: &str,
) -> Result<(PathBuf, String), Failure> {
    set_mode(control_dir, 0o700)?;
    let promoted = (|| {
        let olean_filename = format!("{stem}.olean");
        let olean_dest = control_dir.join(&olean_filename);
        if fs::symlink_metadata(&olean_dest).is_ok() {
            let _ = fs::remove_file(&olean_dest);
        }
        let sha = validate_and_promote_olean(out_dir, &olean_filename, &olean_dest)?;
        let entry_dest = control_dir.join(format!("{stem}Entry.lean"));
        if fs::symlink_metadata(&entry_dest).is_ok() {
            let _ = fs::remove_file(&entry_dest);
        }
        fs::write(&entry_dest, format!("import {stem}\n")).map_err(|e| {
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
            spec_preflight: None,
            spec_preflight_sha256: None,
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
            sysroot_manifest_sha256: None,
            inspector_olean: None,
            runtime_libs_verified: false,
            spec_preflight_olean: None,
            ndjson_tools: None,
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
            spec_preflight: None,
            spec_preflight_sha256: None,
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
            sysroot_manifest_sha256: None,
            inspector_olean: Some((olean.clone(), sha256_file(&olean, "test").unwrap())),
            runtime_libs_verified: false,
            spec_preflight_olean: None,
            ndjson_tools: None,
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

    #[test]
    fn pinned_admission_runs_version_and_prefix_inside_exec_seal() {
        let lean = crate::default_lean_path();
        if !lean.is_file() {
            return;
        }
        let anneal_root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .parent()
            .unwrap();

        // 1. Pinned admission under default ExecSeal probes and caches
        //    `sandbox_runtime` while running `--version` and `--print-prefix`
        //    inside the sandbox.
        let mut ok_checker = Checker::new(anneal_root, Some(&lean)).unwrap();
        let adm = ok_checker.tool_admission().unwrap().clone();
        assert!(!adm.unpinned);
        assert!(
            ok_checker.sandbox_runtime.is_some(),
            "pinned ExecSeal admission must probe and cache sandbox_runtime"
        );
        assert!(
            matches!(
                ok_checker.active_sandbox(),
                Some(ActiveSandbox::LinuxBwrap | ActiveSandbox::LinuxLandlockSeccomp)
            ),
            "expected sandboxed backend after pinned admission, got {:?}",
            ok_checker.active_sandbox()
        );

        // 2. A 1ns child timeout trips on the sandboxed `--version` query
        //    inside pinned admission (proving the query ran through
        //    `run_sandboxed_lean_query` rather than an unsandboxed host call).
        let mut timeout_checker = Checker::new(anneal_root, Some(&lean)).unwrap();
        timeout_checker.set_child_timeout(Duration::from_nanos(1));
        let err = timeout_checker
            .tool_admission()
            .expect_err("1ns query timeout must fail pinned admission inside ExecSeal");
        assert_eq!(err.phase, "sandbox-timeout", "{err}");
        assert!(
            matches!(
                timeout_checker.active_sandbox(),
                Some(ActiveSandbox::LinuxBwrap | ActiveSandbox::LinuxLandlockSeccomp)
            ),
            "expected probed active_sandbox after post-probe pinned query timeout"
        );
        assert!(timeout_checker.sandbox_runtime.is_none());
    }

    #[test]
    fn bundled_olean_cache_reuses_disk_artifacts_and_enforces_no_rebuild() {
        use std::os::unix::fs::PermissionsExt;

        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let root = base.join("bundle");
        let prefix = base.join("sysroot");
        let disk_cache = base.join("disk-cache");
        let log_file = base.join("lean-compile.log");
        fs::create_dir_all(prefix.join("lib/lean/Init")).unwrap();

        let inspector_src = root.join("trusted/audit/TrustedBoundary.lean");
        fs::create_dir_all(inspector_src.parent().unwrap()).unwrap();
        fs::write(&inspector_src, "-- synthetic inspector\n").unwrap();

        let lean = base.join("lean");
        fs::write(
            &lean,
            format!(
                r#"#!/bin/sh
case "$1" in
    --version) printf 'Lean 4.34.1\n'; exit ;;
    --print-prefix) printf '%s\n' '{}'; exit ;;
esac
out=""
while [ "$#" -gt 0 ]; do
    case "$1" in
        -o) out="$2"; shift 2 ;;
        *) shift ;;
    esac
done
if [ -n "$out" ]; then
    printf '%s\n' "$out" >> '{}'
    printf 'olean\0024.34.1\000synthetic' > "$out"
    exit 0
fi
exit 1
"#,
                prefix.display(),
                log_file.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();

        let mod_src = base.join("MirAst.lean");
        fs::write(&mod_src, "prelude\n").unwrap();
        let order = vec!["Trusted.MirAst".to_owned()];
        let sources = BTreeMap::from([("Trusted.MirAst".to_owned(), mod_src.clone())]);
        let imports = BTreeMap::from([("Trusted.MirAst".to_owned(), Vec::new())]);
        let is_module = BTreeMap::from([("Trusted.MirAst".to_owned(), false)]);

        // Cold run compiles both TrustedBoundary and Trusted.MirAst and populates disk cache.
        let mut c1 = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c1.set_allow_unpinned_lean(true);
        c1.set_sandbox_mode(SandboxMode::Unsandboxed);
        c1.set_olean_disk_cache_dir_for_test(Some(disk_cache.clone()));
        c1.tool_admission().unwrap();
        let _ = c1.ensure_inspector_compiled("headers", true, false).unwrap();
        c1.compile_lean_modules_parallel(
            &order, &sources, &imports, &is_module, "lib", false, false, 1,
        )
        .unwrap();
        let cold_lines: Vec<String> =
            fs::read_to_string(&log_file).unwrap().lines().map(str::to_owned).collect();
        assert_eq!(cold_lines.len(), 2, "expected 2 compiles on cold run: {cold_lines:?}");
        fs::write(&log_file, b"").unwrap();

        // Warm run with `--no-rebuild-bundled` hits disk cache with 0 Lean compile spawns.
        let mut c2 = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c2.set_allow_unpinned_lean(true);
        c2.set_sandbox_mode(SandboxMode::Unsandboxed);
        c2.set_olean_disk_cache_dir_for_test(Some(disk_cache.clone()));
        c2.set_no_rebuild_bundled(true);
        c2.tool_admission().unwrap();
        let _ = c2.ensure_inspector_compiled("headers", true, false).unwrap();
        c2.compile_lean_modules_parallel(
            &order, &sources, &imports, &is_module, "lib", false, false, 1,
        )
        .unwrap();
        assert_eq!(fs::read_to_string(&log_file).unwrap(), "", "warm run must not spawn lean");

        // Changing bundled module source invalidates key and fails closed under `--no-rebuild-bundled`.
        fs::write(&mod_src, "prelude\n-- modified\n").unwrap();
        let mut c3 = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c3.set_allow_unpinned_lean(true);
        c3.set_sandbox_mode(SandboxMode::Unsandboxed);
        c3.set_olean_disk_cache_dir_for_test(Some(disk_cache.clone()));
        c3.set_no_rebuild_bundled(true);
        c3.tool_admission().unwrap();
        let _ = c3.ensure_inspector_compiled("headers", true, false).unwrap();
        let err = c3
            .compile_lean_modules_parallel(
                &order, &sources, &imports, &is_module, "lib", false, false, 1,
            )
            .unwrap_err();
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("--no-rebuild-bundled"), "{err}");

        // `--no-cache` bypasses disk cache and compiles again.
        let mut c4 = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c4.set_allow_unpinned_lean(true);
        c4.set_sandbox_mode(SandboxMode::Unsandboxed);
        c4.set_olean_disk_cache_dir_for_test(Some(disk_cache));
        c4.set_use_olean_cache(false);
        c4.tool_admission().unwrap();
        let _ = c4.ensure_inspector_compiled("headers", true, false).unwrap();
        c4.compile_lean_modules_parallel(
            &order, &sources, &imports, &is_module, "lib", false, false, 1,
        )
        .unwrap();
        assert_eq!(
            fs::read_to_string(&log_file).unwrap().lines().count(),
            1,
            "--no-cache must compile Trusted.MirAst directly (in-memory inspector still cached)"
        );
    }

    #[test]
    fn build_lean_compile_args_disables_auto_implicit_only_when_requested() {
        let setup = Path::new("/work/in/Spec.setup.json");
        let out = Path::new("/work/out/Spec.olean");
        let src = Path::new("/work/in/Spec.lean");

        let spec_args = build_lean_compile_args(setup, out, src, 2048, false, true, true);
        assert!(spec_args.iter().any(|a| a == "-DautoImplicit=false"));
        assert!(spec_args.iter().any(|a| a == "-DrelaxedAutoImplicit=false"));

        let proof_args = build_lean_compile_args(setup, out, src, 2048, false, true, false);
        assert!(!proof_args.iter().any(|a| a.contains("autoImplicit")));
        assert!(!proof_args.iter().any(|a| a.contains("relaxedAutoImplicit")));
    }

    #[cfg(unix)]
    #[test]
    fn lean_stderr_panic_markers_fail_closed_even_at_exit_zero() {
        use std::os::unix::process::ExitStatusExt;

        let ok_status = std::process::ExitStatus::from_raw(0);
        for marker_line in [
            "PANIC at Lean.Elab.Foo Foo.lean:12:4: unexpected state",
            "INTERNAL PANIC: broken invariant",
            "PANIC: Promise.result!: empty",
            "lean_internal_panic_out_of_memory",
            "uncaught exception: internal exception #17",
            "internal exception: unknown binder",
            "internal exception foo",
        ] {
            let err = check_lean_output(
                "unit",
                Output {
                    status: ok_status,
                    stdout: b"{}".to_vec(),
                    stderr: format!("{marker_line}\n").into_bytes(),
                },
                true,
            )
            .expect_err("panic marker at exit 0 must fail closed");
            assert_eq!(err.code, 2, "{err}");
            assert!(err.message.contains("Lean runtime panic marker"), "{err}");
        }

        // Benign warnings or user identifiers mentioning "PANIC" without any
        // Lean runtime panic prefix must not trigger a false positive.
        let out = check_lean_output(
            "unit",
            Output {
                status: ok_status,
                stdout: b"ok\n".to_vec(),
                stderr: b"warning: unused declaration `PANIC_HANDLER`\ninfo: internal check\n"
                    .to_vec(),
            },
            false,
        )
        .expect("benign stderr diagnostic must pass");
        assert_eq!(out, "ok\n");
    }

    #[cfg(unix)]
    #[test]
    fn run_lean_script_fails_closed_when_exit_zero_emits_panic_stderr() {
        let dir = tempfile::tempdir().unwrap();
        let root = fs::canonicalize(dir.path()).unwrap();
        let inspector = root.join("trusted/audit/TrustedBoundary.lean");
        fs::create_dir_all(inspector.parent().unwrap()).unwrap();
        fs::write(&inspector, "-- stub\n").unwrap();

        let mut checker = shell_checker(&root);
        let err = checker
            .process(
                "probe",
                &[
                    "-c".to_owned(),
                    "printf 'PANIC at Fake.Mod Fake.lean:1:1: simulated VM panic\\n' >&2; \
                     printf 'ok\\n'; exit 0"
                        .to_owned(),
                ],
            )
            .expect_err("zero exit with panic stderr must fail closed");
        assert_eq!(err.code, 2, "{err}");
        assert!(err.message.contains("Lean runtime panic marker"), "{err}");
    }

    #[test]
    fn bundled_olean_cache_invalidates_downstream_through_unchanged_barrel() {
        use std::os::unix::fs::PermissionsExt;

        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let root = base.join("bundle");
        let prefix = base.join("sysroot");
        let disk_cache = base.join("disk-cache");
        let log_file = base.join("lean-compile.log");
        fs::create_dir_all(prefix.join("lib/lean/Init")).unwrap();

        let inspector_src = root.join("trusted/audit/TrustedBoundary.lean");
        fs::create_dir_all(inspector_src.parent().unwrap()).unwrap();
        fs::write(&inspector_src, "-- synthetic inspector\n").unwrap();

        let lean = base.join("lean");
        fs::write(
            &lean,
            format!(
                r#"#!/bin/sh
case "$1" in
    --version) printf 'Lean 4.34.1\n'; exit ;;
    --print-prefix) printf '%s\n' '{}'; exit ;;
esac
out=""
src=""
while [ "$#" -gt 0 ]; do
    case "$1" in
        -o) out="$2"; shift 2 ;;
        *) src="$1"; shift ;;
    esac
done
if [ -n "$out" ]; then
    printf '%s\n' "$out" >> '{}'
    case "$out" in
        */Leaf.olean)
            printf 'olean\0024.34.1\000' > "$out"
            cat "$src" >> "$out"
            ;;
        *)
            printf 'olean\0024.34.1\000constant-payload' > "$out"
            ;;
    esac
    exit 0
fi
exit 1
"#,
                prefix.display(),
                log_file.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();

        let leaf_src = base.join("Leaf.lean");
        let barrel_src = base.join("Barrel.lean");
        let downstream_src = base.join("Downstream.lean");
        fs::write(&leaf_src, "prelude\n-- leaf v1\n").unwrap();
        fs::write(&barrel_src, "prelude\nimport Trusted.Leaf\n").unwrap();
        fs::write(&downstream_src, "prelude\nimport Trusted.Barrel\n").unwrap();

        let edge = |m: &str| ImportEdge {
            module: m.to_owned(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        };
        let order_prefix = vec!["Trusted.Leaf".to_owned(), "Trusted.Barrel".to_owned()];
        let order_all = vec![
            "Trusted.Leaf".to_owned(),
            "Trusted.Barrel".to_owned(),
            "Anneal.Downstream".to_owned(),
        ];
        let sources = BTreeMap::from([
            ("Trusted.Leaf".to_owned(), leaf_src.clone()),
            ("Trusted.Barrel".to_owned(), barrel_src),
            ("Anneal.Downstream".to_owned(), downstream_src),
        ]);
        let imports = BTreeMap::from([
            ("Trusted.Leaf".to_owned(), Vec::new()),
            ("Trusted.Barrel".to_owned(), vec![edge("Trusted.Leaf")]),
            ("Anneal.Downstream".to_owned(), vec![edge("Trusted.Barrel")]),
        ]);
        let is_module = BTreeMap::from([
            ("Trusted.Leaf".to_owned(), false),
            ("Trusted.Barrel".to_owned(), false),
            ("Anneal.Downstream".to_owned(), false),
        ]);

        // 1. Cold run populates Leaf(v1), Barrel, and Downstream(v1).
        let mut c1 = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c1.set_allow_unpinned_lean(true);
        c1.set_sandbox_mode(SandboxMode::Unsandboxed);
        c1.set_olean_disk_cache_dir_for_test(Some(disk_cache.clone()));
        c1.tool_admission().unwrap();
        let _ = c1.ensure_inspector_compiled("headers", true, false).unwrap();
        c1.compile_lean_modules_parallel(
            &order_all, &sources, &imports, &is_module, "lib", false, false, 1,
        )
        .unwrap();
        assert_eq!(fs::read_to_string(&log_file).unwrap().lines().count(), 4);
        fs::write(&log_file, b"").unwrap();

        // 2. Edit Leaf(v2); Barrel and Downstream sources and `Barrel.olean`
        // bytes stay identical.
        fs::write(&leaf_src, "prelude\n-- leaf v2\n").unwrap();
        let mut c2 = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c2.set_allow_unpinned_lean(true);
        c2.set_sandbox_mode(SandboxMode::Unsandboxed);
        c2.set_olean_disk_cache_dir_for_test(Some(disk_cache.clone()));
        c2.tool_admission().unwrap();
        let _ = c2.ensure_inspector_compiled("headers", true, false).unwrap();
        c2.compile_lean_modules_parallel(
            &order_prefix,
            &sources,
            &imports,
            &is_module,
            "lib",
            false,
            false,
            1,
        )
        .unwrap();
        assert_eq!(fs::read_to_string(&log_file).unwrap().lines().count(), 2);
        fs::write(&log_file, b"").unwrap();

        // 3. Downstream MUST miss cache under `--no-rebuild-bundled` even
        // though both Downstream.lean and Barrel.olean bytes did not change.
        let mut c3 = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c3.set_allow_unpinned_lean(true);
        c3.set_sandbox_mode(SandboxMode::Unsandboxed);
        c3.set_olean_disk_cache_dir_for_test(Some(disk_cache.clone()));
        c3.set_no_rebuild_bundled(true);
        c3.tool_admission().unwrap();
        let _ = c3.ensure_inspector_compiled("headers", true, false).unwrap();
        let err = c3
            .compile_lean_modules_parallel(
                &order_all, &sources, &imports, &is_module, "lib", false, false, 1,
            )
            .unwrap_err();
        assert_eq!(err.phase, "olean-cache");
        assert!(err.message.contains("Anneal.Downstream"), "{err}");
        assert!(err.message.contains("--no-rebuild-bundled"), "{err}");
        assert_eq!(fs::read_to_string(&log_file).unwrap(), "");

        // 4. Rebuilding populates only Downstream (Leaf and Barrel hit cache).
        let mut c4 = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c4.set_allow_unpinned_lean(true);
        c4.set_sandbox_mode(SandboxMode::Unsandboxed);
        c4.set_olean_disk_cache_dir_for_test(Some(disk_cache.clone()));
        c4.tool_admission().unwrap();
        let _ = c4.ensure_inspector_compiled("headers", true, false).unwrap();
        c4.compile_lean_modules_parallel(
            &order_all, &sources, &imports, &is_module, "lib", false, false, 1,
        )
        .unwrap();
        let rebuilt: Vec<String> =
            fs::read_to_string(&log_file).unwrap().lines().map(str::to_owned).collect();
        assert_eq!(rebuilt.len(), 1, "expected only Downstream rebuild: {rebuilt:?}");
        assert!(rebuilt[0].ends_with("Anneal/Downstream.olean"), "{rebuilt:?}");
        fs::write(&log_file, b"").unwrap();

        // 5. Subsequent `--no-rebuild-bundled` run hits all three cleanly.
        let mut c5 = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c5.set_allow_unpinned_lean(true);
        c5.set_sandbox_mode(SandboxMode::Unsandboxed);
        c5.set_olean_disk_cache_dir_for_test(Some(disk_cache.clone()));
        c5.set_no_rebuild_bundled(true);
        c5.tool_admission().unwrap();
        let _ = c5.ensure_inspector_compiled("headers", true, false).unwrap();
        c5.compile_lean_modules_parallel(
            &order_all, &sources, &imports, &is_module, "lib", false, false, 1,
        )
        .unwrap();
        assert_eq!(fs::read_to_string(&log_file).unwrap(), "");
    }

    #[test]
    fn write_setup_json_strips_private_oleans_for_module_without_import_all() {
        use std::collections::{BTreeMap, BTreeSet};

        use crate::toolchain::{AdmittedToolchain, ImportEdge, ModuleArtifacts};

        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().to_path_buf();
        let mut graph = BTreeMap::new();
        graph.insert("Init.Core".to_owned(), Vec::new());
        graph.insert(
            "Model".to_owned(),
            vec![ImportEdge {
                module: "Init.Core".to_owned(),
                is_exported: true,
                import_all: false,
                is_meta: false,
            }],
        );
        let mut artifacts = BTreeMap::new();
        artifacts.insert(
            "Init.Core".to_owned(),
            ModuleArtifacts {
                olean_parts: vec![
                    "/sys/Init/Core.olean".to_owned(),
                    "/sys/Init/Core.olean.server".to_owned(),
                    "/sys/Init/Core.olean.private".to_owned(),
                ],
                ir_parts: vec!["/sys/Init/Core.ir".to_owned()],
            },
        );
        artifacts.insert(
            "Model".to_owned(),
            ModuleArtifacts {
                olean_parts: vec![
                    "/lib/Model.olean".to_owned(),
                    "/lib/Model.olean.server".to_owned(),
                    "/lib/Model.olean.private".to_owned(),
                ],
                ir_parts: Vec::new(),
            },
        );
        let adm = AdmittedToolchain {
            inspector: root.join("TrustedBoundary.lean"),
            inspector_sha256: String::new(),
            lean_sha256: String::new(),
            version: "4.34.1".to_owned(),
            prefix: root.clone(),
            axioms: Vec::new(),
            foundation_graph: BTreeMap::new(),
            graph,
            artifacts,
            library_lock: None,
            library_modules: BTreeSet::new(),
            unpinned: true,
            sysroot_package_roots: BTreeSet::new(),
            unpinned_records: BTreeMap::new(),
            lean_binary_sha256: None,
            exec_lean: root.join("lean"),
            expected_lean_sha: None,
            sysroot_manifest_sha256: None,
            inspector_olean: None,
            runtime_libs_verified: false,
            ndjson_tools: None,
            spec_preflight: None,
            spec_preflight_sha256: None,
            spec_preflight_olean: None,
        };

        let std_import = vec![ImportEdge {
            module: "Model".to_owned(),
            is_exported: true,
            import_all: false,
            is_meta: false,
        }];
        let mod_setup = root.join("mod.setup.json");
        write_setup_json_to_path(&mod_setup, &adm, "Spec", &std_import, true, None).unwrap();
        let mod_json: Json = serde_json::from_slice(&fs::read(&mod_setup).unwrap()).unwrap();
        assert_eq!(mod_json["isModule"], true);
        let init_oleans = mod_json["importArts"]["Init.Core"][0].as_array().unwrap();
        assert_eq!(
            init_oleans,
            &vec![Json::from("/sys/Init/Core.olean"), Json::from("/sys/Init/Core.olean.server"),]
        );
        assert_eq!(
            mod_json["importArts"]["Init.Core"][1].as_array().unwrap(),
            &vec![Json::from("/sys/Init/Core.ir")]
        );
        assert_eq!(
            mod_json["importArts"]["Model"][0].as_array().unwrap(),
            &vec![Json::from("/lib/Model.olean"), Json::from("/lib/Model.olean.server")]
        );

        let import_all_edge = vec![ImportEdge {
            module: "Model".to_owned(),
            is_exported: false,
            import_all: true,
            is_meta: false,
        }];
        let all_setup = root.join("import_all.setup.json");
        write_setup_json_to_path(&all_setup, &adm, "Anneal.Bit", &import_all_edge, true, None)
            .unwrap();
        let all_json: Json = serde_json::from_slice(&fs::read(&all_setup).unwrap()).unwrap();
        assert_eq!(
            all_json["importArts"]["Model"][0].as_array().unwrap(),
            &vec![
                Json::from("/lib/Model.olean"),
                Json::from("/lib/Model.olean.server"),
                Json::from("/lib/Model.olean.private"),
            ]
        );

        let nonmod_setup = root.join("nonmod.setup.json");
        write_setup_json_to_path(&nonmod_setup, &adm, "Legacy", &std_import, false, None).unwrap();
        let nonmod_json: Json = serde_json::from_slice(&fs::read(&nonmod_setup).unwrap()).unwrap();
        assert_eq!(nonmod_json["isModule"], false);
        assert_eq!(
            nonmod_json["importArts"]["Model"][0].as_array().unwrap(),
            &vec![
                Json::from("/lib/Model.olean"),
                Json::from("/lib/Model.olean.server"),
                Json::from("/lib/Model.olean.private"),
            ]
        );
    }

    #[test]
    fn source_starts_with_module_keyword_handles_adjacent_comments_and_identifiers() {
        assert!(source_starts_with_module_keyword(b"module\nprelude\n"));
        assert!(source_starts_with_module_keyword(b"module"));
        assert!(source_starts_with_module_keyword(
            b"-- line\n/- nested /- block -/ -/\nmodule--comment\nprelude\n"
        ));
        assert!(source_starts_with_module_keyword(b"module/-block-/\nprelude\n"));
        assert!(!source_starts_with_module_keyword(b"modulefoo\nprelude\n"));
        assert!(!source_starts_with_module_keyword(b"module_1\nprelude\n"));
        assert!(!source_starts_with_module_keyword(b"prelude\nmodule\n"));
    }

    fn create_synthetic_sysroot(prefix: &Path) {
        use std::os::unix::fs::PermissionsExt;

        fs::create_dir_all(prefix.join("bin")).unwrap();
        let lean = prefix.join("bin/lean");
        fs::write(&lean, b"#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();

        fs::create_dir_all(prefix.join("lib/lean/Init")).unwrap();
        fs::write(prefix.join("lib/libInit_shared.so"), b"so").unwrap();
        fs::write(prefix.join("lib/lean/Init.olean"), b"init").unwrap();
        fs::write(prefix.join("lib/lean/Init/Prelude.olean"), b"prelude").unwrap();
        fs::write(prefix.join("lib/lean/Std.ir"), b"ir").unwrap();
    }

    fn symlink_tree_files(src_dir: &Path, dst_dir: &Path) {
        use std::os::unix::fs::symlink;

        for entry in walkdir::WalkDir::new(src_dir).follow_links(false) {
            let entry = entry.unwrap();
            let rel = entry.path().strip_prefix(src_dir).unwrap();
            let dst = dst_dir.join(rel);
            if entry.file_type().is_dir() {
                fs::create_dir_all(&dst).unwrap();
            } else {
                let target = fs::canonicalize(entry.path()).unwrap();
                symlink(target, dst).unwrap();
            }
        }
    }

    fn copy_tree_deref_no_symlinks(src_dir: &Path, dst_dir: &Path) {
        for entry in walkdir::WalkDir::new(src_dir).follow_links(false) {
            let entry = entry.unwrap();
            let rel = entry.path().strip_prefix(src_dir).unwrap();
            let dst = dst_dir.join(rel);
            if entry.file_type().is_dir() {
                fs::create_dir_all(&dst).unwrap();
            } else {
                let target = fs::canonicalize(entry.path()).unwrap();
                fs::hard_link(&target, &dst)
                    .or_else(|_| fs::copy(&target, &dst).map(|_| ()))
                    .unwrap();
            }
        }
    }

    #[test]
    fn unpinned_static_toolchain_handles_runfiles_symlinks_escapes_loops_and_zero_symlink_dirs() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let canon_prefix = base.join("canon-sysroot");
        create_synthetic_sysroot(&canon_prefix);
        let canon_exec_lean = fs::canonicalize(canon_prefix.join("bin/lean")).unwrap();

        // 1. Bazel-runfiles per-file symlink forest under `lib/` resolves to
        //    `canon_prefix`.
        let runfiles = base.join("bazel-runfiles");
        fs::create_dir_all(runfiles.join("bin")).unwrap();
        symlink(&canon_exec_lean, runfiles.join("bin/lean")).unwrap();
        symlink_tree_files(&canon_prefix.join("lib"), &runfiles.join("lib"));
        let (resolved_prefix, resolved_exec) =
            resolve_unpinned_static_toolchain(&runfiles.join("bin/lean")).unwrap();
        assert_eq!(resolved_prefix, canon_prefix);
        assert_eq!(resolved_exec, canon_exec_lean);

        // 2. Direct `lib/lean` directory symlink (and top-level `lib` symlink)
        //    pointing inside `canon_prefix/lib` both resolve to `canon_prefix`.
        let lib_lean_sym = base.join("lib-lean-sym");
        fs::create_dir_all(lib_lean_sym.join("bin")).unwrap();
        fs::create_dir_all(lib_lean_sym.join("lib")).unwrap();
        symlink(&canon_exec_lean, lib_lean_sym.join("bin/lean")).unwrap();
        symlink(canon_prefix.join("lib/lean"), lib_lean_sym.join("lib/lean")).unwrap();
        symlink(
            canon_prefix.join("lib/libInit_shared.so"),
            lib_lean_sym.join("lib/libInit_shared.so"),
        )
        .unwrap();
        assert_eq!(
            resolve_unpinned_static_toolchain(&lib_lean_sym.join("bin/lean")).unwrap(),
            (canon_prefix.clone(), canon_exec_lean.clone())
        );

        let top_lib_sym = base.join("top-lib-sym");
        fs::create_dir_all(top_lib_sym.join("bin")).unwrap();
        symlink(&canon_exec_lean, top_lib_sym.join("bin/lean")).unwrap();
        symlink(canon_prefix.join("lib"), top_lib_sym.join("lib")).unwrap();
        assert_eq!(
            resolve_unpinned_static_toolchain(&top_lib_sym.join("bin/lean")).unwrap(),
            (canon_prefix.clone(), canon_exec_lean.clone())
        );

        // 3. Zero-symlink logical `lib/` directory behaves identically to
        //    `resolve_static_toolchain` (preserves `zero_sym` prefix).
        let zero_sym = base.join("zero-symlink");
        fs::create_dir_all(zero_sym.join("bin")).unwrap();
        symlink(&canon_exec_lean, zero_sym.join("bin/lean")).unwrap();
        copy_tree_deref_no_symlinks(&canon_prefix.join("lib"), &zero_sym.join("lib"));
        assert_eq!(
            resolve_unpinned_static_toolchain(&zero_sym.join("bin/lean")).unwrap(),
            resolve_static_toolchain(&zero_sym.join("bin/lean")).unwrap()
        );
        assert_eq!(
            resolve_unpinned_static_toolchain(&zero_sym.join("bin/lean")).unwrap().0,
            zero_sym
        );

        // 4. Copied `lib/` preserving an internal relative symlink inside
        //    `logical_lib` keeps the logical prefix.
        let internal_sym = base.join("internal-sym");
        fs::create_dir_all(internal_sym.join("bin")).unwrap();
        symlink(&canon_exec_lean, internal_sym.join("bin/lean")).unwrap();
        copy_tree_deref_no_symlinks(&canon_prefix.join("lib"), &internal_sym.join("lib"));
        fs::write(internal_sym.join("lib/libLLVM.so.22.1"), b"llvm").unwrap();
        symlink("libLLVM.so.22.1", internal_sym.join("lib/libLLVM.so")).unwrap();
        assert_eq!(
            resolve_unpinned_static_toolchain(&internal_sym.join("bin/lean")).unwrap().0,
            internal_sym
        );

        // 5. Escaping symlink, broken symlink, symlink loop, mixed regular
        //    file, and symlinked `lib -> other_dir` must never promote to
        //    `canon_prefix` (preserving `logical_prefix` so `SandboxRuntime`
        //    rejects invalid/escaping trees fail-closed).
        let outside_file = base.join("outside.olean");
        fs::write(&outside_file, b"outside").unwrap();

        let escape = base.join("escape");
        fs::create_dir_all(escape.join("bin")).unwrap();
        symlink(&canon_exec_lean, escape.join("bin/lean")).unwrap();
        symlink_tree_files(&canon_prefix.join("lib"), &escape.join("lib"));
        symlink(&outside_file, escape.join("lib/lean/Escape.olean")).unwrap();
        assert_eq!(resolve_unpinned_static_toolchain(&escape.join("bin/lean")).unwrap().0, escape);
        let escape_err = SandboxRuntime::probe(
            SandboxMode::PreferBwrapOrLandlock,
            &canon_exec_lean,
            &escape,
            &base.join("stage-escape"),
        )
        .unwrap_err();
        #[cfg(target_os = "linux")]
        {
            assert_eq!(
                (escape_err.code, escape_err.phase.as_str()),
                (2, "sandbox"),
                "{escape_err}"
            );
            assert!(escape_err.message.contains("refusing escaping symlink"), "{escape_err}");
        }
        let _ = escape_err;

        let broken = base.join("broken");
        fs::create_dir_all(broken.join("bin")).unwrap();
        symlink(&canon_exec_lean, broken.join("bin/lean")).unwrap();
        symlink_tree_files(&canon_prefix.join("lib"), &broken.join("lib"));
        symlink(base.join("does-not-exist"), broken.join("lib/lean/Broken.olean")).unwrap();
        assert_eq!(resolve_unpinned_static_toolchain(&broken.join("bin/lean")).unwrap().0, broken);
        let broken_err = SandboxRuntime::probe(
            SandboxMode::PreferBwrapOrLandlock,
            &canon_exec_lean,
            &broken,
            &base.join("stage-broken"),
        )
        .unwrap_err();
        #[cfg(target_os = "linux")]
        {
            assert_eq!(
                (broken_err.code, broken_err.phase.as_str()),
                (2, "sandbox"),
                "{broken_err}"
            );
            assert!(
                broken_err.message.contains("cannot canonicalize toolchain symlink")
                    || broken_err.message.contains("refusing escaping symlink"),
                "{broken_err}"
            );
        }
        let _ = broken_err;

        let looped = base.join("looped");
        fs::create_dir_all(looped.join("bin")).unwrap();
        symlink(&canon_exec_lean, looped.join("bin/lean")).unwrap();
        symlink_tree_files(&canon_prefix.join("lib"), &looped.join("lib"));
        symlink("LoopA.olean", looped.join("lib/lean/LoopB.olean")).unwrap();
        symlink("LoopB.olean", looped.join("lib/lean/LoopA.olean")).unwrap();
        symlink("..", looped.join("lib/lean/DirLoop")).unwrap();
        assert_eq!(resolve_unpinned_static_toolchain(&looped.join("bin/lean")).unwrap().0, looped);
        let looped_err = SandboxRuntime::probe(
            SandboxMode::PreferBwrapOrLandlock,
            &canon_exec_lean,
            &looped,
            &base.join("stage-looped"),
        )
        .unwrap_err();
        #[cfg(target_os = "linux")]
        {
            assert_eq!(
                (looped_err.code, looped_err.phase.as_str()),
                (2, "sandbox"),
                "{looped_err}"
            );
            assert!(
                looped_err.message.contains("cannot canonicalize toolchain symlink")
                    || looped_err.message.contains("refusing escaping symlink"),
                "{looped_err}"
            );
        }
        let _ = looped_err;

        let mixed = base.join("mixed");
        fs::create_dir_all(mixed.join("bin")).unwrap();
        symlink(&canon_exec_lean, mixed.join("bin/lean")).unwrap();
        symlink_tree_files(&canon_prefix.join("lib"), &mixed.join("lib"));
        fs::write(mixed.join("lib/lean/Tampered.olean"), b"regular").unwrap();
        assert_eq!(resolve_unpinned_static_toolchain(&mixed.join("bin/lean")).unwrap().0, mixed);
        let mixed_err = SandboxRuntime::probe(
            SandboxMode::PreferBwrapOrLandlock,
            &canon_exec_lean,
            &mixed,
            &base.join("stage-mixed"),
        )
        .unwrap_err();
        #[cfg(target_os = "linux")]
        {
            assert_eq!((mixed_err.code, mixed_err.phase.as_str()), (2, "sandbox"), "{mixed_err}");
            assert!(mixed_err.message.contains("refusing escaping symlink"), "{mixed_err}");
        }
        let _ = mixed_err;

        let self_dir = base.join("self-dir");
        fs::create_dir_all(self_dir.join("bin")).unwrap();
        symlink(&canon_exec_lean, self_dir.join("bin/lean")).unwrap();
        symlink_tree_files(&canon_prefix.join("lib"), &self_dir.join("lib"));
        symlink(canon_prefix.join("lib"), self_dir.join("lib/self")).unwrap();
        assert_eq!(
            resolve_unpinned_static_toolchain(&self_dir.join("bin/lean")).unwrap().0,
            self_dir
        );

        let alt_lib_target = base.join("alt-lib-target");
        symlink_tree_files(&canon_prefix.join("lib"), &alt_lib_target);
        let alt_lib = base.join("alt-lib");
        fs::create_dir_all(alt_lib.join("bin")).unwrap();
        symlink(&canon_exec_lean, alt_lib.join("bin/lean")).unwrap();
        symlink(&alt_lib_target, alt_lib.join("lib")).unwrap();
        assert_eq!(
            resolve_unpinned_static_toolchain(&alt_lib.join("bin/lean")).unwrap().0,
            alt_lib
        );
        // Also ensure non-executable logical lean still fails closed.
        let nonexec = base.join("nonexec");
        fs::create_dir_all(nonexec.join("bin")).unwrap();
        fs::write(nonexec.join("bin/lean"), b"not-exec").unwrap();
        fs::set_permissions(nonexec.join("bin/lean"), fs::Permissions::from_mode(0o644)).unwrap();
        assert!(resolve_unpinned_static_toolchain(&nonexec.join("bin/lean")).is_err());
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn unpinned_bazel_runfiles_admission_and_fail_closed_symlink_guards_end_to_end() {
        use std::os::unix::fs::symlink;

        let real_lean_raw = crate::default_lean_path();
        if !real_lean_raw.is_file() {
            return;
        }
        let real_lean = fs::canonicalize(&real_lean_raw).unwrap();
        let real_prefix = real_lean.parent().unwrap().parent().unwrap().to_path_buf();
        let real_lean_sha = sha256_file_deref(&real_lean, "test").unwrap();
        let anneal_root = Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap();

        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();

        // 1. Bazel-runfiles `bin/lean` + `lib/**` symlinks inside `real_prefix`
        //    pass unpinned `ExecSeal` admission (pre-probe SHA, sandbox probe,
        //    and sysroot root/manifest hashing bind `real_prefix`).
        let runfiles = base.join("runfiles-ok");
        fs::create_dir_all(runfiles.join("bin")).unwrap();
        symlink(&real_lean, runfiles.join("bin/lean")).unwrap();
        symlink_tree_files(&real_prefix.join("lib"), &runfiles.join("lib"));

        let mut ok_checker = Checker::new(anneal_root, Some(&runfiles.join("bin/lean"))).unwrap();
        ok_checker.set_allow_unpinned_lean(true);
        let adm = ok_checker.tool_admission().unwrap().clone();
        assert!(adm.unpinned);
        assert_eq!(adm.prefix, real_prefix);
        assert_eq!(adm.exec_lean, real_lean);
        assert_eq!(adm.lean_binary_sha256.as_deref(), Some(real_lean_sha.as_str()));
        assert!(adm.sysroot_package_roots.contains("Init"));
        assert!(
            matches!(
                ok_checker.active_sandbox(),
                Some(ActiveSandbox::LinuxBwrap | ActiveSandbox::LinuxLandlockSeccomp)
            ),
            "expected ExecSeal backend, got {:?}",
            ok_checker.active_sandbox()
        );
        let manifest_sha = ok_checker.ensure_sysroot_manifest_sha256().unwrap();
        assert_eq!(manifest_sha.len(), 64);
        ok_checker.admit_unpinned_sysroot(["Init.Prelude".to_string()]).unwrap();
        assert!(ok_checker.admitted().unwrap().unpinned_records.contains_key("Init.Prelude"));

        // Pinned mode on the same Bazel-runfiles symlink tree must still reject
        // symlinks rather than dereferencing them.
        let mut pinned_checker =
            Checker::new(anneal_root, Some(&runfiles.join("bin/lean"))).unwrap();
        let pinned_err = pinned_checker.tool_admission().unwrap_err();
        assert!(!pinned_checker.execution_began(), "{pinned_err}");

        // 2. Direct `lib/lean -> real_prefix/lib/lean` symlink with symlinked
        //    sibling runtime libs also succeeds under unpinned `ExecSeal`.
        let lib_lean_sym = base.join("runfiles-lib-lean-sym");
        fs::create_dir_all(lib_lean_sym.join("bin")).unwrap();
        fs::create_dir_all(lib_lean_sym.join("lib")).unwrap();
        symlink(&real_lean, lib_lean_sym.join("bin/lean")).unwrap();
        for entry in fs::read_dir(real_prefix.join("lib")).unwrap() {
            let entry = entry.unwrap();
            let dst = lib_lean_sym.join("lib").join(entry.file_name());
            if entry.file_name() == OsStr::new("lean") {
                symlink(real_prefix.join("lib/lean"), dst).unwrap();
            } else if entry.file_type().unwrap().is_dir() {
                symlink_tree_files(&entry.path(), &dst);
            } else {
                symlink(fs::canonicalize(entry.path()).unwrap(), dst).unwrap();
            }
        }
        let mut dir_sym_checker =
            Checker::new(anneal_root, Some(&lib_lean_sym.join("bin/lean"))).unwrap();
        dir_sym_checker.set_allow_unpinned_lean(true);
        let dir_sym_adm = dir_sym_checker.tool_admission().unwrap();
        assert_eq!(dir_sym_adm.prefix, real_prefix);
        assert_eq!(dir_sym_adm.exec_lean, real_lean);

        // 3. Escaping symlink outside `canon_lib` stays fail-closed before any
        //    probe executes.
        let outside_olean = base.join("outside.olean");
        fs::write(&outside_olean, b"outside").unwrap();
        let escape_rf = base.join("runfiles-escape");
        fs::create_dir_all(escape_rf.join("bin")).unwrap();
        symlink(&real_lean, escape_rf.join("bin/lean")).unwrap();
        symlink_tree_files(&real_prefix.join("lib"), &escape_rf.join("lib"));
        symlink(&outside_olean, escape_rf.join("lib/lean/Escape.olean")).unwrap();
        let mut escape_checker =
            Checker::new(anneal_root, Some(&escape_rf.join("bin/lean"))).unwrap();
        escape_checker.set_allow_unpinned_lean(true);
        let escape_err = escape_checker.tool_admission().unwrap_err();
        assert_eq!((escape_err.code, escape_err.phase.as_str()), (2, "sandbox"), "{escape_err}");
        assert!(escape_err.message.contains("refusing escaping symlink"), "{escape_err}");
        assert!(!escape_checker.execution_began());

        // 4. Broken symlink inside `logical_lib` stays fail-closed.
        let broken_rf = base.join("runfiles-broken");
        fs::create_dir_all(broken_rf.join("bin")).unwrap();
        symlink(&real_lean, broken_rf.join("bin/lean")).unwrap();
        symlink_tree_files(&real_prefix.join("lib"), &broken_rf.join("lib"));
        symlink(base.join("missing.olean"), broken_rf.join("lib/lean/Broken.olean")).unwrap();
        let mut broken_checker =
            Checker::new(anneal_root, Some(&broken_rf.join("bin/lean"))).unwrap();
        broken_checker.set_allow_unpinned_lean(true);
        let broken_err = broken_checker.tool_admission().unwrap_err();
        assert_eq!((broken_err.code, broken_err.phase.as_str()), (2, "sandbox"), "{broken_err}");
        assert!(
            broken_err.message.contains("cannot canonicalize toolchain symlink")
                || broken_err.message.contains("refusing escaping symlink"),
            "{broken_err}"
        );
        assert!(!broken_checker.execution_began());

        // 4b. Symlink loop inside `logical_lib` stays fail-closed.
        let loop_rf = base.join("runfiles-loop");
        fs::create_dir_all(loop_rf.join("bin")).unwrap();
        symlink(&real_lean, loop_rf.join("bin/lean")).unwrap();
        symlink_tree_files(&real_prefix.join("lib"), &loop_rf.join("lib"));
        symlink("LoopA.olean", loop_rf.join("lib/lean/LoopB.olean")).unwrap();
        symlink("LoopB.olean", loop_rf.join("lib/lean/LoopA.olean")).unwrap();
        let mut loop_checker = Checker::new(anneal_root, Some(&loop_rf.join("bin/lean"))).unwrap();
        loop_checker.set_allow_unpinned_lean(true);
        let loop_err = loop_checker.tool_admission().unwrap_err();
        assert_eq!((loop_err.code, loop_err.phase.as_str()), (2, "sandbox"), "{loop_err}");
        assert!(
            loop_err.message.contains("cannot canonicalize toolchain symlink")
                || loop_err.message.contains("refusing escaping symlink"),
            "{loop_err}"
        );
        assert!(!loop_checker.execution_began());

        // 5. Zero-symlink logical `lib/` keeps `zero_sym` prefix (copied
        //    `bin/lean` lets Tier-2 Landlock resolve `$ORIGIN/../lib`;
        //    Tier-1 `bwrap` also exercises symlinked `bin/lean`), and
        //    broken or looping symlinks trigger `cannot canonicalize`.
        let zero_sym = base.join("zero-sym-live");
        fs::create_dir_all(zero_sym.join("bin")).unwrap();
        fs::copy(&real_lean, zero_sym.join("bin/lean")).unwrap();
        copy_tree_deref_no_symlinks(&real_prefix.join("lib"), &zero_sym.join("lib"));
        let mut zero_checker = Checker::new(anneal_root, Some(&zero_sym.join("bin/lean"))).unwrap();
        zero_checker.set_allow_unpinned_lean(true);
        let zero_adm = zero_checker.tool_admission().unwrap().clone();
        assert_eq!(zero_adm.prefix, zero_sym);
        assert_eq!(zero_adm.exec_lean, zero_sym.join("bin/lean"));

        if matches!(ok_checker.active_sandbox(), Some(ActiveSandbox::LinuxBwrap)) {
            let zero_bin = zero_sym.join("bin/lean");
            fs::remove_file(&zero_bin).unwrap();
            symlink(&real_lean, &zero_bin).unwrap();
            let mut zero_sym_bin_checker = Checker::new(anneal_root, Some(&zero_bin)).unwrap();
            zero_sym_bin_checker.set_allow_unpinned_lean(true);
            let zero_sym_bin_adm = zero_sym_bin_checker.tool_admission().unwrap();
            assert_eq!(zero_sym_bin_adm.prefix, zero_sym);
            assert_eq!(zero_sym_bin_adm.exec_lean, real_lean);
        }

        let zero_broken = zero_sym.join("lib/lean/Broken.olean");
        symlink(base.join("missing.olean"), &zero_broken).unwrap();
        let mut zero_broken_checker =
            Checker::new(anneal_root, Some(&zero_sym.join("bin/lean"))).unwrap();
        zero_broken_checker.set_allow_unpinned_lean(true);
        let zero_broken_err = zero_broken_checker.tool_admission().unwrap_err();
        assert!(
            zero_broken_err.message.contains("cannot canonicalize toolchain symlink"),
            "{zero_broken_err}"
        );
        assert!(!zero_broken_checker.execution_began());
        fs::remove_file(&zero_broken).unwrap();

        symlink("LoopA.olean", zero_sym.join("lib/lean/LoopB.olean")).unwrap();
        symlink("LoopB.olean", zero_sym.join("lib/lean/LoopA.olean")).unwrap();
        let mut zero_loop_checker =
            Checker::new(anneal_root, Some(&zero_sym.join("bin/lean"))).unwrap();
        zero_loop_checker.set_allow_unpinned_lean(true);
        let zero_loop_err = zero_loop_checker.tool_admission().unwrap_err();
        assert!(
            zero_loop_err.message.contains("cannot canonicalize toolchain symlink"),
            "{zero_loop_err}"
        );
        assert!(!zero_loop_checker.execution_began());
    }
    #[test]
    fn spec_preflight_uses_distinct_inspector_cache_key_and_supports_no_rebuild() {
        use std::os::unix::fs::PermissionsExt;

        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let root = base.join("bundle");
        let prefix = base.join("sysroot");
        let disk_cache = base.join("disk-cache");
        let log_file = base.join("lean-compile.log");
        fs::create_dir_all(prefix.join("lib/lean/Init")).unwrap();

        fs::create_dir_all(root.join("trusted/audit")).unwrap();
        fs::write(root.join("trusted/audit/TrustedBoundary.lean"), "-- trusted boundary\n")
            .unwrap();
        fs::write(root.join("trusted/audit/SpecPreflight.lean"), "-- spec preflight\n").unwrap();

        let lean = base.join("lean");
        fs::write(
            &lean,
            format!(
                r#"#!/bin/sh
case "$1" in
    --version) printf 'Lean 4.34.1\n'; exit ;;
    --print-prefix) printf '%s\n' '{}'; exit ;;
esac
out=""
while [ "$#" -gt 0 ]; do
    case "$1" in
        -o) out="$2"; shift 2 ;;
        *) shift ;;
    esac
done
if [ -n "$out" ]; then
    printf '%s\n' "$out" >> '{}'
    printf 'olean\0024.34.1\000synthetic' > "$out"
    exit 0
fi
exit 1
"#,
                prefix.display(),
                log_file.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();

        // Populate TrustedBoundary first, then ensure SpecPreflight still
        // misses TrustedBoundary's cache key and compiles into its own slot.
        let mut c1 = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c1.set_allow_unpinned_lean(true);
        c1.set_sandbox_mode(SandboxMode::Unsandboxed);
        c1.set_olean_disk_cache_dir_for_test(Some(disk_cache.clone()));
        c1.tool_admission().unwrap();
        let tb = c1.ensure_inspector_compiled("target-audit", true, false).unwrap();
        let sp = c1.ensure_inspector_compiled("headers", true, true).unwrap();
        assert!(tb.ends_with("TrustedBoundary.olean"), "{}", tb.display());
        assert!(sp.ends_with("SpecPreflight.olean"), "{}", sp.display());
        let cold_lines: Vec<String> =
            fs::read_to_string(&log_file).unwrap().lines().map(str::to_owned).collect();
        assert_eq!(cold_lines.len(), 2, "expected distinct cold compiles: {cold_lines:?}");
        fs::write(&log_file, b"").unwrap();

        // Both inspectors must hit disk cache under `--no-rebuild-bundled`.
        let mut c2 = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c2.set_allow_unpinned_lean(true);
        c2.set_sandbox_mode(SandboxMode::Unsandboxed);
        c2.set_olean_disk_cache_dir_for_test(Some(disk_cache));
        c2.set_no_rebuild_bundled(true);
        c2.tool_admission().unwrap();
        let tb2 = c2.ensure_inspector_compiled("target-audit", true, false).unwrap();
        let sp2 = c2.ensure_inspector_compiled("headers", true, true).unwrap();
        assert!(tb2.ends_with("TrustedBoundary.olean"), "{}", tb2.display());
        assert!(sp2.ends_with("SpecPreflight.olean"), "{}", sp2.display());
        assert_eq!(fs::read_to_string(&log_file).unwrap(), "", "warm --no-rebuild must not compile");
    }

    #[test]
    fn arena_ndjson_kernels_run_verified_with_capped_jobs() {
        let jobs = crate::toolchain::default_compile_workers(2);
        assert!((1..=2).contains(&jobs), "{jobs}");
        for kernel in [StandaloneNdjsonKernel::ConRon, StandaloneNdjsonKernel::ConLeche] {
            assert_eq!(kernel.args(), ["--verified".to_owned(), format!("--jobs={jobs}")]);
        }
        assert_eq!(StandaloneNdjsonKernel::Lean4lean.args(), ["--import"]);
    }

    #[test]
    fn sysroot_content_key_binds_unpinned_olean_part_digests() {
        let root = PathBuf::from("/sysroot");
        let mut adm = AdmittedToolchain {
            inspector: root.join("TrustedBoundary.lean"),
            inspector_sha256: String::new(),
            lean_sha256: "lean".to_owned(),
            version: "4.35.0".to_owned(),
            prefix: root.clone(),
            axioms: Vec::new(),
            foundation_graph: BTreeMap::new(),
            graph: BTreeMap::new(),
            artifacts: BTreeMap::new(),
            library_lock: None,
            library_modules: BTreeSet::new(),
            unpinned: true,
            sysroot_package_roots: BTreeSet::new(),
            unpinned_records: BTreeMap::new(),
            lean_binary_sha256: None,
            exec_lean: root.join("bin/lean"),
            expected_lean_sha: None,
            sysroot_manifest_sha256: None,
            inspector_olean: None,
            runtime_libs_verified: false,
            ndjson_tools: None,
            spec_preflight: None,
            spec_preflight_sha256: None,
            spec_preflight_olean: None,
        };
        let record = |olean: &str| crate::toolchain::UnpinnedSysrootArtifacts {
            artifacts: ModuleArtifacts {
                olean_parts: vec!["/sysroot/lib/lean/Init/Prelude.olean".to_owned()],
                ir_parts: Vec::new(),
            },
            source_sha256: None,
            part_hashes: vec![("olean".to_owned(), olean.to_owned())],
        };
        adm.unpinned_records.insert("Init.Prelude".to_owned(), record("aa"));
        let base = sysroot_content_key(&adm);

        // Changing only a `.olean` digest (same Lean binary, same source
        // digest) changes the key.
        adm.unpinned_records.insert("Init.Prelude".to_owned(), record("bb"));
        let changed = sysroot_content_key(&adm);
        assert_ne!(base, changed);

        // An additional admitted module changes the key too.
        adm.unpinned_records.insert("Init.Core".to_owned(), record("aa"));
        assert_ne!(changed, sysroot_content_key(&adm));

        // A verified pinned manifest digest is the key.
        adm.sysroot_manifest_sha256 = Some("manifest".to_owned());
        assert_eq!(sysroot_content_key(&adm), "manifest");
    }

    #[test]
    fn target_shard_disk_cache_skips_reads_and_writes_when_unsandboxed() {
        use std::os::unix::fs::PermissionsExt;

        assert!(!is_cacheable_module("Proof.IdTree", false));
        assert!(!is_cacheable_module("Captured.Shard_000", false));
        assert!(!is_cacheable_module("Proof.Shard_000", false));
        assert!(is_cacheable_module("Trusted", false));

        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let root = base.join("bundle");
        let prefix = base.join("sysroot");
        let disk_cache = base.join("disk-cache");
        let log_file = base.join("lean-compile.log");
        fs::create_dir_all(prefix.join("lib/lean/Init")).unwrap();

        let inspector_src = root.join("trusted/audit/TrustedBoundary.lean");
        fs::create_dir_all(inspector_src.parent().unwrap()).unwrap();
        fs::write(&inspector_src, "-- synthetic inspector\n").unwrap();

        let lean = base.join("lean");
        fs::write(
            &lean,
            format!(
                r#"#!/bin/sh
case "$1" in
    --version) printf 'Lean 4.34.1\n'; exit ;;
    --print-prefix) printf '%s\n' '{}'; exit ;;
esac
out=""
while [ "$#" -gt 0 ]; do
    case "$1" in
        -o) out="$2"; shift 2 ;;
        *) shift ;;
    esac
done
if [ -n "$out" ]; then
    printf '%s\n' "$out" >> '{}'
    printf 'olean\0024.34.1\000shard-payload' > "$out"
    exit 0
fi
exit 1
"#,
                prefix.display(),
                log_file.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&lean, fs::Permissions::from_mode(0o755)).unwrap();

        let bundled_src = base.join("BinChunkTree.lean");
        let id_src = base.join("IdTree.lean");
        let cap_src = base.join("CapturedShard0.lean");
        let proof_src = base.join("ProofShard0.lean");
        fs::write(&bundled_src, "prelude\n").unwrap();
        fs::write(&id_src, "prelude\nimport Anneal.SccSharding.BinChunkTree\n").unwrap();
        fs::write(&cap_src, "prelude\n").unwrap();
        fs::write(&proof_src, "prelude\nimport Proof.IdTree\nimport Captured.Shard_000\n")
            .unwrap();

        let edge = |m: &str| ImportEdge {
            module: m.to_owned(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        };
        let order = vec![
            "Anneal.SccSharding.BinChunkTree".to_owned(),
            "Proof.IdTree".to_owned(),
            "Captured.Shard_000".to_owned(),
            "Proof.Shard_000".to_owned(),
        ];
        let sources = BTreeMap::from([
            ("Anneal.SccSharding.BinChunkTree".to_owned(), bundled_src),
            ("Proof.IdTree".to_owned(), id_src),
            ("Captured.Shard_000".to_owned(), cap_src.clone()),
            ("Proof.Shard_000".to_owned(), proof_src),
        ]);
        let imports = BTreeMap::from([
            ("Anneal.SccSharding.BinChunkTree".to_owned(), Vec::new()),
            ("Proof.IdTree".to_owned(), vec![edge("Anneal.SccSharding.BinChunkTree")]),
            ("Captured.Shard_000".to_owned(), Vec::new()),
            (
                "Proof.Shard_000".to_owned(),
                vec![edge("Proof.IdTree"), edge("Captured.Shard_000")],
            ),
        ]);
        let is_module = BTreeMap::from([
            ("Anneal.SccSharding.BinChunkTree".to_owned(), false),
            ("Proof.IdTree".to_owned(), false),
            ("Captured.Shard_000".to_owned(), false),
            ("Proof.Shard_000".to_owned(), false),
        ]);
        let count_v2_entries = |cache_root: &Path| -> usize {
            let v2 = cache_root.join("v2");
            if !v2.exists() {
                return 0;
            }
            fs::read_dir(&v2)
                .unwrap()
                .filter_map(Result::ok)
                .filter(|e| e.file_type().map(|ft| ft.is_dir()).unwrap_or(false))
                .count()
        };

        // Include a bundled module (`Anneal.SccSharding.BinChunkTree`) so
        // `cache_ctx` is created just like production sharded verification.
        // Run 0 populates only the bundled entry; Run 1 hits the bundled entry
        // while recompiling all 3 target shards without writing them.
        let mut lean_sha = String::new();
        let mut sysroot_sha = String::new();
        for run in 0..2 {
            fs::write(&log_file, b"").unwrap();
            let mut c = Checker::new_with_env(&root, Some(&lean), []).unwrap();
            c.set_allow_unpinned_lean(true);
            c.set_sandbox_mode(SandboxMode::Unsandboxed);
            c.set_olean_disk_cache_dir_for_test(Some(disk_cache.clone()));
            c.tool_admission().unwrap();
            c.compile_lean_modules_parallel(
                &order, &sources, &imports, &is_module, "lib", false, true, 1,
            )
            .unwrap();
            if run == 0 {
                lean_sha = c.admitted().unwrap().lean_sha256.clone();
                sysroot_sha = c.ensure_sysroot_manifest_sha256().unwrap();
            }
            let compiled = fs::read_to_string(&log_file).unwrap();
            let expected_compiles = if run == 0 { 4 } else { 3 };
            assert_eq!(
                compiled.lines().count(),
                expected_compiles,
                "run {run} compile count mismatch: {compiled}"
            );
            if run == 1 {
                assert!(
                    !compiled.lines().any(|l| l.ends_with("BinChunkTree.olean")),
                    "run 1 should reuse bundled BinChunkTree from disk cache: {compiled}"
                );
            }
            assert_eq!(
                count_v2_entries(&disk_cache),
                1,
                "unsandboxed run {run} must cache only the bundled module, never target shards"
            );
        }

        // Pre-seed a valid disk-cache entry for `Captured.Shard_000` (as a
        // prior sandboxed run would) and verify unsandboxed elaboration refuses
        // to read it.
        let seeded_olean = base.join("seeded-shard0.olean");
        let seeded_bytes = b"olean\x024.34.1\0seeded-sandboxed-payload";
        fs::write(&seeded_olean, seeded_bytes).unwrap();
        let seeded_sha = sha256_bytes(seeded_bytes);
        let shard_key = OleanCacheKeyInput {
            kind: CacheKind::Module,
            module: "Captured.Shard_000".to_owned(),
            lean_sha256: lean_sha,
            sysroot_manifest_sha256: sysroot_sha,
            source_sha256: sha256_bytes(&fs::read(&cap_src).unwrap()),
            is_module: false,
            flags: canonical_compile_flags(false),
            imports: Vec::new(),
        };
        let mut seed_cache = OleanCache::with_env_vars(None, None);
        seed_cache.set_disk_dir(Some(disk_cache.clone()));
        seed_cache
            .store_compiled(&shard_key, &[("olean", seeded_olean.as_path(), &seeded_sha)])
            .unwrap();
        assert!(
            seed_cache.lookup_bytes(&shard_key).unwrap().is_some(),
            "pre-seeded Captured.Shard_000 entry must be readable by OleanCache"
        );
        assert_eq!(count_v2_entries(&disk_cache), 2);

        fs::write(&log_file, b"").unwrap();
        let mut c = Checker::new_with_env(&root, Some(&lean), []).unwrap();
        c.set_allow_unpinned_lean(true);
        c.set_sandbox_mode(SandboxMode::Unsandboxed);
        c.set_olean_disk_cache_dir_for_test(Some(disk_cache.clone()));
        c.tool_admission().unwrap();
        c.compile_lean_modules_parallel(
            &order, &sources, &imports, &is_module, "lib", false, true, 1,
        )
        .unwrap();
        let compiled = fs::read_to_string(&log_file).unwrap();
        assert_eq!(
            compiled.lines().count(),
            3,
            "unsandboxed run must still recompile all 3 target shards even when pre-seeded: {compiled}"
        );
        assert_eq!(
            compiled.lines().filter(|l| l.ends_with("/Shard_000.olean")).count(),
            2,
            "unsandboxed run must not read pre-seeded Captured.Shard_000 cache entry: {compiled}"
        );
        assert_eq!(
            count_v2_entries(&disk_cache),
            2,
            "unsandboxed run must not write Proof.IdTree or Proof.Shard_000 entries"
        );
    }
}
