// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Bind one configured compilation to its canonical Lean verification claim.
//!
//! The proof package supplies specifications and proof terms. It cannot supply
//! the source model, captured subject or expected proposition. Those inputs are
//! staged independently and passed to the compiled-environment auditor.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
    process::{Command, ExitCode},
    time::Instant,
};

use cargo_anneal::{
    Checker, TargetAuditRequest, TargetBindings, TargetModule, TargetRole, sha256_bytes,
};
use clap::Args;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

use crate::setup::installed_tools;

// Generated resources keep installed and packaged builds independent of the
// source checkout. The explicit regeneration check binds these bytes to the
// canonical audited sources without running a build hook.
include!("bundled_resources.rs");

const PINNED_CAPTURE_SCHEMA_VERSION: u32 = 3;
const PINNED_RUSTC_COMMIT: &str = "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1";

/// Arguments of the build-neutral verification command.
#[derive(Args)]
pub struct VerifyArgs {
    /// JSON compilation and proof request for one selected function.
    #[arg(long)]
    request: PathBuf,
    /// New UTF-8 directory path for retained capture, sources and audit
    /// evidence.
    #[arg(long)]
    artifacts: Option<PathBuf>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    schema_version: u32,
    compilation: Compilation,
    scope: Scope,
    proof: Proof,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Compilation {
    source_root: PathBuf,
    crate_root: PathBuf,
    crate_name: String,
    #[serde(default = "edition")]
    edition: String,
    #[serde(default = "target")]
    target: String,
    #[serde(default)]
    cfg: BTreeSet<String>,
    source_files: Vec<PathBuf>,
}

fn edition() -> String {
    "2024".to_owned()
}

// This target belongs to the verification profile. Archive variants select
// executables for the host running Anneal; adding a host must not expand the
// semantic domain. Capture admits only this triple before compiler setup in
// `trusted/rustc-capture/src/main.rs` (`run`).
// A compatible custom sysroot can provide this target's libraries on another
// host. Keep library availability under the compiler's authority so neither a
// host ban nor a guessed standard-library inventory rejects that configuration.
fn target() -> String {
    "x86_64-unknown-linux-gnu".to_owned()
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
enum Scope {
    SelectedUnit { roots: BTreeSet<String> },
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Proof {
    source_root: PathBuf,
    #[serde(default = "spec_name")]
    specification: String,
    #[serde(default = "proof_name")]
    theorem: String,
    #[serde(default)]
    specification_module: Option<String>,
    #[serde(default)]
    theorem_module: Option<String>,
    sources: Vec<ProofSource>,
}

fn spec_name() -> String {
    "Spec.specs".to_owned()
}

fn proof_name() -> String {
    "Proof.verify".to_owned()
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProofSource {
    module: String,
    path: PathBuf,
    role: AuthoredRole,
}

/// Authored inputs cannot claim ownership of the model, captured program,
/// or expected proposition. Those roles would let a proof producer replace
/// the meaning of the obligation instead of proving it.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum AuthoredRole {
    Specification,
    Proof,
}

#[derive(Clone, Serialize)]
struct SourceIdentity {
    relative_path: PathBuf,
    sha256: String,
}

#[derive(Deserialize)]
struct CaptureReceipt {
    configuration: Value,
    source_files: Vec<CapturedSourceFile>,
    census: Value,
    selected: Value,
    program: CaptureProgram,
}

#[derive(Deserialize)]
struct CaptureCompiler {
    commit: String,
}

#[derive(Deserialize)]
struct CapturedSourceFile {
    path: PathBuf,
    sha256: String,
}

#[derive(Deserialize)]
struct CaptureProgram {
    scope: Scope,
    #[serde(rename = "bodies")]
    _bodies: serde::de::IgnoredAny,
}

#[derive(Deserialize)]
struct CaptureSchemaHeader {
    schema_version: u32,
    #[serde(default)]
    compiler: Option<CaptureCompiler>,
}

fn parse_capture_receipt(bytes: &[u8]) -> Result<CaptureReceipt> {
    let header: CaptureSchemaHeader =
        serde_json::from_slice(bytes).map_err(|e| error("tool_failed", "capture", e))?;
    // Capture schema 3 records structured `IntWidth` / `IntTy`, `ConstLit`,
    // `EnumTagRepr`, and a single authoritative `program.scope` (including
    // rootless `crate` scope values), retaining schema 2's `with_retag` flags
    // and source identities. Check the schema version and compiler commit
    // before strict deserialization so older capture ABIs report a clear
    // version mismatch. Request schema 1 is independent.
    if header.schema_version != PINNED_CAPTURE_SCHEMA_VERSION
        || header.compiler.as_ref().map(|compiler| compiler.commit.as_str())
            != Some(PINNED_RUSTC_COMMIT)
    {
        return Err(error("tool_failed", "capture", "unexpected capture schema or compiler"));
    }
    serde_json::from_slice(bytes).map_err(|e| error("tool_failed", "capture", e))
}

#[derive(Serialize)]
struct FailureReceipt<'a> {
    schema_version: u32,
    status: &'a str,
    phase: &'a str,
    detail: &'a str,
    // `None` omits the key (pre-run staging/retention failures); `Some(None)`
    // emits `"artifacts": null` when `--artifacts` was omitted on failure.
    #[serde(skip_serializing_if = "Option::is_none")]
    artifacts: Option<Option<&'a str>>,
}

#[derive(Debug)]
struct Error {
    status: &'static str,
    phase: &'static str,
    detail: String,
}

type Result<T> = std::result::Result<T, Error>;

fn error(status: &'static str, phase: &'static str, detail: impl ToString) -> Error {
    Error { status, phase, detail: detail.to_string() }
}

fn io(phase: &'static str, failure: std::io::Error) -> Error {
    error("tool_failed", phase, failure)
}

fn identifier(value: &str) -> bool {
    !value.is_empty() && value.split('.').all(cargo_anneal::is_lean_ident)
}

fn module_of(name: &str) -> Result<String> {
    if !identifier(name) || !name.contains('.') {
        return Err(error("unsupported", "request", "expected a qualified Lean declaration name"));
    }
    Ok(name.rsplit_once('.').unwrap().0.to_owned())
}

/// Return whether `module` names a runner-owned module or namespace.
///
/// The `Trusted` and `Anneal` namespaces hold the installed model and theory.
/// The `Captured` and `Expected` modules are the captured subject and the
/// generated claim. Names already used by staged modules are also rejected as
/// duplicates; reserving whole namespaces covers names that no bundled module
/// uses yet.
fn reserved_proof_module(module: &str) -> bool {
    matches!(module, "Expected" | "Captured" | "Trusted" | "Anneal")
        || module.starts_with("Trusted.")
        || module.starts_with("Anneal.")
}

/// Require a declared regular file beneath an already canonical root.
///
/// Relative paths cannot escape the staging namespace. Canonical equality
/// also rejects symlink traversal; adjacent compiled Lean files are never read.
fn declared_file(root: &Path, relative: &Path) -> Result<PathBuf> {
    if relative.as_os_str().is_empty()
        || relative.components().any(|part| !matches!(part, Component::Normal(_)))
    {
        return Err(error("unsupported", "inputs", "input paths must be clean relative paths"));
    }
    let path = root.join(relative);
    let meta = fs::symlink_metadata(&path).map_err(|e| io("inputs", e))?;
    if !meta.is_file()
        || meta.file_type().is_symlink()
        || fs::canonicalize(&path).map_err(|e| io("inputs", e))? != path
    {
        return Err(error(
            "unsupported",
            "inputs",
            format!("not a declared regular file: {}", path.display()),
        ));
    }
    Ok(path)
}

fn request_root(base: &Path, path: &Path) -> Result<PathBuf> {
    if path.as_os_str().is_empty()
        || path.components().any(|part| !matches!(part, Component::Normal(_) | Component::CurDir))
    {
        return Err(error("unsupported", "inputs", "source roots must be relative to the request"));
    }
    let root = fs::canonicalize(base.join(path)).map_err(|e| io("inputs", e))?;
    if !root.starts_with(base) || !root.is_dir() {
        return Err(error(
            "unsupported",
            "inputs",
            "source root must be a directory inside the request directory",
        ));
    }
    Ok(root)
}

fn write(path: &Path, bytes: &[u8]) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| io("staging", e))?;
    }
    fs::write(path, bytes).map_err(|e| io("staging", e))
}

fn encoded<T: Serialize>(value: &T) -> Result<Vec<u8>> {
    serde_json::to_vec_pretty(value).map_err(|e| error("tool_failed", "json", e))
}

fn load_request(path: &Path) -> Result<(Request, PathBuf)> {
    let path = fs::canonicalize(path).map_err(|e| io("request", e))?;
    if !path.is_file() {
        return Err(error("unsupported", "request", "request must be a regular file"));
    }
    let bytes = fs::read(&path).map_err(|e| io("request", e))?;
    let request = serde_json::from_slice(&bytes).map_err(|e| error("unsupported", "request", e))?;
    Ok((request, path.parent().unwrap().to_path_buf()))
}

fn run(args: &VerifyArgs, work: &Path) -> Result<Value> {
    let start = Instant::now();
    let (request, base) = load_request(&args.request)?;
    let Scope::SelectedUnit { roots } = &request.scope;
    if roots.len() != 1 {
        return Err(error("unsupported", "request", "select exactly one function"));
    }
    let source_root = request_root(&base, &request.compilation.source_root)?;
    let proof_root = request_root(&base, &request.proof.source_root)?;
    if request.schema_version != 1 || request.compilation.source_files.is_empty() {
        return Err(error("unsupported", "request", "unsupported or empty compilation request"));
    }
    if !identifier(&request.proof.specification) || !identifier(&request.proof.theorem) {
        return Err(error("unsupported", "request", "invalid Lean declaration identifier"));
    }
    let spec_module = match &request.proof.specification_module {
        Some(module) if identifier(module) => module.clone(),
        Some(_) => {
            return Err(error("unsupported", "request", "invalid specification module"));
        }
        None => module_of(&request.proof.specification)?,
    };
    let theorem_module = match &request.proof.theorem_module {
        Some(module) if identifier(module) => module.clone(),
        Some(_) => {
            return Err(error("unsupported", "request", "invalid theorem module"));
        }
        None => module_of(&request.proof.theorem)?,
    };
    // Selection roots and cfg entries use BTreeSet so spelling order and
    // duplicates normalize automatically in the hashed request identity.
    let request_bytes = encoded(&request)?;
    let request_sha256 = sha256_bytes(&request_bytes);
    write(&work.join("request.json"), &request_bytes)?;

    // Rust and Lean consume private snapshots, not paths they can resolve
    // back into the caller's live checkout. Record the original bytes too:
    // the final identity check must still bind the receipt to those inputs.
    let rust_stage = work.join("rust");
    fs::create_dir_all(&rust_stage).map_err(|e| io("staging", e))?;
    let mut originals = Vec::new();
    let mut sources = Vec::new();
    let mut paths = BTreeSet::new();
    for relative in &request.compilation.source_files {
        if !paths.insert(relative.clone()) {
            return Err(error("unsupported", "inputs", "duplicate source input"));
        }
        let original = declared_file(&source_root, relative)?;
        let bytes = fs::read(&original).map_err(|e| io("inputs", e))?;
        let sha256 = sha256_bytes(&bytes);
        write(&rust_stage.join(relative), &bytes)?;
        originals.push((original, sha256.clone()));
        sources.push(SourceIdentity { relative_path: relative.clone(), sha256 });
    }
    if !paths.contains(&request.compilation.crate_root) {
        return Err(error("unsupported", "inputs", "crate_root is not a declared source"));
    }
    // The invocation owns tool selection; target requests cannot name a
    // compiler executable. Adapter correctness is a stated TCB assumption.
    // Its digest identifies the selected build and detects later changes, but
    // no lock pins it. Capture checks only the commit that the Rust compiler
    // and sysroot report; neither is hashed.
    // Select all three tools from the same installation.
    let tools = installed_tools().map_err(|detail| error("tool_failed", "setup", detail))?;
    let capture = fs::canonicalize(tools.capture).map_err(|e| io("capture-tool", e))?;
    let capture_binary_sha256 =
        sha256_bytes(&fs::read(&capture).map_err(|e| io("capture-tool", e))?);
    let capture_dir = work.join("capture");
    // Capture reserves and publishes a new output directory itself; precreating
    // it here would violate its create-only publication contract.
    // Do not let a target crate's ambient compiler wrappers or search paths
    // enter the capture process. The only added library path below comes
    // from the operator-selected compiler installation.
    let mut command = Command::new(&capture);
    command
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .args(["capture", "--crate-root"])
        .arg(rust_stage.join(&request.compilation.crate_root))
        .args([
            "--crate-name",
            &request.compilation.crate_name,
            "--edition",
            &request.compilation.edition,
            "--target",
            &request.compilation.target,
            "--out-dir",
        ])
        .arg(&capture_dir)
        .current_dir(&rust_stage);
    let sysroot = fs::canonicalize(tools.sysroot).map_err(|e| io("sysroot", e))?;
    command.env("LD_LIBRARY_PATH", sysroot.join("lib"));
    command.arg("--sysroot").arg(sysroot);
    for name in roots {
        command.arg("--select").arg(name);
    }
    // Preserve each cfg as option data through capture's parser. Capture must
    // use the joined form again when rebuilding compiler argv: the pinned
    // response-file expansion gate is "arg.strip_prefix('@')", before --cfg
    // parsing. Extracting the String must not restore a standalone @file arg.
    // https://github.com/rust-lang/rust/blob/f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1/compiler/rustc_driver_impl/src/args.rs#L14-L32
    for cfg in &request.compilation.cfg {
        command.arg(format!("--cfg={cfg}"));
    }
    for source in &sources {
        command.arg("--source-file").arg(rust_stage.join(&source.relative_path));
    }
    let capture_start = Instant::now();
    let output = command.output().map_err(|e| io("capture", e))?;
    write(&work.join("capture.stdout"), &output.stdout)?;
    write(&work.join("capture.stderr"), &output.stderr)?;
    if !output.status.success() {
        let envelope: Value = serde_json::from_slice(&output.stdout).unwrap_or(Value::Null);
        let status = match envelope["status"].as_str() {
            Some("unsupported") => "unsupported",
            Some("compiler_failed") => "compiler_failed",
            _ => "tool_failed",
        };
        let detail = if envelope.is_object() {
            if !output.stderr.is_empty() {
                eprint!("{}", String::from_utf8_lossy(&output.stderr));
            }
            envelope.to_string()
        } else {
            String::from_utf8_lossy(&output.stderr).into_owned()
        };
        return Err(error(status, "capture", detail));
    }
    let capture_ms = capture_start.elapsed().as_millis();
    let capture_bytes = fs::read(capture_dir.join("capture.json")).map_err(|e| io("capture", e))?;
    let manifest = parse_capture_receipt(&capture_bytes)?;
    // Authenticate configuration and scope before compiling any authored
    // Lean. A valid theorem about another target or a narrower selection
    // cannot satisfy this request.
    if manifest.program.scope != request.scope
        || manifest.configuration["crate_name"] != request.compilation.crate_name
        || manifest.configuration["target"] != request.compilation.target
        || manifest.configuration["edition"] != request.compilation.edition
        || manifest.configuration["cfg"] != json!(request.compilation.cfg)
    {
        return Err(error(
            "tool_failed",
            "capture",
            "capture differs from the requested compilation or scope",
        ));
    }
    // Every observed compiler read must match a staged, declared input.
    // Unused declared files remain in the receipt identity; they need not
    // become compiler reads merely because the request staged them.
    let source_by_path: BTreeMap<_, _> =
        sources.iter().map(|s| (rust_stage.join(&s.relative_path), &s.sha256)).collect();
    for source in &manifest.source_files {
        let Some(expected) = source_by_path.get(&source.path) else {
            return Err(error("tool_failed", "capture", "compiler read an undeclared source"));
        };
        if &source.sha256 != *expected {
            return Err(error("tool_failed", "capture", "compiler read different source bytes"));
        }
    }
    let capture_sha256 = sha256_bytes(&capture_bytes);

    let bundle = work.join("anneal");
    let mut modules = Vec::new();
    let mut model_identity = Vec::new();
    // Installed theory remains proof code even though it ships with the
    // model. Only primitive trusted modules may determine the canonical
    // proposition; packaging must not promote proof helpers into its TCB.
    for (relative, text) in BUNDLE {
        let path = bundle.join(relative);
        write(&path, text.as_bytes())?;
        let file_sha256 = sha256_bytes(text.as_bytes());
        model_identity.push((*relative, file_sha256.clone()));
        if relative.ends_with(".lean") && relative.starts_with("trusted/lean/") {
            modules.push(TargetModule {
                module: relative
                    .trim_start_matches("trusted/lean/")
                    .trim_end_matches(".lean")
                    .replace('/', "."),
                source: path,
                expected_sha256: file_sha256,
                role: TargetRole::Model,
            });
        } else if relative.ends_with(".lean") && relative.starts_with("theory/") {
            modules.push(TargetModule {
                module: relative
                    .trim_start_matches("theory/")
                    .trim_end_matches(".lean")
                    .replace('/', "."),
                source: path,
                expected_sha256: file_sha256,
                role: TargetRole::Proof,
            });
        }
    }
    let model_manifest_sha256 = sha256_bytes(&encoded(&model_identity)?);
    let captured_lean = capture_dir.join("Captured.lean");
    modules.push(TargetModule {
        module: "Captured".to_owned(),
        expected_sha256: sha256_bytes(&fs::read(&captured_lean).map_err(|e| io("capture", e))?),
        source: captured_lean,
        role: TargetRole::Capture,
    });

    // Module names choose destinations in the private stage. Reserve the
    // runner-owned names before writing anything so authored files cannot
    // shadow the model, captured subject, or generated expectation.
    let mut module_names: BTreeSet<_> = modules.iter().map(|m| m.module.clone()).collect();
    let mut spec_identity = Vec::new();
    for input in &request.proof.sources {
        if !identifier(&input.module)
            || reserved_proof_module(&input.module)
            || !module_names.insert(input.module.clone())
        {
            return Err(error(
                "unsupported",
                "proof",
                "invalid, duplicate or reserved proof module",
            ));
        }
        let original = declared_file(&proof_root, &input.path)?;
        let bytes = fs::read(&original).map_err(|e| io("proof", e))?;
        let sha256 = sha256_bytes(&bytes);
        originals.push((original, sha256.clone()));
        let source =
            work.join("authored").join(input.module.replace('.', "/")).with_extension("lean");
        write(&source, &bytes)?;
        let role = match input.role {
            AuthoredRole::Specification => {
                spec_identity.push((input.module.clone(), sha256.clone()));
                TargetRole::Specification
            }
            AuthoredRole::Proof => TargetRole::Proof,
        };
        modules.push(TargetModule {
            module: input.module.clone(),
            source,
            expected_sha256: sha256,
            role,
        });
    }
    if !modules
        .iter()
        .any(|m| m.module == spec_module && matches!(m.role, TargetRole::Specification))
        || !modules
            .iter()
            .any(|m| m.module == theorem_module && matches!(m.role, TargetRole::Proof))
    {
        return Err(error(
            "unsupported",
            "proof",
            "specification and theorem must have their declared source roles",
        ));
    }
    // Keep the reviewed specification identity separate from ordinary
    // proof edits. The auditor also checks actual compiled dependencies,
    // so a helper that changes a specification's meaning needs its role.
    let specification_manifest_sha256 = sha256_bytes(&encoded(&spec_identity)?);
    let root_name = "UnitTheorem";
    // Only validated declaration identifiers enter this fixed template. The
    // authored proof package never supplies an expected proposition or model.
    let header = "-- Copyright 2026 The Fuchsia Authors\n--\n-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n-- This file may not be copied, modified, or distributed except according to\n-- those terms.\n\n";
    let expected = format!(
        "{header}prelude\nimport Trusted.MirSemantics\nimport Captured\nimport {spec_module}\n\nnamespace Expected\ndef claim : Prop := _root_.Trusted.MirSemantics.{root_name} (_root_.Trusted.MirSemantics.Crate.mk _root_.Captured.program _root_.{})\nend Expected\n",
        request.proof.specification
    );
    let expected_path = work.join("generated/Expected.lean");
    write(&expected_path, expected.as_bytes())?;
    modules.push(TargetModule {
        module: "Expected".to_owned(),
        source: expected_path,
        expected_sha256: sha256_bytes(expected.as_bytes()),
        role: TargetRole::Expected,
    });
    let audit_request = TargetAuditRequest {
        modules,
        theorem_module,
        theorem_name: request.proof.theorem.clone(),
        expected_module: "Expected".to_owned(),
        expected_declaration: "Expected.claim".to_owned(),
        canonical_root: format!("Trusted.MirSemantics.{root_name}"),
        subject_declaration: "Captured.program".to_owned(),
        specification_declaration: request.proof.specification.clone(),
        bindings: TargetBindings {
            request_sha256: request_sha256.clone(),
            capture_sha256: capture_sha256.clone(),
            model_manifest_sha256: model_manifest_sha256.clone(),
            specification_manifest_sha256: specification_manifest_sha256.clone(),
        },
    };
    write(&work.join("audit-request.json"), &encoded(&audit_request)?)?;
    let proof_start = Instant::now();
    // Authored elaboration is not acceptance. The inspector must replay
    // the exact closed root and enforce origin roles before a receipt can
    // report verification success. Operational failures stay distinct from
    // a successfully executed checker rejecting a proof.
    let mut checker = Checker::new(&bundle, Some(&tools.lean)).map_err(|e| io("audit", e))?;
    let audit = checker.run_target(&audit_request).map_err(|e| {
        error(if e.code == 1 { "proof_failed" } else { "tool_failed" }, "audit", e.to_string())
    })?;
    let proof_ms = proof_start.elapsed().as_millis();
    // Snapshot identity is checked again at the accepting boundary. Logical
    // type equality cannot authenticate unused source or configuration hashes.
    for (path, expected) in &originals {
        if sha256_bytes(&fs::read(path).map_err(|e| io("binding", e))?) != *expected {
            return Err(error("tool_failed", "binding", "an input changed during verification"));
        }
    }
    if sha256_bytes(&fs::read(&capture).map_err(|e| io("binding", e))?) != capture_binary_sha256 {
        return Err(error(
            "tool_failed",
            "binding",
            "capture executable changed during verification",
        ));
    }
    let correspondence_provenance: Value = serde_json::from_str(CORRESPONDENCE_PROVENANCE_JSON)
        .map_err(|e| {
            error(
                "tool_failed",
                "bundle",
                format!("corrupt bundled correspondence provenance: {e}"),
            )
        })?;
    // These assumptions delimit the result, including development builds
    // selected by the operator. Identity hashes make the subject and tool
    // choice reviewable; they do not prove the trusted adapter correct.
    //
    // `toolchain_identity` separates toolchain files whose SHA-256 digests
    // verification compares with the bundled locks from the capture
    // executable, whose digest is only recorded, and from components that
    // verification does not hash. At most a version that the toolchain
    // reports about itself identifies an unhashed component, so its integrity
    // rests on the uncompromised execution environment assumed by
    // THREAT_MODEL.md section 2.1.
    let result = json!({
        "schema_version": 1, "status": "selected_unit_verified", "experimental": true,
        "request_sha256": request_sha256, "capture_sha256": capture_sha256,
        "capture_binary_sha256": capture_binary_sha256,
        "toolchain_identity": {
            "sha256_locked": [
                "Lean executable in foundation-lock.json",
                "foundation-lock.json modules",
                "imported library-lock.json modules",
            ],
            "sha256_recorded": ["capture executable as capture_binary_sha256"],
            "unhashed": [
                "Lean shared libraries, identified by lean --version",
                "Lean sysroot modules outside the locks, including Lean.* and Std.*",
                "Rust compiler and sysroot, identified by their reported commit",
            ],
        },
        "model_manifest_sha256": model_manifest_sha256,
        "specification_manifest_sha256": specification_manifest_sha256,
        "correspondence_provenance": correspondence_provenance,
        "scope": request.scope, "selected": manifest.selected,
        "census": manifest.census, "sources": sources,
        "configuration": manifest.configuration, "audit": audit,
        "timing_ms": {
            "capture": capture_ms,
            "proof_and_audit": proof_ms,
            "total": start.elapsed().as_millis(),
        },
        "assumptions": [
            "faithful pinned compiler capture",
            "experimental pointer-free MIR semantics",
            "Lean kernel and admitted foundation",
            "intact compiler and verification environment",
        ],
        "deferred": [
            "hostile Lean elaborator effects",
            "complete review-surface reporting",
            "source-to-deployed-binary correspondence",
        ]
    });
    write(&work.join("result.json"), &encoded(&result)?)?;
    Ok(result)
}

fn verification_stage() -> std::io::Result<tempfile::TempDir> {
    // Capture canonicalizes source paths before recording its read inventory.
    // Create the stage below a canonical parent so compiler arguments and our
    // inventory keys use that same namespace, even when TMPDIR is a symlink.
    // TempDir owns the resulting physical path and still handles its cleanup.
    let parent = fs::canonicalize(std::env::temp_dir())?;
    let mut builder = tempfile::Builder::new();
    builder.prefix("anneal-verification-");
    // Snapshots contain source and diagnostics that other local users should
    // not read. Set permissions at creation instead of relying on the umask.
    // This is Unix user privacy, not isolation from same-user host access.
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        builder.permissions(fs::Permissions::from_mode(0o700));
    }
    builder.tempdir_in(parent)
}

fn emit_failure(
    status: &str,
    phase: &str,
    detail: &str,
    artifacts: Option<Option<&str>>,
    code: u8,
) -> ExitCode {
    let receipt = FailureReceipt { schema_version: 1, status, phase, detail, artifacts };
    println!("{}", serde_json::to_string(&receipt).expect("serializable failure receipt"));
    ExitCode::from(code)
}

pub fn main(args: VerifyArgs) -> ExitCode {
    // Receipts encode the artifact destination as JSON text. Check its exact
    // spelling before staging or retention can create evidence, so an encoding
    // failure cannot leave an export with no receipt. Carry the checked text
    // into retention and reporting; lossy conversion would change its path.
    let artifacts = match args.artifacts.as_deref() {
        Some(path) => match path.to_str() {
            Some(path) => Some(path),
            None => {
                return emit_failure(
                    "tool_failed",
                    "retention",
                    "artifact destination path must be UTF-8",
                    None,
                    2,
                );
            }
        },
        None => None,
    };
    let stage = match verification_stage() {
        Ok(stage) => stage,
        Err(failure) => {
            return emit_failure("tool_failed", "staging", &failure.to_string(), None, 2);
        }
    };
    // Preserve diagnostic evidence for rejected requests as well as proved
    // ones. Export failure takes precedence over the verification result:
    // the requested evidence operation has not completed successfully.
    let outcome = run(&args, stage.path());
    // Retention is create-only. A caller cannot accidentally overwrite a proof
    // package or an earlier verification receipt by choosing an existing path.
    let retained = if let Some(destination) = artifacts {
        match retain(stage.path(), Path::new(destination)) {
            Ok(()) => Some(destination),
            Err(failure) => {
                return emit_failure("tool_failed", failure.phase, &failure.detail, None, 2);
            }
        }
    } else {
        None
    };
    match outcome {
        Ok(mut result) => {
            if let Some(path) = retained {
                result["artifacts"] = json!(path);
            }
            println!("{}", serde_json::to_string_pretty(&result).unwrap());
            ExitCode::SUCCESS
        }
        Err(failure) => {
            let code = if matches!(failure.status, "unsupported" | "proof_failed") { 1 } else { 2 };
            emit_failure(failure.status, failure.phase, &failure.detail, Some(retained), code)
        }
    }
}

/// Copy diagnostics into a destination owned by this export.
///
/// Existing destinations are never changed. A failed copy removes the newly
/// created directory; a cleanup failure identifies possibly incomplete output.
/// Callers report success only after every file has been copied.
fn retain(source: &Path, destination: &Path) -> Result<()> {
    // Exported evidence contains the same private inputs as the stage. Set
    // the Unix mode at creation so no permissive chmod window exposes them.
    let directory = fs::DirBuilder::new();
    #[cfg(unix)]
    let directory = {
        use std::os::unix::fs::DirBuilderExt;
        let mut directory = directory;
        directory.mode(0o700);
        directory
    };
    // Acquire ownership with create-only admission before entering any
    // cleanup path. A caller's existing directory must never be deleted
    // merely because retention failed to claim its requested destination.
    directory.create(destination).map_err(|e| io("retention", e))?;
    if let Err(failure) = copy_artifacts(source, destination) {
        // The destination belongs to this export, so a failed copy can be
        // removed without leaving a path that blocks retry. If removal
        // fails too, report possible partial output rather than claiming
        // either a complete export or a clean filesystem rollback.
        if let Err(cleanup) = fs::remove_dir_all(destination) {
            return Err(error(
                "tool_failed",
                "retention",
                format!(
                    "{}; incomplete artifacts may remain at {} (cleanup failed: {cleanup})",
                    failure.detail,
                    destination.display()
                ),
            ));
        }
        return Err(failure);
    }
    Ok(())
}

fn copy_artifacts(source: &Path, destination: &Path) -> Result<()> {
    for entry in walkdir::WalkDir::new(source).min_depth(1).follow_links(false) {
        let entry = entry.map_err(|e| error("tool_failed", "retention", e))?;
        let relative = entry.path().strip_prefix(source).unwrap();
        if entry.file_type().is_symlink() {
            return Err(error("tool_failed", "retention", "unexpected staging symlink"));
        }
        let target = destination.join(relative);
        if entry.file_type().is_dir() {
            fs::create_dir(&target).map_err(|e| io("retention", e))?;
        } else {
            fs::copy(entry.path(), target).map_err(|e| io("retention", e))?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn verification_directories_are_private_with_umask_022() {
        use std::os::unix::fs::{DirBuilderExt, PermissionsExt};

        const CHILD: &str = "ANNEAL_VERIFICATION_DIRECTORY_PERMISSION_CHILD";
        if std::env::var_os(CHILD).is_some() {
            let stage = verification_stage().unwrap();
            fs::write(stage.path().join("input.rs"), b"private source bytes").unwrap();
            let parent = tempfile::tempdir().unwrap();
            let destination = parent.path().join("artifacts");
            assert!(retain(stage.path(), &destination).is_ok());
            assert_eq!(fs::read(destination.join("input.rs")).unwrap(), b"private source bytes");

            let existing = parent.path().join("existing");
            fs::DirBuilder::new().mode(0o750).create(&existing).unwrap();
            fs::write(existing.join("keep"), b"caller bytes").unwrap();
            assert!(retain(stage.path(), &existing).is_err());
            assert_eq!(fs::metadata(&existing).unwrap().permissions().mode() & 0o777, 0o750);
            assert_eq!(fs::read(existing.join("keep")).unwrap(), b"caller bytes");
            assert!(!existing.join("input.rs").exists());

            assert_eq!(
                (
                    fs::metadata(stage.path()).unwrap().permissions().mode() & 0o777,
                    fs::metadata(&destination).unwrap().permissions().mode() & 0o777,
                ),
                (0o700, 0o700)
            );
            return;
        }

        // Umask is process-wide. Change it only in a fresh child so this
        // regression cannot race other tests running in the parent binary.
        let output = Command::new("/bin/sh")
            .args(["-c", "umask 022; exec \"$@\"", "anneal-private-directories"])
            .arg(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "verify::tests::verification_directories_are_private_with_umask_022",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "permission probe failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        // `--exact` with a stale module path matches no test and still exits
        // successfully. Require the child to have run this probe.
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(stdout.contains("1 passed"), "permission probe did not run:\n{stdout}");
    }

    #[test]
    fn declaration_names_cannot_inject_lean_commands() {
        for valid in ["Spec.specs", "A.B_2.proof", "Proof.verify"] {
            assert!(identifier(valid));
        }
        for invalid in [
            "",
            ".Proof",
            "Proof..verify",
            "Proof.verify\naxiom x : False",
            "Proof.(verify)",
            "Proof.7bad",
        ] {
            assert!(!identifier(invalid));
        }
    }

    #[test]
    fn proof_modules_cannot_claim_runner_owned_names() {
        for reserved in [
            "Trusted",
            "Trusted.Foo",
            "Trusted.MirSemantics",
            "Captured",
            "Expected",
            "Anneal",
            "Anneal.Shadow",
        ] {
            assert!(reserved_proof_module(reserved), "{reserved}");
        }
        // A prefix within a component or a later component reserves nothing.
        for authored in
            ["Spec", "Proof", "TrustedHelper", "AnnealProof", "Proof.Trusted", "Spec.Expected"]
        {
            assert!(!reserved_proof_module(authored), "{authored}");
        }
    }

    #[test]
    fn declared_inputs_reject_escape_and_symlinks() {
        let dir = tempfile::tempdir().unwrap();
        fs::write(dir.path().join("source.rs"), "pub fn f() {}").unwrap();
        let root = fs::canonicalize(dir.path()).unwrap();
        assert!(declared_file(&root, Path::new("source.rs")).is_ok());
        assert!(declared_file(&root, Path::new("../source.rs")).is_err());
        assert!(declared_file(&root, Path::new("/source.rs")).is_err());
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink("source.rs", root.join("alias.rs")).unwrap();
            assert!(declared_file(&root, Path::new("alias.rs")).is_err());
        }
    }

    #[cfg(unix)]
    #[test]
    fn request_roots_are_confined_to_the_request_directory() {
        let outside = tempfile::tempdir().unwrap();
        let dir = tempfile::tempdir().unwrap();
        let base = dir.path().canonicalize().unwrap();
        let inside = base.join("rust");
        fs::create_dir(&inside).unwrap();

        assert_eq!(request_root(&base, Path::new(".")).unwrap(), base);
        assert_eq!(request_root(&base, Path::new("rust")).unwrap(), inside);
        assert!(request_root(&base, Path::new("..")).is_err());
        assert!(request_root(&base, outside.path()).is_err());
        #[cfg(unix)]
        {
            std::os::unix::fs::symlink(outside.path(), base.join("alias")).unwrap();
            assert!(request_root(&base, Path::new("alias")).is_err());
        }
    }

    #[test]
    fn artifact_retention_cleans_failed_copy_and_allows_retry() {
        use std::os::unix::fs::symlink;

        let source = tempfile::tempdir().unwrap();
        fs::create_dir(source.path().join("logs")).unwrap();
        fs::write(source.path().join("logs/compiler.stderr"), b"diagnostics").unwrap();
        let outside = tempfile::tempdir().unwrap();
        let sentinel = outside.path().join("keep");
        fs::write(&sentinel, b"outside bytes").unwrap();
        let link = source.path().join("unexpected");
        symlink(&sentinel, &link).unwrap();
        let export_parent = tempfile::tempdir().unwrap();
        let destination = export_parent.path().join("artifacts");

        let Err(failure) = retain(source.path(), &destination) else {
            panic!("a staging symlink must reject retention");
        };
        assert_eq!(failure.status, "tool_failed");
        assert_eq!(failure.phase, "retention");
        assert!(!destination.exists(), "a failed export must be removed");
        assert_eq!(fs::read(&sentinel).unwrap(), b"outside bytes");

        fs::remove_file(link).unwrap();
        assert!(retain(source.path(), &destination).is_ok());
        assert_eq!(fs::read(destination.join("logs/compiler.stderr")).unwrap(), b"diagnostics");
    }

    #[test]
    fn artifact_retention_preserves_existing_empty_destination() {
        let source = tempfile::tempdir().unwrap();
        fs::write(source.path().join("new"), b"new output").unwrap();
        let destination = tempfile::tempdir().unwrap();
        assert!(retain(source.path(), destination.path()).is_err());
        assert!(destination.path().is_dir());
        assert_eq!(fs::read_dir(destination.path()).unwrap().count(), 0);
    }

    #[cfg(unix)]
    #[test]
    fn artifact_retention_preserves_existing_symlink_destination() {
        use std::os::unix::fs::symlink;

        let source = tempfile::tempdir().unwrap();
        fs::write(source.path().join("new"), b"new output").unwrap();
        let outside = tempfile::tempdir().unwrap();
        fs::write(outside.path().join("keep"), b"outside bytes").unwrap();
        let parent = tempfile::tempdir().unwrap();
        let destination = parent.path().join("artifacts");
        symlink(outside.path(), &destination).unwrap();
        assert!(retain(source.path(), &destination).is_err());
        assert!(fs::symlink_metadata(&destination).unwrap().is_symlink());
        assert_eq!(fs::read(outside.path().join("keep")).unwrap(), b"outside bytes");
        assert!(!outside.path().join("new").exists());
    }

    #[test]
    fn artifact_retention_never_overwrites() {
        let source = tempfile::tempdir().unwrap();
        let target = tempfile::tempdir().unwrap();
        fs::write(target.path().join("keep"), b"valuable").unwrap();
        assert!(retain(source.path(), target.path()).is_err());
        assert_eq!(fs::read(target.path().join("keep")).unwrap(), b"valuable");
    }

    #[test]
    fn old_capture_schema_reports_version_mismatch_before_strict_deserialization() {
        let schema2 = br#"{"schema_version":2,"compiler":{"commit":"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"},"legacy":true}"#;
        let Err(err) = parse_capture_receipt(schema2) else {
            panic!("schema 2 receipt must be rejected");
        };
        assert_eq!(err.status, "tool_failed");
        assert_eq!(err.phase, "capture");
        assert_eq!(err.detail, "unexpected capture schema or compiler");
    }

    #[test]
    fn failure_receipt_preserves_null_or_omitted_artifacts() {
        let omitted: Value = serde_json::to_value(FailureReceipt {
            schema_version: 1,
            status: "tool_failed",
            phase: "retention",
            detail: "bad path",
            artifacts: None,
        })
        .unwrap();
        assert!(omitted.get("artifacts").is_none(), "{omitted}");

        let explicit_null: Value = serde_json::to_value(FailureReceipt {
            schema_version: 1,
            status: "unsupported",
            phase: "capture",
            detail: "bad item",
            artifacts: Some(None),
        })
        .unwrap();
        assert_eq!(explicit_null.get("artifacts"), Some(&Value::Null), "{explicit_null}");

        let retained: Value = serde_json::to_value(FailureReceipt {
            schema_version: 1,
            status: "proof_failed",
            phase: "audit",
            detail: "mismatch",
            artifacts: Some(Some("/tmp/evidence")),
        })
        .unwrap();
        assert_eq!(retained["artifacts"], "/tmp/evidence");
    }

    #[test]
    fn scope_deserialization_accepts_only_the_selected_unit_format() {
        assert_eq!(
            serde_json::from_str::<Scope>(r#"{"kind":"selected_unit","roots":["a","b","a"]}"#)
                .unwrap(),
            Scope::SelectedUnit { roots: BTreeSet::from(["a".to_owned(), "b".to_owned()]) }
        );
        for invalid in [
            r#"{"kind":"crate"}"#,
            r#"{"kind":"crate","roots":["a"]}"#,
            r#"{"kind":"crate","roots":null}"#,
            r#"{"kind":"crate","extra":1}"#,
            r#"{"kind":"selected_unit"}"#,
            r#"{"kind":"selected_unit","roots":null}"#,
            r#"{"kind":"selected_unit","roots":["a"],"extra":1}"#,
            r#"{"kind":"other"}"#,
        ] {
            assert!(
                serde_json::from_str::<Scope>(invalid).is_err(),
                "expected invalid scope JSON to fail: {invalid}"
            );
        }
    }

    #[test]
    fn bundled_correspondence_provenance_is_well_formed() {
        let provenance: Value = serde_json::from_str(CORRESPONDENCE_PROVENANCE_JSON)
            .expect("bundled correspondence provenance must be valid JSON");
        assert_eq!(provenance["schema_version"], 1);
        assert_eq!(provenance["upstream_repository"], "https://github.com/proofs-rs/lean-miri.git");
        assert_eq!(provenance["upstream_commit"], "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a");
        assert_eq!(
            provenance["sysroot_foundation_manifest_sha256"],
            cargo_anneal::LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256
        );
        assert_eq!(provenance["upstream_pin_sha256"].as_str().unwrap().len(), 64);
        assert_eq!(provenance["correspondence_adapter_sha256"].as_str().unwrap().len(), 64);
        assert_eq!(provenance["patched_files"].as_array().unwrap().len(), 10);
        assert_eq!(provenance["correspondence_proofs"].as_object().unwrap().len(), 2);
        assert_eq!(provenance["trusted_lean"].as_object().unwrap().len(), 5);
    }
}
