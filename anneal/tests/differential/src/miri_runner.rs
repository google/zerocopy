// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Reference-oracle runner invoking Miri on staged differential fixtures.
//!
//! Uses a file-locked offline `cargo miri setup` cache configured with
//! `CARGO_NET_OFFLINE=true` and vendored crates from
//! `<rust_sysroot>/lib/rustlib/src/rust/library/vendor` inside an isolated
//! scratch `CARGO_HOME/config.toml` unless `ANNEAL_MIRI_SYSROOT` explicitly
//! provides a valid prepared non-symlink sysroot.

use std::{
    collections::{BTreeMap, BTreeSet, hash_map::RandomState},
    env,
    ffi::OsString,
    fmt::Write as _,
    fs::{self, File},
    hash::{BuildHasher as _, Hasher as _},
    io::Read as _,
    path::{Component, Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, SystemTime, UNIX_EPOCH},
};

use anneal_testkit::{Invocation, ProcessOutcome, ProcessSupervisor, Termination};
use serde::Serialize;
use serde_json::Value;
use sha2::{Digest, Sha256};

use crate::{
    corpus::LitmusCase,
    lean_runner::{effective_timeout_secs, sha256_bytes_hex, sha256_file_hex},
    verdict::{Expectation, IntKind, MirValue, ObservedOutcome, OrderingKind},
};

mod parse;
mod sysroot;

use parse::*;
pub use parse::{parse_miri_output, parse_miri_ret_line};
use sysroot::*;

const MIRI_RET_STEM: &str = "ANNEAL_MIRI_RET";
const MIRI_RET_PREFIX: &str = "ANNEAL_MIRI_RET=";
static MIRI_MARKER_SEQ: AtomicU64 = AtomicU64::new(0);
const PINNED_MIRI_TARGET: &str = "x86_64-unknown-linux-gnu";
const MIRI_SETUP_TIMEOUT_SECS: u64 = 300;
const MIRI_CASE_TIMEOUT_SECS: u64 = 120;
const RUSTC_PROBE_TIMEOUT_SECS: u64 = 30;

/// Prepared Miri binary and sysroot coordinates for executing reference checks.
#[derive(Clone, Debug)]
pub struct MiriSession {
    pub miri_bin: PathBuf,
    pub rust_sysroot: PathBuf,
    pub miri_sysroot: PathBuf,
}

impl MiriSession {
    /// Locate `miri` alongside `rust_sysroot` and resolve or offline-prepare
    /// a Miri target sysroot under `cache_root`.
    pub fn prepare(rust_sysroot: &Path, cache_root: &Path) -> Result<Self, String> {
        Self::prepare_with_env(rust_sysroot, cache_root, |k| env::var_os(k))
    }

    pub fn prepare_with_env(
        rust_sysroot: &Path,
        cache_root: &Path,
        get_env: impl Fn(&str) -> Option<OsString>,
    ) -> Result<Self, String> {
        let rust_sysroot = fs::canonicalize(rust_sysroot)
            .map_err(|e| format!("canonicalize rust_sysroot: {e}"))?;
        let miri_bin = rust_sysroot.join("bin/miri");
        if !miri_bin.is_file() {
            return Err(format!("pinned sysroot lacks `bin/miri`: {}", miri_bin.display()));
        }

        if let Some(explicit) =
            get_env("ANNEAL_MIRI_SYSROOT").filter(|v| !v.is_empty()).map(PathBuf::from)
        {
            if fs::symlink_metadata(&explicit)
                .map_err(|e| format!("stat ANNEAL_MIRI_SYSROOT={}: {e}", explicit.display()))?
                .file_type()
                .is_symlink()
            {
                return Err(format!(
                    "ANNEAL_MIRI_SYSROOT={} must not be a symlink",
                    explicit.display()
                ));
            }
            if !explicit.join("lib/rustlib").is_dir() {
                return Err(format!(
                    "ANNEAL_MIRI_SYSROOT={} does not contain `lib/rustlib`",
                    explicit.display()
                ));
            }
            let miri_sysroot = fs::canonicalize(&explicit)
                .map_err(|e| format!("canonicalize ANNEAL_MIRI_SYSROOT: {e}"))?;
            let ver_tag = rustc_version_tag(&rust_sysroot)?;
            let setup_sha = compute_miri_setup_input_sha256(&rust_sysroot, &ver_tag)?;
            verify_explicit_miri_sysroot_stamp(&miri_sysroot, &ver_tag, &setup_sha)?;
            return Ok(Self { miri_bin, rust_sysroot, miri_sysroot });
        }

        let ver_tag = rustc_version_tag(&rust_sysroot)?;
        let setup_sha = compute_miri_setup_input_sha256(&rust_sysroot, &ver_tag)?;
        let cache_id = format!("{ver_tag}-{}", &setup_sha[..16]);
        let expected_stamp = expected_miri_ready_stamp(&ver_tag, &setup_sha);
        fs::create_dir_all(cache_root)
            .map_err(|e| format!("create cache dir {}: {e}", cache_root.display()))?;
        let target_dir = cache_root.join(format!("miri-sysroot-{cache_id}"));
        let lock_path = cache_root.join(format!("miri-sysroot-{cache_id}.setup.lock"));
        let lock_file = File::options()
            .create(true)
            .read(true)
            .write(true)
            .truncate(false)
            .open(&lock_path)
            .map_err(|e| format!("open Miri lock {}: {e}", lock_path.display()))?;
        lock_file
            .lock()
            .map_err(|e| format!("acquire Miri setup lock {}: {e}", lock_path.display()))?;

        let ready_stamp = target_dir.join(".anneal-miri-ready");
        let stamp_matches = fs::symlink_metadata(&ready_stamp)
            .ok()
            .is_some_and(|m| !m.file_type().is_symlink() && m.is_file())
            && fs::read_to_string(&ready_stamp).ok().as_deref() == Some(expected_stamp.as_str());
        if !stamp_matches || !target_dir.join("lib/rustlib").is_dir() {
            build_offline_miri_sysroot(&rust_sysroot, &miri_bin, &target_dir)?;
            fs::write(&ready_stamp, &expected_stamp)
                .map_err(|e| format!("write Miri ready stamp: {e}"))?;
        }
        drop(lock_file);

        let miri_sysroot = fs::canonicalize(&target_dir)
            .map_err(|e| format!("canonicalize Miri sysroot {}: {e}", target_dir.display()))?;
        Ok(Self { miri_bin, rust_sysroot, miri_sysroot })
    }

    /// Execute all litmus cases under Miri, grouping harness generation by
    /// fixture source file and running cases across bounded worker threads.
    pub fn run_cases(
        &self,
        cases: &[LitmusCase],
    ) -> Result<BTreeMap<String, ObservedOutcome>, String> {
        let mut by_source: BTreeMap<PathBuf, Vec<&LitmusCase>> = BTreeMap::new();
        for case in cases {
            by_source.entry(case.source_abs.clone()).or_default().push(case);
        }

        let workers = thread::available_parallelism().map(|n| n.get().clamp(1, 4)).unwrap_or(1);
        let ld_path = join_library_path(&self.rust_sysroot.join("lib"));
        let path_env = build_child_path(&self.rust_sysroot.join("bin"))?;
        let rustc_bin = fs::canonicalize(self.rust_sysroot.join("bin/rustc"))
            .map_err(|e| format!("canonicalize rustc in {}: {e}", self.rust_sysroot.display()))?;
        let setup_timeout = effective_timeout_secs(MIRI_SETUP_TIMEOUT_SECS)?;

        let work_root = tempfile::tempdir()
            .map_err(|e| format!("create temporary Miri harness workspace: {e}"))?;
        let mut results = BTreeMap::new();
        struct MiriWorkItem {
            case_id: String,
            harness_path: PathBuf,
            bridge_rlib: PathBuf,
            corpus_dir: PathBuf,
            selector: String,
            token: String,
        }
        let mut work_items: Vec<MiriWorkItem> = Vec::with_capacity(cases.len());

        for (group_idx, (source_abs, group_cases)) in by_source.iter().enumerate() {
            let source_text = fs::read_to_string(source_abs)
                .map_err(|e| format!("read fixture {}: {e}", source_abs.display()))?;
            let bundle_res = build_isolated_miri_group(
                work_root.path(),
                group_idx,
                &source_text,
                group_cases,
                &rustc_bin,
                &self.miri_sysroot,
                &ld_path,
                &path_env,
                Duration::from_secs(setup_timeout),
            );
            match bundle_res {
                Ok(bundle) => {
                    for case in group_cases {
                        work_items.push(MiriWorkItem {
                            case_id: case.id.clone(),
                            harness_path: bundle.harness_path.clone(),
                            bridge_rlib: bundle.bridge_rlib.clone(),
                            corpus_dir: bundle.corpus_dir.clone(),
                            selector: case.id.clone(),
                            token: bundle.token.clone(),
                        });
                    }
                }
                Err(detail) => {
                    for case in group_cases {
                        results.insert(
                            case.id.clone(),
                            ObservedOutcome::ToolError { detail: detail.clone() },
                        );
                    }
                }
            }
        }

        for chunk in work_items.chunks(workers) {
            let outcomes = thread::scope(|scope| {
                let mut handles = Vec::with_capacity(chunk.len());
                for item in chunk {
                    let miri_bin = &self.miri_bin;
                    let miri_sysroot = &self.miri_sysroot;
                    let ld_path = &ld_path;
                    let path_env = &path_env;
                    handles.push(scope.spawn(move || {
                        let out = run_single_miri(
                            miri_bin,
                            miri_sysroot,
                            ld_path,
                            path_env,
                            &item.harness_path,
                            &item.bridge_rlib,
                            &item.corpus_dir,
                            &item.selector,
                            Some(item.token.as_str()),
                        );
                        (item.case_id.clone(), out)
                    }));
                }
                handles
                    .into_iter()
                    .map(|h| {
                        h.join().unwrap_or_else(|_| {
                            (
                                "<panicked>".to_owned(),
                                ObservedOutcome::ToolError {
                                    detail: "Miri worker thread panicked".to_owned(),
                                },
                            )
                        })
                    })
                    .collect::<Vec<_>>()
            });
            for (case_id, outcome) in outcomes {
                results.insert(case_id, outcome);
            }
        }

        Ok(results)
    }
}

fn fresh_miri_marker_token(disallowed_haystack: &str) -> String {
    loop {
        let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
        let seq = MIRI_MARKER_SEQ.fetch_add(1, Ordering::Relaxed);
        let mut h = Sha256::new();
        h.update(b"anneal-miri-marker-v2\0");
        h.update(nanos.to_le_bytes());
        h.update(std::process::id().to_le_bytes());
        h.update(seq.to_le_bytes());
        h.update((disallowed_haystack.len() as u64).to_le_bytes());
        let mut rs = RandomState::new().build_hasher();
        rs.write_u64(seq);
        h.update(rs.finish().to_le_bytes());
        if let Ok(mut urand) = File::open("/dev/urandom") {
            let mut buf = [0u8; 16];
            if urand.read_exact(&mut buf).is_ok() {
                h.update(buf);
            }
        }
        let digest = h.finalize();
        let mut tok = String::with_capacity(32);
        for b in &digest[..16] {
            let _ = write!(tok, "{b:02x}");
        }
        if !disallowed_haystack.contains(&tok) {
            return tok;
        }
    }
}

fn validate_rust_ident(ident: &str, label: &str) -> Result<(), String> {
    let mut bytes = ident.bytes();
    let Some(first) = bytes.next() else {
        return Err(format!("empty {label}"));
    };
    if !(first.is_ascii_alphabetic() || first == b'_')
        || !bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
    {
        return Err(format!("invalid {label} `{ident}`"));
    }
    Ok(())
}

fn validate_rust_fn_path(path: &str) -> Result<(), String> {
    if path.is_empty()
        || path.split("::").any(|seg| validate_rust_ident(seg, "fixture function segment").is_err())
    {
        return Err(format!("invalid fixture function path `{path}`"));
    }
    Ok(())
}

struct IsolatedMiriBundle {
    token: String,
    harness_path: PathBuf,
    bridge_rlib: PathBuf,
    corpus_dir: PathBuf,
}

#[allow(clippy::too_many_arguments)]
fn compile_miri_rlib(
    rustc_bin: &Path,
    miri_sysroot: &Path,
    ld_path: &str,
    path_env: &OsString,
    crate_name: &str,
    src_path: &Path,
    out_rlib: &Path,
    extra_extern: Option<(&str, &Path)>,
    extra_lib_dir: Option<&Path>,
    timeout_secs: u64,
) -> Result<(), String> {
    let mut inv = Invocation::new(rustc_bin, &["--edition=2024", "--target", PINNED_MIRI_TARGET])
        .arg("--sysroot")
        .arg(miri_sysroot)
        .arg("--cfg")
        .arg("miri")
        .arg("-Zalways-encode-mir")
        .arg("-C")
        .arg("opt-level=0")
        .arg("-C")
        .arg("debug-assertions=no")
        .arg("-C")
        .arg("overflow-checks=no")
        .arg("-A")
        .arg("dead_code")
        .arg("--crate-type=lib")
        .arg("--crate-name")
        .arg(crate_name);
    if let Some((dep_name, dep_rlib)) = extra_extern {
        inv = inv.arg("--extern").arg(format!("{dep_name}={}", dep_rlib.display()));
    }
    if let Some(lib_dir) = extra_lib_dir {
        inv = inv.arg("-L").arg(lib_dir);
    }
    inv = inv
        .arg("-o")
        .arg(out_rlib)
        .arg(src_path)
        .env("LD_LIBRARY_PATH", ld_path)
        .env("PATH", path_env);
    if let Some(tmp) = env::var_os("TMPDIR").filter(|v| !v.is_empty()) {
        inv = inv.env("TMPDIR", tmp);
    }

    let work_dir = src_path.parent().unwrap_or_else(|| Path::new("/"));
    let out = run_supervised(&inv, work_dir, timeout_secs, crate_name)?;
    match out.termination {
        Termination::Exited(status) if status.success() => Ok(()),
        other => Err(format!(
            "compile Miri `{crate_name}` crate failed ({}): {}",
            other.describe(),
            String::from_utf8_lossy(&out.stderr).lines().take(6).collect::<Vec<_>>().join(" | ")
        )),
    }
}

#[allow(clippy::too_many_arguments)]
fn build_isolated_miri_group(
    work_root: &Path,
    group_idx: usize,
    source_text: &str,
    group_cases: &[&LitmusCase],
    rustc_bin: &Path,
    miri_sysroot: &Path,
    ld_path: &str,
    path_env: &OsString,
    setup_timeout: Duration,
) -> Result<IsolatedMiriBundle, String> {
    let group_dir = work_root.join(format!("group_{group_idx}"));
    let corpus_dir = group_dir.join("c");
    let bridge_dir = group_dir.join("b");
    fs::create_dir_all(&corpus_dir)
        .map_err(|e| format!("create Miri corpus dir {}: {e}", corpus_dir.display()))?;
    fs::create_dir_all(&bridge_dir)
        .map_err(|e| format!("create Miri bridge dir {}: {e}", bridge_dir.display()))?;

    // Compile `corpus` and `bridge` into separate `.rlib` crates BEFORE
    // generating the secret token or writing `h/harness.rs`, keeping the
    // token strictly inside `h/harness.rs` source literals (never in paths,
    // symbols, args, or stack frame metadata).
    let corpus_src = corpus_dir.join("corpus.rs");
    fs::write(&corpus_src, source_text)
        .map_err(|e| format!("write Miri corpus {}: {e}", corpus_src.display()))?;
    let corpus_rlib = corpus_dir.join("libcorpus.rlib");
    let timeout_secs = setup_timeout.as_secs().max(1);
    compile_miri_rlib(
        rustc_bin,
        miri_sysroot,
        ld_path,
        path_env,
        "corpus",
        &corpus_src,
        &corpus_rlib,
        None,
        None,
        timeout_secs,
    )?;

    let bridge_code = generate_miri_bridge(group_cases)?;
    let bridge_src = bridge_dir.join("bridge.rs");
    fs::write(&bridge_src, &bridge_code)
        .map_err(|e| format!("write Miri bridge {}: {e}", bridge_src.display()))?;
    let bridge_rlib = bridge_dir.join("libbridge.rlib");
    compile_miri_rlib(
        rustc_bin,
        miri_sysroot,
        ld_path,
        path_env,
        "bridge",
        &bridge_src,
        &bridge_rlib,
        Some(("corpus", &corpus_rlib)),
        Some(&corpus_dir),
        timeout_secs,
    )?;

    let mut disallowed = String::with_capacity(source_text.len() + bridge_code.len() + 1);
    disallowed.push_str(source_text);
    disallowed.push('\n');
    disallowed.push_str(&bridge_code);
    let token = fresh_miri_marker_token(&disallowed);

    let harness_code = generate_miri_harness_with_token(group_cases, Some(&token))?;
    let harness_dir = group_dir.join("h");
    fs::create_dir_all(&harness_dir)
        .map_err(|e| format!("create Miri harness dir {}: {e}", harness_dir.display()))?;
    let harness_path = harness_dir.join("harness.rs");
    fs::write(&harness_path, harness_code)
        .map_err(|e| format!("write Miri harness {}: {e}", harness_path.display()))?;

    Ok(IsolatedMiriBundle { token, harness_path, bridge_rlib, corpus_dir })
}

fn miri_ret_prefix_for_token(token: Option<&str>) -> String {
    match token {
        Some(tok) => format!("{MIRI_RET_STEM}:{tok}="),
        None => MIRI_RET_PREFIX.to_owned(),
    }
}

fn generate_miri_bridge(cases: &[&LitmusCase]) -> Result<String, String> {
    let mut out = String::from("#![allow(unused_unsafe)]\nextern crate corpus;\n\n");
    for (idx, case) in cases.iter().enumerate() {
        validate_rust_fn_path(&case.function)?;
        let arg_exprs =
            case.args.iter().map(rust_arg_expr).collect::<Result<Vec<_>, _>>()?.join(", ");
        let call = format!("unsafe {{ corpus::{}({arg_exprs}) }}", case.function);
        match (&case.expected, &case.expected_return) {
            (Expectation::Pass, Some(exp)) => {
                let ret_ty = rust_ret_type(exp)?;
                let _ = writeln!(
                    out,
                    "#[inline(never)]\npub fn call_case_{idx}() -> {ret_ty} {{\n    {call}\n}}\n"
                );
            }
            _ => {
                let _ = writeln!(
                    out,
                    "#[inline(never)]\npub fn call_case_{idx}() {{\n    let _ret = {call};\n}}\n"
                );
            }
        }
    }
    Ok(out)
}

#[cfg_attr(not(test), allow(dead_code))]
fn generate_miri_harness(cases: &[&LitmusCase]) -> Result<String, String> {
    generate_miri_harness_with_token(cases, None)
}

fn generate_miri_harness_with_token(
    cases: &[&LitmusCase],
    token: Option<&str>,
) -> Result<String, String> {
    let ret_prefix = miri_ret_prefix_for_token(token);
    let mut out = String::from("extern crate bridge;\n\nfn main() {\n");
    out.push_str("    let selector = std::env::args().nth(1).expect(\"missing case selector\");\n");
    out.push_str("    match selector.as_str() {\n");

    for (idx, case) in cases.iter().enumerate() {
        out.push_str(&format!("        {:?} => {{\n", case.id));
        match (&case.expected, &case.expected_return) {
            (Expectation::Pass, Some(exp)) => {
                let ret_ty = rust_ret_type(exp)?;
                out.push_str(&format!(
                    "            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(bridge::call_case_{idx})) {{\n\
                     \x20               Ok(ret) => {{ let ret: {ret_ty} = ret; {}; }}\n\
                     \x20               Err(_) => println!(\"{ret_prefix}PANICKED\"),\n\
                     \x20           }}\n",
                    rust_print_ret_stmt(exp, "ret", &ret_prefix)?
                ));
            }
            _ => {
                out.push_str(&format!(
                    "            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(bridge::call_case_{idx})) {{\n\
                     \x20               Ok(()) => println!(\"{ret_prefix}UNEXPECTED_RETURN\"),\n\
                     \x20               Err(_) => println!(\"{ret_prefix}PANICKED\"),\n\
                     \x20           }}\n"
                ));
            }
        }
        out.push_str("        }\n");
    }

    out.push_str("        other => panic!(\"unknown differential case selector: {other}\"),\n");
    out.push_str("    }\n}\n");
    Ok(out)
}

fn rust_arg_expr(val: &MirValue) -> Result<String, String> {
    match val {
        MirValue::Int { int_kind, bits } => Ok(int_kind.format_rust_literal(*bits)),
        MirValue::Bool { value } => Ok(value.to_string()),
        MirValue::Char { scalar } => {
            char::from_u32(*scalar).ok_or_else(|| format!("invalid Unicode scalar {scalar}"))?;
            Ok(format!("char::from_u32({scalar}u32).unwrap()"))
        }
        MirValue::Ordering { value } => Ok(value.to_rust_expr().to_owned()),
        MirValue::Unit => Ok("()".to_owned()),
        MirValue::Enum { enum_type, variant, .. } => {
            validate_rust_ident(enum_type, "enum name")?;
            validate_rust_ident(variant, "enum variant")?;
            Ok(format!("corpus::{enum_type}::{variant}"))
        }
        MirValue::OverflowPair { .. } => {
            Err("OverflowPair is not a supported Miri harness input type in Stage 1".to_owned())
        }
    }
}

fn rust_ret_type(shape: &MirValue) -> Result<String, String> {
    match shape {
        MirValue::Int { int_kind, .. } => Ok(int_kind.rust_name().to_owned()),
        MirValue::Bool { .. } => Ok("bool".to_owned()),
        MirValue::Char { .. } => Ok("char".to_owned()),
        MirValue::Ordering { .. } => Ok("core::cmp::Ordering".to_owned()),
        MirValue::Unit => Ok("()".to_owned()),
        MirValue::OverflowPair { int_kind, .. } => Ok(format!("({}, bool)", int_kind.rust_name())),
        MirValue::Enum { .. } => Err("Enum expected_return is not supported in Stage 1".to_owned()),
    }
}

fn rust_print_ret_stmt(shape: &MirValue, var: &str, ret_prefix: &str) -> Result<String, String> {
    match shape {
        MirValue::Int { int_kind, .. } => {
            Ok(format!("println!(\"{ret_prefix}INT:{}:{{}}\", {var})", int_kind.rust_name()))
        }
        MirValue::Bool { .. } => Ok(format!("println!(\"{ret_prefix}BOOL:{{}}\", {var})")),
        MirValue::Char { .. } => Ok(format!("println!(\"{ret_prefix}CHAR:{{}}\", {var} as u32)")),
        MirValue::Ordering { .. } => Ok(format!(
            "println!(\"{ret_prefix}ORDERING:{{}}\", match {var} {{ \
             core::cmp::Ordering::Less => \"less\", \
             core::cmp::Ordering::Equal => \"equal\", \
             core::cmp::Ordering::Greater => \"greater\" }})"
        )),
        MirValue::Unit => Ok(format!("let () = {var}; println!(\"{ret_prefix}UNIT\")")),
        MirValue::OverflowPair { int_kind, .. } => Ok(format!(
            "println!(\"{ret_prefix}OVF:{}:{{}}:{{}}\", {var}.0, {var}.1)",
            int_kind.rust_name()
        )),
        MirValue::Enum { .. } => Err("Enum expected_return is not supported in Stage 1".to_owned()),
    }
}

#[allow(clippy::too_many_arguments)]
fn invoke_single_miri(
    miri_bin: &Path,
    miri_sysroot: &Path,
    ld_path: &str,
    path_env: &OsString,
    harness_path: &Path,
    bridge_rlib: &Path,
    corpus_dir: &Path,
    selector: &str,
    mute_target_io: bool,
) -> Result<(Option<i32>, String, String), ObservedOutcome> {
    let bridge_dir = bridge_rlib.parent().unwrap_or_else(|| Path::new("/"));
    let mut inv = Invocation::new(
        miri_bin,
        &["--edition=2024", "--target", PINNED_MIRI_TARGET, "--error-format=json"],
    )
    .arg("--sysroot")
    .arg(miri_sysroot)
    .arg("-C")
    .arg("opt-level=0")
    .arg("-C")
    .arg("debug-assertions=no")
    .arg("-C")
    .arg("overflow-checks=no")
    .arg("-Zmiri-tree-borrows")
    .arg("-Zmiri-seed=0");
    if mute_target_io {
        inv = inv.arg("-Zmiri-mute-stdout-stderr");
    }
    inv = inv
        .arg("--crate-name")
        .arg("harness")
        .arg("--extern")
        .arg(format!("bridge={}", bridge_rlib.display()))
        .arg("-L")
        .arg(bridge_dir)
        .arg("-L")
        .arg(corpus_dir)
        .arg(harness_path)
        .arg("--")
        .arg(selector)
        .env("LD_LIBRARY_PATH", ld_path)
        .env("PATH", path_env);
    if let Some(tmp) = env::var_os("TMPDIR").filter(|v| !v.is_empty()) {
        inv = inv.env("TMPDIR", tmp);
    }

    let case_timeout = effective_timeout_secs(MIRI_CASE_TIMEOUT_SECS)
        .map_err(|detail| ObservedOutcome::ToolError { detail })?;
    let work_dir = harness_path.parent().unwrap_or_else(|| Path::new("/"));
    let out = run_supervised(&inv, work_dir, case_timeout, selector)
        .map_err(|detail| ObservedOutcome::ToolError { detail })?;
    let exit_code = match out.termination {
        Termination::Exited(status) => status.code(),
        Termination::TimedOut(status) => {
            return Err(ObservedOutcome::ToolError {
                detail: format!("miri timed out after {case_timeout}s for {selector} ({status})"),
            });
        }
        Termination::LaunchFailed(err) => {
            return Err(ObservedOutcome::ToolError {
                detail: format!("spawn miri for {selector}: {err}"),
            });
        }
    };
    Ok((
        exit_code,
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    ))
}

#[allow(clippy::too_many_arguments)]
fn run_single_miri(
    miri_bin: &Path,
    miri_sysroot: &Path,
    ld_path: &str,
    path_env: &OsString,
    harness_path: &Path,
    bridge_rlib: &Path,
    corpus_dir: &Path,
    selector: &str,
    expected_token: Option<&str>,
) -> ObservedOutcome {
    let (exit_code, stdout, stderr) = match invoke_single_miri(
        miri_bin,
        miri_sysroot,
        ld_path,
        path_env,
        harness_path,
        bridge_rlib,
        corpus_dir,
        selector,
        false,
    ) {
        Ok(res) => res,
        Err(err) => return err,
    };
    if exit_code == Some(0) {
        return parse_miri_output_with_token(exit_code, &stdout, &stderr, expected_token);
    }
    // Non-zero exits re-run with `-Zmiri-mute-stdout-stderr` so Miri's host
    // diagnostics arrive over a channel fixture code cannot write.
    let (muted_exit, _muted_stdout, muted_stderr) = match invoke_single_miri(
        miri_bin,
        miri_sysroot,
        ld_path,
        path_env,
        harness_path,
        bridge_rlib,
        corpus_dir,
        selector,
        true,
    ) {
        Ok(res) => res,
        Err(err) => return err,
    };
    if muted_exit == Some(0) {
        return ObservedOutcome::ToolError {
            detail: format!(
                "Miri non-zero exit ({exit_code:?}) for {selector} did not reproduce under -Zmiri-mute-stdout-stderr"
            ),
        };
    }
    parse_miri_output_with_token(muted_exit, "", &muted_stderr, expected_token)
}

#[cfg(test)]
mod tests;
