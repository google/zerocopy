// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Opt-in installed tests: `cargo test -p cargo-anneal --test installed_smoke
//! -- --ignored --exact installed_smoke --nocapture`.
//!
//! Set `ANNEAL_TEST_SOURCE_REVISION` and supply exact artifact paths through
//! `ANNEAL_TEST_CARGO_ANNEAL` and `ANNEAL_TEST_AUDITOR` for selected cases.
//! `ANNEAL_TEST_ARCHIVE` makes a
//! fresh test-owned installation shared by the selected cases. The alternative
//! `ANNEAL_TEST_INSTALL_ROOT` tests an existing explicit installation and does
//! not establish fresh-archive coverage. Supply exactly one of these inputs.
//!
//! `ANNEAL_TEST_CASE` selects one exact name from `CASES`; absence selects all
//! smoke cases. The defaults are two workers and 120 seconds per child process;
//! override them with `ANNEAL_TEST_JOBS` and `ANNEAL_TEST_TIMEOUT_SECS`.
//! Failures retain all inputs and command evidence in a reported temporary
//! directory; `ANNEAL_TEST_DIAGNOSTICS` also exports it for CI collection. Run
//! `python3 reproduce.py` in a retained command directory to repeat its argv,
//! environment, and working directory with the recorded toolchain artifacts.

#![cfg(feature = "setup")]

#[allow(dead_code)]
#[path = "../src/setup.rs"]
mod setup;
mod support;

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    env, fs,
    path::{Path, PathBuf},
    time::Duration,
};

use cargo_anneal::{
    Failure, ImportEdge, ParallelDagPlan, is_lean_ident, run_parallel_dag, topo_sort_modules,
};
use serde_json::{Value, json};
use support::{
    CaseDirectory, Invocation, ProcessOutcome, RunDirectory, TestResult, select_cases, write_json,
};

const CASES: &[&str] = &[
    "audit-accepted",
    "audit-missing-lean",
    "audit-rejected",
    "bundled-cargo-check",
    "cargo-arguments",
    "cargo-help",
    #[cfg(target_os = "linux")]
    "cargo-setup-invalid-archive",
    "cargo-version",
    "driver-callback",
    "lean-file",
    "rustdoc-html",
];

#[test]
#[ignore = "requires explicit current-run installed artifacts; CI runs this suite"]
fn installed_smoke() {
    let revision = env::var("ANNEAL_TEST_SOURCE_REVISION")
        .unwrap_or_else(|_| "<missing ANNEAL_TEST_SOURCE_REVISION>".into());
    // Invalid settings are reported inside the owned run so startup failures
    // receive the same evidence retention as failures in a case body.
    let seconds = setting("ANNEAL_TEST_TIMEOUT_SECS", 120, 3600).unwrap_or(120);
    let run = RunDirectory::new(&revision, Duration::from_secs(seconds as u64))
        .expect("create smoke evidence directory");
    let result = run_smoke(&run);
    let diagnostics = env::var_os("ANNEAL_TEST_DIAGNOSTICS").map(PathBuf::from);
    if let Err(error) = run.finish(result, diagnostics.as_deref()) {
        panic!("{error}");
    }
}

fn run_smoke(run: &RunDirectory) -> TestResult {
    let supplied: std::collections::BTreeMap<_, _> = [
        "ANNEAL_TEST_SOURCE_REVISION",
        "ANNEAL_TEST_ARCHIVE",
        "ANNEAL_TEST_INSTALL_ROOT",
        "ANNEAL_TEST_CARGO_ANNEAL",
        "ANNEAL_TEST_AUDITOR",
        "ANNEAL_TEST_CASE",
        "ANNEAL_TEST_JOBS",
        "ANNEAL_TEST_TIMEOUT_SECS",
        "ANNEAL_TEST_DIAGNOSTICS",
    ]
    .into_iter()
    .filter_map(|key| env::var_os(key).map(|value| (key, value.to_string_lossy().into_owned())))
    .collect();
    write_json(&run.path().join("supplied-inputs.json"), &json!(supplied))?;
    let selection = env::var("ANNEAL_TEST_CASE").ok();
    let selected = select_cases(CASES, selection.as_deref())?;
    let jobs = setting("ANNEAL_TEST_JOBS", 2, 32)?;
    setting("ANNEAL_TEST_TIMEOUT_SECS", 120, 3600)?;
    let revision = env::var("ANNEAL_TEST_SOURCE_REVISION")
        .map_err(|_| "ANNEAL_TEST_SOURCE_REVISION must identify the run's source revision")?;
    if revision.trim().is_empty() {
        return Err("ANNEAL_TEST_SOURCE_REVISION must be nonempty".into());
    }
    write_json(
        &run.path().join("selection.json"),
        &json!({
            "cases": selected,
            "workers": jobs,
        }),
    )?;
    let checkout = Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .unwrap();
    // Installed tools must work without checkout-relative configuration or
    // build outputs. Keep every case below an unrelated working directory
    // so a missing installed input cannot be supplied by this source tree.
    if fs::canonicalize(run.path())
        .map_err(|error| error.to_string())?
        .starts_with(checkout)
    {
        return Err("installed smoke working directories must be outside the checkout".into());
    }

    let needs_installation = selected.iter().any(|name| !name.starts_with("cargo-"));
    let installation = if needs_installation {
        Some(installation(run)?)
    } else {
        None
    };
    run.run_cases(&selected, jobs, |name, case| {
        if name.starts_with("cargo-") {
            cargo_case(name, case)
        } else {
            let root = installation
                .as_deref()
                .expect("installation selected above");
            match name {
                "bundled-cargo-check" => bundled_cargo_case(case, root),
                "lean-file" => lean_case(case, root, jobs),
                "driver-callback" => driver_case(case, root),
                "rustdoc-html" => rustdoc_case(case, root),
                "audit-accepted" | "audit-rejected" | "audit-missing-lean" => {
                    audit_case(name, case, root)
                }
                _ => Err(format!("unknown installed case {name}")),
            }
        }
    })
}

fn installation(run: &RunDirectory) -> TestResult<PathBuf> {
    match (
        env::var_os("ANNEAL_TEST_ARCHIVE"),
        env::var_os("ANNEAL_TEST_INSTALL_ROOT"),
    ) {
        (Some(_), Some(_)) => {
            Err("supply only ANNEAL_TEST_ARCHIVE or ANNEAL_TEST_INSTALL_ROOT".into())
        }
        (None, None) => {
            Err("selected cases require ANNEAL_TEST_ARCHIVE or ANNEAL_TEST_INSTALL_ROOT".into())
        }
        (None, Some(_)) => {
            let root = required_path("ANNEAL_TEST_INSTALL_ROOT")?;
            write_json(
                &run.path().join("installation.json"),
                &json!({
                    "mode": "explicit-existing-installation",
                    "root": root,
                }),
            )?;
            Ok(root)
        }
        (Some(_), None) => {
            let archive = required_path("ANNEAL_TEST_ARCHIVE")?;
            let mut startup = run.case("installation")?;
            let mut command = Invocation::new(
                env::current_exe().map_err(|error| error.to_string())?,
                &[
                    "--exact",
                    "install_archive_worker",
                    "--ignored",
                    "--nocapture",
                ],
            );
            command
                .environment
                .insert("ANNEAL_TEST_ARCHIVE".into(), text_path(&archive)?);
            command.environment.insert(
                "ANNEAL_TEST_INSTALL_DEST".into(),
                text_path(&run.path().join("installation"))?,
            );
            startup.run(&command)?.expect_code(0)?;
            let root = PathBuf::from(
                fs::read_to_string(startup.path().join("installed-root.txt"))
                    .map_err(|error| format!("read fresh installation root: {error}"))?,
            );
            if !root.starts_with(run.path()) || !root.is_dir() {
                return Err(format!(
                    "installer did not return a test-owned installation: {}",
                    root.display()
                ));
            }
            write_json(
                &run.path().join("installation.json"),
                &json!({
                    "mode": "fresh-local-archive",
                    "archive": archive,
                    "root": root,
                }),
            )?;
            Ok(root)
        }
    }
}

// Installation runs in a child so archive extraction also has a process
// deadline. Location::Custom prevents an older user-global installation from
// satisfying a test of a newly supplied archive.
#[test]
#[ignore = "internal archive-install subprocess"]
fn install_archive_worker() {
    let archive = required_path("ANNEAL_TEST_ARCHIVE").unwrap();
    let destination = env::var_os("ANNEAL_TEST_INSTALL_DEST").unwrap();
    let root = setup::install_at(
        Some(archive),
        exocrate::Location::Custom(destination.into()),
    )
    .expect("install run's local archive in fresh test-owned storage");
    fs::write("installed-root.txt", text_path(&root).unwrap()).unwrap();
}

fn cargo_case(name: &str, case: &mut CaseDirectory) -> TestResult {
    let cargo = required_path("ANNEAL_TEST_CARGO_ANNEAL")?;
    version(case, &cargo, "cargo-anneal")?;
    match name {
        "cargo-help" => {
            for arguments in [&["--help"][..], &["anneal", "--help"], &["setup", "--help"]] {
                let out = case.run(&Invocation::new(&cargo, arguments))?;
                out.expect_code(0)?;
                require_text(&out.stdout, "setup", &out)?;
            }
            Ok(())
        }
        "cargo-version" => {
            for arguments in [&["--version"][..], &["anneal", "--version"]] {
                let out = case.run(&Invocation::new(&cargo, arguments))?;
                out.expect_code(0)?;
                require_text(&out.stdout, "cargo-anneal", &out)?;
            }
            Ok(())
        }
        "cargo-arguments" => {
            let out = case.run(&Invocation::new(&cargo, &["unknown-scaffold-command"]))?;
            out.expect_code(2)?;
            require_text(&out.stderr, "unknown-scaffold-command", &out)
        }
        #[cfg(target_os = "linux")]
        "cargo-setup-invalid-archive" => cargo_setup_failure(case, &cargo),
        _ => Err(format!("unknown cargo case {name}")),
    }
}

#[cfg(target_os = "linux")]
fn write_test_archive(path: &Path, marker: &[u8]) -> TestResult {
    let file = fs::File::create(path)
        .map_err(|error| format!("create test archive {}: {error}", path.display()))?;
    let encoder =
        zstd::Encoder::new(file, 1).map_err(|error| format!("create zstd encoder: {error}"))?;
    let mut archive = tar::Builder::new(encoder);
    let mut header = tar::Header::new_gnu();
    header.set_size(marker.len() as u64);
    header.set_mode(0o644);
    header.set_cksum();
    archive
        .append_data(&mut header, "marker.txt", marker)
        .map_err(|error| format!("append marker to test archive: {error}"))?;
    archive
        .into_inner()
        .map_err(|error| format!("finish tar archive: {error}"))?
        .finish()
        .map_err(|error| format!("finish zstd archive: {error}"))?;
    Ok(())
}

#[cfg(target_os = "linux")]
fn run_local_setup(
    case: &mut CaseDirectory,
    cargo: &Path,
    cache: &Path,
    archive_arg: &str,
) -> TestResult<ProcessOutcome> {
    let mut command = Invocation::new(cargo, &["setup", "--local-archive", archive_arg]);
    // Exocrate's user-global location honors XDG_CACHE_HOME on Linux.
    command
        .environment
        .insert("XDG_CACHE_HOME".into(), text_path(cache)?);
    case.run(&command)
}

#[cfg(target_os = "linux")]
fn cargo_setup_failure(case: &mut CaseDirectory, cargo: &Path) -> TestResult {
    case.write("invalid.tar.zst", b"invalid local toolchain archive")?;
    let v1_archive = case.path().join("valid-v1.tar.zst");
    let v2_archive = case.path().join("valid-v2.tar.zst");
    write_test_archive(&v1_archive, b"installed smoke v1")?;
    write_test_archive(&v2_archive, b"installed smoke v2")?;

    let fresh_cache = case.path().join("fresh-cache");
    fs::create_dir(&fresh_cache).map_err(|error| format!("create fresh setup cache: {error}"))?;
    let fresh_fail = run_local_setup(case, cargo, &fresh_cache, "invalid.tar.zst")?;
    fresh_fail.expect_code(1)?;
    require_text(
        &fresh_fail.stderr,
        "error: failed to install Anneal toolchain:",
        &fresh_fail,
    )?;
    if !fresh_fail.stdout.is_empty() {
        return Err(format!(
            "failed setup unexpectedly wrote stdout: {}",
            fresh_fail.describe()
        ));
    }

    let cache = case.path().join("reinstall-cache");
    fs::create_dir(&cache).map_err(|error| format!("create reinstall cache: {error}"))?;
    let v1_out = run_local_setup(case, cargo, &cache, "valid-v1.tar.zst")?;
    v1_out.expect_code(0)?;
    let v1_stdout = String::from_utf8(v1_out.stdout.clone())
        .map_err(|error| format!("setup stdout is not UTF-8: {error}"))?;
    let installed_root = PathBuf::from(
        v1_stdout
            .trim_end()
            .strip_prefix("Installed Anneal toolchain at ")
            .ok_or_else(|| format!("unexpected setup output: {}", v1_out.describe()))?,
    );
    if !installed_root.starts_with(&cache) {
        return Err(format!(
            "setup installed outside XDG_CACHE_HOME: {}",
            installed_root.display()
        ));
    }
    if fs::read(installed_root.join("marker.txt")).ok().as_deref() != Some(b"installed smoke v1") {
        return Err("v1 archive marker missing after initial setup".into());
    }

    let v2_out = run_local_setup(case, cargo, &cache, "valid-v2.tar.zst")?;
    v2_out.expect_code(0)?;
    require_text(&v2_out.stdout, "Installed Anneal toolchain at ", &v2_out)?;
    if fs::read(installed_root.join("marker.txt")).ok().as_deref() != Some(b"installed smoke v2") {
        return Err("reinstall with new local archive did not replace existing toolchain".into());
    }

    for bad_arg in ["invalid.tar.zst", "missing.tar.zst"] {
        let out = run_local_setup(case, cargo, &cache, bad_arg)?;
        out.expect_code(1)?;
        require_text(
            &out.stderr,
            "error: failed to install Anneal toolchain:",
            &out,
        )?;
        if !out.stdout.is_empty() {
            return Err(format!(
                "failed reinstall ({bad_arg}) unexpectedly wrote stdout: {}",
                out.describe()
            ));
        }
        if fs::read(installed_root.join("marker.txt")).ok().as_deref()
            != Some(b"installed smoke v2")
        {
            return Err(format!(
                "failed reinstall ({bad_arg}) damaged existing installation"
            ));
        }
    }
    Ok(())
}

fn next_lean_header_token(
    bytes: &[u8],
    pos: &mut usize,
    module: &str,
) -> TestResult<Option<String>> {
    loop {
        while *pos < bytes.len() && bytes[*pos].is_ascii_whitespace() {
            *pos += 1;
        }
        if *pos >= bytes.len() {
            return Ok(None);
        }
        if bytes[*pos..].starts_with(b"--") {
            *pos += 2;
            while *pos < bytes.len() && bytes[*pos] != b'\n' {
                *pos += 1;
            }
            continue;
        }
        if bytes[*pos..].starts_with(b"/-") {
            *pos += 2;
            let mut depth = 1usize;
            while depth > 0 {
                if *pos + 1 >= bytes.len() {
                    return Err(format!("unclosed block comment in Lean header of {module}"));
                }
                if bytes[*pos..].starts_with(b"/-") {
                    depth += 1;
                    *pos += 2;
                } else if bytes[*pos..].starts_with(b"-/") {
                    depth -= 1;
                    *pos += 2;
                } else {
                    *pos += 1;
                }
            }
            continue;
        }
        break;
    }
    let start = *pos;
    while *pos < bytes.len()
        && !bytes[*pos].is_ascii_whitespace()
        && !bytes[*pos..].starts_with(b"--")
        && !bytes[*pos..].starts_with(b"/-")
    {
        *pos += 1;
    }
    let token = std::str::from_utf8(&bytes[start..*pos])
        .map_err(|error| format!("non-UTF-8 token in Lean header of {module}: {error}"))?;
    Ok(Some(token.to_owned()))
}

fn lean_header_imports(source: &str, module: &str) -> TestResult<Vec<String>> {
    let bytes = source.as_bytes();
    let mut pos = 0;
    let mut imports = Vec::new();
    let mut expecting_import_target = false;
    while let Some(token) = next_lean_header_token(bytes, &mut pos, module)? {
        if expecting_import_target {
            if token == "all" {
                continue;
            }
            if token.split('.').any(|seg| !is_lean_ident(seg)) {
                return Err(format!(
                    "unexpected import module name {token:?} in {module}"
                ));
            }
            imports.push(token);
            expecting_import_target = false;
        } else if token == "import" {
            expecting_import_target = true;
        } else if matches!(token.as_str(), "prelude" | "module" | "public" | "meta") {
            continue;
        } else {
            break;
        }
    }
    if expecting_import_target {
        return Err(format!("truncated import statement in header of {module}"));
    }
    Ok(imports)
}

fn resolve_packaged_lean_source(
    trusted_root: &Path,
    theory_root: &Path,
    module: &str,
) -> TestResult<(PathBuf, PathBuf)> {
    if module.split('.').any(|seg| !is_lean_ident(seg)) {
        return Err(format!("invalid packaged Lean module name {module:?}"));
    }
    let rel = PathBuf::from(format!("{}.lean", module.replace('.', "/")));
    let trusted_path = trusted_root.join(&rel);
    let theory_path = theory_root.join(&rel);
    match (trusted_path.is_file(), theory_path.is_file()) {
        (true, true) => Err(format!(
            "ambiguous packaged Lean module {module} in both trusted/lean and theory"
        )),
        (true, false) => Ok((trusted_root.to_path_buf(), trusted_path)),
        (false, true) => Ok((theory_root.to_path_buf(), theory_path)),
        (false, false) => Err(format!(
            "missing packaged Lean module source for {module} ({})",
            rel.display()
        )),
    }
}

fn lean_case(case: &mut CaseDirectory, root: &Path, jobs: usize) -> TestResult {
    let lean = root.join("lean/bin/lean");
    version(case, &lean, "Lean (version 4.34.1")?;
    case.copy(&root.join("share/anneal/trusted/lean"), "trusted/lean")?;
    case.copy(&root.join("share/anneal/theory"), "theory")?;

    let trusted_root = case.path().join("trusted/lean");
    let theory_root = case.path().join("theory");
    let mut sources: BTreeMap<String, (PathBuf, PathBuf)> = BTreeMap::new();
    let mut imports_map: BTreeMap<String, Vec<ImportEdge>> = BTreeMap::new();
    let mut queue = VecDeque::from([String::from("Anneal")]);
    while let Some(module) = queue.pop_front() {
        if sources.contains_key(&module) {
            continue;
        }
        let (root_dir, src_path) =
            resolve_packaged_lean_source(&trusted_root, &theory_root, &module)?;
        let content = fs::read_to_string(&src_path)
            .map_err(|error| format!("read {}: {error}", src_path.display()))?;
        let raw_imports = lean_header_imports(&content, &module)?;
        let mut edges = Vec::with_capacity(raw_imports.len());
        for dep in raw_imports {
            let is_init = dep == "Init" || dep.starts_with("Init.");
            let is_packaged = dep == "Trusted"
                || dep.starts_with("Trusted.")
                || dep == "Anneal"
                || dep.starts_with("Anneal.");
            if !is_init && !is_packaged {
                return Err(format!(
                    "unexpected non-Init/Trusted/Anneal import {dep} in {module}"
                ));
            }
            if is_packaged && !sources.contains_key(&dep) {
                queue.push_back(dep.clone());
            }
            edges.push(ImportEdge {
                module: dep,
                import_all: false,
                is_exported: true,
                is_meta: false,
            });
        }
        sources.insert(module.clone(), (root_dir, src_path));
        imports_map.insert(module, edges);
    }

    let pending: BTreeSet<String> = sources.keys().cloned().collect();
    let order = topo_sort_modules(
        pending,
        &imports_map,
        "import cycle in packaged Anneal Lean sources",
    )
    .map_err(|error| error.to_string())?;
    let plan = ParallelDagPlan::from_module_order(
        &order,
        &imports_map,
        "lean-file",
        "import cycle in packaged Anneal Lean sources",
    )
    .map_err(|error| error.to_string())?;

    let lean_lib = case.path().join("lean-lib");
    fs::create_dir(&lean_lib).map_err(|error| format!("create lean-lib: {error}"))?;
    for module in &order {
        let olean = lean_lib.join(format!("{}.olean", module.replace('.', "/")));
        if let Some(parent) = olean.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("create {}: {error}", parent.display()))?;
        }
    }

    let lean_path_env = text_path(&lean_lib)?;
    let shared_case = &*case;
    let mut shared = ();
    run_parallel_dag(
        &plan,
        jobs,
        "lean-file",
        "packaged Lean compile worker panicked",
        &mut shared,
        |_, idx| Ok(idx),
        |_, idx| {
            let module = &order[idx];
            let (root_dir, src_path) = &sources[module];
            let olean_out = lean_lib.join(format!("{}.olean", module.replace('.', "/")));
            let mut command = Invocation::new(
                &lean,
                &[
                    "-j1",
                    "-DElab.async=false",
                    "-Ddebug.skipKernelTC=false",
                    "-R",
                    &text_path(root_dir).map_err(|e| Failure::operational("lean-file", e))?,
                    "-o",
                    &text_path(&olean_out).map_err(|e| Failure::operational("lean-file", e))?,
                    &text_path(src_path).map_err(|e| Failure::operational("lean-file", e))?,
                ],
            );
            command
                .environment
                .insert("LEAN_PATH".into(), lean_path_env.clone());
            let out = shared_case
                .run_shared(&command)
                .map_err(|e| Failure::operational("lean-file", e))?;
            out.expect_code(0)
                .map_err(|e| Failure::operational("lean-file", e))
        },
        |_, _, ()| Ok(()),
    )
    .map_err(|error| error.to_string())?;

    for required in ["Trusted.olean", "Anneal.olean"] {
        if !lean_lib.join(required).is_file() {
            return Err(format!("missing compiled packaged module {required}"));
        }
    }

    case.write(
        "Small.lean",
        b"prelude\nimport Anneal\n\n\
          example (c : Trusted.MirSemantics.Crate) : Prop :=\n\
          \x20 Trusted.MirSemantics.CrateTheorem c\n\n\
          example := @Anneal.MirWp.wpProg\n\
          example := @Anneal.MirWp.wellFormed_and_spec_of_wp\n\
          example := @Anneal.PureLift.mirBitWidth\n\
          example := @Anneal.LoopInv.wpUntil\n\
          example := @Anneal.MirTotal.wpProg_of_evalMirFuelTotal\n",
    )?;
    let mut small = Invocation::new(
        &lean,
        &[
            "-j1",
            "-DElab.async=false",
            "-Ddebug.skipKernelTC=false",
            "-DwarningAsError=true",
            "-R",
            &text_path(case.path())?,
            "Small.lean",
        ],
    );
    small.environment.insert("LEAN_PATH".into(), lean_path_env);
    let out = case.run(&small)?;
    out.expect_code(0)
}

// The explicit workspace boundary below keeps Cargo from discovering an
// ancestor workspace when a user places retained evidence inside one.
fn bundled_cargo_case(case: &mut CaseDirectory, root: &Path) -> TestResult {
    let cargo = root.join("rust/bin/cargo");
    version(case, &cargo, "cargo ")?;
    case.write(
        "fixture/Cargo.toml",
        b"[package]\nname = \"installed_probe\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\n[workspace]\n",
    )?;
    case.write(
        "fixture/src/lib.rs",
        b"pub fn identity(n: u32) -> u32 { n }\n",
    )?;
    let cargo_home = case.path().join("cargo-home");
    fs::create_dir(&cargo_home).map_err(|error| format!("create owned Cargo home: {error}"))?;
    let target = case.path().join("target");
    let mut command = Invocation::new(
        &cargo,
        &[
            "check",
            "--offline",
            "--manifest-path",
            &text_path(&case.path().join("fixture/Cargo.toml"))?,
            "--target-dir",
            &text_path(&target)?,
        ],
    );
    // Cargo must use this installation and this case's empty cache even when
    // the host has a different Rust toolchain or populated Cargo home.
    for (name, path) in [
        ("RUSTC", root.join("rust/bin/rustc")),
        ("RUSTDOC", root.join("rust/bin/rustdoc")),
        ("CARGO_HOME", cargo_home),
    ] {
        command.environment.insert(name.into(), text_path(&path)?);
    }
    let out = case.run(&command)?;
    out.expect_code(0)?;
    let dependencies = fs::read_dir(target.join("debug/deps"))
        .map_err(|error| format!("read checked crate outputs: {error}"))?;
    for entry in dependencies {
        let path = entry
            .map_err(|error| format!("read checked crate output: {error}"))?
            .path();
        if path
            .extension()
            .is_some_and(|extension| extension == "rmeta")
            && path
                .file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with("libinstalled_probe-")
            && fs::metadata(&path)
                .map_err(|error| format!("inspect checked metadata: {error}"))?
                .len()
                > 0
        {
            return Ok(());
        }
    }
    Err("bundled Cargo check did not create nonempty crate metadata".into())
}

// A version banner does not exercise the documentation backend. Require the
// crate page and its linked function page from this installation as well.
fn rustdoc_case(case: &mut CaseDirectory, root: &Path) -> TestResult {
    let rustdoc = root.join("rust/bin/rustdoc");
    version(case, &rustdoc, "rustdoc ")?;
    case.write(
        "small.rs",
        b"//! Installed documentation probe.\npub fn identity(n: u32) -> u32 { n }\n",
    )?;
    let documentation = case.path().join("documentation");
    let out = case.run(&Invocation::new(
        &rustdoc,
        &[
            "--sysroot",
            &text_path(&root.join("rust"))?,
            "--crate-name=installed_probe",
            "--crate-type=lib",
            "--edition=2024",
            "--out-dir",
            &text_path(&documentation)?,
            "small.rs",
        ],
    ))?;
    out.expect_code(0)?;
    let index = fs::read(documentation.join("installed_probe/index.html"))
        .map_err(|error| format!("read generated documentation: {error}"))?;
    require_text(&index, "Installed documentation probe.", &out)?;
    require_text(&index, "fn.identity.html", &out)?;
    if !documentation
        .join("installed_probe/fn.identity.html")
        .is_file()
    {
        return Err("rustdoc did not create the function documentation".into());
    }
    Ok(())
}

fn driver_case(case: &mut CaseDirectory, root: &Path) -> TestResult {
    let driver = root.join("bin/anneal-rustc-capture");
    version(case, &root.join("rust/bin/rustc"), "rustc ")?;
    version(case, &driver, "anneal-rustc-capture")?;
    case.write(
        "small.rs",
        b"pub fn increment(n: u32) -> u32 { n.wrapping_add(1) }\n",
    )?;
    let sysroot = text_path(&root.join("rust"))?;
    let out = case.run(&Invocation::new(
        &driver,
        &[
            "--sysroot",
            &sysroot,
            "--crate-type=lib",
            "--emit=metadata",
            "--edition=2024",
            "small.rs",
            "-o",
            "small.rmeta",
        ],
    ))?;
    out.expect_code(0)?;
    require_text(
        &out.stderr,
        "note: anneal-rustc-capture: compiler analysis callback reached; verification not performed",
        &out,
    )?;
    if !out.stdout.is_empty() {
        return Err(format!(
            "metadata compilation unexpectedly wrote stdout: {}",
            out.describe()
        ));
    }
    if !case.path().join("small.rmeta").is_file() {
        return Err("driver callback case did not create Rust metadata".into());
    }
    Ok(())
}

fn audit_case(name: &str, case: &mut CaseDirectory, root: &Path) -> TestResult {
    let auditor = required_path("ANNEAL_TEST_AUDITOR")?;
    let lean = root.join("lean/bin/lean");
    version(case, &auditor, "anneal-audit")?;
    if name != "audit-missing-lean" {
        version(case, &lean, "Lean (version 4.34.1")?;
    }
    case.copy(
        &root.join("share/anneal/trusted/lean/lean-toolchain"),
        "fixture/trusted/lean/lean-toolchain",
    )?;
    case.copy(
        &root.join("share/anneal/trusted/lean/foundation-lock.json"),
        "fixture/trusted/lean/foundation-lock.json",
    )?;
    for file in ["TrustedBoundary.lean", "library-lock.json"] {
        case.copy(
            &root.join("share/anneal/trusted/audit").join(file),
            format!("fixture/trusted/audit/{file}"),
        )?;
    }
    let source = if name == "audit-rejected" {
        // This is the existing boundary suite's surface-sorry rejection. Check
        // the policy phase and execution gate, not an arbitrary nonzero exit.
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\ntheorem bad : False := by sorry\n"
    } else {
        include_str!("fixtures/audit-positive.lean")
    };
    case.write("fixture/trusted/lean/Trusted.lean", source.as_bytes())?;
    if name == "audit-accepted" {
        case.copy(
            &root.join("share/anneal/trusted/lean/Trusted"),
            "fixture/trusted/lean/Trusted",
        )?;
        case.copy(
            &root.join("share/anneal/theory/Anneal/NatBitwise.lean"),
            "fixture/theory/Anneal/NatBitwise.lean",
        )?;
        case.copy(
            &root.join("share/anneal/theory/Anneal/MirWp.lean"),
            "fixture/theory/Anneal/MirWp.lean",
        )?;
        case.copy(
            &root.join("share/anneal/theory/Anneal/MirWp"),
            "fixture/theory/Anneal/MirWp",
        )?;
        case.write(
            "fixture/theory/Anneal.lean",
            b"module\nprelude\npublic import Init.NotationExtra\npublic import Trusted\npublic import Anneal.MirWp\n",
        )?;
    }
    let requested_lean = if name == "audit-missing-lean" {
        case.path().join("absent-lean")
    } else {
        lean
    };
    let lean_arg = text_path(&requested_lean)?;
    let fixture_arg = text_path(&case.path().join("fixture"))?;
    let out = case.run(&Invocation::new(
        &auditor,
        &["--lean", &lean_arg, "--anneal-root", &fixture_arg, "--json"],
    ))?;
    match name {
        "audit-accepted" => {
            out.expect_code(0)?;
            let report: Value = serde_json::from_slice(&out.stdout).map_err(|error| {
                format!("read accepted audit report: {error}; {}", out.describe())
            })?;
            if report["replay"] != true || report["kernelDeclarations"].as_u64().unwrap_or(0) < 30 {
                return Err(format!(
                    "positive fixture did not reach kernel replay: {report}"
                ));
            }
            Ok(())
        }
        "audit-rejected" => {
            out.expect_code(1)?;
            require_text(&out.stderr, "Trusted check failed (preflight)", &out)?;
            require_text(&out.stderr, "Target execution began: false", &out)
        }
        "audit-missing-lean" => {
            out.expect_code(2)?;
            require_text(&out.stderr, "Trusted check failed (toolchain)", &out)?;
            require_text(&out.stderr, "absent-lean", &out)
        }
        _ => Err(format!("unknown audit case {name}")),
    }
}

fn version(case: &mut CaseDirectory, tool: &Path, expected: &str) -> TestResult {
    let out = case.run(&Invocation::new(tool, &["--version"]))?;
    out.expect_code(0)?;
    require_text(&out.stdout, expected, &out)
}

fn require_text(bytes: &[u8], expected: &str, outcome: &ProcessOutcome) -> TestResult {
    if String::from_utf8_lossy(bytes).contains(expected) {
        Ok(())
    } else {
        Err(format!(
            "expected output {expected:?}: {}",
            outcome.describe()
        ))
    }
}

fn text_path(path: &Path) -> TestResult<String> {
    path.to_str()
        .map(str::to_owned)
        .ok_or_else(|| format!("test artifact path is not UTF-8: {}", path.display()))
}

fn required_path(name: &str) -> TestResult<PathBuf> {
    let value = env::var_os(name).ok_or_else(|| format!("selected case requires {name}"))?;
    let path = PathBuf::from(value);
    if !path.is_absolute() {
        return Err(format!(
            "{name} must be an absolute path: {}",
            path.display()
        ));
    }
    if !path.exists() {
        return Err(format!("{name} does not exist: {}", path.display()));
    }
    Ok(path)
}

fn setting(name: &str, default: usize, maximum: usize) -> TestResult<usize> {
    let Some(value) = env::var_os(name) else {
        return Ok(default);
    };
    let parsed = value
        .to_str()
        .and_then(|text| text.parse::<usize>().ok())
        .filter(|number| (1..=maximum).contains(number));
    parsed.ok_or_else(|| format!("{name} must be an integer in 1..={maximum}, got {value:?}"))
}
