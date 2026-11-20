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
//! `ANNEAL_TEST_CARGO_ANNEAL`, `ANNEAL_TEST_AUDITOR`, and
//! `ANNEAL_TEST_INSPECTOR` for selected cases. `ANNEAL_TEST_ARCHIVE` makes a
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

#[allow(dead_code)]
#[path = "../src/setup.rs"]
mod setup;
mod support;

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

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
        "ANNEAL_TEST_INSPECTOR",
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
                "lean-file" => lean_case(case, root),
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
fn cargo_setup_failure(case: &mut CaseDirectory, cargo: &Path) -> TestResult {
    case.write("invalid.tar.zst", b"invalid local toolchain archive")?;
    let cache = case.path().join("cache");
    fs::create_dir(&cache).map_err(|error| format!("create fresh setup cache: {error}"))?;
    let mut command = Invocation::new(cargo, &["setup", "--local-archive", "invalid.tar.zst"]);
    // Exocrate's user-global location honors XDG_CACHE_HOME on Linux. A
    // fresh child cache prevents an existing installation from hiding failure.
    command
        .environment
        .insert("XDG_CACHE_HOME".into(), text_path(&cache)?);
    let out = case.run(&command)?;
    out.expect_code(1)?;
    require_text(
        &out.stderr,
        "error: failed to install Anneal toolchain:",
        &out,
    )?;
    if !out.stdout.is_empty() {
        return Err(format!(
            "failed setup unexpectedly wrote stdout: {}",
            out.describe()
        ));
    }
    Ok(())
}

fn lean_case(case: &mut CaseDirectory, root: &Path) -> TestResult {
    let lean = root.join("lean/bin/lean");
    version(case, &lean, "Lean (version 4.34.1")?;
    case.copy(
        &root.join("share/anneal/trusted/lean/lean-toolchain"),
        "toolchain/lean-toolchain",
    )?;
    case.write("Small.lean", b"example (n : Nat) : n = n := rfl\n")?;
    let out = case.run(&Invocation::new(&lean, &["Small.lean"]))?;
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
    let inspector = required_path("ANNEAL_TEST_INSPECTOR")?;
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
    case.copy(&inspector, "fixture/trusted/audit/TrustedBoundary.lean")?;
    let source = if name == "audit-rejected" {
        // This is the existing boundary suite's surface-sorry rejection. Check
        // the policy phase and execution gate, not an arbitrary nonzero exit.
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\ntheorem bad : False := by sorry\n"
    } else {
        include_str!("fixtures/audit-positive.lean")
    };
    case.write("fixture/trusted/lean/Trusted.lean", source.as_bytes())?;
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
