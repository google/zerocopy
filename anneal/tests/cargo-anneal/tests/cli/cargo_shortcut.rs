// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The Cargo-mode shortcut: source namespace, overwrite handling, target
//! paths, and `CARGO_HOME`.

use super::*;

#[test]
fn cargo_shortcut_declares_only_its_documented_source_namespace() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let package = project.path().join("package");
    fs::create_dir_all(package.join("src")).unwrap();
    fs::create_dir(package.join("proof")).unwrap();
    fs::create_dir(package.join(".hidden")).unwrap();
    fs::create_dir(package.join("target")).unwrap();
    fs::create_dir(package.join("benches")).unwrap();
    fs::create_dir(package.join("tests")).unwrap();
    fs::create_dir(package.join("examples")).unwrap();
    fs::write(
        package.join("Cargo.toml"),
        "[package]\nname = \"source_namespace\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
         [features]\ndefault = [\"std\"]\nstd = []\ni128 = []\n\n\
         [dev-dependencies]\nquickcheck = { path = \"../unused-dev\" }\n",
    )
    .unwrap();
    fs::create_dir_all(project.path().join("unused-dev/src")).unwrap();
    fs::write(
        project.path().join("unused-dev/Cargo.toml"),
        "[package]\nname = \"quickcheck\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(project.path().join("unused-dev/src/lib.rs"), b"").unwrap();
    fs::write(package.join("src/lib.rs"), b"pub fn zero() -> u64 { include!(\"zero.inc\") }\n")
        .unwrap();
    fs::write(package.join("src/unused.rs"), b"unused declared input\n").unwrap();
    fs::write(package.join("src/zero.inc"), b"0u64\n").unwrap();
    fs::write(package.join(".hidden/ignored.rs"), b"not a shortcut input\n").unwrap();
    fs::write(package.join("target/ignored.rs"), b"not a shortcut input\n").unwrap();
    fs::write(package.join("benches/bench.rs"), b"not a shortcut input\n").unwrap();
    fs::write(package.join("tests/it.rs"), b"not a shortcut input\n").unwrap();
    fs::write(package.join("examples/demo.rs"), b"not a shortcut input\n").unwrap();
    fs::write(package.join("proof/Spec.lean"), b"not compiled by this check\n").unwrap();
    let evidence = project.path().join("evidence");
    // A missing capture tool stops after request construction and staging,
    // so this checks actual shortcut inventory without compiling the fixture.
    let mut child = command(Route::Direct, project.path());
    let mut paths = vec![Path::new(env!("CARGO")).parent().unwrap().to_path_buf()];
    if let Some(path) = env::var_os("PATH") {
        paths.extend(env::split_paths(&path));
    }
    child
        .env("PATH", env::join_paths(paths).unwrap())
        .args(["verify", "--format", "json"])
        .arg("--manifest-path")
        .arg(package.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(package.join("proof"))
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--sysroot")
        .arg(project.path())
        .arg("--artifacts")
        .arg(&evidence);
    #[cfg(not(feature = "setup"))]
    child.arg("--lean").arg(project.path().join("missing-lean"));
    let output = child.output().unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 3);
    assert_eq!(receipt["taint_reasons"], serde_json::json!([]));
    assert_eq!(receipt["phase"], "capture-tool", "{receipt}");
    let request: serde_json::Value =
        serde_json::from_slice(&fs::read(evidence.join("request.json")).unwrap()).unwrap();
    assert_eq!(
        request["compilation"]["source_files"],
        serde_json::json!(["src/lib.rs", "src/unused.rs"])
    );
    assert_eq!(
        request["compilation"]["cfg"],
        serde_json::json!(["feature=\"default\"", "feature=\"std\""])
    );
    assert!(!evidence.join("rust/src/zero.inc").exists());
    assert!(!evidence.join("rust/.hidden").exists());
    assert!(!evidence.join("rust/target").exists());
    assert!(!evidence.join("rust/benches").exists());
    assert!(!evidence.join("rust/tests").exists());
    assert!(!evidence.join("rust/examples").exists());
    assert!(!evidence.join("rust/proof").exists());
}

fn run_cargo_shortcut_probe(
    project: &Path,
    package: &Path,
    evidence: &Path,
    extra_args: &[&str],
) -> (std::process::Output, serde_json::Value) {
    let mut child = command(Route::Direct, project);
    let mut paths = vec![Path::new(env!("CARGO")).parent().unwrap().to_path_buf()];
    if let Some(path) = env::var_os("PATH") {
        paths.extend(env::split_paths(&path));
    }
    child
        .env("PATH", env::join_paths(paths).unwrap())
        .args(["verify", "--format", "json"])
        .arg("--manifest-path")
        .arg(package.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(package.join("proof"))
        .args(extra_args)
        .arg("--capture")
        .arg(project.join("missing-capture"))
        .arg("--sysroot")
        .arg(project)
        .arg("--artifacts")
        .arg(evidence);
    #[cfg(not(feature = "setup"))]
    child.arg("--lean").arg(project.join("missing-lean"));
    let output = child.output().unwrap();
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    (output, receipt)
}

/// A Cargo-shortcut rerun with `--overwrite-artifacts` leaves an artifact
/// directory inside the package or proof directory out of source discovery,
/// instead of refusing to replace its own staged copies, yet still refuses
/// a Cargo target root inside that directory.
#[test]
fn cargo_shortcut_overwrite_skips_its_own_artifacts() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let package = project.path().join("package");
    fs::create_dir_all(package.join("src")).unwrap();
    fs::create_dir(package.join("proof")).unwrap();
    let manifest = "[package]\nname = \"rerun\"\nversion = \"0.1.0\"\nedition = \"2024\"\n";
    fs::write(package.join("Cargo.toml"), manifest).unwrap();
    fs::write(package.join("src/lib.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    fs::write(package.join("proof/Spec.lean"), b"-- not compiled by this check\n").unwrap();
    for evidence in [package.join("proof/out"), package.join("out")] {
        for run in 0..2 {
            let (output, receipt) = run_cargo_shortcut_probe(
                project.path(),
                &package,
                &evidence,
                &["--overwrite-artifacts"],
            );
            assert_result(&output, 2, "", "");
            assert_eq!(receipt["phase"], "capture-tool", "run {run}: {receipt}");
            let request: serde_json::Value =
                serde_json::from_slice(&fs::read(evidence.join("request.json")).unwrap()).unwrap();
            assert_eq!(request["compilation"]["source_files"], serde_json::json!(["src/lib.rs"]));
            let modules: Vec<_> = request["proof"]["sources"]
                .as_array()
                .unwrap()
                .iter()
                .map(|source| source["module"].as_str().unwrap().to_owned())
                .collect();
            assert_eq!(modules, ["Spec"], "{request}");
            assert!(evidence.join("rust/src/lib.rs").is_file());
            // A Lean file left in an earlier run's evidence is no proof input.
            fs::create_dir_all(evidence.join("authored")).unwrap();
            fs::write(evidence.join("authored/Stale.lean"), b"-- earlier copy\n").unwrap();
        }
        // Any other directory in the package is ordinary source discovery.
        if evidence.starts_with(package.join("proof")) {
            fs::remove_dir_all(&evidence).unwrap();
        }
    }

    // A target root inside the destination is a verification input.
    let out = package.join("out");
    fs::write(
        package.join("Cargo.toml"),
        format!("{manifest}\n[lib]\npath = \"out/rust/src/lib.rs\"\n"),
    )
    .unwrap();
    let (output, receipt) =
        run_cargo_shortcut_probe(project.path(), &package, &out, &["--overwrite-artifacts"]);
    assert_result(&output, 2, "", "");
    assert_eq!(receipt["phase"], "retention", "{receipt}");
    assert!(receipt["detail"].as_str().unwrap().contains("verification input"), "{receipt}");
    assert_eq!(fs::read(out.join("rust/src/lib.rs")).unwrap(), b"pub fn zero() -> u64 { 0 }\n");
}

/// Before it modifies an existing `--overwrite-artifacts` destination, a
/// Cargo-mode run refuses one that holds the root of any package target,
/// and one whose package targets it cannot list, even when the run would
/// fail early anyway (here: a missing `--proof-dir`).
#[test]
fn cargo_overwrite_refuses_destinations_holding_any_target_root() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let package = project.path().join("package");
    let out = package.join("out");
    let header = "[package]\nname = \"targets\"\nversion = \"0.1.0\"\nedition = \"2024\"\n";
    let lib = b"pub fn zero() -> u64 { 0 }\n";
    for (manifest, config, expected) in [
        ("[lib]\npath = \"out/rust/src/lib.rs\"\n", None, "verification input"),
        ("[lib]\npath = \"out/lean-lib/lib.rs\"\n", None, "verification input"),
        (
            "[[bin]]\nname = \"extra\"\npath = \"out/rust/src/main.rs\"\n",
            None,
            "verification input",
        ),
        ("", Some("[build]\nrustflags = []\n"), "cannot list the Cargo targets"),
    ] {
        let _ = fs::remove_dir_all(&package);
        fs::create_dir_all(package.join("src")).unwrap();
        fs::create_dir_all(out.join("rust/src")).unwrap();
        fs::create_dir_all(out.join("lean-lib")).unwrap();
        fs::write(package.join("Cargo.toml"), format!("{header}\n{manifest}")).unwrap();
        fs::write(package.join("src/lib.rs"), lib).unwrap();
        fs::write(out.join(".cargo-anneal-artifacts"), "cargo-anneal verification artifacts\n")
            .unwrap();
        fs::write(out.join("result.json"), b"{\"status\":\"crate_verified\"}").unwrap();
        for file in ["rust/src/lib.rs", "rust/src/main.rs", "lean-lib/lib.rs"] {
            fs::write(out.join(file), lib).unwrap();
        }
        if let Some(config) = config {
            fs::create_dir(package.join(".cargo")).unwrap();
            fs::write(package.join(".cargo/config.toml"), config).unwrap();
        }
        let (output, receipt) =
            run_cargo_shortcut_probe(project.path(), &package, &out, &["--overwrite-artifacts"]);
        assert_result(&output, 2, "", "");
        assert_eq!(receipt["phase"], "retention", "{receipt}");
        assert!(receipt["detail"].as_str().unwrap().contains(expected), "{receipt}");
        assert_eq!(fs::read(out.join("result.json")).unwrap(), b"{\"status\":\"crate_verified\"}");
        for file in ["rust/src/lib.rs", "rust/src/main.rs", "lean-lib/lib.rs"] {
            assert_eq!(fs::read(out.join(file)).unwrap(), lib, "{file}");
        }
    }
}

#[test]
fn cargo_shortcut_handles_rlib_shared_target_paths_and_bin_required_features() {
    use std::fs;
    // 1. `[lib] crate-type = ["rlib"]` with a non-primary target outside
    // top-level `tests/`/`benches/`/`examples/` and a shared `[[test]]` path.
    let project = tempfile::tempdir().unwrap();
    let pkg_rlib = project.path().join("rlib-pkg");
    fs::create_dir_all(pkg_rlib.join("src")).unwrap();
    fs::create_dir(pkg_rlib.join("proof")).unwrap();
    fs::write(
        pkg_rlib.join("Cargo.toml"),
        "[package]\nname = \"rlib_pkg\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
         [lib]\ncrate-type = [\"rlib\"]\npath = \"src/lib.rs\"\n\n\
         [[bench]]\nname = \"custom_bench\"\npath = \"src/custom_bench.rs\"\n\n\
         [[test]]\nname = \"shared_path\"\npath = \"src/lib.rs\"\n",
    )
    .unwrap();
    fs::write(pkg_rlib.join("src/lib.rs"), b"pub fn id(x: u64) -> u64 { x }\n").unwrap();
    fs::write(pkg_rlib.join("src/custom_bench.rs"), b"fn main() {}\n").unwrap();
    fs::write(pkg_rlib.join("proof/Spec.lean"), b"-- placeholder\n").unwrap();
    let ev_rlib = project.path().join("ev-rlib");
    let (out_rlib, rec_rlib) = run_cargo_shortcut_probe(project.path(), &pkg_rlib, &ev_rlib, &[]);
    assert_result(&out_rlib, 2, "", "");
    assert_eq!(rec_rlib["phase"], "capture-tool", "{rec_rlib}");
    let req_rlib: serde_json::Value =
        serde_json::from_slice(&fs::read(ev_rlib.join("request.json")).unwrap()).unwrap();
    assert_eq!(req_rlib["compilation"]["crate_type"], "lib");
    assert_eq!(req_rlib["compilation"]["source_files"], serde_json::json!(["src/lib.rs"]));

    // 2. Primary `[lib]` placed inside `tests/lib.rs` with Cargo autotests
    // enabled keeps `tests/lib.rs` while still filtering `tests/other.rs`.
    let pkg_tests_lib = project.path().join("tests-lib-pkg");
    fs::create_dir_all(pkg_tests_lib.join("tests")).unwrap();
    fs::create_dir(pkg_tests_lib.join("proof")).unwrap();
    fs::write(
        pkg_tests_lib.join("Cargo.toml"),
        "[package]\nname = \"tests_lib_pkg\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
         [lib]\npath = \"tests/lib.rs\"\n",
    )
    .unwrap();
    fs::write(pkg_tests_lib.join("tests/lib.rs"), b"pub fn one() -> u64 { 1 }\n").unwrap();
    fs::write(pkg_tests_lib.join("tests/other.rs"), b"#[test] fn t() {}\n").unwrap();
    fs::write(pkg_tests_lib.join("proof/Spec.lean"), b"-- placeholder\n").unwrap();
    let ev_tests_lib = project.path().join("ev-tests-lib");
    let (out_tl, rec_tl) =
        run_cargo_shortcut_probe(project.path(), &pkg_tests_lib, &ev_tests_lib, &[]);
    assert_result(&out_tl, 2, "", "");
    assert_eq!(rec_tl["phase"], "capture-tool", "{rec_tl}");
    let req_tl: serde_json::Value =
        serde_json::from_slice(&fs::read(ev_tests_lib.join("request.json")).unwrap()).unwrap();
    assert_eq!(req_tl["compilation"]["crate_root"], "tests/lib.rs");
    assert_eq!(req_tl["compilation"]["source_files"], serde_json::json!(["tests/lib.rs"]));

    // 3. `[[bin]]` with `required-features` fails closed unless enabled.
    let pkg_bin = project.path().join("bin-req-feat");
    fs::create_dir_all(pkg_bin.join("src")).unwrap();
    fs::create_dir(pkg_bin.join("proof")).unwrap();
    fs::write(
        pkg_bin.join("Cargo.toml"),
        "[package]\nname = \"bin_req\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
         [[bin]]\nname = \"bin_req\"\npath = \"src/main.rs\"\nrequired-features = [\"cli\"]\n\n\
         [features]\ncli = []\n",
    )
    .unwrap();
    fs::write(pkg_bin.join("src/main.rs"), b"fn main() {}\n").unwrap();
    fs::write(pkg_bin.join("proof/Spec.lean"), b"-- placeholder\n").unwrap();
    let ev_bin_fail = project.path().join("ev-bin-fail");
    let (out_bf, rec_bf) = run_cargo_shortcut_probe(project.path(), &pkg_bin, &ev_bin_fail, &[]);
    assert_result(&out_bf, 1, "", "");
    assert_eq!(rec_bf["status"], "unsupported", "{rec_bf}");
    assert_eq!(rec_bf["phase"], "cargo", "{rec_bf}");
    assert!(
        rec_bf["detail"].as_str().unwrap_or_default().contains("requires Cargo feature `cli`"),
        "{rec_bf}"
    );
    let ev_bin_ok = project.path().join("ev-bin-ok");
    let (out_bo, rec_bo) =
        run_cargo_shortcut_probe(project.path(), &pkg_bin, &ev_bin_ok, &["--features", "cli"]);
    assert_result(&out_bo, 2, "", "");
    assert_eq!(rec_bo["phase"], "capture-tool", "{rec_bo}");
}

#[cfg(unix)]
#[test]
fn cargo_shortcut_pins_resolved_cargo_home_for_metadata() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    let package = project.path().join("package");
    fs::create_dir_all(package.join("src")).unwrap();
    fs::create_dir(package.join("proof")).unwrap();
    fs::write(
        package.join("Cargo.toml"),
        "[package]\nname = \"homepin\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(package.join("src/lib.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    fs::write(package.join("proof/Spec.lean"), b"-- not compiled by this check\n").unwrap();

    let base_path = || {
        let mut paths = vec![Path::new(env!("CARGO")).parent().unwrap().to_path_buf()];
        if let Some(path) = env::var_os("PATH") {
            paths.extend(env::split_paths(&path));
        }
        paths
    };

    // (a) Empty `CARGO_HOME` with a `HOME` whose `.cargo/config.toml` has
    //     `[build]` fails closed before spawning `cargo metadata`.
    let bad_home = project.path().join("bad-home");
    fs::create_dir_all(bad_home.join(".cargo")).unwrap();
    fs::write(bad_home.join(".cargo/config.toml"), "[build]\nrustflags = []\n").unwrap();
    let mut home_cmd = command(Route::Direct, project.path());
    home_cmd
        .env("PATH", env::join_paths(base_path()).unwrap())
        .env("CARGO_HOME", "")
        .env("HOME", &bad_home)
        .args(["verify", "--format", "json", "--manifest-path"])
        .arg(package.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(package.join("proof"))
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--sysroot")
        .arg(project.path());
    #[cfg(not(feature = "setup"))]
    home_cmd.arg("--lean").arg(project.path().join("missing-lean"));
    let home_out = home_cmd.output().unwrap();
    assert_result(&home_out, 1, "", "");
    let home_rec: serde_json::Value = serde_json::from_slice(&home_out.stdout).unwrap();
    assert_eq!(home_rec["status"], "unsupported", "{home_rec}");
    assert_eq!(home_rec["phase"], "cargo", "{home_rec}");
    assert!(home_rec["detail"].as_str().unwrap_or("").contains("table [build]"), "{home_rec}");

    // (b) Relative `CARGO_HOME` containing `[build]` is refused regardless of
    //     `cargo metadata`'s isolated probe cwd.
    let rel_bad = project.path().join("rel-bad-cargo");
    fs::create_dir_all(&rel_bad).unwrap();
    fs::write(rel_bad.join("config.toml"), "[build]\nrustc-wrapper = \"/bin/false\"\n").unwrap();
    let mut rel_bad_cmd = command(Route::Direct, project.path());
    rel_bad_cmd
        .env("PATH", env::join_paths(base_path()).unwrap())
        .env("CARGO_HOME", "rel-bad-cargo")
        .args(["verify", "--format", "json", "--manifest-path"])
        .arg(package.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(package.join("proof"))
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--sysroot")
        .arg(project.path());
    #[cfg(not(feature = "setup"))]
    rel_bad_cmd.arg("--lean").arg(project.path().join("missing-lean"));
    let rel_bad_out = rel_bad_cmd.output().unwrap();
    assert_result(&rel_bad_out, 1, "", "");
    let rel_bad_rec: serde_json::Value = serde_json::from_slice(&rel_bad_out.stdout).unwrap();
    assert_eq!(rel_bad_rec["status"], "unsupported", "{rel_bad_rec}");
    assert_eq!(rel_bad_rec["phase"], "cargo", "{rel_bad_rec}");
    assert!(
        rel_bad_rec["detail"].as_str().unwrap_or("").contains("table [build]"),
        "{rel_bad_rec}"
    );

    // (c) `cargo metadata` receives the exact absolutized `CARGO_HOME` that
    //     was inspected (for both relative `CARGO_HOME` and `HOME` fallback).
    let bin_dir = project.path().join("wrap-bin");
    fs::create_dir_all(&bin_dir).unwrap();
    let seen_file = project.path().join("cargo_home_seen.txt");
    let cargo_wrap = bin_dir.join("cargo");
    let wrap_script = format!(
        "#!/bin/sh\nprintf '%s' \"$CARGO_HOME\" > \"{}\"\nexec \"{}\" \"$@\"\n",
        seen_file.display(),
        env!("CARGO")
    );
    fs::write(&cargo_wrap, wrap_script).unwrap();
    fs::set_permissions(&cargo_wrap, fs::Permissions::from_mode(0o755)).unwrap();

    let mut wrap_paths = vec![bin_dir];
    wrap_paths.extend(base_path());
    let wrap_path_env = env::join_paths(wrap_paths).unwrap();

    let rel_ok = project.path().join("rel-ok-cargo");
    fs::create_dir_all(&rel_ok).unwrap();
    fs::write(rel_ok.join("config.toml"), "[net]\nretry = 1\n").unwrap();
    let mut rel_ok_cmd = command(Route::Direct, project.path());
    rel_ok_cmd
        .env("PATH", &wrap_path_env)
        .env("CARGO_HOME", "rel-ok-cargo")
        .args(["verify", "--format", "json", "--manifest-path"])
        .arg(package.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(package.join("proof"))
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--sysroot")
        .arg(project.path());
    #[cfg(not(feature = "setup"))]
    rel_ok_cmd.arg("--lean").arg(project.path().join("missing-lean"));
    let rel_ok_out = rel_ok_cmd.output().unwrap();
    assert_result(&rel_ok_out, 2, "", "");
    let rel_ok_rec: serde_json::Value = serde_json::from_slice(&rel_ok_out.stdout).unwrap();
    assert_eq!(rel_ok_rec["phase"], "capture-tool", "{rel_ok_rec}");
    let expected_rel = fs::canonicalize(&rel_ok).unwrap();
    let observed_rel = fs::canonicalize(fs::read_to_string(&seen_file).unwrap()).unwrap();
    assert_eq!(observed_rel, expected_rel);

    let ok_home = project.path().join("ok-home");
    fs::create_dir_all(ok_home.join(".cargo")).unwrap();
    fs::write(ok_home.join(".cargo/config.toml"), "[net]\nretry = 2\n").unwrap();
    let mut ok_home_cmd = command(Route::Direct, project.path());
    ok_home_cmd
        .env("PATH", &wrap_path_env)
        .env("CARGO_HOME", "")
        .env("HOME", &ok_home)
        .args(["verify", "--format", "json", "--manifest-path"])
        .arg(package.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(package.join("proof"))
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--sysroot")
        .arg(project.path());
    #[cfg(not(feature = "setup"))]
    ok_home_cmd.arg("--lean").arg(project.path().join("missing-lean"));
    let ok_home_out = ok_home_cmd.output().unwrap();
    assert_result(&ok_home_out, 2, "", "");
    let ok_home_rec: serde_json::Value = serde_json::from_slice(&ok_home_out.stdout).unwrap();
    assert_eq!(ok_home_rec["phase"], "capture-tool", "{ok_home_rec}");
    let expected_home = fs::canonicalize(ok_home.join(".cargo")).unwrap();
    let observed_home = fs::canonicalize(fs::read_to_string(&seen_file).unwrap()).unwrap();
    assert_eq!(observed_home, expected_home);

    // (d) A symlinked `CARGO_HOME` directory fails closed like `.cargo`.
    let sym_cargo_home = project.path().join("sym-cargo-home");
    std::os::unix::fs::symlink(&rel_ok, &sym_cargo_home).unwrap();
    let mut sym_cmd = command(Route::Direct, project.path());
    sym_cmd
        .env("PATH", &wrap_path_env)
        .env("CARGO_HOME", &sym_cargo_home)
        .args(["verify", "--format", "json", "--manifest-path"])
        .arg(package.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(package.join("proof"))
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--sysroot")
        .arg(project.path());
    #[cfg(not(feature = "setup"))]
    sym_cmd.arg("--lean").arg(project.path().join("missing-lean"));
    let sym_out = sym_cmd.output().unwrap();
    assert_result(&sym_out, 1, "", "");
    let sym_rec: serde_json::Value = serde_json::from_slice(&sym_out.stdout).unwrap();
    assert_eq!(sym_rec["status"], "unsupported", "{sym_rec}");
    assert_eq!(sym_rec["phase"], "cargo", "{sym_rec}");
    assert!(
        sym_rec["detail"].as_str().unwrap_or("").contains("not a regular directory"),
        "{sym_rec}"
    );
}
