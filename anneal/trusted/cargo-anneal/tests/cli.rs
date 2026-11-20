// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Command behavior through direct invocation and Cargo's subcommand dispatch.

use std::env;
use std::path::Path;
use std::process::{Command, Output};

#[derive(Clone, Copy, Debug)]
enum Route {
    Direct,
    Cargo,
}

fn command(route: Route, workdir: &Path) -> Command {
    let binary = Path::new(env!("CARGO_BIN_EXE_cargo-anneal"));
    assert!(
        binary.is_file(),
        "missing test binary: {}",
        binary.display()
    );
    let mut command = match route {
        Route::Direct => Command::new(binary),
        Route::Cargo => {
            let mut command = Command::new(env!("CARGO"));
            command.arg("anneal");
            command.env("CARGO_HOME", workdir.join("cargo-home"));
            let mut paths = vec![
                binary
                    .parent()
                    .expect("test binary has a parent")
                    .to_path_buf(),
            ];
            if let Some(path) = env::var_os("PATH") {
                paths.extend(env::split_paths(&path));
            }
            command.env(
                "PATH",
                env::join_paths(paths).expect("construct subcommand search path"),
            );
            command
        }
    };
    command.current_dir(workdir);
    command
}

fn assert_result(output: &Output, code: i32, stdout: &str, stderr: &str) {
    let actual_stdout = String::from_utf8_lossy(&output.stdout);
    let actual_stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.code() == Some(code)
            && actual_stdout.contains(stdout)
            && actual_stderr.contains(stderr),
        "expected status {code}, stdout containing {stdout:?}, stderr \
         containing {stderr:?}; got status {}\nstdout:\n{actual_stdout}\n\
         stderr:\n{actual_stderr}",
        output.status
    );
}

#[test]
fn help_and_version_work_through_direct_and_cargo_invocation() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        for args in [
            &[][..],
            &["help"],
            &["-h"],
            &["--help"],
            &["setup", "-h"],
            &["setup", "--help"],
            &["help", "setup"],
            &["verify", "-h"],
            &["verify", "--help"],
            &["help", "verify"],
        ] {
            let output = command(route, project.path())
                .args(args)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 0, "Usage:", "");
            assert!(output.stderr.is_empty(), "{output:?}");
        }
        for arg in ["-V", "--version"] {
            let output = command(route, project.path())
                .arg(arg)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(
                &output,
                0,
                &format!("cargo-anneal {}", env!("CARGO_PKG_VERSION")),
                "",
            );
            assert!(output.stderr.is_empty(), "{output:?}");
        }
    }
}

#[test]
fn malformed_arguments_fail_through_direct_and_cargo_invocation() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        for args in [
            &["unknown"][..],
            &["--unknown"],
            &["setup", "--unknown"],
            &["setup", "--local-archive"],
            &["verify"],
            &["verify", "--request"],
            &["verify", "--request", "request.json", "--unknown"],
            &[
                "verify",
                "--request",
                "request.json",
                "--manifest-path",
                "Cargo.toml",
            ],
        ] {
            let output = command(route, project.path())
                .args(args)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 2, "", "error:");
            assert!(output.stdout.is_empty(), "{output:?}");
        }
    }
}

#[cfg(target_os = "linux")]
fn local_archive(path: &Path) {
    archive_entries(path, &[("marker.txt", b"current-run CLI archive", 0o644)]);
}

#[cfg(target_os = "linux")]
fn archive_entries(path: &Path, entries: &[(&str, &[u8], u32)]) {
    let file = std::fs::File::create(path).expect("create archive");
    let encoder = zstd::Encoder::new(file, 1).expect("create compressor");
    let mut archive = tar::Builder::new(encoder);
    for (name, contents, mode) in entries {
        let mut header = tar::Header::new_gnu();
        header.set_size(contents.len() as u64);
        header.set_mode(*mode);
        header.set_cksum();
        archive
            .append_data(&mut header, name, *contents)
            .expect("write archive fixture");
    }
    archive
        .into_inner()
        .expect("finish tar archive")
        .finish()
        .expect("finish compressed archive");
}

#[cfg(target_os = "linux")]
#[test]
fn setup_uses_fresh_child_cache_for_each_invocation() {
    let project = tempfile::tempdir().expect("create external working directory");
    let archive = project.path().join("local archive.tar.zst");
    local_archive(&archive);
    for route in [Route::Direct, Route::Cargo] {
        let cache = tempfile::tempdir().expect("create owned cache");
        // On Linux, exocrate's user-global location honors XDG_CACHE_HOME.
        // Override it only in the child so this test process keeps its cache.
        let output = command(route, project.path())
            .env("XDG_CACHE_HOME", cache.path())
            .args(["setup", "--local-archive"])
            .arg(&archive)
            .output()
            .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
        assert_result(&output, 0, "Installed Anneal toolchain at ", "");
        assert!(output.stderr.is_empty(), "{output:?}");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let installed = Path::new(
            stdout
                .trim_end()
                .strip_prefix("Installed Anneal toolchain at ")
                .expect("setup reports its installation root"),
        );
        assert!(
            installed.starts_with(cache.path()),
            "{}",
            installed.display()
        );
        assert_eq!(
            std::fs::read(installed.join("marker.txt")).expect("read installed current-run marker"),
            b"current-run CLI archive"
        );

        for name in ["missing", "broken"] {
            let failed_cache = tempfile::tempdir().expect("create fresh cache");
            let bad_archive = project.path().join(format!("{name}.tar.zst"));
            if name == "broken" {
                std::fs::write(&bad_archive, b"invalid archive").expect("write broken archive");
            }
            let output = command(route, project.path())
                .env("XDG_CACHE_HOME", failed_cache.path())
                .args(["setup", "--local-archive"])
                .arg(&bad_archive)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 1, "", "error: failed to install Anneal toolchain:");
            assert!(output.stdout.is_empty(), "{output:?}");
        }
        assert!(installed.join("marker.txt").is_file());
    }
}

#[cfg(unix)]
#[test]
fn rejects_non_utf8_artifact_paths_before_staging_or_retention() {
    use std::ffi::OsString;
    use std::fs;
    use std::os::unix::ffi::OsStringExt;

    let project = tempfile::tempdir().expect("create artifact-path fixture");
    let request = project.path().join("request.json");
    let request_bytes = b"not JSON\n";
    fs::write(&request, request_bytes).unwrap();
    for route in [Route::Direct, Route::Cargo] {
        let absent = project.path().join(OsString::from_vec(
            format!("{route:?}-new-")
                .into_bytes()
                .into_iter()
                .chain([0xff])
                .collect(),
        ));
        let existing = project.path().join(OsString::from_vec(
            format!("{route:?}-existing-")
                .into_bytes()
                .into_iter()
                .chain([0xff])
                .collect(),
        ));
        fs::create_dir(&existing).unwrap();
        fs::write(existing.join("keep"), b"caller evidence").unwrap();
        for destination in [&absent, &existing] {
            let output = command(route, project.path())
                .arg("verify")
                .arg("--request")
                .arg(&request)
                .arg("--artifacts")
                .arg(destination)
                .output()
                .unwrap();
            assert_result(&output, 2, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            let receipt: serde_json::Value = serde_json::from_slice(&output.stdout)
                .expect("invalid artifact path returns a JSON receipt");
            assert_eq!(receipt["schema_version"], 1);
            assert_eq!(receipt["status"], "tool_failed");
            assert_eq!(receipt["phase"], "retention");
            assert_eq!(receipt["detail"], "artifact destination path must be UTF-8");
            assert!(receipt.get("artifacts").is_none(), "{receipt}");
            assert!(!absent.exists());
            assert_eq!(fs::read(existing.join("keep")).unwrap(), b"caller evidence");
            assert_eq!(fs::read_dir(&existing).unwrap().count(), 1);
            assert_eq!(fs::read(&request).unwrap(), request_bytes);
        }
        // A missing temp parent would fail stage creation. The encoding check
        // must run first, without reading a request or creating either path.
        let missing_tmp = project.path().join(format!("{route:?}-missing-temp"));
        let output = command(route, project.path())
            .env("TMPDIR", &missing_tmp)
            .arg("verify")
            .arg("--request")
            .arg(project.path().join("missing-request"))
            .arg("--artifacts")
            .arg(&absent)
            .output()
            .unwrap();
        assert_result(&output, 2, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["schema_version"], 1);
        assert_eq!(receipt["phase"], "retention");
        assert_eq!(receipt["detail"], "artifact destination path must be UTF-8");
        assert!(!missing_tmp.exists());
        assert!(!absent.exists());

        // UTF-8 paths retain the normal rejected-request evidence and receipt.
        // This control needs no compiler or Lean process.
        let ordinary = project.path().join(format!("{route:?}-ordinary-evidence"));
        let output = command(route, project.path())
            .arg("verify")
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(&ordinary)
            .output()
            .unwrap();
        assert_result(&output, 1, "", "");
        assert!(output.stderr.is_empty(), "{output:?}");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["schema_version"], 1);
        assert_eq!(receipt["status"], "unsupported");
        assert_eq!(receipt["phase"], "request");
        assert_eq!(receipt["artifacts"].as_str(), ordinary.to_str());
        assert!(ordinary.is_dir());
        assert_eq!(fs::read(&request).unwrap(), request_bytes);
    }
}

#[test]
fn early_verification_failures_have_versioned_receipts() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let existing = project.path().join("existing");
    fs::create_dir(&existing).unwrap();
    fs::write(existing.join("keep"), b"caller evidence").unwrap();
    for route in [Route::Direct, Route::Cargo] {
        for phase in ["staging", "retention"] {
            let mut child = command(route, project.path());
            child.arg("verify").arg("--request").arg(&request);
            if phase == "staging" {
                child.env("TMPDIR", project.path().join("missing-temp"));
            } else {
                child.arg("--artifacts").arg(&existing);
            }
            let output = child.output().unwrap();
            assert_result(&output, 2, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(receipt["schema_version"], 1, "{receipt}");
            assert_eq!(receipt["status"], "tool_failed");
            assert_eq!(receipt["phase"], phase);
            assert_eq!(fs::read(existing.join("keep")).unwrap(), b"caller evidence");
            assert_eq!(fs::read_dir(&existing).unwrap().count(), 1);
        }
    }
}

#[cfg(target_os = "linux")]
#[test]
fn capture_discovery_prefers_explicit_then_installed_then_sibling() {
    use std::fs;
    use std::os::unix::fs::PermissionsExt;
    let project = tempfile::tempdir().unwrap();
    let bin = project.path().join("bin");
    fs::create_dir(&bin).unwrap();
    let cli = bin.join("cargo-anneal");
    fs::copy(env!("CARGO_BIN_EXE_cargo-anneal"), &cli).unwrap();
    let script = |label| {
        format!(
            "#!/bin/sh\nprintf '%s\\n' '{{\"status\":\"unsupported\",\"detail\":\"{label}\"}}'\nexit 2\n"
        )
    };
    for (path, label) in [
        (bin.join("anneal-rustc-capture"), "sibling"),
        (bin.join("explicit"), "explicit"),
    ] {
        fs::write(&path, script(label)).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
    }
    let archive = project.path().join("tools.tar.zst");
    let cached = script("installed");
    archive_entries(
        &archive,
        &[
            ("bin/anneal-rustc-capture", cached.as_bytes(), 0o755),
            ("rust/marker", b"paired sysroot", 0o644),
        ],
    );
    let cache = project.path().join("cache");
    let setup = Command::new(&cli)
        .current_dir(project.path())
        .env("XDG_CACHE_HOME", &cache)
        .args(["setup", "--local-archive"])
        .arg(&archive)
        .output()
        .unwrap();
    assert_result(&setup, 0, "Installed Anneal toolchain at ", "");
    let rust = project.path().join("rust");
    fs::create_dir(&rust).unwrap();
    fs::write(rust.join("lib.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    let request = project.path().join("request.json");
    fs::write(
        &request,
        serde_json::to_vec(&serde_json::json!({
            "schema_version":1,
            "compilation":{"source_root":rust,"crate_root":"lib.rs","crate_name":"fixture",
                "edition":"2024","target":"x86_64-unknown-linux-gnu","source_files":["lib.rs"]},
            "scope":{"kind":"crate"},"proof":{"source_root":"unused","sources":[]}
        }))
        .unwrap(),
    )
    .unwrap();
    // These fixture tools refuse capture. Their marker diagnoses selection;
    // they cannot produce a fake verification result and never start Lean.
    for expected in ["installed", "explicit", "sibling"] {
        let mut child = Command::new(&cli);
        child
            .current_dir(project.path())
            .arg("verify")
            .arg("--request")
            .arg(&request);
        child.env(
            "XDG_CACHE_HOME",
            if expected == "sibling" {
                project.path().join("empty-cache")
            } else {
                cache.clone()
            },
        );
        if expected == "explicit" {
            child.arg("--capture").arg(bin.join("explicit"));
        }
        let output = child.output().unwrap();
        assert_result(&output, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["schema_version"], 1);
        assert_eq!(receipt["phase"], "capture", "{receipt}");
        let detail: serde_json::Value =
            serde_json::from_str(receipt["detail"].as_str().unwrap()).unwrap();
        assert_eq!(detail["detail"], expected, "{receipt}");
    }
    let help = Command::new(&cli)
        .args(["verify", "--help"])
        .output()
        .unwrap();
    assert_result(
        &help,
        0,
        "defaults to the installed bundle, then a sibling",
        "",
    );
}

#[test]
fn cargo_shortcut_declares_only_its_documented_source_namespace() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let package = project.path().join("package");
    fs::create_dir_all(package.join("src")).unwrap();
    fs::create_dir(package.join("proof")).unwrap();
    fs::create_dir(package.join(".hidden")).unwrap();
    fs::create_dir(package.join("target")).unwrap();
    fs::write(
        package.join("Cargo.toml"),
        "[package]\nname = \"source_namespace\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(
        package.join("src/lib.rs"),
        b"pub fn zero() -> u64 { include!(\"zero.inc\") }\n",
    )
    .unwrap();
    fs::write(package.join("src/unused.rs"), b"unused declared input\n").unwrap();
    fs::write(package.join("src/zero.inc"), b"0u64\n").unwrap();
    fs::write(
        package.join(".hidden/ignored.rs"),
        b"not a shortcut input\n",
    )
    .unwrap();
    fs::write(package.join("target/ignored.rs"), b"not a shortcut input\n").unwrap();
    fs::write(
        package.join("proof/Spec.lean"),
        b"not compiled by this check\n",
    )
    .unwrap();
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
        .arg("verify")
        .arg("--manifest-path")
        .arg(package.join("Cargo.toml"))
        .arg("--proof-dir")
        .arg(package.join("proof"))
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--artifacts")
        .arg(&evidence);
    let output = child.output().unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 1);
    assert_eq!(receipt["phase"], "capture-tool", "{receipt}");
    let request: serde_json::Value =
        serde_json::from_slice(&fs::read(evidence.join("request.json")).unwrap()).unwrap();
    assert_eq!(
        request["compilation"]["source_files"],
        serde_json::json!(["src/lib.rs", "src/unused.rs"])
    );
    assert!(!evidence.join("rust/src/zero.inc").exists());
    assert!(!evidence.join("rust/.hidden").exists());
    assert!(!evidence.join("rust/target").exists());
    assert!(!evidence.join("rust/proof").exists());
}
