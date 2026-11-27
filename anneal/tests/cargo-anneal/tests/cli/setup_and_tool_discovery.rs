// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `setup` bundle caching and tool discovery (requires the `setup`
//! feature).

use super::*;

#[cfg(all(unix, feature = "setup"))]
fn local_archive(path: &Path) {
    archive_entries(path, &[("marker.txt", b"current-run CLI archive", 0o644)]);
}

#[cfg(all(unix, feature = "setup"))]
fn archive_entries(path: &Path, entries: &[(&str, &[u8], u32)]) {
    let file = std::fs::File::create(path).expect("create archive");
    let encoder = zstd::Encoder::new(file, 1).expect("create compressor");
    let mut archive = tar::Builder::new(encoder);
    for (name, contents, mode) in entries {
        let mut header = tar::Header::new_gnu();
        header.set_size(contents.len() as u64);
        header.set_mode(*mode);
        header.set_cksum();
        archive.append_data(&mut header, name, *contents).expect("write archive fixture");
    }
    archive.into_inner().expect("finish tar archive").finish().expect("finish compressed archive");
}

#[cfg(all(unix, feature = "setup"))]
#[test]
fn setup_uses_fresh_child_cache_for_each_invocation() {
    let project = tempfile::tempdir().expect("create external working directory");
    let archive = project.path().join("local archive.tar.zst");
    local_archive(&archive);
    for route in [Route::Direct, Route::Cargo] {
        let cache = tempfile::tempdir().expect("create owned cache");
        // Override both XDG_CACHE_HOME (Linux) and HOME (macOS
        // `~/Library/Caches`) in the child so this test stays hermetic.
        let output = command(route, project.path())
            .env("XDG_CACHE_HOME", cache.path())
            .env("HOME", cache.path())
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
        assert!(installed.starts_with(cache.path()), "{}", installed.display());
        let [expected_cache_base, _home_base] = cargo_anneal::default_lean_search_bases_from_env(
            Some(cache.path().as_os_str()),
            Some(cache.path().as_os_str()),
        );
        assert_eq!(
            installed.parent(),
            Some(expected_cache_base.as_path()),
            "exocrate UserGlobal install {} must live under default Lean cache base {}",
            installed.display(),
            expected_cache_base.display()
        );
        assert_eq!(
            std::fs::read(installed.join("marker.txt")).expect("read installed current-run marker"),
            b"current-run CLI archive"
        );

        let updated_archive = project.path().join("local archive v2.tar.zst");
        archive_entries(&updated_archive, &[("marker.txt", b"replaced CLI archive", 0o644)]);
        let reinstall = command(route, project.path())
            .env("XDG_CACHE_HOME", cache.path())
            .env("HOME", cache.path())
            .args(["setup", "--local-archive"])
            .arg(&updated_archive)
            .output()
            .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
        assert_result(&reinstall, 0, "Installed Anneal toolchain at ", "");
        assert!(reinstall.stderr.is_empty(), "{reinstall:?}");
        assert_eq!(
            std::fs::read(installed.join("marker.txt")).expect("read replaced archive marker"),
            b"replaced CLI archive"
        );

        let fresh_cache = tempfile::tempdir().expect("create fresh cache");
        for name in ["missing", "broken"] {
            let bad_archive = project.path().join(format!("{name}.tar.zst"));
            if name == "broken" {
                std::fs::write(&bad_archive, b"invalid archive").expect("write broken archive");
            }
            for cache_dir in [fresh_cache.path(), cache.path()] {
                let output = command(route, project.path())
                    .env("XDG_CACHE_HOME", cache_dir)
                    .env("HOME", cache_dir)
                    .args(["setup", "--local-archive"])
                    .arg(&bad_archive)
                    .output()
                    .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
                assert_result(&output, 1, "", "error: failed to install Anneal toolchain:");
                assert!(output.stdout.is_empty(), "{output:?}");
            }
        }
        assert_eq!(
            std::fs::read(installed.join("marker.txt"))
                .expect("replaced marker must survive error"),
            b"replaced CLI archive"
        );
    }
}

#[cfg(all(unix, feature = "setup"))]
#[test]
fn setup_help_and_verify_fail_closed_on_symlinked_cache_bundle() {
    use std::{fs, os::unix::fs::symlink};

    let project = tempfile::tempdir().expect("create fixture");
    let help = command(Route::Direct, project.path()).args(["setup", "--help"]).output().unwrap();
    assert_result(&help, 0, "replaces any existing cached installation", "");
    assert_result(&help, 0, "--clear-old", "");

    let cache = tempfile::tempdir().expect("create cache");
    let archive = project.path().join("v1.tar.zst");
    local_archive(&archive);
    let setup_out = command(Route::Direct, project.path())
        .env("XDG_CACHE_HOME", cache.path())
        .env("HOME", cache.path())
        .args(["setup", "--local-archive"])
        .arg(&archive)
        .output()
        .unwrap();
    assert_result(&setup_out, 0, "Installed Anneal toolchain at ", "");
    let stdout = String::from_utf8_lossy(&setup_out.stdout);
    let installed = std::path::PathBuf::from(
        stdout.trim_end().strip_prefix("Installed Anneal toolchain at ").unwrap(),
    );

    fs::remove_dir_all(&installed).unwrap();
    let target = project.path().join("outside-dir");
    fs::create_dir(&target).unwrap();
    symlink(&target, &installed).unwrap();

    fs::write(project.path().join("lib.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"-- spec\n").unwrap();
    fs::write(project.path().join("Proof.lean"), b"-- proof\n").unwrap();

    let verify_out = command(Route::Direct, project.path())
        .env("XDG_CACHE_HOME", cache.path())
        .env("HOME", cache.path())
        .args([
            "verify",
            "--format",
            "json",
            "rustc",
            "lib.rs",
            "--crate-name",
            "sample",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ])
        .output()
        .unwrap();
    assert_result(&verify_out, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&verify_out.stdout).unwrap();
    assert_eq!(receipt["status"], "tool_failed", "{receipt}");
    assert_eq!(receipt["phase"], "capture-tool", "{receipt}");
    assert!(receipt["detail"].as_str().unwrap_or("").contains("symlink"), "{receipt}");
}

#[cfg(all(unix, feature = "setup"))]
#[test]
fn setup_clear_old_flag_and_non_tty_note() {
    use std::{fs, os::unix::fs::symlink};

    let project = tempfile::tempdir().expect("create fixture");
    let archive = project.path().join("v1.tar.zst");
    local_archive(&archive);

    for route in [Route::Direct, Route::Cargo] {
        let cache = tempfile::tempdir().expect("create cache");
        let initial = command(route, project.path())
            .env("XDG_CACHE_HOME", cache.path())
            .env("HOME", cache.path())
            .args(["setup", "--local-archive"])
            .arg(&archive)
            .output()
            .unwrap();
        assert_result(&initial, 0, "Installed Anneal toolchain at ", "");
        assert!(initial.stderr.is_empty(), "{initial:?}");
        let stdout = String::from_utf8_lossy(&initial.stdout);
        let installed = std::path::PathBuf::from(
            stdout.trim_end().strip_prefix("Installed Anneal toolchain at ").unwrap(),
        );
        let parent = installed.parent().expect("toolchain parent");

        let old_dir = parent.join("0.1.0-old-toolchain");
        fs::create_dir_all(&old_dir).unwrap();
        fs::write(old_dir.join("marker.txt"), b"old").unwrap();
        for suffix in [".lock", ".reinstall.lock", ".incomplete"] {
            fs::write(parent.join(format!("0.1.0-old-toolchain{suffix}")), b"").unwrap();
        }
        let staging_dir = parent.join(".staging-keep");
        let backup_dir = parent.join(".backup-keep");
        let exocrate_staging = parent.join("0.2.0-in-flight.staging");
        let unmanaged_dir = parent.join("unmanaged-keep");
        fs::create_dir_all(&staging_dir).unwrap();
        fs::create_dir_all(&backup_dir).unwrap();
        fs::create_dir_all(&exocrate_staging).unwrap();
        fs::create_dir_all(&unmanaged_dir).unwrap();

        let outside = project.path().join(format!("outside-{route:?}"));
        fs::create_dir_all(&outside).unwrap();
        fs::write(outside.join("keep.txt"), b"survive").unwrap();
        let sym = parent.join("0.1.0-sym");
        symlink(&outside, &sym).unwrap();

        // Without `--clear-old` on non-TTY: keep old dir and note on stderr.
        let non_tty = command(route, project.path())
            .env("XDG_CACHE_HOME", cache.path())
            .env("HOME", cache.path())
            .args(["setup", "--local-archive"])
            .arg(&archive)
            .output()
            .unwrap();
        assert_result(&non_tty, 0, "Installed Anneal toolchain at ", "--clear-old");
        assert_eq!(
            String::from_utf8_lossy(&non_tty.stdout),
            format!("Installed Anneal toolchain at {}\n", installed.display())
        );
        assert!(old_dir.is_dir());

        // With `--clear-old`: remove old dir and `.incomplete`, keeping lock
        // files, current, staging/backup dirs, unmanaged dirs, and symlinks.
        let cleared = command(route, project.path())
            .env("XDG_CACHE_HOME", cache.path())
            .env("HOME", cache.path())
            .args(["setup", "--local-archive"])
            .arg(&archive)
            .arg("--clear-old")
            .output()
            .unwrap();
        assert_result(
            &cleared,
            0,
            "Installed Anneal toolchain at ",
            "Removed old Anneal toolchain at ",
        );
        assert_eq!(
            String::from_utf8_lossy(&cleared.stdout),
            format!("Installed Anneal toolchain at {}\n", installed.display())
        );
        assert!(!old_dir.exists());
        assert!(!parent.join("0.1.0-old-toolchain.incomplete").exists());
        assert!(parent.join("0.1.0-old-toolchain.lock").is_file());
        assert!(parent.join("0.1.0-old-toolchain.reinstall.lock").is_file());
        assert!(installed.is_dir());
        assert!(staging_dir.is_dir());
        assert!(backup_dir.is_dir());
        assert!(exocrate_staging.is_dir());
        assert!(unmanaged_dir.is_dir());
        assert!(fs::symlink_metadata(&sym).unwrap().file_type().is_symlink());
        assert_eq!(fs::read(outside.join("keep.txt")).unwrap(), b"survive");
    }
}

#[cfg(all(unix, feature = "setup"))]
#[test]
fn capture_discovery_prefers_explicit_then_installed_then_sibling() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let bin = project.path().join("bin");
    fs::create_dir(&bin).unwrap();
    let cli = bin.join("cargo-anneal");
    let script = |label| {
        format!(
            "#!/bin/sh\nprintf '%s\\n' '{{\"status\":\"unsupported\",\"detail\":\"{label}\"}}'\nexit 2\n"
        )
    };
    // Stage executable fixtures in a short-lived child process so this test
    // binary never holds `O_WRONLY` descriptors in its shared file-descriptor
    // table while sibling test threads call `Command::current_dir` (`fork()`
    // on Linux), which would otherwise race before `execve()` with `ETXTBSY`.
    let stage = Command::new("/bin/sh")
        .arg("-ceu")
        .arg(
            "ln \"$1\" \"$2/cargo-anneal\" 2>/dev/null || cp \"$1\" \"$2/cargo-anneal\"\n\
             printf '%s' \"$3\" > \"$2/anneal-rustc-capture\"\n\
             printf '%s' \"$4\" > \"$2/explicit\"\n\
             chmod 0755 \"$2/anneal-rustc-capture\" \"$2/explicit\"",
        )
        .arg("sh")
        .arg(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"))
        .arg(&bin)
        .arg(script("sibling"))
        .arg(script("explicit"))
        .output()
        .unwrap();
    assert_result(&stage, 0, "", "");
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
        .env("HOME", &cache)
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
            .args(["verify", "--format", "json"])
            .arg("--request")
            .arg(&request);
        let cache_dir =
            if expected == "sibling" { project.path().join("empty-cache") } else { cache.clone() };
        child.env("XDG_CACHE_HOME", &cache_dir).env("HOME", &cache_dir);
        if expected == "explicit" {
            child.arg("--capture").arg(bin.join("explicit")).arg("--sysroot").arg(project.path());
        }
        let output = child.output().unwrap();
        assert_result(&output, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["schema_version"], 3);
        assert_eq!(receipt["taint_reasons"], serde_json::json!([]));
        assert_eq!(receipt["phase"], "capture", "{receipt}");
        let detail: serde_json::Value =
            serde_json::from_str(receipt["detail"].as_str().unwrap()).unwrap();
        assert_eq!(detail["detail"], expected, "{receipt}");
    }
    let help = Command::new(&cli).args(["verify", "--help"]).output().unwrap();
    assert_result(&help, 0, "defaults to the installed bundle, then a sibling", "");
}

/// A capture driver that `verify` would discover beside the running
/// `cargo-anneal` is protected before an existing destination is modified.
#[cfg(feature = "setup")]
#[test]
fn overwrite_artifacts_refuses_destinations_holding_discovered_tools() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let destination = project.path().join("evidence");
    fs::create_dir_all(destination.join("lean-lib")).unwrap();
    fs::write(destination.join(".cargo-anneal-artifacts"), "cargo-anneal verification artifacts\n")
        .unwrap();
    fs::write(destination.join("result.json"), b"{}").unwrap();
    let binary = Path::new(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"));
    let relocated = destination.join("lean-lib").join(binary.file_name().unwrap());
    if fs::hard_link(binary, &relocated).is_err() {
        fs::copy(binary, &relocated).unwrap();
    }
    let output = Command::new(&relocated)
        .current_dir(project.path())
        .env("XDG_CACHE_HOME", project.path().join("empty-cache"))
        .args(["verify", "--format", "json", "--request"])
        .arg(&request)
        .arg("--artifacts")
        .arg(&destination)
        .arg("--overwrite-artifacts")
        .args(["--lean", "lean"])
        .output()
        .unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["phase"], "retention", "{receipt}");
    assert!(receipt["detail"].as_str().unwrap().contains("anneal-rustc-capture"), "{receipt}");
    assert_eq!(fs::read(destination.join("result.json")).unwrap(), b"{}");
}

#[cfg(feature = "setup")]
#[test]
fn setup_allows_independent_lean_override_without_capture_pair() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();

    // `--lean` alone without `--capture`/`--sysroot` must pass CLI host-policy
    // validation when `setup` is enabled and reach `verify::main`.
    let output = command(Route::Direct, project.path())
        .args(["verify", "--format", "json", "--request"])
        .arg(&request)
        .args(["--lean", "custom-lean"])
        .output()
        .unwrap();
    assert_result(&output, 1, "", "");
    assert!(output.stderr.is_empty(), "{output:?}");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 3, "{receipt}");
    assert_eq!(receipt["status"], "unsupported");
    assert_eq!(receipt["phase"], "request");
}

#[cfg(all(target_os = "linux", feature = "setup"))]
#[test]
fn quiet_suppresses_non_tty_setup_note_while_keeping_taint_caveats() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let archive = project.path().join("v1.tar.zst");
    local_archive(&archive);
    let cache = tempfile::tempdir().unwrap();

    let first = command(Route::Direct, project.path())
        .env("XDG_CACHE_HOME", cache.path())
        .args(["setup", "--local-archive"])
        .arg(&archive)
        .output()
        .unwrap();
    assert_result(&first, 0, "Installed Anneal toolchain at ", "");
    let stdout = String::from_utf8_lossy(&first.stdout);
    let installed = std::path::PathBuf::from(
        stdout.trim_end().strip_prefix("Installed Anneal toolchain at ").unwrap(),
    );
    let old_dir = installed.parent().unwrap().join("0.1.0-old-toolchain");
    fs::create_dir_all(&old_dir).unwrap();

    // `-q` suppresses the non-interactive old-toolchain `note:` on stderr.
    let quiet_setup = command(Route::Direct, project.path())
        .env("XDG_CACHE_HOME", cache.path())
        .args(["-q", "setup", "--local-archive"])
        .arg(&archive)
        .output()
        .unwrap();
    assert_result(&quiet_setup, 0, "Installed Anneal toolchain at ", "");
    assert!(quiet_setup.stderr.is_empty(), "{quiet_setup:?}");

    // `-q` on `verify` NEVER suppresses mandatory security taint banners/rows.
    let request = project.path().join("bad.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let quiet_taint = command(Route::Direct, project.path())
        .args(["-q", "verify", "--allow-unsandboxed-elaboration", "--request"])
        .arg(&request)
        .output()
        .unwrap();
    assert_result(&quiet_taint, 1, "! TAINT    : unsandboxed_elaboration", "TAINTED");
}
