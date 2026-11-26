// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Command behavior through direct invocation and Cargo's subcommand dispatch.

use std::{
    env,
    path::Path,
    process::{Command, Output},
};

#[derive(Clone, Copy, Debug)]
enum Route {
    Direct,
    Cargo,
}

fn command(route: Route, workdir: &Path) -> Command {
    let binary = Path::new(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"));
    assert!(binary.is_file(), "missing test binary: {}", binary.display());
    let cargo_home = workdir.join("cargo-home");
    let mut command = match route {
        Route::Direct => {
            let mut command = Command::new(binary);
            // Isolate `CARGO_HOME` so ambient `~/.cargo/config.toml` cannot
            // affect `--manifest-path` tests; tests may still override it.
            command.env("CARGO_HOME", &cargo_home);
            command
        }
        Route::Cargo => {
            let mut command = Command::new(env!("CARGO"));
            command.arg("anneal");
            command.env("CARGO_HOME", &cargo_home);
            // Cargo dispatches `cargo anneal` to an executable literally named
            // `cargo-anneal` on `PATH`. Stage a link inside `cargo-home/bin` so
            // the test crate's non-colliding `cargo-anneal-test-bin` is found
            // without opening an `O_WRONLY` fd to an executable in this process.
            let cargo_bin = cargo_home.join("bin");
            std::fs::create_dir_all(&cargo_bin).expect("create cargo subcommand bin dir");
            let subcmd = cargo_bin.join(format!("cargo-anneal{}", env::consts::EXE_SUFFIX));
            if std::fs::symlink_metadata(&subcmd).is_err() {
                #[cfg(unix)]
                std::os::unix::fs::symlink(binary, &subcmd)
                    .expect("symlink cargo-anneal subcommand binary");
                #[cfg(not(unix))]
                if std::fs::hard_link(binary, &subcmd).is_err() {
                    std::fs::copy(binary, &subcmd).expect("copy cargo-anneal subcommand binary");
                }
            }
            let mut paths = vec![cargo_bin];
            if let Some(path) = env::var_os("PATH") {
                paths.extend(env::split_paths(&path));
            }
            command.env("PATH", env::join_paths(paths).expect("construct subcommand search path"));
            command
        }
    };
    // The CI images export `CARGO_TERM_COLOR=always`, which would color the
    // child's `error:` prefixes and break plain-text stderr assertions.
    // Tests that exercise color set these variables explicitly.
    command.env_remove("CARGO_TERM_COLOR").env_remove("CLICOLOR_FORCE").env_remove("FORCE_COLOR");
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
            #[cfg(feature = "setup")]
            &["setup", "-h"],
            #[cfg(feature = "setup")]
            &["setup", "--help"],
            #[cfg(feature = "setup")]
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
                &format!("cargo-anneal {}", cargo_anneal::cli::PKG_VERSION),
                "",
            );
            assert!(output.stderr.is_empty(), "{output:?}");
        }
    }
}

#[test]
fn bundled_skill_is_discoverable_and_matches_the_source_file() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        for (args, hint) in [
            (&["--help"][..], "Print the bundled agent skill"),
            (&["verify", "--help"][..], "cargo anneal skill"),
        ] {
            let output = command(route, project.path())
                .args(args)
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 0, hint, "");
            assert!(output.stderr.is_empty(), "{output:?}");
        }

        let output = command(route, project.path())
            .arg("skill")
            .output()
            .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
        assert_result(&output, 0, "", "");
        assert!(output.stderr.is_empty(), "{output:?}");
        assert_eq!(
            output.stdout,
            include_bytes!("../../../trusted/cargo-anneal/skills/cargo-anneal/SKILL.md")
        );

        // Companion skills print byte-for-byte from their packaged copies,
        // which `ci/check_skills.py` keeps identical to `anneal/skills/`.
        const SPEC_AUTHORING: &[u8] =
            include_bytes!("../../../trusted/cargo-anneal/assets/skills/spec-authoring/SKILL.md");
        const PROOF_SCALING: &[u8] =
            include_bytes!("../../../trusted/cargo-anneal/assets/skills/proof-scaling/SKILL.md");
        for (topic, canonical) in [
            (
                "cargo-anneal",
                &include_bytes!("../../../trusted/cargo-anneal/skills/cargo-anneal/SKILL.md")[..],
            ),
            ("spec-authoring", SPEC_AUTHORING),
            ("proof-scaling", PROOF_SCALING),
        ] {
            let output = command(route, project.path())
                .args(["skill", topic])
                .output()
                .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
            assert_result(&output, 0, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            assert_eq!(output.stdout, canonical, "skill {topic}");
        }
        let output = command(route, project.path())
            .args(["skill", "list"])
            .output()
            .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
        for topic in ["cargo-anneal", "spec-authoring", "proof-scaling"] {
            assert_result(&output, 0, topic, "");
        }
        let output = command(route, project.path())
            .args(["skill", "no-such-topic"])
            .output()
            .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
        assert_result(&output, 2, "", "no-such-topic");
    }
}

#[test]
fn bundled_example_matches_the_verified_fixture() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        let output = command(route, project.path())
            .args(["skill", "--example"])
            .output()
            .unwrap_or_else(|error| panic!("launch {route:?}: {error}"));
        assert_result(&output, 0, "cargo anneal verify --request request.json", "");
        assert!(output.stderr.is_empty(), "{output:?}");
        let stdout = String::from_utf8(output.stdout).expect("UTF-8 example");
        let sections: Vec<_> = stdout.trim_end().split("\n\n## ").skip(1).collect();
        assert_eq!(
            sections,
            [
                concat!(
                    "`lib.rs`\n\n```rust\n",
                    include_str!("../../../trusted/cargo-anneal/assets/scalar/lib.rs"),
                    "```",
                ),
                concat!(
                    "`request.json`\n\n```json\n",
                    include_str!("../../../trusted/cargo-anneal/assets/scalar/request.json"),
                    "```",
                ),
                concat!(
                    "`Spec.lean`\n\n```lean\n",
                    include_str!("../../../trusted/cargo-anneal/assets/scalar/Spec.lean"),
                    "```",
                ),
                concat!(
                    "`Proof.lean`\n\n```lean\n",
                    include_str!("../../../trusted/cargo-anneal/assets/scalar/Proof.lean"),
                    "```",
                ),
            ],
        );
    }
}

#[test]
fn malformed_arguments_fail_through_direct_and_cargo_invocation() {
    let project = tempfile::tempdir().expect("create external working directory");
    for route in [Route::Direct, Route::Cargo] {
        for args in [
            &["unknown"][..],
            &["--unknown"],
            #[cfg(not(feature = "setup"))]
            &["setup"],
            #[cfg(feature = "setup")]
            &["setup", "--unknown"],
            #[cfg(feature = "setup")]
            &["setup", "--local-archive"],
            &["verify"],
            &["verify", "--request"],
            &["verify", "--request", "request.json", "--unknown"],
            &["verify", "--request", "request.json", "--manifest-path", "Cargo.toml"],
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

#[cfg(unix)]
#[test]
fn rejects_non_utf8_artifact_paths_before_staging_or_retention() {
    use std::{ffi::OsString, fs, os::unix::ffi::OsStringExt};

    let project = tempfile::tempdir().expect("create artifact-path fixture");
    let request = project.path().join("request.json");
    let request_bytes = b"not JSON\n";
    fs::write(&request, request_bytes).unwrap();
    for route in [Route::Direct, Route::Cargo] {
        let absent = project.path().join(OsString::from_vec(
            format!("{route:?}-new-").into_bytes().into_iter().chain([0xff]).collect(),
        ));
        let existing = project.path().join(OsString::from_vec(
            format!("{route:?}-existing-").into_bytes().into_iter().chain([0xff]).collect(),
        ));
        fs::create_dir(&existing).unwrap();
        fs::write(existing.join("keep"), b"caller evidence").unwrap();
        for destination in [&absent, &existing] {
            let mut cmd = command(route, project.path());
            cmd.args(["verify", "--format", "json"])
                .arg("--request")
                .arg(&request)
                .arg("--artifacts")
                .arg(destination);
            #[cfg(not(feature = "setup"))]
            cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
            let output = cmd.output().unwrap();
            assert_result(&output, 2, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            let receipt: serde_json::Value = serde_json::from_slice(&output.stdout)
                .expect("invalid artifact path returns a JSON receipt");
            assert_eq!(receipt["schema_version"], 3);
            assert_eq!(receipt["taint_reasons"], serde_json::json!([]));
            assert!(receipt.get("tainted").is_none(), "{receipt}");
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
        let mut cmd = command(route, project.path());
        cmd.env("TMPDIR", &missing_tmp)
            .args(["verify", "--format", "json"])
            .arg("--request")
            .arg(project.path().join("missing-request"))
            .arg("--artifacts")
            .arg(&absent);
        #[cfg(not(feature = "setup"))]
        cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = cmd.output().unwrap();
        assert_result(&output, 2, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["schema_version"], 3);
        assert_eq!(receipt["taint_reasons"], serde_json::json!([]));
        assert_eq!(receipt["phase"], "retention");
        assert_eq!(receipt["detail"], "artifact destination path must be UTF-8");
        assert!(!missing_tmp.exists());
        assert!(!absent.exists());

        // UTF-8 paths retain the normal rejected-request evidence and receipt.
        // This control needs no compiler or Lean process.
        let ordinary = project.path().join(format!("{route:?}-ordinary-evidence"));
        let mut cmd = command(route, project.path());
        cmd.args(["verify", "--format", "json"])
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(&ordinary);
        #[cfg(not(feature = "setup"))]
        cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = cmd.output().unwrap();
        assert_result(&output, 1, "", "");
        assert!(output.stderr.is_empty(), "{output:?}");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["schema_version"], 3);
        assert_eq!(receipt["taint_reasons"], serde_json::json!([]));
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
            child.args(["verify", "--format", "json"]).arg("--request").arg(&request);
            #[cfg(not(feature = "setup"))]
            child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
            if phase == "staging" {
                child.env("TMPDIR", project.path().join("missing-temp"));
            } else {
                child.arg("--artifacts").arg(&existing);
            }
            let output = child.output().unwrap();
            assert_result(&output, 2, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(receipt["schema_version"], 3, "{receipt}");
            assert_eq!(receipt["taint_reasons"], serde_json::json!([]));
            assert!(receipt.get("tainted").is_none(), "{receipt}");
            assert_eq!(receipt["status"], "tool_failed");
            assert_eq!(receipt["phase"], phase);
            assert_eq!(fs::read(existing.join("keep")).unwrap(), b"caller evidence");
            assert_eq!(fs::read_dir(&existing).unwrap().count(), 1);
        }
    }
}

#[test]
fn overwrite_artifacts_replaces_only_earlier_artifacts() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let destination = project.path().join("evidence");
    let run = |route: Route, overwrite: bool| {
        let mut child = command(route, project.path());
        child
            .args(["verify", "--format", "json"])
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(&destination);
        if overwrite {
            child.arg("--overwrite-artifacts");
        }
        #[cfg(not(feature = "setup"))]
        child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = child.output().unwrap();
        let receipt: serde_json::Value =
            serde_json::from_slice(&output.stdout).unwrap_or_else(|e| panic!("{e}: {output:?}"));
        (output, receipt)
    };
    // The rejected request needs no compiler or Lean process, yet retains
    // its (empty) evidence directory each time.
    for route in [Route::Direct, Route::Cargo] {
        let (output, receipt) = run(route, true);
        assert_result(&output, 1, "", "");
        assert_eq!(receipt["phase"], "request", "{receipt}");
        assert_eq!(receipt["artifacts"].as_str(), destination.to_str());
        assert!(destination.is_dir());
        // Without the flag, the existing destination is still refused.
        let (output, receipt) = run(route, false);
        assert_result(&output, 2, "", "");
        assert_eq!(receipt["phase"], "retention", "{receipt}");
        assert!(receipt["detail"].as_str().unwrap().contains("--overwrite-artifacts"), "{receipt}");
    }
    // An earlier artifact entry is replaced; no staging siblings remain.
    fs::write(destination.join("request.json"), b"earlier").unwrap();
    let (output, _) = run(Route::Direct, true);
    assert_result(&output, 1, "", "");
    assert!(!destination.join("request.json").exists());
    let names: Vec<_> = fs::read_dir(project.path())
        .unwrap()
        .map(|e| e.unwrap().file_name().into_string().unwrap())
        .filter(|n| n.contains("anneal-"))
        .collect();
    assert!(names.is_empty(), "{names:?}");
    // A foreign entry blocks replacement before staging.
    fs::write(destination.join("notes.txt"), b"caller notes").unwrap();
    let (output, receipt) = run(Route::Direct, true);
    assert_result(&output, 2, "", "");
    assert_eq!(receipt["phase"], "retention", "{receipt}");
    assert!(receipt["detail"].as_str().unwrap().contains("notes.txt"), "{receipt}");
    assert_eq!(fs::read(destination.join("notes.txt")).unwrap(), b"caller notes");
    #[cfg(unix)]
    {
        let link = project.path().join("evidence-link");
        let target = project.path().join("link-target");
        fs::create_dir(&target).unwrap();
        std::os::unix::fs::symlink(&target, &link).unwrap();
        let mut child = command(Route::Direct, project.path());
        child
            .args(["verify", "--format", "json"])
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(&link)
            .arg("--overwrite-artifacts");
        #[cfg(not(feature = "setup"))]
        child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = child.output().unwrap();
        assert_result(&output, 2, "symlink", "");
        assert!(fs::symlink_metadata(&link).unwrap().is_symlink());
        assert_eq!(fs::read_dir(&target).unwrap().count(), 0);
    }
}

/// `--overwrite-artifacts` never deletes the caller's inputs: a destination
/// holding the `--request` file, or a source root that a readable request
/// declares, is refused before staging and left untouched.
#[test]
fn overwrite_artifacts_refuses_destinations_holding_inputs() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let destination = project.path().join("ev");
    fs::create_dir_all(destination.join("rust")).unwrap();
    fs::write(destination.join(".cargo-anneal-artifacts"), "cargo-anneal verification artifacts\n")
        .unwrap();
    let lib = include_str!("../../../trusted/cargo-anneal/assets/scalar/lib.rs");
    fs::write(destination.join("rust/lib.rs"), lib).unwrap();
    let inner_request = destination.join("request.json");
    fs::write(&inner_request, b"not JSON\n").unwrap();
    let outer_request = project.path().join("outer.json");
    fs::write(
        &outer_request,
        serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": "ev/rust",
                "crate_root": "lib.rs",
                "crate_name": "scalar",
                "source_files": ["lib.rs"],
            },
            "scope": {"kind": "selected_unit", "roots": ["zero"]},
            "proof": {"source_root": ".", "sources": []},
        })
        .to_string(),
    )
    .unwrap();
    for request in [&inner_request, &outer_request] {
        let mut child = command(Route::Direct, project.path());
        child
            .args(["verify", "--format", "json", "--request"])
            .arg(request)
            .arg("--artifacts")
            .arg(&destination)
            .arg("--overwrite-artifacts")
            .args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = child.output().unwrap();
        assert_result(&output, 2, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["phase"], "retention", "{receipt}");
        assert!(receipt["detail"].as_str().unwrap().contains("verification input"), "{receipt}");
        assert_eq!(fs::read(&inner_request).unwrap(), b"not JSON\n");
        assert_eq!(fs::read_to_string(destination.join("rust/lib.rs")).unwrap(), lib);
    }
}

/// An earlier run's success evidence (`result.json`, `lean-lib/`) never
/// survives a later failing `--overwrite-artifacts` run.
#[test]
fn overwrite_artifacts_drops_earlier_success_evidence_on_failure() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let destination = project.path().join("evidence");
    fs::create_dir_all(destination.join("lean-lib/Proof")).unwrap();
    fs::write(destination.join(".cargo-anneal-artifacts"), "cargo-anneal verification artifacts\n")
        .unwrap();
    fs::write(destination.join("result.json"), b"{\"status\":\"crate_verified\"}").unwrap();
    fs::write(destination.join("lean-lib/Proof/Proof.olean"), b"olean").unwrap();
    let mut child = command(Route::Direct, project.path());
    child
        .args(["verify", "--format", "json", "--request"])
        .arg(&request)
        .arg("--artifacts")
        .arg(&destination)
        .arg("--overwrite-artifacts");
    #[cfg(not(feature = "setup"))]
    child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = child.output().unwrap();
    assert_result(&output, 1, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["phase"], "request", "{receipt}");
    assert_eq!(receipt["artifacts"].as_str(), destination.to_str(), "{receipt}");
    assert!(!destination.join("result.json").exists());
    assert!(!destination.join("lean-lib").exists());
    assert!(destination.join(".cargo-anneal-artifacts").is_file());
}

/// A run that stages every early entry, including a `--verify-shard-plan`
/// snapshot (`expected-shard-plan.json`), leaves a retained directory that a
/// rerun with `--overwrite-artifacts` must still recognize and replace.
#[test]
fn overwrite_artifacts_replaces_retained_shard_plan_snapshot() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    for (name, contents) in [
        ("lib.rs", include_str!("../../../trusted/cargo-anneal/assets/scalar/lib.rs")),
        ("request.json", include_str!("../../../trusted/cargo-anneal/assets/scalar/request.json")),
        ("Spec.lean", include_str!("../../../trusted/cargo-anneal/assets/scalar/Spec.lean")),
        ("Proof.lean", include_str!("../../../trusted/cargo-anneal/assets/scalar/Proof.lean")),
    ] {
        fs::write(project.path().join(name), contents).unwrap();
    }
    let plan = project.path().join("anneal-shards.json");
    fs::write(
        &plan,
        serde_json::json!({
            "schema_version": 1,
            "sharded": false,
            "scope": "crate",
            "shard_min_bodies": 0,
            "shard_max_bodies": 0,
            "shard_max_ast_nodes": 0,
            "total_bodies": 0,
            "total_shards": 0,
            "id_tree_sha256": null,
            "shards": [],
        })
        .to_string(),
    )
    .unwrap();
    let destination = project.path().join("evidence");
    // Nonexistent tool paths stop the run at `capture-tool`, after the
    // request and shard plan are staged, without any compiler or Lean.
    let run = |overwrite: bool| {
        let mut child = command(Route::Direct, project.path());
        child
            .args(["verify", "--format", "json", "--request"])
            .arg(project.path().join("request.json"))
            .arg("--verify-shard-plan")
            .arg(&plan)
            .arg("--artifacts")
            .arg(&destination)
            .args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        if overwrite {
            child.arg("--overwrite-artifacts");
        }
        let output = child.output().unwrap();
        let receipt: serde_json::Value =
            serde_json::from_slice(&output.stdout).unwrap_or_else(|e| panic!("{e}: {output:?}"));
        (output, receipt)
    };
    let (output, receipt) = run(false);
    assert_result(&output, 2, "", "");
    assert_eq!(receipt["phase"], "capture-tool", "{receipt}");
    assert_eq!(receipt["artifacts"].as_str(), destination.to_str(), "{receipt}");
    assert!(destination.join("expected-shard-plan.json").is_file());
    assert!(destination.join("request.json").is_file());
    fs::write(destination.join("expected-shard-plan.json"), b"earlier").unwrap();

    let (output, receipt) = run(true);
    assert_result(&output, 2, "", "");
    assert_eq!(receipt["phase"], "capture-tool", "{receipt}");
    assert_eq!(receipt["artifacts"].as_str(), destination.to_str(), "{receipt}");
    assert_eq!(
        fs::read(destination.join("expected-shard-plan.json")).unwrap(),
        fs::read(&plan).unwrap()
    );
}

#[test]
fn unclaimable_artifact_destinations_fail_before_staging_or_request_reading() {
    use std::{fs, path::PathBuf};
    let project = tempfile::tempdir().unwrap();
    let directory = project.path().join("existing-directory");
    fs::create_dir(&directory).unwrap();
    fs::write(directory.join("keep"), b"caller evidence").unwrap();
    let file = project.path().join("existing-file");
    fs::write(&file, b"caller file").unwrap();
    // Relative destinations resolve against the working directory, which
    // `command` sets to `project`.
    let base_destinations = [
        (directory.clone(), "already exists"),
        (PathBuf::from("existing-directory"), "already exists"),
        (file.clone(), "already exists"),
        (project.path().join("missing-parent/out"), "artifact destination parent"),
        (file.join("out"), "artifact destination parent"),
        (project.path().join("missing-parent/."), "must end in a new directory name"),
    ];
    #[cfg(unix)]
    let unix_destinations = {
        let dangling = project.path().join("dangling-link");
        std::os::unix::fs::symlink(project.path().join("absent-target"), &dangling).unwrap();
        // With a trailing separator, `lstat` follows the link but `mkdir`
        // still refuses it.
        vec![(PathBuf::from("dangling-link/"), "already exists"), (dangling, "already exists")]
    };
    #[cfg(not(unix))]
    let unix_destinations: [(PathBuf, &str); 0] = [];
    let destinations: Vec<_> = base_destinations.into_iter().chain(unix_destinations).collect();
    // A missing request and a missing temp parent would each fail later
    // phases. The receipt must still name retention, showing the destination
    // was rejected before staging, request parsing, capture, or Lean.
    let missing_tmp = project.path().join("missing-temp");
    for route in [Route::Direct, Route::Cargo] {
        for (destination, detail) in &destinations {
            let mut child = command(route, project.path());
            child
                .env("TMPDIR", &missing_tmp)
                .arg("verify")
                .args(["--format", "json"])
                .arg("--request")
                .arg(project.path().join("missing-request"))
                .arg("--artifacts")
                .arg(destination);
            #[cfg(not(feature = "setup"))]
            child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
            let output = child.output().unwrap();
            assert_result(&output, 2, "", "");
            assert!(output.stderr.is_empty(), "{output:?}");
            let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
            assert_eq!(receipt["schema_version"], 3, "{receipt}");
            assert_eq!(receipt["status"], "tool_failed", "{receipt}");
            assert_eq!(receipt["phase"], "retention", "{receipt}");
            assert!(receipt["detail"].as_str().unwrap().contains(detail), "{receipt}");
            assert!(receipt.get("artifacts").is_none(), "{receipt}");
            assert!(!missing_tmp.exists());
        }
    }
    // Default human verdict card + `--receipt-out` also honor `--artifacts`
    // preflight rejection before staging.
    let receipt_file = project.path().join("preflight-receipt.json");
    let mut human_child = command(Route::Direct, project.path());
    human_child
        .env_remove("CARGO_TERM_COLOR")
        .env_remove("CLICOLOR_FORCE")
        .env_remove("FORCE_COLOR")
        .env("TMPDIR", &missing_tmp)
        .arg("verify")
        .arg("--request")
        .arg(project.path().join("missing-request"))
        .arg("--artifacts")
        .arg(&directory)
        .arg("--receipt-out")
        .arg(&receipt_file);
    #[cfg(not(feature = "setup"))]
    human_child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let human_out = human_child.output().unwrap();
    assert_result(
        &human_out,
        2,
        "[FAIL] VERIFICATION FAILED (tool_failed in phase `retention`, exit 2)",
        "",
    );
    let written_receipt: serde_json::Value =
        serde_json::from_slice(&fs::read(&receipt_file).unwrap()).unwrap();
    assert_eq!(written_receipt["status"], "tool_failed", "{written_receipt}");
    assert_eq!(written_receipt["phase"], "retention", "{written_receipt}");
    assert!(written_receipt.get("artifacts").is_none(), "{written_receipt}");
    assert!(!missing_tmp.exists());

    assert_eq!(fs::read(directory.join("keep")).unwrap(), b"caller evidence");
    assert_eq!(fs::read_dir(&directory).unwrap().count(), 1);
    assert_eq!(fs::read(&file).unwrap(), b"caller file");
    assert!(!project.path().join("missing-parent").exists());
    assert!(!project.path().join("absent-target").exists());

    // New paths inside an existing directory, including a relative single
    // component, pass preflight and still retain rejected-request evidence.
    // This control needs no compiler or Lean process.
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    for (spelling, created) in [
        (directory.join("fresh-evidence"), directory.join("fresh-evidence")),
        (PathBuf::from("relative-evidence"), project.path().join("relative-evidence")),
    ] {
        let mut child = command(Route::Direct, project.path());
        child
            .arg("verify")
            .args(["--format", "json"])
            .arg("--request")
            .arg(&request)
            .arg("--artifacts")
            .arg(&spelling);
        #[cfg(not(feature = "setup"))]
        child.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let output = child.output().unwrap();
        assert_result(&output, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["status"], "unsupported", "{receipt}");
        assert_eq!(receipt["phase"], "request", "{receipt}");
        assert_eq!(receipt["artifacts"].as_str(), spelling.to_str());
        assert!(created.is_dir());
    }

    // Late retention failure: an unwritable parent passes preflight (which does
    // not check parent write permission), runs staging and request parsing, and
    // fails in `retain_stage` (`phase: "retention"`, exit 2).
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;

        let readonly_parent = project.path().join("readonly-parent");
        fs::create_dir(&readonly_parent).unwrap();
        fs::set_permissions(&readonly_parent, fs::Permissions::from_mode(0o555)).unwrap();
        let probe = readonly_parent.join("probe-perm");
        match fs::create_dir(&probe) {
            Ok(()) => {
                let _ = fs::remove_dir(&probe);
            }
            Err(probe_err) => {
                let late_dest = readonly_parent.join("late-retention-fail");
                // Missing `TMPDIR` must fail in `staging` rather than
                // `retention`, proving preflight admitted `late_dest`.
                let missing_late_tmp = project.path().join("missing-late-temp");
                let mut preflight_ok_cmd = command(Route::Direct, project.path());
                preflight_ok_cmd
                    .env("TMPDIR", &missing_late_tmp)
                    .arg("verify")
                    .args(["--format", "json"])
                    .arg("--request")
                    .arg(&request)
                    .arg("--artifacts")
                    .arg(&late_dest);
                #[cfg(not(feature = "setup"))]
                preflight_ok_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
                let preflight_ok_out = preflight_ok_cmd.output().unwrap();
                assert_result(&preflight_ok_out, 2, "", "");
                let preflight_ok_rec: serde_json::Value =
                    serde_json::from_slice(&preflight_ok_out.stdout).unwrap();
                assert_eq!(preflight_ok_rec["phase"], "staging", "{preflight_ok_rec}");

                let mut late_cmd = command(Route::Direct, project.path());
                late_cmd
                    .arg("verify")
                    .args(["--format", "json"])
                    .arg("--request")
                    .arg(&request)
                    .arg("--artifacts")
                    .arg(&late_dest);
                #[cfg(not(feature = "setup"))]
                late_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
                let late_out = late_cmd.output().unwrap();
                assert_result(&late_out, 2, "", "");
                let late_rec: serde_json::Value = serde_json::from_slice(&late_out.stdout).unwrap();
                assert_eq!(late_rec["schema_version"], 3, "{late_rec}");
                assert_eq!(late_rec["status"], "tool_failed", "{late_rec}");
                assert_eq!(late_rec["phase"], "retention", "{late_rec}");
                let late_detail = late_rec["detail"].as_str().unwrap();
                assert!(!late_detail.starts_with("artifact destination"), "{late_rec}");
                assert!(late_detail.contains(&probe_err.to_string()), "{late_rec}");
                assert!(late_rec.get("artifacts").is_none(), "{late_rec}");
                assert!(!late_dest.exists());
            }
        }
        let _ = fs::set_permissions(&readonly_parent, fs::Permissions::from_mode(0o700));
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

#[cfg(not(feature = "setup"))]
#[test]
fn verify_without_setup_feature_requires_explicit_tool_paths() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let rust = project.path().join("rust");
    fs::create_dir(&rust).unwrap();
    fs::write(rust.join("lib.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    let request = project.path().join("request.json");
    fs::write(
        &request,
        serde_json::to_vec(&serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": rust,
                "crate_root": "lib.rs",
                "crate_name": "fixture",
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "source_files": ["lib.rs"]
            },
            "scope": {"kind": "crate"},
            "proof": {"source_root": "unused", "sources": []}
        }))
        .unwrap(),
    )
    .unwrap();

    for route in [Route::Direct, Route::Cargo] {
        for extra in [&[][..], &["--capture", "cap", "--sysroot", "sys"], &["--lean", "lean"]] {
            let mut cmd = command(route, project.path());
            cmd.arg("verify").arg("--request").arg(&request).args(extra);
            let output = cmd.output().unwrap();
            assert_result(&output, 2, "", "error:");
            assert!(output.stdout.is_empty(), "{output:?}");
        }
    }
}

#[test]
fn host_policy_conflicts_exit_2_on_stderr_with_empty_stdout() {
    let project = tempfile::tempdir().unwrap();
    let base_rustc = [
        "verify",
        "rustc",
        "lib.rs",
        "--crate-name",
        "fixture",
        "--spec-file",
        "Spec=Spec.lean",
        "--proof-file",
        "Proof=Proof.lean",
    ];

    let bad_cases: Vec<Vec<&str>> = vec![
        vec!["verify", "--request", "r.json", "--export-lean-lib"],
        vec!["verify", "--request", "r.json", "--capture", "cap", "--lean", "lean"],
        vec!["verify", "--request", "r.json", "--sysroot", "sys", "--lean", "lean"],
        vec![
            "verify",
            "--request",
            "r.json",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--allow-unpinned-lean",
        ],
        vec![
            "verify",
            "--request",
            "r.json",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--lean",
            "lean",
            "--lean-memory-mb",
            "0",
        ],
        vec![
            "verify",
            "--request",
            "r.json",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--lean",
            "lean",
            "--select",
            "foo",
        ],
        [
            &[
                "verify",
                "--request",
                "r.json",
                "--capture",
                "cap",
                "--sysroot",
                "sys",
                "--lean",
                "lean",
            ][..],
            &base_rustc[1..],
        ]
        .concat(),
        [
            &[
                "verify",
                "--manifest-path",
                "Cargo.toml",
                "--proof-dir",
                "proof",
                "--capture",
                "cap",
                "--sysroot",
                "sys",
                "--lean",
                "lean",
            ][..],
            &base_rustc[1..],
        ]
        .concat(),
        [
            &base_rustc[..],
            &[
                "--capture",
                "cap",
                "--sysroot",
                "sys",
                "--lean",
                "lean",
                "--spec-file",
                "Spec=Other.lean",
            ],
        ]
        .concat(),
        [
            &base_rustc[..],
            &["--capture", "cap", "--sysroot", "sys", "--lean", "lean", "--export-lean-lib"],
        ]
        .concat(),
        vec![
            "verify",
            "--request",
            "r.json",
            "--panic",
            "abort",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--lean",
            "lean",
        ],
        [
            &[
                "verify",
                "--panic",
                "abort",
                "--capture",
                "cap",
                "--sysroot",
                "sys",
                "--lean",
                "lean",
            ][..],
            &base_rustc[1..],
        ]
        .concat(),
        vec![
            "verify",
            "--manifest-path",
            "Cargo.toml",
            "--proof-dir",
            "proof",
            "--panic",
            "bogus",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--lean",
            "lean",
        ],
    ];

    for args in bad_cases {
        let output = command(Route::Direct, project.path()).args(&args).output().unwrap();
        assert_result(&output, 2, "", "error:");
        assert!(output.stdout.is_empty(), "{args:?}: {output:?}");
    }
}

#[test]
fn unpinned_policy_taint_emits_stderr_banner_and_v3_failure_receipt() {
    use std::fs;
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let missing_tmp = project.path().join("missing-tmp");

    let mut cmd = command(Route::Direct, project.path());
    cmd.env("TMPDIR", &missing_tmp)
        .args(["verify", "--format", "json", "--request"])
        .arg(&request)
        .args([
            "--allow-unpinned-lean",
            "--lean",
            "custom-lean",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
        ]);
    let output = cmd.output().unwrap();
    assert_result(&output, 2, "", "TAINTED");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 3, "{receipt}");
    assert_eq!(receipt["taint_reasons"], serde_json::json!(["unpinned_lean"]), "{receipt}");
    assert!(receipt.get("tainted").is_none(), "{receipt}");
    assert!(receipt.get("unpinned_lean").is_none(), "{receipt}");
    assert_eq!(receipt["phase"], "staging");
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

#[cfg(unix)]
#[test]
fn rustc_mode_stages_symlinks_strict_roles_and_rejects_fifos() {
    use std::{fs, os::unix::fs::symlink};

    let project = tempfile::tempdir().unwrap();
    let cas = project.path().join("cas");
    fs::create_dir(&cas).unwrap();
    fs::write(cas.join("a.rs"), b"pub mod sub;\n").unwrap();
    fs::write(cas.join("b.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    fs::write(cas.join("spec.lean"), b"-- spec\n").unwrap();
    fs::write(cas.join("proof.lean"), b"-- proof\n").unwrap();

    let runfiles = project.path().join("runfiles/crate/src");
    fs::create_dir_all(&runfiles).unwrap();
    symlink(cas.join("a.rs"), runfiles.join("lib.rs")).unwrap();
    symlink(cas.join("b.rs"), runfiles.join("sub.rs")).unwrap();
    symlink(cas.join("spec.lean"), runfiles.join("Contract.lean")).unwrap();
    symlink(cas.join("proof.lean"), runfiles.join("Spec.Helper.lean")).unwrap();

    let evidence = project.path().join("evidence");
    // Host flags passed both BEFORE and AFTER `rustc` must work.
    let output = command(Route::Direct, project.path())
        .args(["verify", "--format", "json"])
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--sysroot")
        .arg(project.path())
        .arg("rustc")
        .arg(runfiles.join("lib.rs"))
        .args(["--crate-name", "sample", "--source-file"])
        .arg(runfiles.join("sub.rs"))
        .arg("--spec-file")
        .arg(format!("Contract={}", runfiles.join("Contract.lean").display()))
        .arg("--proof-file")
        .arg(format!("Spec.Helper={}", runfiles.join("Spec.Helper.lean").display()))
        .args([
            "--spec-decl",
            "Contract:StarnixEbpf.Contract.specs",
            "--theorem",
            "Spec.Helper:Proof.custom",
            "--lean",
        ])
        .arg(project.path().join("missing-lean"))
        .arg("--artifacts")
        .arg(&evidence)
        .output()
        .unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 3, "{receipt}");
    assert_eq!(receipt["phase"], "capture-tool", "{receipt}");
    let req: serde_json::Value =
        serde_json::from_slice(&fs::read(evidence.join("request.json")).unwrap()).unwrap();
    assert_eq!(req["compilation"]["source_root"], "rust");
    assert_eq!(req["compilation"]["crate_root"], "lib.rs");
    assert_eq!(req["compilation"]["source_files"], serde_json::json!(["lib.rs", "sub.rs"]));
    assert_eq!(req["proof"]["source_root"], "authored");
    assert_eq!(req["proof"]["specification_module"], "Contract");
    assert_eq!(req["proof"]["specification"], "StarnixEbpf.Contract.specs");
    assert_eq!(req["proof"]["theorem_module"], "Spec.Helper");
    assert_eq!(req["proof"]["theorem"], "Proof.custom");
    assert_eq!(
        req["proof"]["sources"],
        serde_json::json!([
            {"module": "Contract", "path": "Contract.lean", "role": "specification"},
            {"module": "Spec.Helper", "path": "Spec/Helper.lean", "role": "proof"},
        ])
    );

    // FIFO symlink target must fail immediately without hanging.
    let fifo = project.path().join("pipe.rs");
    assert!(Command::new("mkfifo").arg(&fifo).status().unwrap().success());
    let fifo_link = runfiles.join("fifo.rs");
    symlink(&fifo, &fifo_link).unwrap();
    let fifo_out = command(Route::Direct, project.path())
        .args(["verify", "--format", "json"])
        .arg("--capture")
        .arg(project.path().join("missing-capture"))
        .arg("--sysroot")
        .arg(project.path())
        .arg("--lean")
        .arg(project.path().join("missing-lean"))
        .arg("rustc")
        .arg(&fifo_link)
        .args(["--crate-name", "sample", "--spec-file"])
        .arg(format!("Spec={}", runfiles.join("Contract.lean").display()))
        .arg("--proof-file")
        .arg(format!("Proof={}", runfiles.join("Spec.Helper.lean").display()))
        .output()
        .unwrap();
    assert_result(&fifo_out, 1, "", "");
    let fifo_receipt: serde_json::Value = serde_json::from_slice(&fifo_out.stdout).unwrap();
    assert_eq!(fifo_receipt["status"], "unsupported");
    assert_eq!(fifo_receipt["phase"], "inputs");
}

#[test]
fn rustc_mode_rejects_reserved_or_mismatched_proof_modules_before_capture() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let lib = project.path().join("lib.rs");
    let spec = project.path().join("Spec.lean");
    let proof = project.path().join("Proof.lean");
    fs::write(&lib, b"pub fn zero() -> u64 { 0 }\n").unwrap();
    fs::write(&spec, b"-- spec\n").unwrap();
    fs::write(&proof, b"-- proof\n").unwrap();

    // Reserved module name (`Trusted`) must be rejected before capture.
    let reserved_out = command(Route::Direct, project.path())
        .args(["verify", "--format", "json", "rustc"])
        .arg(&lib)
        .args(["--crate-name", "sample", "--spec-file"])
        .arg(format!("Trusted={}", spec.display()))
        .arg("--proof-file")
        .arg(format!("Proof={}", proof.display()))
        .args([
            "--spec-decl",
            "Trusted:Trusted.specs",
            "--capture",
            "missing-capture",
            "--sysroot",
            "missing-sysroot",
            "--lean",
            "missing-lean",
        ])
        .output()
        .unwrap();
    assert_result(&reserved_out, 1, "", "");
    let reserved_receipt: serde_json::Value = serde_json::from_slice(&reserved_out.stdout).unwrap();
    assert_eq!(reserved_receipt["status"], "unsupported");
    assert_eq!(reserved_receipt["phase"], "proof");

    // Unknown `--spec-decl` module or role mismatch must be rejected early
    // before capture runs.
    for extra in [
        &["--spec-decl", "Missing:Missing.specs"][..],
        &["--theorem", "Missing:Missing.verify"][..],
        &["--spec-decl", "Proof:Proof.specs"][..],
        &["--theorem", "Spec:Spec.verify"][..],
    ] {
        let out = command(Route::Direct, project.path())
            .args(["verify", "--format", "json", "rustc"])
            .arg(&lib)
            .args(["--crate-name", "sample", "--spec-file"])
            .arg(format!("Spec={}", spec.display()))
            .arg("--proof-file")
            .arg(format!("Proof={}", proof.display()))
            .args(extra)
            .args([
                "--capture",
                "missing-capture",
                "--sysroot",
                "missing-sysroot",
                "--lean",
                "missing-lean",
            ])
            .output()
            .unwrap();
        assert_result(&out, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(receipt["status"], "unsupported", "{extra:?}: {receipt}");
        assert_eq!(receipt["phase"], "proof", "{extra:?}: {receipt}");
    }
}

#[test]
fn unsandboxed_elaboration_flag_marks_early_failure_receipt_tainted() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let mut cmd = command(Route::Direct, project.path());
    cmd.args(["verify", "--format", "json", "--allow-unsandboxed-elaboration", "--request"])
        .arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "", "TAINTED");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 3, "{receipt}");
    assert_eq!(
        receipt["taint_reasons"],
        serde_json::json!(["unsandboxed_elaboration"]),
        "{receipt}"
    );
    assert_eq!(receipt["status"], "unsupported", "{receipt}");
    assert_eq!(receipt["phase"], "request", "{receipt}");
    assert!(
        receipt.get("elaboration_sandbox").is_none(),
        "pre-sandbox failure must omit elaboration_sandbox: {receipt}"
    );
}

#[test]
fn taint_monoid_combines_all_three_allow_flags_in_canonical_order() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let mut cmd = command(Route::Direct, project.path());
    // Pass relaxation flags in reverse lexicographical order to confirm the
    // receipt projects a canonical sorted `BTreeSet<VerificationTaint>`.
    cmd.args([
        "verify",
        "--format",
        "json",
        "--allow-unsandboxed-elaboration",
        "--allow-unpinned-lean",
        "--allow-sorry-in-proof",
        "--lean",
        "fake-lean",
        "--request",
    ])
    .arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "", "TAINTED");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--allow-sorry-in-proof"), "{stderr}");
    assert!(stderr.contains("--allow-unpinned-lean"), "{stderr}");
    assert!(stderr.contains("--allow-unsandboxed-elaboration"), "{stderr}");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["schema_version"], 3, "{receipt}");
    assert_eq!(
        receipt["taint_reasons"],
        serde_json::json!(["sorry_in_proof", "unpinned_lean", "unsandboxed_elaboration"]),
        "{receipt}"
    );
    assert_eq!(receipt["status"], "unsupported", "{receipt}");
    assert_eq!(receipt["phase"], "request", "{receipt}");
    assert!(
        receipt.get("elaboration_sandbox").is_none(),
        "pre-sandbox failure must omit elaboration_sandbox: {receipt}"
    );
}

#[test]
fn verify_rejects_smuggled_env_key_in_request_json() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(
        &request,
        serde_json::to_vec(&serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "lib.rs",
                "crate_name": "demo",
                "env": { "A=B": "C" },
                "source_files": ["lib.rs"]
            },
            "scope": { "kind": "selected_unit", "roots": ["f"] },
            "proof": {
                "source_root": ".",
                "sources": []
            }
        }))
        .unwrap(),
    )
    .unwrap();
    let mut cmd = command(Route::Direct, project.path());
    cmd.args(["verify", "--format", "json", "--request"]).arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["status"], "unsupported", "{receipt}");
    assert_eq!(receipt["phase"], "request", "{receipt}");
    assert!(receipt["detail"].as_str().unwrap_or("").contains("must not contain '='"), "{receipt}");
}

#[cfg(unix)]
#[test]
fn verify_passes_env_flags_and_rejects_mismatched_capture_env() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    fs::write(project.path().join("lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"").unwrap();
    fs::write(project.path().join("Proof.lean"), b"").unwrap();
    let sysroot = project.path().join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.path().join("lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    let recorded_args = project.path().join("capture_args.txt");
    let fake_capture = project.path().join("fake-capture");
    // Emit a syntactically valid schema-5 capture manifest whose
    // `configuration.env` disagrees with the requested `--env` binding.
    let script = format!(
        "#!/bin/sh\n\
         out_dir=\"\"\n\
         : > \"{args_file}\"\n\
         while [ \"$#\" -gt 0 ]; do\n\
           printf '%s\\n' \"$1\" >> \"{args_file}\"\n\
           if [ \"$1\" = \"--out-dir\" ]; then\n\
             shift\n\
             out_dir=\"$1\"\n\
             printf '%s\\n' \"$1\" >> \"{args_file}\"\n\
           fi\n\
           shift\n\
         done\n\
         mkdir -p \"$out_dir\"\n\
         cat > \"$out_dir/capture.json\" <<'JSON'\n\
         {{\n\
           \"schema_version\": 5,\n\
           \"compiler\": {{\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"}},\n\
           \"configuration\": {{\n\
             \"crate_root\": \"lib.rs\",\n\
             \"crate_name\": \"demo\",\n\
             \"crate_type\": \"lib\",\n\
             \"panic\": \"unwind\",\n\
             \"overflow_checks\": false,\n\
             \"target\": \"x86_64-unknown-linux-gnu\",\n\
             \"edition\": \"2024\",\n\
             \"cfg\": [],\n\
             \"env\": {{\"CARGO_PKG_VERSION\": \"0.0.0-mismatch\"}}\n\
           }},\n\
           \"source_files\": [],\n\
           \"census\": [],\n\
           \"selected\": [],\n\
           \"program\": {{\"scope\": {{\"kind\": \"selected_unit\", \"roots\": [\"f\"]}}, \"bodies\": []}}\n\
         }}\n\
         JSON\n\
         printf '{{\"status\":\"captured\"}}\\n'\n",
        args_file = recorded_args.display(),
    );
    fs::write(&fake_capture, script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    let output = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--env",
            "CARGO_PKG_VERSION=0.8.64",
            "--select",
            "f",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ])
        .output()
        .unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["status"], "tool_failed", "{receipt}");
    assert_eq!(receipt["phase"], "capture", "{receipt}");
    assert!(
        receipt["detail"]
            .as_str()
            .unwrap_or("")
            .contains("capture differs from the requested compilation or scope"),
        "{receipt}"
    );
    let args_text = fs::read_to_string(&recorded_args).unwrap();
    let recorded_lines: Vec<&str> = args_text.lines().collect();
    assert!(
        recorded_lines.contains(&"--env=CARGO_PKG_VERSION=0.8.64"),
        "expected --env=CARGO_PKG_VERSION=0.8.64 in capture args:\n{args_text}"
    );
    assert!(
        recorded_lines.windows(2).any(|w| w == ["--crate-type", "lib"]),
        "expected --crate-type lib in capture args:\n{args_text}"
    );
    assert!(
        recorded_lines.windows(2).any(|w| w == ["--panic", "unwind"]),
        "expected --panic unwind in capture args:\n{args_text}"
    );

    // Also confirm `cargo-anneal` rejects capture manifests whose reported
    // `crate_type`, `panic` strategy, or `overflow_checks` setting disagrees
    // with the request.
    for (bad_crate_type, bad_panic, bad_overflow, req_crate_type, req_panic, req_overflow) in [
        ("lib", "unwind", false, "bin", "unwind", false),
        ("bin", "unwind", false, "bin", "abort", false),
        ("bin", "unwind", true, "bin", "unwind", false),
        ("bin", "unwind", false, "bin", "unwind", true),
    ] {
        let mismatch_script = format!(
            "#!/bin/sh\n\
             out_dir=\"\"\n\
             while [ \"$#\" -gt 0 ]; do\n\
               if [ \"$1\" = \"--out-dir\" ]; then shift; out_dir=\"$1\"; fi\n\
               shift\n\
             done\n\
             mkdir -p \"$out_dir\"\n\
             cat > \"$out_dir/capture.json\" <<'JSON'\n\
             {{\n\
               \"schema_version\": 5,\n\
               \"compiler\": {{\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"}},\n\
               \"configuration\": {{\n\
                 \"crate_root\": \"lib.rs\",\n\
                 \"crate_name\": \"demo\",\n\
                 \"crate_type\": \"{bad_crate_type}\",\n\
                 \"panic\": \"{bad_panic}\",\n\
                 \"overflow_checks\": {bad_overflow},\n\
                 \"target\": \"x86_64-unknown-linux-gnu\",\n\
                 \"edition\": \"2024\",\n\
                 \"cfg\": [],\n\
                 \"env\": {{}}\n\
               }},\n\
               \"source_files\": [],\n\
               \"census\": [],\n\
               \"selected\": [],\n\
               \"program\": {{\"scope\": {{\"kind\": \"selected_unit\", \"roots\": [\"f\"]}}, \"bodies\": []}}\n\
             }}\n\
             JSON\n\
             printf '{{\"status\":\"captured\"}}\\n'\n"
        );
        fs::write(&fake_capture, mismatch_script).unwrap();
        fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();
        let mut mismatch_args = vec![
            "verify",
            "--format",
            "json",
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--crate-type",
            req_crate_type,
            "--panic",
            req_panic,
            "--select",
            "f",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ];
        if req_overflow {
            mismatch_args.push("--overflow-checks");
        }
        let mismatch_out =
            command(Route::Direct, project.path()).args(&mismatch_args).output().unwrap();
        assert_result(&mismatch_out, 2, "", "");
        let mismatch_receipt: serde_json::Value =
            serde_json::from_slice(&mismatch_out.stdout).unwrap();
        assert_eq!(mismatch_receipt["status"], "tool_failed", "{mismatch_receipt}");
        assert_eq!(mismatch_receipt["phase"], "capture", "{mismatch_receipt}");
        assert!(
            mismatch_receipt["detail"]
                .as_str()
                .unwrap_or("")
                .contains("capture differs from the requested compilation or scope"),
            "{mismatch_receipt}"
        );
    }
}

#[cfg(unix)]
#[test]
fn verify_rejects_mismatched_capture_crate_root() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    fs::write(project.path().join("lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"").unwrap();
    fs::write(project.path().join("Proof.lean"), b"").unwrap();
    let sysroot = project.path().join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.path().join("lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();
    let fake_capture = project.path().join("fake-capture");
    let script = "#!/bin/sh\n\
         out_dir=\"\"\n\
         while [ \"$#\" -gt 0 ]; do\n\
           if [ \"$1\" = \"--out-dir\" ]; then shift; out_dir=\"$1\"; fi\n\
           shift\n\
         done\n\
         mkdir -p \"$out_dir\"\n\
         cat > \"$out_dir/capture.json\" <<'JSON'\n\
         {\n\
           \"schema_version\": 5,\n\
           \"compiler\": {\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"},\n\
           \"configuration\": {\n\
             \"crate_root\": \"other.rs\",\n\
             \"crate_name\": \"demo\",\n\
             \"crate_type\": \"lib\",\n\
             \"panic\": \"unwind\",\n\
             \"overflow_checks\": false,\n\
             \"target\": \"x86_64-unknown-linux-gnu\",\n\
             \"edition\": \"2024\",\n\
             \"cfg\": [],\n\
             \"env\": {}\n\
           },\n\
           \"source_files\": [],\n\
           \"census\": [],\n\
           \"selected\": [],\n\
           \"program\": {\"scope\": {\"kind\": \"selected_unit\", \"roots\": [\"f\"]}, \"bodies\": []}\n\
         }\n\
         JSON\n\
         printf '{\"status\":\"captured\"}\\n'\n";
    fs::write(&fake_capture, script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    let output = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--select",
            "f",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ])
        .output()
        .unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["status"], "tool_failed", "{receipt}");
    assert_eq!(receipt["phase"], "capture", "{receipt}");
    assert!(
        receipt["detail"]
            .as_str()
            .unwrap_or("")
            .contains("capture differs from the requested compilation or scope"),
        "{receipt}"
    );
}

#[cfg(unix)]
#[test]
fn verify_accepts_equivalent_request_crate_root_spellings() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    fs::create_dir_all(project.path().join("src")).unwrap();
    fs::write(project.path().join("src/lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"").unwrap();
    fs::write(project.path().join("Proof.lean"), b"").unwrap();
    let sysroot = project.path().join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.path().join("lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    let write_fake_capture = |name: &str, crate_root_field: &str| {
        let path = project.path().join(name);
        let script = format!(
            "#!/bin/sh\n\
             out_dir=\"\"\n\
             while [ \"$#\" -gt 0 ]; do\n\
               if [ \"$1\" = \"--out-dir\" ]; then shift; out_dir=\"$1\"; fi\n\
               shift\n\
             done\n\
             mkdir -p \"$out_dir\"\n\
             cat > \"$out_dir/capture.json\" <<'JSON'\n\
             {{\n\
               \"schema_version\": 5,\n\
               \"compiler\": {{\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"}},\n\
               \"configuration\": {{\n\
                 {crate_root_field}\
                 \"crate_name\": \"demo\",\n\
                 \"crate_type\": \"lib\",\n\
                 \"panic\": \"unwind\",\n\
                 \"overflow_checks\": false,\n\
                 \"target\": \"x86_64-unknown-linux-gnu\",\n\
                 \"edition\": \"2024\",\n\
                 \"cfg\": [],\n\
                 \"env\": {{}}\n\
               }},\n\
               \"source_files\": [],\n\
               \"census\": [],\n\
               \"selected\": [],\n\
               \"program\": {{\"scope\": {{\"kind\": \"selected_unit\", \"roots\": [\"f\"]}}, \"bodies\": []}}\n\
             }}\n\
             JSON\n\
             printf -- '-- captured\\n' > \"$out_dir/Captured.lean\"\n\
             printf '{{\"status\":\"captured\"}}\\n'\n"
        );
        fs::write(&path, script).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
        path
    };

    let run_req = |capture_bin: &std::path::Path, crate_root: &str| -> serde_json::Value {
        let req_path = project.path().join("request.json");
        let req = serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": crate_root,
                "crate_name": "demo",
                "crate_type": "lib",
                "panic": "unwind",
                "overflow_checks": false,
                "target": "x86_64-unknown-linux-gnu",
                "edition": "2024",
                "cfg": [],
                "env": {},
                "source_files": [crate_root]
            },
            "scope": { "kind": "selected_unit", "roots": ["f"] },
            "proof": {
                "source_root": ".",
                "sources": [
                    { "module": "Spec", "path": "Spec.lean", "role": "specification" },
                    { "module": "Proof", "path": "Proof.lean", "role": "proof" }
                ],
                "specification": "Spec.specs",
                "theorem": "Proof.verify"
            }
        });
        fs::write(&req_path, serde_json::to_vec(&req).unwrap()).unwrap();
        let output = command(Route::Direct, project.path())
            .args([
                "verify",
                "--format",
                "json",
                "--capture",
                capture_bin.to_str().unwrap(),
                "--sysroot",
                sysroot.to_str().unwrap(),
                "--lean",
                fake_lean.to_str().unwrap(),
                "--request",
                req_path.to_str().unwrap(),
            ])
            .output()
            .unwrap();
        assert_result(&output, 2, "", "");
        serde_json::from_slice(&output.stdout).unwrap()
    };

    // Component-equivalent spellings admitted by `declared_file` must pass
    // capture authentication against normalized `src/lib.rs` and reach audit.
    let norm_cap = write_fake_capture("fake-capture-norm", "\"crate_root\": \"src/lib.rs\",\n");
    for spelling in ["src//lib.rs", "src/./lib.rs"] {
        let receipt = run_req(&norm_cap, spelling);
        assert_eq!(receipt["phase"], "audit", "spelling={spelling}: {receipt}");
    }

    // Missing or non-string `crate_root` in `capture.json` still fails closed.
    let missing_cap = write_fake_capture("fake-capture-missing", "");
    let nonstr_cap = write_fake_capture("fake-capture-nonstr", "\"crate_root\": 123,\n");
    for bad_cap in [&missing_cap, &nonstr_cap] {
        let receipt = run_req(bad_cap, "src/lib.rs");
        assert_eq!(receipt["phase"], "capture", "{receipt}");
        assert!(
            receipt["detail"]
                .as_str()
                .unwrap_or("")
                .contains("capture differs from the requested compilation or scope"),
            "{receipt}"
        );
    }
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

#[cfg(unix)]
#[test]
fn verify_passes_stdlib_crate_flag_and_rejects_mismatched_capture_capability() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    fs::write(project.path().join("lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"").unwrap();
    fs::write(project.path().join("Proof.lean"), b"").unwrap();
    let sysroot = project.path().join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.path().join("lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();
    let recorded_args = project.path().join("capture_args.txt");
    let fake_capture = project.path().join("fake-capture");

    // A capture with relaxed language-item admission must never satisfy a
    // request that did not ask for it, and vice versa.
    for (request_capability, manifest_capability) in [(true, ""), (false, "\"core\"")] {
        let stdlib_field = if manifest_capability.is_empty() {
            String::new()
        } else {
            format!(",\\n\"stdlib_crate\": {manifest_capability}")
        };
        let script = format!(
            "#!/bin/sh\n\
             out_dir=\"\"\n\
             : > \"{args_file}\"\n\
             while [ \"$#\" -gt 0 ]; do\n\
               printf '%s\\n' \"$1\" >> \"{args_file}\"\n\
               if [ \"$1\" = \"--out-dir\" ]; then shift; out_dir=\"$1\"; fi\n\
               shift\n\
             done\n\
             mkdir -p \"$out_dir\"\n\
             printf '{{\\n\
               \"schema_version\": 5,\\n\
               \"compiler\": {{\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"}},\\n\
               \"configuration\": {{\\n\
                 \"crate_root\": \"lib.rs\",\\n\
                 \"crate_name\": \"core\",\\n\
                 \"crate_type\": \"lib\",\\n\
                 \"panic\": \"unwind\",\\n\
                 \"overflow_checks\": false,\\n\
                 \"target\": \"x86_64-unknown-linux-gnu\",\\n\
                 \"edition\": \"2024\",\\n\
                 \"cfg\": [],\\n\
                 \"env\": {{}}{stdlib_field}\\n\
               }},\\n\
               \"source_files\": [],\\n\
               \"census\": [],\\n\
               \"selected\": [],\\n\
               \"program\": {{\"scope\": {{\"kind\": \"selected_unit\", \"roots\": [\"f\"]}}, \"bodies\": []}}\\n\
             }}\\n' > \"$out_dir/capture.json\"\n\
             printf '{{\"status\":\"captured\"}}\\n'\n",
            args_file = recorded_args.display(),
        );
        fs::write(&fake_capture, script).unwrap();
        fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();
        let mut args = vec![
            "verify",
            "--format",
            "json",
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "rustc",
            "lib.rs",
            "--crate-name",
            "core",
            "--select",
            "f",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ];
        if request_capability {
            args.extend(["--stdlib-crate", "core"]);
        }
        let output = command(Route::Direct, project.path()).args(&args).output().unwrap();
        assert_result(&output, 2, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["status"], "tool_failed", "{receipt}");
        assert_eq!(receipt["phase"], "capture", "{receipt}");
        assert!(
            receipt["detail"]
                .as_str()
                .unwrap_or("")
                .contains("capture differs from the requested compilation or scope"),
            "{receipt}"
        );
        let args_text = fs::read_to_string(&recorded_args).unwrap();
        let recorded: Vec<&str> = args_text.lines().collect();
        assert_eq!(
            recorded.windows(2).any(|w| w == ["--stdlib-crate", "core"]),
            request_capability,
            "capture args:\n{args_text}"
        );
    }
}

#[cfg(unix)]
#[test]
fn verify_rejects_whole_crate_stdlib_crate_as_unsupported() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    fs::write(project.path().join("lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"").unwrap();
    fs::write(project.path().join("Proof.lean"), b"").unwrap();
    let sysroot = project.path().join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.path().join("fake-lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();
    let capture_invoked = project.path().join("capture_invoked");
    let fake_capture = project.path().join("fake-capture");
    let capture_script = format!("#!/bin/sh\n: > {:?}\nexit 99\n", capture_invoked.display());
    fs::write(&fake_capture, capture_script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    let request_path = project.path().join("request.json");
    fs::write(
        &request_path,
        r#"{
  "schema_version": 1,
  "compilation": {
    "source_root": ".",
    "crate_root": "lib.rs",
    "crate_name": "core",
    "source_files": ["lib.rs"],
    "stdlib_crate": "core"
  },
  "scope": {"kind": "crate"},
  "proof": {
    "source_root": ".",
    "specification": "Spec.specs",
    "theorem": "Proof.verify",
    "sources": [
      {"module": "Spec", "path": "Spec.lean", "role": "specification"},
      {"module": "Proof", "path": "Proof.lean", "role": "proof"}
    ]
  }
}
"#,
    )
    .unwrap();

    let request_args = [
        "verify",
        "--format",
        "json",
        "--capture",
        fake_capture.to_str().unwrap(),
        "--sysroot",
        sysroot.to_str().unwrap(),
        "--lean",
        fake_lean.to_str().unwrap(),
        "--request",
        request_path.to_str().unwrap(),
    ];
    let rustc_args = [
        "verify",
        "--format",
        "json",
        "--capture",
        fake_capture.to_str().unwrap(),
        "--sysroot",
        sysroot.to_str().unwrap(),
        "--lean",
        fake_lean.to_str().unwrap(),
        "rustc",
        "lib.rs",
        "--crate-name",
        "core",
        "--stdlib-crate",
        "core",
        "--spec-file",
        "Spec=Spec.lean",
        "--proof-file",
        "Proof=Proof.lean",
    ];
    for args in [&request_args[..], &rustc_args[..]] {
        let output = command(Route::Direct, project.path()).args(args).output().unwrap();
        assert_result(&output, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(receipt["status"], "unsupported", "{receipt}");
        assert_eq!(receipt["phase"], "request", "{receipt}");
        assert!(
            receipt["detail"]
                .as_str()
                .unwrap_or("")
                .contains("--stdlib-crate requires selected scope"),
            "{receipt}"
        );
        assert!(!capture_invoked.exists(), "capture should not be invoked for {args:?}");
    }
}

#[test]
fn verify_passes_instantiate_flags_and_rejects_mismatched_capture_scope() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    fs::write(project.path().join("lib.rs"), b"pub fn id<T>(x: T) -> T { x }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"-- spec\n").unwrap();
    fs::write(project.path().join("Proof.lean"), b"-- proof\n").unwrap();

    // Malformed `--instantiate` JSON and `--request` + `--instantiate` conflict
    // must fail CLI validation with exit 2 and empty stdout.
    for bad in [
        &["verify", "--request", "r.json", "--instantiate", r#"{"path":"id","args":["usize"]}"#][..],
        &[
            "verify",
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--instantiate",
            "not-json",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ][..],
    ] {
        let output = command(Route::Direct, project.path()).args(bad).output().unwrap();
        assert_result(&output, 2, "", "error:");
        assert!(output.stdout.is_empty(), "{bad:?}: {output:?}");
    }

    let sysroot = project.path().join("sysroot");
    fs::create_dir(&sysroot).unwrap();
    let fake_lean = project.path().join("fake-lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    let recorded_args = project.path().join("capture.args");
    let fake_capture = project.path().join("fake-capture");
    // Emit a capture manifest whose scope omits the requested instantiation so
    // cargo-anneal rejects the mismatched scope before invoking Lean.
    let script = format!(
        "#!/bin/sh\n\
         set -eu\n\
         printf '%s\\n' \"$@\" > {args_file:?}\n\
         out_dir=''\n\
         while [ \"$#\" -gt 0 ]; do\n\
           if [ \"$1\" = '--out-dir' ]; then\n\
             shift\n\
             out_dir=\"$1\"\n\
           fi\n\
           shift\n\
         done\n\
         mkdir -p \"$out_dir\"\n\
         cat > \"$out_dir/capture.json\" <<'JSON'\n\
         {{\n\
           \"schema_version\": 5,\n\
           \"compiler\": {{\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"}},\n\
           \"configuration\": {{\n\
             \"crate_root\": \"lib.rs\",\n\
             \"crate_name\": \"demo\",\n\
             \"target\": \"x86_64-unknown-linux-gnu\",\n\
             \"edition\": \"2024\",\n\
             \"cfg\": [],\n\
             \"env\": {{}}\n\
           }},\n\
           \"source_files\": [],\n\
           \"census\": [],\n\
           \"selected\": [],\n\
           \"program\": {{\"scope\": {{\"kind\": \"selected_unit\", \"roots\": []}}, \"bodies\": []}}\n\
         }}\n\
         JSON\n\
         printf '{{\"status\":\"captured\"}}\\n'\n",
        args_file = recorded_args.display(),
    );
    fs::write(&fake_capture, script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    let output = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--instantiate",
            r#"{"path":"id","args":["usize"]}"#,
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ])
        .output()
        .unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["status"], "tool_failed", "{receipt}");
    assert_eq!(receipt["phase"], "capture", "{receipt}");
    assert!(
        receipt["detail"]
            .as_str()
            .unwrap_or("")
            .contains("capture differs from the requested compilation or scope"),
        "{receipt}"
    );
    let args_text = fs::read_to_string(&recorded_args).unwrap();
    assert!(
        args_text.lines().any(|line| line == r#"{"path":"id","args":["usize"]}"#),
        "expected serialized --instantiate JSON in capture args:\n{args_text}"
    );
}

#[test]
fn testkit_parses_cli_failure_receipt_cleanly() {
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    std::fs::write(&request, b"not JSON\n").unwrap();
    let mut cmd = command(Route::Direct, project.path());
    cmd.args(["verify", "--format", "json"]).arg("--request").arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "", "");
    let parsed = anneal_testkit::VerifyReceipt::from_json_slice(&output.stdout).unwrap();
    anneal_testkit::assert_rejected(&parsed, "unsupported", Some("request"), "").unwrap();
}

#[test]
fn init_scaffolds_cargo_and_standalone_without_overwriting() {
    use std::fs;

    for route in [Route::Direct, Route::Cargo] {
        let project = tempfile::tempdir().unwrap();
        let no_manifest = command(route, project.path()).arg("init").output().unwrap();
        assert_result(&no_manifest, 1, "", "no Cargo.toml found");

        fs::write(project.path().join("Cargo.toml"), "[workspace]\nmembers = [\"a\"]\n").unwrap();
        let workspace = command(route, project.path()).arg("init").output().unwrap();
        assert_result(&workspace, 1, "", "virtual workspace");

        fs::write(
            project.path().join("Cargo.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        let ok = command(route, project.path()).arg("init").output().unwrap();
        assert_result(&ok, 0, "Initialized Anneal proof files:", "");
        assert!(project.path().join("proof/Spec.lean").is_file());
        assert!(project.path().join("proof/Proof.lean").is_file());
        let spec_text = fs::read_to_string(project.path().join("proof/Spec.lean")).unwrap();
        let proof_text = fs::read_to_string(project.path().join("proof/Proof.lean")).unwrap();
        assert!(spec_text.starts_with("module\nprelude\npublic import Trusted.MirSemantics"));
        assert!(spec_text.contains("@[expose] public section"));
        assert!(!spec_text.contains("sorry"));
        assert!(proof_text.starts_with("module\nprelude\npublic import Expected"));
        assert!(proof_text.contains("public theorem verify : Expected.claim"));

        let second = command(route, project.path()).arg("init").output().unwrap();
        assert_result(&second, 1, "", "refusing to overwrite existing file");

        let standalone_dir = project.path().join("hello");
        let standalone = command(route, project.path())
            .args(["init", "--standalone", "--proof-dir"])
            .arg(&standalone_dir)
            .output()
            .unwrap();
        assert_result(&standalone, 0, "cargo anneal verify --request", "");
        for name in ["lib.rs", "request.json", "Spec.lean", "Proof.lean"] {
            assert!(standalone_dir.join(name).is_file(), "missing {name}");
        }
        let sa_spec = fs::read_to_string(standalone_dir.join("Spec.lean")).unwrap();
        let sa_proof = fs::read_to_string(standalone_dir.join("Proof.lean")).unwrap();
        assert!(sa_spec.starts_with("module\nprelude\npublic import Trusted.MirSemantics"));
        assert!(sa_proof.contains("public theorem verify : Expected.claim"));
    }
}

#[test]
fn init_profile_v2_scaffolds_specs_v2_and_conflicts_with_standalone() {
    use std::fs;

    for route in [Route::Direct, Route::Cargo] {
        let project = tempfile::tempdir().unwrap();
        fs::write(
            project.path().join("Cargo.toml"),
            "[package]\nname = \"demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        )
        .unwrap();
        let ok = command(route, project.path()).args(["init", "--profile", "v2"]).output().unwrap();
        assert_result(&ok, 0, "mir_profile_version = 2", "");
        let spec_text = fs::read_to_string(project.path().join("proof/Spec.lean")).unwrap();
        let proof_text = fs::read_to_string(project.path().join("proof/Proof.lean")).unwrap();
        assert!(spec_text.contains("def specs : SpecsV2 where"), "{spec_text}");
        assert!(proof_text.contains("public theorem verify : Expected.claim"), "{proof_text}");

        let conflict = command(route, project.path())
            .args(["init", "--standalone", "--profile", "v2", "--proof-dir"])
            .arg(project.path().join("standalone"))
            .output()
            .unwrap();
        assert_result(&conflict, 2, "", "cannot be used with");
        assert!(!project.path().join("standalone").exists());
    }
}

#[test]
fn failure_receipts_emit_actionable_hints_while_preserving_detail() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    fs::create_dir_all(project.path().join("crate_proc_macro/src")).unwrap();
    fs::create_dir_all(project.path().join("crate_proc_macro/proof")).unwrap();
    fs::write(
        project.path().join("crate_proc_macro/Cargo.toml"),
        "[package]\nname = \"pm_demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\nproc-macro = true\n",
    )
    .unwrap();
    fs::write(project.path().join("crate_proc_macro/src/lib.rs"), b"pub fn f() -> u64 { 0 }\n")
        .unwrap();

    // 1. Missing Cargo manifest names the path and sets a clear hint.
    let missing_manifest = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--manifest-path",
            "absent/Cargo.toml",
            "--proof-dir",
            "crate_proc_macro/proof",
        ])
        .args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"])
        .output()
        .unwrap();
    assert_result(&missing_manifest, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&missing_manifest.stdout).unwrap();
    assert_eq!(receipt["phase"], "cargo");
    assert!(receipt["detail"].as_str().unwrap().contains("Cargo.toml"), "{receipt}");
    assert!(receipt["hint"].as_str().unwrap().contains("--manifest-path"), "{receipt}");

    // 2. Cargo shortcut refusal preserves detail and suggests `--request` / `skill --example`.
    let feat_out = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--manifest-path",
            "crate_proc_macro/Cargo.toml",
            "--proof-dir",
            "crate_proc_macro/proof",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--lean",
            "lean",
        ])
        .output()
        .unwrap();
    assert_result(&feat_out, 1, "", "");
    let feat_receipt: serde_json::Value = serde_json::from_slice(&feat_out.stdout).unwrap();
    assert_eq!(feat_receipt["phase"], "cargo");
    assert_eq!(
        feat_receipt["detail"],
        "build scripts and procedural macros need an explicit configured compilation"
    );
    assert!(feat_receipt["hint"].as_str().unwrap().contains("--request"), "{feat_receipt}");

    // 3. Missing `--proof-dir` names the path and suggests `cargo anneal init`.
    fs::create_dir_all(project.path().join("crate_ok/src")).unwrap();
    fs::create_dir_all(project.path().join("crate_ok/proof")).unwrap();
    fs::write(
        project.path().join("crate_ok/Cargo.toml"),
        "[package]\nname = \"ok_demo\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(project.path().join("crate_ok/src/lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    let dummy_sysroot = project.path().join("dummy-sysroot");
    fs::create_dir(&dummy_sysroot).unwrap();
    let dummy_capture = project.path().join("dummy-capture");
    let dummy_lean = project.path().join("dummy-lean");
    fs::write(&dummy_capture, b"stub\n").unwrap();
    fs::write(&dummy_lean, b"stub\n").unwrap();
    let missing_proof_dir = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--manifest-path",
            "crate_ok/Cargo.toml",
            "--proof-dir",
            "crate_ok/missing-proof",
            "--capture",
        ])
        .arg(&dummy_capture)
        .arg("--sysroot")
        .arg(&dummy_sysroot)
        .arg("--lean")
        .arg(&dummy_lean)
        .output()
        .unwrap();
    assert_result(&missing_proof_dir, 2, "", "");
    let proof_receipt: serde_json::Value =
        serde_json::from_slice(&missing_proof_dir.stdout).unwrap();
    assert_eq!(proof_receipt["phase"], "proof");
    assert!(
        proof_receipt["detail"].as_str().unwrap().contains("cannot inspect proof directory"),
        "{proof_receipt}"
    );
    assert!(
        proof_receipt["hint"].as_str().unwrap().contains("cargo anneal init"),
        "{proof_receipt}"
    );

    // 4. Missing capture tool emits setup/explicit-tool guidance.
    let missing_explicit = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--manifest-path",
            "crate_ok/Cargo.toml",
            "--proof-dir",
            "crate_ok/proof",
            "--capture",
            "absent-capture",
            "--sysroot",
        ])
        .arg(&dummy_sysroot)
        .arg("--lean")
        .arg(&dummy_lean)
        .output()
        .unwrap();
    assert_result(&missing_explicit, 2, "", "");
    let explicit_receipt: serde_json::Value =
        serde_json::from_slice(&missing_explicit.stdout).unwrap();
    assert_eq!(explicit_receipt["phase"], "capture-tool");
    assert!(
        explicit_receipt["hint"].as_str().unwrap().contains("`--capture`"),
        "{explicit_receipt}"
    );
    #[cfg(feature = "setup")]
    {
        // Under `cargo test --workspace`, Cargo builds `anneal-rustc-capture`
        // beside `CARGO_BIN_EXE_cargo-anneal`; stage an isolated `cargo-anneal`
        // binary in an empty directory so sibling fallback cannot find it.
        let isolated_dir = project.path().join("isolated-bin");
        fs::create_dir(&isolated_dir).unwrap();
        let exe_name = Path::new(env!("CARGO_BIN_EXE_cargo-anneal-test-bin")).file_name().unwrap();
        let isolated_cli = isolated_dir.join(exe_name);
        if fs::hard_link(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"), &isolated_cli).is_err() {
            #[cfg(unix)]
            {
                let stage = Command::new("/bin/sh")
                    .arg("-ceu")
                    .arg("cp \"$1\" \"$2\"")
                    .arg("sh")
                    .arg(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"))
                    .arg(&isolated_cli)
                    .output()
                    .unwrap();
                assert_result(&stage, 0, "", "");
            }
            #[cfg(not(unix))]
            fs::copy(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"), &isolated_cli).unwrap();
        }
        let empty_cache = project.path().join("empty-cache");
        let missing_tools = Command::new(&isolated_cli)
            .current_dir(project.path())
            .env("XDG_CACHE_HOME", &empty_cache)
            .env("HOME", &empty_cache)
            .env_remove("ANNEAL_CAPTURE")
            .env_remove("ANNEAL_SYSROOT")
            .env_remove("ANNEAL_LEAN")
            .args([
                "verify",
                "--format",
                "json",
                "--manifest-path",
                "crate_ok/Cargo.toml",
                "--proof-dir",
                "crate_ok/proof",
            ])
            .output()
            .unwrap();
        assert_result(&missing_tools, 2, "", "");
        let tool_receipt: serde_json::Value =
            serde_json::from_slice(&missing_tools.stdout).unwrap();
        assert_eq!(tool_receipt["phase"], "capture-tool");
        assert!(tool_receipt["hint"].as_str().unwrap().contains("setup"), "{tool_receipt}");
    }

    // 5. Capture JSON envelope remains valid JSON in `detail` while `hint` explains Rust MIR bounds.
    #[cfg(unix)]
    {
        let fake_capture = project.path().join("fake-capture");
        let body = "#!/bin/sh\n\
            printf '%s\\n' '{\"status\":\"unsupported\",\"diagnostics\":[\"1 required obligations are unsupported\"],\"unsupported\":[{\"def_id\":3,\"path\":\"take_ref\",\"reason\":\"unsupported type: &\\u0027{erased} u64\"}]}'\n\
            exit 1\n";
        let stage = Command::new("/bin/sh")
            .arg("-ceu")
            .arg("printf '%s' \"$1\" > \"$2\" && chmod 0755 \"$2\"")
            .arg("sh")
            .arg(body)
            .arg(&fake_capture)
            .output()
            .unwrap();
        assert_result(&stage, 0, "", "");

        fs::write(project.path().join("crate_ok/proof/Spec.lean"), b"prelude\n").unwrap();
        fs::write(project.path().join("crate_ok/proof/Proof.lean"), b"prelude\n").unwrap();
        let sysroot = project.path().join("sysroot");
        fs::create_dir(&sysroot).unwrap();
        let fake_lean = project.path().join("fake-lean");
        fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();

        let cap_out = command(Route::Direct, project.path())
            .args([
                "verify",
                "--format",
                "json",
                "--manifest-path",
                "crate_ok/Cargo.toml",
                "--proof-dir",
                "crate_ok/proof",
                "--capture",
            ])
            .arg(&fake_capture)
            .arg("--sysroot")
            .arg(&sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .output()
            .unwrap();
        assert_result(&cap_out, 1, "", "");
        let cap_receipt: serde_json::Value = serde_json::from_slice(&cap_out.stdout).unwrap();
        assert_eq!(cap_receipt["phase"], "capture");
        let parsed_detail: serde_json::Value =
            serde_json::from_str(cap_receipt["detail"].as_str().unwrap()).unwrap();
        assert_eq!(parsed_detail["unsupported"][0]["path"], "take_ref");
        let hint = cap_receipt["hint"].as_str().unwrap();
        assert!(hint.contains("`take_ref`") && hint.contains("references"), "{cap_receipt}");
    }
}
#[test]
fn default_verify_format_is_human_and_format_json_never_emits_ansi() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    fs::write(&request, b"not JSON\n").unwrap();

    // 1. Default invocation (`--format` omitted) emits human `[FAIL]` card with
    //    zero ANSI on non-TTY pipes even when `CI=true`.
    let mut default_cmd = command(Route::Direct, project.path());
    default_cmd
        .env_remove("CARGO_TERM_COLOR")
        .env_remove("CLICOLOR_FORCE")
        .env_remove("FORCE_COLOR")
        .env("CI", "true")
        .args(["verify", "--request"])
        .arg(&request);
    #[cfg(not(feature = "setup"))]
    default_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let default_out = default_cmd.output().unwrap();
    assert_result(
        &default_out,
        1,
        "[FAIL] VERIFICATION FAILED (unsupported in phase `request`, exit 1)",
        "",
    );
    let default_stdout = String::from_utf8(default_out.stdout).unwrap();
    assert!(
        !default_stdout.contains('\x1b'),
        "non-TTY pipe must omit ANSI even when CI=true:\n{default_stdout}"
    );
    assert!(!default_stdout.contains("[OK]"), "{default_stdout}");

    // 2. `--color always` styles human cards with SGR, while
    //    `--format json --color always` remains pure RFC 8259 JSON with zero
    //    ANSI escapes.
    let mut colored_human = command(Route::Direct, project.path());
    colored_human.args(["--color", "always", "verify", "--request"]).arg(&request);
    #[cfg(not(feature = "setup"))]
    colored_human.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let colored_out = colored_human.output().unwrap();
    let colored_stdout = String::from_utf8(colored_out.stdout).unwrap();
    assert!(colored_stdout.contains("\x1b[1;31m[FAIL]\x1b[0m"), "{colored_stdout}");

    let mut colored_json = command(Route::Direct, project.path());
    colored_json
        .args(["--color", "always", "verify", "--format", "json", "--request"])
        .arg(&request);
    #[cfg(not(feature = "setup"))]
    colored_json.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let json_out = colored_json.output().unwrap();
    assert_eq!(json_out.status.code(), Some(1));
    assert!(!json_out.stdout.contains(&0x1b), "JSON stdout must never contain ESC");
    let parsed: serde_json::Value = serde_json::from_slice(&json_out.stdout).unwrap();
    assert_eq!(parsed["schema_version"], 3);
    assert_eq!(parsed["status"], "unsupported");

    // 3. `--format auto` resolves to JSON when stdout is piped.
    let mut auto_cmd = command(Route::Direct, project.path());
    auto_cmd.args(["verify", "--format", "auto", "--request"]).arg(&request);
    #[cfg(not(feature = "setup"))]
    auto_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let auto_out = auto_cmd.output().unwrap();
    assert_eq!(auto_out.status.code(), Some(1));
    let auto_parsed: serde_json::Value = serde_json::from_slice(&auto_out.stdout).unwrap();
    assert_eq!(auto_parsed["schema_version"], 3);
}

#[cfg(unix)]
#[test]
fn receipt_out_persists_valid_v3_json_and_rejects_symlinks_dirs_and_input_aliases() {
    use std::{
        fs,
        os::unix::fs::{PermissionsExt as _, symlink},
    };

    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    let precious_bytes = b"precious caller source bytes\n";
    fs::write(&request, precious_bytes).unwrap();

    // 1. Valid `--receipt-out` alongside default `--format human` writes atomic
    //    `0o600` Receipt v3 JSON while rendering the human card on stdout.
    let receipt_file = project.path().join("out-receipt.json");
    let mut ok_cmd = command(Route::Direct, project.path());
    ok_cmd.args(["verify", "--request"]).arg(&request).arg("--receipt-out").arg(&receipt_file);
    #[cfg(not(feature = "setup"))]
    ok_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let out = ok_cmd.output().unwrap();
    assert_result(&out, 1, "[FAIL]", "");
    assert_result(&out, 1, &format!("Receipt    : {}", receipt_file.display()), "");
    let meta = fs::symlink_metadata(&receipt_file).unwrap();
    assert!(meta.file_type().is_file() && !meta.file_type().is_symlink());
    assert_eq!(meta.permissions().mode() & 0o777, 0o600);
    let saved: serde_json::Value =
        serde_json::from_slice(&fs::read(&receipt_file).unwrap()).unwrap();
    assert_eq!(saved["schema_version"], 3);
    assert_eq!(saved["status"], "unsupported");
    assert_eq!(saved["phase"], "request");

    // 2. Accepts destinations beneath a symlinked ancestor directory (matching
    //    `--artifacts` and symlinked `TMPDIR` / macOS `/var` setups) while
    //    rejecting input aliasing (including through the symlinked ancestor),
    //    symlinked leaf destinations, directory destinations, and `--artifacts`
    //    collisions with exit 2 (`phase == "receipt-out"`), never clobbering
    //    caller files.
    let target_file = project.path().join("target.json");
    fs::write(&target_file, b"untouched\n").unwrap();
    let sym_dest = project.path().join("sym-receipt.json");
    symlink(&target_file, &sym_dest).unwrap();

    let real_dir = project.path().join("real-dir");
    fs::create_dir(&real_dir).unwrap();
    let real_sub = real_dir.join("sub");
    fs::create_dir(&real_sub).unwrap();
    let sym_dir = project.path().join("sym-dir");
    symlink(&real_dir, &sym_dir).unwrap();

    // Symlinked ancestor destination is accepted and writes `0o600` JSON into
    // the canonical target directory.
    let sym_ancestor_dest = sym_dir.join("sub").join("nested.json");
    let mut sym_ok_cmd = command(Route::Direct, project.path());
    sym_ok_cmd
        .args(["verify", "--format", "json", "--request"])
        .arg(&request)
        .arg("--receipt-out")
        .arg(&sym_ancestor_dest);
    #[cfg(not(feature = "setup"))]
    sym_ok_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let sym_ok_out = sym_ok_cmd.output().unwrap();
    assert_eq!(sym_ok_out.status.code(), Some(1), "{sym_ok_out:?}");
    let sym_ok_meta = fs::symlink_metadata(real_sub.join("nested.json")).unwrap();
    assert!(sym_ok_meta.file_type().is_file() && !sym_ok_meta.file_type().is_symlink());
    assert_eq!(sym_ok_meta.permissions().mode() & 0o777, 0o600);
    let sym_ok_saved: serde_json::Value =
        serde_json::from_slice(&fs::read(real_sub.join("nested.json")).unwrap()).unwrap();
    assert_eq!(sym_ok_saved["schema_version"], 3);
    assert_eq!(sym_ok_saved["phase"], "request");

    // A symlinked-ancestor path that aliases `--request` is still rejected.
    let real_req_in_dir = real_dir.join("aliased-req.json");
    fs::write(&real_req_in_dir, precious_bytes).unwrap();
    let mut sym_alias_cmd = command(Route::Direct, project.path());
    sym_alias_cmd
        .args(["verify", "--format", "json", "--request"])
        .arg(&real_req_in_dir)
        .arg("--receipt-out")
        .arg(sym_dir.join("aliased-req.json"));
    #[cfg(not(feature = "setup"))]
    sym_alias_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let sym_alias_out = sym_alias_cmd.output().unwrap();
    assert_eq!(sym_alias_out.status.code(), Some(2), "{sym_alias_out:?}");
    let sym_alias_rec: serde_json::Value = serde_json::from_slice(&sym_alias_out.stdout).unwrap();
    assert_eq!(sym_alias_rec["phase"], "receipt-out", "{sym_alias_rec}");
    assert_eq!(fs::read(&real_req_in_dir).unwrap(), precious_bytes);

    let artifacts_dir = project.path().join("ev");
    for bad_dest in [request.clone(), sym_dest.clone(), real_dir.clone(), artifacts_dir.clone()] {
        let mut bad_cmd = command(Route::Direct, project.path());
        bad_cmd
            .args(["verify", "--format", "json", "--request"])
            .arg(&request)
            .arg("--artifacts")
            .arg(&artifacts_dir)
            .arg("--receipt-out")
            .arg(&bad_dest);
        #[cfg(not(feature = "setup"))]
        bad_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let bad_out = bad_cmd.output().unwrap();
        assert_eq!(bad_out.status.code(), Some(2), "{bad_dest:?}: {bad_out:?}");
        let fail_rec: serde_json::Value = serde_json::from_slice(&bad_out.stdout).unwrap();
        assert_eq!(fail_rec["status"], "tool_failed", "{fail_rec}");
        assert_eq!(fail_rec["phase"], "receipt-out", "{fail_rec}");
    }
    assert_eq!(fs::read(&request).unwrap(), precious_bytes);
    assert_eq!(fs::read(&target_file).unwrap(), b"untouched\n");
    assert!(!artifacts_dir.exists());

    // 3. Request-declared proof/source files and explicit tool paths cannot be
    //    clobbered by `--receipt-out` even when capture fails early.
    let valid_dir = project.path().join("valid-req");
    fs::create_dir_all(valid_dir.join("src")).unwrap();
    fs::create_dir_all(valid_dir.join("proof")).unwrap();
    let src_bytes = b"pub fn bad_ref(x: &u64) -> u64 { *x }\n";
    let spec_bytes = b"prelude\n-- keep spec\n";
    let proof_bytes = b"prelude\n-- keep proof\n";
    fs::write(valid_dir.join("src/lib.rs"), src_bytes).unwrap();
    fs::write(valid_dir.join("proof/Spec.lean"), spec_bytes).unwrap();
    fs::write(valid_dir.join("proof/Proof.lean"), proof_bytes).unwrap();
    let valid_req = valid_dir.join("request.json");
    fs::write(
        &valid_req,
        r#"{
  "schema_version": 1,
  "compilation": {
    "source_root": "src",
    "crate_root": "lib.rs",
    "crate_name": "fixture",
    "edition": "2024",
    "target": "x86_64-unknown-linux-gnu",
    "source_files": ["lib.rs"]
  },
  "scope": { "kind": "crate" },
  "proof": {
    "source_root": "proof",
    "sources": [
      { "module": "Spec", "path": "Spec.lean", "role": "specification" },
      { "module": "Proof", "path": "Proof.lean", "role": "proof" }
    ]
  }
}"#,
    )
    .unwrap();
    let fake_sysroot = project.path().join("fake-sysroot");
    fs::create_dir(&fake_sysroot).unwrap();
    let fake_lean = project.path().join("fake-lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();
    let fake_cap = project.path().join("fake-cap");
    fs::write(
        &fake_cap,
        "#!/bin/sh\nprintf '{\"status\":\"unsupported\",\"diagnostics\":[\"ref\"]}\\n'\nexit 1\n",
    )
    .unwrap();
    fs::set_permissions(&fake_cap, fs::Permissions::from_mode(0o755)).unwrap();

    for alias_dest in [
        valid_dir.join("proof/Proof.lean"),
        valid_dir.join("src/lib.rs"),
        fake_cap.clone(),
        fake_lean.clone(),
    ] {
        let mut alias_cmd = command(Route::Direct, project.path());
        alias_cmd
            .args(["verify", "--format", "json", "--capture"])
            .arg(&fake_cap)
            .arg("--sysroot")
            .arg(&fake_sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .arg("--request")
            .arg(&valid_req)
            .arg("--receipt-out")
            .arg(&alias_dest);
        let alias_out = alias_cmd.output().unwrap();
        assert_eq!(alias_out.status.code(), Some(2), "{alias_dest:?}: {alias_out:?}");
        let alias_rec: serde_json::Value = serde_json::from_slice(&alias_out.stdout).unwrap();
        assert_eq!(alias_rec["status"], "tool_failed", "{alias_rec}");
        assert_eq!(alias_rec["phase"], "receipt-out", "{alias_rec}");
    }

    // Also test manifest mode failing in `cargo` phase with `--receipt-out`
    // targeting both `proof/Spec.lean` and `src/lib.rs` / `Cargo.lock`.
    fs::write(
        valid_dir.join("Cargo.toml"),
        "[package]\nname = \"pm\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[lib]\nproc-macro = true\n",
    )
    .unwrap();
    for manifest_alias in [
        valid_dir.join("proof/Spec.lean"),
        valid_dir.join("src/lib.rs"),
        valid_dir.join("Cargo.lock"),
    ] {
        let manifest_out = command(Route::Direct, project.path())
            .args(["verify", "--format", "json", "--capture"])
            .arg(&fake_cap)
            .arg("--sysroot")
            .arg(&fake_sysroot)
            .arg("--lean")
            .arg(&fake_lean)
            .arg("--manifest-path")
            .arg(valid_dir.join("Cargo.toml"))
            .arg("--proof-dir")
            .arg(valid_dir.join("proof"))
            .arg("--receipt-out")
            .arg(&manifest_alias)
            .output()
            .unwrap();
        assert_eq!(manifest_out.status.code(), Some(2), "{manifest_alias:?}: {manifest_out:?}");
        let manifest_rec: serde_json::Value = serde_json::from_slice(&manifest_out.stdout).unwrap();
        assert_eq!(manifest_rec["status"], "tool_failed", "{manifest_rec}");
        assert_eq!(manifest_rec["phase"], "receipt-out", "{manifest_rec}");
    }

    assert_eq!(fs::read(valid_dir.join("src/lib.rs")).unwrap(), src_bytes);
    assert_eq!(fs::read(valid_dir.join("proof/Spec.lean")).unwrap(), spec_bytes);
    assert_eq!(fs::read(valid_dir.join("proof/Proof.lean")).unwrap(), proof_bytes);
    assert!(fs::read_to_string(&fake_cap).unwrap().contains("unsupported"));
    assert_eq!(fs::read(&fake_lean).unwrap(), b"#!/bin/sh\nexit 0\n");

    // 4. Bare relative `--request request.json` still guards `.rs` and `.lean`
    //    files under the working directory before `load_request` runs.
    let bare_spec = project.path().join("Spec.lean");
    let bare_spec_bytes = b"prelude\n-- keep bare spec\n";
    fs::write(&bare_spec, bare_spec_bytes).unwrap();
    let mut bare_cmd = command(Route::Direct, project.path());
    bare_cmd.args([
        "verify",
        "--format",
        "json",
        "--request",
        "request.json",
        "--receipt-out",
        "Spec.lean",
    ]);
    #[cfg(not(feature = "setup"))]
    bare_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let bare_out = bare_cmd.output().unwrap();
    assert_eq!(bare_out.status.code(), Some(2), "{bare_out:?}");
    let bare_rec: serde_json::Value = serde_json::from_slice(&bare_out.stdout).unwrap();
    assert_eq!(bare_rec["status"], "tool_failed", "{bare_rec}");
    assert_eq!(bare_rec["phase"], "receipt-out", "{bare_rec}");
    assert_eq!(fs::read(&bare_spec).unwrap(), bare_spec_bytes);

    // 5. Unwritable `--receipt-out` parent fails before retaining `--artifacts`
    //    so `--artifacts` is never published on a `tool_failed`/`receipt-out`
    //    exit 2.
    let ro_dir = project.path().join("readonly-receipt-dir");
    fs::create_dir(&ro_dir).unwrap();
    fs::set_permissions(&ro_dir, fs::Permissions::from_mode(0o555)).unwrap();
    let probe_file = ro_dir.join("probe-write");
    match fs::write(&probe_file, b"") {
        Ok(()) => {
            let _ = fs::remove_file(&probe_file);
        }
        Err(_) => {
            let skipped_artifacts = project.path().join("unretained-artifacts");
            let mut ro_cmd = command(Route::Direct, project.path());
            ro_cmd
                .args(["verify", "--format", "json", "--request"])
                .arg(&request)
                .arg("--artifacts")
                .arg(&skipped_artifacts)
                .arg("--receipt-out")
                .arg(ro_dir.join("receipt.json"));
            #[cfg(not(feature = "setup"))]
            ro_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
            let ro_out = ro_cmd.output().unwrap();
            assert_eq!(ro_out.status.code(), Some(2), "{ro_out:?}");
            let ro_rec: serde_json::Value = serde_json::from_slice(&ro_out.stdout).unwrap();
            assert_eq!(ro_rec["status"], "tool_failed", "{ro_rec}");
            assert_eq!(ro_rec["phase"], "receipt-out", "{ro_rec}");
            assert!(ro_rec.get("artifacts").is_none(), "{ro_rec}");
            assert!(!skipped_artifacts.exists());
        }
    }
    let _ = fs::set_permissions(&ro_dir, fs::Permissions::from_mode(0o700));

    // 6. Out-of-tree `--request` input and workspace-root `Cargo.lock` cannot
    //    be overwritten even when `--artifacts` preflight fails before
    //    `load_request`, and a late aliasing failure suppresses `--artifacts`
    //    retention.
    let out_of_tree = project.path().join("oot-src");
    fs::create_dir_all(&out_of_tree).unwrap();
    let oot_data = out_of_tree.join("data.txt");
    fs::write(&oot_data, b"keep out-of-tree input\n").unwrap();
    let oot_lib = out_of_tree.join("lib.rs");
    fs::write(&oot_lib, b"pub fn keep() {}\n").unwrap();
    let oot_req_dir = project.path().join("proofs/unit");
    fs::create_dir_all(&oot_req_dir).unwrap();
    let oot_req = oot_req_dir.join("request.json");
    fs::write(
        &oot_req,
        r#"{
  "schema_version": 1,
  "compilation": {
    "source_root": "../../oot-src",
    "crate_root": "lib.rs",
    "crate_name": "oot",
    "edition": "2024",
    "target": "x86_64-unknown-linux-gnu",
    "source_files": ["lib.rs", "data.txt"]
  },
  "scope": { "kind": "crate" },
  "proof": { "source_root": ".", "sources": [] }
}"#,
    )
    .unwrap();
    let oot_fresh_art = project.path().join("oot-never-created");
    for target in [&oot_data, &oot_lib] {
        let mut oot_cmd = command(Route::Direct, project.path());
        oot_cmd
            .args(["verify", "--format", "json", "--request"])
            .arg(&oot_req)
            .arg("--artifacts")
            .arg(&oot_fresh_art)
            .arg("--receipt-out")
            .arg(target);
        #[cfg(not(feature = "setup"))]
        oot_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let oot_out = oot_cmd.output().unwrap();
        assert_eq!(oot_out.status.code(), Some(2), "{target:?}: {oot_out:?}");
        let oot_rec: serde_json::Value = serde_json::from_slice(&oot_out.stdout).unwrap();
        assert_eq!(oot_rec["phase"], "receipt-out", "{oot_rec}");
        assert!(oot_rec.get("artifacts").is_none(), "{oot_rec}");
    }
    assert_eq!(fs::read(&oot_data).unwrap(), b"keep out-of-tree input\n");
    assert_eq!(fs::read(&oot_lib).unwrap(), b"pub fn keep() {}\n");
    assert!(!oot_fresh_art.exists());

    // 7. Cross-directory symlinked `--request` resolves relative inputs
    //    against the canonical request target's parent (matching
    //    `load_request`), so an early `--artifacts` preflight failure cannot
    //    overwrite a declared non-`.rs`/`.lean` input.
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;

        let link_dir = project.path().join("req-link-dir");
        fs::create_dir(&link_dir).unwrap();
        let linked_req = link_dir.join("request.json");
        symlink(&oot_req, &linked_req).unwrap();
        let existing_art = project.path().join("existing-artifacts-dir");
        fs::create_dir(&existing_art).unwrap();

        let mut sym_req_cmd = command(Route::Direct, project.path());
        sym_req_cmd
            .args(["verify", "--format", "json", "--request"])
            .arg(&linked_req)
            .arg("--artifacts")
            .arg(&existing_art)
            .arg("--receipt-out")
            .arg(&oot_data);
        #[cfg(not(feature = "setup"))]
        sym_req_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let sym_req_out = sym_req_cmd.output().unwrap();
        assert_eq!(sym_req_out.status.code(), Some(2), "{sym_req_out:?}");
        let sym_req_rec: serde_json::Value = serde_json::from_slice(&sym_req_out.stdout).unwrap();
        assert_eq!(sym_req_rec["phase"], "receipt-out", "{sym_req_rec}");
        assert_eq!(fs::read(&oot_data).unwrap(), b"keep out-of-tree input\n");

        // 8. `--artifacts` containing `<symlink>/..` resolves symlinks before
        //    applying `..`, blocking `--receipt-out` inside existing or
        //    aliasing non-existent `--artifacts` destinations pre-stage.
        let dir_a = project.path().join("art-dir-a");
        let dir_b_sub = project.path().join("art-dir-b/sub");
        let dir_b_ev = project.path().join("art-dir-b/ev");
        fs::create_dir_all(&dir_a).unwrap();
        fs::create_dir_all(&dir_b_sub).unwrap();
        fs::create_dir_all(&dir_b_ev).unwrap();
        symlink(&dir_b_sub, dir_a.join("link_b")).unwrap();

        let existing_sentinel = dir_b_ev.join("receipt.json");
        fs::write(&existing_sentinel, b"preserve inside artifacts\n").unwrap();
        let sym_existing_art = dir_a.join("link_b/../ev");
        let mut sym_art_cmd = command(Route::Direct, project.path());
        sym_art_cmd
            .args(["verify", "--format", "json", "--request"])
            .arg(&request)
            .arg("--artifacts")
            .arg(&sym_existing_art)
            .arg("--receipt-out")
            .arg(&existing_sentinel);
        #[cfg(not(feature = "setup"))]
        sym_art_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let sym_art_out = sym_art_cmd.output().unwrap();
        assert_eq!(sym_art_out.status.code(), Some(2), "{sym_art_out:?}");
        let sym_art_rec: serde_json::Value = serde_json::from_slice(&sym_art_out.stdout).unwrap();
        assert_eq!(sym_art_rec["phase"], "receipt-out", "{sym_art_rec}");
        assert_eq!(fs::read(&existing_sentinel).unwrap(), b"preserve inside artifacts\n");

        let new_ev_alias = project.path().join("art-dir-b/new-ev");
        let sym_new_art = dir_a.join("link_b/../new-ev");
        let mut sym_new_cmd = command(Route::Direct, project.path());
        sym_new_cmd
            .args(["verify", "--format", "json", "--request"])
            .arg(&request)
            .arg("--artifacts")
            .arg(&sym_new_art)
            .arg("--receipt-out")
            .arg(&new_ev_alias);
        #[cfg(not(feature = "setup"))]
        sym_new_cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
        let sym_new_out = sym_new_cmd.output().unwrap();
        assert_eq!(sym_new_out.status.code(), Some(2), "{sym_new_out:?}");
        let sym_new_rec: serde_json::Value = serde_json::from_slice(&sym_new_out.stdout).unwrap();
        assert_eq!(sym_new_rec["phase"], "receipt-out", "{sym_new_rec}");
        assert!(!new_ev_alias.exists());
    }
}

#[cfg(unix)]
#[test]
fn receipt_out_invalidates_stale_passing_receipt_before_capture_and_on_write_failure() {
    use std::{fs, os::unix::fs::PermissionsExt as _};

    let project = tempfile::tempdir().unwrap();
    let src_dir = project.path().join("src");
    let proof_dir = project.path().join("proof");
    let out_dir = project.path().join("out");
    fs::create_dir_all(&src_dir).unwrap();
    fs::create_dir_all(&proof_dir).unwrap();
    fs::create_dir_all(&out_dir).unwrap();
    fs::write(src_dir.join("lib.rs"), b"pub fn zero() -> u64 { 0 }\n").unwrap();
    fs::write(proof_dir.join("Spec.lean"), b"prelude\n").unwrap();
    fs::write(proof_dir.join("Proof.lean"), b"prelude\n").unwrap();
    let req_path = project.path().join("request.json");
    fs::write(
        &req_path,
        r#"{
  "schema_version": 1,
  "compilation": {
    "source_root": "src",
    "crate_root": "lib.rs",
    "crate_name": "stale_demo",
    "edition": "2024",
    "target": "x86_64-unknown-linux-gnu",
    "source_files": ["lib.rs"]
  },
  "scope": { "kind": "crate" },
  "proof": {
    "source_root": "proof",
    "sources": [
      { "module": "Spec", "path": "Spec.lean", "role": "specification" },
      { "module": "Proof", "path": "Proof.lean", "role": "proof" }
    ]
  }
}"#,
    )
    .unwrap();
    let fake_sysroot = project.path().join("sysroot");
    fs::create_dir(&fake_sysroot).unwrap();
    let fake_lean = project.path().join("fake-lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    // 1. Pre-existing passing receipt is unlinked BEFORE capture runs; even if
    //    capture subsequently fails and the destination parent becomes
    //    unwritable (simulating ENOSPC/EACCES on failure-receipt write), no
    //    stale `crate_verified` receipt remains on disk.
    let stale_receipt = out_dir.join("receipt.json");
    let stale_pass = br#"{"schema_version":3,"status":"crate_verified"}"#;
    fs::write(&stale_receipt, stale_pass).unwrap();
    let seen_absent_marker = project.path().join("capture-saw-absent");
    let fake_cap = project.path().join("fake-cap");
    fs::write(
        &fake_cap,
        format!(
            "#!/bin/sh\n\
             if [ ! -e '{}' ]; then printf 'absent' > '{}'; fi\n\
             chmod 0555 '{}'\n\
             printf '{{\"status\":\"unsupported\",\"diagnostics\":[\"ref\"]}}\\n'\n\
             exit 1\n",
            stale_receipt.display(),
            seen_absent_marker.display(),
            out_dir.display(),
        ),
    )
    .unwrap();
    fs::set_permissions(&fake_cap, fs::Permissions::from_mode(0o755)).unwrap();

    let out = command(Route::Direct, project.path())
        .args(["verify", "--format", "json", "--capture"])
        .arg(&fake_cap)
        .arg("--sysroot")
        .arg(&fake_sysroot)
        .arg("--lean")
        .arg(&fake_lean)
        .arg("--request")
        .arg(&req_path)
        .arg("--receipt-out")
        .arg(&stale_receipt)
        .output()
        .unwrap();
    let _ = fs::set_permissions(&out_dir, fs::Permissions::from_mode(0o700));
    assert_eq!(
        fs::read_to_string(&seen_absent_marker).unwrap_or_default(),
        "absent",
        "stale receipt must be unlinked before capture begins"
    );
    // Non-root users get exit 2 (`receipt-out`) with `stale_receipt` absent;
    // root ignores `0555` and writes the new `unsupported` failure receipt.
    // Either way, the stale `crate_verified` payload is NEVER preserved.
    assert_ne!(out.status.code(), Some(0), "{out:?}");
    if stale_receipt.exists() {
        let written: serde_json::Value =
            serde_json::from_slice(&fs::read(&stale_receipt).unwrap()).unwrap();
        assert_ne!(written["status"], "crate_verified", "{written}");
        assert_eq!(written["status"], "unsupported", "{written}");
    } else {
        assert_eq!(out.status.code(), Some(2), "{out:?}");
        let rec: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(rec["status"], "tool_failed", "{rec}");
        assert_eq!(rec["phase"], "receipt-out", "{rec}");
    }

    // 2. If `--receipt-out` starts as a stale file inside an already-unwritable
    //    directory, invalidation fails closed BEFORE capture is invoked.
    let ro_dir = project.path().join("ro-stale-dir");
    fs::create_dir(&ro_dir).unwrap();
    let ro_stale = ro_dir.join("receipt.json");
    fs::write(&ro_stale, stale_pass).unwrap();
    fs::set_permissions(&ro_dir, fs::Permissions::from_mode(0o555)).unwrap();
    let probe = ro_dir.join("probe");
    match fs::write(&probe, b"") {
        Ok(()) => {
            let _ = fs::remove_file(&probe);
        }
        Err(_) => {
            let cap_ran_marker = project.path().join("ro-cap-ran");
            let fake_cap2 = project.path().join("fake-cap-2");
            fs::write(
                &fake_cap2,
                format!("#!/bin/sh\nprintf 'ran' > '{}'\nexit 1\n", cap_ran_marker.display()),
            )
            .unwrap();
            fs::set_permissions(&fake_cap2, fs::Permissions::from_mode(0o755)).unwrap();
            let ro_out = command(Route::Direct, project.path())
                .args(["verify", "--format", "json", "--capture"])
                .arg(&fake_cap2)
                .arg("--sysroot")
                .arg(&fake_sysroot)
                .arg("--lean")
                .arg(&fake_lean)
                .arg("--request")
                .arg(&req_path)
                .arg("--receipt-out")
                .arg(&ro_stale)
                .output()
                .unwrap();
            assert_eq!(ro_out.status.code(), Some(2), "{ro_out:?}");
            let ro_rec: serde_json::Value = serde_json::from_slice(&ro_out.stdout).unwrap();
            assert_eq!(ro_rec["status"], "tool_failed", "{ro_rec}");
            assert_eq!(ro_rec["phase"], "receipt-out", "{ro_rec}");
            assert!(!cap_ran_marker.exists(), "capture must not run when stale unlink fails");
        }
    }
    let _ = fs::set_permissions(&ro_dir, fs::Permissions::from_mode(0o700));
}

#[cfg(unix)]
#[test]
fn broken_pipe_exits_cleanly_and_preserves_nonzero_verify_exit_codes() {
    use std::fs;

    let project = tempfile::tempdir().unwrap();
    let binary = Path::new(env!("CARGO_BIN_EXE_cargo-anneal-test-bin"));
    let request = project.path().join("bad-request.json");
    fs::write(&request, b"not JSON\n").unwrap();
    let missing_tmp = project.path().join("missing-tmp");

    // 1. `cargo-anneal skill | true`: closed read end triggers `EPIPE`;
    //    `computed_exit == 0` -> exits `0` with zero panic diagnostics on
    //    stderr.
    let skill_rc = project.path().join("skill.rc");
    let skill_pipe = Command::new("/bin/sh")
        .arg("-c")
        .arg("(\"$1\" skill 2>\"$2\"; printf '%d' \"$?\" > \"$3\") | true")
        .arg("sh")
        .arg(binary)
        .arg(project.path().join("skill.stderr"))
        .arg(&skill_rc)
        .output()
        .unwrap();
    assert!(skill_pipe.status.success(), "{skill_pipe:?}");
    assert_eq!(fs::read_to_string(&skill_rc).unwrap(), "0");
    assert!(fs::read(project.path().join("skill.stderr")).unwrap().is_empty());

    // 2. Failing `verify` (`exit 1` and `exit 2`) with an immediately closed
    //    stdout pipe preserves its exact non-zero exit code (`1` or `2`, never
    //    `0` or `101`) and still writes `--receipt-out` atomically before exit.
    let receipt_one = project.path().join("pipe-exit1.json");
    #[cfg(feature = "setup")]
    let extra = "";
    #[cfg(not(feature = "setup"))]
    let extra = "--capture cap --sysroot sys --lean lean";

    let verify_exit1 = Command::new("/bin/sh")
        .arg("-c")
        .arg(format!(
            "(\"$1\" verify --request \"$2\" --receipt-out \"$3\" {extra}; printf '%d' \"$?\" > \"$4\") | true"
        ))
        .arg("sh")
        .arg(binary)
        .arg(&request)
        .arg(&receipt_one)
        .arg(project.path().join("rc1.txt"))
        .output()
        .unwrap();
    assert!(verify_exit1.status.success());
    assert_eq!(fs::read_to_string(project.path().join("rc1.txt")).unwrap(), "1");
    let rec1: serde_json::Value = serde_json::from_slice(&fs::read(&receipt_one).unwrap()).unwrap();
    assert_eq!(rec1["status"], "unsupported");

    let verify_exit2 = Command::new("/bin/sh")
        .arg("-c")
        .arg(format!(
            "(TMPDIR=\"$3\" \"$1\" verify --request \"$2\" {extra}; printf '%d' \"$?\" > \"$4\") | true"
        ))
        .arg("sh")
        .arg(binary)
        .arg(&request)
        .arg(&missing_tmp)
        .arg(project.path().join("rc2.txt"))
        .output()
        .unwrap();
    assert!(verify_exit2.status.success());
    assert_eq!(fs::read_to_string(project.path().join("rc2.txt")).unwrap(), "2");
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

#[cfg(unix)]
#[test]
fn sharding_cli_guards_reserved_modules_missing_shards_and_shard_plan() {
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

    let project = tempfile::tempdir().unwrap();
    fs::write(project.path().join("lib.rs"), b"pub fn f() -> u64 { 0 }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"").unwrap();
    fs::write(project.path().join("Proof.lean"), b"").unwrap();
    fs::write(project.path().join("Bad.lean"), b"").unwrap();
    let sysroot = project.path().join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.path().join("lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    let fake_capture = project.path().join("fake-capture");
    let script = "#!/bin/sh\n\
        set -eu\n\
        out_dir=''\n\
        while [ \"$#\" -gt 0 ]; do\n\
          if [ \"$1\" = '--out-dir' ]; then shift; out_dir=\"$1\"; fi\n\
          shift\n\
        done\n\
        mkdir -p \"$out_dir\"\n\
        cat > \"$out_dir/capture.json\" <<'JSON'\n\
        {\n\
          \"schema_version\": 5,\n\
          \"compiler\": {\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"},\n\
          \"configuration\": {\n\
            \"crate_root\": \"lib.rs\",\n\
            \"crate_name\": \"demo\",\n\
            \"crate_type\": \"lib\",\n\
            \"panic\": \"unwind\",\n\
            \"overflow_checks\": false,\n\
            \"target\": \"x86_64-unknown-linux-gnu\",\n\
            \"edition\": \"2024\",\n\
            \"cfg\": [],\n\
            \"env\": {}\n\
          },\n\
          \"source_files\": [],\n\
          \"census\": [],\n\
          \"selected\": [],\n\
          \"program\": {\"scope\": {\"kind\": \"crate\"}, \"bodies\": [{}, {}]}\n\
        }\n\
        JSON\n\
        printf '{\"status\":\"captured\"}\\n'\n";
    fs::write(&fake_capture, script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    // 1. `--shard-max-bodies 0` fails argument parsing with exit code 2.
    let zero_max = command(Route::Direct, project.path())
        .args([
            "verify",
            "--shard-max-bodies",
            "0",
            "--request",
            "request.json",
        ])
        .output()
        .unwrap();
    assert_result(&zero_max, 2, "", "value must be at least 1");

    // 2. Authored `Captured.*` and `Expected.*` submodules are reserved.
    for (flag, arg) in [
        ("--proof-file", "Captured.Shard_000=Bad.lean"),
        ("--proof-file", "Expected.Claim=Bad.lean"),
        ("--spec-file", "Captured.Spec=Bad.lean"),
    ] {
        let out = command(Route::Direct, project.path())
            .args([
                "verify",
                "--format",
                "json",
                "--capture",
                fake_capture.to_str().unwrap(),
                "--sysroot",
                sysroot.to_str().unwrap(),
                "--lean",
                fake_lean.to_str().unwrap(),
                "rustc",
                "lib.rs",
                "--crate-name",
                "demo",
                "--spec-file",
                "Spec=Spec.lean",
                "--proof-file",
                "Proof=Proof.lean",
                flag,
                arg,
            ])
            .output()
            .unwrap();
        assert_result(&out, 1, "", "");
        let receipt: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
        assert_eq!(receipt["status"], "unsupported", "{receipt}");
        assert_eq!(receipt["phase"], "proof", "{receipt}");
        assert!(
            receipt["detail"].as_str().unwrap_or("").contains("reserved proof module"),
            "{receipt}"
        );
    }

    // 3. Emitting > `--shard-min-bodies` bodies without shards fails closed.
    let missing_shards = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--shard-min-bodies",
            "1",
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ])
        .output()
        .unwrap();
    assert_result(&missing_shards, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&missing_shards.stdout).unwrap();
    assert_eq!(receipt["status"], "tool_failed", "{receipt}");
    assert_eq!(receipt["phase"], "capture", "{receipt}");
    assert!(
        receipt["detail"].as_str().unwrap_or("").contains("without capture_shards.json"),
        "{receipt}"
    );

    // 4. `shard-plan --write` / `--check` and `--verify-shard-plan` checks.
    let req_path = project.path().join("request.json");
    fs::write(
        &req_path,
        serde_json::to_vec(&serde_json::json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "lib.rs",
                "crate_name": "demo",
                "source_files": ["lib.rs"]
            },
            "scope": { "kind": "crate" },
            "proof": {
                "source_root": ".",
                "sources": [
                    { "module": "Spec", "path": "Spec.lean", "role": "specification" },
                    { "module": "Proof", "path": "Proof.lean", "role": "proof" }
                ]
            }
        }))
        .unwrap(),
    )
    .unwrap();
    let plan_path = project.path().join("anneal-shards.json");
    let write_plan = command(Route::Direct, project.path())
        .args([
            "shard-plan",
            "--request",
            req_path.to_str().unwrap(),
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--shard-min-bodies",
            "10",
            "--write",
            plan_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_result(&write_plan, 0, "\"sharded\": false", "wrote shard plan");

    let check_ok = command(Route::Cargo, project.path())
        .args([
            "shard-plan",
            "--request",
            req_path.to_str().unwrap(),
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--shard-min-bodies",
            "10",
            "--check",
            plan_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_result(&check_ok, 0, "\"total_bodies\": 2", "");

    let check_drift = command(Route::Direct, project.path())
        .args([
            "shard-plan",
            "--request",
            req_path.to_str().unwrap(),
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--shard-min-bodies",
            "5",
            "--check",
            plan_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_result(&check_drift, 1, "", "shard-plan mismatch");

    let verify_drift = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--request",
            req_path.to_str().unwrap(),
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "--shard-min-bodies",
            "5",
            "--verify-shard-plan",
            plan_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_result(&verify_drift, 2, "", "");
    let drift_receipt: serde_json::Value = serde_json::from_slice(&verify_drift.stdout).unwrap();
    assert!(
        drift_receipt["detail"].as_str().unwrap_or("").contains("shard-plan mismatch"),
        "{drift_receipt}"
    );

    // 5. `--receipt-out` aliasing `--verify-shard-plan` fails closed (exit 2)
    //    without modifying the shard plan on disk.
    let plan_before = fs::read(&plan_path).unwrap();
    let alias_out = command(Route::Direct, project.path())
        .args([
            "verify",
            "--format",
            "json",
            "--request",
            req_path.to_str().unwrap(),
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "--verify-shard-plan",
            plan_path.to_str().unwrap(),
            "--receipt-out",
            plan_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert_result(&alias_out, 2, "", "");
    let alias_receipt: serde_json::Value = serde_json::from_slice(&alias_out.stdout).unwrap();
    assert_eq!(alias_receipt["phase"], "receipt-out", "{alias_receipt}");
    assert!(
        alias_receipt["detail"].as_str().unwrap_or("").contains("aliases verification input"),
        "{alias_receipt}"
    );
    assert_eq!(fs::read(&plan_path).unwrap(), plan_before);
}

#[test]
fn allow_unstable_feature_flag_validates_names_and_conflicts() {
    let project = tempfile::tempdir().unwrap();
    std::fs::write(project.path().join("lib.rs"), b"pub fn id(x: u8) -> u8 { x }\n").unwrap();
    for bad in [
        &["verify", "--request", "r.json", "--allow-unstable-feature", "*"][..],
        &["verify", "--request", "r.json", "--allow-unstable-feature", "Doc_cfg"][..],
        &["verify", "--request", "r.json", "--allow-unstable-feature", "doc_cfg,"][..],
        &["verify", "--request", "r.json", "--allow-unstable-feature=doc-cfg"][..],
        &[
            "verify",
            "--allow-unstable-feature",
            "doc_cfg",
            "rustc",
            "lib.rs",
            "--crate-name",
            "core",
            "--stdlib-crate",
            "core",
            "--select",
            "id",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ][..],
    ] {
        let output = command(Route::Direct, project.path()).args(bad).output().unwrap();
        assert_result(&output, 2, "", "error:");
        assert!(output.stdout.is_empty(), "{bad:?}: {output:?}");
    }
}

#[test]
fn allow_unstable_feature_flag_marks_early_failure_receipt_tainted() {
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    std::fs::write(&request, b"not JSON\n").unwrap();
    let mut cmd = command(Route::Direct, project.path());
    cmd.args([
        "verify",
        "--format",
        "json",
        "--allow-unstable-feature",
        "doc_cfg",
        "--allow-sorry-in-proof",
        "--request",
    ])
    .arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "", "--allow-unstable-feature");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(
        receipt["taint_reasons"],
        serde_json::json!(["sorry_in_proof", "unmodeled_unstable_features"]),
        "{receipt}"
    );
    assert_eq!(receipt["status"], "unsupported", "{receipt}");
}

/// Run `verify rustc` against a fake capture that records its arguments and
/// publishes `configuration_extra` merged into a matching configuration.
fn verify_with_fake_capture(
    project: &std::path::Path,
    configuration_extra: &str,
    extra_args: &[&str],
) -> (std::process::Output, String) {
    use std::{fs, os::unix::fs::PermissionsExt};

    fs::write(project.join("lib.rs"), b"pub fn id(x: u8) -> u8 { x }\n").unwrap();
    fs::write(project.join("Spec.lean"), b"-- spec\n").unwrap();
    fs::write(project.join("Proof.lean"), b"-- proof\n").unwrap();
    let sysroot = project.join("sysroot");
    fs::create_dir_all(&sysroot).unwrap();
    let fake_lean = project.join("fake-lean");
    fs::write(&fake_lean, b"#!/bin/sh\nexit 0\n").unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();
    let recorded_args = project.join("capture.args");
    let fake_capture = project.join("fake-capture");
    let script = format!(
        "#!/bin/sh\n\
         set -eu\n\
         printf '%s\\n' \"$@\" > {args_file:?}\n\
         out_dir=''\n\
         while [ \"$#\" -gt 0 ]; do\n\
           if [ \"$1\" = '--out-dir' ]; then\n\
             shift\n\
             out_dir=\"$1\"\n\
           fi\n\
           shift\n\
         done\n\
         mkdir -p \"$out_dir\"\n\
         cat > \"$out_dir/capture.json\" <<'JSON'\n\
         {{\n\
           \"schema_version\": 5,\n\
           \"compiler\": {{\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"}},\n\
           \"configuration\": {{\n\
             \"crate_root\": \"lib.rs\",\n\
             \"crate_name\": \"demo\",\n\
             \"crate_type\": \"lib\",\n\
             \"panic\": \"unwind\",\n\
             \"overflow_checks\": false,\n\
             \"target\": \"x86_64-unknown-linux-gnu\",\n\
             \"edition\": \"2024\",\n\
             \"cfg\": [],\n\
             \"env\": {{}}{configuration_extra}\n\
           }},\n\
           \"source_files\": [],\n\
           \"census\": [],\n\
           \"selected\": [],\n\
           \"program\": {{\"scope\": {{\"kind\": \"selected_unit\", \"roots\": [\"id\"]}}, \"bodies\": []}}\n\
         }}\n\
         JSON\n\
         printf '{{\"status\":\"captured\"}}\\n'\n",
        args_file = recorded_args.display(),
    );
    fs::write(&fake_capture, script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    let mut cmd = command(Route::Direct, project);
    cmd.args([
        "verify",
        "--format",
        "json",
        "--capture",
        fake_capture.to_str().unwrap(),
        "--sysroot",
        sysroot.to_str().unwrap(),
        "--lean",
        fake_lean.to_str().unwrap(),
    ])
    .args(extra_args)
    .args([
        "rustc",
        "lib.rs",
        "--crate-name",
        "demo",
        "--select",
        "id",
        "--spec-file",
        "Spec=Spec.lean",
        "--proof-file",
        "Proof=Proof.lean",
    ]);
    let output = cmd.output().unwrap();
    let args = fs::read_to_string(&recorded_args).unwrap_or_default();
    (output, args)
}

#[test]
fn verify_forwards_allowed_unstable_features_and_authenticates_capture() {
    let flags = [
        "--allow-unstable-feature",
        "doc_cfg,allocator_api",
        "--allow-unstable-feature",
        "doc_cfg",
    ];
    let detail = |output: &std::process::Output| -> serde_json::Value {
        serde_json::from_slice(&output.stdout).unwrap()
    };

    // Capture must record exactly the sorted, deduplicated operator list.
    for (label, extra) in [
        ("omitted allowlist", ""),
        ("narrowed allowlist", r#", "allowed_unstable_features": ["doc_cfg"]"#),
        (
            "observed outside allowlist",
            r#", "allowed_unstable_features": ["allocator_api", "doc_cfg"],
              "observed_unstable_features": ["specialization"]"#,
        ),
    ] {
        let project = tempfile::tempdir().unwrap();
        let (output, args) = verify_with_fake_capture(project.path(), extra, &flags);
        let receipt = detail(&output);
        assert_eq!(receipt["status"], "tool_failed", "{label}: {receipt}");
        assert_eq!(receipt["phase"], "capture", "{label}: {receipt}");
        assert!(receipt["detail"].as_str().unwrap().contains("unstable"), "{label}: {receipt}");
        assert_eq!(
            receipt["taint_reasons"],
            serde_json::json!(["unmodeled_unstable_features"]),
            "{label}: {receipt}"
        );
        let forwarded: Vec<&str> =
            args.lines().filter(|line| line.starts_with("--allow-unstable-feature")).collect();
        assert_eq!(
            forwarded,
            ["--allow-unstable-feature=allocator_api", "--allow-unstable-feature=doc_cfg"],
            "{label}: {args}"
        );
    }

    // A capture that reports features without the flag is refused too.
    let project = tempfile::tempdir().unwrap();
    let (output, args) = verify_with_fake_capture(
        project.path(),
        r#", "allowed_unstable_features": ["doc_cfg"]"#,
        &[],
    );
    let receipt = detail(&output);
    assert_eq!(receipt["phase"], "capture", "{receipt}");
    assert!(receipt["detail"].as_str().unwrap().contains("unstable"), "{receipt}");
    assert!(!args.contains("--allow-unstable-feature"), "{args}");

    // A matching capture passes the feature checks (verification then fails
    // later for unrelated reasons in this fake setup).
    let project = tempfile::tempdir().unwrap();
    let (output, _) = verify_with_fake_capture(
        project.path(),
        r#", "allowed_unstable_features": ["allocator_api", "doc_cfg"],
          "observed_unstable_features": ["doc_cfg"]"#,
        &flags,
    );
    let receipt = detail(&output);
    assert!(
        !receipt["detail"].as_str().unwrap_or("").contains("unstable"),
        "matching capture rejected: {receipt}"
    );
}

#[test]
fn allow_unstable_feature_conflicts_with_stdlib_crate_request() {
    let project = tempfile::tempdir().unwrap();
    let request = project.path().join("request.json");
    std::fs::write(
        &request,
        br#"{
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "lib.rs",
                "crate_name": "core",
                "source_files": ["lib.rs"],
                "stdlib_crate": "core"
            },
            "scope": {"kind": "selected_unit", "roots": ["id"]},
            "proof": {"source_root": ".", "sources": []}
        }"#,
    )
    .unwrap();
    std::fs::write(project.path().join("lib.rs"), b"pub fn id(x: u8) -> u8 { x }\n").unwrap();
    let mut cmd = command(Route::Direct, project.path());
    cmd.args(["verify", "--format", "json", "--allow-unstable-feature", "doc_cfg", "--request"])
        .arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 2, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["status"], "tool_failed", "{receipt}");
    assert_eq!(receipt["phase"], "request", "{receipt}");
    assert!(receipt["detail"].as_str().unwrap().contains("stdlib_crate"), "{receipt}");
}

#[test]
fn max_inspector_output_bytes_validates_bounds_and_propagates_to_verify() {
    let project = tempfile::tempdir().unwrap();
    for route in [Route::Direct, Route::Cargo] {
        for subargs in [&["verify", "--help"][..], &["verify", "rustc", "--help"][..]] {
            let mut cmd = command(route, project.path());
            cmd.args(subargs);
            let output = cmd.output().unwrap();
            assert_eq!(output.status.code(), Some(0), "{route:?} {subargs:?}: {output:?}");
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(stdout.contains("--max-inspector-output-bytes"), "{route:?} {subargs:?}");
        }

        for bad in ["0", "1073741825", "-1", "not-a-number"] {
            let flag = format!("--max-inspector-output-bytes={bad}");
            let mut cmd = command(route, project.path());
            cmd.args(["verify", "--request", "request.json", &flag]);
            let output = cmd.output().unwrap();
            assert_result(&output, 2, "", "");
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("max-inspector-output-bytes"), "{route:?} bad={bad}: {stderr}");
        }
    }

    // End-to-end propagation through `verify`: configure a fake unpinned Lean
    // toolchain whose inspector run writes a 256-byte `result.json`. Under
    // `--max-inspector-output-bytes 64`, Door 1 rejects `result.json` with the
    // size-cap error and `audit` hint; raising `--max-inspector-output-bytes`
    // to `4096` admits the 256-byte file past Door 1 into protocol parsing.
    {
        use std::{fs, os::unix::fs::PermissionsExt};

        let project = tempfile::tempdir().unwrap();
        let root = project.path();
        fs::write(root.join("lib.rs"), b"pub fn id(x: u8) -> u8 { x }\n").unwrap();
        fs::write(root.join("Spec.lean"), b"-- spec\n").unwrap();
        fs::write(root.join("Proof.lean"), b"-- proof\n").unwrap();
        let sysroot = root.join("rust-sysroot");
        fs::create_dir_all(&sysroot).unwrap();

        let lean_prefix = root.join("lean-prefix");
        fs::create_dir_all(lean_prefix.join("bin")).unwrap();
        fs::create_dir_all(lean_prefix.join("lib/lean")).unwrap();
        fs::write(lean_prefix.join("lib/lean/Init.olean"), b"olean\x02init").unwrap();
        let fake_lean = lean_prefix.join("bin/lean");
        let lean_script = format!(
            "#!/bin/sh\n\
             set -eu\n\
             if [ \"${{1:-}}\" = '--version' ]; then\n\
               printf 'Lean (version 4.35.0)\\n'\n\
               exit 0\n\
             fi\n\
             if [ \"${{1:-}}\" = '--print-prefix' ]; then\n\
               printf '%s\\n' {prefix:?}\n\
               exit 0\n\
             fi\n\
             out_olean=''\n\
             run_mode=0\n\
             last=''\n\
             while [ \"$#\" -gt 0 ]; do\n\
               case \"$1\" in\n\
                 -o)\n\
                   shift\n\
                   out_olean=\"$1\"\n\
                   ;;\n\
                 --run)\n\
                   run_mode=1\n\
                   ;;\n\
               esac\n\
               last=\"$1\"\n\
               shift\n\
             done\n\
             if [ -n \"$out_olean\" ]; then\n\
               printf 'olean\\002inspector' > \"$out_olean\"\n\
               exit 0\n\
             fi\n\
             if [ \"$run_mode\" -eq 1 ]; then\n\
               dd if=/dev/zero bs=256 count=1 of=\"$last\" status=none\n\
               exit 0\n\
             fi\n\
             exit 0\n",
            prefix = lean_prefix.display(),
        );
        fs::write(&fake_lean, lean_script).unwrap();
        fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_capture = root.join("fake-capture");
        let cap_script = "#!/bin/sh\n\
            set -eu\n\
            out_dir=''\n\
            while [ \"$#\" -gt 0 ]; do\n\
              if [ \"$1\" = '--out-dir' ]; then\n\
                shift\n\
                out_dir=\"$1\"\n\
              fi\n\
              shift\n\
            done\n\
            mkdir -p \"$out_dir\"\n\
            cat > \"$out_dir/capture.json\" <<'JSON'\n\
            {\n\
              \"schema_version\": 5,\n\
              \"compiler\": {\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"},\n\
              \"configuration\": {\n\
                \"crate_root\": \"lib.rs\",\n\
                \"crate_name\": \"demo\",\n\
                \"crate_type\": \"lib\",\n\
                \"panic\": \"unwind\",\n\
                \"overflow_checks\": false,\n\
                \"target\": \"x86_64-unknown-linux-gnu\",\n\
                \"edition\": \"2024\",\n\
                \"cfg\": [],\n\
                \"env\": {}\n\
              },\n\
              \"source_files\": [],\n\
              \"census\": [],\n\
              \"selected\": [],\n\
              \"program\": {\"scope\": {\"kind\": \"selected_unit\", \"roots\": [\"id\"]}, \"bodies\": []}\n\
            }\n\
            JSON\n\
            printf -- '-- captured\\n' > \"$out_dir/Captured.lean\"\n\
            printf '{\"status\":\"captured\"}\\n'\n";
        fs::write(&fake_capture, cap_script).unwrap();
        fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

        let run_verify_with_cap = |cap_bytes: &str| -> serde_json::Value {
            let mut cmd = command(Route::Direct, root);
            cmd.args([
                "verify",
                "--format",
                "json",
                "--no-cache",
                "--allow-unpinned-lean",
                "--allow-unsandboxed-elaboration",
                "--capture",
                fake_capture.to_str().unwrap(),
                "--sysroot",
                sysroot.to_str().unwrap(),
                "--lean",
                fake_lean.to_str().unwrap(),
                "--max-inspector-output-bytes",
                cap_bytes,
                "rustc",
                "lib.rs",
                "--crate-name",
                "demo",
                "--select",
                "id",
                "--spec-file",
                "Spec=Spec.lean",
                "--proof-file",
                "Proof=Proof.lean",
            ]);
            let output = cmd.output().unwrap();
            assert_eq!(output.status.code(), Some(2), "cap={cap_bytes}: {output:?}");
            serde_json::from_slice(&output.stdout).unwrap()
        };

        let small_receipt = run_verify_with_cap("64");
        assert_eq!(small_receipt["status"], "tool_failed", "{small_receipt}");
        assert_eq!(small_receipt["phase"], "audit", "{small_receipt}");
        let small_detail = small_receipt["detail"].as_str().unwrap();
        assert!(small_detail.contains("exceeds size cap (256 > 64 bytes)"), "{small_receipt}");
        let small_hint = small_receipt["hint"].as_str().unwrap();
        assert!(small_hint.contains("--max-inspector-output-bytes"), "{small_receipt}");

        let raised_receipt = run_verify_with_cap("4096");
        assert_eq!(raised_receipt["status"], "tool_failed", "{raised_receipt}");
        assert_eq!(raised_receipt["phase"], "audit", "{raised_receipt}");
        let raised_detail = raised_receipt["detail"].as_str().unwrap();
        assert!(!raised_detail.contains("exceeds size cap"), "{raised_receipt}");
        assert!(
            raised_detail.contains("unexpected inspector protocol response"),
            "{raised_receipt}"
        );
        assert!(raised_receipt["hint"].is_null(), "{raised_receipt}");
    }
}

#[cfg(unix)]
#[test]
fn verify_emits_structured_reason_on_authored_proof_heartbeat_limit() {
    use std::{fs, os::unix::fs::PermissionsExt};

    let project = tempfile::tempdir().unwrap();
    let root = project.path();
    fs::write(root.join("lib.rs"), b"pub fn id(x: u8) -> u8 { x }\n").unwrap();
    fs::write(root.join("Spec.lean"), b"-- spec\n").unwrap();
    fs::write(root.join("Proof.lean"), b"-- proof\n").unwrap();
    let sysroot = root.join("rust-sysroot");
    fs::create_dir_all(&sysroot).unwrap();

    let lean_prefix = root.join("lean-prefix");
    fs::create_dir_all(lean_prefix.join("bin")).unwrap();
    fs::create_dir_all(lean_prefix.join("lib/lean/Init")).unwrap();
    fs::write(lean_prefix.join("lib/lean/Init.olean"), b"olean\x02init").unwrap();
    for m in ["Coe", "Core", "Notation", "Prelude", "SizeOf", "Tactics"] {
        fs::write(lean_prefix.join(format!("lib/lean/Init/{m}.olean")), b"olean\x02fnd").unwrap();
    }
    let fake_lean = lean_prefix.join("bin/lean");
    let lean_script = format!(
        "#!/bin/sh\n\
         set -eu\n\
         if [ \"${{1:-}}\" = '--version' ]; then\n\
           printf 'Lean (version 4.35.0)\\n'\n\
           exit 0\n\
         fi\n\
         if [ \"${{1:-}}\" = '--print-prefix' ]; then\n\
           printf '%s\\n' {prefix:?}\n\
           exit 0\n\
         fi\n\
         out_olean=''\n\
         run_mode=0\n\
         prev=''\n\
         last=''\n\
         while [ \"$#\" -gt 0 ]; do\n\
           case \"$1\" in\n\
             -o)\n\
               shift\n\
               out_olean=\"$1\"\n\
               ;;\n\
             --run)\n\
               run_mode=1\n\
               ;;\n\
           esac\n\
           prev=\"$last\"\n\
           last=\"$1\"\n\
           shift\n\
         done\n\
         if [ \"$run_mode\" -eq 1 ]; then\n\
           /usr/bin/python3 -c 'import json, sys; req = json.load(open(sys.argv[1])); m = req[\"mode\"]; fnd = [\"Init.Coe\", \"Init.Core\", \"Init.Notation\", \"Init.Prelude\", \"Init.SizeOf\", \"Init.Tactics\"]; res = {{\"headers\": [{{\"module\": n, \"imports\": [], \"isModule\": False}} for n, _ in req[\"sources\"]]}} if m == \"headers\" else ({{\"checked\": [n for n, _ in req[\"sources\"]]}} if m == \"spec-preflight\" else ({{\"graph\": {{k: ([{{\"module\": d, \"importAll\": False, \"isExported\": True, \"isMeta\": False}} for d in fnd if d != k] if k == \"Init.Core\" else []) for k in fnd}}}} if m == \"resolve-imports\" else {{}})); json.dump({{\"ok\": True, \"result\": res}}, open(sys.argv[2], \"w\"))' \"$prev\" \"$last\"\n\
           exit 0\n\
         fi\n\
         case \"$out_olean\" in\n\
           */Proof.olean|Proof.olean)\n\
             printf '{{\"severity\":\"error\",\"kind\":\"runtime.maxHeartbeats\",\"data\":\"(deterministic) timeout\"}}\\n'\n\
             exit 1\n\
             ;;\n\
         esac\n\
         if [ -n \"$out_olean\" ]; then\n\
           printf 'olean\\002stub' > \"$out_olean\"\n\
           exit 0\n\
         fi\n\
         exit 0\n",
        prefix = lean_prefix.display(),
    );
    fs::write(&fake_lean, lean_script).unwrap();
    fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

    let fake_capture = root.join("fake-capture");
    let cap_script = "#!/bin/sh\n\
        set -eu\n\
        out_dir=''\n\
        while [ \"$#\" -gt 0 ]; do\n\
          if [ \"$1\" = '--out-dir' ]; then\n\
            shift\n\
            out_dir=\"$1\"\n\
          fi\n\
          shift\n\
        done\n\
        mkdir -p \"$out_dir\"\n\
        cat > \"$out_dir/capture.json\" <<'JSON'\n\
        {\n\
          \"schema_version\": 5,\n\
          \"compiler\": {\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"},\n\
          \"configuration\": {\n\
            \"crate_root\": \"lib.rs\",\n\
            \"crate_name\": \"demo\",\n\
            \"crate_type\": \"lib\",\n\
            \"panic\": \"unwind\",\n\
            \"overflow_checks\": false,\n\
            \"target\": \"x86_64-unknown-linux-gnu\",\n\
            \"edition\": \"2024\",\n\
            \"cfg\": [],\n\
            \"env\": {}\n\
          },\n\
          \"source_files\": [],\n\
          \"census\": [],\n\
          \"selected\": [],\n\
          \"program\": {\"scope\": {\"kind\": \"selected_unit\", \"roots\": [\"id\"]}, \"bodies\": []}\n\
        }\n\
        JSON\n\
        printf -- '-- captured\\n' > \"$out_dir/Captured.lean\"\n\
        printf '{\"status\":\"captured\"}\\n'\n";
    fs::write(&fake_capture, cap_script).unwrap();
    fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

    let receipt_out = root.join("emitted-receipt.json");
    let output = command(Route::Direct, root)
        .args([
            "verify",
            "--format",
            "json",
            "--no-cache",
            "--allow-unpinned-lean",
            "--allow-unsandboxed-elaboration",
            "--receipt-out",
            receipt_out.to_str().unwrap(),
            "--capture",
            fake_capture.to_str().unwrap(),
            "--sysroot",
            sysroot.to_str().unwrap(),
            "--lean",
            fake_lean.to_str().unwrap(),
            "rustc",
            "lib.rs",
            "--crate-name",
            "demo",
            "--select",
            "id",
            "--spec-file",
            "Spec=Spec.lean",
            "--proof-file",
            "Proof=Proof.lean",
        ])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");

    let stdout_receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    let file_receipt: serde_json::Value =
        serde_json::from_slice(&fs::read(&receipt_out).unwrap()).unwrap();
    for (label, receipt) in [("stdout", &stdout_receipt), ("receipt-out", &file_receipt)] {
        assert_eq!(receipt["status"], "proof_failed", "{label}: {receipt}");
        assert_eq!(receipt["phase"], "audit", "{label}: {receipt}");
        assert_eq!(receipt["reason"], "heartbeat_limit_exceeded", "{label}: {receipt}");
    }
}
