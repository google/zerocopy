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
    let mut command = match route {
        Route::Direct => Command::new(binary),
        Route::Cargo => {
            let mut command = Command::new(env!("CARGO"));
            command.arg("anneal");
            let cargo_home = workdir.join("cargo-home");
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

#[cfg(all(target_os = "linux", feature = "setup"))]
fn local_archive(path: &Path) {
    archive_entries(path, &[("marker.txt", b"current-run CLI archive", 0o644)]);
}

#[cfg(all(target_os = "linux", feature = "setup"))]
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

#[cfg(all(target_os = "linux", feature = "setup"))]
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
        assert!(installed.starts_with(cache.path()), "{}", installed.display());
        let [expected_cache_base, _home_base] = cargo_anneal::default_lean_search_bases_from_env(
            Some(cache.path().as_os_str()),
            std::env::var_os("HOME").as_deref(),
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
        archive_entries(
            &updated_archive,
            &[("marker.txt", b"replaced CLI archive", 0o644)],
        );
        let reinstall = command(route, project.path())
            .env("XDG_CACHE_HOME", cache.path())
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

#[cfg(all(target_os = "linux", feature = "setup"))]
#[test]
fn setup_help_and_verify_fail_closed_on_symlinked_cache_bundle() {
    use std::{fs, os::unix::fs::symlink};

    let project = tempfile::tempdir().expect("create fixture");
    let help = command(Route::Direct, project.path())
        .args(["setup", "--help"])
        .output()
        .unwrap();
    assert_result(&help, 0, "replaces any existing cached installation", "");
    assert_result(&help, 0, "--clear-old", "");

    let cache = tempfile::tempdir().expect("create cache");
    let archive = project.path().join("v1.tar.zst");
    local_archive(&archive);
    let setup_out = command(Route::Direct, project.path())
        .env("XDG_CACHE_HOME", cache.path())
        .args(["setup", "--local-archive"])
        .arg(&archive)
        .output()
        .unwrap();
    assert_result(&setup_out, 0, "Installed Anneal toolchain at ", "");
    let stdout = String::from_utf8_lossy(&setup_out.stdout);
    let installed = std::path::PathBuf::from(
        stdout
            .trim_end()
            .strip_prefix("Installed Anneal toolchain at ")
            .unwrap(),
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
        .args([
            "verify",
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
    assert!(
        receipt["detail"].as_str().unwrap_or("").contains("symlink"),
        "{receipt}"
    );
}

#[cfg(all(target_os = "linux", feature = "setup"))]
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
            cmd.arg("verify").arg("--request").arg(&request).arg("--artifacts").arg(destination);
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
            .arg("verify")
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
        cmd.arg("verify").arg("--request").arg(&request).arg("--artifacts").arg(&ordinary);
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
            child.arg("verify").arg("--request").arg(&request);
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

#[cfg(all(target_os = "linux", feature = "setup"))]
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
        child.current_dir(project.path()).arg("verify").arg("--request").arg(&request);
        child.env(
            "XDG_CACHE_HOME",
            if expected == "sibling" { project.path().join("empty-cache") } else { cache.clone() },
        );
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
    fs::write(
        package.join("Cargo.toml"),
        "[package]\nname = \"source_namespace\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(package.join("src/lib.rs"), b"pub fn zero() -> u64 { include!(\"zero.inc\") }\n")
        .unwrap();
    fs::write(package.join("src/unused.rs"), b"unused declared input\n").unwrap();
    fs::write(package.join("src/zero.inc"), b"0u64\n").unwrap();
    fs::write(package.join(".hidden/ignored.rs"), b"not a shortcut input\n").unwrap();
    fs::write(package.join("target/ignored.rs"), b"not a shortcut input\n").unwrap();
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
        .arg("verify")
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
    assert!(!evidence.join("rust/src/zero.inc").exists());
    assert!(!evidence.join("rust/.hidden").exists());
    assert!(!evidence.join("rust/target").exists());
    assert!(!evidence.join("rust/proof").exists());
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
            &["verify", "--panic", "abort", "--capture", "cap", "--sysroot", "sys", "--lean", "lean"]
                [..],
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
    cmd.env("TMPDIR", &missing_tmp).args(["verify", "--request"]).arg(&request).args([
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
    assert_eq!(
        receipt["taint_reasons"],
        serde_json::json!(["unpinned_lean"]),
        "{receipt}"
    );
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
        .args(["verify", "--request"])
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
        .arg("verify")
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
        .arg("verify")
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
        .args(["verify", "rustc"])
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
            .args(["verify", "rustc"])
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
    cmd.args(["verify", "--allow-unsandboxed-elaboration", "--request"])
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
    assert!(
        stderr.contains("--allow-unsandboxed-elaboration"),
        "{stderr}"
    );
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
    cmd.args(["verify", "--request"]).arg(&request);
    #[cfg(not(feature = "setup"))]
    cmd.args(["--capture", "cap", "--sysroot", "sys", "--lean", "lean"]);
    let output = cmd.output().unwrap();
    assert_result(&output, 1, "", "");
    let receipt: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(receipt["status"], "unsupported", "{receipt}");
    assert_eq!(receipt["phase"], "request", "{receipt}");
    assert!(
        receipt["detail"].as_str().unwrap_or("").contains("must not contain '='"),
        "{receipt}"
    );
}

#[cfg(unix)]
#[test]
fn verify_passes_env_flags_and_rejects_mismatched_capture_env() {
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

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
    // Emit a syntactically valid schema-4 capture manifest whose
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
           \"schema_version\": 4,\n\
           \"compiler\": {{\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"}},\n\
           \"configuration\": {{\n\
             \"crate_name\": \"demo\",\n\
             \"crate_type\": \"lib\",\n\
             \"panic\": \"unwind\",\n\
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
    // `crate_type` or `panic` strategy disagrees with the request.
    for (bad_crate_type, bad_panic, req_crate_type, req_panic) in
        [("lib", "unwind", "bin", "unwind"), ("bin", "unwind", "bin", "abort")]
    {
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
               \"schema_version\": 4,\n\
               \"compiler\": {{\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"}},\n\
               \"configuration\": {{\n\
                 \"crate_name\": \"demo\",\n\
                 \"crate_type\": \"{bad_crate_type}\",\n\
                 \"panic\": \"{bad_panic}\",\n\
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
        let mismatch_out = command(Route::Direct, project.path())
            .args([
                "verify",
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
            ])
            .output()
            .unwrap();
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

#[test]
fn verify_passes_instantiate_flags_and_rejects_mismatched_capture_scope() {
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

    let project = tempfile::tempdir().unwrap();
    fs::write(project.path().join("lib.rs"), b"pub fn id<T>(x: T) -> T { x }\n").unwrap();
    fs::write(project.path().join("Spec.lean"), b"-- spec\n").unwrap();
    fs::write(project.path().join("Proof.lean"), b"-- proof\n").unwrap();

    // Malformed `--instantiate` JSON and `--request` + `--instantiate` conflict
    // must fail CLI validation with exit 2 and empty stdout.
    for bad in [
        &[
            "verify",
            "--request",
            "r.json",
            "--instantiate",
            r#"{"path":"id","args":["usize"]}"#,
        ][..],
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
           \"schema_version\": 4,\n\
           \"compiler\": {{\"commit\": \"f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1\"}},\n\
           \"configuration\": {{\n\
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
