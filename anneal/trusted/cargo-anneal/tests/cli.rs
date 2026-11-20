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
    let file = std::fs::File::create(path).expect("create archive");
    let encoder = zstd::Encoder::new(file, 1).expect("create compressor");
    let mut archive = tar::Builder::new(encoder);
    let contents = b"current-run CLI archive";
    let mut header = tar::Header::new_gnu();
    header.set_size(contents.len() as u64);
    header.set_mode(0o644);
    header.set_cksum();
    archive
        .append_data(&mut header, "marker.txt", contents.as_slice())
        .expect("write archive marker");
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
