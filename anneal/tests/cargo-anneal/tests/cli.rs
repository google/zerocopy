// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Command behavior through direct invocation and Cargo's subcommand dispatch.
//!
//! The tests live in domain submodules under `tests/cli/`, which share this
//! file's helpers and imports through `use super::*`. They stay in this one
//! `cli` test target, which CI builds and lints both with and without the
//! `setup` feature.

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

#[path = "cli/artifacts_and_overwrite.rs"]
mod artifacts_and_overwrite;
#[path = "cli/capture_request_binding.rs"]
mod capture_request_binding;
#[path = "cli/cargo_shortcut.rs"]
mod cargo_shortcut;
#[path = "cli/help_and_bundled_resources.rs"]
mod help_and_bundled_resources;
#[path = "cli/init_and_receipt_output.rs"]
mod init_and_receipt_output;
#[path = "cli/policy_taint_and_unstable_features.rs"]
mod policy_taint_and_unstable_features;
#[path = "cli/receipt_out.rs"]
mod receipt_out;
#[path = "cli/rustc_mode_and_env.rs"]
mod rustc_mode_and_env;
#[cfg(feature = "setup")]
#[path = "cli/setup_and_tool_discovery.rs"]
mod setup_and_tool_discovery;
#[path = "cli/sharding_and_limits.rs"]
mod sharding_and_limits;
