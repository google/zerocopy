// Copyright 2025 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[cfg(not(feature = "ui-tests"))]
mod trampoline {
    use std::{env, process::Command};

    use testutil::ToolchainVersion;

    pub fn run() {
        // 1. Identify Toolchain
        let toolchain_version = ToolchainVersion::extract_from_pwd().unwrap();
        let test_dir_name = toolchain_version.get_ui_source_files_dirname_and_maybe_print_warning();
        let toolchain = env::var("RUSTUP_TOOLCHAIN").unwrap_or_else(|_| "stable".to_string());
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let workspace_root = std::path::Path::new(manifest_dir).parent().unwrap();
        let test_dir = std::path::Path::new(manifest_dir).join("tests").join(test_dir_name);

        // 2. Guard Recursion
        if env::var("ZEROCOPY_UI_TEST_INTERNAL").is_ok() {
            panic!("ZEROCOPY_UI_TEST_INTERNAL is set, preventing infinite recursion");
        }

        // 3. Build Dependencies
        // We need to build zerocopy so we can link against it in the tests.
        // We use the current toolchain (which might be MSRV).
        let mut build_cmd = Command::new("cargo");
        build_cmd
            .arg("build")
            .arg("-p")
            .arg("zerocopy")
            .arg("--features")
            .arg("derive")
            .arg("--message-format=json");

        if let Ok(rustflags) = env::var("RUSTFLAGS") {
            build_cmd.env("RUSTFLAGS", rustflags);
        }

        let target = get_target_triple();
        if let Some(ref target) = target {
            build_cmd.arg("--target").arg(target);
        }

        let output = build_cmd.output().expect("failed to run cargo build");
        if !output.status.success() {
            eprintln!("failed to build zerocopy dependencies");
            panic!("failed to build zerocopy dependencies");
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        let mut rlib_path = None;
        let mut derive_lib_path = None;

        for line in stdout.lines() {
            if line.contains(r#""compiler-artifact""#) {
                if line.contains(r#""name":"zerocopy""#)
                    && !line.contains(r#""name":"zerocopy-derive""#)
                {
                    if let Some(path) = extract_path(line, ".rlib") {
                        rlib_path = Some(path);
                    }
                } else if line.contains(r#""name":"zerocopy-derive""#)
                    || line.contains(r#""name":"zerocopy_derive""#)
                {
                    if let Some(path) = extract_path(line, ".so")
                        .or_else(|| extract_path(line, ".dylib"))
                        .or_else(|| extract_path(line, ".dll"))
                    {
                        derive_lib_path = Some(path);
                    }
                }
            }
        }

        let rlib_path = rlib_path.expect("failed to find zerocopy rlib");
        let derive_lib_path = derive_lib_path.expect("failed to find zerocopy-derive lib");

        // 4. Spawn Inner Layer
        // We use `cargo +stable run` to run the harness via the separate runner crate.
        let mut cmd = Command::new("cargo");
        cmd.arg("+stable")
            .arg("run")
            .arg("--manifest-path")
            .arg("../tools/ui-runner/Cargo.toml")
            .arg("--");

        // Forward extra arguments (like --bless)
        for arg in env::args().skip(1) {
            cmd.arg(arg);
        }

        // Env vars to pass info to the harness
        let deps_dir = rlib_path.parent().unwrap().join("deps");
        let host_deps_dir = derive_lib_path.parent().unwrap().to_path_buf();
        cmd.env("ZEROCOPY_UI_TEST_INTERNAL", "1");
        cmd.env("ZEROCOPY_UI_TEST_TOOLCHAIN", toolchain);
        cmd.env("ZEROCOPY_UI_TEST_DIR", test_dir);
        cmd.env("ZEROCOPY_WORKSPACE_ROOT", workspace_root);
        cmd.env("ZEROCOPY_RLIB_PATH", rlib_path);
        cmd.env("ZEROCOPY_DERIVE_LIB_PATH", derive_lib_path);
        cmd.env("ZEROCOPY_DEPS_DIR", deps_dir);
        cmd.env("ZEROCOPY_HOST_DEPS_DIR", host_deps_dir);
        if let Ok(rustflags) = env::var("RUSTFLAGS") {
            cmd.env("ZEROCOPY_RUNNER_RUSTFLAGS", rustflags);
            cmd.env_remove("RUSTFLAGS");
        }
        if let Some(ref target) = target {
            cmd.env("ZEROCOPY_UI_TARGET", target);
        }

        let status = cmd.status().expect("failed to run cargo");
        if !status.success() {
            panic!("ui-test failed with status: {}", status);
        }
    }

    fn extract_path(line: &str, extension: &str) -> Option<std::path::PathBuf> {
        // Simple parser for JSON output to find paths ending with extension
        // This is hacky but avoids depending on serde_json in the trampoline
        let mut current_pos = 0;
        while let Some(start) = line[current_pos..].find('"') {
            let start_pos = current_pos + start + 1;
            if let Some(end) = line[start_pos..].find('"') {
                let end_pos = start_pos + end;
                let path = &line[start_pos..end_pos];
                if path.ends_with(extension) && !path.ends_with(".rmeta") {
                    return Some(std::path::PathBuf::from(path));
                }
                current_pos = end_pos + 1;
            } else {
                break;
            }
        }
        None
    }

    fn get_target_triple() -> Option<String> {
        if let Ok(target) = env::var("ZEROCOPY_TARGET") {
            return Some(target);
        }

        // Try to get it from rustc.
        let output = Command::new("rustc").arg("-vV").output().ok()?;
        if !output.status.success() {
            return None;
        }
        let stdout = String::from_utf8_lossy(&output.stdout);
        for line in stdout.lines() {
            if let Some(host) = line.strip_prefix("host: ") {
                return Some(host.to_string());
            }
        }
        None
    }
}

#[cfg(feature = "ui-tests")]
mod harness {
    use std::env;

    use ui_test::{status_emitter, Config, OutputConflictHandling};

    pub fn run() {
        let test_dir = env::var("ZEROCOPY_UI_TEST_DIR").expect("ZEROCOPY_UI_TEST_DIR not set");
        let toolchain =
            env::var("ZEROCOPY_UI_TEST_TOOLCHAIN").expect("ZEROCOPY_UI_TEST_TOOLCHAIN not set");
        let workspace_root =
            env::var("ZEROCOPY_WORKSPACE_ROOT").expect("ZEROCOPY_WORKSPACE_ROOT not set");

        let mut config = Config::rustc(test_dir.clone());

        // Configure toolchain for the test cases
        config.program.envs.push(("RUSTUP_TOOLCHAIN".into(), Some(toolchain.into())));

        if let Ok(target) = env::var("ZEROCOPY_UI_TARGET") {
            config.target = Some(target);
        }

        let rustflags = env::var("ZEROCOPY_RUNNER_RUSTFLAGS").or_else(|_| env::var("RUSTFLAGS"));
        if let Ok(rustflags) = rustflags {
            for flag in rustflags.split_whitespace() {
                config.program.args.push(flag.into());
            }
        }

        use ui_test::spanned::{Span, Spanned};
        let default_rev_config = config.comment_defaults.revisioned.entry(vec![]).or_default();
        default_rev_config.require_annotations = Spanned::new(false, Span::default()).into();

        // Dependencies: manual configuration
        let rlib_path = env::var("ZEROCOPY_RLIB_PATH").expect("ZEROCOPY_RLIB_PATH not set");
        let derive_lib_path =
            env::var("ZEROCOPY_DERIVE_LIB_PATH").expect("ZEROCOPY_DERIVE_LIB_PATH not set");
        let deps_dir = env::var("ZEROCOPY_DEPS_DIR").expect("ZEROCOPY_DEPS_DIR not set");
        let host_deps_dir =
            env::var("ZEROCOPY_HOST_DEPS_DIR").expect("ZEROCOPY_HOST_DEPS_DIR not set");

        config.program.args.push("-L".into());
        config.program.args.push(format!("dependency={}", deps_dir).into());
        config.program.args.push("-L".into());
        config.program.args.push(format!("dependency={}", host_deps_dir).into());
        config.program.args.push("--extern".into());
        config.program.args.push(format!("zerocopy={}", rlib_path).into());
        config.program.args.push("--extern".into());
        config.program.args.push(format!("zerocopy_derive={}", derive_lib_path).into());

        // Normalization
        //
        // FIXME(#187): Bizarrely, this seems to just *strip* the workspace
        // root, but does not replace it with the string `$WORKSPACE`. Not a
        // huge deal, but we should fix it eventually.
        config.stderr_filter(&workspace_root, "$WORKSPACE");
        config.stderr_filter(&std::env::var("HOME").unwrap(), "$HOME");

        // Blessing
        if env::args().any(|arg| arg == "--bless") || env::var("BLESS").is_ok() {
            config.output_conflict_handling = OutputConflictHandling::Bless;
        }

        // Execution
        ui_test::run_tests_generic(
            vec![config],
            |path, _config| {
                let path_str = path.to_string_lossy();
                let args: Vec<_> = env::args().skip(1).filter(|arg| arg != "--bless").collect();

                // Filter by file extension
                if path.extension().map(|ext| ext == "rs").unwrap_or(false) {
                    // If arguments are provided, filter by those arguments
                    if args.is_empty() || args.iter().any(|arg| path_str.contains(arg)) {
                        return Some(true);
                    }
                }
                Some(false)
            },
            |_, _| {},
            status_emitter::Text::verbose(),
        )
        .unwrap();
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--skip" && i + 1 < args.len() && args[i + 1] == "ui" {
            return;
        }
        i += 1;
    }

    #[cfg(not(feature = "ui-tests"))]
    trampoline::run();

    #[cfg(feature = "ui-tests")]
    harness::run();
}
