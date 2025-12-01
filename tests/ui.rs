// Copyright 2025 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#[cfg(feature = "derive")]
#[cfg(not(feature = "ui-tests"))]
#[cfg(not(miri))]
mod trampoline {
    use std::env;
    use std::path::{Path, PathBuf};
    use std::process::{Command, ExitStatus};
    use testutil::ToolchainVersion;

    pub fn main() {
        // 1. Identify Toolchain
        let toolchain_version = ToolchainVersion::extract_from_pwd().unwrap();
        let test_dir = toolchain_version.get_ui_source_files_dirname_and_maybe_print_warning();
        let toolchain = env::var("RUSTUP_TOOLCHAIN").unwrap_or_else(|_| "stable".to_string());

        // 2. Guard Recursion
        if env::var("ZEROKOPY_UI_TEST_INTERNAL").is_ok() {
            panic!("ZEROKOPY_UI_TEST_INTERNAL is set, preventing infinite recursion");
        }

        // 3. Spawn Inner Layer
        let manifest_dir = env!("CARGO_MANIFEST_DIR");
        let cargo_sh = Path::new(manifest_dir).join("cargo.sh");

        let cmd_path = if cargo_sh.exists() {
            cargo_sh.to_str().unwrap().to_string()
        } else {
            "cargo".to_string()
        };

        let mut cmd = Command::new(cmd_path);

        if cargo_sh.exists() {
            cmd.arg("+stable");
        } else {
            cmd.arg("+stable");
        }

        cmd.arg("run")
            .arg("--manifest-path")
            .arg("tools/ui-runner/Cargo.toml");

        cmd.arg("--");

        // Forward extra arguments (skip binary path)
        for arg in env::args().skip(1) {
            cmd.arg(arg);
        }

        // Env vars
        cmd.env("ZEROKOPY_UI_TEST_INTERNAL", "1");
        cmd.env("ZEROKOPY_UI_TEST_TOOLCHAIN", toolchain);
        cmd.env("ZEROKOPY_UI_TEST_DIR", test_dir);

        // Build zerocopy to ensure artifacts exist
        let output = Command::new("cargo")
            .arg("build")
            .arg("--features")
            .arg("derive")
            .arg("--message-format=json")
            .output()
            .expect("failed to run cargo build");

        if !output.status.success() {
            panic!("failed to build zerocopy dependencies");
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        let mut rlib_path = None;
        let mut derive_lib_path = None;

        for line in stdout.lines() {
            if line.contains(r#""compiler-artifact""#) {
                if line.contains(r#""name":"zerocopy""#) {
                    let parts: Vec<&str> = line.split('"').collect();
                    for part in parts {
                        if part.ends_with(".rlib") {
                            rlib_path = Some(PathBuf::from(part));
                            break;
                        }
                    }
                } else if line.contains(r#""name":"zerocopy-derive""#)
                    || line.contains(r#""name":"zerocopy_derive""#)
                {
                    let parts: Vec<&str> = line.split('"').collect();
                    for part in parts {
                        if (part.ends_with(".so")
                            || part.ends_with(".dylib")
                            || part.ends_with(".dll"))
                            && !part.ends_with(".rmeta")
                        {
                            derive_lib_path = Some(PathBuf::from(part));
                            break;
                        }
                    }
                }
            }
        }

        let rlib_path = rlib_path.expect("failed to find zerocopy rlib");
        let derive_lib_path = derive_lib_path.expect("failed to find zerocopy-derive lib");
        let deps_dir = rlib_path.parent().unwrap().join("deps");

        let rustflags = env::var("RUSTFLAGS").unwrap_or_default();
        cmd.env("ZEROKOPY_UI_TEST_RUSTFLAGS", rustflags);
        cmd.env_remove("RUSTFLAGS");
        cmd.env("ZEROKOPY_RLIB_PATH", rlib_path);
        cmd.env("ZEROKOPY_DERIVE_LIB_PATH", derive_lib_path);
        cmd.env("ZEROKOPY_DEPS_DIR", deps_dir);

        let status = cmd.status().expect("failed to run cargo");

        if !status.success() {
            std::process::exit(status.code().unwrap_or(1));
        }
    }
}

#[cfg(feature = "derive")]
#[cfg(feature = "ui-tests")]
mod harness {
    use std::env;
    use std::path::PathBuf;
    use ui_test::{status_emitter, Config, OutputConflictHandling};

    pub fn main() {
        // 3. Select Test Directory (Logic moved from Step 3 to init to use in Config)
        let test_dir_name =
            env::var("ZEROKOPY_UI_TEST_DIR").expect("ZEROKOPY_UI_TEST_DIR not set");
        let test_dir = PathBuf::from("tests").join(test_dir_name);
        println!("Running tests in: {:?}", test_dir);

        // 1. Setup Config
        let mut config = Config::rustc(test_dir);

        // 2. Target Toolchain
        let toolchain =
            env::var("ZEROKOPY_UI_TEST_TOOLCHAIN").expect("ZEROKOPY_UI_TEST_TOOLCHAIN not set");
        let rustflags = env::var("ZEROKOPY_UI_TEST_RUSTFLAGS").unwrap_or_default();

        config
            .program
            .envs
            .push(("RUSTUP_TOOLCHAIN".into(), Some(toolchain.clone().into())));

        for flag in rustflags.split_whitespace() {
            config.program.args.push(flag.into());
        }

        // 4. Handle Dependencies
        let rlib_path =
            PathBuf::from(env::var("ZEROKOPY_RLIB_PATH").expect("ZEROKOPY_RLIB_PATH not set"));
        let derive_lib_path = PathBuf::from(
            env::var("ZEROKOPY_DERIVE_LIB_PATH").expect("ZEROKOPY_DERIVE_LIB_PATH not set"),
        );
        let deps_dir =
            PathBuf::from(env::var("ZEROKOPY_DEPS_DIR").expect("ZEROKOPY_DEPS_DIR not set"));

        config.program.args.push("-L".into());
        config
            .program
            .args
            .push(format!("dependency={}", deps_dir.display()).into());
        config.program.args.push("--extern".into());
        config
            .program
            .args
            .push(format!("zerocopy={}", rlib_path.display()).into());
        config.program.args.push("--extern".into());
        config
            .program
            .args
            .push(format!("zerocopy_derive={}", derive_lib_path.display()).into());

        // 5. Normalization
        config.stderr_filter("(?ms)^[ \\t]*Compiling .+$", "");
        config.stderr_filter("(?ms)^[ \\t]*Finished .+$", "");
        config.stderr_filter("(?ms)^[ \\t]*error: internal compiler error: .+$", "");

        // 6. Blessing
        if env::args().any(|arg| arg == "--bless") {
            config.output_conflict_handling = OutputConflictHandling::Bless;
        }

        // 7. Execution
        ui_test::run_tests_generic(
            vec![config],
            |path, _config| Some(path.extension().map(|ext| ext == "rs").unwrap_or(false)),
            |_, _| {},
            status_emitter::Text::verbose(),
        )
        .unwrap();
    }
}

fn main() {
    #[cfg(all(feature = "derive", not(feature = "ui-tests")))]
    trampoline::main();

    #[cfg(all(feature = "derive", feature = "ui-tests"))]
    harness::main();
}
