// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Orchestration of Charon extraction.
//!
//! This module handles the invocation of the `charon` tool to extract
//! Low-Level Borrow Calculus (LLBC) from Rust crates. It manages:
//! - Setting up the Charon command and arguments (including features,
//!   targets, and output paths).
//! - Handling `unsafe(axiom)` functions by marking them as opaque to Charon.
//! - Streaming and filtering compiler output to provide user-friendly
//!   feedback via `indicatif` and `miette`.
//! - Validating the extraction result.

use anyhow::Context as _;
use rayon::prelude::IntoParallelRefIterator as _;
use rayon::prelude::ParallelIterator as _;

/// Runs Charon on the specified packages to generate LLBC artifacts.
///
/// This function requires [`crate::resolve::LockedRoots`] to ensure that it has exclusive access
/// to the `llbc` output directory. It iterates over each [`crate::scanner::AnnealArtifact`],
/// constructs the appropriate `charon` command, and executes it.
///
/// It handles:
/// - **Opaque Functions**: identifying `unsafe(axiom)` functions and passing
///   `--opaque` to Charon.
/// - **Entry Points**: passing the computed `start_from` roots to Charon to
///   minimize extraction scope.
/// - **Output Handling**: capturing stdout/stderr, parsing JSON compiler
///   messages, and rendering them using [`crate::diagnostics::DiagnosticMapper`].
pub fn run_charon(
    args: &crate::resolve::Args,
    toolchain: &crate::setup::Toolchain,
    roots: &crate::resolve::LockedRoots,
    packages: &[crate::scanner::AnnealArtifact],
    show_progress: bool,
) -> anyhow::Result<()> {
    let llbc_root = roots.llbc_root();
    std::fs::create_dir_all(&llbc_root).context("Failed to create LLBC output directory")?;

    // Prepend to `PATH` to ensure that when `charon` delegates to tools such as
    // `cargo` and `rustc` it invokes the correct rust toolchain.
    let new_path = crate::util::prepend_to_env_var("PATH", &toolchain.rust_bin());

    let lib_env_var =
        if cfg!(target_os = "macos") { "DYLD_LIBRARY_PATH" } else { "LD_LIBRARY_PATH" };
    // Set `LD_LIBRARY_PATH` (or `DYLD_LIBRARY_PATH` on macOS) to point to the
    // managed Rust toolchain's `lib` directory so that dynamic executables (like
    // `charon-driver` which links against `rustc` dynamic libraries) can find them.
    let new_lib_path = crate::util::prepend_to_env_var(lib_env_var, &toolchain.rust_lib());

    // Global print mutex to prevent interleaved printing of consolidated artifact buffers.
    let print_mutex = std::sync::Arc::new(std::sync::Mutex::new(()));

    // Initialize MultiProgress if progress is enabled.
    let mp = if show_progress {
        Some(std::sync::Arc::new(indicatif::MultiProgress::new()))
    } else {
        None
    };

    packages.par_iter().try_for_each(|artifact| {
        let pb = mp.as_ref().map(|m| {
            let pb = m.add(indicatif::ProgressBar::new_spinner());
            pb.set_style(
                indicatif::ProgressStyle::default_spinner()
                    .template("{spinner:.green} {msg}")
                    .unwrap(),
            );
            pb.set_message("Compiling...");
            pb
        });

        log::info!("Invoking Charon on package '{}'...", artifact.name.package_name);

        let mut cmd = toolchain.command(crate::setup::Tool::Charon);

        // Set `CHARON_TOOLCHAIN_IS_IN_PATH=1` to instruct Charon to bypass its
        // standard toolchain resolution logic (which expects the compiler to be
        // managed via `rustup`). Instead, it will directly use the `rustc` and
        // `cargo` binaries we prepended to the `PATH` environment variable.
        cmd.env("CHARON_TOOLCHAIN_IS_IN_PATH", "1");
        cmd.env("PATH", &new_path);
        cmd.env(lib_env_var, &new_lib_path);

        cmd.arg("cargo");
        cmd.arg("--preset=aeneas");

        let llbc_path = artifact.llbc_path(roots);
        cmd.arg("--dest-file").arg(llbc_path);

        // Fail fast on errors: if Charon (or `rustc`) encounters a compilation error or
        // translation failure (e.g., an unsupported Rust feature), it will terminate
        // the process immediately rather than attempting to proceed and translate other parts of the crate.
        cmd.arg("--abort-on-error");

        // Separator for the underlying cargo command.
        cmd.arg("--");

        // Ensure cargo emits json msgs which charon-driver natively generates.
        cmd.arg("--message-format=json");

        cmd.arg("--manifest-path").arg(&artifact.manifest_path);

        use crate::resolve::AnnealTargetKind::*;
        match artifact.target_kind {
            Lib | RLib | ProcMacro | CDyLib | DyLib | StaticLib => cmd.arg("--lib"),
            Bin => cmd.args(["--bin", &artifact.name.target_name]),
            Example => cmd.args(["--example", &artifact.name.target_name]),
            Test => cmd.args(["--test", &artifact.name.target_name]),
        };

        // Forward all feature-related flags.
        if args.features.all_features {
            cmd.arg("--all-features");
        }
        if args.features.no_default_features {
            cmd.arg("--no-default-features");
        }
        for feature in &args.features.features {
            cmd.arg("--features").arg(feature);
        }

        // Reuse the main target directory for dependencies to save time: share
        // `CARGO_TARGET_DIR` (`target/anneal/cargo_target`) across all Charon
        // invocations to enable Cargo's incremental build cache.
        cmd.env("CARGO_TARGET_DIR", roots.cargo_target_dir());

        log::debug!("Executing charon command: {:?}", cmd);

        let start = std::time::Instant::now();
        let output_error = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let output_error_clone = std::sync::Arc::clone(&output_error);

        // Charon's standard error stream contains unstructured diagnostic
        // output (such as panic messages from build scripts or ICEs). We
        // collect this in a safety buffer to ensure that even if Charon aborts
        // unexpectedly, the user receives the complete unstructured output
        // instead of a generic "silent death".
        let safety_buffer = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let safety_buffer_clone = std::sync::Arc::clone(&safety_buffer);

        // Local buffer to collect all output (diagnostics) for this artifact.
        let artifact_diagnostics = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let artifact_diagnostics_clone = std::sync::Arc::clone(&artifact_diagnostics);

        let mut mapper = crate::diagnostics::DiagnosticMapper::new(roots.workspace().clone());

        let pb_clone = pb.clone();
        let res = crate::util::run_command_with_progress(cmd, pb_clone, move |line, pb| {
            if let Ok(msg) = serde_json::from_str::<cargo_metadata::Message>(line) {
                match msg {
                    cargo_metadata::Message::CompilerArtifact(a) => {
                        if let Some(p) = pb {
                            p.set_message(format!("Compiling {}", a.target.name));
                        }
                    }
                    cargo_metadata::Message::CompilerMessage(msg) => {
                        let mut rendered = String::new();
                        mapper.render_miette(&msg.message, |s| rendered.push_str(&s));
                        if !rendered.is_empty() {
                            artifact_diagnostics_clone.lock().unwrap().push(rendered);
                        }
                        if matches!(
                            msg.message.level,
                            cargo_metadata::diagnostic::DiagnosticLevel::Error
                                | cargo_metadata::diagnostic::DiagnosticLevel::Ice
                        ) {
                            output_error_clone.store(true, std::sync::atomic::Ordering::Relaxed);
                        }
                    }
                    cargo_metadata::Message::TextLine(t) => {
                        safety_buffer_clone.lock().unwrap().push(t);
                    }
                    _ => {}
                }
            } else {
                safety_buffer_clone.lock().unwrap().push(line.to_string());
            }
            Ok(())
        })?;

        log::trace!("Charon for '{}' took {:.2?}", artifact.name.package_name, start.elapsed());

        // Lock the print mutex to print this artifact's consolidated output atomically.
        let _lock = print_mutex.lock().unwrap();

        // Print all collected diagnostics for this artifact.
        let diags = artifact_diagnostics.lock().unwrap();
        if !diags.is_empty() {
            eprintln!("=== Diagnostics for '{}' ===", artifact.name.package_name);
            for diag in diags.iter() {
                eprintln!("{}", diag);
            }
        }

        if output_error.load(std::sync::atomic::Ordering::Relaxed) {
            anyhow::bail!("Diagnostic error in charon");
        } else if !res.status.success() {
            // Print safety buffer on failure (also atomically since we hold print_mutex).
            eprintln!("=== Failure output for '{}' ===", artifact.name.package_name);
            for line in safety_buffer.lock().unwrap().iter() {
                eprintln!("{}", line);
            }
            // Also dump the dynamic linker errors or panic messages captured in stderr.
            for line in &res.stderr_lines {
                eprintln!("{}", line);
            }
            anyhow::bail!("Charon failed with status: {}", res.status);
        }

        Ok(())
    })?;

    Ok(())
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "exocrate_tests")]
    use super::*;
    #[cfg(feature = "exocrate_tests")]
    use crate::resolve::{Args, resolve_roots};
    #[cfg(feature = "exocrate_tests")]
    use crate::scanner::scan_workspace;
    #[cfg(feature = "exocrate_tests")]
    use clap::Parser as _;
    #[cfg(feature = "exocrate_tests")]
    use std::fs;

    // Shared helper to parse LLBC output and verify local status and compiled body variant.
    #[cfg(feature = "exocrate_tests")]
    fn assert_fn_body(
        path: &std::path::Path,
        components: &[&str],
        expected_local: bool,
        expected_structured: bool,
    ) {
        let file = std::fs::File::open(path).unwrap();
        let crate_data: charon_lib::export::CrateData = serde_json::from_reader(file).unwrap();

        let fun = crate_data
            .translated
            .fun_decls
            .iter()
            .find(|fun| {
                let name = &fun.item_meta.name;
                if name.name.len() != components.len() {
                    return false;
                }
                for (i, elem) in name.name.iter().enumerate() {
                    match elem {
                        charon_lib::ast::PathElem::Ident(ident, _) => {
                            if ident != components[i] {
                                return false;
                            }
                        }
                        _ => return false,
                    }
                }
                true
            })
            .unwrap_or_else(|| {
                panic!("Function with name path {:?} was not found/declared in LLBC!", components)
            });

        assert_eq!(
            fun.item_meta.is_local, expected_local,
            "Local/External status mismatch for function {:?}",
            components
        );

        if expected_structured {
            assert!(
                matches!(fun.body, charon_lib::ullbc_ast::Body::Structured(_)),
                "Function {:?} was expected to contain a compiled structured implementation body!",
                components
            );
        } else {
            assert!(
                matches!(fun.body, charon_lib::ullbc_ast::Body::Opaque),
                "Function {:?} was expected to be Opaque (referred to but implementation body NOT included)!",
                components
            );
        }
    }

    #[cfg(feature = "exocrate_tests")]
    fn resolve_test_toolchain() -> &'static crate::setup::Toolchain {
        static TOOLCHAIN: std::sync::OnceLock<crate::setup::Toolchain> = std::sync::OnceLock::new();
        TOOLCHAIN.get_or_init(|| {
            crate::setup::run_setup(crate::setup::SetupArgs {
                local_archive: Some("target/anneal-exocrate.tar.zst".into()),
            })
            .expect("Failed to run setup");
            crate::setup::Toolchain::resolve().expect("Failed to resolve toolchain")
        })
    }

    #[cfg(feature = "exocrate_tests")]
    #[test]
    fn test_run_charon_simple() {
        // 1. Create a temporary directory.
        let temp_dir = tempfile::tempdir().unwrap();
        let proj_dir = temp_dir.path().join("test_proj");
        fs::create_dir_all(&proj_dir).unwrap();

        // 2. Create a simple Cargo.toml.
        let cargo_toml = r#"
            [package]
            name = "test_proj"
            version = "0.1.0"
            edition = "2021"

            [lib]
            path = "src/lib.rs"
        "#;
        fs::write(proj_dir.join("Cargo.toml"), cargo_toml).unwrap();

        // 3. Create a simple src/lib.rs.
        fs::create_dir_all(proj_dir.join("src")).unwrap();
        let lib_rs = r#"
            pub fn add(left: usize, right: usize) -> usize {
                left + right
            }
        "#;
        fs::write(proj_dir.join("src").join("lib.rs"), lib_rs).unwrap();

        // 4. Construct Args pointing to this temp project.
        let args = Args::try_parse_from(&[
            "cargo-anneal",
            "--manifest-path",
            proj_dir.join("Cargo.toml").to_str().unwrap(),
        ])
        .unwrap();

        // 5. Resolve roots.
        let roots = resolve_roots(&args).unwrap();

        // 6. Scan workspace.
        let packages = scan_workspace(&roots).unwrap();
        assert_eq!(packages.len(), 1);

        // 7. Lock run root.
        let locked_roots = roots.lock_run_root().unwrap();

        // 8. Resolve standard developer toolchain and run charon.
        let toolchain = resolve_test_toolchain();

        let res = run_charon(
            &args,
            &toolchain,
            &locked_roots,
            &packages,
            false, // show_progress
        );
        assert!(res.is_ok(), "charon failed: {:?}", res.err());

        // 9. Verify .llbc file exists.
        let llbc_path = packages[0].llbc_path(&locked_roots);
        assert!(llbc_path.exists(), "llbc file not found at {:?}", llbc_path);
    }

    #[cfg(feature = "exocrate_tests")]
    #[test]
    fn test_run_charon_multiple_modules() {
        let _ = env_logger::builder().is_test(true).try_init();

        // 1. Create a temporary workspace with multiple modules.
        let temp_dir = tempfile::tempdir().unwrap();
        crate::workspace_fixture!(&temp_dir, {
            "Cargo.toml" => r#"
                [package]
                name = "test_proj"
                version = "0.1.0"
                edition = "2021"

                [lib]
                path = "src/lib.rs"
            "#,
            "src/lib.rs" => r#"
                pub mod foo;
                pub mod bar;
            "#,
            "src/foo.rs" => r#"
                pub fn foo_fn() {}
            "#,
            "src/bar.rs" => r#"
                pub fn bar_fn() {}
            "#,
        });

        // 2. Construct Args pointing to this temp project.
        let args = Args::try_parse_from(&[
            "cargo-anneal",
            "--manifest-path",
            temp_dir.path().join("Cargo.toml").to_str().unwrap(),
        ])
        .unwrap();

        // 3. Resolve roots and scan workspace.
        let roots = resolve_roots(&args).unwrap();
        let packages = scan_workspace(&roots).unwrap();
        assert_eq!(packages.len(), 1);

        // 4. Lock run root.
        let locked_roots = roots.lock_run_root().unwrap();

        // 5. Resolve toolchain and run charon.
        let toolchain = resolve_test_toolchain();
        let res = run_charon(
            &args,
            &toolchain,
            &locked_roots,
            &packages,
            false, // show_progress
        );
        assert!(res.is_ok(), "charon failed: {:?}", res.err());

        // 6. Verify .llbc file exists and contains BOTH functions.
        let llbc_path = packages[0].llbc_path(&locked_roots);
        assert!(llbc_path.exists(), "llbc file not found at {:?}", llbc_path);

        log::debug!("llbc path: {:?}", llbc_path);

        let llbc_content = std::fs::read_to_string(&llbc_path).expect("failed to read llbc file");

        log::debug!("llbc content:\n'''\n{}\n'''", llbc_content);

        // Assert that the serialized AST contains the names of both functions
        // defined in separate, independent modules.
        assert!(llbc_content.contains("foo_fn"), "Function 'foo_fn' was not translated!");
        assert!(llbc_content.contains("bar_fn"), "Function 'bar_fn' was not translated!");
    }

    #[cfg(feature = "exocrate_tests")]
    #[test]
    fn test_charon_crates_io_dependency() {
        let _ = env_logger::builder().is_test(true).try_init();

        let temp_dir = tempfile::tempdir().unwrap();
        crate::workspace_fixture!(&temp_dir, {
            "Cargo.toml" => r#"
                [package]
                name = "test_proj"
                version = "0.1.0"
                edition = "2021"

                [dependencies]
                fs2 = "0.4.3"

                [lib]
                path = "src/lib.rs"
            "#,
            "src/lib.rs" => r#"
                pub fn get_free_space(path: &std::path::Path) -> u64 {
                    fs2::free_space(path).unwrap_or(0)
                }
            "#,
        });

        let args = Args::try_parse_from(&[
            "cargo-anneal",
            "--manifest-path",
            temp_dir.path().join("Cargo.toml").to_str().unwrap(),
        ])
        .unwrap();

        let roots = resolve_roots(&args).unwrap();
        let packages = scan_workspace(&roots).unwrap();
        let locked_roots = roots.lock_run_root().unwrap();

        let toolchain = resolve_test_toolchain();
        let res = run_charon(&args, &toolchain, &locked_roots, &packages, false);
        assert!(res.is_ok(), "charon failed: {:?}", res.err());

        let llbc_path = packages[0].llbc_path(&locked_roots);
        assert!(llbc_path.exists());

        // 1. Assert that the local function 'get_free_space' is fully translated with a structured body definition.
        assert_fn_body(&llbc_path, &["test_proj", "get_free_space"], true, true);

        // 2. Assert that the crates.io dependency 'fs2::free_space' is referred to but NOT translated (opaque).
        assert_fn_body(&llbc_path, &["fs2", "free_space"], false, false);

        // Standard library calls may be lowered directly into the calling crate rather than
        // emitted as standalone LLBC declarations.
    }

    #[cfg(feature = "exocrate_tests")]
    #[test]
    fn test_charon_path_dependency_behavior() {
        let _ = env_logger::builder().is_test(true).try_init();

        let temp_dir = tempfile::tempdir().unwrap();
        crate::workspace_fixture!(&temp_dir, {
            "Cargo.toml" => r#"
                [workspace]
                resolver = "2"
                members = [
                    "test_proj",
                ]
            "#,
            "my_dep/Cargo.toml" => r#"
                [package]
                name = "my_dep"
                version = "0.1.0"
                edition = "2021"

                [lib]
                path = "src/lib.rs"
            "#,
            "my_dep/src/lib.rs" => r#"
                pub fn dep_fn() {}
            "#,
            "test_proj/Cargo.toml" => r#"
                [package]
                name = "test_proj"
                version = "0.1.0"
                edition = "2021"

                [dependencies]
                my_dep = { path = "../my_dep" }

                [lib]
                path = "src/lib.rs"
            "#,
            "test_proj/src/lib.rs" => r#"
                pub fn call_dep() {
                    my_dep::dep_fn();
                }
            "#,
        });

        let args = Args::try_parse_from(&[
            "cargo-anneal",
            "--manifest-path",
            temp_dir.path().join("test_proj").join("Cargo.toml").to_str().unwrap(),
        ])
        .unwrap();

        let roots = resolve_roots(&args).unwrap();
        let packages = scan_workspace(&roots).unwrap();
        assert_eq!(packages.len(), 1);
        let locked_roots = roots.lock_run_root().unwrap();

        let toolchain = resolve_test_toolchain();
        let res = run_charon(&args, &toolchain, &locked_roots, &packages, false);
        assert!(res.is_ok(), "charon failed: {:?}", res.err());

        let llbc_path = packages[0].llbc_path(&locked_roots);
        assert!(llbc_path.exists());

        // 1. Assert that local target function 'call_dep' is fully translated (definition included).
        assert_fn_body(&llbc_path, &["test_proj", "call_dep"], true, true);

        // 2. Assert that local path dependency 'my_dep::dep_fn' is referred to but NOT translated (opaque).
        assert_fn_body(&llbc_path, &["my_dep", "dep_fn"], false, false);
    }

    #[cfg(feature = "exocrate_tests")]
    #[test]
    fn test_run_charon_multiple_packages() {
        let _ = env_logger::builder().is_test(true).try_init();

        // 1. Create a temporary workspace containing multiple packages.
        let temp_dir = tempfile::tempdir().unwrap();
        crate::workspace_fixture!(&temp_dir, {
            "Cargo.toml" => r#"
                [workspace]
                resolver = "2"
                members = [
                    "package_a",
                    "package_b",
                ]
            "#,
            "package_a/Cargo.toml" => r#"
                [package]
                name = "package_a"
                version = "0.1.0"
                edition = "2021"

                [lib]
                path = "src/lib.rs"
            "#,
            "package_a/src/lib.rs" => r#"
                pub fn func_a() {}
            "#,
            "package_b/Cargo.toml" => r#"
                [package]
                name = "package_b"
                version = "0.1.0"
                edition = "2021"

                [lib]
                path = "src/lib.rs"
            "#,
            "package_b/src/lib.rs" => r#"
                pub fn func_b() {}
            "#,
        });

        // 2. Construct Args pointing to this temp project.
        let args = Args::try_parse_from(&[
            "cargo-anneal",
            "--manifest-path",
            temp_dir.path().join("Cargo.toml").to_str().unwrap(),
        ])
        .unwrap();

        // 3. Resolve roots and scan workspace.
        let roots = resolve_roots(&args).unwrap();
        let packages = scan_workspace(&roots).unwrap();
        assert_eq!(packages.len(), 2, "Expected exactly two packages resolved in workspace");

        // 4. Lock run root.
        let locked_roots = roots.lock_run_root().unwrap();

        // 5. Resolve toolchain and run charon on both packages.
        let toolchain = resolve_test_toolchain();
        let res = run_charon(
            &args,
            &toolchain,
            &locked_roots,
            &packages,
            false, // show_progress
        );
        assert!(res.is_ok(), "charon failed: {:?}", res.err());

        // 6. Verify .llbc file exists and contains correct code for Package A.
        let llbc_path_a = packages[0].llbc_path(&locked_roots);
        assert!(llbc_path_a.exists(), "llbc file for Package A not found at {:?}", llbc_path_a);
        let llbc_content_a =
            std::fs::read_to_string(&llbc_path_a).expect("failed to read llbc file A");
        assert!(
            llbc_content_a.contains("func_a"),
            "Function 'func_a' was not translated in Package A!"
        );
        assert!(
            !llbc_content_a.contains("func_b"),
            "Function 'func_b' was incorrectly translated in Package A!"
        );

        // 7. Verify .llbc file exists and contains correct code for Package B.
        let llbc_path_b = packages[1].llbc_path(&locked_roots);
        assert!(llbc_path_b.exists(), "llbc file for Package B not found at {:?}", llbc_path_b);
        let llbc_content_b =
            std::fs::read_to_string(&llbc_path_b).expect("failed to read llbc file B");
        assert!(
            llbc_content_b.contains("func_b"),
            "Function 'func_b' was not translated in Package B!"
        );
        assert!(
            !llbc_content_b.contains("func_a"),
            "Function 'func_a' was incorrectly translated in Package B!"
        );
    }
}
