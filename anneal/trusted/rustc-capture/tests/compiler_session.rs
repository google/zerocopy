// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exercise compiler work through the private driver boundary.

use std::path::PathBuf;
use std::process::{Command, Output};

const CALLBACK: &str =
    "anneal-rustc-capture: compiler analysis callback reached; verification not performed";

struct Session {
    directory: tempfile::TempDir,
}

impl Session {
    fn new(source: &str) -> Self {
        let directory = tempfile::tempdir().expect("create compiler fixture");
        std::fs::write(directory.path().join("input.rs"), source).expect("write compiler fixture");
        Self { directory }
    }

    fn command_for(&self, executable: impl AsRef<std::ffi::OsStr>) -> Command {
        let mut command = Command::new(executable);
        command.current_dir(self.directory.path()).args([
            "input.rs",
            "--crate-name=session",
            "--edition=2024",
            "--crate-type=lib",
            "--emit=metadata",
            "--color=never",
            "-o",
            "session.rmeta",
        ]);
        command
    }

    fn command(&self) -> Command {
        let sysroot = std::env::var_os("ANNEAL_TEST_RUST_SYSROOT")
            .expect("set ANNEAL_TEST_RUST_SYSROOT to the pinned Rust distribution");
        let mut command = self.command_for(env!("CARGO_BIN_EXE_anneal-rustc-capture"));
        command.arg("--sysroot").arg(sysroot);
        command
    }

    fn compile(&self) -> Output {
        self.command().output().expect("run capture driver")
    }
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn assert_failed(output: &Output, diagnostic: &str) {
    assert!(!output.status.success(), "unexpected success: {output:?}");
    assert!(stderr(output).contains(diagnostic), "{output:?}");
    assert!(!stdout(output).contains(CALLBACK), "{output:?}");
    assert!(!stderr(output).contains(CALLBACK), "{output:?}");
}

fn assert_callback(output: &Output) {
    assert!(output.status.success(), "{output:?}");
    assert_eq!(stderr(output).trim(), format!("note: {CALLBACK}"));
}

fn json_diagnostics(output: &Output) -> Vec<serde_json::Value> {
    let diagnostics: Vec<serde_json::Value> = stderr(output)
        .lines()
        .map(|line| serde_json::from_str(line).expect("JSON diagnostic line"))
        .collect();
    assert!(!diagnostics.is_empty(), "{output:?}");
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic["$message_type"] == "diagnostic"),
        "{diagnostics:?}"
    );
    diagnostics
}

#[test]
fn compiler_arguments_reach_analysis_outside_the_checkout() {
    let session = Session::new(
        "#[cfg(not(anneal_driver_test))] compile_error!(\"missing compiler cfg\");\n\
         pub async fn edition_probe() -> u8 { 42 }\n",
    );
    let output = session
        .command()
        .args(["--cfg", "anneal_driver_test"])
        .output()
        .expect("run configured capture driver");
    assert!(output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert_callback(&output);
    assert!(
        std::fs::metadata(session.directory.path().join("session.rmeta"))
            .expect("compiler metadata output")
            .len()
            > 0
    );
}

#[test]
fn parse_errors_preserve_diagnostics_and_fail() {
    let output = Session::new("pub fn broken( {\n").compile();
    assert_failed(&output, "unclosed delimiter");
}

#[test]
fn type_errors_preserve_diagnostics_and_fail() {
    let output = Session::new("pub fn mismatch() -> u8 { \"wrong type\" }\n").compile();
    assert_failed(&output, "E0308");
}

#[test]
fn borrow_errors_preserve_diagnostics_and_fail() {
    let output = Session::new(
        "pub fn conflicting() -> usize {\n\
         let mut value = 0_usize;\n\
         let first = &mut value;\n\
         let second = &mut value;\n\
         *first + *second\n\
         }\n",
    )
    .compile();
    assert_failed(&output, "E0499");
}

#[test]
fn warnings_allow_callback_evidence_until_promoted_to_errors() {
    for json in [false, true] {
        for deny_warnings in [false, true] {
            let session = Session::new("pub fn warning() { let unused_variable = 0; }\n");
            let mut command = session.command();
            if json {
                command.arg("--error-format=json");
            }
            if deny_warnings {
                command.arg("-Dwarnings");
            }
            let output = command.output().expect("run compiler lint session");
            assert!(output.stdout.is_empty(), "{output:?}");
            if deny_warnings {
                assert_failed(&output, "unused variable");
                assert_eq!(output.status.code(), Some(1), "{output:?}");
            } else {
                assert!(output.status.success(), "{output:?}");
            }
            let level = if deny_warnings { "error" } else { "warning" };
            if json {
                let diagnostics = json_diagnostics(&output);
                assert!(
                    diagnostics.iter().any(|diagnostic| {
                        diagnostic["level"] == level
                            && diagnostic["code"]["code"] == "unused_variables"
                    }),
                    "{diagnostics:?}"
                );
                if !deny_warnings {
                    assert_eq!(
                        diagnostics
                            .iter()
                            .filter(|diagnostic| {
                                diagnostic["level"] == "note" && diagnostic["message"] == CALLBACK
                            })
                            .count(),
                        1,
                        "{diagnostics:?}"
                    );
                }
            } else {
                assert!(
                    stderr(&output).contains(&format!("{level}: unused variable")),
                    "{output:?}"
                );
                if !deny_warnings {
                    assert_eq!(stderr(&output).matches(CALLBACK).count(), 1, "{output:?}");
                }
            }
        }
    }
}

#[test]
fn invalid_compiler_options_use_early_diagnostics_without_callback_evidence() {
    for (argument, diagnostic) in [
        ("--unknown-anneal-test-flag", "Unrecognized option"),
        ("--crate-name", "Argument to option 'crate-name' missing"),
    ] {
        for json in [false, true] {
            let session = Session::new("pub fn valid() {}\n");
            let mut command = session.command();
            if json {
                command.arg("--error-format=json");
            }
            let output = command
                .arg(argument)
                .output()
                .expect("run compiler with invalid option");
            assert_failed(&output, diagnostic);
            assert_eq!(output.status.code(), Some(1), "{output:?}");
            assert!(output.stdout.is_empty(), "{output:?}");
            assert!(stderr(&output).starts_with("error: "), "{output:?}");
        }
    }
}

#[test]
fn missing_response_files_use_early_diagnostics_without_callback_evidence() {
    for json in [false, true] {
        let session = Session::new("pub fn valid() {}\n");
        let mut command = session.command();
        if json {
            command.arg("--error-format=json");
        }
        let output = command
            .arg("@missing-response")
            .output()
            .expect("run compiler with missing response file");
        assert_failed(&output, "failed to load argument file");
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(stderr(&output).starts_with("error: "), "{output:?}");
        assert!(stderr(&output).contains("missing-response"), "{output:?}");
    }
}

#[test]
fn missing_source_files_preserve_diagnostics_without_callback_evidence() {
    for json in [false, true] {
        let session = Session::new("pub fn valid() {}\n");
        std::fs::remove_file(session.directory.path().join("input.rs"))
            .expect("remove compiler fixture source");
        let mut command = session.command();
        if json {
            command.arg("--error-format=json");
        }
        let output = command.output().expect("run compiler with missing source");
        assert_failed(&output, "couldn't read");
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(stderr(&output).contains("input.rs"), "{output:?}");
        if json {
            json_diagnostics(&output);
        }
    }
}

#[test]
fn metadata_output_failures_emit_no_callback_evidence() {
    for json in [false, true] {
        let session = Session::new("pub fn valid() {}\n");
        std::fs::write(
            session.directory.path().join("output-parent"),
            "regular file\n",
        )
        .expect("write regular file in place of output directory");
        let mut command = session.command();
        command.arg("--emit=metadata=output-parent/session.rmeta");
        if json {
            command.arg("--error-format=json");
        }
        let output = command.output().expect("run failing metadata output");
        assert_failed(&output, "output-parent");
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        if json {
            json_diagnostics(&output);
        }
    }
}

#[cfg(unix)]
#[test]
fn non_utf8_arguments_fail_without_panicking_or_callback_evidence() {
    use std::os::unix::ffi::OsStringExt;

    for json in [false, true] {
        let session = Session::new("pub fn valid() {}\n");
        let mut command = session.command();
        if json {
            command.arg("--error-format=json");
        }
        let output = command
            .arg(std::ffi::OsString::from_vec(vec![0xff]))
            .env_remove("RUST_BACKTRACE")
            .output()
            .expect("run compiler with non-UTF-8 argument");
        assert_failed(&output, "compiler argument is not UTF-8");
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(stderr(&output).starts_with("error: "), "{output:?}");
        assert!(!stderr(&output).contains("panicked"), "{output:?}");
    }
}

#[cfg(unix)]
#[test]
fn non_utf8_program_names_fail_without_panicking_or_callback_evidence() {
    use std::os::unix::ffi::OsStringExt;
    use std::os::unix::process::CommandExt;

    for json in [false, true] {
        let session = Session::new("pub fn valid() {}\n");
        let mut command = session.command();
        if json {
            command.arg("--error-format=json");
        }
        let output = command
            .arg0(std::ffi::OsString::from_vec(vec![0xff]))
            .env_remove("RUST_BACKTRACE")
            .output()
            .expect("run compiler with non-UTF-8 program name");
        assert_failed(&output, "compiler program name is not UTF-8");
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(stderr(&output).starts_with("error: "), "{output:?}");
        assert!(!stderr(&output).contains("panicked"), "{output:?}");
    }
}

#[test]
fn linker_failure_after_analysis_emits_no_callback_evidence() {
    let session = Session::new("pub fn valid() {}\n");
    let missing_linker: PathBuf = session.directory.path().join("missing-linker");
    for json in [false, true] {
        let mut command = session.command();
        command
            .arg("--emit=link")
            .arg(format!("-Clinker={}", missing_linker.display()))
            .arg("--crate-type=cdylib");
        if json {
            command.arg("--error-format=json");
        }
        let output = command.output().expect("run failing linker session");
        assert_failed(&output, "linker");
        if json {
            json_diagnostics(&output);
        }
    }
}

#[test]
fn compiler_information_is_not_callback_evidence() {
    let session = Session::new("pub fn valid() {}\n");
    let output = session
        .command()
        .arg("--print=sysroot")
        .output()
        .expect("run compiler information request");
    assert_failed(&output, "without reaching a clean analysis callback");
}

#[test]
fn rustc_resolves_sysroot_options_in_response_files() {
    let session = Session::new("pub fn valid() {}\n");
    let sysroot = std::env::var("ANNEAL_TEST_RUST_SYSROOT")
        .expect("set ANNEAL_TEST_RUST_SYSROOT to the pinned Rust distribution");
    std::fs::write(
        session.directory.path().join("options"),
        format!(
            "--sysroot\n{sysroot}\ninput.rs\n--crate-type=lib\n\
             --emit=metadata\n-o\nsession.rmeta\n"
        ),
    )
    .expect("write compiler response file");
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .current_dir(session.directory.path())
        .arg("@options")
        .output()
        .expect("run compiler response file");
    assert!(output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert_callback(&output);
}

#[test]
fn unbundled_driver_requires_an_explicit_sysroot() {
    let session = Session::new("pub fn valid() {}\n");
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .current_dir(session.directory.path())
        .args([
            "input.rs",
            "--crate-type=lib",
            "--emit=metadata",
            "-o",
            "session.rmeta",
        ])
        .output()
        .expect("run unbundled driver without sysroot");
    assert_failed(&output, "packaged Rust sysroot is missing");
}

#[test]
fn help_and_version_do_not_claim_callback_execution() {
    for option in ["--help", "-h", "--version", "-V"] {
        let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
            .arg(option)
            .output()
            .expect("run informational command");
        assert!(output.status.success(), "{output:?}");
        assert!(stdout(&output).contains("anneal-rustc-capture"));
        assert!(!stdout(&output).contains(CALLBACK));
    }
}

#[test]
fn explicit_separator_routes_information_requests_to_rustc() {
    for (option, compiler_output) in [
        ("--help", "Usage: rustc"),
        ("--version", "rustc 1.98.0-nightly (f8a08b688 2026-05-30)"),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
            .args(["--", option])
            .output()
            .expect("run compiler information command through separator");
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(stdout(&output).starts_with(compiler_output), "{output:?}");
        assert!(!stdout(&output).contains(CALLBACK), "{output:?}");
        assert!(!stderr(&output).contains(CALLBACK), "{output:?}");
    }
}

#[test]
fn compiler_artifacts_on_stdout_match_rustc_bytes() {
    let session = Session::new("pub fn valid() -> u8 { 42 }\n");
    // Use the build's pinned compiler command. Nix supplies a loader wrapper
    // because upstream rustc's host loader is absent from its build sandbox.
    let rustc = std::env::var_os("RUSTC")
        .expect("set RUSTC to the pinned Rust compiler or its build wrapper");
    let version = Command::new(&rustc)
        .arg("--version")
        .output()
        .expect("run the pinned build compiler");
    assert!(version.status.success(), "{version:?}");
    assert_eq!(
        stdout(&version).trim(),
        "rustc 1.98.0-nightly (f8a08b688 2026-05-30)"
    );
    for emission in ["--emit=asm=-", "--emit=llvm-ir=-", "--emit=obj=-"] {
        let expected = session
            .command_for(&rustc)
            .arg(emission)
            .output()
            .expect("run rustc with artifact on stdout");
        assert!(expected.status.success(), "{expected:?}");
        assert!(!expected.stdout.is_empty(), "{expected:?}");
        let output = session
            .command()
            .arg(emission)
            .output()
            .expect("run capture driver with artifact on stdout");
        assert_callback(&output);
        assert_eq!(output.stdout, expected.stdout, "{emission}");
    }
}

#[test]
fn successful_json_compilation_emits_a_callback_note() {
    let output = Session::new("pub fn valid() {}\n")
        .command()
        .arg("--error-format=json")
        .output()
        .expect("run capture driver with JSON diagnostics");
    assert!(output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    let diagnostics = json_diagnostics(&output);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
    assert_eq!(diagnostics[0]["level"], "note");
    assert_eq!(diagnostics[0]["message"], CALLBACK);
}

#[test]
fn json_compile_failures_contain_only_compiler_diagnostics() {
    for (source, diagnostic) in [
        ("pub fn broken( {\n", "unclosed delimiter"),
        ("pub fn mismatch() -> u8 { \"wrong type\" }\n", "E0308"),
    ] {
        let output = Session::new(source)
            .command()
            .arg("--error-format=json")
            .output()
            .expect("run failing compiler session with JSON diagnostics");
        assert_failed(&output, diagnostic);
        json_diagnostics(&output);
    }
}

#[test]
fn missing_packaged_sysroot_preserves_json_diagnostic_format() {
    let session = Session::new("pub fn valid() {}\n");
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .current_dir(session.directory.path())
        .args(["input.rs", "--crate-type=lib", "--error-format=json"])
        .output()
        .expect("run unbundled driver with JSON diagnostics");
    assert_failed(&output, "packaged Rust sysroot is missing");
    json_diagnostics(&output);
}

#[test]
fn information_without_analysis_preserves_json_diagnostic_format() {
    let output = Session::new("pub fn valid() {}\n")
        .command()
        .args(["--print=sysroot", "--error-format=json"])
        .output()
        .expect("run compiler information request with JSON diagnostics");
    assert_failed(&output, "without reaching a clean analysis callback");
    json_diagnostics(&output);
}

#[test]
fn compiler_panics_use_rustcs_ice_hook() {
    let output = Session::new("pub fn mismatch() -> u8 { \"wrong type\" }\n")
        .command()
        .arg("-Ztreat-err-as-bug=1")
        .env("RUST_BACKTRACE", "0")
        .env("RUSTC_ICE", "0")
        .output()
        .expect("run compiler with error promoted to an ICE");
    assert_failed(&output, "the compiler unexpectedly panicked");
    let diagnostics = stderr(&output);
    assert!(
        diagnostics.contains("https://github.com/joshlf/anneal/issues/new"),
        "{diagnostics}"
    );
    assert!(diagnostics.contains("f8a08b688"), "{diagnostics}");
    assert!(
        diagnostics.contains("query stack during panic"),
        "{diagnostics}"
    );
}
