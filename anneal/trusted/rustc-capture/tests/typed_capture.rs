// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Check explicit typed capture and its separation from raw compiler arguments.

mod common;

use std::path::PathBuf;
use std::process::{Command, Output};

use common::sysroot;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fmt::Write as _;

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hex = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        let _ = write!(&mut hex, "{byte:02x}");
    }
    hex
}

struct Capture {
    directory: tempfile::TempDir,
    source: PathBuf,
    output: PathBuf,
}

impl Capture {
    fn new(source: &[u8]) -> Self {
        let directory = tempfile::tempdir().expect("create capture fixture");
        let source_path = directory.path().join("input.rs");
        std::fs::write(&source_path, source).expect("write capture fixture");
        let output = directory.path().join("output");
        Self {
            directory,
            source: source_path,
            output,
        }
    }

    fn command(&self) -> Command {
        self.command_with("session", true)
    }

    fn command_with(&self, crate_name: &str, declare_source: bool) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"));
        command
            .current_dir(self.directory.path())
            .arg("capture")
            .arg("--crate-root")
            .arg(&self.source)
            .arg(format!("--crate-name={crate_name}"))
            .arg("--target=x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&self.output)
            .arg("--sysroot")
            .arg(sysroot());
        if declare_source {
            command.arg("--source-file").arg(&self.source);
        }
        command
    }

    fn selected_command(&self) -> Command {
        let mut command = self.command();
        command.arg("--select=selected");
        command
    }

    fn manifest(&self) -> Value {
        serde_json::from_slice(
            &std::fs::read(self.output.join("capture.json")).expect("read capture manifest"),
        )
        .expect("parse capture manifest")
    }

    fn assert_no_capture_artifacts(&self) {
        for name in ["capture.json", "Captured.lean"] {
            assert!(
                std::fs::symlink_metadata(self.output.join(name)).is_err(),
                "capture artifact {name} exists after failure"
            );
        }
    }
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn status(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).expect("typed capture returns one JSON status")
}

#[test]
fn no_arguments_show_help_without_running_the_compiler() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .output()
        .expect("run capture without arguments");
    assert!(output.status.success(), "{output:?}");
    assert!(stdout(&output).contains("Usage:"), "{output:?}");
    assert!(stdout(&output).contains("capture"), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
}

#[test]
fn explicit_capture_requires_typed_arguments_and_has_its_own_help() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .arg("capture")
        .output()
        .expect("run capture without typed arguments");
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");

    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .args(["capture", "--help"])
        .output()
        .expect("run typed capture help");
    assert!(output.status.success(), "{output:?}");
    assert!(stdout(&output).contains("--crate-root"), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
}

#[test]
fn separator_preserves_a_raw_input_named_capture() {
    let fixture = Capture::new(b"pub fn selected() {}\n");
    let source = fixture.directory.path().join("capture");
    std::fs::rename(&fixture.source, &source).expect("name raw source capture");
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .current_dir(fixture.directory.path())
        .args([
            "--",
            "capture",
            "--crate-name=session",
            "--crate-type=lib",
            "--emit=metadata",
            "-o",
            "session.rmeta",
        ])
        .arg("--sysroot")
        .arg(sysroot())
        .output()
        .expect("run raw source named capture");
    assert!(output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(
        stderr(&output).contains("compiler analysis callback reached; verification not performed"),
        "{output:?}"
    );
    assert!(fixture.directory.path().join("session.rmeta").is_file());
}

#[test]
fn typed_options_do_not_select_typed_mode_without_the_subcommand() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .args(["--crate-root", "input.rs"])
        .output()
        .expect("pass typed option to raw compiler mode");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(
        stderr(&output).contains("Unrecognized option"),
        "{output:?}"
    );
    assert!(stderr(&output).contains("crate-root"), "{output:?}");
}

#[test]
fn selected_capture_keeps_unselected_unsupported_items_in_the_census() {
    let fixture = Capture::new(
        b"pub fn selected(value: u64) -> u64 { value }\n\
          pub fn unsupported(value: f64) -> f64 { value }\n",
    );
    let output = fixture
        .selected_command()
        .output()
        .expect("capture selected supported function");
    assert!(output.status.success(), "{output:?}");
    assert_eq!(status(&output)["status"], "captured", "{output:?}");
    let manifest = fixture.manifest();
    assert_eq!(manifest["schema_version"], 5);
    assert!(manifest.get("scope").is_none(), "{manifest}");
    assert_eq!(manifest["program"]["scope"]["kind"], "selected_unit");
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 1);
    let census = manifest["census"].as_array().expect("complete census");
    for (path, selected) in [("selected", true), ("unsupported", false)] {
        let item = census
            .iter()
            .find(|item| item["path"] == path)
            .expect("both function bodies are inventoried");
        assert_eq!(item["has_body"], true);
        assert_eq!(item["required"], true);
        assert_eq!(item["selected"], selected);
    }
    assert!(fixture.output.join("Captured.lean").is_file());
}

#[test]
fn whole_crate_capture_refuses_an_unsupported_function() {
    let fixture = Capture::new(
        b"pub fn selected(value: u64) -> u64 { value }\n\
          pub fn unsupported(value: f64) -> f64 { value }\n",
    );
    let output = fixture
        .command()
        .arg("--scope=crate")
        .output()
        .expect("capture crate with an unsupported function");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{output:?}");
    assert!(
        failure["unsupported"]
            .as_array()
            .expect("unsupported obligations")
            .iter()
            .any(|item| item["path"] == "unsupported"),
        "{failure}"
    );
    fixture.assert_no_capture_artifacts();
}

#[test]
fn source_hashes_bind_the_exact_crlf_input_bytes() {
    let source = b"pub fn selected(value: u64) -> u64 {\r\n    value\r\n}\r\n";
    let fixture = Capture::new(source);
    let output = fixture
        .selected_command()
        .output()
        .expect("capture CRLF source input");
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let files = manifest["source_files"].as_array().expect("source records");
    assert_eq!(files.len(), 1, "{manifest}");
    assert_eq!(files[0]["sha256"], sha256_hex(source));
    assert_eq!(files[0]["read_kind"], "text");
}

#[test]
fn typed_argument_and_compiler_failures_leave_no_capture_artifacts() {
    let fixture = Capture::new(b"pub fn selected() {}\n");
    let output = fixture
        .selected_command()
        .arg("--unknown-anneal-test-option")
        .output()
        .expect("run invalid typed arguments");
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");
    fixture.assert_no_capture_artifacts();

    for source in [
        b"pub fn selected( {\n".as_slice(),
        b"pub fn selected() -> u64 { \"wrong type\" }\n".as_slice(),
    ] {
        let fixture = Capture::new(source);
        let output = fixture
            .selected_command()
            .output()
            .expect("run typed capture with compiler errors");
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn metadata_failure_after_typed_analysis_prohibits_capture_artifacts() {
    let fixture = Capture::new(b"pub fn selected() {}\n");
    // The name is valid Rust but its metadata filename exceeds supported hosts'
    // filesystem component limit. This fails after typed analysis without
    // pre-creating an output directory that the publisher must now refuse.
    let output = fixture
        .command_with(&"m".repeat(256), true)
        .arg("--select=selected")
        .output()
        .expect("run typed capture with metadata output failure");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
    fixture.assert_no_capture_artifacts();
}

#[cfg(unix)]
#[test]
fn typed_non_utf8_program_name_is_rejected_before_the_ice_hook() {
    use std::os::unix::ffi::OsStringExt;
    use std::os::unix::process::CommandExt;

    let fixture = Capture::new(b"pub fn selected() {}\n");
    let output = fixture
        .selected_command()
        .arg0(std::ffi::OsString::from_vec(vec![0xff]))
        .env_remove("RUST_BACKTRACE")
        .output()
        .expect("run typed capture with non-UTF-8 program name");
    assert!(!output.status.success(), "{output:?}");
    assert!(
        stderr(&output).contains("compiler program name is not UTF-8"),
        "{output:?}"
    );
    assert!(!stderr(&output).contains("panicked"), "{output:?}");
    fixture.assert_no_capture_artifacts();
}

#[test]
fn source_allowlist_is_required_and_enforced_for_modules() {
    let fixture = Capture::new(b"mod side;\npub fn selected(value: u64) -> u64 { value }\n");
    let side = fixture.directory.path().join("side.rs");
    std::fs::write(&side, "pub fn unselected() {}\n").unwrap();
    let output = fixture
        .command_with("session", false)
        .arg("--select=selected")
        .output()
        .expect("omit the source allowlist");
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert!(
        status(&output)["diagnostics"]
            .to_string()
            .contains("--source-file")
    );
    fixture.assert_no_capture_artifacts();

    let output = fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    // An undeclared ordinary module is absent to module resolution. Explicit
    // include reads are checked separately below so refusal remains required
    // even when rustc can recover from the loader's I/O error.
    assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
    assert!(
        stderr(&output).contains("file not found for module"),
        "{output:?}"
    );
    fixture.assert_no_capture_artifacts();

    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(side)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        fixture.manifest()["source_files"].as_array().unwrap().len(),
        2
    );
}

#[test]
fn monomorphization_errors_outside_the_selected_body_prohibit_capture() {
    // The selected body's syntax is unchanged between the two cases. The
    // separate exported function makes ordinary code generation evaluate the
    // generic constant, so only the compiler-completion guard distinguishes it.
    for (argument, success) in [(0, false), (1, true)] {
        let source = format!(
            "pub fn selected(value: u64) -> u64 {{ value }}\n\
             fn generic<const N: usize>() {{ const {{ assert!(N > 0); }} }}\n\
             pub fn other() {{ generic::<{argument}>(); }}\n"
        );
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.selected_command().output().unwrap();
        assert_eq!(output.status.success(), success, "{output:?}");
        if success {
            assert_eq!(status(&output)["status"], "captured", "{output:?}");
            assert_eq!(std::fs::read_dir(&fixture.output).unwrap().count(), 2);
        } else {
            assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
            assert!(stderr(&output).contains("E0080"), "{output:?}");
            fixture.assert_no_capture_artifacts();
            assert!(!fixture.output.exists());
        }
    }
}

#[test]
fn existing_destinations_are_refused_without_changing_their_contents() {
    for populated in [false, true] {
        let fixture = Capture::new(b"pub fn selected() {}\n");
        std::fs::create_dir(&fixture.output).unwrap();
        if populated {
            std::fs::write(fixture.output.join("caller-data"), b"preserve").unwrap();
        }
        let output = fixture.selected_command().output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(
            stdout(&output).contains("new output directory"),
            "{output:?}"
        );
        fixture.assert_no_capture_artifacts();
        assert_eq!(
            std::fs::read_dir(&fixture.output).unwrap().count(),
            usize::from(populated)
        );
        if populated {
            assert_eq!(
                std::fs::read(fixture.output.join("caller-data")).unwrap(),
                b"preserve"
            );
        }
    }
}

#[cfg(unix)]
#[test]
fn existing_output_symlink_is_refused_without_touching_its_target() {
    let fixture = Capture::new(b"pub fn selected() {}\n");
    let target = fixture.directory.path().join("caller-directory");
    std::fs::create_dir(&target).unwrap();
    std::fs::write(target.join("caller-data"), b"preserve").unwrap();
    std::os::unix::fs::symlink(&target, &fixture.output).unwrap();
    let output = fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(
        stdout(&output).contains("new output directory"),
        "{output:?}"
    );
    assert_eq!(
        std::fs::read(target.join("caller-data")).unwrap(),
        b"preserve"
    );
    assert_eq!(std::fs::read_dir(target).unwrap().count(), 1);
    assert!(
        std::fs::symlink_metadata(&fixture.output)
            .unwrap()
            .file_type()
            .is_symlink()
    );
}

#[test]
fn unicode_function_identity_is_data_in_the_captured_subject() {
    // The manifest keeps UTF-8 text while Lean receives numeric character data.
    // Check both representations at a non-ASCII boundary used by real names.
    let fixture = Capture::new("pub unsafe fn café() -> u64 { 0 }\n".as_bytes());
    let output = fixture
        .command()
        .arg("--select=café")
        .output()
        .expect("capture a Unicode function identity");
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    assert_eq!(
        manifest["program"]["bodies"][0]["identity"],
        "rust-path-v1::café"
    );
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(!lean.contains("café"));
    assert!(lean.contains("(_root_.Char.ofNat 233)"));
}

#[test]
fn function_identities_survive_unrelated_impl_insertion_and_reordering() {
    // Impl ordinals change when another impl is inserted. The same method name
    // on different self types must keep its own semantic owner in the key.
    let before = Capture::new(
        b"pub struct A; pub struct B;\n\
          impl A { pub unsafe fn entry() -> u64 { 0 } }\n\
          impl B { pub unsafe fn entry() -> u64 { 0 } }\n",
    );
    let after = Capture::new(
        b"pub struct A; pub struct B; pub struct C;\n\
          impl C { pub unsafe fn entry() -> u64 { 0 } }\n\
          impl B { pub unsafe fn entry() -> u64 { 0 } }\n\
          impl A { pub unsafe fn entry() -> u64 { 0 } }\n",
    );
    let identities = |fixture: &Capture| {
        let output = fixture
            .command()
            .args(["--select=A::entry", "--select=B::entry"])
            .output()
            .expect("capture selected associated functions");
        assert!(output.status.success(), "{output:?}");
        let manifest = fixture.manifest();
        manifest["selected"]
            .as_array()
            .unwrap()
            .iter()
            .map(|selected| {
                let index = selected["body_index"].as_u64().unwrap() as usize;
                (
                    selected["path"].as_str().unwrap().to_owned(),
                    manifest["program"]["bodies"][index]["identity"]
                        .as_str()
                        .unwrap()
                        .to_owned(),
                )
            })
            .collect::<std::collections::BTreeMap<_, _>>()
    };
    let expected = std::collections::BTreeMap::from([
        ("A::entry".to_owned(), "rust-path-v1::A::entry".to_owned()),
        ("B::entry".to_owned(), "rust-path-v1::B::entry".to_owned()),
    ]);
    assert_eq!(identities(&before), expected);
    assert_eq!(identities(&after), expected);
}

#[test]
fn trait_impl_identity_uses_the_semantic_owner() {
    // Trait members can share a name across impls. Their contract keys must
    // retain the self/trait owner rather than collapse to that member name.
    let fixture = Capture::new(
        b"pub struct A; pub struct B;\n\
          pub trait T { unsafe fn entry() -> u64; }\n\
          impl T for A { unsafe fn entry() -> u64 { 0 } }\n\
          impl T for B { unsafe fn entry() -> u64 { 0 } }\n",
    );
    let output = fixture
        .command()
        .args(["--select=<A as T>::entry", "--select=<B as T>::entry"])
        .output()
        .expect("capture selected trait-implementation functions");
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let identities: std::collections::BTreeSet<_> = manifest["program"]["bodies"]
        .as_array()
        .unwrap()
        .iter()
        .map(|body| body["identity"].as_str().unwrap())
        .collect();
    assert_eq!(
        identities,
        std::collections::BTreeSet::from([
            "rust-path-v1::<A as T>::entry",
            "rust-path-v1::<B as T>::entry",
        ])
    );
}

#[test]
fn cfg_values_are_literals_not_response_files() {
    // Keep the response file outside the declared source inventory. Expansion
    // would inject `injected`, bypassing this source's compilation guard while
    // the capture manifest still reported the original @path as its cfg.
    const SOURCE: &[u8] = b"#[cfg(not(injected))]\ncompile_error!(\"missing declared cfg\");\npub fn selected() -> u64 { 0 }\n";
    let external = tempfile::tempdir().unwrap();
    let response = external.path().join("compiler-flags.rsp");
    std::fs::write(&response, b"dummy\n--cfg\ninjected\n").unwrap();
    for path in [response, external.path().join("missing.rsp")] {
        let fixture = Capture::new(SOURCE);
        let cfg = format!("@{}", path.to_str().unwrap());
        let output = fixture
            .selected_command()
            .arg(format!("--cfg={cfg}"))
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "cfg response path was accepted:\n{}\n{}",
            stdout(&output),
            stderr(&output)
        );
        assert_eq!(status(&output)["status"], "compiler_failed");
        // Both an existing response and a nonexistent path must reach rustc's
        // cfg parser. A response-file read would instead load extra flags or
        // produce an argument-file I/O error before cfg parsing.
        assert!(stderr(&output).contains("invalid `--cfg` argument"));
        assert!(!stderr(&output).contains("failed to load argument file"));
        fixture.assert_no_capture_artifacts();
    }

    // Preserve ordinary flag and quoted-string cfgs, including @ inside a
    // legitimate string value. Rustc remains the authority for cfg grammar.
    let fixture = Capture::new(SOURCE);
    let output = fixture
        .selected_command()
        .arg("--cfg=injected")
        .arg(r#"--cfg=feature="@literal""#)
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", stderr(&output));
    assert_eq!(
        fixture.manifest()["configuration"]["cfg"],
        serde_json::json!([r#"feature="@literal""#, "injected"])
    );
}

// Compare complete artifacts, not only exit status: an ambient file must not
// silently change the compiler census, captured body, or recorded read set.
fn capture_pair(fixture: &Capture) -> [Vec<u8>; 2] {
    ["capture.json", "Captured.lean"].map(|name| {
        std::fs::read(fixture.output.join(name)).expect("read successful capture artifact")
    })
}

#[test]
fn declared_namespace_hides_ambient_module_alternatives() {
    let mut fixture = Capture::new(b"mod side;\npub fn selected() -> u64 { 0 }\n");
    let side = fixture.directory.path().join("side.rs");
    let secondary = fixture.directory.path().join("side/mod.rs");
    std::fs::write(&side, "pub fn other() {}\n").unwrap();
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&side)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "initial declared module: {output:?}"
    );
    let expected = capture_pair(&fixture);

    std::fs::create_dir(secondary.parent().unwrap()).unwrap();
    std::fs::write(&secondary, "pub fn ambient() {}\n").unwrap();
    fixture.output = fixture.directory.path().join("with-ambient-file");
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&side)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "undeclared alternative changed compilation: {output:?}"
    );
    assert_eq!(capture_pair(&fixture), expected);

    // Declaring both names deliberately changes the configured compilation.
    // Hiding all module probes would miss rustc's required ambiguity error.
    fixture.output = fixture.directory.path().join("both-declared");
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&side)
        .arg("--source-file")
        .arg(&secondary)
        .output()
        .unwrap();
    assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
    assert!(stderr(&output).contains("found at both"), "{output:?}");
    fixture.assert_no_capture_artifacts();

    fixture.output = fixture.directory.path().join("secondary-declared");
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&secondary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "declared secondary module: {output:?}"
    );
    assert_eq!(
        fixture.manifest()["source_files"].as_array().unwrap().len(),
        2
    );

    #[cfg(unix)]
    {
        // Target membership alone would expose this unlisted alias and restore
        // the same hidden ambiguity, despite the target's declared bytes.
        std::fs::remove_file(&secondary).unwrap();
        std::os::unix::fs::symlink(&side, &secondary).unwrap();
        fixture.output = fixture.directory.path().join("with-ambient-alias");
        let output = fixture
            .selected_command()
            .arg("--source-file")
            .arg(&side)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "undeclared alias changed compilation: {output:?}"
        );
        assert_eq!(capture_pair(&fixture), expected);
    }
}

#[test]
fn declared_namespace_preserves_parent_paths_and_hides_missing_prefixes() {
    let mut fixture = Capture::new(b"pub fn selected() -> u64 { 0 }\n");
    let sub = fixture.directory.path().join("sub");
    std::fs::create_dir(&sub).unwrap();
    fixture.source = sub.join("input.rs");
    std::fs::write(
        &fixture.source,
        "#[path=\"../shared.rs\"] mod shared;\npub fn selected() -> u64 { 0 }\n",
    )
    .unwrap();
    let shared = fixture.directory.path().join("shared.rs");
    std::fs::write(&shared, "pub fn other() {}\n").unwrap();
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&shared)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "declared ancestor ../ path: {output:?}"
    );

    // A canceled directory still has to exist in the declared namespace. The
    // answer must stay the same when the ambient directory appears later.
    std::fs::write(
        &fixture.source,
        "#[path=\"missing/../../shared.rs\"] mod shared;\npub fn selected() -> u64 { 0 }\n",
    )
    .unwrap();
    for present in [false, true] {
        if present {
            std::fs::create_dir(sub.join("missing")).unwrap();
        }
        fixture.output = fixture
            .directory
            .path()
            .join(format!("missing-prefix-{present}"));
        let output = fixture
            .selected_command()
            .arg("--source-file")
            .arg(&shared)
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "ambient prefix admitted: {output:?}"
        );
        assert!(
            stdout(&output).contains("undeclared compiler read"),
            "{output:?}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn declared_namespace_guards_text_and_binary_include_reads() {
    let mut fixture = Capture::new(
        b"const TEXT: &str = include_str!(\"text.txt\");\n\
        const BINARY: &[u8] = include_bytes!(\"binary.dat\");\n\
        pub fn selected() -> u64 { 0 }\n",
    );
    let text = fixture.directory.path().join("text.txt");
    let binary = fixture.directory.path().join("binary.dat");
    std::fs::write(&text, b"line one\r\nline two\r\n").unwrap();
    std::fs::write(&binary, [0, 255, 13, 10]).unwrap();
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&text)
        .arg("--source-file")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "declared text/binary include: {output:?}"
    );
    let sources = fixture.manifest()["source_files"]
        .as_array()
        .unwrap()
        .clone();
    for (path, bytes, kind) in [
        (&text, std::fs::read(&text).unwrap(), "binary"),
        (&binary, std::fs::read(&binary).unwrap(), "binary"),
    ] {
        let entry = sources
            .iter()
            .find(|entry| entry["path"] == path.to_str().unwrap())
            .unwrap();
        assert_eq!(entry["sha256"], sha256_hex(&bytes));
        assert_eq!(entry["read_kind"], kind);
    }
    fixture.output = fixture.directory.path().join("undeclared-include");
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&text)
        .output()
        .unwrap();
    assert_eq!(status(&output)["status"], "unsupported", "{output:?}");
    assert!(
        stdout(&output).contains("undeclared compiler read"),
        "{output:?}"
    );
    fixture.assert_no_capture_artifacts();

    #[cfg(unix)]
    {
        let alias = fixture.directory.path().join("text-alias.txt");
        std::os::unix::fs::symlink(&text, &alias).unwrap();
        std::fs::write(&fixture.source,
            "const TEXT: &str = include_str!(\"text-alias.txt\");\npub fn selected() -> u64 { 0 }\n").unwrap();
        fixture.output = fixture.directory.path().join("undeclared-include-alias");
        let output = fixture
            .selected_command()
            .arg("--source-file")
            .arg(&text)
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "undeclared read alias admitted: {output:?}"
        );
        assert!(
            stdout(&output).contains("undeclared compiler read"),
            "{output:?}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[cfg(unix)]
#[test]
fn non_utf8_output_destinations_fail_before_publication_and_remain_retryable() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;

    for form in ["final", "ancestor", "relative", "symlink"] {
        let mut fixture = Capture::new(b"pub fn selected() -> u64 { 0 }\n");
        let non_utf8 = OsString::from_vec(b"output-\xff".to_vec());
        let native_parent = fixture.directory.path().join(&non_utf8);
        let mut cwd = fixture.directory.path().to_path_buf();
        let destination = if form == "final" {
            fixture.directory.path().join(&non_utf8)
        } else {
            std::fs::create_dir(&native_parent).unwrap();
            native_parent.join("output")
        };
        fixture.output = match form {
            "relative" => {
                // A UTF-8 argv spelling can resolve through a native cwd.
                cwd = native_parent.clone();
                PathBuf::from("output")
            }
            "symlink" => {
                // The publisher canonicalizes parents. Its returned receipt
                // path must be checked, not just the UTF-8 symlink spelling.
                let alias = fixture.directory.path().join("alias");
                std::os::unix::fs::symlink(&native_parent, &alias).unwrap();
                alias.join("output")
            }
            _ => destination.clone(),
        };
        for attempt in 0..2 {
            let output = fixture
                .selected_command()
                .current_dir(&cwd)
                .output()
                .unwrap();
            assert_eq!(
                output.status.code(),
                Some(1),
                "{form}/{attempt}: {output:?}"
            );
            assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");
            assert!(
                !destination.exists(),
                "failed receipt left a published destination ({form}/{attempt}): {output:?}"
            );
            assert!(
                stdout(&output).contains("output destination must be UTF-8"),
                "{form}/{attempt}: {output:?}"
            );
            assert!(output.stderr.is_empty(), "{form}/{attempt}: {output:?}");
            let parent = destination.parent().unwrap();
            assert!(std::fs::read_dir(parent).unwrap().all(|entry| {
                !entry
                    .unwrap()
                    .file_name()
                    .to_string_lossy()
                    .starts_with(".anneal-capture-")
            }));
        }
        // Refusal reserves no output name and leaves the source usable. A
        // corrected UTF-8 destination can publish the complete pair normally.
        fixture.output = fixture.directory.path().join("valid-output");
        let output = fixture.selected_command().output().unwrap();
        assert!(output.status.success(), "{form}: {output:?}");
        assert_eq!(status(&output)["status"], "captured");
        assert_eq!(std::fs::read_dir(&fixture.output).unwrap().count(), 2);
    }
}

#[test]
fn captured_safety_bits_follow_safe_and_unsafe_declarations() {
    let fixture = Capture::new(
        b"pub fn safe_entry() -> u64 { 0 }\n\
          pub unsafe fn unsafe_entry() -> u64 { 0 }\n",
    );
    let output = fixture
        .command()
        .args(["--select=safe_entry", "--select=unsafe_entry"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let bodies = manifest["program"]["bodies"].as_array().unwrap();
    assert_eq!(bodies.len(), 2);
    for (identity, expected) in [
        ("rust-path-v1::safe_entry", false),
        ("rust-path-v1::unsafe_entry", true),
    ] {
        let body = bodies
            .iter()
            .find(|body| body["identity"] == identity)
            .unwrap();
        assert_eq!(body["is_unsafe"], expected, "{body}");
    }
}

#[test]
fn enum_representations_follow_admitted_zst_and_scalar_tag_rules() {
    let empty_source = b"pub enum Empty {}\npub fn selected(x: Empty) -> u64 { match x {} }\n";
    for crate_scope in [false, true] {
        let fixture = Capture::new(empty_source);
        let mut cmd = if crate_scope {
            let mut cmd = fixture.command();
            cmd.arg("--scope=crate");
            cmd
        } else {
            fixture.selected_command()
        };
        let output = cmd.output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{failure}");
        assert!(
            failure
                .to_string()
                .contains("uninhabited zero-variant enums are unsupported"),
            "{failure}"
        );
        fixture.assert_no_capture_artifacts();
    }

    let repr_single =
        b"#[repr(isize)]\npub enum ReprSingle { Only = 7 }\npub fn selected(x: ReprSingle) -> isize { match x { ReprSingle::Only => 7 } }\n";
    let fixture = Capture::new(repr_single);
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let ty = &manifest["program"]["bodies"][0]["local_tys"][1];
    assert_eq!(ty["kind"], "enum", "{ty}");
    assert_eq!(ty["discr_width"], "isize", "{ty}");
    assert_eq!(ty["discr_signed"], true, "{ty}");
    assert_eq!(ty["tag_repr"]["kind"], "scalar", "{ty}");
    assert_eq!(ty["tag_repr"]["width"], "i64", "{ty}");
    assert_eq!(ty["discriminants"], serde_json::json!(["7"]), "{ty}");

    let zst_single =
        b"pub enum Single { Only = 42 }\npub fn selected(x: Single) -> isize { match x { Single::Only => 42 } }\n";
    let fixture = Capture::new(zst_single);
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let ty = &manifest["program"]["bodies"][0]["local_tys"][1];
    assert_eq!(ty["kind"], "enum", "{ty}");
    assert_eq!(ty["tag_repr"]["kind"], "zero_sized", "{ty}");
    assert_eq!(ty["discriminants"], serde_json::json!(["42"]), "{ty}");

    let repr_u8 = b"#[repr(u8)]\npub enum ExplicitU8 { Ten = 10, Twenty = 20 }\npub fn selected(x: ExplicitU8) -> u8 { match x { ExplicitU8::Ten => 10, ExplicitU8::Twenty => 20 } }\n";
    let fixture = Capture::new(repr_u8);
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let ty = &manifest["program"]["bodies"][0]["local_tys"][1];
    assert_eq!(ty["kind"], "enum", "{ty}");
    assert_eq!(ty["discr_width"], "i8", "{ty}");
    assert_eq!(ty["discr_signed"], false, "{ty}");
    assert_eq!(ty["tag_repr"]["width"], "i8", "{ty}");
    assert_eq!(ty["discriminants"], serde_json::json!(["10", "20"]), "{ty}");

    let empty_crate = Capture::new(b"");
    let output = empty_crate.command().arg("--scope=crate").output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(
        failure
            .to_string()
            .contains("captured program contains no executable bodies"),
        "{failure}"
    );
    empty_crate.assert_no_capture_artifacts();
}

#[test]
fn negative_isize_enum_discriminants_are_captured_as_64_bit_twos_complement() {
    let source = b"\
        #[repr(isize)]\n\
        pub enum Signed {\n\
            Neg = -1,\n\
            Zero = 0,\n\
            Pos = 1,\n\
        }\n\
        pub fn selected(s: Signed) -> isize {\n\
            match s {\n\
                Signed::Neg => -1,\n\
                Signed::Zero => 0,\n\
                Signed::Pos => 1,\n\
            }\n\
        }\n";
    let fixture = Capture::new(source);
    let output = fixture
        .selected_command()
        .output()
        .expect("capture signed repr(isize) enum");
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let discriminants = manifest["program"]["bodies"][0]["local_tys"][1]["discriminants"]
        .as_array()
        .expect("enum discriminants");
    let values: Vec<u128> = discriminants
        .iter()
        .map(|v| {
            v.as_str()
                .expect("decimal string discriminant")
                .parse::<u128>()
                .expect("u128 discriminant")
        })
        .collect();
    assert_eq!(values, vec![u128::from(u64::MAX), 0, 1]);
    let lean =
        std::fs::read_to_string(fixture.output.join("Captured.lean")).expect("read Captured.lean");
    assert!(
        lean.contains("[18446744073709551615, 0, 1]"),
        "expected 64-bit two's-complement discriminant list in Captured.lean:\n{lean}"
    );
}

#[test]
fn retag_flags_are_recorded_on_scalar_use_and_reference_assignments_are_refused() {
    let scalar_fixture = Capture::new(b"pub fn selected(x: u64) -> u64 { x }\n");
    let output = scalar_fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = scalar_fixture.manifest();
    let stmt = &manifest["program"]["bodies"][0]["blocks"][0]["statements"][0];
    assert_eq!(stmt["value"]["kind"], "use", "{stmt}");
    assert_eq!(stmt["value"]["with_retag"], true, "{stmt}");
    let lean = std::fs::read_to_string(scalar_fixture.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("Trusted.MirAst.Rvalue.use"), "{lean}");
    assert!(!lean.contains("Rvalue.unsupported"), "{lean}");

    let ref_fixture = Capture::new(b"pub fn selected(x: &u64) -> &u64 { x }\n");
    let output = ref_fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(status(&output)["status"], "unsupported", "{output:?}");
    ref_fixture.assert_no_capture_artifacts();
}

#[test]
fn empty_tuple_preserves_distinct_unit_ir_and_admits_non_empty_tuples() {
    let fixture = Capture::new(b"pub fn selected() -> () { let x = (); x }\n");
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let stmts = manifest["program"]["bodies"][0]["blocks"][0]["statements"]
        .as_array()
        .expect("statements");
    assert!(
        stmts
            .iter()
            .any(|s| s["kind"] == "assign" && s["value"] == serde_json::json!({"kind": "unit"})),
        "expected distinct {{\"kind\": \"unit\"}} rvalue in capture.json: {stmts:?}"
    );
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(
        lean.contains("(Trusted.MirAst.Rvalue.aggregateTuple [])"),
        "{lean}"
    );
    assert!(
        !lean.contains("(Trusted.MirAst.Rvalue.use (Trusted.MirAst.Operand.constant (Trusted.MirAst.ConstOperand.mk Trusted.MirAst.MirTy.unit Trusted.MirAst.ConstLit.zeroSized)))"),
        "empty tuple aggregate must render 1:1 as aggregateTuple [], not constant use:\n{lean}"
    );

    let non_empty_tuple = Capture::new(
        b"pub fn selected(x: u64, b: bool) -> (u64, bool) { let p = (x, b); (p.0, !p.1) }\n",
    );
    let output = non_empty_tuple.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let lean = std::fs::read_to_string(non_empty_tuple.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("Trusted.MirAst.MirTy.tuple"), "{lean}");
    assert!(
        lean.contains("Trusted.MirAst.ProjectionElem.field 0"),
        "{lean}"
    );
    assert!(
        lean.contains("Trusted.MirAst.ProjectionElem.field 1"),
        "{lean}"
    );
    assert!(
        lean.contains("Trusted.MirAst.Rvalue.aggregateTuple ["),
        "{lean}"
    );
}

#[test]
fn whole_crate_admits_implicit_fieldless_enums_and_refuses_all_anon_consts() {
    // Implicit-discriminant fieldless enums (both multi-variant and single-
    // variant ZST) have no `AnonConst` items and capture cleanly in crate
    // scope.
    let implicit_enums = b"\
        pub enum E { A, B }\n\
        pub enum Single { Only }\n\
        pub fn tag(x: E) -> u8 { match x { E::A => 0, E::B => 1 } }\n\
        pub fn match_single(v: Single) -> u8 { match v { Single::Only => 1 } }\n";
    let fixture = Capture::new(implicit_enums);
    let output = fixture.command().arg("--scope=crate").output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    assert_eq!(manifest["schema_version"], 5);
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 2);
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("EnumTagRepr.zeroSized"), "{lean}");

    // Whole-crate scope refuses ALL `DefKind::AnonConst` items fail-closed,
    // including literal explicit enum discriminants, negated literals, calls,
    // `unsafe` blocks, external constants, nested items, and array lengths.
    let refused_anon_const_cases: &[(&str, &[u8])] = &[
        (
            "explicit_u8_literal",
            b"#[repr(u8)]\n\
              pub enum ExplicitU8 { Ten = 10, Twenty = 20 }\n\
              pub fn tag(x: ExplicitU8) -> u8 {\n\
                  match x { ExplicitU8::Ten => 10, ExplicitU8::Twenty => 20 }\n\
              }\n",
        ),
        (
            "explicit_negative_literal",
            b"pub enum NarrowSigned { Neg = -1, Pos = 1 }\n\
              pub fn read_discr(v: NarrowSigned) -> isize {\n\
                  match v { NarrowSigned::Neg => -1, NarrowSigned::Pos => 1 }\n\
              }\n",
        ),
        (
            "array_length_anon_const",
            b"pub fn len_only() -> usize { let a = [0u8; 2 + 2]; a.len() }\n",
        ),
        (
            "nested_array_in_discr",
            b"pub enum Nested { A = [0u8; 1].len() as isize, B = 2 }\n\
              pub fn tag(x: Nested) -> isize { match x { Nested::A => 1, Nested::B => 2 } }\n",
        ),
        (
            "const_unsafe_fn_call",
            b"const unsafe fn h(x: isize) -> isize { x }\n\
              pub enum E { A = unsafe { h(3) }, B = 7 }\n\
              pub fn ok() -> u8 { 0 }\n",
        ),
        (
            "const_fn_call",
            b"const fn helper() -> isize { 5 }\n\
              pub enum E { A = helper(), B = 7 }\n\
              pub fn ok() -> u8 { 0 }\n",
        ),
        (
            "external_size_of_call",
            b"pub enum E { A = core::mem::size_of::<usize>() as isize, B = 7 }\n\
              pub fn ok() -> u8 { 0 }\n",
        ),
        (
            "unsafe_block_literal",
            b"pub enum E { A = unsafe { 1 }, B = 7 }\n\
              pub fn ok() -> u8 { 0 }\n",
        ),
        (
            "external_const_ref",
            b"pub enum E { A = isize::MAX, B = 7 }\n\
              pub fn ok() -> u8 { 0 }\n",
        ),
        (
            "nested_const_unsafe_fn",
            b"pub enum E {\n\
                  A = {\n\
                      const unsafe fn h(x: isize) -> isize { x }\n\
                      unsafe { h(3) }\n\
                  },\n\
                  B = 7,\n\
              }\n",
        ),
        (
            "nested_type_alias",
            b"pub enum E {\n\
                  A = {\n\
                      type Alias = isize;\n\
                      3 as Alias\n\
                  },\n\
                  B = 7,\n\
              }\n\
              pub fn ok() -> u8 { 0 }\n",
        ),
        (
            "nested_mod_fn",
            b"pub enum E {\n\
                  A = {\n\
                      mod m { pub fn f() -> u8 { 0 } }\n\
                      3\n\
                  },\n\
                  B = 7,\n\
              }\n",
        ),
    ];
    for (name, source) in refused_anon_const_cases {
        let fixture = Capture::new(source);
        let output = fixture.command().arg("--scope=crate").output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure
                .to_string()
                .contains("whole-crate obligation is unsupported: AnonConst"),
            "{name}: {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }

    // A payload enum with explicit discriminants must stay refused in
    // whole-crate scope because of its `AnonConst` items.
    let payload_enum = b"\
        #[repr(u8)]\n\
        pub enum WithPayload { A = 1, B(u8) = 2 }\n\
        pub fn ok() -> u8 { 0 }\n";
    let fixture = Capture::new(payload_enum);
    let output = fixture.command().arg("--scope=crate").output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(
        failure
            .to_string()
            .contains("whole-crate obligation is unsupported: AnonConst"),
        "{failure}"
    );
    fixture.assert_no_capture_artifacts();
}

#[test]
fn selected_unit_captures_explicit_fieldless_enum_discriminants_and_refuses_unmodeled_adts() {
    // Default-repr narrow signed enum (`discr = isize`, `tag = i8`): in
    // `selected_unit` scope, `rustc`'s evaluated discriminants record the
    // 64-bit two's-complement discriminant alongside the signed 8-bit tag.
    let default_narrow = b"\
        pub enum NarrowSigned { Neg = -1, Pos = 1 }\n\
        pub fn read_discr(v: NarrowSigned) -> isize {\n\
            match v { NarrowSigned::Neg => -1, NarrowSigned::Pos => 1 }\n\
        }\n";
    let fixture = Capture::new(default_narrow);
    let output = fixture
        .command()
        .arg("--select=read_discr")
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    assert_eq!(manifest["schema_version"], 5);
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 1);
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(
        lean.contains("EnumTagRepr.scalar Trusted.MirAst.IntWidth.i8 true"),
        "{lean}"
    );
    assert!(lean.contains("[18446744073709551615, 1]"), "{lean}");

    // `#[repr(i8)]` fieldless enum records 8-bit signed tag and 8-bit
    // discriminants `[255, 1]`.
    let repr_i8 = b"\
        #[repr(i8)]\n\
        pub enum NarrowSigned { Neg = -1, Pos = 1 }\n\
        pub fn read_discr(v: NarrowSigned) -> isize {\n\
            match v { NarrowSigned::Neg => -1, NarrowSigned::Pos => 1 }\n\
        }\n";
    let fixture = Capture::new(repr_i8);
    let output = fixture
        .command()
        .arg("--select=read_discr")
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(
        lean.contains("EnumTagRepr.scalar Trusted.MirAst.IntWidth.i8 true"),
        "{lean}"
    );
    assert!(lean.contains("[255, 1]"), "{lean}");

    // 1-variant ZST fieldless enum with explicit discriminant captures cleanly
    // in `selected_unit` scope with `EnumTagRepr.zeroSized`.
    let single_zst = b"\
        pub enum SingleExplicit { Only = 42 }\n\
        pub fn read_discr(v: SingleExplicit) -> isize {\n\
            match v { SingleExplicit::Only => 42 }\n\
        }\n";
    let fixture = Capture::new(single_zst);
    let output = fixture
        .command()
        .arg("--select=read_discr")
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("EnumTagRepr.zeroSized"), "{lean}");
    assert!(lean.contains("[42]"), "{lean}");

    // Direct ADT aggregates for fieldless enums, payload enums, and unit
    // structs are admitted in Tier 2.
    let admitted_cases: &[(&str, &[u8], &[&str], &str)] = &[
        (
            "direct_narrow_signed_aggregate",
            b"#[repr(i8)]\n\
              pub enum NarrowSigned { Neg = -1, Pos = 1 }\n\
              pub fn make() -> NarrowSigned { NarrowSigned::Neg }\n",
            &["--select=make"],
            "Trusted.MirAst.AggregateKind.adtEnum",
        ),
        (
            "direct_single_zst_aggregate",
            b"pub enum Single { Only }\n\
              pub fn make() -> Single { Single::Only }\n",
            &["--scope=crate"],
            "Trusted.MirAst.EnumTagRepr.zeroSized",
        ),
        (
            "payload_unit_variant",
            b"pub enum Payload { None, Some(u8) }\n\
              pub fn f() -> Payload { Payload::None }\n",
            &["--select=f"],
            "Trusted.MirAst.AggregateKind.adtEnum",
        ),
        (
            "unit_struct",
            b"pub struct UnitStruct;\n\
              pub fn f() -> UnitStruct { UnitStruct }\n",
            &["--select=f"],
            "Trusted.MirAst.MirTy.adtStruct",
        ),
    ];
    for (name, source, scope_args, expected_lean) in admitted_cases {
        let fixture = Capture::new(source);
        let output = fixture.command().args(*scope_args).output().unwrap();
        assert!(output.status.success(), "{name}: {output:?}");
        let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
        assert!(
            lean.contains(expected_lean),
            "{name}: expected {expected_lean:?} in:\n{lean}"
        );
    }

    // Unevaluated required constants, unions, unmodeled non-local enums, and
    // generic ADTs in crate scope must still fail closed.
    let refused_cases: &[(&str, &[u8], &[&str], &str)] = &[
        (
            "const_enum_required_consts",
            b"#[repr(i8)]\n\
              pub enum NarrowSigned { Neg = -1, Pos = 1 }\n\
              const NEG: NarrowSigned = NarrowSigned::Neg;\n\
              pub fn make_neg() -> NarrowSigned { NEG }\n",
            &["--select=make_neg"],
            "required constants are unavailable",
        ),
        (
            "union_adt",
            b"pub union U { pub a: u32, pub b: u32 }\n\
              pub fn f(a: u32) -> U { U { a } }\n",
            &["--select=f"],
            "union types are unsupported",
        ),
        (
            "non_local_enum",
            b"pub fn f() -> core::cmp::Ordering { core::cmp::Ordering::Less }\n",
            &["--scope=crate"],
            "unsupported type",
        ),
        (
            "generic_struct_in_crate_scope",
            b"pub struct Wrap<T>(pub T);\n\
              pub fn f(x: u32) -> Wrap<u32> { Wrap(x) }\n",
            &["--scope=crate"],
            "unsupported type: T/#0",
        ),
    ];
    for (name, source, scope_args, expected) in refused_cases {
        let fixture = Capture::new(source);
        let output = fixture.command().args(*scope_args).output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure.to_string().contains(expected),
            "{name}: expected {expected:?}, got {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn intrinsic_fallback_bodies_are_refused_in_selected_and_crate_scope() {
    // rustc lowers every call to this intrinsic to an `Unreachable`
    // terminator. Capturing the benign fallback body would verify code that
    // no caller executes, so both scopes must refuse the definition itself.
    let source = b"#![feature(intrinsics)]\n\
        #![allow(internal_features)]\n\
        #[rustc_intrinsic]\n\
        pub unsafe fn unreachable() -> ! { loop {} }\n";
    for scope in ["--select=unreachable", "--scope=crate"] {
        let fixture = Capture::new(source);
        let output = fixture.command().arg(scope).output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{scope}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{scope}: {failure}");
        assert!(
            failure
                .to_string()
                .contains("intrinsic `unreachable` is unsupported"),
            "{scope}: {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn entry_conditions_outside_the_scalar_model_are_refused() {
    // Each selected body is otherwise admissible scalar MIR, so the refusal
    // must come from its entry condition rather than from body translation.
    let refused_cases: &[(&str, &[u8], &str)] = &[
        (
            "generic",
            b"pub fn selected<T>(value: u64) -> u64 { value }\n",
            "generic functions require quantified instantiation obligations",
        ),
        (
            "extern_c",
            b"pub extern \"C\" fn selected(value: u64) -> u64 { value }\n",
            "only non-variadic Rust ABI functions are admitted",
        ),
        (
            "c_variadic",
            b"#![feature(c_variadic)]\n\
              pub unsafe extern \"C\" fn selected(value: i32, mut args: ...) -> i32 { value }\n",
            "only non-variadic Rust ABI functions are admitted",
        ),
        (
            "target_feature",
            b"#[target_feature(enable = \"avx2\")]\n\
              pub fn selected(value: u64) -> u64 { value }\n",
            "target-feature entry obligations are unsupported",
        ),
    ];
    for (name, source, expected) in refused_cases {
        let fixture = Capture::new(source);
        let output = fixture.selected_command().output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure.to_string().contains(expected),
            "{name}: expected {expected:?}, got {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn unmodeled_codegen_attributes_are_refused_in_selected_and_crate_scope() {
    // Linked calls need not execute a weak or available_externally body, and
    // symbol or section attributes carry link-time obligations that the
    // captured safety bit does not record. Each body is the admissible scalar
    // identity below, and each source compiles through object emission, so
    // the refusal must come from the attribute itself.
    const BODY: &str = "pub fn selected(value: u64) -> u64 { value }\n";
    let refused_cases: &[(&str, &str, &str)] = &[
        (
            "linkage_weak",
            "#![feature(linkage)]\n#[linkage = \"weak\"]\n",
            "linkage attribute WeakAny is unsupported",
        ),
        (
            "linkage_available_externally",
            "#![feature(linkage)]\n#[linkage = \"available_externally\"]\n",
            "linkage attribute AvailableExternally is unsupported",
        ),
        (
            "no_mangle",
            "#[unsafe(no_mangle)]\n",
            "codegen attribute flags NO_MANGLE are unsupported",
        ),
        (
            "export_name",
            "#[unsafe(export_name = \"custom_symbol\")]\n",
            "exported symbol name `custom_symbol` is unsupported",
        ),
        (
            "link_section",
            "#[unsafe(link_section = \".text.custom\")]\n",
            "link section `.text.custom` is unsupported",
        ),
        (
            "track_caller",
            "#[track_caller]\n",
            "codegen attribute flags TRACK_CALLER are unsupported",
        ),
    ];
    for (name, attributes, expected) in refused_cases {
        for scope in ["--select=selected", "--scope=crate"] {
            let fixture = Capture::new(format!("{attributes}{BODY}").as_bytes());
            let output = fixture.command().arg(scope).output().unwrap();
            assert_eq!(output.status.code(), Some(1), "{name} {scope}: {output:?}");
            let failure = status(&output);
            assert_eq!(
                failure["status"], "unsupported",
                "{name} {scope}: {failure}"
            );
            assert!(
                failure.to_string().contains(expected),
                "{name} {scope}: expected {expected:?}, got {failure}"
            );
            fixture.assert_no_capture_artifacts();
        }
    }

    // The same body is captured with no attribute and with hints that leave
    // its meaning unchanged, so each refusal above is specific to its
    // attribute rather than to the body or the scope.
    for attributes in ["", "#[inline(always)]\n#[cold]\n"] {
        for scope in ["--select=selected", "--scope=crate"] {
            let fixture = Capture::new(format!("{attributes}{BODY}").as_bytes());
            let output = fixture.command().arg(scope).output().unwrap();
            assert!(
                output.status.success(),
                "{attributes:?} {scope}: {output:?}"
            );
            let manifest = fixture.manifest();
            assert_eq!(
                manifest["selected"][0]["path"], "selected",
                "{attributes:?} {scope}: {manifest}"
            );
        }
    }
}

#[test]
fn drop_guard_struct_remains_refused_while_cleanup_blocks_are_modeled() {
    // Tier 2 admits structs and cleanup blocks (`BasicBlock.cleanup = true`)
    // and `UnwindResume`, while `Drop` terminators remain refused.
    let source = b"pub struct Guard;\n\
        impl Drop for Guard { fn drop(&mut self) {} }\n\
        pub fn callee() {}\n\
        pub fn selected() { let _guard = Guard; callee(); }\n";
    let fixture = Capture::new(source);
    let output = fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(
        failure.to_string().contains("unsupported terminator: drop"),
        "{failure}"
    );
    fixture.assert_no_capture_artifacts();
}

#[test]
fn environment_reads_are_refused_even_when_the_variable_is_absent() {
    // Reading an absent variable is still an input: setting it later would
    // change the expansion without changing any declared source byte.
    const VARIABLE: &str = "ANNEAL_CAPTURE_TEST_ENV";
    let cases: &[(&str, &[u8], Option<&str>)] = &[
        (
            "option_env_absent",
            b"pub const INPUT: Option<&str> = option_env!(\"ANNEAL_CAPTURE_TEST_ENV\");\n\
              pub fn selected() -> u64 { 0 }\n",
            None,
        ),
        (
            "env_present",
            b"pub const INPUT: &str = env!(\"ANNEAL_CAPTURE_TEST_ENV\");\n\
              pub fn selected() -> u64 { 0 }\n",
            Some("present"),
        ),
    ];
    for (name, source, value) in cases {
        let fixture = Capture::new(source);
        let mut command = fixture.selected_command();
        match value {
            Some(value) => command.env(VARIABLE, value),
            None => command.env_remove(VARIABLE),
        };
        let output = command.output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure
                .to_string()
                .contains("environment-dependent source inputs are unsupported"),
            "{name}: {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn enum_ids_survive_unrelated_item_insertion() {
    // `EnumTy.id` enters Lean type equality, and reviewed specifications can
    // name it as a literal. Inserting items before the enum moves its compiler
    // index, which the census exposes, but must not move the captured key.
    const ENUM_AND_SELECTED: &str = "pub enum E { A, B }\n\
        pub fn selected(x: E) -> u8 { match x { E::A => 0, E::B => 1 } }\n";
    let capture_ids = |source: &str| {
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.selected_command().output().unwrap();
        assert!(output.status.success(), "{output:?}");
        let manifest = fixture.manifest();
        let census_index = manifest["census"]
            .as_array()
            .unwrap()
            .iter()
            .find(|item| item["path"] == "E")
            .expect("the enum is inventoried")["def_id"]
            .as_u64()
            .unwrap();
        let ty = &manifest["program"]["bodies"][0]["local_tys"][1];
        assert_eq!(ty["kind"], "enum", "{ty}");
        (ty["id"].as_u64().unwrap(), census_index)
    };
    let (before, before_index) = capture_ids(ENUM_AND_SELECTED);
    let inserted = format!(
        "pub enum Inserted {{ X }}\npub struct Other;\npub fn other() {{}}\n{ENUM_AND_SELECTED}"
    );
    let (after, after_index) = capture_ids(inserted.as_str());
    assert_ne!(
        before_index, after_index,
        "the insertion must move the DefIndex"
    );
    assert_eq!(before, after);
    // Pin the documented scheme: the first four digest bytes, big-endian.
    let digest = Sha256::digest(b"anneal:enum:v1:rust-path-v1::E");
    let expected = u32::from_be_bytes([digest[0], digest[1], digest[2], digest[3]]);
    assert_eq!(before, u64::from(expected));
}

#[test]
fn enum_id_collisions_between_distinct_local_enums_are_refused() {
    // Same-named enums in sibling blocks print the same semantic path, so
    // their keys collide although they are distinct types. The refusal covers
    // every local enum, whether or not a captured body uses it.
    let source = b"pub fn selected() -> u64 {\n\
            { enum E { A } }\n\
            { enum E { B } }\n\
            0\n\
        }\n";
    for scope in ["--select=selected", "--scope=crate"] {
        let fixture = Capture::new(source);
        let output = fixture.command().arg(scope).output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{scope}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{scope}: {failure}");
        assert!(
            failure.to_string().contains("enum identity collision"),
            "{scope}: {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn pre_capture_identity_check_rejects_missing_or_mismatched_sysroot_as_tool_failed() {
    let fixture = Capture::new(b"pub fn selected(x: u64) -> u64 { x }\n");
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .current_dir(fixture.directory.path())
        .arg("capture")
        .arg("--crate-root")
        .arg(&fixture.source)
        .arg("--crate-name=session")
        .arg("--target=x86_64-unknown-linux-gnu")
        .arg("--out-dir")
        .arg(&fixture.output)
        .arg("--select=selected")
        .arg("--source-file")
        .arg(&fixture.source)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    fixture.assert_no_capture_artifacts();

    #[cfg(unix)]
    {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let real_sysroot = sysroot();
        let fake_sysroot = fixture.directory.path().join("fake-sysroot");
        std::fs::create_dir_all(fake_sysroot.join("bin")).unwrap();
        std::fs::create_dir_all(fake_sysroot.join("lib")).unwrap();
        symlink(
            real_sysroot.join("lib/rustlib"),
            fake_sysroot.join("lib/rustlib"),
        )
        .unwrap();
        let fake_rustc = fake_sysroot.join("bin/rustc");
        std::fs::write(
            &fake_rustc,
            "#!/bin/sh\n\
             printf 'rustc 1.98.0-nightly (f8a08b688 2026-05-30)\\n'\n\
             printf 'binary: rustc\\n'\n\
             printf 'commit-hash: 0000000000000000000000000000000000000000\\n'\n\
             printf 'host: x86_64-unknown-linux-gnu\\n'\n",
        )
        .unwrap();
        std::fs::set_permissions(&fake_rustc, std::fs::Permissions::from_mode(0o755)).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
            .current_dir(fixture.directory.path())
            .arg("capture")
            .arg("--crate-root")
            .arg(&fixture.source)
            .arg("--crate-name=session")
            .arg("--target=x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&fixture.output)
            .arg("--sysroot")
            .arg(&fake_sysroot)
            .arg("--select=selected")
            .arg("--source-file")
            .arg(&fixture.source)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        fixture.assert_no_capture_artifacts();
    }
}

#[cfg(target_os = "linux")]
#[test]
fn linux_residency_accepts_symlinked_sysroot_and_rejects_mismatched_driver_inode() {
    use std::os::unix::fs::symlink;

    let real_sysroot = sysroot();
    let fixture = Capture::new(b"pub fn selected(x: u64) -> u64 { x }\n");
    let link_sysroot = fixture.directory.path().join("symlinked-sysroot");
    std::fs::create_dir_all(link_sysroot.join("bin")).unwrap();
    std::fs::create_dir_all(link_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();
    symlink(
        real_sysroot.join("bin/rustc"),
        link_sysroot.join("bin/rustc"),
    )
    .unwrap();
    for entry in std::fs::read_dir(real_sysroot.join("lib")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name() == "rustlib" {
            continue;
        }
        symlink(
            entry.path(),
            link_sysroot.join("lib").join(entry.file_name()),
        )
        .unwrap();
    }
    for entry in
        std::fs::read_dir(real_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap()
    {
        let entry = entry.unwrap();
        symlink(
            entry.path(),
            link_sysroot
                .join("lib/rustlib/x86_64-unknown-linux-gnu/lib")
                .join(entry.file_name()),
        )
        .unwrap();
    }

    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .current_dir(fixture.directory.path())
        .arg("capture")
        .arg("--crate-root")
        .arg(&fixture.source)
        .arg("--crate-name=session")
        .arg("--target=x86_64-unknown-linux-gnu")
        .arg("--out-dir")
        .arg(&fixture.output)
        .arg("--sysroot")
        .arg(&link_sysroot)
        .arg("--select=selected")
        .arg("--source-file")
        .arg(&fixture.source)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(fixture.manifest()["schema_version"], 5);

    // Replacing the driver symlink with a distinct regular file inode must fail
    // closed.
    let bad_sysroot = fixture.directory.path().join("bad-driver-sysroot");
    std::fs::create_dir_all(bad_sysroot.join("bin")).unwrap();
    std::fs::create_dir_all(bad_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();
    symlink(
        real_sysroot.join("bin/rustc"),
        bad_sysroot.join("bin/rustc"),
    )
    .unwrap();
    for entry in
        std::fs::read_dir(real_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap()
    {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if let Some(name_str) = name.to_str()
            && name_str.starts_with("librustc_driver-")
            && name_str.ends_with(".so")
        {
            continue;
        }
        symlink(
            entry.path(),
            bad_sysroot
                .join("lib/rustlib/x86_64-unknown-linux-gnu/lib")
                .join(name),
        )
        .unwrap();
    }
    std::fs::write(
        bad_sysroot.join("lib/librustc_driver-0000000000000000.so"),
        b"not the loaded driver",
    )
    .unwrap();
    let bad_output_dir = fixture.directory.path().join("bad-output");
    let bad_output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture"))
        .current_dir(fixture.directory.path())
        .arg("capture")
        .arg("--crate-root")
        .arg(&fixture.source)
        .arg("--crate-name=session")
        .arg("--target=x86_64-unknown-linux-gnu")
        .arg("--out-dir")
        .arg(&bad_output_dir)
        .arg("--sysroot")
        .arg(&bad_sysroot)
        .arg("--select=selected")
        .arg("--source-file")
        .arg(&fixture.source)
        .output()
        .unwrap();
    assert_eq!(bad_output.status.code(), Some(1), "{bad_output:?}");
    assert_eq!(
        status(&bad_output)["status"],
        "tool_failed",
        "{bad_output:?}"
    );
    assert!(!bad_output_dir.exists());
}

#[test]
fn sysroot_only_gate_admits_no_std_core_and_refuses_proc_macro_and_extern_crates() {
    let no_std_fixture = Capture::new(b"#![no_std]\npub fn selected(x: u64) -> u64 { x }\n");
    let output = no_std_fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(no_std_fixture.manifest()["schema_version"], 5);

    let proc_macro_fixture = Capture::new(
        b"#![crate_type = \"proc-macro\"]\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let output = proc_macro_fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_ne!(status(&output)["status"], "captured", "{output:?}");
    proc_macro_fixture.assert_no_capture_artifacts();

    let extern_proc_macro_fixture = Capture::new(
        b"extern crate proc_macro;\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let output = extern_proc_macro_fixture
        .selected_command()
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_ne!(status(&output)["status"], "captured", "{output:?}");
    extern_proc_macro_fixture.assert_no_capture_artifacts();

    let extern_crate_fixture = Capture::new(
        b"extern crate nonexistent_external_dep;\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let output = extern_crate_fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
    extern_crate_fixture.assert_no_capture_artifacts();

    // `#![feature(rustc_private)]` and `#![cfg_attr(..., crate_type = ...)]`
    // must be rejected before macro expansion so sysroot `rustc-dev` proc
    // macros can never load or run.
    for pre_expansion_src in [
        b"#![feature(rustc_private)]\n\
          extern crate rustc_macros;\n\
          pub fn selected(x: u64) -> u64 { x }\n"
            .as_slice(),
        b"#![cfg_attr(all(), feature(rustc_private))]\n\
          extern crate rustc_macros;\n\
          pub fn selected(x: u64) -> u64 { x }\n"
            .as_slice(),
        b"#![cfg_attr(all(), crate_type = \"proc-macro\")]\n\
          pub fn selected(x: u64) -> u64 { x }\n"
            .as_slice(),
    ] {
        let fixture = Capture::new(pre_expansion_src);
        let output = fixture.selected_command().output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert_eq!(status(&output)["status"], "unsupported", "{output:?}");
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn tier1_ops_casts_u128_and_overflow_check_modes_capture_cleanly() {
    let source = b"\
        pub const fn div_ceil_usize(a: usize, b: usize) -> usize {\n\
            if a == 0 { 0 } else { (a - 1) / b + 1 }\n\
        }\n\
        pub fn ops_and_casts(x: i32, y: u8, flag: bool, wide: u128) -> (i32, u64, u128) {\n\
            let neg = -x;\n\
            let inv = !neg;\n\
            let rem = inv % 3;\n\
            let widened = (y as u64) + (flag as u64);\n\
            let sum128 = wide + 0x1_0000_0000_0000_0001_u128;\n\
            (rem, widened, sum128)\n\
        }\n";

    // Default `-Coverflow-checks=no`: `div_ceil_usize` keeps non-optional
    // `DivisionByZero` assert and emits no optional overflow asserts.
    let off = Capture::new(source);
    let output = off
        .command()
        .args(["--select=div_ceil_usize", "--select=ops_and_casts"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest_off = off.manifest();
    assert_eq!(manifest_off["configuration"]["overflow_checks"], false);
    let lean_off = std::fs::read_to_string(off.output.join("Captured.lean")).unwrap();
    assert!(
        lean_off.contains("Trusted.MirAst.AssertKind.divByZero"),
        "{lean_off}"
    );
    assert!(
        lean_off.contains("Trusted.MirAst.AssertKind.remByZero"),
        "{lean_off}"
    );
    assert!(lean_off.contains("Trusted.MirAst.UnOp.neg"), "{lean_off}");
    assert!(lean_off.contains("Trusted.MirAst.UnOp.not"), "{lean_off}");
    assert!(lean_off.contains("Trusted.MirAst.BinOp.div"), "{lean_off}");
    assert!(lean_off.contains("Trusted.MirAst.BinOp.rem"), "{lean_off}");
    assert!(
        lean_off.contains("Trusted.MirAst.CastKind.intToInt"),
        "{lean_off}"
    );
    assert!(
        lean_off.contains("Trusted.MirAst.IntWidth.i128"),
        "{lean_off}"
    );
    assert!(lean_off.contains("18446744073709551617"), "{lean_off}");

    // `--overflow-checks`: `-Coverflow-checks=yes` emits `*WithOverflow` and
    // optional overflow `Assert`s, which capture admits cleanly.
    let on = Capture::new(source);
    let output = on
        .command()
        .args(["--select=div_ceil_usize", "--overflow-checks"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest_on = on.manifest();
    assert_eq!(manifest_on["configuration"]["overflow_checks"], true);
    let lean_on = std::fs::read_to_string(on.output.join("Captured.lean")).unwrap();
    assert!(
        lean_on.contains("Trusted.MirAst.BinOp.subWithOverflow"),
        "{lean_on}"
    );
    assert!(
        lean_on.contains("Trusted.MirAst.BinOp.addWithOverflow"),
        "{lean_on}"
    );
    assert!(
        lean_on.contains("(Trusted.MirAst.AssertKind.overflow Trusted.MirAst.BinOp.sub)"),
        "{lean_on}"
    );
    assert!(
        lean_on.contains("(Trusted.MirAst.AssertKind.overflow Trusted.MirAst.BinOp.add)"),
        "{lean_on}"
    );
    assert!(
        lean_on.contains("Trusted.MirAst.AssertKind.divByZero"),
        "{lean_on}"
    );
}

#[test]
fn transitive_crate_local_call_closure_and_call_refusals() {
    let source = b"\
        pub struct UnusedStruct(pub u64);\n\
        pub fn unused_bad(s: UnusedStruct) -> u64 { s.0 }\n\
        fn leaf(x: u32) -> u32 { x + 1 }\n\
        fn middle(x: u32) -> u32 { leaf(x) + leaf(x) }\n\
        pub fn selected(x: u32) -> u32 { middle(x) }\n";
    let fixture = Capture::new(source);
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let selected = manifest["selected"].as_array().expect("selected");
    assert_eq!(selected.len(), 3, "{selected:?}");
    assert_eq!(selected[0]["path"], "selected");
    assert_eq!(selected[0]["body_index"], 0);
    assert_eq!(selected[1]["path"], "middle");
    assert_eq!(selected[1]["body_index"], 1);
    assert_eq!(selected[2]["path"], "leaf");
    assert_eq!(selected[2]["body_index"], 2);
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(
        lean.contains("(Trusted.MirAst.TerminatorKind.call 1 "),
        "{lean}"
    );
    assert!(
        lean.contains("(Trusted.MirAst.TerminatorKind.call 2 "),
        "{lean}"
    );

    // Indirect, generic local, and unrecognized external `core` calls refuse.
    let refused_calls: &[(&str, &[u8], &str)] = &[
        (
            "indirect_fn_ptr",
            b"pub fn selected(f: fn(u32) -> u32, x: u32) -> u32 { f(x) }\n",
            "unsupported type",
        ),
        (
            "generic_local_call",
            b"fn id<T>(x: T) -> T { x }\npub fn selected(x: u32) -> u32 { id::<u32>(x) }\n",
            "generic crate-local call is unsupported",
        ),
        (
            "unrecognized_core_call",
            b"pub fn selected(x: u32) -> u32 { core::hint::black_box(x) }\n",
            "unsupported external `core` call",
        ),
        (
            "cmp_min_non_integer",
            b"pub fn selected(a: bool, b: bool) -> bool { core::cmp::min(a, b) }\n",
            "only admitted for integer types",
        ),
        (
            "float_cast",
            b"pub fn selected(x: u32) -> f32 { x as f32 }\n",
            "unsupported type",
        ),
    ];
    for (name, bad_src, expected) in refused_calls {
        let bad = Capture::new(bad_src);
        let out = bad.selected_command().output().unwrap();
        assert_eq!(out.status.code(), Some(1), "{name}: {out:?}");
        let failure = status(&out);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure.to_string().contains(expected),
            "{name}: expected {expected:?}, got {failure}"
        );
        bad.assert_no_capture_artifacts();
    }
}

#[test]
fn all_fifteen_core_builtins_capture_in_std_and_no_std() {
    let body = "\
        pub fn selected(a: u32, b: u32, s: u32, x: i64, y: i64) -> (u32, i64, bool) {\n\
            let w1 = a.wrapping_add(b);\n\
            let w2 = w1.wrapping_sub(b);\n\
            let w3 = w2.wrapping_mul(b);\n\
            let w4 = w3.wrapping_shl(s);\n\
            let w5 = w4.wrapping_shr(s);\n\
            let (o1, f1) = w5.overflowing_add(b);\n\
            let (o2, f2) = o1.overflowing_sub(b);\n\
            let (o3, f3) = o2.overflowing_mul(b);\n\
            let s1 = o3.saturating_add(b);\n\
            let s2 = s1.saturating_sub(b);\n\
            let lz = s2.leading_zeros();\n\
            let tz = s2.trailing_zeros();\n\
            let mult = a.is_multiple_of(b);\n\
            let mn = core::cmp::min(lz, tz);\n\
            let mx = core::cmp::max(x, y);\n\
            (mn, mx, f1 ^ f2 ^ f3 ^ mult)\n\
        }\n";
    for (label, prefix) in [("std", ""), ("no_std", "#![no_std]\n")] {
        let src = format!("{prefix}{body}");
        let fixture = Capture::new(src.as_bytes());
        let output = fixture.selected_command().output().unwrap();
        assert!(output.status.success(), "{label}: {output:?}");
        let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
        for builtin in [
            "wrappingAdd",
            "wrappingSub",
            "wrappingMul",
            "wrappingShl",
            "wrappingShr",
            "overflowingAdd",
            "overflowingSub",
            "overflowingMul",
            "saturatingAdd",
            "saturatingSub",
            "leadingZeros",
            "trailingZeros",
            "isMultipleOf",
            "cmpMin",
            "cmpMax",
        ] {
            assert!(
                lean.contains(&format!("Trusted.MirAst.CoreBuiltin.{builtin}")),
                "{label}: missing CoreBuiltin.{builtin} in:\n{lean}"
            );
        }
        assert_eq!(fixture.manifest()["configuration"]["panic"], "unwind");
    }
}

#[test]
fn assert_refuses_no_std_and_crate_local_panic_handler() {
    let cases = [
        (
            "no_std_library_without_panic_handler",
            "#![no_std]\n\
             pub fn selected(a: u64, b: u64) -> u64 { a / b }\n",
            "panic asserts require sysroot `std` unwinding panic handler",
        ),
        (
            "no_std_with_crate_local_panic_handler",
            "#![no_std]\n\
             #[panic_handler]\n\
             fn my_panic(_: &core::panic::PanicInfo) -> ! { loop {} }\n\
             pub fn selected(a: u64, b: u64) -> u64 { a / b }\n",
            "must resolve to sysroot `std`",
        ),
    ];
    for (name, src, expected) in cases {
        let bad = Capture::new(src.as_bytes());
        let output = bad.selected_command().output().unwrap();
        assert!(!output.status.success(), "{name} must be refused");
        let failure: Value = serde_json::from_slice(&output.stdout).unwrap();
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        let reason = failure["unsupported"][0]["reason"].as_str().unwrap_or("");
        assert!(
            reason.contains(expected),
            "{name}: expected {expected:?}, got {failure}"
        );
        bad.assert_no_capture_artifacts();
    }
}

#[test]
fn tier2_structs_payload_enums_niche_arrays_and_builtins_capture_cleanly() {
    // Exercise structs, inherent impl methods, single-variant and multi-variant
    // payload enums (direct scalar tag and niche tag, including nested tuple
    // niches), fixed-size arrays, repeat rvalues, downcast/index/constant-index
    // projections, bounds checks in `#![no_std]`, and Tier 2 `core::num`
    // builtins (`checked_add`, `checked_sub`, `checked_mul`, `to_le_bytes`,
    // `from_le_bytes`), including the exact Starnix `U64Range` and Fuchsia
    // `make_identity` shapes.
    let source = b"\
        #![no_std]\n\
        pub struct U64Range {\n\
            pub min: u64,\n\
            pub max: u64,\n\
        }\n\
        impl U64Range {\n\
            pub fn max_range() -> Self {\n\
                Self { min: 0, max: u64::MAX }\n\
            }\n\
            pub fn add_range(self, rhs: Self) -> Self {\n\
                let (min, min_overflow) = self.min.overflowing_add(rhs.min);\n\
                let (max, max_overflow) = self.max.overflowing_add(rhs.max);\n\
                if min_overflow != max_overflow {\n\
                    Self::max_range()\n\
                } else {\n\
                    Self { min, max }\n\
                }\n\
            }\n\
            pub fn mul_range(self, rhs: Self) -> Self {\n\
                match (self.min.checked_mul(rhs.min), self.max.checked_mul(rhs.max)) {\n\
                    (Some(min), Some(max)) => Self { min, max },\n\
                    _ => Self::max_range(),\n\
                }\n\
            }\n\
        }\n\
        pub fn make_identity(length: u32, level: u64, offset: u64) -> [u8; 12] {\n\
            let [o0, o1, o2, o3, o4, o5, o6, o7] = (offset | level).to_le_bytes();\n\
            let [l0, l1, l2, l3] = length.to_le_bytes();\n\
            [o0, o1, o2, o3, o4, o5, o6, o7, l0, l1, l2, l3]\n\
        }\n\
        pub enum WrapSingle { Only(u64) }\n\
        pub fn tier2_kitchen_sink(\n\
            flag: Option<bool>,\n\
            nested: Option<(u64, bool)>,\n\
            res: Result<u64, u32>,\n\
            wrap: WrapSingle,\n\
            idx: usize,\n\
            a: u32,\n\
            b: u32,\n\
        ) -> (u64, [u8; 4]) {\n\
            let base = match flag {\n\
                Some(true) => 1,\n\
                Some(false) => 2,\n\
                None => 3,\n\
            };\n\
            let from_nested = match nested {\n\
                Some((v, true)) => v,\n\
                Some((v, false)) => v.wrapping_add(1),\n\
                None => 0,\n\
            };\n\
            let from_res = match res {\n\
                Ok(v) => v,\n\
                Err(e) => e as u64,\n\
            };\n\
            let WrapSingle::Only(w) = wrap;\n\
            let zeros = [0u8; 4];\n\
            let elem = zeros[idx] as u64;\n\
            let sum = a.checked_add(b);\n\
            let diff = a.checked_sub(b);\n\
            let bytes = match (sum, diff) {\n\
                (Some(s), Some(d)) => (s ^ d).to_le_bytes(),\n\
                _ => [1u8; 4],\n\
            };\n\
            let rt = u32::from_le_bytes(bytes) as u64;\n\
            (base ^ from_nested ^ from_res ^ w ^ elem ^ rt, bytes)\n\
        }\n";
    let fixture = Capture::new(source);
    let output = fixture
        .command()
        .args([
            "--select=U64Range::add_range",
            "--select=U64Range::mul_range",
            "--select=make_identity",
            "--select=tier2_kitchen_sink",
        ])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    assert_eq!(manifest["schema_version"], 5);
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    for needle in [
        "Trusted.MirAst.MirTy.adtStruct",
        "Trusted.MirAst.MirTy.enum",
        "Trusted.MirAst.MirTy.array",
        "Trusted.MirAst.EnumTagRepr.single",
        "Trusted.MirAst.EnumTagRepr.scalar",
        "Trusted.MirAst.EnumTagRepr.niche",
        "Trusted.MirAst.ProjectionElem.downcast",
        "Trusted.MirAst.ProjectionElem.index",
        "Trusted.MirAst.ProjectionElem.constantIndex",
        "Trusted.MirAst.AggregateKind.adtStruct",
        "Trusted.MirAst.AggregateKind.array",
        "Trusted.MirAst.Rvalue.repeat_",
        "Trusted.MirAst.AssertKind.boundsCheck",
        "Trusted.MirAst.CoreBuiltin.checkedAdd",
        "Trusted.MirAst.CoreBuiltin.checkedSub",
        "Trusted.MirAst.CoreBuiltin.checkedMul",
        "Trusted.MirAst.CoreBuiltin.toLeBytes",
        "Trusted.MirAst.CoreBuiltin.fromLeBytes",
    ] {
        assert!(
            lean.contains(needle),
            "expected {needle:?} in captured Lean:\n{lean}"
        );
    }

    // Whole-crate scope also admits non-generic structs + inherent impls.
    let whole_crate = Capture::new(
        b"#![no_std]\n\
          pub struct Pair { pub lo: u64, pub hi: u64 }\n\
          impl Pair {\n\
              pub fn make(lo: u64, hi: u64) -> Self { Self { lo, hi } }\n\
              pub fn swap(self) -> Self { Self::make(self.hi, self.lo) }\n\
          }\n",
    );
    let output = whole_crate.command().arg("--scope=crate").output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        whole_crate.manifest()["program"]["bodies"]
            .as_array()
            .unwrap()
            .len(),
        2
    );
}
