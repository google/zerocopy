// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Check explicit typed capture and its separation from raw compiler arguments.

// The packaged compiler has only its native standard library. The typed
// capture profile requires the x86-64 Linux standard library.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use std::{
    fmt::Write as _,
    path::{Path, PathBuf},
    process::{Command, Output},
};

use serde_json::Value;
use sha2::{Digest, Sha256};

fn sysroot() -> PathBuf {
    anneal_testkit::default_rust_sysroot().expect("resolve pinned compiler sysroot")
}

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
        Self { directory, source: source_path, output }
    }

    fn command(&self) -> Command {
        self.command_with("session", true)
    }

    fn command_with(&self, crate_name: &str, declare_source: bool) -> Command {
        self.command_in(&sysroot(), crate_name, declare_source)
    }

    fn command_in(&self, sysroot: &Path, crate_name: &str, declare_source: bool) -> Command {
        let mut command = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"));
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
            .arg(sysroot);
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

    fn lean_source(&self) -> String {
        std::fs::read_to_string(self.output.join("Captured.lean")).expect("read Captured.lean")
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
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
        .output()
        .expect("run capture without arguments");
    assert!(output.status.success(), "{output:?}");
    assert!(stdout(&output).contains("Usage:"), "{output:?}");
    assert!(stdout(&output).contains("capture"), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
}

#[test]
fn explicit_capture_requires_typed_arguments_and_has_its_own_help() {
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
        .arg("capture")
        .output()
        .expect("run capture without typed arguments");
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");

    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
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
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
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
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
        .args(["--crate-root", "input.rs"])
        .output()
        .expect("pass typed option to raw compiler mode");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(stderr(&output).contains("Unrecognized option"), "{output:?}");
    assert!(stderr(&output).contains("crate-root"), "{output:?}");
}

#[test]
fn selected_capture_keeps_unselected_unsupported_items_in_the_census() {
    let fixture = Capture::new(
        b"pub fn selected(value: u64) -> u64 { value }\n\
          pub fn unsupported(value: f64) -> f64 { value }\n",
    );
    let output = fixture.selected_command().output().expect("capture selected supported function");
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
    let output = fixture.selected_command().output().expect("capture CRLF source input");
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
        let output =
            fixture.selected_command().output().expect("run typed capture with compiler errors");
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
    use std::os::unix::{ffi::OsStringExt, process::CommandExt};

    let fixture = Capture::new(b"pub fn selected() {}\n");
    let output = fixture
        .selected_command()
        .arg0(std::ffi::OsString::from_vec(vec![0xff]))
        .env_remove("RUST_BACKTRACE")
        .output()
        .expect("run typed capture with non-UTF-8 program name");
    assert!(!output.status.success(), "{output:?}");
    assert!(stderr(&output).contains("compiler program name is not UTF-8"), "{output:?}");
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
    assert!(status(&output)["diagnostics"].to_string().contains("--source-file"));
    fixture.assert_no_capture_artifacts();

    let output = fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    // An undeclared ordinary module is absent to module resolution. Explicit
    // include reads are checked separately below so refusal remains required
    // even when rustc can recover from the loader's I/O error.
    assert_eq!(status(&output)["status"], "compiler_failed", "{output:?}");
    assert!(stderr(&output).contains("file not found for module"), "{output:?}");
    fixture.assert_no_capture_artifacts();

    let output = fixture.selected_command().arg("--source-file").arg(side).output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(fixture.manifest()["source_files"].as_array().unwrap().len(), 2);
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
        assert!(stdout(&output).contains("new output directory"), "{output:?}");
        fixture.assert_no_capture_artifacts();
        assert_eq!(std::fs::read_dir(&fixture.output).unwrap().count(), usize::from(populated));
        if populated {
            assert_eq!(std::fs::read(fixture.output.join("caller-data")).unwrap(), b"preserve");
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
    assert!(stdout(&output).contains("new output directory"), "{output:?}");
    assert_eq!(std::fs::read(target.join("caller-data")).unwrap(), b"preserve");
    assert_eq!(std::fs::read_dir(target).unwrap().count(), 1);
    assert!(std::fs::symlink_metadata(&fixture.output).unwrap().file_type().is_symlink());
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
    assert_eq!(manifest["program"]["bodies"][0]["identity"], "rust-path-v1::café");
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
                    manifest["program"]["bodies"][index]["identity"].as_str().unwrap().to_owned(),
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
        let output = fixture.selected_command().arg(format!("--cfg={cfg}")).output().unwrap();
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
    let output = fixture.selected_command().arg("--source-file").arg(&side).output().unwrap();
    assert!(output.status.success(), "initial declared module: {output:?}");
    let expected = capture_pair(&fixture);

    std::fs::create_dir(secondary.parent().unwrap()).unwrap();
    std::fs::write(&secondary, "pub fn ambient() {}\n").unwrap();
    fixture.output = fixture.directory.path().join("with-ambient-file");
    let output = fixture.selected_command().arg("--source-file").arg(&side).output().unwrap();
    assert!(output.status.success(), "undeclared alternative changed compilation: {output:?}");
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
    let output = fixture.selected_command().arg("--source-file").arg(&secondary).output().unwrap();
    assert!(output.status.success(), "declared secondary module: {output:?}");
    assert_eq!(fixture.manifest()["source_files"].as_array().unwrap().len(), 2);

    #[cfg(unix)]
    {
        // Target membership alone would expose this unlisted alias and restore
        // the same hidden ambiguity, despite the target's declared bytes.
        std::fs::remove_file(&secondary).unwrap();
        std::os::unix::fs::symlink(&side, &secondary).unwrap();
        fixture.output = fixture.directory.path().join("with-ambient-alias");
        let output = fixture.selected_command().arg("--source-file").arg(&side).output().unwrap();
        assert!(output.status.success(), "undeclared alias changed compilation: {output:?}");
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
    let output = fixture.selected_command().arg("--source-file").arg(&shared).output().unwrap();
    assert!(output.status.success(), "declared ancestor ../ path: {output:?}");

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
        fixture.output = fixture.directory.path().join(format!("missing-prefix-{present}"));
        let output = fixture.selected_command().arg("--source-file").arg(&shared).output().unwrap();
        assert!(!output.status.success(), "ambient prefix admitted: {output:?}");
        assert!(stdout(&output).contains("undeclared compiler read"), "{output:?}");
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
    assert!(output.status.success(), "declared text/binary include: {output:?}");
    let sources = fixture.manifest()["source_files"].as_array().unwrap().clone();
    for (path, bytes, kind) in [
        (&text, std::fs::read(&text).unwrap(), "binary"),
        (&binary, std::fs::read(&binary).unwrap(), "binary"),
    ] {
        let entry = sources.iter().find(|entry| entry["path"] == path.to_str().unwrap()).unwrap();
        assert_eq!(entry["sha256"], sha256_hex(&bytes));
        assert_eq!(entry["read_kind"], kind);
    }
    fixture.output = fixture.directory.path().join("undeclared-include");
    let output = fixture.selected_command().arg("--source-file").arg(&text).output().unwrap();
    assert_eq!(status(&output)["status"], "unsupported", "{output:?}");
    assert!(stdout(&output).contains("undeclared compiler read"), "{output:?}");
    fixture.assert_no_capture_artifacts();

    #[cfg(unix)]
    {
        let alias = fixture.directory.path().join("text-alias.txt");
        std::os::unix::fs::symlink(&text, &alias).unwrap();
        std::fs::write(&fixture.source,
            "const TEXT: &str = include_str!(\"text-alias.txt\");\npub fn selected() -> u64 { 0 }\n").unwrap();
        fixture.output = fixture.directory.path().join("undeclared-include-alias");
        let output = fixture.selected_command().arg("--source-file").arg(&text).output().unwrap();
        assert!(!output.status.success(), "undeclared read alias admitted: {output:?}");
        assert!(stdout(&output).contains("undeclared compiler read"), "{output:?}");
        fixture.assert_no_capture_artifacts();
    }
}

#[cfg(unix)]
#[test]
fn inputs_through_a_moving_symlink_capture_one_resolved_snapshot() {
    use std::os::unix::fs::symlink;

    // Two snapshots of a two-file crate that differ only in `sub.rs`, reached
    // through `current`, as with a symlink that is atomically retargeted.
    let mut fixture = Capture::new(b"");
    let base = fixture.directory.path().canonicalize().unwrap();
    for (snapshot, value) in [("snap_v1", 1), ("snap_v2", 2)] {
        let src = base.join(snapshot).join("src");
        std::fs::create_dir_all(&src).unwrap();
        std::fs::write(src.join("lib.rs"), "mod sub;\npub fn selected() -> u64 { sub::value() }\n")
            .unwrap();
        std::fs::write(src.join("sub.rs"), format!("pub fn value() -> u64 {{ {value} }}\n"))
            .unwrap();
    }
    let current = base.join("current");
    symlink("snap_v1", &current).unwrap();
    let path_str = |path: PathBuf| path.to_str().unwrap().to_owned();
    let v1_sub_sha = sha256_hex(&std::fs::read(base.join("snap_v1/src/sub.rs")).unwrap());
    let v2_sub_sha = sha256_hex(&std::fs::read(base.join("snap_v2/src/sub.rs")).unwrap());

    // `--crate-root` and `--source-file` name the same file through the link.
    // rustc receives the resolved crate root, so `mod sub;` resolves inside
    // the snapshot, and the manifest names only resolved paths.
    fixture.source = current.join("src/lib.rs");
    let sub = current.join("src/sub.rs");
    let output = fixture.selected_command().arg("--source-file").arg(&sub).output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let configuration = &manifest["configuration"];
    assert_eq!(configuration["crate_root"], path_str(base.join("snap_v1/src/lib.rs")));
    assert_eq!(
        configuration["declared_source_files"],
        serde_json::json!([
            path_str(base.join("snap_v1/src/lib.rs")),
            path_str(base.join("snap_v1/src/sub.rs")),
        ])
    );
    let sources = manifest["source_files"].as_array().unwrap();
    assert_eq!(sources.len(), 2, "{sources:?}");
    let sub_entry = sources
        .iter()
        .find(|entry| entry["path"] == path_str(base.join("snap_v1/src/sub.rs")))
        .unwrap();
    assert_eq!(sub_entry["sha256"], v1_sub_sha);

    // A `--source-root` reached through the same link resolves into the same
    // snapshot, so the crate root and sources normalize under it.
    fixture.output = base.join("output-source-root");
    let output = fixture
        .selected_command()
        .arg("--source-file")
        .arg(&sub)
        .arg("--source-root")
        .arg(&current)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(fixture.manifest()["configuration"]["crate_root"], "src/lib.rs");

    // Resolution happens once per invocation: after the link moves, the next
    // capture reads the new snapshot.
    symlink("snap_v2", base.join("next")).unwrap();
    std::fs::rename(base.join("next"), &current).unwrap();
    fixture.output = base.join("output-v2");
    let output = fixture.selected_command().arg("--source-file").arg(&sub).output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    assert_eq!(manifest["configuration"]["crate_root"], path_str(base.join("snap_v2/src/lib.rs")));
    let sources = manifest["source_files"].as_array().unwrap();
    let sub_entry = sources
        .iter()
        .find(|entry| entry["path"] == path_str(base.join("snap_v2/src/sub.rs")))
        .unwrap();
    assert_eq!(sub_entry["sha256"], v2_sub_sha);

    // An undeclared sibling module stays absent through the link.
    fixture.output = base.join("output-undeclared-sub");
    let output = fixture.selected_command().output().unwrap();
    assert!(!output.status.success(), "undeclared sibling admitted: {output:?}");
    fixture.assert_no_capture_artifacts();

    // A crate root that resolves outside the declared files fails before the
    // compiler runs. This is what a link that moved between resolving
    // `--crate-root` and resolving `--source-file` would produce, and also
    // covers an undeclared crate root and a directory crate root.
    for (name, crate_root) in
        [("other-snapshot", base.join("snap_v1/src/lib.rs")), ("directory", current.join("src"))]
    {
        fixture.source = crate_root.clone();
        fixture.output = base.join(format!("output-{name}"));
        let output = fixture
            .command_with("session", false)
            .arg("--select=selected")
            .arg("--source-file")
            .arg(current.join("src/lib.rs"))
            .arg("--source-file")
            .arg(&sub)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        assert_eq!(status(&output)["status"], "unsupported", "{name}: {output:?}");
        let expected = format!(
            "--crate-root is not a declared --source-file: {}",
            crate_root.canonicalize().unwrap().display()
        );
        assert!(stdout(&output).contains(&expected), "{name}: {output:?}");
        fixture.assert_no_capture_artifacts();
    }

    // A missing crate root fails during resolution.
    fixture.source = current.join("src/missing.rs");
    fixture.output = base.join("output-missing");
    let output = fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(status(&output)["status"], "tool_failed", "{output:?}");
    fixture.assert_no_capture_artifacts();
}

#[cfg(unix)]
#[test]
fn non_utf8_output_destinations_fail_before_publication_and_remain_retryable() {
    use std::{ffi::OsString, os::unix::ffi::OsStringExt};

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
            let output = fixture.selected_command().current_dir(&cwd).output().unwrap();
            assert_eq!(output.status.code(), Some(1), "{form}/{attempt}: {output:?}");
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
                !entry.unwrap().file_name().to_string_lossy().starts_with(".anneal-capture-")
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
    let output =
        fixture.command().args(["--select=safe_entry", "--select=unsafe_entry"]).output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let bodies = manifest["program"]["bodies"].as_array().unwrap();
    assert_eq!(bodies.len(), 2);
    for (identity, expected) in
        [("rust-path-v1::safe_entry", false), ("rust-path-v1::unsafe_entry", true)]
    {
        let body = bodies.iter().find(|body| body["identity"] == identity).unwrap();
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
            failure.to_string().contains("uninhabited zero-variant enums are unsupported"),
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
        failure.to_string().contains("captured program contains no executable bodies"),
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
    let output = fixture.selected_command().output().expect("capture signed repr(isize) enum");
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let discriminants = manifest["program"]["bodies"][0]["local_tys"][1]["discriminants"]
        .as_array()
        .expect("enum discriminants");
    let values: Vec<&str> =
        discriminants.iter().map(|v| v.as_str().expect("decimal string discriminant")).collect();
    assert_eq!(values, vec!["18446744073709551615", "0", "1"]);
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
    assert!(output.status.success(), "{output:?}");
    assert_eq!(ref_fixture.manifest()["program"]["mir_profile_version"], 2);
    let ref_lean = std::fs::read_to_string(ref_fixture.output.join("Captured.lean")).unwrap();
    assert!(ref_lean.contains("Trusted.MirAst.Rvalue.useRetag"), "{ref_lean}");

    let unsupported_ref = Capture::new(b"pub fn selected(x: &mut str) -> &mut str { x }\n");
    let output = unsupported_ref.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(status(&output)["status"], "unsupported", "{output:?}");
    unsupported_ref.assert_no_capture_artifacts();
}

#[test]
fn tuple_aggregate_empty() {
    let fixture = Capture::new(b"pub fn selected() -> () { let x = (); x }\n");
    let output = fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert_eq!(status(&output)["status"], "unsupported", "{output:?}");
    assert!(stdout(&output).contains("unsupported rvalue"), "{output:?}");
    fixture.assert_no_capture_artifacts();
}

#[test]
fn tuple_aggregate_non_empty() {
    let fixture = Capture::new(b"pub fn selected(x: u64) -> (u64, u64) { (x, x) }\n");
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(fixture.manifest()["program"]["mir_profile_version"], 2);
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("Trusted.MirAst.Rvalue.aggregateTuple"), "{lean}");
}

#[test]
fn whole_crate_admits_pure_anon_consts_and_refuses_unsafe_or_call_anon_consts() {
    // Implicit-discriminant fieldless enums and pure literal/negated-literal
    // explicit fieldless enum discriminants capture cleanly in crate scope.
    for (name, source) in [
        (
            "implicit_enums",
            b"pub enum E { A, B }\n\
              pub enum Single { Only }\n\
              pub fn tag(x: E) -> u8 { match x { E::A => 0, E::B => 1 } }\n\
              pub fn match_single(v: Single) -> u8 { match v { Single::Only => 1 } }\n"
                .as_slice(),
        ),
        (
            "explicit_u8_literal",
            b"#[repr(u8)]\n\
              pub enum ExplicitU8 { Ten = 10, Twenty = 20 }\n\
              pub fn tag(x: ExplicitU8) -> u8 {\n\
                  match x { ExplicitU8::Ten => 10, ExplicitU8::Twenty => 20 }\n\
              }\n"
            .as_slice(),
        ),
        (
            "explicit_negative_literal",
            b"pub enum NarrowSigned { Neg = -1, Pos = 1 }\n\
              pub fn read_discr(v: NarrowSigned) -> isize {\n\
                  match v { NarrowSigned::Neg => -1, NarrowSigned::Pos => 1 }\n\
              }\n"
            .as_slice(),
        ),
    ] {
        let fixture = Capture::new(source);
        let output = fixture.command().arg("--scope=crate").output().unwrap();
        assert!(output.status.success(), "{name}: {output:?}");
        let manifest = fixture.manifest();
        assert_eq!(manifest["schema_version"], 5, "{name}");
    }

    // Pure arithmetic array-length `AnonConst` (`2 + 2`) is admitted: simple
    // `[0u8; 2 + 2]` `.len()` bodies capture in crate scope, while an array of
    // references (`[&u8; 2 + 2]`) still fails closed on the unsupported element
    // type rather than on `AnonConst`.
    let array_ok_fixture =
        Capture::new(b"pub fn len_only() -> usize { let a = [0u8; 2 + 2]; a.len() }\n");
    let array_ok_out = array_ok_fixture.command().arg("--scope=crate").output().unwrap();
    assert!(array_ok_out.status.success(), "{array_ok_out:?}");

    let array_len_fixture = Capture::new(
        b"pub fn len_only<'a>(x: &'a u8) -> usize { let a = [x; 2 + 2]; a.len() }\n",
    );
    let array_len_out = array_len_fixture.command().arg("--scope=crate").output().unwrap();
    assert_eq!(array_len_out.status.code(), Some(1), "{array_len_out:?}");
    let array_len_failure = status(&array_len_out);
    assert_eq!(array_len_failure["status"], "unsupported", "{array_len_failure}");
    assert!(
        !array_len_failure.to_string().contains("AnonConst")
            && array_len_failure
                .to_string()
                .contains("outside the Profile v2 type fragment"),
        "{array_len_failure}"
    );
    array_len_fixture.assert_no_capture_artifacts();

    // Whole-crate scope continues to refuse `DefKind::AnonConst` items with
    // calls, `unsafe` blocks, external constants, or nested items fail-closed.
    let refused_anon_const_cases: &[(&str, &[u8])] = &[
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
            failure.to_string().contains("whole-crate obligation is unsupported: AnonConst"),
            "{name}: {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }

    // A payload enum with explicit discriminants must stay refused.
    let payload_enum = b"\
        #[repr(u8)]\n\
        pub enum WithPayload { A = 1, B(u8) = 2 }\n\
        pub fn ok() -> u8 { 0 }\n";
    let fixture = Capture::new(payload_enum);
    let output = fixture.command().arg("--scope=crate").output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(failure.to_string().contains("enum payloads are unsupported"), "{failure}");
    fixture.assert_no_capture_artifacts();
}

#[test]
fn selected_unit_captures_explicit_fieldless_enum_discriminants_and_refuses_adt_aggregates() {
    // Default-repr narrow signed enum (`discr = isize`, `tag = i8`): in
    // `selected_unit` scope, `rustc`'s evaluated discriminants record the
    // 64-bit two's-complement discriminant alongside the signed 8-bit tag.
    let default_narrow = b"\
        pub enum NarrowSigned { Neg = -1, Pos = 1 }\n\
        pub fn read_discr(v: NarrowSigned) -> isize {\n\
            match v { NarrowSigned::Neg => -1, NarrowSigned::Pos => 1 }\n\
        }\n";
    let fixture = Capture::new(default_narrow);
    let output = fixture.command().arg("--select=read_discr").output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    assert_eq!(manifest["schema_version"], 5);
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 1);
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("EnumTagRepr.scalar Trusted.MirAst.IntWidth.i8 true"), "{lean}");
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
    let output = fixture.command().arg("--select=read_discr").output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("EnumTagRepr.scalar Trusted.MirAst.IntWidth.i8 true"), "{lean}");
    assert!(lean.contains("[255, 1]"), "{lean}");

    // 1-variant ZST fieldless enum with explicit discriminant captures cleanly
    // in `selected_unit` scope with `EnumTagRepr.zeroSized`.
    let single_zst = b"\
        pub enum SingleExplicit { Only = 42 }\n\
        pub fn read_discr(v: SingleExplicit) -> isize {\n\
            match v { SingleExplicit::Only => 42 }\n\
        }\n";
    let fixture = Capture::new(single_zst);
    let output = fixture.command().arg("--select=read_discr").output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("EnumTagRepr.zeroSized"), "{lean}");
    assert!(lean.contains("[42]"), "{lean}");

    // Enum `AggregateKind::Adt` aggregates, including direct fieldless enum
    // construction, payload-enum unit variants, and non-local enums, must all
    // fail closed.
    let refused_cases: &[(&str, &[u8], &[&str], &str)] = &[
        (
            "direct_narrow_signed_aggregate",
            b"#[repr(i8)]\n\
              pub enum NarrowSigned { Neg = -1, Pos = 1 }\n\
              pub fn make() -> NarrowSigned { NarrowSigned::Neg }\n",
            &["--select=make"],
            "unsupported rvalue",
        ),
        (
            "direct_single_zst_aggregate",
            b"pub enum Single { Only }\n\
              pub fn make() -> Single { Single::Only }\n",
            &["--scope=crate"],
            "unsupported rvalue",
        ),
        (
            "payload_unit_variant",
            b"pub enum Payload { None, Some(u8) }\n\
              pub fn f() -> Payload { Payload::None }\n",
            &["--select=f"],
            "enum payloads are unsupported",
        ),
        (
            "ordering_adt_aggregate",
            b"pub fn f() -> core::cmp::Ordering { core::cmp::Ordering::Less }\n",
            &["--scope=crate"],
            "unsupported rvalue",
        ),
        (
            "non_local_enum",
            b"pub fn f(x: core::sync::atomic::Ordering) -> core::sync::atomic::Ordering { x }\n",
            &["--scope=crate"],
            "unsupported type",
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
    // On normal crates, `#![feature(intrinsics)]` is refused before macro
    // expansion by the closed positive feature allowlist.
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
            failure.to_string().contains("#![feature(intrinsics)] is unsupported"),
            "{scope}: {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }

    // Under `--stdlib-crate=core` (where `intrinsics` is in the pinned
    // allowlist), `extract::body` still refuses `#[rustc_intrinsic]` fallback
    // bodies directly: rustc lowers calls to `Unreachable`, so capturing the
    // benign loop fallback body would verify code no caller executes.
    let core_intrinsic = b"#![feature(no_core, lang_items, intrinsics)]\n\
        #![allow(internal_features)]\n\
        #![no_core]\n\
        #[lang = \"pointee_sized\"] pub trait PointeeSized {}\n\
        #[lang = \"meta_sized\"] pub trait MetaSized: PointeeSized {}\n\
        #[lang = \"sized\"] pub trait Sized: MetaSized {}\n\
        #[rustc_intrinsic]\n\
        pub unsafe fn unreachable() -> ! { loop {} }\n";
    let fixture = Capture::new(core_intrinsic);
    let output = fixture
        .command_with("core", true)
        .args(["--stdlib-crate=core", "--select=unreachable"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(failure.to_string().contains("intrinsic `unreachable` is unsupported"), "{failure}");
    fixture.assert_no_capture_artifacts();
}

#[test]
fn entry_conditions_outside_the_scalar_model_are_refused() {
    // Each selected body is otherwise admissible scalar MIR, so the refusal
    // must come from its entry condition (or the closed feature allowlist for
    // `c_variadic`, with `signature.c_variadic()` retained as defense in
    // depth).
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
            "#![feature(c_variadic)] is unsupported during capture",
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
    // captured safety bit does not record. `#[linkage]` additionally requires
    // `#![feature(linkage)]`, which the closed positive feature allowlist now
    // refuses first (while `extract::codegen_attrs` retains the `Linkage`
    // guard as defense in depth).
    const BODY: &str = "pub fn selected(value: u64) -> u64 { value }\n";
    let refused_cases: &[(&str, &str, &str)] = &[
        (
            "linkage_weak",
            "#![feature(linkage)]\n#[linkage = \"weak\"]\n",
            "#![feature(linkage)] is unsupported during capture",
        ),
        (
            "linkage_available_externally",
            "#![feature(linkage)]\n#[linkage = \"available_externally\"]\n",
            "#![feature(linkage)] is unsupported during capture",
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
    ];
    for (name, attributes, expected) in refused_cases {
        for scope in ["--select=selected", "--scope=crate"] {
            let fixture = Capture::new(format!("{attributes}{BODY}").as_bytes());
            let output = fixture.command().arg(scope).output().unwrap();
            assert_eq!(output.status.code(), Some(1), "{name} {scope}: {output:?}");
            let failure = status(&output);
            assert_eq!(failure["status"], "unsupported", "{name} {scope}: {failure}");
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
    for attributes in ["", "#[inline(always)]\n#[cold]\n#[track_caller]\n"] {
        for scope in ["--select=selected", "--scope=crate"] {
            let fixture = Capture::new(format!("{attributes}{BODY}").as_bytes());
            let output = fixture.command().arg(scope).output().unwrap();
            assert!(output.status.success(), "{attributes:?} {scope}: {output:?}");
            let manifest = fixture.manifest();
            assert_eq!(
                manifest["selected"][0]["path"], "selected",
                "{attributes:?} {scope}: {manifest}"
            );
        }
    }
}

#[test]
fn cleanup_blocks_are_refused_before_local_types() {
    // Capture passes no `-Cpanic`, so this target unwinds and the call to
    // `callee` keeps a cleanup edge that drops the guard. The guard's struct
    // type is unsupported as well; checking blocks first reports the cleanup.
    let source = b"pub struct Guard;\n\
        impl Drop for Guard { fn drop(&mut self) {} }\n\
        pub fn callee() {}\n\
        pub fn selected() { let _guard = Guard; callee(); }\n";
    let fixture = Capture::new(source);
    let output = fixture.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(failure.to_string().contains("cleanup block bb"), "{failure}");
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
            failure.to_string().contains("environment-dependent source inputs are unsupported"),
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
    assert_ne!(before_index, after_index, "the insertion must move the DefIndex");
    assert_eq!(before, after);
    // Pin the documented scheme: the first four digest bytes, big-endian.
    let digest = Sha256::digest(b"anneal:enum:v1:rust-path-v1::E");
    let expected = u32::from_be_bytes([digest[0], digest[1], digest[2], digest[3]]);
    assert_eq!(before, u64::from(expected));
}

#[test]
fn enum_id_collisions_between_distinct_local_enums_are_refused() {
    // Same-named enums in sibling blocks print the same semantic path, so
    // their keys collide although they are distinct types. Whole-crate scope
    // admits every local enum and refuses the collision even when no body uses
    // either enum; selected-unit scope refuses whenever a captured body
    // references the colliding enum.
    let unreferenced_source = b"pub fn selected() -> u64 {\n\
            { enum E { A } }\n\
            { enum E { B } }\n\
            0\n\
        }\n";
    let crate_fixture = Capture::new(unreferenced_source);
    let crate_output = crate_fixture.command().arg("--scope=crate").output().unwrap();
    assert_eq!(crate_output.status.code(), Some(1), "{crate_output:?}");
    let failure = status(&crate_output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(failure.to_string().contains("enum identity collision"), "{failure}");
    crate_fixture.assert_no_capture_artifacts();

    let referenced_source = b"pub fn outer() {\n\
            {\n\
                pub enum E { A, B }\n\
                pub fn selected(x: E) -> u8 { match x { E::A => 0, E::B => 1 } }\n\
            }\n\
            { enum E { C, D } }\n\
        }\n";
    for scope in ["--select=outer::selected", "--scope=crate"] {
        let fixture = Capture::new(referenced_source);
        let output = fixture.command().arg(scope).output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{scope}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{scope}: {failure}");
        assert!(failure.to_string().contains("enum identity collision"), "{scope}: {failure}");
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn enum_id_collisions_outside_selected_scope_do_not_block_capture() {
    // Macro-expanded `const _: () = { enum ... }` blocks and sibling-block
    // enums elsewhere in a crate share printed paths (`_::CastToWrapper`,
    // `other::E`). Selected-unit capture must ignore collisions that do not
    // enter any captured body while still admitting non-colliding enums used
    // by the selected function.
    let source = b"\
        macro_rules! dup_const_enum {\n\
            () => {\n\
                const _: () = {\n\
                    #[allow(dead_code)]\n\
                    enum CastToWrapper {}\n\
                };\n\
            };\n\
        }\n\
        dup_const_enum!();\n\
        dup_const_enum!();\n\
        #[allow(dead_code)]\n\
        pub fn other() -> u64 {\n\
            { enum E { A } }\n\
            { enum E { B } }\n\
            0\n\
        }\n\
        pub enum Good { X, Y }\n\
        pub fn selected(g: Good) -> u8 {\n\
            match g { Good::X => 1, Good::Y => 2 }\n\
        }\n";
    let fixture = Capture::new(source);
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    let ty = &manifest["program"]["bodies"][0]["local_tys"][1];
    assert_eq!(ty["kind"], "enum", "{ty}");
    let digest = Sha256::digest(b"anneal:enum:v1:rust-path-v1::Good");
    let expected = u32::from_be_bytes([digest[0], digest[1], digest[2], digest[3]]);
    assert_eq!(ty["id"].as_u64().unwrap(), u64::from(expected));
}

#[test]
fn identically_named_enums_in_distinct_modules_capture_with_distinct_ids() {
    let source = b"\
        pub mod a { pub enum E { A } }\n\
        pub mod b { pub enum E { B } }\n\
        pub fn selected(_x: a::E, _y: b::E) -> u8 { 0 }\n";
    for scope in ["--select=selected", "--scope=crate"] {
        let fixture = Capture::new(source);
        let output = fixture.command().arg(scope).output().unwrap();
        assert!(output.status.success(), "{scope}: {output:?}");
        let manifest = fixture.manifest();
        let ty_a = &manifest["program"]["bodies"][0]["local_tys"][1];
        let ty_b = &manifest["program"]["bodies"][0]["local_tys"][2];
        assert_eq!(ty_a["kind"], "enum", "{ty_a}");
        assert_eq!(ty_b["kind"], "enum", "{ty_b}");
        let id_a = ty_a["id"].as_u64().unwrap();
        let id_b = ty_b["id"].as_u64().unwrap();
        assert_ne!(id_a, id_b);
        let digest_a = Sha256::digest(b"anneal:enum:v1:rust-path-v1::a::E");
        let digest_b = Sha256::digest(b"anneal:enum:v1:rust-path-v1::b::E");
        assert_eq!(
            id_a,
            u64::from(u32::from_be_bytes([digest_a[0], digest_a[1], digest_a[2], digest_a[3],]))
        );
        assert_eq!(
            id_b,
            u64::from(u32::from_be_bytes([digest_b[0], digest_b[1], digest_b[2], digest_b[3],]))
        );
    }
}

#[test]
fn explicit_env_bindings_admit_env_macros_override_ambient_and_bind_manifest() {
    // Mirrors real-world crates using `#[doc = concat!(...,
    // env!("CARGO_PKG_VERSION"))]` alongside macro-expanded anonymous
    // `const _` blocks.
    let source = b"\
        macro_rules! dup_wrapper {\n\
            () => {\n\
                const _: () = {\n\
                    #[allow(dead_code)]\n\
                    enum CastToWrapper {}\n\
                };\n\
            };\n\
        }\n\
        dup_wrapper!();\n\
        dup_wrapper!();\n\
        #[doc = concat!(\"version \", env!(\"CARGO_PKG_VERSION\"))]\n\
        pub const TAG: Option<&str> = option_env!(\"ANNEAL_BUILD_TAG\");\n\
        pub fn selected(x: usize) -> usize { x }\n";

    // 1. Declared `--env` bindings admit both `env!` and `option_env!`,
    //    override conflicting ambient process environment values, and record
    //    a deterministically sorted `configuration.env` map.
    let fixture_a = Capture::new(source);
    let mut cmd_a = fixture_a.selected_command();
    cmd_a
        .arg("--env=CARGO_PKG_VERSION=0.8.64")
        .arg("--env=ANNEAL_BUILD_TAG=rc1")
        .env("CARGO_PKG_VERSION", "99.99.99-ambient")
        .env("ANNEAL_BUILD_TAG", "ambient-ignored");
    let out_a = cmd_a.output().unwrap();
    assert!(out_a.status.success(), "{out_a:?}");
    let manifest_a = fixture_a.manifest();
    assert_eq!(
        manifest_a["configuration"]["env"],
        serde_json::json!({
            "ANNEAL_BUILD_TAG": "rc1",
            "CARGO_PKG_VERSION": "0.8.64",
        })
    );
    let bytes_a = std::fs::read(fixture_a.output.join("capture.json")).unwrap();

    // 2. Changing an `--env` value changes the recorded `capture.json` digest.
    let fixture_b = Capture::new(source);
    let mut cmd_b = fixture_b.selected_command();
    cmd_b.arg("--env=ANNEAL_BUILD_TAG=rc1").arg("--env=CARGO_PKG_VERSION=0.8.65");
    let out_b = cmd_b.output().unwrap();
    assert!(out_b.status.success(), "{out_b:?}");
    let bytes_b = std::fs::read(fixture_b.output.join("capture.json")).unwrap();
    assert_ne!(Sha256::digest(&bytes_a), Sha256::digest(&bytes_b));

    // 3. Omitting a single accessed variable (`ANNEAL_BUILD_TAG`) still fails
    //    closed, even when `CARGO_PKG_VERSION` is declared.
    let partial = Capture::new(source);
    let mut cmd_partial = partial.selected_command();
    cmd_partial.arg("--env=CARGO_PKG_VERSION=0.8.64").env_remove("ANNEAL_BUILD_TAG");
    let out_partial = cmd_partial.output().unwrap();
    assert_eq!(out_partial.status.code(), Some(1), "{out_partial:?}");
    let failure = status(&out_partial);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(
        failure.to_string().contains("environment-dependent source inputs are unsupported")
            && failure.to_string().contains("ANNEAL_BUILD_TAG"),
        "{failure}"
    );
    partial.assert_no_capture_artifacts();

    // 4. Conflicting duplicate `--env` keys fail closed as `tool_failed`.
    let dup = Capture::new(source);
    let mut cmd_dup = dup.selected_command();
    cmd_dup
        .arg("--env=CARGO_PKG_VERSION=0.8.64")
        .arg("--env=CARGO_PKG_VERSION=0.8.65")
        .arg("--env=ANNEAL_BUILD_TAG=rc1");
    let out_dup = cmd_dup.output().unwrap();
    assert_eq!(out_dup.status.code(), Some(1), "{out_dup:?}");
    let failure = status(&out_dup);
    assert_eq!(failure["status"], "tool_failed", "{failure}");
    assert!(
        failure.to_string().contains("duplicate --env binding for CARGO_PKG_VERSION"),
        "{failure}"
    );
    dup.assert_no_capture_artifacts();
}

#[test]
fn pre_capture_identity_check_rejects_missing_or_mismatched_sysroot_as_tool_failed() {
    let fixture = Capture::new(b"pub fn selected(x: u64) -> u64 { x }\n");
    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
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
        symlink(real_sysroot.join("lib/rustlib"), fake_sysroot.join("lib/rustlib")).unwrap();
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
        let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
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
    symlink(real_sysroot.join("bin/rustc"), link_sysroot.join("bin/rustc")).unwrap();
    for entry in std::fs::read_dir(real_sysroot.join("lib")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name() == "rustlib" {
            continue;
        }
        symlink(entry.path(), link_sysroot.join("lib").join(entry.file_name())).unwrap();
    }
    for entry in
        std::fs::read_dir(real_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap()
    {
        let entry = entry.unwrap();
        symlink(
            entry.path(),
            link_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib").join(entry.file_name()),
        )
        .unwrap();
    }

    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
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
    symlink(real_sysroot.join("bin/rustc"), bad_sysroot.join("bin/rustc")).unwrap();
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
            bad_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib").join(name),
        )
        .unwrap();
    }
    std::fs::write(
        bad_sysroot.join("lib/librustc_driver-0000000000000000.so"),
        b"not the loaded driver",
    )
    .unwrap();
    let bad_output_dir = fixture.directory.path().join("bad-output");
    let bad_output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
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
    assert_eq!(status(&bad_output)["status"], "tool_failed", "{bad_output:?}");
    assert!(!bad_output_dir.exists());
}

#[cfg(target_os = "linux")]
#[test]
fn logical_symlinked_sysroot_preserves_path_and_rejects_mismatched_libllvm_and_loader_injection() {
    use std::os::unix::fs::symlink;

    let real_sysroot = sysroot();
    let fixture = Capture::new(b"pub fn selected(x: u64) -> u64 { x }\n");

    // 1. Virtual CAS-style symlink forest accessed through a top-level logical
    //    directory symlink, with a decoy `./lib/rustlib` in `AT_FDCWD`.
    //    Capture must succeed, preserve the logical sysroot path rather than
    //    canonicalizing it away, and never consult `./lib/rustlib`.
    let tree_sysroot = fixture.directory.path().join("cas-tree-sysroot");
    std::fs::create_dir_all(tree_sysroot.join("bin")).unwrap();
    std::fs::create_dir_all(tree_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();
    symlink(real_sysroot.join("bin/rustc"), tree_sysroot.join("bin/rustc")).unwrap();
    for entry in std::fs::read_dir(real_sysroot.join("lib")).unwrap() {
        let entry = entry.unwrap();
        if entry.file_name() == "rustlib" {
            continue;
        }
        symlink(entry.path(), tree_sysroot.join("lib").join(entry.file_name())).unwrap();
    }
    for entry in
        std::fs::read_dir(real_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap()
    {
        let entry = entry.unwrap();
        symlink(
            entry.path(),
            tree_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib").join(entry.file_name()),
        )
        .unwrap();
    }
    let logical_sysroot = fixture.directory.path().join("logical-sysroot-link");
    symlink(&tree_sysroot, &logical_sysroot).unwrap();

    // Plant a decoy `./lib/rustlib` inside `AT_FDCWD` to confirm explicit
    // `--sysroot` overrides `rustc`'s default relative lookup unconditionally.
    std::fs::create_dir_all(fixture.directory.path().join("lib/rustlib")).unwrap();
    std::fs::write(fixture.directory.path().join("lib/rustlib/decoy.rlib"), b"decoy").unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
        .current_dir(fixture.directory.path())
        .arg("capture")
        .arg("--crate-root")
        .arg(&fixture.source)
        .arg("--crate-name=session")
        .arg("--target=x86_64-unknown-linux-gnu")
        .arg("--out-dir")
        .arg(&fixture.output)
        .arg("--sysroot")
        .arg(&logical_sysroot)
        .arg("--select=selected")
        .arg("--source-file")
        .arg(&fixture.source)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "logical symlinked sysroot capture failed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = fixture.manifest();
    assert_eq!(
        manifest["compiler"]["sysroot"],
        logical_sysroot.to_str().unwrap(),
        "expected logical sysroot path to be preserved without canonicalization: {manifest}"
    );
    let is_sha256 = |val: &serde_json::Value| {
        val.as_str().is_some_and(|s| s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit()))
    };
    assert!(
        is_sha256(&manifest["compiler"]["rustc_sha256"]),
        "expected 64-hex rustc_sha256 in manifest: {manifest}"
    );
    let driver = &manifest["compiler"]["driver"];
    let linkage = driver["linkage"].as_str().unwrap();
    assert!(matches!(linkage, "dynamic_dso" | "static_exe"), "unexpected driver linkage: {driver}");
    assert!(
        is_sha256(&driver["driver_sha256"]),
        "expected 64-hex driver_sha256 in manifest: {driver}"
    );
    let dso_digests = driver["dso_digests"].as_object().unwrap();
    for (name, digest) in dso_digests {
        assert!(is_sha256(digest), "expected 64-hex digest for {name}: {driver}");
    }
    if linkage == "dynamic_dso" {
        assert!(
            dso_digests.iter().any(|(name, digest)| name.starts_with("librustc_driver-")
                && digest == &driver["driver_sha256"]),
            "expected dynamic driver digest recorded in dso_digests: {driver}"
        );
    }

    // 2. Replacing `libLLVM*` in the sysroot with a distinct file inode while
    //    keeping `librustc_driver-*.so` matching simulates a spliced mismatched
    //    `libLLVM.so` via `LD_LIBRARY_PATH` and must fail closed as `tool_failed`.
    //    Replace `libLLVM*` in both `lib/` and `lib/rustlib/<host>/lib/` because
    //    multi-component sysroots (such as those including `llvm-tools`) place a
    //    copy in both directories that deduplicating stores can hardlink to the
    //    same `(st_dev, st_ino)`.
    let bad_llvm_sysroot = fixture.directory.path().join("bad-llvm-sysroot");
    std::fs::create_dir_all(bad_llvm_sysroot.join("bin")).unwrap();
    std::fs::create_dir_all(bad_llvm_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib"))
        .unwrap();
    symlink(real_sysroot.join("bin/rustc"), bad_llvm_sysroot.join("bin/rustc")).unwrap();
    let mut replaced_llvm = false;
    for entry in std::fs::read_dir(real_sysroot.join("lib")).unwrap() {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if name == "rustlib" {
            continue;
        }
        if let Some(name_str) = name.to_str()
            && name_str.starts_with("libLLVM")
        {
            std::fs::write(bad_llvm_sysroot.join("lib").join(&name), b"mismatched-llvm").unwrap();
            replaced_llvm = true;
            continue;
        }
        symlink(entry.path(), bad_llvm_sysroot.join("lib").join(name)).unwrap();
    }
    for entry in
        std::fs::read_dir(real_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap()
    {
        let entry = entry.unwrap();
        let name = entry.file_name();
        if let Some(name_str) = name.to_str()
            && name_str.starts_with("libLLVM")
        {
            std::fs::write(
                bad_llvm_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib").join(&name),
                b"mismatched-llvm",
            )
            .unwrap();
            replaced_llvm = true;
            continue;
        }
        symlink(
            entry.path(),
            bad_llvm_sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib").join(name),
        )
        .unwrap();
    }
    if dso_digests.keys().any(|k| k.starts_with("libLLVM")) {
        assert!(
            replaced_llvm,
            "expected sysroot to contain libLLVM* when dynamic libLLVM is mapped"
        );
    }
    if replaced_llvm {
        let bad_llvm_out = fixture.directory.path().join("bad-llvm-out");
        let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
            .current_dir(fixture.directory.path())
            .arg("capture")
            .arg("--crate-root")
            .arg(&fixture.source)
            .arg("--crate-name=session")
            .arg("--target=x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&bad_llvm_out)
            .arg("--sysroot")
            .arg(&bad_llvm_sysroot)
            .arg("--select=selected")
            .arg("--source-file")
            .arg(&fixture.source)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "tool_failed", "{failure}");
        assert!(
            failure.to_string().contains("libLLVM")
                && failure.to_string().contains("does not match any library in sysroot"),
            "expected closed-world libLLVM residency rejection, got {failure}"
        );
        assert!(!bad_llvm_out.exists());
    }

    // 3. Ambient dynamic-linker injection variables must fail closed on
    //    presence (including empty-string values for presence-triggered flags)
    //    before entering the compiler session.
    for (idx, (var, val)) in
        [("LD_DYNAMIC_WEAK", "1"), ("LD_DYNAMIC_WEAK", ""), ("DYLD_FORCE_FLAT_NAMESPACE", "")]
            .into_iter()
            .enumerate()
    {
        let preload_out = fixture.directory.path().join(format!("preload-out-{idx}"));
        let output = Command::new(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))
            .current_dir(fixture.directory.path())
            .env(var, val)
            .arg("capture")
            .arg("--crate-root")
            .arg(&fixture.source)
            .arg("--crate-name=session")
            .arg("--target=x86_64-unknown-linux-gnu")
            .arg("--out-dir")
            .arg(&preload_out)
            .arg("--sysroot")
            .arg(&logical_sysroot)
            .arg("--select=selected")
            .arg("--source-file")
            .arg(&fixture.source)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{var}={val:?}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "tool_failed", "{var}={val:?}: {failure}");
        assert!(
            failure
                .to_string()
                .contains(&format!("forbidden dynamic linker environment variable is set: {var}")),
            "{var}={val:?}: {failure}"
        );
        assert!(!preload_out.exists());
    }
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
    let output = extern_proc_macro_fixture.selected_command().output().unwrap();
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

/// Compile `Captured.lean` against `Trusted.MirAst` with the pinned `lean`
/// executable under its default `maxRecDepth` whenever `../lean` is present in
/// the source tree (all local and CI workspace runs; inside Nix's isolated
/// `rustcCaptureSourceFiles` derivation `../lean` is intentionally absent).
fn compile_captured_lean_if_trusted_sources_present(captured_lean: &std::path::Path) -> bool {
    let lean_src_root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../trusted/lean");
    if !lean_src_root.join("Trusted/MirAst.lean").is_file() {
        return false;
    }
    let lean_bin = anneal_testkit::default_lean_path().expect("resolve pinned Lean executable");
    let stage = tempfile::tempdir().expect("create temporary Lean build directory");
    let lean_lib = stage.path().join("lib");
    std::fs::create_dir_all(lean_lib.join("Trusted/MirAst")).unwrap();

    for rel in [
        "Trusted/MirAst/Types",
        "Trusted/MirAst/Places",
        "Trusted/MirAst/Rvalues",
        "Trusted/MirAst/Statements",
        "Trusted/MirAst/Terminators",
        "Trusted/MirAst/Body",
        "Trusted/MirAst",
    ] {
        let src = lean_src_root.join(format!("{rel}.lean"));
        let olean = lean_lib.join(format!("{rel}.olean"));
        let out = Command::new(&lean_bin)
            .current_dir(&lean_src_root)
            .env("LEAN_PATH", &lean_lib)
            .arg("-DwarningAsError=true")
            .arg("-o")
            .arg(&olean)
            .arg(&src)
            .output()
            .expect("invoke pinned lean on Trusted.MirAst");
        assert!(
            out.status.success(),
            "failed compiling {}: {}\n{}",
            src.display(),
            stdout(&out),
            stderr(&out)
        );
    }

    let captured_dir = captured_lean.parent().expect("Captured.lean parent");
    let shard_dir = captured_dir.join("Captured");
    if shard_dir.is_dir() {
        let mut shards: Vec<_> = std::fs::read_dir(&shard_dir)
            .unwrap()
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.extension().is_some_and(|ext| ext == "lean"))
            .collect();
        shards.sort();
        std::fs::create_dir_all(lean_lib.join("Captured")).unwrap();
        for shard_src in shards {
            let stem = shard_src.file_stem().unwrap().to_str().unwrap();
            let shard_olean = lean_lib.join(format!("Captured/{stem}.olean"));
            let out = Command::new(&lean_bin)
                .current_dir(captured_dir)
                .env("LEAN_PATH", &lean_lib)
                .arg("-DwarningAsError=true")
                .arg("-o")
                .arg(&shard_olean)
                .arg(&shard_src)
                .output()
                .expect("invoke pinned lean on Captured shard");
            let combined = format!("{}{}", stdout(&out), stderr(&out));
            assert!(
                out.status.success(),
                "{} failed Lean compilation:\n{combined}",
                shard_src.display()
            );
        }
    }

    let captured_olean = lean_lib.join("Captured.olean");
    let out = Command::new(&lean_bin)
        .current_dir(captured_lean.parent().expect("Captured.lean parent"))
        .env("LEAN_PATH", &lean_lib)
        .arg("-DwarningAsError=true")
        .arg("-o")
        .arg(&captured_olean)
        .arg(captured_lean)
        .output()
        .expect("invoke pinned lean on Captured.lean");
    let combined = format!("{}{}", stdout(&out), stderr(&out));
    assert!(
        !combined.contains("maximum recursion depth"),
        "Captured.lean hit recursion-depth limit:\n{combined}"
    );
    assert!(out.status.success(), "Captured.lean failed Lean compilation:\n{combined}");
    assert!(captured_olean.is_file());
    true
}

#[test]
fn scalar_cast_cmp_div_unary_and_overflow_pair_constructs_capture_and_typecheck_in_lean() {
    // Part 1: Normal-crate capture with zero `#![feature(...)]` covers 128-bit
    // scalars, unary `Not`/`Neg`, `char`, `IntToInt` casts, `Ordering` matches,
    // and `(u64, bool)` overflow-pair types.
    let normal_source = br#"
#[repr(u128)]
pub enum WideImplicit {
    Zero,
    One,
}

pub fn wide_scalars(a: u128, b: i128, tag: WideImplicit) -> u128 {
    let max_val: u128 = 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff_u128;
    let min_val: i128 = -0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff_i128 - 1;
    let neg_b: i128 = -b;
    let not_a: u128 = !a;
    let tag_val: u128 = match tag {
        WideImplicit::Zero => 0,
        WideImplicit::One => 1,
    };
    match a {
        0 => (min_val as u128) ^ tag_val,
        340282366920938463463374607431768211455 => not_a,
        _ => max_val & (neg_b as u128),
    }
}

pub fn char_and_casts(c: char, byte: u8, flag: bool, signed: i16) -> u32 {
    let from_byte: char = byte as char;
    let flag_int: i64 = flag as i64;
    let ext: i128 = signed as i128;
    if c < from_byte || c == '\u{03bb}' || c >= '\u{10ffff}' {
        (c as u32) ^ (flag_int as u32)
    } else {
        match c {
            'a' => 1,
            '\u{e000}' => ext as u32,
            _ => 0,
        }
    }
}

pub fn match_ordering(ord: core::cmp::Ordering) -> i8 {
    match ord {
        core::cmp::Ordering::Less => -1i8,
        core::cmp::Ordering::Equal => 0i8,
        core::cmp::Ordering::Greater => 1i8,
    }
}

pub fn pass_overflow_pair(p: (u64, bool)) -> (u64, bool) {
    p
}
"#;

    let fixture = Capture::new(normal_source);
    let output = fixture.command().arg("--scope=crate").output().unwrap();
    assert!(
        output.status.success(),
        "expected crate capture to succeed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = fixture.manifest();
    assert_eq!(manifest["schema_version"], 5);
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 4);

    let manifest_text = std::fs::read_to_string(fixture.output.join("capture.json")).unwrap();
    assert!(
        manifest_text.contains("\"340282366920938463463374607431768211455\""),
        "expected canonical decimal string for u128::MAX in capture.json:\n{manifest_text}"
    );
    assert!(manifest_text.contains("\"kind\": \"overflow_pair\""));
    assert!(manifest_text.contains("\"kind\": \"ordering\""));
    assert!(manifest_text.contains("\"kind\": \"char\""));
    assert!(manifest_text.contains("\"cast_kind\": \"int_to_int\""));

    let lean_path = fixture.output.join("Captured.lean");
    let lean_src = std::fs::read_to_string(&lean_path).unwrap();
    for expected_token in [
        "Trusted.MirAst.IntWidth.i128",
        "Trusted.MirAst.MirTy.char",
        "Trusted.MirAst.MirTy.ordering",
        "(Trusted.MirAst.MirTy.tuple [(Trusted.MirAst.MirTy.int Trusted.MirAst.IntWidth.i64 false), Trusted.MirAst.MirTy.bool])",
        "Trusted.MirAst.UnOp.not",
        "Trusted.MirAst.UnOp.neg",
        "Trusted.MirAst.CastKind.intToInt",
        "BitVec.ofNat 128 340282366920938463463374607431768211455",
    ] {
        assert!(
            lean_src.contains(expected_token),
            "Captured.lean missing {expected_token:?}:\n{lean_src}"
        );
    }
    compile_captured_lean_if_trusted_sources_present(&lean_path);

    // Part 2: Direct intrinsic-lowered Profile v1 `BinOp.cmp`, unchecked
    // `BinOp.div`/`rem`, and `BinOp.*WithOverflow` are exercised under
    // `--stdlib-crate=core`, where `#![feature(intrinsics)]` is in the pinned
    // allowlist.
    let core_intrinsics_src = br#"#![feature(no_core, lang_items, intrinsics)]
#![allow(internal_features)]
#![no_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
impl Copy for bool {}
impl Copy for char {}
impl Copy for i8 {}
impl Copy for i64 {}
impl Copy for u64 {}
impl Copy for u128 {}
impl Copy for Ordering {}

#[lang = "Ordering"]
#[repr(i8)]
pub enum Ordering {
    Less = 0xff_u8 as i8,
    Equal = 0,
    Greater = 1,
}

#[rustc_intrinsic]
pub fn three_way_compare<T: Copy>(lhs: T, rhs: T) -> Ordering;
#[rustc_intrinsic]
pub unsafe fn unchecked_div<T: Copy>(x: T, y: T) -> T;
#[rustc_intrinsic]
pub unsafe fn unchecked_rem<T: Copy>(x: T, y: T) -> T;
#[rustc_intrinsic]
pub fn add_with_overflow<T: Copy>(x: T, y: T) -> (T, bool);
#[rustc_intrinsic]
pub fn sub_with_overflow<T: Copy>(x: T, y: T) -> (T, bool);
#[rustc_intrinsic]
pub fn mul_with_overflow<T: Copy>(x: T, y: T) -> (T, bool);

pub fn ordering_and_cmp(x: i64, y: i64, c1: char, c2: char) -> i8 {
    let ord_i: Ordering = three_way_compare(x, y);
    let ord_c: Ordering = three_way_compare(c1, c2);
    let first = match ord_i {
        Ordering::Less => 0xff_u8 as i8,
        Ordering::Equal => 0i8,
        Ordering::Greater => 1i8,
    };
    let second = match ord_c {
        Ordering::Less => 0xff_u8 as i8,
        Ordering::Equal => 0i8,
        Ordering::Greater => 1i8,
    };
    match first {
        0 => second,
        _ => first,
    }
}

pub unsafe fn unchecked_div_rem(a: i64, b: i64, u: u128, v: u128) -> u128 {
    let q: i64 = unsafe { unchecked_div(a, b) };
    let r: i64 = unsafe { unchecked_rem(a, b) };
    let uq: u128 = unsafe { unchecked_div(u, v) };
    let ur: u128 = unsafe { unchecked_rem(u, v) };
    match q {
        0 => match r {
            0 => uq,
            _ => ur,
        },
        _ => ur,
    }
}

pub fn overflow_pairs(a: u64, b: u64, take_add: bool) -> (u64, bool) {
    let p_add: (u64, bool) = add_with_overflow(a, b);
    let _p_sub: (u64, bool) = sub_with_overflow(a, b);
    let p_mul: (u64, bool) = mul_with_overflow(a, b);
    let copied: (u64, bool) = p_add;
    if take_add {
        copied
    } else {
        p_mul
    }
}
"#;
    let core_fixture = Capture::new(core_intrinsics_src);
    let core_out = core_fixture
        .command_with("core", true)
        .args([
            "--stdlib-crate=core",
            "--select=ordering_and_cmp",
            "--select=unchecked_div_rem",
            "--select=overflow_pairs",
        ])
        .output()
        .unwrap();
    assert!(
        core_out.status.success(),
        "expected --stdlib-crate=core intrinsics capture to succeed:\n{}\n{}",
        stdout(&core_out),
        stderr(&core_out)
    );
    let core_lean_path = core_fixture.output.join("Captured.lean");
    let core_lean_src = std::fs::read_to_string(&core_lean_path).unwrap();
    for expected_token in [
        "Trusted.MirAst.MirTy.ordering",
        "(Trusted.MirAst.MirTy.tuple [(Trusted.MirAst.MirTy.int Trusted.MirAst.IntWidth.i64 false), Trusted.MirAst.MirTy.bool])",
        "Trusted.MirAst.BinOp.div",
        "Trusted.MirAst.BinOp.rem",
        "Trusted.MirAst.BinOp.addWithOverflow",
        "Trusted.MirAst.BinOp.subWithOverflow",
        "Trusted.MirAst.BinOp.mulWithOverflow",
        "Trusted.MirAst.BinOp.cmp",
    ] {
        assert!(
            core_lean_src.contains(expected_token),
            "core Captured.lean missing {expected_token:?}:\n{core_lean_src}"
        );
    }
    compile_captured_lean_if_trusted_sources_present(&core_lean_path);

    // Explicit 128-bit signed enum discriminants (`-1i128 == u128::MAX`) also
    // capture cleanly in `selected_unit` scope.
    let i128_enum_src = br#"#[repr(i128)]
pub enum Signed128 {
    NegOne = -1,
    Zero = 0,
    High = 1 << 100,
}
pub fn selected(x: Signed128) -> i128 {
    match x {
        Signed128::NegOne => -1,
        Signed128::Zero => 0,
        Signed128::High => 1 << 100,
    }
}
"#;
    let i128_fixture = Capture::new(i128_enum_src);
    let i128_out = i128_fixture.selected_command().output().unwrap();
    assert!(i128_out.status.success(), "{i128_out:?}");
    let i128_manifest = i128_fixture.manifest();
    assert_eq!(
        i128_manifest["program"]["bodies"][0]["local_tys"][1]["discriminants"],
        serde_json::json!([
            "340282366920938463463374607431768211455",
            "0",
            "1267650600228229401496703205376"
        ])
    );
    compile_captured_lean_if_trusted_sources_present(&i128_fixture.output.join("Captured.lean"));
}

#[test]
fn unmodeled_projections_tuples_casts_and_operators_fail_closed() {
    // Under Profile v2, tuple aggregates, `.field` projections, and
    // `TerminatorKind::Assert` are captured at `mir_profile_version == 2`.
    let v2_admitted_cases: &[(&str, &[u8])] = &[
        (
            "overflow_pair_field_0_projection",
            b"pub fn selected(p: (u32, bool)) -> u32 { p.0 }\n",
        ),
        (
            "overflow_pair_field_1_projection",
            b"pub fn selected(p: (u32, bool)) -> bool { p.1 }\n",
        ),
        (
            "overflow_pair_tuple_aggregate",
            b"pub fn selected(x: u32, flag: bool) -> (u32, bool) { (x, flag) }\n",
        ),
        (
            "non_overflow_pair_tuple_bool_int",
            b"pub fn selected(p: (bool, u32)) -> (bool, u32) { p }\n",
        ),
        (
            "non_overflow_pair_tuple_char_bool",
            b"pub fn selected(p: (char, bool)) -> (char, bool) { p }\n",
        ),
        (
            "triple_tuple",
            b"pub fn selected(p: (u32, bool, bool)) -> (u32, bool, bool) { p }\n",
        ),
        (
            "checked_div_with_ref_param",
            b"pub fn selected(a: &u32, b: u32) -> u32 { *a / b }\n",
        ),
        (
            "checked_add_option_call",
            b"pub fn selected(a: u32, b: u32) -> Option<u32> { a.checked_add(b) }\n",
        ),
        (
            "slice_index_projection",
            b"pub fn selected(s: &[u8], i: usize) -> u8 { s[i] }\n",
        ),
    ];
    for (name, source) in v2_admitted_cases {
        let fixture = Capture::new(source);
        let output = fixture.selected_command().output().unwrap();
        assert!(output.status.success(), "{name}: {output:?}");
        assert_eq!(fixture.manifest()["program"]["mir_profile_version"], 2, "{name}");
    }

    // Primitive checked division without Profile v2 locals stays on Profile v1
    // with its `TerminatorKind.assert` preserved verbatim.
    let v1_div = Capture::new(b"pub fn selected(a: u32, b: u32) -> u32 { a / b }\n");
    let v1_div_out = v1_div.selected_command().output().unwrap();
    assert!(v1_div_out.status.success(), "{v1_div_out:?}");
    assert_eq!(v1_div.manifest()["program"]["mir_profile_version"], 1);
    assert!(v1_div.lean_source().contains("TerminatorKind.assert"));

    let refused_cases: &[(&str, &[u8], &str)] = &[
        (
            "checked_div_option_call",
            b"pub fn selected(a: u32, b: u32) -> Option<u32> { a.checked_div(b) }\n",
            "unsupported",
        ),
        (
            "transmute_cast_kind",
            b"pub unsafe fn selected(x: u32) -> i32 {\n\
                  unsafe { core::mem::transmute::<u32, i32>(x) }\n\
              }\n",
            "unsupported cast kind: Transmute",
        ),
        (
            "raw_slice_len_core_call_unsupported",
            b"pub fn selected(p: *const [u8]) -> usize { p.len() }\n",
            "unsupported",
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

    // `BinOp::ShlUnchecked` stays explicitly refused in `extract::bin_op`
    // even under `--stdlib-crate=core` where `#![feature(intrinsics)]` is
    // allowlisted.
    let shl_unchecked_core = b"#![feature(no_core, lang_items, intrinsics)]\n\
        #![allow(internal_features)]\n\
        #![no_core]\n\
        #[lang = \"pointee_sized\"] pub trait PointeeSized {}\n\
        #[lang = \"meta_sized\"] pub trait MetaSized: PointeeSized {}\n\
        #[lang = \"sized\"] pub trait Sized: MetaSized {}\n\
        #[lang = \"copy\"] pub trait Copy {}\n\
        impl Copy for u32 {}\n\
        #[rustc_intrinsic]\n\
        pub unsafe fn unchecked_shl<T: Copy, U: Copy>(x: T, y: U) -> T;\n\
        pub unsafe fn selected(a: u32, b: u32) -> u32 {\n\
            unsafe { unchecked_shl(a, b) }\n\
        }\n";
    let shl_fixture = Capture::new(shl_unchecked_core);
    let shl_output = shl_fixture
        .command_with("core", true)
        .args(["--stdlib-crate=core", "--select=selected"])
        .output()
        .unwrap();
    assert_eq!(shl_output.status.code(), Some(1), "{shl_output:?}");
    let shl_failure = status(&shl_output);
    assert_eq!(shl_failure["status"], "unsupported", "{shl_failure}");
    assert!(
        shl_failure.to_string().contains("unsupported binary operator: ShlUnchecked"),
        "expected ShlUnchecked refusal, got {shl_failure}"
    );
    shl_fixture.assert_no_capture_artifacts();
}

#[test]
fn unchecked_arith_intrinsics_and_intra_crate_and_sysroot_num_calls_capture() {
    // Direct unchecked_add/sub/mul intrinsics capture as `BinOp.*Unchecked`
    // under `--stdlib-crate=core` (where `#![feature(intrinsics)]` is pinned).
    let intrinsics_source = b"#![feature(no_core, lang_items, intrinsics)]\n\
        #![allow(internal_features)]\n\
        #![no_core]\n\
        #[lang = \"pointee_sized\"] pub trait PointeeSized {}\n\
        #[lang = \"meta_sized\"] pub trait MetaSized: PointeeSized {}\n\
        #[lang = \"sized\"] pub trait Sized: MetaSized {}\n\
        #[lang = \"copy\"] pub trait Copy {}\n\
        impl Copy for u32 {}\n\
        #[rustc_intrinsic]\n\
        pub unsafe fn unchecked_add<T: Copy>(x: T, y: T) -> T;\n\
        #[rustc_intrinsic]\n\
        pub unsafe fn unchecked_sub<T: Copy>(x: T, y: T) -> T;\n\
        #[rustc_intrinsic]\n\
        pub unsafe fn unchecked_mul<T: Copy>(x: T, y: T) -> T;\n\
        pub unsafe fn selected(a: u32, b: u32) -> u32 {\n\
            let s = unsafe { unchecked_add(a, b) };\n\
            let d = unsafe { unchecked_sub(s, 1) };\n\
            unsafe { unchecked_mul(d, 2) }\n\
        }\n";
    let intrinsics_fixture = Capture::new(intrinsics_source);
    let out = intrinsics_fixture
        .command_with("core", true)
        .args(["--stdlib-crate=core", "--select=selected"])
        .output()
        .unwrap();
    assert!(out.status.success(), "{out:?}");
    let subject = intrinsics_fixture.lean_source();
    for tok in ["BinOp.addUnchecked", "BinOp.subUnchecked", "BinOp.mulUnchecked"] {
        assert!(subject.contains(tok), "missing {tok}:\n{subject}");
    }

    // `zerocopy::layout::add_scaled_metadata` pattern (`usize::unchecked_mul`
    // + `usize::unchecked_add`) captures cleanly as `sysrootCall` on
    // `selected`.
    let add_scaled_source = b"pub unsafe fn add_scaled_metadata(base: usize, metadata: usize, multiple: usize) -> usize {\n\
            let scaled = unsafe { metadata.unchecked_mul(multiple) };\n\
            unsafe { base.unchecked_add(scaled) }\n\
        }\n";
    let scaled_fixture = Capture::new(add_scaled_source);
    let out = scaled_fixture
        .command()
        .arg("--select=add_scaled_metadata")
        .output()
        .unwrap();
    assert!(out.status.success(), "{out:?}");
    let subject = scaled_fixture.lean_source();
    assert!(
        subject.contains("Trusted.MirAst.TerminatorKind.sysrootCall")
            && subject.contains("Trusted.MirAst.SysrootNumKind.uncheckedMul")
            && subject.contains("Trusted.MirAst.SysrootNumKind.uncheckedAdd")
            && subject.contains("Trusted.MirAst.IntWidth.isize false"),
        "{subject}"
    );
    let manifest = scaled_fixture.manifest();
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 1);
    assert_eq!(manifest["selected"][0]["path"], "add_scaled_metadata");
    assert_eq!(manifest["selected"][0]["body_index"], 0);

    // All 6 whitelisted `core::num` ops capture across signed/unsigned types.
    let all_sysroot_source = b"pub unsafe fn selected(a: u16, b: i128) -> u16 {\n\
            let u0 = a.wrapping_add(1);\n\
            let u1 = u0.wrapping_sub(2);\n\
            let u2 = u1.wrapping_mul(3);\n\
            let u3 = unsafe { u2.unchecked_add(1) };\n\
            let u4 = unsafe { u3.unchecked_sub(1) };\n\
            let u5 = unsafe { u4.unchecked_mul(2) };\n\
            let _s0 = b.wrapping_add(1);\n\
            let _s1 = unsafe { b.unchecked_sub(1) };\n\
            u5\n\
        }\n";
    let all_sysroot_fixture = Capture::new(all_sysroot_source);
    let out = all_sysroot_fixture.selected_command().output().unwrap();
    assert!(out.status.success(), "{out:?}");
    let subject = all_sysroot_fixture.lean_source();
    for kind in [
        "SysrootNumKind.wrappingAdd",
        "SysrootNumKind.wrappingSub",
        "SysrootNumKind.wrappingMul",
        "SysrootNumKind.uncheckedAdd",
        "SysrootNumKind.uncheckedSub",
        "SysrootNumKind.uncheckedMul",
    ] {
        assert!(subject.contains(kind), "missing {kind}:\n{subject}");
    }

    // Intra-crate multi-hop calls pull private helpers into `program.bodies`
    // while keeping `--select` root at `body_index: 0` and leaving
    // `census.selected` strictly for `--select` roots.
    let call_source = b"#[inline(never)] fn leaf(x: u16) -> u16 { x.wrapping_add(3) }\n\
        #[inline(never)] fn mid(x: u16) -> u16 { leaf(x).wrapping_mul(2) }\n\
        #[allow(dead_code)] fn unused_ptr(p: *const u8) -> *const u8 { p }\n\
        pub fn selected(x: u16) -> u16 { mid(x) }\n";
    let call_fixture = Capture::new(call_source);
    let out = call_fixture.selected_command().output().unwrap();
    assert!(out.status.success(), "{out:?}");
    let subject = call_fixture.lean_source();
    assert!(
        subject.contains("Trusted.MirAst.TerminatorKind.call")
            && subject.contains("body_0")
            && subject.contains("body_1")
            && subject.contains("body_2"),
        "{subject}"
    );
    let manifest = call_fixture.manifest();
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 3);
    // Reachable helpers stay out of `selected` (and so out of the receipt).
    assert_eq!(manifest["selected"].as_array().unwrap().len(), 1, "{manifest}");
    assert_eq!(manifest["selected"][0]["path"], "selected");
    assert_eq!(manifest["selected"][0]["body_index"], 0);
    let census = manifest["census"].as_array().unwrap();
    let mid_census = census.iter().find(|item| item["path"] == "mid").unwrap();
    assert_eq!(mid_census["selected"], false, "{mid_census}");

    // A crate-local look-alike of a `core::num` method is an ordinary
    // intra-crate `call`, never a pinned `sysrootCall`: only callees in the
    // authenticated sysroot crate named `core` reach sysroot matching.
    let spoof_source = b"mod core {\n\
            pub mod num {\n\
                #[inline(never)]\n\
                pub fn wrapping_add(a: u16, b: u16) -> u16 { a ^ b }\n\
            }\n\
        }\n\
        pub fn selected(x: u16) -> u16 { crate::core::num::wrapping_add(x, 1) }\n";
    let spoof_fixture = Capture::new(spoof_source);
    let out = spoof_fixture.selected_command().output().unwrap();
    assert!(out.status.success(), "{out:?}");
    let subject = spoof_fixture.lean_source();
    assert!(
        subject.contains("Trusted.MirAst.TerminatorKind.call")
            && !subject.contains("sysrootCall")
            && !subject.contains("SysrootNumKind"),
        "{subject}"
    );
}

#[test]
fn unsupported_calls_fail_closed() {
    let bad_call_cases: &[(&str, &[u8], &str)] = &[
        (
            "indirect_fn_ptr_call",
            b"pub fn selected(f: fn(u16) -> u16, x: u16) -> u16 { f(x) }\n",
            "unsupported",
        ),
        (
            "generic_local_call",
            b"fn id<T>(x: T) -> T { x }\n\
              pub fn selected(x: u16) -> u16 { id(x) }\n",
            "generic",
        ),
        (
            "external_non_whitelisted_core_call",
            b"pub fn selected(x: u16) -> u16 { x.swap_bytes() }\n",
            "unsupported core call",
        ),
        (
            "track_caller_intra_crate_callee",
            b"#[track_caller] fn helper(x: u16) -> u16 { x }\n\
              pub fn selected(x: u16) -> u16 { helper(x) }\n",
            "#[track_caller]",
        ),
        (
            "transitive_unsupported_helper",
            b"fn bad_helper(a: f32) -> f32 { a }\n\
              pub fn selected(a: u32) -> u32 { let _ = bad_helper(1.0); a }\n",
            "unsupported",
        ),
    ];
    for (name, source, expected) in bad_call_cases {
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
fn each_sysroot_num_method_captures_its_own_kind() {
    // Each `core::num` method maps to exactly one `SysrootNumKind`; a swapped
    // entry would otherwise still emit some valid kind.
    let kinds = [
        ("unchecked_add", "uncheckedAdd"),
        ("unchecked_sub", "uncheckedSub"),
        ("unchecked_mul", "uncheckedMul"),
        ("wrapping_add", "wrappingAdd"),
        ("wrapping_sub", "wrappingSub"),
        ("wrapping_mul", "wrappingMul"),
    ];
    for (method, kind) in kinds {
        let source = format!(
            "pub unsafe fn selected(a: u16, b: u16) -> u16 {{\n\
                 #[allow(unused_unsafe)]\n\
                 unsafe {{ a.{method}(b) }}\n\
             }}\n"
        );
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.selected_command().output().unwrap();
        assert!(output.status.success(), "{method}: {output:?}");
        let subject = fixture.lean_source();
        for (_, other) in kinds {
            let needle = format!("Trusted.MirAst.SysrootNumKind.{other} ");
            assert_eq!(
                subject.contains(&needle),
                other == kind,
                "{method} must capture only `{kind}`:\n{subject}"
            );
        }
    }
}

#[test]
fn profile_v1_calls_and_profile_v2_core_calls_stay_disjoint() {
    // `usize::unchecked_sub` is in the Profile v2 `CoreCallOp` table, so it
    // lowers to `coreCall` rather than the Profile v1 `sysrootCall` path.
    let core_call = Capture::new(
        b"pub unsafe fn selected(a: usize, b: usize) -> usize {\n\
              unsafe { a.unchecked_sub(b) }\n\
          }\n",
    );
    let output = core_call.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let subject = core_call.lean_source();
    assert!(
        subject.contains("Trusted.MirAst.TerminatorKind.coreCall")
            && subject.contains("Trusted.MirAst.CoreCallOp.usizeUncheckedSub")
            && !subject.contains("Trusted.MirAst.TerminatorKind.sysrootCall"),
        "{subject}"
    );

    // Primitive division-by-zero `Assert` stays on Profile v1, so intra-crate
    // calls to `helper` remain admitted in Profile v1.
    let v1_div_call = Capture::new(
        b"fn helper(a: u32, b: u32) -> u32 { a / b }\n\
          pub fn selected(a: u32, b: u32) -> u32 { helper(a, b) }\n",
    );
    let v1_div_call_out = v1_div_call.selected_command().output().unwrap();
    assert!(v1_div_call_out.status.success(), "{v1_div_call_out:?}");
    assert_eq!(v1_div_call.manifest()["program"]["mir_profile_version"], 1);

    // Lowering `assert!` to `CoreCallOp.panicAbort` under `--panic=abort` makes
    // `helper` a Profile v2 body. Intra-crate calls are admitted in both
    // profiles, so the whole program is captured as Profile v2.
    let v2_call = Capture::new(
        b"fn helper(a: u32, b: u32) -> u32 { assert!(b != 0); a / b }\n\
          pub fn selected(a: u32, b: u32) -> u32 { helper(a, b) }\n",
    );
    let output = v2_call.selected_command().arg("--panic=abort").output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(v2_call.manifest()["program"]["mir_profile_version"], 2);
    assert!(v2_call.lean_source().contains("Trusted.MirAst.TerminatorKind.call\n"));

    // Profile v2 still refuses the Profile v1 `core::num` sysroot path.
    let mixed = Capture::new(
        b"fn helper(a: u32, b: u32) -> u32 { assert!(b != 0); a / b }\n\
          pub fn selected(a: u32, b: u32) -> u32 { helper(a, b).wrapping_add(1) }\n",
    );
    let output = mixed.selected_command().arg("--panic=abort").output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert!(
        failure.to_string().contains("makes a Profile v1 call in a Profile v2 program"),
        "{failure}"
    );
    mixed.assert_no_capture_artifacts();
}

/// A single body whose blocks carry several thousand numeric literals exceeds
/// Lean's default `maxRecDepth` when emitted as one definition, so capture
/// splits its blocks into 16-block chunk definitions.
#[test]
fn many_block_body_compiles_in_lean_under_default_max_rec_depth() {
    let mut source =
        String::from("pub fn many_blocks(x: u32) -> u32 {\n    let mut acc: u32 = x;\n");
    for idx in 0..96u32 {
        let _ = writeln!(
            source,
            "    if acc == {idx}u32 {{ acc = ((acc ^ {}u32) & {}u32) | {}u32; }}",
            idx * 7919 + 1,
            idx * 104_729 + 3,
            idx * 15_485_863 + 5
        );
    }
    source.push_str("    acc\n}\n");
    let fixture = Capture::new(source.as_bytes());
    let output = fixture.command().arg("--scope=crate").output().unwrap();
    assert!(
        output.status.success(),
        "expected many-block capture to succeed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = fixture.manifest();
    let blocks = manifest["program"]["bodies"][0]["blocks"].as_array().unwrap().len();
    assert!(blocks >= 160, "expected at least 160 blocks, got {blocks}");

    let captured_lean = fixture.output.join("Captured.lean");
    let lean_text = std::fs::read_to_string(&captured_lean).unwrap();
    let last_chunk = (blocks - 1) / 16;
    assert!(lean_text.contains(&format!(
        "def body_0_blocks_c{last_chunk} : _root_.List Trusted.MirAst.BasicBlock :="
    )));
    assert!(!lean_text.contains(&format!("def body_0_blocks_c{}", last_chunk + 1)));

    compile_captured_lean_if_trusted_sources_present(&captured_lean);
}

#[test]
fn profile_v1_call_refusal_names_the_profile_v2_trigger() {
    // Each case pairs a Profile v1 call with a construct that selects Profile
    // v2. The refusal must name the calling body, the refused call, and the
    // body and construct that selected Profile v2, even when they differ.
    // (name, source, extra flags, diagnostic substrings)
    type Case<'a> = (&'a str, &'a [u8], &'a [&'a str], &'a [&'a str]);
    let cases: [Case<'_>; 2] = [
        (
            // `--overflow-checks` gives `helper` an optional `Add` overflow
            // `Assert`, which selects Profile v2. Profile v2 admits `caller`'s
            // intra-crate call but refuses its `wrapping_add` sysroot call.
            "overflow_checks",
            b"pub fn helper(x: u32) -> u32 { x + 1 }\n\
              pub fn caller(x: u32) -> u32 { helper(x).wrapping_add(1) }\n",
            &["--overflow-checks"],
            &[
                "rust-path-v1::caller makes a Profile v1 call in a Profile v2 program",
                "terminator: `core::num` call SysrootNumOp { kind: WrappingAdd,",
                "Profile v2 was selected by rust-path-v1::helper (",
                "terminator: `Assert` (Overflow { op: Add })",
            ],
        ),
        (
            // Building the `(u64, bool)` return value with a tuple aggregate
            // selects Profile v2, which refuses the body's own `wrapping_sub`
            // sysroot call.
            "tuple_return",
            b"pub fn sub_borrow(a: u64, b: u32) -> (u64, bool) {\n\
                  let c = b as u64;\n\
                  (a.wrapping_sub(c), a < c)\n\
              }\n",
            &[],
            &[
                "rust-path-v1::sub_borrow makes a Profile v1 call in a Profile v2 program",
                "terminator: `core::num` call SysrootNumOp { kind: WrappingSub,",
                "Profile v2 was selected by rust-path-v1::sub_borrow (",
                ": rvalue AggregateTuple {",
            ],
        ),
    ];
    for (name, source, flags, needles) in cases {
        let fixture = Capture::new(source);
        let output = fixture.command().arg("--scope=crate").args(flags).output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        let diagnostic = failure["diagnostics"][0].as_str().unwrap();
        for needle in needles {
            assert!(diagnostic.contains(needle), "{name}: missing {needle:?} in {diagnostic}");
        }
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn thousand_one_hundred_function_crate_compiles_in_lean_under_default_max_rec_depth() {
    let mut source = String::with_capacity(64 * 1024);
    for idx in 0..1_100usize {
        let _ = writeln!(source, "pub fn f_{idx}(x: u64) -> u64 {{ (x ^ {idx}u64) + 1u64 }}");
    }
    let fixture = Capture::new(source.as_bytes());
    let output = fixture
        .command()
        .arg("--scope=crate")
        .arg("--shard-min-bodies=2000")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "expected 1,100-function crate capture to succeed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = fixture.manifest();
    assert_eq!(manifest["schema_version"], 5);
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 1_100);

    let captured_lean = fixture.output.join("Captured.lean");
    let lean_text = std::fs::read_to_string(&captured_lean).unwrap();
    assert!(lean_text.contains("def body_0 : Trusted.MirAst.Body :="));
    assert!(lean_text.contains("def body_1099 : Trusted.MirAst.Body :="));
    assert!(lean_text.contains("def bodies_chunk_0 : _root_.List Trusted.MirAst.Body :="));
    assert!(lean_text.contains("def bodies_chunk_68 : _root_.List Trusted.MirAst.Body :="));
    assert!(!lean_text.contains("def bodies_chunk_69"));
    assert!(lean_text.contains("(_root_.List.append "));

    compile_captured_lean_if_trusted_sources_present(&captured_lean);
}

#[test]
fn mir_preserve_ub_retains_bare_place_mention_and_rejects_projected_place_mention() {
    // `-Zmir-preserve-ub` disables `RemovePlaceMention` before
    // `Runtime(PostCleanup)`. A bare unprojected `Sized` local mention survives
    // into `capture.json` as `place_mention` and renders cleanly to Lean.
    let bare = Capture::new(
        b"pub fn selected(x: u64) -> u64 {\n\
              let _ = x;\n\
              x\n\
          }\n",
    );
    let output = bare.selected_command().output().unwrap();
    assert!(
        output.status.success(),
        "bare PlaceMention capture failed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = bare.manifest();
    assert_eq!(manifest["configuration"]["mir_preserve_ub"], true);
    let has_place_mention = manifest["program"]["bodies"][0]["blocks"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|bb| bb["statements"].as_array().unwrap())
        .any(|stmt| stmt["kind"] == "place_mention");
    assert!(
        has_place_mention,
        "expected -Zmir-preserve-ub to preserve PlaceMention in Runtime(PostCleanup) MIR: {manifest}"
    );
    let captured_lean = bare.output.join("Captured.lean");
    let lean_text = std::fs::read_to_string(&captured_lean).unwrap();
    assert!(
        lean_text.contains("Trusted.MirAst.StatementKind.nop"),
        "expected bare PlaceMention to render as StatementKind.nop in Captured.lean:\n{lean_text}"
    );
    compile_captured_lean_if_trusted_sources_present(&captured_lean);

    // All locals here have admitted types (`u64` and `(u64, bool)`), and the
    // body contains no `Call` terminators; only `let _ = p.0;` emits a
    // projected `PlaceMention((_1.0: u64))`. Without `-Zmir-preserve-ub`,
    // `RemovePlaceMention` would erase this statement and capture would succeed
    // silently; with `-Zmir-preserve-ub`, capture must fail closed explicitly.
    let projected = Capture::new(
        b"pub fn selected(p: (u64, bool)) -> u64 {\n\
              let _ = p.0;\n\
              p.0\n\
          }\n",
    );
    let output = projected.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(
        failure.to_string().contains("PlaceMention with projections is unsupported"),
        "expected explicit projected PlaceMention refusal, got {failure}"
    );
    projected.assert_no_capture_artifacts();
}

#[test]
fn ergonomic_clones_and_call_source_use_fail_closed_at_capture() {
    // Even on a pure scalar function, enabling `#![feature(ergonomic_clones)]`
    // activates post-capture `optimize_use_clone` in `rustc_codegen_ssa` and
    // must fail closed during capture.
    let feature_only = Capture::new(
        b"#![feature(ergonomic_clones)]\n\
          #![allow(incomplete_features)]\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let output = feature_only.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(
        failure.to_string().contains("ergonomic_clones")
            && failure.to_string().contains("optimize_use_clone"),
        "expected explicit ergonomic_clones/optimize_use_clone refusal, got {failure}"
    );
    feature_only.assert_no_capture_artifacts();

    // Concrete `.use` syntax requires `#![feature(ergonomic_clones)]`. Here
    // `Wrapper` is `!Copy`, so `rustc_mir_build` lowers `x.use` to
    // `TerminatorKind::Call { call_source: CallSource::Use, .. }` rather than
    // `Rvalue::Use(Copy)` (`capture::collect`, with `extract::body` in defense
    // in depth, rejects `ergonomic_clones` first with no published capture
    // artifacts, while `extract::tests` directly unit-tests
    // `check_call_source(mir::CallSource::Use)` via
    // `call_source_use_fails_closed_while_other_call_sources_pass_guard`).
    let use_site = Capture::new(
        b"#![feature(ergonomic_clones)]\n\
          #![allow(incomplete_features)]\n\
          use core::clone::UseCloned;\n\
          pub struct Wrapper(pub u32);\n\
          impl Clone for Wrapper {\n\
              fn clone(&self) -> Self { Wrapper(self.0 + 1) }\n\
          }\n\
          impl UseCloned for Wrapper {}\n\
          pub fn selected(x: Wrapper) -> u32 {\n\
              let a = x.use;\n\
              a.0\n\
          }\n",
    );
    let output = use_site.selected_command().output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(
        failure.to_string().contains("ergonomic_clones")
            && failure.to_string().contains("optimize_use_clone"),
        "expected explicit ergonomic_clones/optimize_use_clone refusal on use site, got {failure}"
    );
    use_site.assert_no_capture_artifacts();

    // Even a bodyless crate enabling `#![feature(ergonomic_clones)]` under
    // `--scope=crate` must fail closed before reaching per-body extraction.
    let bodyless_crate = Capture::new(
        b"#![feature(ergonomic_clones)]\n\
          #![allow(incomplete_features)]\n\
          pub struct Empty;\n",
    );
    let output = bodyless_crate.command().arg("--scope=crate").output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(
        failure.to_string().contains("ergonomic_clones")
            && failure.to_string().contains("optimize_use_clone"),
        "expected explicit ergonomic_clones/optimize_use_clone refusal on bodyless crate, got {failure}"
    );
    bodyless_crate.assert_no_capture_artifacts();
}

#[test]
fn whole_crate_refuses_exported_macros_but_allows_crate_private_macro_rules() {
    let exported = b"#[macro_export]\n\
        macro_rules! read_at {\n\
            ($a:expr) => { unsafe { ::core::ptr::read($a as *const u8) } };\n\
        }\n\
        pub fn zero() -> u64 { 0 }\n";
    let fixture = Capture::new(exported);
    let output = fixture.command().arg("--scope=crate").output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(
        failure.to_string().contains("Macro("),
        "expected exported macro refusal, got {failure}"
    );
    fixture.assert_no_capture_artifacts();

    // Crate-private helper `macro_rules!` only affects crate-local bodies that
    // are already captured in MIR, so whole-crate capture continues to admit it.
    let private_helper = b"macro_rules! zero_lit {\n\
            () => { 0u64 };\n\
        }\n\
        pub fn zero() -> u64 { zero_lit!() }\n";
    let ok_fixture = Capture::new(private_helper);
    let ok_output = ok_fixture.command().arg("--scope=crate").output().unwrap();
    assert!(
        ok_output.status.success(),
        "crate-private macro_rules! should pass whole-crate capture:\n{}\n{}",
        stdout(&ok_output),
        stderr(&ok_output)
    );
    let manifest = ok_fixture.manifest();
    let macro_entry = manifest["census"]
        .as_array()
        .unwrap()
        .iter()
        .find(|item| item["path"] == "zero_lit")
        .expect("private macro should appear in census");
    assert_eq!(macro_entry["required"], false, "{macro_entry}");
    assert_eq!(macro_entry["selected"], false, "{macro_entry}");
}

#[test]
fn whole_crate_refuses_exported_macro_rules_without_unsafe_tokens() {
    // The first eight definitions spell neither `unsafe` nor `global_asm`,
    // yet each lets a downstream `#![forbid(unsafe_code)]` crate emit global
    // assembly, an unsafe block, or an unsafe function that the `unsafe_code`
    // lint does not report, because the construct takes a span from the
    // external definition. The last one can carry no unsafe code at all:
    // exported macros stay refused regardless of their tokens.
    let cases: [(&str, &[u8]); 9] = [
        // `up::m!(core::arch::global_asm);`
        (
            "path metavariable",
            b"#[macro_export] macro_rules! m { ($p:path) => { $p!(\"nop\"); }; }\n",
        ),
        // `up::m!(global_asm);` through a glob re-export.
        (
            "glob re-export",
            b"pub use core::arch::*;\n\
              #[macro_export]\n\
              macro_rules! m { ($x:ident) => { $crate::$x!(\"nop\"); }; }\n",
        ),
        // `up::m!(global_asm);`
        (
            "ident metavariable",
            b"#[macro_export] macro_rules! m { ($m:ident) => { core::arch::$m!(\"nop\"); }; }\n",
        ),
        // `use core::arch::global_asm as inner; up::m!();`
        ("call-site name", b"#[macro_export] macro_rules! m { () => { inner!(\"nop\"); }; }\n"),
        // `use core::arch::global_asm as g; up::m!();`
        (
            "call-site crate path",
            b"#[macro_export] macro_rules! m { () => { crate::g!(\"nop\"); }; }\n",
        ),
        // `up::m!(core::arch::global_asm, !);`
        (
            "caller-supplied bang",
            b"#[macro_export] macro_rules! m { ($p:path, $b:tt) => { $p $b (\"nop\"); }; }\n",
        ),
        // `up::m!(unsafe *p)`: the block ends in definition tokens.
        (
            "caller-supplied unsafe",
            b"#[macro_export] macro_rules! m { ($u:tt $($b:tt)*) => { $u { $($b)* } }; }\n",
        ),
        // `up::m!(pub unsafe fn g());`
        (
            "caller-supplied unsafe fn",
            b"#[macro_export] macro_rules! m { ($($t:tt)*) => { $($t)* {} }; }\n",
        ),
        // A recursive tt-muncher with no reachable unsafe construct.
        (
            "tt-muncher",
            b"#[macro_export]\n\
              macro_rules! count_tts {\n\
                  () => { 0usize };\n\
                  ($head:tt $($tail:tt)*) => { 1usize + $crate::count_tts!($($tail)*) };\n\
              }\n",
        ),
    ];
    for (name, source) in cases {
        let mut full = source.to_vec();
        full.extend_from_slice(b"pub fn zero() -> u64 { 0 }\n");
        let fixture = Capture::new(&full);
        let output = fixture.command().arg("--scope=crate").output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure.to_string().contains("Macro("),
            "{name}: expected exported macro refusal, got {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }

    // `macro` 2.0 (`#![feature(decl_macro)]`) is now blocked even earlier by
    // the closed positive feature allowlist (while `DefKind::Macro` remains
    // required as defense in depth).
    let decl_macro_fixture = Capture::new(
        b"#![feature(decl_macro)]\npub macro zero_v2() { 0u64 }\npub fn zero() -> u64 { 0 }\n",
    );
    let decl_out = decl_macro_fixture.command().arg("--scope=crate").output().unwrap();
    assert_eq!(decl_out.status.code(), Some(1), "{decl_out:?}");
    let decl_failure = status(&decl_out);
    assert_eq!(decl_failure["status"], "unsupported", "{decl_failure}");
    assert!(
        decl_failure.to_string().contains("#![feature(decl_macro)] is unsupported"),
        "expected decl_macro refusal, got {decl_failure}"
    );
    decl_macro_fixture.assert_no_capture_artifacts();
}

#[test]
fn whole_crate_admits_inline_hints_on_trait_method_declarations_only() {
    // rustc ignores (with a warning) `#[inline]` on a bodyless trait method;
    // capture admits the same modes `codegen_attrs` admits on bodies.
    let source = b"#![allow(unused_attributes)]\n\
        pub trait ConstantTimeEq {\n\
            #[inline]\n\
            fn ct_eq(&self, other: &Self) -> u8;\n\
            #[inline(always)]\n\
            fn ct_ne(&self, other: &Self) -> u8;\n\
            #[inline(never)]\n\
            fn ct_id(&self) -> u8;\n\
        }\n\
        pub fn zero() -> u64 { 0 }\n";
    let fixture = Capture::new(source);
    let output = fixture.command().arg("--scope=crate").output().unwrap();
    assert!(
        output.status.success(),
        "inline hints on trait method declarations should pass whole-crate capture:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );

    // Other attributes on declarations, and `#[inline]` on non-method items,
    // stay refused.
    for (expected, source) in [
        (
            "AssocFn: unmodeled attribute",
            b"#![allow(unused_attributes)]\n\
              pub trait T { #[cold] fn f(&self) -> u8; }\n"
                .as_slice(),
        ),
        (
            "AssocConst",
            b"#![allow(unused_attributes)]\n\
              pub trait T { #[inline] const C: u8; }\n"
                .as_slice(),
        ),
    ] {
        let fixture = Capture::new(source);
        let output = fixture.command().arg("--scope=crate").output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{expected}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{expected}: {failure}");
        assert!(
            failure.to_string().contains(expected),
            "expected {expected:?} refusal, got {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn crate_type_attribute_is_admitted_only_when_it_restates_lib() {
    for attr in ["#![crate_type = \"rlib\"]\n", "#![crate_type = \"lib\"]\n"] {
        let source = format!("{attr}pub fn selected(x: u64) -> u64 {{ x }}\n");
        for scope in ["--scope=crate", "--select=selected"] {
            let fixture = Capture::new(source.as_bytes());
            let output = fixture.command().arg(scope).output().unwrap();
            assert!(
                output.status.success(),
                "{attr:?} {scope} should be admitted:\n{}\n{}",
                stdout(&output),
                stderr(&output)
            );
        }
    }

    let refused_lib_sources = [
        "#![crate_type = \"dylib\"]\npub fn selected(x: u64) -> u64 { x }\n",
        "#![crate_type = \"cdylib\"]\npub fn selected(x: u64) -> u64 { x }\n",
        "#![crate_type = \"staticlib\"]\npub fn selected(x: u64) -> u64 { x }\n",
        "#![crate_type = \"proc-macro\"]\npub fn selected(x: u64) -> u64 { x }\n",
        "#![crate_type = \"bin\"]\npub fn selected(x: u64) -> u64 { x }\n",
        "#![crate_type = \"rlib\"]\n#![crate_type = \"proc-macro\"]\n\
         pub fn selected(x: u64) -> u64 { x }\n",
        "#![cfg_attr(all(), crate_type = \"rlib\")]\npub fn selected(x: u64) -> u64 { x }\n",
        "#![cfg_attr(any(), crate_type = \"rlib\")]\npub fn selected(x: u64) -> u64 { x }\n",
        "#![crate_type]\npub fn selected(x: u64) -> u64 { x }\n",
    ];
    for source in refused_lib_sources {
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.command().arg("--scope=crate").output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{source:?}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{source:?}: {failure}");
        assert!(failure.to_string().contains("crate_type"), "{source:?}: {failure}");
        fixture.assert_no_capture_artifacts();
    }

    // A `lib`/`rlib` attribute does not match a binary capture.
    let bin = Capture::new(b"#![crate_type = \"rlib\"]\nfn main() {}\n");
    let output = bin.command().args(["--crate-type=bin", "--scope=crate"]).output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(failure.to_string().contains("crate_type"), "{failure}");
    bin.assert_no_capture_artifacts();
}

#[test]
fn crate_root_cfg_attr_with_non_literal_arguments_is_refused() {
    // `Attribute::meta` cannot parse a non-literal value such as
    // `concat!(..)`, so the pre-expansion check must refuse the whole
    // attribute rather than skip the `feature` or `crate_type` inside it.
    // The same holds for brackets in place of parentheses.
    for attr in [
        "#![cfg_attr(all(), doc = concat!(\"a\"), feature(rustc_private))]\n",
        "#![cfg_attr(any(), doc = concat!(\"a\"), crate_type = \"rlib\")]\n",
        "#![cfg_attr(any(), crate_type = concat!(\"r\", \"lib\"))]\n",
        "#![cfg_attr(any(), doc = concat!(\"a\"), crate_type = \"proc-macro\")]\n",
        "#![cfg_attr[all(), feature(rustc_private)]]\n",
    ] {
        let source = format!("{attr}pub fn selected(x: u64) -> u64 {{ x }}\n");
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.command().arg("--scope=crate").output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{attr:?}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{attr:?}: {failure}");
        assert!(failure.to_string().contains("unparsed"), "{attr:?}: {failure}");
        fixture.assert_no_capture_artifacts();
    }

    // `Attribute::meta` reads `unsafe(..)` inside a `cfg_attr` as a meta item
    // named `unsafe`; what it wraps must be checked too.
    for (attr, expected) in [
        ("#![cfg_attr(all(), unsafe(feature(rustc_private)))]\n", "rustc_private"),
        ("#![cfg_attr(all(), unsafe(r#feature(r#rustc_private)))]\n", "rustc_private"),
        ("#![cfg_attr(all(), unsafe(cfg_attr(all(), feature(rustc_private))))]\n", "rustc_private"),
        ("#![cfg_attr(any(), unsafe(crate_type = \"proc-macro\"))]\n", "crate_type"),
        ("#![cfg_attr(any(), unsafe(crate_type = \"rlib\"))]\n", "crate_type"),
    ] {
        let source = format!("{attr}pub fn selected(x: u64) -> u64 {{ x }}\n");
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.command().arg("--scope=crate").output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{attr:?}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{attr:?}: {failure}");
        assert!(failure.to_string().contains(expected), "{attr:?}: {failure}");
        fixture.assert_no_capture_artifacts();
    }

    // A non-literal crate-level `doc` stays admitted.
    let fixture = Capture::new(b"#![doc = concat!(\"a\")]\npub fn selected(x: u64) -> u64 { x }\n");
    let output = fixture.command().arg("--scope=crate").output().unwrap();
    assert!(
        output.status.success(),
        "non-literal crate doc should pass:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
}

#[test]
fn whole_crate_refuses_itemless_link_foreign_block_and_native_libraries() {
    let linked_foreign = b"#[link(name = \"nonexistent_native_lib\")]\n\
        unsafe extern \"C\" {}\n\
        pub fn zero() -> u64 { 0 }\n";
    let fixture = Capture::new(linked_foreign);
    let output = fixture.command().arg("--scope=crate").output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(
        failure.to_string().contains("ForeignMod"),
        "expected ForeignMod refusal, got {failure}"
    );
    fixture.assert_no_capture_artifacts();

    // Even in selected-unit mode, crate-local native library directives are
    // refused by the belt-and-suspenders `native_libraries` check.
    let sel_fixture = Capture::new(linked_foreign);
    let sel_output = sel_fixture.command().arg("--select=zero").output().unwrap();
    assert_eq!(sel_output.status.code(), Some(1), "{sel_output:?}");
    let sel_failure = status(&sel_output);
    assert_eq!(sel_failure["status"], "unsupported", "{sel_failure}");
    assert!(
        sel_failure.to_string().contains("crate-local native libraries are unsupported"),
        "expected native_libraries refusal, got {sel_failure}"
    );
    sel_fixture.assert_no_capture_artifacts();
}

#[test]
fn nostd_nomain_binary_selected_unit_captures_panic_handler_and_diverging_call() {
    let nostd_src = br#"#![no_std]
#![no_main]

use core::panic::PanicInfo;

unsafe extern "C" {
    fn zx_process_exit(code: i32) -> !;
}

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    unsafe { zx_process_exit(1) }
}

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    unsafe { zx_process_exit(0) }
}

#[inline(never)]
fn loop_forever() -> ! {
    loop {}
}

pub unsafe fn guarded_exit(x: u64) -> u64 {
    if x == 0 {
        unsafe { zx_process_exit(1) }
    }
    x
}

pub unsafe fn guarded_local_diverge(flag: bool) -> u64 {
    if flag {
        42
    } else {
        loop_forever()
    }
}

pub fn spin_never() -> ! {
    loop {}
}
"#;

    // 1. Selected function with diverging foreign `-> !` call compiles and captures
    // under `--crate-type=bin --panic=abort`, emitting `.unsupported` for `target: None`.
    let fixture = Capture::new(nostd_src);
    let output = fixture
        .command()
        .args(["--crate-type=bin", "--panic=abort", "--select=guarded_exit"])
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest_raw = std::fs::read_to_string(fixture.output.join("capture.json")).unwrap();
    let manifest: serde_json::Value = serde_json::from_str(&manifest_raw).unwrap();
    assert_eq!(manifest["configuration"]["crate_type"], "bin");
    assert_eq!(manifest["configuration"]["panic"], "abort");
    assert_eq!(manifest["program"]["panic"], "abort");
    assert_eq!(manifest["program"]["has_local_panic_handler"], true);
    let lean_path = fixture.output.join("Captured.lean");
    let lean_src = std::fs::read_to_string(&lean_path).unwrap();
    assert!(
        lean_src.contains("hasLocalPanicHandler := true"),
        "expected crate-local #[panic_handler] to emit hasLocalPanicHandler := true:\n{lean_src}"
    );
    assert!(
        lean_src.contains("Trusted.MirAst.TerminatorKind.unsupported"),
        "expected diverging `-> !` call to emit TerminatorKind.unsupported:\n{lean_src}"
    );
    compile_captured_lean_if_trusted_sources_present(&lean_path);

    // 2. Selected function calling a local `-> !` helper also lowers `target: None`
    // cleanly without accepting returning calls.
    let local_div_fixture = Capture::new(nostd_src);
    let local_div_out = local_div_fixture
        .command()
        .args(["--crate-type=bin", "--panic=abort", "--select=guarded_local_diverge"])
        .output()
        .unwrap();
    assert!(local_div_out.status.success(), "{local_div_out:?}");
    compile_captured_lean_if_trusted_sources_present(
        &local_div_fixture.output.join("Captured.lean"),
    );

    // 3. Selected function returning `!` (`MirTy.never`) captures cleanly.
    let spin_fixture = Capture::new(nostd_src);
    let spin_out = spin_fixture
        .command()
        .args(["--crate-type=bin", "--panic=abort", "--select=spin_never"])
        .output()
        .unwrap();
    assert!(spin_out.status.success(), "{spin_out:?}");
    compile_captured_lean_if_trusted_sources_present(&spin_fixture.output.join("Captured.lean"));

    // 4. Selecting `_start` (`no_mangle` + `extern "C"`) or `panic` (`&PanicInfo`)
    // must still fail closed.
    for forbidden_root in ["_start", "panic"] {
        let bad_sel = Capture::new(nostd_src);
        let bad_out = bad_sel
            .command()
            .args(["--crate-type=bin", "--panic=abort", &format!("--select={forbidden_root}")])
            .output()
            .unwrap();
        assert_eq!(bad_out.status.code(), Some(1), "{forbidden_root}: {bad_out:?}");
        let failure = status(&bad_out);
        assert_eq!(failure["status"], "unsupported", "{failure}");
        bad_sel.assert_no_capture_artifacts();
    }

    // 5. Whole-crate mode refuses the `#![no_std]` binary crate because `#[panic_handler]`
    // (`PanicImpl`), `ForeignMod`, and `_start` ABI/`no_mangle` are excluded from crate scope.
    let crate_bad = Capture::new(nostd_src);
    let crate_out = crate_bad
        .command()
        .args(["--crate-type=bin", "--panic=abort", "--scope=crate"])
        .output()
        .unwrap();
    assert_eq!(crate_out.status.code(), Some(1), "{crate_out:?}");
    let crate_status = status(&crate_out);
    assert_eq!(crate_status["status"], "unsupported");
    assert!(
        crate_status.to_string().contains("PanicImpl"),
        "expected PanicImpl whole-crate refusal, got {crate_status}"
    );
    crate_bad.assert_no_capture_artifacts();

    // 6. Omitting `--panic=abort` defaults to `--panic=unwind` and fails closed.
    let unwind_bad = Capture::new(nostd_src);
    let unwind_out =
        unwind_bad.command().args(["--crate-type=bin", "--select=guarded_exit"]).output().unwrap();
    assert_eq!(unwind_out.status.code(), Some(1), "{unwind_out:?}");
    assert_eq!(status(&unwind_out)["status"], "compiler_failed");
    unwind_bad.assert_no_capture_artifacts();
}

#[test]
fn binary_capture_boundaries_admit_std_bin_and_refuse_lib_panic_impl_returning_calls_and_static() {
    // 1. Standard library-backed binary (`fn main() {}`) passes whole-crate capture.
    let std_bin = b"pub fn answer() -> u64 { 42 }\nfn main() {}\n";
    let ok_bin = Capture::new(std_bin);
    let ok_out = ok_bin.command().args(["--crate-type=bin", "--scope=crate"]).output().unwrap();
    assert!(ok_out.status.success(), "{ok_out:?}");
    let manifest_raw = std::fs::read_to_string(ok_bin.output.join("capture.json")).unwrap();
    let manifest: serde_json::Value = serde_json::from_str(&manifest_raw).unwrap();
    assert_eq!(manifest["configuration"]["crate_type"], "bin");
    assert_eq!(manifest["configuration"]["panic"], "unwind");
    compile_captured_lean_if_trusted_sources_present(&ok_bin.output.join("Captured.lean"));

    // 2. Crate-local `#[panic_handler]` (`LangItem::PanicImpl`) remains refused on `--crate-type=lib`.
    let nostd_lib_with_panic = br#"#![no_std]
use core::panic::PanicInfo;
#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! { loop {} }
pub fn id(x: u64) -> u64 { x }
"#;
    let bad_lib = Capture::new(nostd_lib_with_panic);
    let bad_lib_out = bad_lib
        .command()
        .args(["--crate-type=lib", "--panic=abort", "--select=id"])
        .output()
        .unwrap();
    assert_eq!(bad_lib_out.status.code(), Some(1), "{bad_lib_out:?}");
    let bad_lib_status = status(&bad_lib_out);
    assert_eq!(bad_lib_status["status"], "unsupported", "{bad_lib_status}");
    assert!(
        bad_lib_status.to_string().contains("PanicImpl")
            || bad_lib_status.to_string().contains("lang item"),
        "expected PanicImpl refusal on lib crate, got {bad_lib_status}"
    );
    bad_lib.assert_no_capture_artifacts();

    // 3. Crate-level `#![crate_type = "bin"]` attribute stays refused even when `--crate-type=bin`
    // is explicitly requested on the CLI.
    let attr_bin = Capture::new(b"#![crate_type = \"bin\"]\nfn main() {}\n");
    let attr_out = attr_bin.command().args(["--crate-type=bin", "--scope=crate"]).output().unwrap();
    assert_eq!(attr_out.status.code(), Some(1), "{attr_out:?}");
    let attr_status = status(&attr_out);
    assert_eq!(attr_status["status"], "unsupported", "{attr_status}");
    assert!(
        attr_status.to_string().contains("crate_type"),
        "expected crate_type attribute refusal, got {attr_status}"
    );
    attr_bin.assert_no_capture_artifacts();

    // 4. Intra-crate returning calls (`target: Some(_)`) succeed in `bin`,
    // while unsupported external returning calls remain refused in both `bin`
    // and `lib`.
    let returning_call = b"#[inline(never)] fn helper() -> u64 { 1 }\npub fn caller() -> u64 { helper() }\nfn main() {}\n";
    let call_bin = Capture::new(returning_call);
    let call_out =
        call_bin.command().args(["--crate-type=bin", "--select=caller"]).output().unwrap();
    assert!(call_out.status.success(), "{call_out:?}");

    let unsupported_call =
        b"pub fn caller(x: u64) -> u64 { x.swap_bytes() }\nfn main() {}\n";
    let unsup_bin = Capture::new(unsupported_call);
    let unsup_out =
        unsup_bin.command().args(["--crate-type=bin", "--select=caller"]).output().unwrap();
    assert_eq!(unsup_out.status.code(), Some(1), "{unsup_out:?}");
    assert_eq!(status(&unsup_out)["status"], "unsupported");
    unsup_bin.assert_no_capture_artifacts();

    // 5. `static` items remain refused (`StaticDef` / `GlobalAlloc::Static`).
    let static_src = b"static S: u64 = 7;\npub fn read_static() -> u64 { S }\n";
    let static_bad = Capture::new(static_src);
    let static_out = static_bad.command().args(["--select=read_static"]).output().unwrap();
    assert_eq!(static_out.status.code(), Some(1), "{static_out:?}");
    assert_eq!(status(&static_out)["status"], "unsupported");
    static_bad.assert_no_capture_artifacts();
}

#[test]
fn required_consts_and_unevaluated_constants_capture_and_typecheck_in_lean() {
    let source = b"#[repr(i8)]\n\
        pub enum NarrowSigned { Neg = -1, Pos = 1 }\n\
        const NEG: NarrowSigned = NarrowSigned::Neg;\n\
        const ANSWER: u64 = 19 + 23;\n\
        const UNIT: () = ();\n\
        pub fn make_neg() -> NarrowSigned { NEG }\n\
        pub fn inline_const_ok() -> u64 {\n\
            const { assert!(core::mem::size_of::<usize>() == 8); }\n\
            ANSWER\n\
        }\n\
        pub fn make_unit() -> () { UNIT }\n";
    let fixture = Capture::new(source);
    let output = fixture
        .command()
        .args(["--select=make_neg", "--select=inline_const_ok", "--select=make_unit"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "expected required_consts capture to succeed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = fixture.manifest();
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 3);
    let lean_text = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(
        lean_text.contains("ConstLit.scalar (BitVec.ofNat 128 255)"),
        "expected evaluated NarrowSigned::Neg (-1i8 = 255) in Lean:\n{lean_text}"
    );
    assert!(
        lean_text.contains("ConstLit.scalar (BitVec.ofNat 128 42)"),
        "expected evaluated ANSWER (42) in Lean:\n{lean_text}"
    );
    assert!(
        lean_text.contains("ConstLit.zeroSized"),
        "expected evaluated UNIT zeroSized constant in Lean:\n{lean_text}"
    );
    compile_captured_lean_if_trusted_sources_present(&fixture.output.join("Captured.lean"));
}

#[test]
fn required_consts_post_monomorphization_errors_fail_closed() {
    let dead_branch_pme = b"pub fn pme<T>() -> usize {\n\
            if false {\n\
                const { assert!(core::mem::size_of::<T>() > 0); }\n\
            }\n\
            1\n\
        }\n";
    let ok_fixture = Capture::new(dead_branch_pme);
    let ok_out = ok_fixture
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"pme","args":["usize"]}"#)
        .output()
        .unwrap();
    assert!(
        ok_out.status.success(),
        "expected non-ZST PME check to pass:\n{}\n{}",
        stdout(&ok_out),
        stderr(&ok_out)
    );

    let fail_fixture = Capture::new(dead_branch_pme);
    let fail_out = fail_fixture
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"pme","args":["()"]}"#)
        .output()
        .unwrap();
    assert_eq!(fail_out.status.code(), Some(1), "{fail_out:?}");
    let failure = status(&fail_out);
    assert!(
        failure["status"] == "compiler_failed" || failure["status"] == "unsupported",
        "expected fail-closed PME refusal, got {failure}"
    );
    fail_fixture.assert_no_capture_artifacts();

    let promoted_pme = b"pub fn promoted_pme<T>() -> usize {\n\
            if false {\n\
                let _ = &const { assert!(core::mem::size_of::<T>() > 0); };\n\
            }\n\
            2\n\
        }\n";
    let promo_fail = Capture::new(promoted_pme);
    let promo_out = promo_fail
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"promoted_pme","args":["()"]}"#)
        .output()
        .unwrap();
    assert_eq!(promo_out.status.code(), Some(1), "{promo_out:?}");
    let promo_failure = status(&promo_out);
    assert!(
        promo_failure["status"] == "compiler_failed" || promo_failure["status"] == "unsupported",
        "expected fail-closed promoted PME refusal, got {promo_failure}"
    );
    promo_fail.assert_no_capture_artifacts();

    let assoc_const_pme = b"pub trait Guard: Sized {\n\
            const OK: usize = {\n\
                assert!(core::mem::size_of::<Self>() > 0);\n\
                core::mem::size_of::<Self>()\n\
            };\n\
        }\n\
        impl Guard for u64 {}\n\
        impl Guard for () {}\n\
        pub fn read_guard<T: Guard>() -> usize { T::OK }\n";
    let assoc_ok = Capture::new(assoc_const_pme);
    let assoc_ok_out = assoc_ok
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"read_guard","args":["u64"]}"#)
        .output()
        .unwrap();
    assert!(
        assoc_ok_out.status.success(),
        "expected associated const Guard::<u64> to pass:\n{}\n{}",
        stdout(&assoc_ok_out),
        stderr(&assoc_ok_out)
    );
    let assoc_lean = std::fs::read_to_string(assoc_ok.output.join("Captured.lean")).unwrap();
    assert!(assoc_lean.contains("ConstLit.scalar (BitVec.ofNat 128 8)"), "{assoc_lean}");

    let assoc_fail = Capture::new(assoc_const_pme);
    let assoc_fail_out = assoc_fail
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"read_guard","args":["()"]}"#)
        .output()
        .unwrap();
    assert_eq!(assoc_fail_out.status.code(), Some(1), "{assoc_fail_out:?}");
    assoc_fail.assert_no_capture_artifacts();
}

#[test]
fn explicit_concrete_monomorphization_captures_generics_consts_lifetimes_and_trait_impls() {
    let source = b"pub fn non_generic(x: u64) -> u64 { x }\n\
        pub fn id<T>(x: T) -> T { x }\n\
        pub fn add_const<const N: usize>(x: usize) -> usize { x + N }\n\
        pub fn with_lt<'a, T: 'a>(x: u64) -> u64 { x }\n\
        pub trait Tag {\n\
            fn tag() -> u8;\n\
        }\n\
        impl Tag for core::mem::ManuallyDrop<u8> {\n\
            fn tag() -> u8 { 7 }\n\
        }\n";
    let fixture = Capture::new(source);
    let output = fixture
        .command()
        .arg("--select=non_generic")
        .arg("--instantiate")
        .arg(r#"{"path":"id","args":["usize"]}"#)
        .arg("--instantiate")
        .arg(r#"{"path":"id","args":["bool"]}"#)
        .arg("--instantiate")
        .arg(r#"{"path":"add_const","args":["42"]}"#)
        .arg("--instantiate")
        .arg(r#"{"path":"with_lt","args":["'static","usize"]}"#)
        .arg("--instantiate")
        .arg(r#"{"path":"with_lt","args":["usize"]}"#)
        .arg("--instantiate")
        .arg(r#"{"path":"Tag::tag","args":["core::mem::ManuallyDrop<u8>"]}"#)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "expected monomorphic instantiation capture to succeed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = fixture.manifest();
    let identities: Vec<&str> = manifest["program"]["bodies"]
        .as_array()
        .unwrap()
        .iter()
        .map(|b| b["identity"].as_str().unwrap())
        .collect();
    // `with_lt<'static, usize>` and `with_lt<usize>` normalize to the same
    // concrete `ty::Instance` and deduplicate to one body.
    assert_eq!(identities.len(), 6, "unexpected identities: {identities:?}");
    assert!(identities.contains(&"rust-path-v1::non_generic"));
    assert!(identities.contains(&"rust-path-v1::id::<usize>"));
    assert!(identities.contains(&"rust-path-v1::id::<bool>"));
    assert!(identities.contains(&"rust-path-v1::add_const::<42>"));
    assert!(identities.iter().any(|id| id.contains("with_lt") && id.contains("usize")));
    assert!(identities.iter().any(|id| id.contains("ManuallyDrop<u8> as Tag>::tag")));
    let lean_text = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(lean_text.contains("ConstLit.scalar (BitVec.ofNat 128 42)"), "{lean_text}");
    assert!(lean_text.contains("ConstLit.scalar (BitVec.ofNat 128 7)"), "{lean_text}");
    compile_captured_lean_if_trusted_sources_present(&fixture.output.join("Captured.lean"));
}

#[test]
fn non_generic_instantiation_shares_body_with_reachable_calls() {
    let source = b"#[inline(never)] pub fn helper(x: u16) -> u16 { x.wrapping_add(1) }\n\
        pub fn selected(x: u16) -> u16 { helper(x) }\n\
        #[inline(never)]\n\
        pub fn countdown(n: u16) -> u16 {\n\
            if n == 0 { 0 } else { countdown(n.wrapping_sub(1)) }\n\
        }\n";
    let identities = |manifest: &Value| -> Vec<String> {
        manifest["program"]["bodies"]
            .as_array()
            .unwrap()
            .iter()
            .map(|b| b["identity"].as_str().unwrap().to_owned())
            .collect()
    };
    let call_callees = |body: &Value| -> Vec<u64> {
        body["blocks"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|block| block["terminator"]["kind"] == "call")
            .map(|block| block["terminator"]["callee"].as_u64().unwrap())
            .collect()
    };

    // A `--select` root calls a non-generic helper that is also passed via
    // `--instantiate`: the call must reuse the instantiated body.
    let fixture = Capture::new(source);
    let output = fixture
        .selected_command()
        .arg("--instantiate")
        .arg(r#"{"path":"helper","args":[]}"#)
        .output()
        .unwrap();
    assert!(output.status.success(), "{}\n{}", stdout(&output), stderr(&output));
    let manifest = fixture.manifest();
    let ids = identities(&manifest);
    assert_eq!(ids, ["rust-path-v1::selected", "rust-path-v1::helper"], "{manifest}");
    let selected = manifest["selected"].as_array().unwrap();
    assert_eq!(selected.len(), 2, "{manifest}");
    assert_eq!(selected[0]["path"], "selected");
    assert_eq!(selected[0]["body_index"], 0);
    assert_eq!(selected[1]["body_index"], 1);
    assert_eq!(call_callees(&manifest["program"]["bodies"][0]), [1]);

    // A self-recursive non-generic instantiation resolves its own call to
    // its own body index rather than re-extracting itself.
    let recursive = Capture::new(source);
    let output = recursive
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"countdown","args":[]}"#)
        .output()
        .unwrap();
    assert!(output.status.success(), "{}\n{}", stdout(&output), stderr(&output));
    let manifest = recursive.manifest();
    assert_eq!(identities(&manifest), ["rust-path-v1::countdown"], "{manifest}");
    assert_eq!(manifest["selected"].as_array().unwrap().len(), 1, "{manifest}");
    assert_eq!(call_callees(&manifest["program"]["bodies"][0]), [0]);
    compile_captured_lean_if_trusted_sources_present(&recursive.output.join("Captured.lean"));
}

#[test]
fn explicit_concrete_monomorphization_refuses_unsatisfied_bounds_and_invalid_requests() {
    let source = b"pub trait Tag { fn tag() -> u8; }\n\
        impl Tag for u8 { fn tag() -> u8 { 1 } }\n\
        pub fn id<T>(x: T) -> T { x }\n\
        pub extern \"C\" fn bad_abi<T>(x: u64) -> u64 { x }\n\
        #[target_feature(enable = \"avx2\")]\n\
        pub fn bad_tf<T>(x: u64) -> u64 { x }\n";

    let cases: &[(&str, &str, &str)] = &[
        (
            "unsatisfied_trait_bound",
            r#"{"path":"Tag::tag","args":["bool"]}"#,
            "trait or well-formedness predicates unsatisfied",
        ),
        ("wrong_arity", r#"{"path":"id","args":["usize","u8"]}"#, "expects 1 generic arguments"),
        ("malformed_arg_syntax", r#"{"path":"id","args":["usize u8"]}"#, "trailing tokens"),
        ("unknown_path", r#"{"path":"missing_fn","args":["usize"]}"#, "was not found"),
        (
            "bad_abi_generic",
            r#"{"path":"bad_abi","args":["usize"]}"#,
            "only non-variadic Rust ABI functions are admitted",
        ),
        (
            "bad_target_feature_generic",
            r#"{"path":"bad_tf","args":["usize"]}"#,
            "target-feature entry obligations are unsupported",
        ),
    ];

    for (name, inst_json, expected) in cases {
        let fixture = Capture::new(source);
        let output = fixture.command().arg("--instantiate").arg(inst_json).output().unwrap();
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
fn explicit_monomorphization_enforces_crate_roots_region_bounds_and_self_const_fn() {
    // External crate roots must not silently fall back to local crate types,
    // and leading `::` must require a known crate root.
    let path_source = b"pub struct LocalOnly;\n\
        pub fn tag<T>() -> u64 { 1 }\n";
    for (name, inst_json, expected) in [
        (
            "missing_external_does_not_fallback_to_local",
            r#"{"path":"tag","args":["core::LocalOnly"]}"#,
            "could not be resolved",
        ),
        (
            "leading_colons_reject_unqualified_local_type",
            r#"{"path":"tag","args":["::LocalOnly"]}"#,
            "unknown crate `LocalOnly`",
        ),
        (
            "leading_colons_reject_crate_keyword",
            r#"{"path":"tag","args":["::crate::LocalOnly"]}"#,
            "invalid leading `::crate`",
        ),
    ] {
        let fixture = Capture::new(path_source);
        let output = fixture.command().arg("--instantiate").arg(inst_json).output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure.to_string().contains(expected),
            "{name}: expected {expected:?}, got {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }

    // Higher-ranked region/outlives obligations must be checked by region
    // resolution, while valid `'static` impls must not feed `ReErased` back
    // into `InferCtxt`.
    let region_source = b"pub trait Hr<'a> {}\n\
        impl Hr<'static> for u8 {}\n\
        pub fn hrtb_outlives<T>() -> u64 where for<'a> &'a T: 'static { 1 }\n\
        pub fn hrtb_trait<T>() -> u64 where for<'a> T: Hr<'a> { 2 }\n\
        pub trait StaticOnly { fn v() -> u64; }\n\
        impl StaticOnly for &'static u8 { fn v() -> u64 { 9 } }\n\
        pub fn call_static<T: StaticOnly>() -> u64 { 3 }\n";
    for (name, inst_json) in [
        ("hrtb_outlives_unsatisfied", r#"{"path":"hrtb_outlives","args":["u8"]}"#),
        ("hrtb_trait_unsatisfied", r#"{"path":"hrtb_trait","args":["u8"]}"#),
    ] {
        let fixture = Capture::new(region_source);
        let output = fixture.command().arg("--instantiate").arg(inst_json).output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure.to_string().contains("region or outlives predicates unsatisfied"),
            "{name}: expected region/outlives refusal, got {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }

    let ok_static = Capture::new(region_source);
    let ok_static_out = ok_static
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"call_static","args":["&'static u8"]}"#)
        .arg("--instantiate")
        .arg(r#"{"path":"StaticOnly::v","args":["&'static u8"]}"#)
        .output()
        .unwrap();
    assert!(
        ok_static_out.status.success(),
        "expected &'static u8 impl instantiations to succeed:\n{}\n{}",
        stdout(&ok_static_out),
        stderr(&ok_static_out)
    );
    assert_eq!(ok_static.manifest()["program"]["bodies"].as_array().unwrap().len(), 2);

    // A non-generic `const fn` referencing a `const` backed by another
    // `const fn`, plus a generic `const fn` whose associated-const impl
    // evaluates another instantiation of the same `const fn` (`helper::<u8>`),
    // must evaluate cleanly outside the MIR provider hook without triggering a
    // query cycle.
    let self_const_source = b"pub const fn add_one(n: u64) -> u64 { n + 1 }\n\
        const HELPER_VAL: u64 = add_one(41);\n\
        pub const fn uses_const_fn() -> u64 { HELPER_VAL }\n\
        pub trait Base { const VAL: u64; }\n\
        impl Base for u8 { const VAL: u64 = 1; }\n\
        impl Base for u16 { const VAL: u64 = helper::<u8>(); }\n\
        pub const fn helper<T: Base>() -> u64 { T::VAL }\n";
    let self_fixture = Capture::new(self_const_source);
    let self_out = self_fixture
        .command()
        .arg("--select=uses_const_fn")
        .arg("--instantiate")
        .arg(r#"{"path":"helper","args":["u16"]}"#)
        .output()
        .unwrap();
    assert!(
        self_out.status.success(),
        "expected const-fn capture without query cycle:\n{}\n{}",
        stdout(&self_out),
        stderr(&self_out)
    );
    assert_eq!(self_fixture.manifest()["program"]["bodies"].as_array().unwrap().len(), 2);
}

/// Capture the explicit instantiations `requests` (`(path, type argument)`
/// pairs) of `source` and return the captured body identities, or each
/// refusal as `(request, reason)`.
///
/// Panics unless the capture either succeeds or refuses cleanly as
/// `unsupported`, so a compiler panic (`tool_failed`) fails the calling test.
fn instantiate(
    source: &str,
    extra_args: &[&str],
    requests: &[(&str, &str)],
) -> Result<Vec<String>, Vec<(String, String)>> {
    instantiate_in(&sysroot(), source, extra_args, requests)
}

/// [`instantiate`] against the compiler sysroot `sysroot`.
fn instantiate_in(
    sysroot: &Path,
    source: &str,
    extra_args: &[&str],
    requests: &[(&str, &str)],
) -> Result<Vec<String>, Vec<(String, String)>> {
    let fixture = Capture::new(source.as_bytes());
    let mut command = fixture.command_in(sysroot, "session", true);
    command.args(extra_args);
    for (path, arg) in requests {
        let request = serde_json::json!({ "path": path, "args": [arg] });
        command.arg("--instantiate").arg(request.to_string());
    }
    let output = command.output().unwrap();
    if output.status.success() {
        let manifest = fixture.manifest();
        let bodies = manifest["program"]["bodies"].as_array().unwrap();
        return Ok(bodies.iter().map(|b| b["identity"].as_str().unwrap().to_owned()).collect());
    }
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}\n{}", stderr(&output));
    fixture.assert_no_capture_artifacts();
    let refusals = failure["unsupported"].as_array().unwrap();
    Err(refusals
        .iter()
        .map(|r| (r["path"].as_str().unwrap().to_owned(), r["reason"].as_str().unwrap().to_owned()))
        .collect())
}

/// Check that `requests` capture exactly the bodies `expected` (identities
/// without their `rust-path-v1::` prefix, in any order).
fn assert_instantiates(
    source: &str,
    extra_args: &[&str],
    requests: &[(&str, &str)],
    expected: &[&str],
) {
    let mut identities = instantiate(source, extra_args, requests)
        .unwrap_or_else(|refusals| panic!("expected {requests:?} to capture, got {refusals:?}"));
    identities.sort();
    let mut expected: Vec<String> = expected.iter().map(|e| format!("rust-path-v1::{e}")).collect();
    expected.sort();
    assert_eq!(identities, expected, "{requests:?}");
}

/// Check that each `(type argument, resolved type)` row resolves as stated.
///
/// Each type argument instantiates its own `pin{i}<T>()`, so the captured
/// identity `pin{i}::<type>` pins the definition that spelling resolved to.
fn assert_resolves(source: &str, rows: &[(&str, &str)]) {
    let mut pinned = source.to_owned();
    for i in 0..rows.len() {
        writeln!(pinned, "pub fn pin{i}<T>() -> u8 {{ 0 }}").unwrap();
    }
    let pins: Vec<String> = (0..rows.len()).map(|i| format!("pin{i}")).collect();
    let requests: Vec<(&str, &str)> =
        pins.iter().zip(rows).map(|(pin, (arg, _))| (pin.as_str(), *arg)).collect();
    let expected: Vec<String> =
        pins.iter().zip(rows).map(|(pin, (_, ty))| format!("{pin}::<{ty}>")).collect();
    let expected: Vec<&str> = expected.iter().map(String::as_str).collect();
    assert_instantiates(&pinned, &[], &requests, &expected);
}

/// Check that every `(path, type argument, reason)` row is refused with a
/// reason containing the stated text.
fn assert_refuses(source: &str, extra_args: &[&str], rows: &[(&str, &str, &str)]) {
    let requests: Vec<(&str, &str)> = rows.iter().map(|(path, arg, _)| (*path, *arg)).collect();
    let refusals = instantiate(source, extra_args, &requests)
        .expect_err("expected every request to be refused");
    assert_eq!(refusals.len(), rows.len(), "{refusals:?}");
    for (path, arg, expected) in rows {
        let request = format!("{path}<{arg}>");
        let (_, reason) = refusals
            .iter()
            .find(|(refused, _)| *refused == request)
            .unwrap_or_else(|| panic!("no refusal for `{request}`: {refusals:?}"));
        assert!(reason.contains(expected), "`{request}`: expected {expected:?}, got {reason:?}");
    }
}

#[test]
fn explicit_monomorphization_resolves_local_adts_aliases_and_rejects_ambiguities() {
    let source = "#![allow(dead_code, non_snake_case)]\n\
        pub trait Tag { fn tag() -> u8; }\n\
        pub fn id_local<T>() -> u8 { 0 }\n\
        pub mod byteorder_like {\n\
            pub struct BigEndian;\n\
            pub enum Endian { Big, Little }\n\
            pub union RawWord { pub bytes: [u8; 2], pub word: u16 }\n\
            pub struct U16<O>(pub u16, pub core::marker::PhantomData<O>);\n\
            pub type BigAlias = BigEndian;\n\
            pub struct Pair<T>(pub T, pub T);\n\
            pub type PairAlias<T> = Pair<T>;\n\
        }\n\
        pub fn byteorder_like() -> u8 { 1 }\n\
        impl Tag for byteorder_like::U16<byteorder_like::BigEndian> {\n\
            fn tag() -> u8 { 11 }\n\
        }\n\
        impl Tag for byteorder_like::U16<byteorder_like::Endian> {\n\
            fn tag() -> u8 { 22 }\n\
        }\n\
        impl Tag for byteorder_like::U16<byteorder_like::RawWord> {\n\
            fn tag() -> u8 { 33 }\n\
        }\n\
        pub mod reexport {\n\
            pub use crate::byteorder_like::BigEndian as ReexportedBig;\n\
            pub use core::num as ext_num;\n\
            pub use core::num::Wrapping as ExtWrap;\n\
        }\n\
        mod priv_mod {\n\
            pub struct PrivAdt { pub v: u8 }\n\
            pub fn PrivAdt() {}\n\
        }\n\
        mod g1 { pub struct Dup; pub mod sub { pub struct Inner; } }\n\
        mod g2 { pub struct Dup; pub mod sub { pub struct Inner; } }\n\
        pub mod amb {\n\
            #[allow(ambiguous_glob_reexports, unused_imports)]\n\
            pub use super::g1::*;\n\
            #[allow(ambiguous_glob_reexports, unused_imports)]\n\
            pub use super::g2::*;\n\
        }\n\
        mod k_struct { pub struct Tri; }\n\
        mod k_trait { pub trait Tri {} }\n\
        mod k_mod { pub mod Tri { pub struct Inner; } }\n\
        pub mod amb3_leaf {\n\
            #[allow(ambiguous_glob_reexports, unused_imports)]\n\
            pub use super::{k_trait::*, k_struct::*, k_mod::*};\n\
        }\n\
        pub mod amb3_mod {\n\
            #[allow(ambiguous_glob_reexports, unused_imports)]\n\
            pub use super::{k_struct::*, k_mod::*, k_trait::*};\n\
        }\n\
        pub mod anon_amb {\n\
            const _: () = { pub struct Same; };\n\
            const _: () = { pub struct Same; };\n\
        }\n";

    // All 6 `BigEndian` spellings deduplicate to one `ty::Instance`.
    assert_instantiates(
        source,
        &[],
        &[
            ("Tag::tag", "byteorder_like::U16<byteorder_like::BigEndian>"),
            ("Tag::tag", "crate::byteorder_like::U16<crate::byteorder_like::BigEndian>"),
            ("Tag::tag", "session::byteorder_like::U16<session::byteorder_like::BigEndian>"),
            ("Tag::tag", "::session::byteorder_like::U16<::session::byteorder_like::BigEndian>"),
            ("Tag::tag", "byteorder_like::U16<byteorder_like::BigAlias>"),
            ("Tag::tag", "byteorder_like::U16<reexport::ReexportedBig>"),
            ("Tag::tag", "byteorder_like::U16<crate::byteorder_like::Endian>"),
            ("Tag::tag", "byteorder_like::U16<byteorder_like::RawWord>"),
            ("id_local", "byteorder_like::PairAlias<u8>"),
            ("id_local", "reexport::ext_num::Wrapping<u8>"),
            ("id_local", "crate::reexport::ExtWrap<u16>"),
            ("id_local", "priv_mod::PrivAdt"),
        ],
        &[
            "<byteorder_like::U16<byteorder_like::BigEndian> as Tag>::tag",
            "<byteorder_like::U16<byteorder_like::Endian> as Tag>::tag",
            "<byteorder_like::U16<byteorder_like::RawWord> as Tag>::tag",
            "id_local::<byteorder_like::Pair<u8>>",
            "id_local::<core::num::wrapping::Wrapping<u8>>",
            "id_local::<core::num::wrapping::Wrapping<u16>>",
            "id_local::<priv_mod::PrivAdt>",
        ],
    );

    // Pin the definition each spelling of a path resolves to.
    assert_resolves(
        source,
        &[
            ("byteorder_like::BigEndian", "byteorder_like::BigEndian"),
            ("crate::byteorder_like::BigEndian", "byteorder_like::BigEndian"),
            ("session::byteorder_like::BigEndian", "byteorder_like::BigEndian"),
            ("::session::byteorder_like::BigEndian", "byteorder_like::BigEndian"),
            ("byteorder_like::BigAlias", "byteorder_like::BigEndian"),
            ("reexport::ReexportedBig", "byteorder_like::BigEndian"),
            ("crate::byteorder_like::Endian", "byteorder_like::Endian"),
            ("byteorder_like::RawWord", "byteorder_like::RawWord"),
            ("byteorder_like::U16<u8>", "byteorder_like::U16<u8>"),
            ("byteorder_like::PairAlias<u8>", "byteorder_like::Pair<u8>"),
            ("reexport::ext_num::Wrapping<u8>", "core::num::wrapping::Wrapping<u8>"),
            ("crate::reexport::ExtWrap<u16>", "core::num::wrapping::Wrapping<u16>"),
            ("priv_mod::PrivAdt", "priv_mod::PrivAdt"),
        ],
    );

    assert_refuses(
        source,
        &[],
        &[
            // Missing local type.
            ("id_local", "crate::byteorder_like::Missing", "could not be resolved"),
            // Glob-ambiguous leaf and module segments.
            ("id_local", "amb::Dup", "resolved ambiguously at segment `Dup`"),
            ("id_local", "crate::amb::sub::Inner", "resolved ambiguously at segment `sub`"),
            // A three-way glob ambiguity stays ambiguous whichever two of the
            // candidates (trait, struct, module) the compiler records.
            ("id_local", "amb3_leaf::Tri", "resolved ambiguously at segment `Tri`"),
            ("id_local", "amb3_mod::Tri::Inner", "resolved ambiguously at segment `Tri`"),
            // Two definitions share one `def_path_str`.
            ("id_local", "anon_amb::_::Same", "resolved ambiguously"),
            // A trait or a module alone is no ADT or type alias.
            ("id_local", "crate::Tag", "could not be resolved"),
            ("id_local", "crate::byteorder_like", "could not be resolved"),
            // The local crate root alone names no type.
            ("id_local", "session", "does not name a type"),
        ],
    );
}

#[test]
fn explicit_monomorphization_gives_type_aliases_use_site_semantics() {
    // A type alias use means what `rustc` makes of it where it is written:
    // its expansion must be well-formed and must normalize under
    // region-aware trait solving, and the regions that normalization erases
    // come back as `'static`, the only free region this language can name.
    let source = r#"#![allow(dead_code, type_alias_bounds)]
use core::marker::PhantomData;
pub fn need_static<T: 'static>() -> u8 { 1 }
pub trait StaticOnly { fn v() -> u64; }
impl StaticOnly for &'static u8 { fn v() -> u64 { 9 } }
impl StaticOnly for &'static [u8] { fn v() -> u64 { 10 } }
pub struct Wrap<'a, T: 'a>(pub &'a T);
pub struct PairStatic<T: 'static>(pub T, pub T);
pub struct Pair<T>(pub T, pub T);
pub struct Inv<'a>(PhantomData<fn(&'a ()) -> &'a ()>);
pub struct AlwaysHr;
pub trait Hr<'a> {}
impl<'a> Hr<'a> for Inv<'a> {}
impl<'a> Hr<'a> for AlwaysHr {}
pub fn hrtb_outlives<T>() -> u64 where for<'a> &'a T: 'static { 1 }
pub fn hrtb_trait<T>() -> u64 where for<'a> T: Hr<'a> { 2 }
pub trait OnlyHr { type Out; }
impl<T> OnlyHr for T where for<'a> T: Hr<'a> { type Out = u64; }
pub trait RefOf { type Out; }
impl<'a> RefOf for &'a u8 { type Out = &'a [u8]; }
pub trait StaticOut { type Out; }
impl StaticOut for &'static u8 { type Out = u64; }
pub trait Any { type Out; }
impl<T: ?Sized> Any for T { type Out = u8; }
pub type StaticRef = &'static u8;
pub type ByteSlice<'a> = &'a [u8];
pub type WrapStatic = Wrap<'static, u8>;
pub type PairOfRefs = PairStatic<&'static u8>;
pub type InvStatic = Inv<'static>;
pub type HrFn = for<'a> fn(&'a u8) -> &'a u8;
pub type OnlyHrOut<T> = <T as OnlyHr>::Out;
pub type RefOut<'a> = <&'a u8 as RefOf>::Out;
pub type RefOutUnderBinder = for<'a> fn(<&'a u8 as RefOf>::Out);
pub type RefOutNoBinder = fn(<&'static u8 as RefOf>::Out);
pub type UnderBinder = for<'a> fn(<&'a u8 as StaticOut>::Out);
pub type AnyOut<T> = <T as Any>::Out;
pub trait AlwaysU8<T: ?Sized> { type Out; }
impl<T: ?Sized> AlwaysU8<T> for () { type Out = u8; }
pub type Discard<T: ?Sized> = <() as AlwaysU8<T>>::Out;
pub type OuterDiscard<T: ?Sized> = Discard<T>;
pub struct NotCopy;
pub type OnlyCopy<T: Copy> = T;
"#;

    // Every request below names a type that `rustc` accepts at a use site.
    // Region and outlives obligations over an alias expansion must see
    // `'static`, never an erased region, and a region bound inside the
    // expansion must stay bound.
    assert_instantiates(
        source,
        &[],
        &[
            ("need_static", "StaticRef"),
            ("StaticOnly::v", "StaticRef"),
            ("StaticOnly::v", "ByteSlice<'static>"),
            ("StaticOnly::v", "ByteSlice"),
            ("StaticOnly::v", "RefOut<'static>"),
            ("need_static", "WrapStatic"),
            ("need_static", "PairOfRefs"),
            ("need_static", "InvStatic"),
            ("need_static", "HrFn"),
            ("need_static", "RefOutUnderBinder"),
            ("need_static", "RefOutNoBinder"),
            ("need_static", "OnlyHrOut<AlwaysHr>"),
            ("need_static", "AnyOut<str>"),
            ("need_static", "Discard<str>"),
            // As in Rust, the bounds of an eager type alias are not enforced.
            ("need_static", "OnlyCopy<NotCopy>"),
        ],
        &[
            "need_static::<&u8>",
            "<&'static u8 as StaticOnly>::v",
            "<&'static [u8] as StaticOnly>::v",
            "need_static::<Wrap<'_, u8>>",
            "need_static::<PairStatic<&u8>>",
            "need_static::<Inv<'_>>",
            "need_static::<for<'a> fn(&'a u8) -> &'a u8>",
            "need_static::<for<'a> fn(&'a [u8])>",
            "need_static::<fn(&[u8])>",
            "need_static::<u64>",
            "need_static::<u8>",
            "need_static::<NotCopy>",
        ],
    );

    // `rustc` rejects every one of these types at a use site.
    let alias_regions = "type alias region or outlives predicates unsatisfied";
    let alias_wf = "type alias trait or well-formedness predicates unsatisfied";
    assert_refuses(
        source,
        &[],
        &[
            // Higher-ranked bounds of the target over an alias expansion.
            ("hrtb_outlives", "StaticRef", "target region or outlives predicates unsatisfied"),
            ("hrtb_trait", "InvStatic", "target region or outlives predicates unsatisfied"),
            // Normalizing the expansion selects an impl whose higher-ranked
            // `where` clause the argument cannot meet.
            ("need_static", "OnlyHrOut<Inv<'static>>", alias_regions),
            ("need_static", "OnlyHrOut<InvStatic>", alias_regions),
            // The same failure under a binder of the expansion.
            ("need_static", "UnderBinder", alias_regions),
            // Normalization would discard the ill-formed projection input,
            // whether it is the self type or a trait argument, and however
            // many aliases deep it sits.
            ("need_static", "AnyOut<Pair<str>>", alias_wf),
            ("need_static", "Discard<Pair<str>>", alias_wf),
            ("need_static", "OuterDiscard<Pair<str>>", alias_wf),
        ],
    );

    // A lazy type alias (`#![feature(lazy_type_alias)]`) also enforces its
    // own bounds wherever it is used.
    let lazy_source = "#![feature(lazy_type_alias)]\n\
        #![allow(incomplete_features, dead_code)]\n\
        pub struct Plain;\n\
        pub type OnlyCopy<T: Copy> = T;\n\
        pub fn need_static<T: 'static>() -> u8 { 1 }\n";
    let allow_lazy = ["--allow-unstable-feature=lazy_type_alias"];
    assert_instantiates(
        lazy_source,
        &allow_lazy,
        &[("need_static", "OnlyCopy<u8>")],
        &["need_static::<u8>"],
    );
    assert_refuses(
        lazy_source,
        &allow_lazy,
        &[(
            "need_static",
            "OnlyCopy<Plain>",
            "type alias trait or well-formedness predicates unsatisfied",
        )],
    );
}

#[test]
fn explicit_monomorphization_never_looks_up_underscore_segments() {
    // No Rust path can name a `_` binding, so `_` segments resolve only as
    // the `_` that `def_path_str` prints for items inside `const _`.
    let self_import = "#![allow(dead_code)]\n\
        extern crate self as _;\n\
        pub struct Target;\n\
        const _: () = { pub struct Target; };\n";
    assert_resolves(
        self_import,
        &[("Target", "Target"), ("_::Target", "_::Target"), ("crate::_::Target", "_::Target")],
    );

    let two_imports = "#![allow(dead_code)]\n\
        extern crate core as _;\n\
        extern crate self as _;\n\
        const _: () = { pub struct Local; };\n";
    assert_resolves(two_imports, &[("_::Local", "_::Local")]);

    let imports_only = "#![allow(dead_code, unused_imports)]\n\
        extern crate core as _;\n\
        mod m { pub struct X; }\n\
        use m as _;\n\
        pub mod n { pub use super::m::X as _; }\n\
        pub fn id_local<T>() -> u8 { 0 }\n";
    assert_refuses(
        imports_only,
        &[],
        &[
            ("id_local", "_::num::Wrapping<u8>", "could not be resolved"),
            ("id_local", "_::X", "could not be resolved"),
            ("id_local", "n::_", "could not be resolved"),
            ("id_local", "::_::num::Wrapping<u8>", "unknown crate `_`"),
        ],
    );
}

#[test]
fn explicit_monomorphization_reconciles_readings_of_a_leading_crate_name() {
    // The leading segment of a relative path may read as a crate name or as
    // an item of the crate root. The path resolves only when every reading
    // that resolves agrees on one definition. All fixtures here are captured
    // as crate `session`.
    let ambiguous = "resolved ambiguously: leading segment";

    // A crate-root module shares the local crate's name.
    let module = "#![allow(dead_code)]\n\
        pub struct Inner;\n\
        pub struct OnlyAtRoot;\n\
        pub mod session { pub struct Inner; pub struct OnlyInMod; }\n\
        pub fn id_local<T>() -> u8 { 0 }\n";
    assert_resolves(
        module,
        &[
            ("session::OnlyInMod", "session::OnlyInMod"),
            ("session::OnlyAtRoot", "OnlyAtRoot"),
            ("session::session::Inner", "session::Inner"),
            ("crate::session::Inner", "session::Inner"),
            ("crate::Inner", "Inner"),
            ("::session::Inner", "Inner"),
            ("::session::session::Inner", "session::Inner"),
        ],
    );
    assert_refuses(module, &[], &[("id_local", "session::Inner", ambiguous)]);

    // A crate-root type shares the local crate's name, and so does a function
    // whose local type `def_path_str` spells `session::Local`. That spelling
    // passes through the struct, so it does not name the function's type.
    let type_and_fn = "#![allow(dead_code, non_camel_case_types)]\n\
        pub struct session {}\n\
        pub fn session() { pub struct Local; }\n\
        pub fn id_local<T>() -> u8 { 0 }\n";
    assert_resolves(type_and_fn, &[("session", "session"), ("crate::session", "session")]);
    let not_a_module = "segment `session` names a struct, not a module";
    assert_refuses(
        type_and_fn,
        &[],
        &[
            ("id_local", "session::Local", not_a_module),
            ("id_local", "crate::session::Local", not_a_module),
        ],
    );

    // The readings also disagree when `def_path_str` spells one of them: the
    // function `session` declares a second `Local`.
    let spelled = "#![allow(dead_code)]\n\
        pub struct Local;\n\
        pub fn session() { pub struct Local; }\n\
        pub fn id_local<T>() -> u8 { 0 }\n";
    assert_resolves(
        spelled,
        &[
            ("Local", "Local"),
            ("crate::Local", "Local"),
            ("::session::Local", "Local"),
            ("crate::session::Local", "session::Local"),
        ],
    );
    assert_refuses(spelled, &[], &[("id_local", "session::Local", ambiguous)]);

    // `extern crate self as session;` and `extern crate alloc;` make the
    // crate-root reading agree with the crate-name reading. A crate-root
    // module named `core` does not agree with the external crate `core`.
    let shadowing = "#![allow(dead_code)]\n\
        extern crate self as session;\n\
        extern crate alloc;\n\
        pub struct Inner;\n\
        pub mod core {\n\
            pub struct OnlyLocal;\n\
            pub mod num { pub struct Wrapping<T>(pub T); }\n\
            pub fn in_fn() { pub struct InFn; }\n\
        }\n\
        pub fn id_local<T>() -> u8 { 0 }\n";
    assert_resolves(
        shadowing,
        &[
            ("session::Inner", "Inner"),
            ("session::session::Inner", "Inner"),
            ("alloc::string::String", "alloc::string::String"),
            ("core::OnlyLocal", "core::OnlyLocal"),
            ("core::mem::ManuallyDrop<u8>", "core::mem::manually_drop::ManuallyDrop<u8>"),
            ("crate::core::num::Wrapping<u8>", "core::num::Wrapping<u8>"),
            ("::core::num::Wrapping<u8>", "core::num::wrapping::Wrapping<u8>"),
            ("crate::core::in_fn::InFn", "core::in_fn::InFn"),
        ],
    );
    assert_refuses(
        shadowing,
        &[],
        &[
            ("id_local", "core::num::Wrapping<u8>", ambiguous),
            // A path that also reads as an external crate's is never taken
            // as a `def_path_str` spelling.
            ("id_local", "core::in_fn::InFn", "could not be resolved"),
            // The crate-root module `core` is no type either.
            ("id_local", "core", "segment `core` names a module, not a struct"),
        ],
    );

    // A glob import supplies the crate-root reading too.
    let glob = "#![allow(dead_code, unused_imports)]\n\
        mod m { pub mod core { pub struct X; } }\n\
        use m::*;\n";
    assert_resolves(
        glob,
        &[
            ("core::X", "m::core::X"),
            ("core::mem::ManuallyDrop<u8>", "core::mem::manually_drop::ManuallyDrop<u8>"),
        ],
    );
}

/// A copy of the compiler sysroot whose target library directory also holds
/// crate `name`, compiled from `source`, so that a capture can load it with
/// `extern crate`.
fn sysroot_with_crate(directory: &Path, name: &str, source: &str) -> PathBuf {
    let real = sysroot();
    let target_lib = "lib/rustlib/x86_64-unknown-linux-gnu/lib";
    let copy = directory.join("sysroot");
    std::fs::create_dir_all(copy.join("bin")).unwrap();
    std::fs::create_dir_all(copy.join(target_lib)).unwrap();
    std::os::unix::fs::symlink(real.join("bin/rustc"), copy.join("bin/rustc")).unwrap();
    for (from, to) in [(real.join("lib"), copy.join("lib")), (real.join(target_lib), copy.join(target_lib))]
    {
        for entry in std::fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            if entry.file_name() != "rustlib" {
                std::os::unix::fs::symlink(entry.path(), to.join(entry.file_name())).unwrap();
            }
        }
    }
    let crate_source = directory.join(format!("{name}.rs"));
    std::fs::write(&crate_source, source).unwrap();
    let output = Command::new(real.join("bin/rustc"))
        .arg("--edition=2021")
        .arg("--crate-type=rlib")
        .arg(format!("--crate-name={name}"))
        .arg("--target=x86_64-unknown-linux-gnu")
        .arg("-Awarnings")
        .arg("-o")
        .arg(copy.join(target_lib).join(format!("lib{name}.rlib")))
        .arg(&crate_source)
        .output()
        .unwrap();
    assert!(output.status.success(), "compile {name}: {}", stderr(&output));
    copy
}

#[test]
fn explicit_monomorphization_refuses_glob_ambiguity_in_external_crates() {
    // A name that glob imports make ambiguous in another crate's module is
    // missing from that module's children. It must still be refused as
    // ambiguous, rather than read as absent while the crate-root reading of
    // the same path resolves.
    let directory = tempfile::tempdir().unwrap();
    let sysroot = sysroot_with_crate(
        directory.path(),
        "dep",
        "pub mod a { pub struct Ambig; pub mod sub { pub struct Target; } }\n\
         pub mod b { pub struct Ambig; pub mod sub { pub struct Target; } }\n\
         pub use a::*;\n\
         pub use b::*;\n\
         pub mod clean { pub struct Unique; }\n",
    );
    let ambiguous_at = |seg: &str| format!("resolved ambiguously at segment `{seg}`");
    let refused = |source: &str, rows: &[(&str, String)]| {
        let requests: Vec<(&str, &str)> = rows.iter().map(|(arg, _)| ("id_local", *arg)).collect();
        let refusals = instantiate_in(&sysroot, source, &[], &requests)
            .expect_err("expected every request to be refused");
        assert_eq!(refusals.len(), rows.len(), "{refusals:?}");
        for (arg, expected) in rows {
            let request = format!("id_local<{arg}>");
            let (_, reason) = refusals
                .iter()
                .find(|(refused, _)| *refused == request)
                .unwrap_or_else(|| panic!("no refusal for `{request}`: {refusals:?}"));
            assert!(reason.contains(expected.as_str()), "`{request}`: got {reason:?}");
        }
    };

    // The external crate alone: its ambiguous names are refused as such, and
    // its unambiguous ones still resolve.
    let external_only = "#![allow(dead_code)]\n\
        extern crate dep as _;\n\
        pub fn id_local<T>() -> u8 { 0 }\n";
    refused(
        external_only,
        &[("dep::Ambig", ambiguous_at("Ambig")), ("dep::sub::Target", ambiguous_at("sub"))],
    );
    assert_eq!(
        instantiate_in(&sysroot, external_only, &[], &[("id_local", "dep::clean::Unique")]),
        Ok(vec!["rust-path-v1::id_local::<dep::clean::Unique>".to_owned()]),
    );

    // A crate-root module named like the crate resolves both paths uniquely,
    // but the crate-name reading is ambiguous, so the paths are refused.
    let with_local = "#![allow(dead_code)]\n\
        extern crate dep as _;\n\
        pub mod dep { pub struct Ambig; pub mod sub { pub struct Target; } }\n\
        pub fn id_local<T>() -> u8 { 0 }\n";
    refused(
        with_local,
        &[("dep::Ambig", ambiguous_at("Ambig")), ("dep::sub::Target", ambiguous_at("sub"))],
    );
}

#[test]
fn explicit_monomorphization_refuses_type_namespace_names_of_other_kinds() {
    // A name that a module binds in the type namespace to anything other than
    // the kind of definition the walk wants is not absent: `rustc` would name
    // that binding there or reject the path. So neither a `def_path_str`
    // spelling nor the other reading of a leading segment may resolve the path
    // instead.
    let not_type = |what: &str| format!("names {what}, not a struct, enum, union, or type alias");
    let not_module = |what: &str| format!("names {what}, not a module");

    // `f::Local` spells the type declared in function `f`, but module `f`
    // binds `Local` to something else.
    for (binding, what) in [
        ("pub use core::primitive::u8 as Local;", "a builtin type"),
        ("pub trait Local {}", "a trait"),
        ("pub mod Local {}", "a module"),
    ] {
        let source = format!(
            "#![allow(dead_code, non_snake_case)]\n\
             pub mod f {{ {binding} }}\n\
             pub fn f() {{ pub struct Local; }}\n\
             pub fn id_local<T>() -> u8 {{ 0 }}\n"
        );
        let reason = not_type(what);
        assert_refuses(
            &source,
            &[],
            &[("id_local", "f::Local", &reason), ("id_local", "crate::f::Local", &reason)],
        );
    }

    // The crate-root reading of `core::cmp::Ordering` meets a binding of
    // another kind, so the external type is not taken instead.
    for (binding, what) in [
        ("pub use ::core::primitive::u8 as Ordering;", "a builtin type"),
        ("pub trait Ordering {}", "a trait"),
    ] {
        let source = format!(
            "#![allow(dead_code)]\n\
             pub mod core {{ pub mod cmp {{ {binding} }} }}\n\
             pub fn id_local<T>() -> u8 {{ 0 }}\n"
        );
        assert_refuses(
            &source,
            &[],
            &[("id_local", "core::cmp::Ordering", &not_type(what))],
        );
        assert_resolves(&source, &[("::core::cmp::Ordering", "core::cmp::Ordering")]);
    }

    // Before the last segment, only a module continues the path.
    let before_last = "#![allow(dead_code)]\n\
        pub mod m { pub use core::primitive::u8 as sub; pub enum E { V } }\n\
        pub fn id_local<T>() -> u8 { 0 }\n";
    assert_refuses(
        before_last,
        &[],
        &[
            ("id_local", "m::sub::X", &not_module("a builtin type")),
            ("id_local", "m::E::V", &not_module("an enum")),
        ],
    );

    // The same holds in another crate's module.
    let directory = tempfile::tempdir().unwrap();
    let sysroot = sysroot_with_crate(
        directory.path(),
        "dep",
        "pub use core::primitive::u8 as Prim;\npub trait Tr {}\n",
    );
    let with_local = "#![allow(dead_code)]\n\
        extern crate dep as _;\n\
        pub mod dep { pub struct Prim; pub struct Tr; }\n\
        pub fn id_local<T>() -> u8 { 0 }\n";
    let refusals = instantiate_in(
        &sysroot,
        with_local,
        &[],
        &[("id_local", "dep::Prim"), ("id_local", "dep::Tr")],
    )
    .expect_err("expected both requests to be refused");
    assert_eq!(refusals.len(), 2, "{refusals:?}");
    for (request, what) in [("id_local<dep::Prim>", "a builtin type"), ("id_local<dep::Tr>", "a trait")]
    {
        let (_, reason) = refusals
            .iter()
            .find(|(refused, _)| refused == request)
            .unwrap_or_else(|| panic!("no refusal for `{request}`: {refusals:?}"));
        assert!(reason.contains(&not_type(what)), "`{request}`: got {reason:?}");
    }
}

#[test]
fn testkit_staged_workspace_runs_capture_and_verifies_status() {
    use std::time::Duration;

    let tools =
        anneal_testkit::ToolchainEnv::resolve(anneal_testkit::ToolchainMode::WorkspaceBuild {
            cli_bin: None,
            capture_bin: Some(PathBuf::from(env!("CARGO_BIN_EXE_anneal-rustc-capture-test-bin"))),
            auditor_bin: None,
        })
        .unwrap();
    let mut ws =
        anneal_testkit::WorkspaceBuilder::new("anneal-cap-testkit-", Duration::from_secs(30))
            .unwrap();
    ws.write_work_file("src/lib.rs", b"pub fn id(x: u64) -> u64 { x }\n").unwrap();
    let staged = ws.stage().unwrap();
    let src = staged.work_dir().join("src/lib.rs");
    let out = staged.work_dir().join("capture_out");
    let args = [
        std::ffi::OsStr::new("--crate-root"),
        src.as_os_str(),
        std::ffi::OsStr::new("--crate-name=testkit_smoke"),
        std::ffi::OsStr::new("--target=x86_64-unknown-linux-gnu"),
        std::ffi::OsStr::new("--out-dir"),
        out.as_os_str(),
        std::ffi::OsStr::new("--select=id"),
        std::ffi::OsStr::new("--source-file"),
        src.as_os_str(),
    ];
    let run = staged.run_capture(&tools, &args).unwrap();
    run.expect_code(0).unwrap();
    let cap_ok = anneal_testkit::assert_captured(&run.output, 1).unwrap();
    assert!(cap_ok.capture.is_file());
    assert!(cap_ok.lean.is_file());
    staged.finish(Ok(())).unwrap();
}

#[test]
fn whole_crate_admits_safe_traits_impls_consts_and_refuses_unsafe_or_extern_obligations() {
    // Positive: safe traits (with bodyless Rust-ABI `AssocFn` and bodyless
    // `AssocConst`), inherent and trait `Impl`s, pure `Const` / `AssocConst`
    // items (`usize`, `[u8; N]`, fieldless enum), and array-length `AnonConst`s
    // all pass `--scope=crate` when every concrete body is scalar-admissible.
    let valid_crate = b"\
        pub const SIZE: usize = 4;\n\
        pub const BYTES: [u8; SIZE] = [1, 2, 3, 4];\n\
        pub enum Tag { Zero, One }\n\
        pub const DEFAULT_TAG: Tag = Tag::Zero;\n\
        pub trait Ops {\n\
            const BASE: usize;\n\
            fn step(x: usize) -> usize;\n\
        }\n\
        impl Tag {\n\
            pub fn as_u8(self) -> u8 {\n\
                match self { Tag::Zero => 0, Tag::One => 1 }\n\
            }\n\
        }\n\
        impl Ops for Tag {\n\
            const BASE: usize = 7;\n\
            fn step(x: usize) -> usize { x ^ 1 }\n\
        }\n";
    let ok_fixture = Capture::new(valid_crate);
    let ok_out = ok_fixture.command().arg("--scope=crate").output().unwrap();
    assert!(
        ok_out.status.success(),
        "expected safe trait/impl/const crate to capture:\n{}\n{}",
        stdout(&ok_out),
        stderr(&ok_out)
    );
    let manifest = ok_fixture.manifest();
    assert!(
        manifest["selected"]
            .as_array()
            .unwrap()
            .iter()
            .any(|b| b["path"].as_str().unwrap().contains("Tag::as_u8")),
        "{manifest}"
    );

    // Builtin `#[derive(Clone, Copy, PartialEq, Eq)]` emits `TrivialClone`,
    // `Copy`, `StructuralPartialEq`, `Clone`, `PartialEq`, and `Eq` impls: all
    // six impl items pass `whole_crate_item`, and Profile v2 captures the
    // derived `clone`, `assert_receiver_is_total_eq`, and `PartialEq::eq`
    // bodies (including projected discriminants through `&Derived`).
    let derived_crate = b"\
        #[derive(Clone, Copy, PartialEq, Eq)]\n\
        pub enum Derived { A, B }\n\
        pub fn ok(x: Derived) -> u8 { match x { Derived::A => 0, Derived::B => 1 } }\n";
    let drv_fixture = Capture::new(derived_crate);
    let drv_out = drv_fixture.command().arg("--scope=crate").output().unwrap();
    assert!(
        drv_out.status.success(),
        "expected derived fieldless enum crate to capture:\n{}\n{}",
        stdout(&drv_out),
        stderr(&drv_out)
    );
    let drv_manifest = drv_fixture.manifest();
    assert!(
        drv_manifest["selected"]
            .as_array()
            .unwrap()
            .iter()
            .any(|b| b["path"].as_str().unwrap().contains("as std::cmp::PartialEq>::eq")),
        "{drv_manifest}"
    );

    // A pure `Struct`-typed `Const` (`Hash([0; 32])`), its `AnonConst`
    // length, and the admitted `Struct` definition itself all capture.
    let struct_const_crate = b"\
        pub const HASH_SIZE: usize = 32;\n\
        pub struct Hash(pub [u8; HASH_SIZE]);\n\
        pub const EMPTY: Hash = Hash([0u8; HASH_SIZE]);\n\
        pub fn ok() -> u8 { 0 }\n";
    let sc_fixture = Capture::new(struct_const_crate);
    let sc_out = sc_fixture.command().arg("--scope=crate").output().unwrap();
    assert!(
        sc_out.status.success(),
        "expected struct const crate to capture:\n{}\n{}",
        stdout(&sc_out),
        stderr(&sc_out)
    );

    // Generic, `Drop`, and unmodeled-field structs stay refused.
    for (name, source, path) in [
        ("generic_struct", "pub struct W<T>(pub T);\npub fn ok() -> u8 { 0 }\n", "W"),
        (
            "recursive_struct",
            "pub struct L { pub next: Option<&'static L> }\npub fn ok() -> u8 { 0 }\n",
            "L",
        ),
        (
            "drop_struct",
            "pub struct G(pub u8);\nimpl Drop for G { fn drop(&mut self) {} }\n\
             pub fn ok() -> u8 { 0 }\n",
            "G",
        ),
    ] {
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.command().arg("--scope=crate").output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure["unsupported"].as_array().unwrap().iter().any(|item| item["path"] == path),
            "{name}: expected {path} refusal, got {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }

    // Negative cases: each unmodeled or unsafe non-callable obligation must
    // fail closed under `--scope=crate`.
    let refused_cases: &[(&str, &[u8], &str)] = &[
        (
            "unsafe_trait",
            b"pub unsafe trait Bad { fn f(); }\npub fn ok() -> u8 { 0 }\n",
            "whole-crate obligation is unsupported: Trait (unsafe trait)",
        ),
        (
            "unsafe_trait_method",
            b"pub trait UnsafeMethod { unsafe fn f(x: u8); }\npub fn ok() -> u8 { 0 }\n",
            "unsafe trait method declarations are unsupported",
        ),
        (
            "unsafe_trait_method_with_impl",
            b"pub trait UnsafeMethod { unsafe fn f(x: u8); }\n\
              pub enum E { A }\n\
              impl UnsafeMethod for E { unsafe fn f(x: u8) {} }\n\
              pub fn ok() -> u8 { 0 }\n",
            "unsafe trait method declarations are unsupported",
        ),
        (
            "auto_trait",
            b"#![feature(auto_traits)]\n\
              pub auto trait MyAuto {}\n\
              pub fn ok() -> u8 { 0 }\n",
            "#![feature(auto_traits)] is unsupported during capture",
        ),
        (
            "unsafe_impl",
            b"pub enum E { A }\n\
              pub unsafe trait Marker {}\n\
              unsafe impl Marker for E {}\n\
              pub fn ok() -> u8 { 0 }\n",
            "whole-crate obligation is unsupported: Impl { of_trait: true } (unsafe impl)",
        ),
        (
            "manual_trivial_clone_impl",
            b"#![feature(trivial_clone)]\n\
              #[derive(Clone, Copy)]\n\
              pub enum E { A }\n\
              pub enum M { X }\n\
              impl Clone for M { fn clone(&self) -> Self { M::X } }\n\
              #[automatically_derived]\n\
              unsafe impl core::clone::TrivialClone for M {}\n\
              pub fn ok() -> u8 { 0 }\n",
            "#![feature(trivial_clone)] is unsupported during capture",
        ),
        (
            "negative_impl",
            b"#![feature(negative_impls)]\n\
              pub enum E { A }\n\
              pub trait Tr {}\n\
              impl !Tr for E {}\n\
              pub fn ok() -> u8 { 0 }\n",
            "#![feature(negative_impls)] is unsupported during capture",
        ),
        (
            "extern_bodyless_fn",
            b"unsafe extern \"C\" { pub fn ext(); }\npub fn ok() -> u8 { 0 }\n",
            "whole-crate obligation is unsupported: Fn",
        ),
        (
            "trait_extern_c_assoc_fn",
            b"pub trait ForeignAbi { extern \"C\" fn f(); }\npub fn ok() -> u8 { 0 }\n",
            "only non-variadic Rust ABI functions are admitted",
        ),
        (
            "trait_linkage_assoc_fn",
            b"#![feature(linkage)]\n\
              pub trait WeakMethod { #[linkage = \"weak\"] fn f(); }\n\
              pub fn ok() -> u8 { 0 }\n",
            "#![feature(linkage)] is unsupported during capture",
        ),
        (
            "unsafe_const",
            b"pub const BAD: usize = unsafe { 1 };\npub fn ok() -> u8 { 0 }\n",
            "unsafe blocks are unsupported in constants",
        ),
        (
            "pointer_const",
            b"pub const PTR: *const u8 = core::ptr::null();\npub fn ok() -> u8 { 0 }\n",
            "unsupported constant type",
        ),
        (
            "ref_const",
            b"pub const MSG: &str = \"hello\";\npub fn ok() -> u8 { 0 }\n",
            "unsupported constant type",
        ),
        (
            "float_const",
            b"pub const F: f64 = 1.0;\npub fn ok() -> u8 { 0 }\n",
            "unsupported constant type",
        ),
        (
            "generic_assoc_const",
            b"pub trait Tr { const C: usize; }\n\
              impl<T> Tr for T { const C: usize = 1; }\n\
              pub fn ok() -> u8 { 0 }\n",
            "generic constants require quantified instantiation obligations",
        ),
        (
            "inline_const",
            b"pub fn ok() -> u8 { let () = const { }; 0 }\n",
            "whole-crate obligation is unsupported: InlineConst",
        ),
    ];
    for (name, source, expected) in refused_cases {
        let fixture = Capture::new(source);
        let output = fixture.command().arg("--scope=crate").output().unwrap();
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
fn captures_profile_v2_slice_and_raw_pointer_bodies_while_keeping_v1_scalar_unchanged() {
    let v2_src = b"\
        pub unsafe fn split_slice<'a>(s: &'a [u8], mid: usize) -> (&'a [u8], &'a [u8]) {\n\
            unsafe { (s.get_unchecked(..mid), s.get_unchecked(mid..)) }\n\
        }\n\
        pub unsafe fn load_u32(p: *const u32) -> u32 {\n\
            unsafe { *p }\n\
        }\n\
        pub unsafe fn store_u8(p: *mut u8, v: u8) {\n\
            unsafe { *p = v; }\n\
        }\n";
    let v2 = Capture::new(v2_src);
    let out = v2.command().arg("--scope=crate").output().unwrap();
    assert!(
        out.status.success(),
        "Profile v2 capture should succeed:\n{}\n{}",
        stdout(&out),
        stderr(&out)
    );
    let manifest = v2.manifest();
    assert_eq!(manifest["program"]["mir_profile_version"], 2, "{manifest}");
    let lean = std::fs::read_to_string(v2.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("mirProfileVersion := 2"), "{lean}");
    assert!(lean.contains("MirTy.slice"), "{lean}");
    assert!(lean.contains("MirTy.rawPtr"), "{lean}");
    assert!(lean.contains("CoreCallOp."), "{lean}");

    // Pure scalar Profile v1 crates must remain at mir_profile_version == 1.
    let v1 = Capture::new(b"pub fn xor(a: u64, b: u64) -> u64 { a ^ b }\n");
    let v1_out = v1.command().arg("--scope=crate").output().unwrap();
    assert!(v1_out.status.success(), "{v1_out:?}");
    assert_eq!(v1.manifest()["program"]["mir_profile_version"], 1);
}

#[test]
fn profile_v2_refuses_unsupported_pointer_casts_and_unsized_types() {
    for (name, source) in [
        (
            "expose-provenance-cast",
            "pub fn selected(p: *const u8) -> usize { p as usize }\n",
        ),
        (
            "ptr-transmute",
            "pub unsafe fn selected(p: *const u8) -> usize {\n\
                 unsafe { core::mem::transmute::<*const u8, usize>(p) }\n\
             }\n",
        ),
        (
            "str-slice",
            "pub fn selected(s: &str) -> usize { s.len() }\n",
        ),
        (
            "signed-ptr-offset",
            "pub unsafe fn selected(p: *const u8, off: isize) -> *const u8 {\n\
                 unsafe { p.offset(off) }\n\
             }\n",
        ),
        (
            "nested-ref",
            "pub fn selected<'a>(r: &'a &'a u8) -> u8 { **r }\n",
        ),
        (
            "ptr-to-ref",
            "pub unsafe fn selected<'a>(p: *mut &'a u8, x: &'a u8) {\n\
                 unsafe { *p = x; }\n\
             }\n",
        ),
        (
            "nested-option",
            "pub fn selected(x: Option<Option<u64>>) -> bool {\n\
                 match x { Some(_) => true, None => false }\n\
             }\n",
        ),
    ] {
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.selected_command().output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn over_aligned_enums_are_refused_because_their_layout_differs_from_the_tag() {
    for (name, source, expected) in [
        (
            "repr-u8-align-4",
            "#[repr(u8, align(4))]\npub enum A4 { X = 0, Y = 1 }\n\
             pub fn selected(x: A4) -> u8 { match x { A4::X => 0, A4::Y => 1 } }\n",
            "over-aligned enum representations are unsupported",
        ),
        (
            "repr-align-8",
            "#[repr(align(8))]\npub enum A8 { X, Y }\n\
             pub fn selected(x: A8) -> u8 { match x { A8::X => 0, A8::Y => 1 } }\n",
            "over-aligned enum representations are unsupported",
        ),
        (
            "repr-align-8-behind-raw-pointer",
            "#[repr(align(8))]\npub enum A8 { X, Y }\n\
             pub unsafe fn selected(p: *const A8) -> *const A8 {\n\
                 unsafe { p.add(1) }\n\
             }\n",
            "over-aligned enum representations are unsupported",
        ),
        (
            "repr-align-16-zero-sized",
            "#[repr(align(16))]\npub enum Z { Only }\n\
             pub fn selected(x: Z) -> u8 { match x { Z::Only => 0 } }\n",
            "over-aligned single-variant enum",
        ),
    ] {
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.selected_command().output().unwrap();
        assert_eq!(status(&output)["status"], "unsupported", "{name}: {output:?}");
        assert_refused(name, &fixture, &output, expected);
    }

    // An alignment request that changes nothing keeps the tag's layout.
    let fixture = Capture::new(
        b"#[repr(u8, align(1))]\npub enum A1 { X = 0, Y = 1 }\n\
          pub fn selected(x: A1) -> u8 { match x { A1::X => 0, A1::Y => 1 } }\n",
    );
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let ty = &fixture.manifest()["program"]["bodies"][0]["local_tys"][1];
    assert_eq!(ty["tag_repr"]["width"], "i8", "{ty}");
}

#[test]
fn overflow_pairs_are_not_addressable_under_profile_v2() {
    for (name, source) in [
        (
            "raw-borrow-of-overflow-pair-local",
            "pub unsafe fn selected(a: u8, b: u8) -> u8 {\n\
                 let pair: (u8, bool) = (a, b == 0);\n\
                 let p = &raw const pair;\n\
                 unsafe { *(p as *const u8) }\n\
             }\n",
        ),
        (
            "borrow-of-overflow-pair-local",
            "pub fn selected(a: u8, b: u8) -> bool {\n\
                 let pair: (u8, bool) = (a, b == 0);\n\
                 let r = &pair;\n\
                 r.1\n\
             }\n",
        ),
        (
            "raw-pointer-to-overflow-pair-argument",
            "pub unsafe fn selected(p: *const (u8, bool)) -> *const (u8, bool) {\n\
                 unsafe { p.add(1) }\n\
             }\n",
        ),
        (
            "reference-to-overflow-pair-argument",
            "pub fn selected(r: &(u32, bool)) -> &(u32, bool) { r }\n",
        ),
        (
            "ptr-to-ptr-cast-to-overflow-pair",
            "pub unsafe fn selected(p: *const u16) -> bool {\n\
                 unsafe { (*(p as *const (u8, bool))).1 }\n\
             }\n",
        ),
    ] {
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.selected_command().output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        let text = failure.to_string();
        assert!(
            text.contains("OverflowPair") || text.contains("overflow pair"),
            "{name}: {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn profile_v2_refuses_const_to_mut_pointer_casts() {
    // Profile v2 models no aliasing rules, so a `*const T` to `*mut T` cast
    // would let a body write to an immutable binding (undefined behavior that
    // v2 would otherwise execute without a fault).
    for (name, source) in [
        (
            "immutable-local",
            "pub fn selected() -> u32 {\n\
                 let x: u32 = 1;\n\
                 let p = &raw const x as *mut u32;\n\
                 unsafe { *p = 2 };\n\
                 x\n\
             }\n",
        ),
        (
            "const-param",
            "pub unsafe fn selected(p: *const u32) {\n\
                 unsafe { *(p as *mut u32) = 2 }\n\
             }\n",
        ),
        (
            "const-slice-param",
            "pub unsafe fn selected(p: *const [u8]) -> *mut [u8] { p as *mut [u8] }\n",
        ),
    ] {
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.selected_command().output().unwrap();
        assert_refused(name, &fixture, &output, "`*const T` to `*mut T`");
    }
}

#[test]
fn tuple_local_field_moves_are_captured() {
    // `t.0` of a non-`Copy` tuple field lowers to `move (_1.0)`, which
    // Profile v2 models by deinitializing just that field. Moving out of
    // `*p` through a reference or raw pointer is a borrow-check error
    // (E0507), so the refused dereference form is covered by the `ir` unit
    // test.
    let fixture = Capture::new(
        b"pub fn selected(t: (core::ops::RangeFrom<usize>, usize)) \
          -> core::ops::RangeFrom<usize> { t.0 }\n",
    );
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert_eq!(fixture.manifest()["program"]["mir_profile_version"], 2);
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("Trusted.MirAst.Operand.move"), "{lean}");
    assert!(lean.contains("Trusted.MirAst.ProjectionElem.field 0"), "{lean}");
}

#[test]
fn overflow_pairs_are_refused_as_vec_box_and_slice_elements() {
    // Like pointees, `Vec`, `Box`, and slice elements are addressable, so an
    // overflow pair, whose layout capture never checks, may not be one.
    for (name, source) in [
        (
            "vec-of-overflow-pair",
            "pub fn selected(v: Vec<(u8, bool)>) -> Vec<(u8, bool)> { v }\n",
        ),
        (
            "box-of-overflow-pair",
            "pub fn selected(b: Box<(u32, bool)>) -> Box<(u32, bool)> { b }\n",
        ),
        (
            "box-slice-of-overflow-pair",
            "pub fn selected(b: Box<[(u8, bool)]>) -> Box<[(u8, bool)]> { b }\n",
        ),
        ("slice-of-overflow-pair", "pub fn selected(s: &[(u8, bool)]) -> &[(u8, bool)] { s }\n"),
        (
            "ref-to-vec-of-overflow-pair",
            "pub fn selected(v: &Vec<(u8, bool)>) -> &Vec<(u8, bool)> { v }\n",
        ),
    ] {
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.selected_command().arg("--panic=abort").output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        let text = failure.to_string();
        assert!(
            text.contains("OverflowPair") || text.contains("overflow pair"),
            "{name}: {failure}"
        );
        fixture.assert_no_capture_artifacts();
    }
}

/// Assert that a fixture captured nothing and failed with `expected` in its
/// status JSON.
fn assert_refused(name: &str, fixture: &Capture, output: &Output, expected: &str) {
    assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
    let failure = status(output);
    assert!(failure.to_string().contains(expected), "{name}: expected {expected:?}, got {failure}");
    fixture.assert_no_capture_artifacts();
}

#[test]
fn crate_named_core_cannot_spoof_trusted_core_items() {
    // A target crate compiled with `--crate-name=core` is itself named
    // `core`, and `def_path_str` prints crate-local paths without a crate
    // prefix, so a local `mod core` prints as `core::...`. Capture must pin
    // trusted `core` items to the sysroot `core` crate (and its lang items),
    // never to the crate name and printed path alone.
    let struct_spoof = b"\
        pub mod core {\n\
            pub mod ops {\n\
                pub mod range {\n\
                    #[derive(Clone, Copy)]\n\
                    pub struct RangeTo<T> { pub end: T, pub pad: T }\n\
                }\n\
            }\n\
        }\n\
        use crate::core::ops::range::RangeTo;\n\
        pub fn selected(r: RangeTo<usize>) -> RangeTo<usize> { r }\n";
    let enum_spoof = b"\
        pub mod core {\n\
            pub mod ops {\n\
                pub mod range {\n\
                    pub enum RangeTo<T> { A(T), B(T) }\n\
                }\n\
            }\n\
        }\n\
        use crate::core::ops::range::RangeTo;\n\
        pub fn selected(x: usize) -> RangeTo<usize> { RangeTo::B(x) }\n";
    let range_spoof = b"\
        pub mod core {\n\
            pub mod ops {\n\
                pub mod range {\n\
                    #[derive(Clone, Copy)]\n\
                    pub struct Range<T> { pub start: T, pub end: T }\n\
                }\n\
            }\n\
        }\n\
        use crate::core::ops::range::Range;\n\
        pub fn selected(a: usize, b: usize) -> Range<usize> {\n\
            Range { start: a, end: b }\n\
        }\n";
    let option_enum_spoof = b"\
        pub mod core {\n\
            pub mod option {\n\
                pub enum Option<T> { None, Some(T) }\n\
            }\n\
        }\n\
        use crate::core::option::Option;\n\
        pub fn selected(x: u64) -> Option<u64> { Option::Some(x) }\n";
    let option_struct_spoof = b"\
        pub mod core {\n\
            pub mod option {\n\
                #[derive(Clone, Copy)]\n\
                pub struct Option<T>(pub T);\n\
            }\n\
        }\n\
        use crate::core::option::Option;\n\
        pub fn selected(x: u64) -> Option<u64> { Option(x) }\n";
    // Local free functions under `pub mod core` compile without E0034 under
    // `--crate-name=core` and print as `core::cmp::min` / `core::mem::replace`.
    // They resolve to crate-local callees, so capture routes them as
    // intra-crate calls (refused as generic) and never consults the trusted
    // `core_def_path` tables.
    let free_fn_spoof = b"\
        pub mod core {\n\
            pub mod cmp {\n\
                pub fn min<T>(_a: T, b: T) -> T { b }\n\
            }\n\
            pub mod mem {\n\
                pub fn replace<T>(_dst: &mut T, src: T) -> T { src }\n\
            }\n\
        }\n\
        pub fn selected(a: u64, b: u64) -> u64 { crate::core::cmp::min(a, b) }\n";
    let mem_replace_spoof = b"\
        pub mod core {\n\
            pub mod mem {\n\
                pub fn replace<T>(_dst: &mut T, src: T) -> T { src }\n\
            }\n\
        }\n\
        pub fn selected(dst: &mut u64, src: u64) -> u64 {\n\
            crate::core::mem::replace(dst, src)\n\
        }\n";
    for (name, source, expected) in [
        ("two-field struct RangeTo", &struct_spoof[..], "unsupported type"),
        ("payload enum RangeTo", &enum_spoof[..], "unsupported type"),
        ("local struct Range", &range_spoof[..], "unsupported type"),
        ("local enum Option", &option_enum_spoof[..], "unsupported type"),
        ("local struct Option", &option_struct_spoof[..], "unsupported type"),
        ("local core::cmp::min call", &free_fn_spoof[..], "calls to generic or monomorphized"),
        (
            "local core::mem::replace call",
            &mem_replace_spoof[..],
            "calls to generic or monomorphized",
        ),
    ] {
        let fixture = Capture::new(source);
        let output = fixture.command_with("core", true).arg("--select=selected").output().unwrap();
        assert_refused(name, &fixture, &output, expected);
    }

    // Sysroot near-misses inside the authenticated `core` crate isolate the
    // `LangItem::{RangeTo, RangeFrom, Range}` and `LangItem::Option` checks in
    // `core_range` and `is_core_option` (whose companion
    // `!def.is_local() && sysroot_core_crate` pins are defense-in-depth
    // unkillable by construction, as a local `#[lang = "Range" | "Option"]`
    // fails with E0152 when sysroot `core` is linked and hits the crate-local
    // lang-item refusal under `#![no_core]`).
    let sysroot_range_inclusive = b"\
        pub fn selected(r: ::core::ops::RangeInclusive<usize>) -> bool {\n\
            let _ = r;\n\
            true\n\
        }\n";
    let sysroot_new_range = b"\
        #![feature(new_range_api)]\n\
        pub fn selected(a: usize, b: usize) -> ::core::range::Range<usize> {\n\
            ::core::range::Range { start: a, end: b }\n\
        }\n";
    let sysroot_poll_enum = b"\
        pub fn selected(x: u64) -> ::core::task::Poll<u64> {\n\
            ::core::task::Poll::Ready(x)\n\
        }\n";
    for (name, source, extra_args, expected) in [
        ("sysroot RangeInclusive<usize>", &sysroot_range_inclusive[..], &[][..], "unsupported type"),
        (
            "sysroot core::range::Range<usize> feature gated",
            &sysroot_new_range[..],
            &[][..],
            "#![feature(new_range_api)] is unsupported",
        ),
        (
            "sysroot core::range::Range<usize>",
            &sysroot_new_range[..],
            &["--allow-unstable-feature=new_range_api"][..],
            "unsupported type",
        ),
        ("sysroot core::task::Poll<u64>", &sysroot_poll_enum[..], &[][..], "unsupported type"),
    ] {
        let fixture = Capture::new(source);
        let mut cmd = fixture.selected_command();
        cmd.args(extra_args);
        let output = cmd.output().unwrap();
        assert_refused(name, &fixture, &output, expected);
    }

    // Look-alike `core::slice::<impl [T]>::len`,
    // `core::ptr::const_ptr::<impl *const T>::add`, and
    // `core::num::<impl u64>::checked_add` cannot reach the call table.
    // Defining inherent impls on primitive types requires
    // `#![feature(rustc_attrs)]` + `#![rustc_coherence_is_core]`, which the
    // closed positive feature allowlist now rejects before macro expansion.
    let method_spoof = b"\
        #![feature(rustc_attrs)]\n\
        #![rustc_coherence_is_core]\n\
        pub mod core {\n\
            pub mod slice {\n\
                impl<T> [T] { pub fn len(&self) -> usize { 7 } }\n\
            }\n\
            pub mod ptr {\n\
                pub mod const_ptr {\n\
                    impl<T> *const T {\n\
                        pub unsafe fn add(self, _count: usize) -> Self { self }\n\
                    }\n\
                }\n\
            }\n\
            pub mod num {\n\
                impl u64 {\n\
                    pub fn checked_add(self, _rhs: Self) -> Option<Self> { Some(7) }\n\
                }\n\
            }\n\
        }\n\
        pub fn selected(s: &[u8]) -> usize { s.len() }\n\
        pub fn checked(x: u64) -> Option<u64> { x.checked_add(1) }\n\
        pub unsafe fn add(p: *const u8) -> *const u8 { unsafe { p.add(1) } }\n";
    for sel in ["--select=selected", "--select=checked"] {
        let fixture = Capture::new(method_spoof);
        let output = fixture.command_with("core", true).arg(sel).output().unwrap();
        assert_refused(
            &format!("method spoof ({sel})"),
            &fixture,
            &output,
            "#![feature(rustc_attrs)] is unsupported",
        );
    }

    // Without the sysroot `core` (`#![no_core]`), the closed positive feature
    // allowlist refuses `#![feature(no_core, lang_items, rustc_attrs)]` on
    // normal crates, and even under `--stdlib-crate=core` (where those
    // features are pinned), `s.len()` and `x.checked_add(1)` cannot spoof core
    // contracts and fall through to unsupported type/call refusals.
    let no_core_spoof = b"\
        #![feature(no_core, lang_items, rustc_attrs)]\n\
        #![no_core]\n\
        #![rustc_coherence_is_core]\n\
        #[lang = \"pointee_sized\"] pub trait PointeeSized {}\n\
        #[lang = \"meta_sized\"] pub trait MetaSized: PointeeSized {}\n\
        #[lang = \"sized\"] pub trait Sized: MetaSized {}\n\
        #[lang = \"copy\"] pub trait Copy {}\n\
        impl Copy for usize {}\n\
        impl Copy for u64 {}\n\
        #[lang = \"legacy_receiver\"] pub trait LegacyReceiver: PointeeSized {}\n\
        impl<T: PointeeSized> LegacyReceiver for &T {}\n\
        pub mod core {\n\
            pub mod option {\n\
                pub enum Option<T> { None, Some(T) }\n\
            }\n\
            pub mod slice {\n\
                impl<T> [T] { pub fn len(&self) -> usize { 7 } }\n\
            }\n\
            pub mod num {\n\
                impl u64 {\n\
                    pub fn checked_add(self, _rhs: Self) -> super::option::Option<Self> {\n\
                        super::option::Option::Some(self)\n\
                    }\n\
                }\n\
            }\n\
        }\n\
        pub fn selected(s: &[u8]) -> usize { s.len() }\n\
        pub fn checked(x: u64) -> crate::core::option::Option<u64> { x.checked_add(1) }\n";
    for sel in ["--select=selected", "--select=checked"] {
        let fixture = Capture::new(no_core_spoof);
        let output = fixture.command_with("core", true).arg(sel).output().unwrap();
        assert_refused(
            &format!("no_core spoof ({sel})"),
            &fixture,
            &output,
            "lang_items, no_core, rustc_attrs",
        );
    }

    let stdlib_fixture = Capture::new(no_core_spoof);
    let stdlib_output = stdlib_fixture
        .command_with("core", true)
        .args(["--stdlib-crate=core", "--select=selected"])
        .output()
        .unwrap();
    assert_refused(
        "no_core stdlib spoof",
        &stdlib_fixture,
        &stdlib_output,
        "calls to generic or monomorphized functions (`core::slice::<impl [T]>::len`) are unsupported",
    );
    let stdlib_checked_fixture = Capture::new(no_core_spoof);
    let stdlib_checked_output = stdlib_checked_fixture
        .command_with("core", true)
        .args(["--stdlib-crate=core", "--select=checked"])
        .output()
        .unwrap();
    assert_refused(
        "no_core stdlib spoof checked",
        &stdlib_checked_fixture,
        &stdlib_checked_output,
        "unsupported type",
    );
}

#[test]
fn unwind_actions_on_asserts_and_core_calls_are_captured_not_normalized() {
    let source = b"\
        pub fn div(a: u64, b: u64) -> u64 { a / b }\n\
        pub unsafe fn bump(p: *const u8) -> *const u8 { unsafe { p.add(1) } }\n";
    for (panic, expected, absent) in [
        ("--panic=abort", "UnwindAction.unreachable", "UnwindAction.continue_"),
        ("--panic=unwind", "UnwindAction.continue_", "UnwindAction.unreachable"),
    ] {
        let fixture = Capture::new(source);
        let output = fixture.command().args([panic, "--scope=crate"]).output().unwrap();
        assert!(
            output.status.success(),
            "{panic}: capture should succeed:\n{}\n{}",
            stdout(&output),
            stderr(&output)
        );
        let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
        let manifest = fixture.manifest();
        let manifest_text = manifest.to_string();
        // Each rendered terminator ends with its `UnwindAction`, and no
        // operand or place renders one, so the first `UnwindAction` after the
        // terminator constructor belongs to that terminator.
        for kind in ["TerminatorKind.assert", "TerminatorKind.coreCall"] {
            let start = lean.find(kind).unwrap_or_else(|| panic!("{panic}: no {kind} in\n{lean}"));
            let rest = &lean[start..];
            let unwind = rest.find("UnwindAction.").map(|at| &rest[at..]).unwrap();
            assert!(unwind.starts_with(expected), "{panic}: {kind} lacks {expected}: {rest}");
        }
        assert!(!lean.contains(absent), "{panic}: unexpected {absent} in\n{lean}");
        let unwind_json = expected.trim_start_matches("UnwindAction.").trim_end_matches('_');
        assert!(
            manifest_text.contains(&format!("\"unwind\":\"{unwind_json}\"")),
            "{panic}: manifest lacks unwind {unwind_json}: {manifest_text}"
        );
    }
}

#[test]
fn overflow_checks_capture_every_optional_overflow_assert_under_both_panic_strategies() {
    // Each of `+`, `-`, `*`, unary `-`, `<<`, and `>>` is an optional
    // overflow check: rustc emits its `Assert` only under
    // `-Coverflow-checks=yes`, which `--overflow-checks` selects.
    let source = b"\
        pub fn selected(a: u16, b: u16, sh: u32, x: i32) -> i32 {\n\
            if a > 100 || b > 100 || a < b || sh >= 16 || x == i32::MIN {\n\
                return 0;\n\
            }\n\
            let shifted = ((((a + b) * (a - b)) as u32) << sh) >> sh;\n\
            -x + (shifted as i32)\n\
        }\n";
    let asserts = [
        "AssertKind.overflow Trusted.MirAst.BinOp.add",
        "AssertKind.overflow Trusted.MirAst.BinOp.sub",
        "AssertKind.overflow Trusted.MirAst.BinOp.mul",
        "AssertKind.overflow Trusted.MirAst.BinOp.shl",
        "AssertKind.overflow Trusted.MirAst.BinOp.shr",
        "AssertKind.overflowNeg",
    ];
    for panic in ["--panic=abort", "--panic=unwind"] {
        let fixture = Capture::new(source);
        let output =
            fixture.selected_command().args([panic, "--overflow-checks"]).output().unwrap();
        assert!(
            output.status.success(),
            "{panic}: capture should succeed:\n{}\n{}",
            stdout(&output),
            stderr(&output)
        );
        let manifest = fixture.manifest();
        assert_eq!(manifest["configuration"]["overflow_checks"], true, "{panic}: {manifest}");
        assert_eq!(manifest["program"]["overflow_checks"], true, "{panic}: {manifest}");
        assert_eq!(manifest["program"]["mir_profile_version"], 2, "{panic}: {manifest}");
        let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
        assert!(lean.contains("overflowChecks := true"), "{panic}: {lean}");
        for expected in asserts.iter().chain(&[
            "BinOp.addWithOverflow",
            "BinOp.subWithOverflow",
            "BinOp.mulWithOverflow",
        ]) {
            assert!(lean.contains(expected), "{panic}: no {expected} in\n{lean}");
        }
        compile_captured_lean_if_trusted_sources_present(&fixture.output.join("Captured.lean"));
    }

    // The default keeps `-Coverflow-checks=no`: wrapping arithmetic and no
    // optional overflow assert.
    let fixture = Capture::new(source);
    let output = fixture.selected_command().output().unwrap();
    assert!(output.status.success(), "{output:?}");
    let manifest = fixture.manifest();
    assert_eq!(manifest["configuration"]["overflow_checks"], false, "{manifest}");
    assert_eq!(manifest["program"]["overflow_checks"], false, "{manifest}");
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("overflowChecks := false"), "{lean}");
    for absent in asserts.iter().chain(&["WithOverflow"]) {
        assert!(!lean.contains(absent), "unexpected {absent} in\n{lean}");
    }
}

#[test]
fn tarjan_scc_sharding_partitions_cyclic_calls_and_verifies_plan() {
    let mut source = String::from(
        "pub fn leaf_00() -> ! { loop {} }\n\
         pub fn cycle_a(x: u64) -> ! { if x == 0 { loop {} } else { cycle_b(x) } }\n\
         pub fn cycle_b(x: u64) -> ! { cycle_a(x) }\n\
         pub fn top_caller(sel: u64) -> u64 {\n\
             match sel {\n\
                 0 => leaf_00(),\n\
                 1 => leaf_01(1),\n\
                 2 => leaf_02(2),\n\
                 3 => leaf_03(3),\n\
                 4 => leaf_04(4),\n\
                 5 => leaf_05(5),\n\
                 _ => 0,\n\
             }\n\
         }\n",
    );
    for idx in 1..=20usize {
        let _ = writeln!(source, "pub fn leaf_{idx:02}(_x: u64) -> ! {{ loop {{}} }}");
    }
    let fixture = Capture::new(source.as_bytes());
    let output = fixture
        .command()
        .arg("--scope=crate")
        .arg("--shard-min-bodies=4")
        .arg("--shard-max-bodies=4")
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "expected cyclic sharded capture to succeed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let out_status = status(&output);
    assert_eq!(out_status["status"], "captured");
    assert!(out_status["shard_count"].as_u64().unwrap() >= 2, "{out_status}");

    let shards_manifest: serde_json::Value = serde_json::from_slice(
        &std::fs::read(fixture.output.join("capture_shards.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(shards_manifest["schema_version"], 1);
    assert_eq!(shards_manifest["total_bodies"], 24);
    assert!(shards_manifest["cyclic_sccs"].as_u64().unwrap() >= 1, "{shards_manifest}");
    let shards = shards_manifest["shards"].as_array().unwrap();
    let cycle_shard = shards
        .iter()
        .find(|s| {
            let ids = s["identities"].as_array().unwrap();
            ids.iter().any(|v| v.as_str().unwrap().ends_with("::cycle_a"))
        })
        .expect("cycle_a shard must exist");
    let cycle_ids = cycle_shard["identities"].as_array().unwrap();
    assert!(
        cycle_ids.iter().any(|v| v.as_str().unwrap().ends_with("::cycle_b")),
        "mutually recursive cycle_a/cycle_b must share one shard: {cycle_shard}"
    );
    assert_eq!(cycle_shard["has_cycle"], true, "{cycle_shard}");

    let leaf_shard_idx = shards
        .iter()
        .find(|s| {
            s["identities"]
                .as_array()
                .unwrap()
                .iter()
                .any(|v| v.as_str().unwrap().ends_with("::leaf_00"))
        })
        .unwrap()["shard_idx"]
        .as_u64()
        .unwrap();
    let caller_shard = shards
        .iter()
        .find(|s| {
            s["identities"]
                .as_array()
                .unwrap()
                .iter()
                .any(|v| v.as_str().unwrap().ends_with("::top_caller"))
        })
        .unwrap();
    let caller_idx = caller_shard["shard_idx"].as_u64().unwrap();
    assert!(
        leaf_shard_idx <= caller_idx,
        "callee shard {leaf_shard_idx} must precede or equal caller shard {caller_idx}"
    );
    let callees: Vec<u64> = caller_shard["callee_shards"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_u64().unwrap())
        .collect();
    assert!(
        !callees.is_empty(),
        "top_caller calls 6 leaves with shard_max_bodies=4, so at least one callee shard must be strictly earlier: {caller_shard}"
    );
    if leaf_shard_idx < caller_idx {
        assert!(callees.contains(&leaf_shard_idx), "{caller_shard}");
    }

    let captured_lean = fixture.output.join("Captured.lean");
    let captured_src = std::fs::read_to_string(&captured_lean).unwrap();
    assert!(
        captured_src.contains("def body_0 : Trusted.MirAst.Body :="),
        "sharded Captured.lean must retain body_<global_idx> aliases for monolithic roots"
    );
    compile_captured_lean_if_trusted_sources_present(&captured_lean);

    // Construct nominal ShardPlan matching `shards_manifest` and check both
    // acceptance and mismatch rejection under `--verify-shard-plan`.
    let plan_entries: Vec<serde_json::Value> = shards
        .iter()
        .map(|s| {
            serde_json::json!({
                "shard_idx": s["shard_idx"],
                "capture_module": s["capture_module"],
                "proof_module": s["proof_module"],
                "num_bodies": s["num_bodies"],
                "has_cycle": s["has_cycle"],
                "oversized_scc": s["oversized_scc"],
                "callee_shards": s["callee_shards"],
                "global_def_id_range": s["global_def_id_range"],
                "identities": s["identities"],
            })
        })
        .collect();
    let plan = serde_json::json!({
        "schema_version": 1,
        "sharded": true,
        "scope": "crate",
        "shard_min_bodies": 4,
        "shard_max_bodies": 4,
        "shard_max_ast_nodes": 2500,
        "total_bodies": 24,
        "total_shards": shards.len(),
        "id_tree_sha256": shards_manifest["id_tree_sha256"],
        "shards": plan_entries,
    });
    let plan_dir = tempfile::tempdir().unwrap();
    let good_plan = plan_dir.path().join("good.json");
    std::fs::write(&good_plan, serde_json::to_vec_pretty(&plan).unwrap()).unwrap();
    let good_fixture = Capture::new(source.as_bytes());
    let good_out = good_fixture
        .command()
        .arg("--scope=crate")
        .arg("--shard-min-bodies=4")
        .arg("--shard-max-bodies=4")
        .arg("--verify-shard-plan")
        .arg(&good_plan)
        .output()
        .unwrap();
    assert!(
        good_out.status.success(),
        "matching --verify-shard-plan must pass:\n{}\n{}",
        stdout(&good_out),
        stderr(&good_out)
    );

    let mut bad_plan_val = plan;
    bad_plan_val["total_bodies"] = serde_json::json!(25);
    let bad_plan = plan_dir.path().join("bad.json");
    std::fs::write(&bad_plan, serde_json::to_vec_pretty(&bad_plan_val).unwrap()).unwrap();
    let bad_fixture = Capture::new(source.as_bytes());
    let bad_out = bad_fixture
        .command()
        .arg("--scope=crate")
        .arg("--shard-min-bodies=4")
        .arg("--shard-max-bodies=4")
        .arg("--verify-shard-plan")
        .arg(&bad_plan)
        .output()
        .unwrap();
    assert!(!bad_out.status.success(), "drifted --verify-shard-plan must fail");
    let bad_combined = format!("{}{}", stdout(&bad_out), stderr(&bad_out));
    assert!(
        bad_combined.contains("drifted from captured crate topology"),
        "{bad_combined}"
    );
    bad_fixture.assert_no_capture_artifacts();
}

#[test]
fn tarjan_scc_sharding_preserves_lifetime_generic_method_and_trait_impl_edges() {
    // Inherent and trait methods on a lifetime-generic type capture with named
    // lifetime `item_identity` (`Wrap::<'a>::step_b`,
    // `<Wrap<'a> as MyMarker>::mark`). Verify callee resolution matches those
    // identities rather than erased `'_` instance strings, keeping mutual
    // recursion in one cyclic shard and ordering the trait callee shard first.
    let source = b"\
        pub struct Wrap<'a>(core::marker::PhantomData<&'a ()>);\n\
        pub trait MyMarker {\n\
            fn mark(x: u64) -> !;\n\
        }\n\
        impl<'a> MyMarker for Wrap<'a> {\n\
            fn mark(_x: u64) -> ! { loop {} }\n\
        }\n\
        impl<'a> Wrap<'a> {\n\
            pub fn step_a(x: u64) -> ! {\n\
                if x == 0 { <Self as MyMarker>::mark(x) } else { Self::step_b(x) }\n\
            }\n\
            pub fn step_b(x: u64) -> ! { Self::step_a(x) }\n\
        }\n\
        pub fn pad_0() -> ! { loop {} }\n\
        pub fn pad_1() -> ! { loop {} }\n";
    let fixture = Capture::new(source);
    let output = fixture
        .command()
        .args([
            "--select=Wrap::<'a>::step_a",
            "--select=Wrap::<'a>::step_b",
            "--select=<Wrap<'a> as MyMarker>::mark",
            "--select=pad_0",
            "--select=pad_1",
            "--shard-min-bodies=2",
            "--shard-max-bodies=2",
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "expected lifetime-generic sharded capture to succeed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let shards_manifest: serde_json::Value = serde_json::from_slice(
        &std::fs::read(fixture.output.join("capture_shards.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(shards_manifest["total_bodies"], 5, "{shards_manifest}");
    assert_eq!(shards_manifest["cyclic_sccs"], 1, "{shards_manifest}");
    let shards = shards_manifest["shards"].as_array().unwrap();
    let find_shard = |suffix: &str| {
        shards
            .iter()
            .find(|s| {
                s["identities"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|v| v.as_str().unwrap().ends_with(suffix))
            })
            .unwrap_or_else(|| panic!("missing shard for {suffix}: {shards_manifest}"))
    };
    let step_a_shard = find_shard("::step_a");
    let step_b_shard = find_shard("::step_b");
    let mark_shard = find_shard("::mark");
    assert_eq!(
        step_a_shard["shard_idx"], step_b_shard["shard_idx"],
        "lifetime-generic cycle step_a <-> step_b must share one shard: {shards_manifest}"
    );
    assert_eq!(step_a_shard["has_cycle"], true, "{step_a_shard}");
    let mark_idx = mark_shard["shard_idx"].as_u64().unwrap();
    let cycle_idx = step_a_shard["shard_idx"].as_u64().unwrap();
    assert!(
        mark_idx < cycle_idx,
        "trait impl callee mark (shard {mark_idx}) must strictly precede full 2-body cycle shard \
         {cycle_idx}: {shards_manifest}"
    );
    let cycle_callees: Vec<u64> = step_a_shard["callee_shards"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v.as_u64().unwrap())
        .collect();
    assert!(
        cycle_callees.contains(&mark_idx),
        "cycle shard must record trait impl callee shard {mark_idx} in callee_shards: {step_a_shard}"
    );
}

#[test]
fn profile_v2_captures_fixed_arrays_rodata_unsize_projected_discriminant_and_core_calls() {
    let src = b"\
        #[repr(u8)]\n\
        pub enum Tag { Alpha = 1, Beta = 2 }\n\
        const HEADER: [u8; 4] = [0x10, 0x20, 0x30, 0x40];\n\
        pub fn pack_u64_u32(hi: u64, lo: u32) -> [u8; 12] {\n\
            let [a0, a1, a2, a3, a4, a5, a6, a7] = hi.to_le_bytes();\n\
            let [b0, b1, b2, b3] = lo.to_le_bytes();\n\
            [a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3]\n\
        }\n\
        pub fn repeat_and_unsize(v: u8) -> usize {\n\
            let arr = [v; 5];\n\
            let s: &[u8] = &arr;\n\
            s.len()\n\
        }\n\
        pub unsafe fn mut_unsize(arr: &mut [u8; 3]) -> &mut [u8] {\n\
            arr\n\
        }\n\
        pub unsafe fn raw_unsize(p: *const [u8; 4]) -> *const [u8] {\n\
            p\n\
        }\n\
        pub fn rodata_slice_len() -> usize {\n\
            let s: &[u8] = &HEADER;\n\
            s.len()\n\
        }\n\
        pub fn tag_eq(a: &Tag, b: &Tag) -> bool {\n\
            match (a, b) {\n\
                (Tag::Alpha, Tag::Alpha) | (Tag::Beta, Tag::Beta) => true,\n\
                _ => false,\n\
            }\n\
        }\n\
        pub fn array_eq(a: &[u8; 4]) -> bool {\n\
            *a == HEADER\n\
        }\n\
        pub fn array_head_tail(a: [u8; 4]) -> u8 {\n\
            let [first, .., last] = a;\n\
            first + last\n\
        }\n";
    let cap = Capture::new(src);
    let out = cap
        .command()
        .args([
            "--select=pack_u64_u32",
            "--select=repeat_and_unsize",
            "--select=mut_unsize",
            "--select=raw_unsize",
            "--select=rodata_slice_len",
            "--select=tag_eq",
            "--select=array_eq",
            "--select=array_head_tail",
        ])
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "Profile v2 array crate capture should succeed:\n{}\n{}",
        stdout(&out),
        stderr(&out)
    );
    let manifest = cap.manifest();
    assert_eq!(manifest["program"]["mir_profile_version"], 2, "{manifest}");
    let lean = std::fs::read_to_string(cap.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("MirTy.array"), "{lean}");
    assert!(lean.contains("ProjectionElem.constantIndex"), "{lean}");
    assert!(lean.contains("Rvalue.aggregateArray"), "{lean}");
    assert!(lean.contains("Rvalue.repeat_"), "{lean}");
    assert!(lean.contains("CastKind.unsize"), "{lean}");
    assert!(lean.contains("CoreCallOp.intToLeBytes"), "{lean}");
    assert!(lean.contains("CoreCallOp.arrayEq"), "{lean}");
    assert!(lean.contains("ConstLit.rodataRef"), "{lean}");
}

#[test]
fn profile_v2_refuses_unsupported_array_and_rodata_shapes() {
    for (name, source, expected_reason) in [
        (
            "array-of-refs",
            "pub fn selected<'a>(a: [&'a u8; 2]) -> u8 { *a[0] }\n",
            "outside the Profile v2 type fragment",
        ),
        (
            "array-of-overflow-pair",
            "pub fn selected(a: [(u32, bool); 2]) -> u32 { a[0].0 }\n",
            "outside the Profile v2 type fragment",
        ),
        (
            "array-of-tuple",
            "pub fn selected(a: [(u8, u16); 2]) -> u8 { a[0].0 }\n",
            "outside the Profile v2 type fragment",
        ),
        (
            "slice-pattern-from-end",
            "pub fn selected(s: &[u8]) -> u8 {\n\
                 match *s {\n\
                     [.., last] => last,\n\
                     [] => 0,\n\
                 }\n\
             }\n",
            "PlaceMention with projections is unsupported",
        ),
        (
            "slice-of-arrays",
            "pub fn selected(s: &[[u8; 2]]) -> usize { s.len() }\n",
            "outside the Profile v2 type fragment",
        ),
        (
            "array-of-refs-partial-eq",
            "pub fn selected<'a>(a: &[&'a u8; 2], b: &[&'a u8; 2]) -> bool { a == b }\n",
            "outside the Profile v2 type fragment",
        ),
        (
            "enum-array-custom-partial-eq",
            "#[repr(u8)] pub enum Tag { A = 0, B = 1 }\n\
             impl PartialEq for Tag { fn eq(&self, _: &Self) -> bool { true } }\n\
             pub fn selected(a: &[Tag; 2], b: &[Tag; 2]) -> bool { *a == *b }\n",
            "unsupported PartialEq::eq types",
        ),
        (
            "wrapper-unsize",
            "pub struct Wrap<T: ?Sized>(pub T);\n\
             pub fn selected<'a>(w: &'a Wrap<[u8; 2]>) -> &'a Wrap<[u8]> { w }\n",
            "unsupported type: Wrap",
        ),
        (
            "rodata-with-provenance",
            "const P: *const u8 = {\n\
                 const INNER: &u8 = &7u8;\n\
                 (&INNER as *const &u8).cast::<u8>()\n\
             };\n\
             pub fn selected() -> *const u8 { P }\n",
            "provenance-bearing global allocation constants are unsupported",
        ),
    ] {
        let fixture = Capture::new(source.as_bytes());
        let output = fixture.selected_command().output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        let reason = failure["unsupported"][0]["reason"]
            .as_str()
            .unwrap_or_default();
        assert!(
            reason.contains(expected_reason),
            "{name}: expected `{expected_reason}` in reason `{reason}` ({failure})"
        );
        fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn captures_panic_strategy_and_assert_unwind_action() {
    let source = b"pub fn selected(a: usize, b: usize) -> usize {\n\
                       a / b\n\
                   }\n";

    let unwind_fix = Capture::new(source);
    let unwind_out = unwind_fix.selected_command().output().unwrap();
    assert!(unwind_out.status.success(), "{unwind_out:?}");
    let unwind_manifest = unwind_fix.manifest();
    assert_eq!(unwind_manifest["program"]["mir_profile_version"], 1);
    assert_eq!(unwind_manifest["program"]["panic"], "unwind");
    assert_eq!(unwind_manifest["program"]["has_local_panic_handler"], false);
    let unwind_lean_path = unwind_fix.output.join("Captured.lean");
    let unwind_lean = std::fs::read_to_string(&unwind_lean_path).unwrap();
    assert!(
        unwind_lean.contains("panicStrategy := Trusted.MirAst.PanicStrategy.unwind"),
        "{unwind_lean}"
    );
    assert!(
        unwind_lean.contains("hasLocalPanicHandler := false"),
        "{unwind_lean}"
    );
    assert!(
        unwind_lean.contains("Trusted.MirAst.UnwindAction.continue_"),
        "{unwind_lean}"
    );
    assert!(
        !unwind_lean.contains("Trusted.MirAst.UnwindAction.unreachable"),
        "{unwind_lean}"
    );
    compile_captured_lean_if_trusted_sources_present(&unwind_lean_path);

    let abort_fix = Capture::new(source);
    let abort_out = abort_fix.selected_command().arg("--panic=abort").output().unwrap();
    assert!(abort_out.status.success(), "{abort_out:?}");
    let abort_manifest = abort_fix.manifest();
    assert_eq!(abort_manifest["program"]["mir_profile_version"], 1);
    assert_eq!(abort_manifest["program"]["panic"], "abort");
    assert_eq!(abort_manifest["program"]["has_local_panic_handler"], false);
    let abort_lean_path = abort_fix.output.join("Captured.lean");
    let abort_lean = std::fs::read_to_string(&abort_lean_path).unwrap();
    assert!(
        abort_lean.contains("panicStrategy := Trusted.MirAst.PanicStrategy.abort"),
        "{abort_lean}"
    );
    assert!(
        abort_lean.contains("hasLocalPanicHandler := false"),
        "{abort_lean}"
    );
    assert!(
        abort_lean.contains("Trusted.MirAst.UnwindAction.unreachable"),
        "{abort_lean}"
    );
    assert!(
        !abort_lean.contains("Trusted.MirAst.UnwindAction.continue_"),
        "{abort_lean}"
    );
    compile_captured_lean_if_trusted_sources_present(&abort_lean_path);

    // A `#![no_std]` binary with a crate-local `#[panic_handler]` records
    // `has_local_panic_handler = true` so Lean keeps failing `Assert`s
    // fail-closed as `.fault .unsupported` even under `--panic=abort`.
    let nostd_div = br#"#![no_std]
#![no_main]

use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    loop {}
}

pub fn div_u64(a: u64, b: u64) -> u64 {
    a / b
}
"#;
    let nostd_fix = Capture::new(nostd_div);
    let nostd_out = nostd_fix
        .command()
        .args(["--crate-type=bin", "--panic=abort", "--select=div_u64"])
        .output()
        .unwrap();
    assert!(nostd_out.status.success(), "{nostd_out:?}");
    let nostd_manifest = nostd_fix.manifest();
    assert_eq!(nostd_manifest["program"]["mir_profile_version"], 1);
    assert_eq!(nostd_manifest["program"]["panic"], "abort");
    assert_eq!(nostd_manifest["program"]["has_local_panic_handler"], true);
    let nostd_lean_path = nostd_fix.output.join("Captured.lean");
    let nostd_lean = std::fs::read_to_string(&nostd_lean_path).unwrap();
    assert!(
        nostd_lean.contains("panicStrategy := Trusted.MirAst.PanicStrategy.abort"),
        "{nostd_lean}"
    );
    assert!(
        nostd_lean.contains("hasLocalPanicHandler := true"),
        "{nostd_lean}"
    );
    compile_captured_lean_if_trusted_sources_present(&nostd_lean_path);
}

#[test]
fn assert_terminators_for_checked_div_and_rem_capture_and_typecheck_in_lean() {
    let source = br#"
pub fn safe_div_u32(a: u32, b: u32) -> u32 {
    if b == 0 { 0 } else { a / b }
}

pub fn safe_rem_u32(a: u32, b: u32) -> u32 {
    if b == 0 { 0 } else { a % b }
}

pub fn checked_div_i32(a: i32, b: i32) -> i32 {
    a / b
}

pub fn checked_rem_i32(a: i32, b: i32) -> i32 {
    a % b
}
"#;
    let fixture = Capture::new(source);
    let output =
        fixture.command().args(["--scope=crate", "--panic=unwind"]).output().unwrap();
    assert!(
        output.status.success(),
        "expected assert capture to succeed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = fixture.manifest();
    assert_eq!(manifest["schema_version"], 5);
    assert_eq!(manifest["program"]["mir_profile_version"], 1);
    assert_eq!(manifest["program"]["panic"], "unwind");
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 4);

    let captured_lean = fixture.output.join("Captured.lean");
    let lean_text = std::fs::read_to_string(&captured_lean).unwrap();
    for expected in [
        "panicStrategy := Trusted.MirAst.PanicStrategy.unwind",
        "Trusted.MirAst.TerminatorKind.assert",
        "Trusted.MirAst.AssertKind.divByZero",
        "Trusted.MirAst.AssertKind.remByZero",
        "(Trusted.MirAst.AssertKind.overflow Trusted.MirAst.BinOp.div)",
        "(Trusted.MirAst.AssertKind.overflow Trusted.MirAst.BinOp.rem)",
        "Trusted.MirAst.UnwindAction.continue_",
    ] {
        assert!(
            lean_text.contains(expected),
            "missing {expected} in emitted Captured.lean:\n{lean_text}"
        );
    }

    compile_captured_lean_if_trusted_sources_present(&captured_lean);
}

#[test]
fn fake_for_ptr_metadata_admits_safe_mut_slice_patterns_and_refuses_real_raw_ptr_mixing() {
    let safe_mut_slice_source = br#"#![no_std]
#![forbid(unsafe_code)]

pub fn is_empty_mut_slice(s: &mut [u8]) -> bool {
    matches!(s, [])
}

pub fn classify_mut_slice(s: &mut [u16], out: &mut u8) -> usize {
    match s {
        [] => {
            *out = 0;
            0
        }
        [_] => {
            *out = 1;
            1
        }
        [_, _, ..] => {
            *out = 2;
            s.len()
        }
    }
}

pub fn two_mut_slice_pats(a: &mut [u8], b: &mut [u32], v: u32) -> u32 {
    if matches!(a, []) && matches!(b, [_]) { v } else { 0 }
}
"#;
    let ok_fix = Capture::new(safe_mut_slice_source);
    let ok_out = ok_fix.command().arg("--scope=crate").output().unwrap();
    assert!(
        ok_out.status.success(),
        "expected safe &mut [T] slice pattern functions to capture cleanly:\n{}\n{}",
        stdout(&ok_out),
        stderr(&ok_out)
    );
    let manifest = ok_fix.manifest();
    assert_eq!(manifest["program"]["mir_profile_version"], 2);
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 3);
    let manifest_str = manifest.to_string();
    assert!(
        manifest_str.contains("\"fake_address_of\""),
        "expected FakeAddressOf in capture.json, got {manifest_str}"
    );
    let lean_path = ok_fix.output.join("Captured.lean");
    let lean_src = std::fs::read_to_string(&lean_path).unwrap();
    assert!(
        lean_src.contains("Trusted.MirAst.Rvalue.fakeAddressOf"),
        "{lean_src}"
    );
    compile_captured_lean_if_trusted_sources_present(&lean_path);

    // Real raw-pointer locals mixed with `&mut [u8]` (even alongside a valid
    // `FakeForPtrMetadata` slice pattern) must still fail closed with the
    // mixed-locals refusal.
    for (name, bad_src) in [
        (
            "mut_slice_to_raw_cast",
            &b"#![no_std]\npub fn f(s: &mut [u8]) -> *const [u8] { s as *const [u8] }\n"[..],
        ),
        (
            "mut_slice_pat_plus_raw_borrow",
            &b"#![no_std]\npub fn f(s: &mut [u8], x: u8) -> bool {\n    let p = &raw const x;\n    let _ = p;\n    matches!(s, [])\n}\n"[..],
        ),
        (
            "mut_slice_pat_plus_raw_param",
            &b"#![no_std]\npub unsafe fn f(s: &mut [u8], p: *const u8) -> u8 {\n    if matches!(s, []) { 0 } else { unsafe { *p } }\n}\n"[..],
        ),
    ] {
        let bad_fix = Capture::new(bad_src);
        let bad_out = bad_fix.command().arg("--scope=crate").output().unwrap();
        assert_eq!(bad_out.status.code(), Some(1), "{name}: {bad_out:?}");
        let failure = status(&bad_out);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure
                .to_string()
                .contains("body mixes reference and raw-pointer locals"),
            "{name}: expected mixed-locals refusal, got {failure}"
        );
        bad_fix.assert_no_capture_artifacts();
    }

    // Safe `&mut [u8]` indexing (`buf[0] = v`, issue #4426) synthesizes a
    // `FakeForPtrMetadata` temporary for its bounds check. It must not fail
    // with the misleading mixed-locals error, and now that Profile v2
    // supports `Index` projections, it captures and typechecks.
    let idx_fix = Capture::new(
        b"#![no_std]\n#![forbid(unsafe_code)]\npub fn set_first(buf: &mut [u8], v: u8) {\n    buf[0] = v;\n}\n",
    );
    let idx_out = idx_fix.command().arg("--scope=crate").output().unwrap();
    assert!(
        idx_out.status.success(),
        "set_first: expected capture to succeed:\n{}\n{}",
        stdout(&idx_out),
        stderr(&idx_out)
    );
    let idx_manifest = idx_fix.manifest();
    assert_eq!(idx_manifest["program"]["mir_profile_version"], 2);
    let idx_manifest_str = idx_manifest.to_string();
    assert!(
        idx_manifest_str.contains("\"fake_address_of\"")
            && idx_manifest_str.contains("\"kind\":\"index\""),
        "set_first: expected FakeAddressOf and Index in capture.json, got {idx_manifest_str}"
    );
    compile_captured_lean_if_trusted_sources_present(&idx_fix.output.join("Captured.lean"));
}

#[test]
fn captures_core_contracts_range_scalar_slice_mem_and_option() {
    let src = b"\
        pub fn slice_ranges<'a>(s: &'a [u8], a: usize, b: usize) -> (&'a [u8], &'a [u8]) {\n\
            (&s[a..b], &s[a..])\n\
        }\n\
        pub fn slice_range_mut<'a>(s: &'a mut [u8], a: usize, b: usize) -> &'a mut [u8] {\n\
            &mut s[a..b]\n\
        }\n\
        pub fn scalar_contracts(a: u64, b: u64, s: u32, x: usize, y: usize) -> (bool, usize, u64, u32, (u64, bool)) {\n\
            let m = a.is_multiple_of(b) && x.is_multiple_of(8) && (s.is_multiple_of(2));\n\
            let sat = x.saturating_add(y);\n\
            let mn = core::cmp::min(x, y);\n\
            let w = a.wrapping_shl(s) ^ a.wrapping_shr(s);\n\
            let lz = a.leading_zeros();\n\
            let (_, ov) = a.overflowing_sub(b);\n\
            let (sum, c) = a.overflowing_add(b);\n\
            (m, sat ^ mn, w ^ sum, lz, (sum, ov ^ c))\n\
        }\n\
        pub fn checked_and_option(a: usize, b: usize, mut opt: Option<u64>, p: &mut u64) -> (bool, usize, u64) {\n\
            let c1 = a.checked_add(b);\n\
            let c2 = a.checked_mul(2);\n\
            let c3 = a.checked_sub(1);\n\
            let v1 = match c1 { Some(x) => x, None => 0 };\n\
            let v2 = match c2 { Some(y) => y, None => 0 };\n\
            let v3 = match c3 { Some(z) => z, None => 0 };\n\
            let v = v1 ^ v2 ^ v3;\n\
            let was_some = opt.is_some();\n\
            let not_some = opt.is_none();\n\
            let taken = opt.take();\n\
            let old = core::mem::replace(p, 99);\n\
            let made = if was_some && !not_some { Some(old) } else { None };\n\
            let out = match made {\n\
                Some(x) => taken.unwrap() ^ x,\n\
                None => old,\n\
            };\n\
            (was_some, v, out)\n\
        }\n\
        pub fn slice_helpers<'a>(s: &'a [u8], mid: usize) -> (bool, (&'a [u8], &'a [u8])) {\n\
            (s.is_empty(), s.split_at(mid))\n\
        }\n";
    let cap = Capture::new(src);
    let out = cap.command().arg("--scope=crate").output().unwrap();
    assert!(
        out.status.success(),
        "Core contracts capture failed:\n{}\n{}",
        stdout(&out),
        stderr(&out)
    );
    let manifest = cap.manifest();
    assert_eq!(manifest["program"]["mir_profile_version"], 2, "{manifest}");
    let lean = std::fs::read_to_string(cap.output.join("Captured.lean")).unwrap();
    for needle in [
        "MirTy.range",
        "MirTy.option",
        "ProjectionElem.downcast",
        "Rvalue.aggregateRange",
        "Rvalue.aggregateOption",
        "CoreCallOp.sliceIndexRange",
        "CoreCallOp.sliceIndexRangeFrom",
        "CoreCallOp.sliceIsEmpty",
        "CoreCallOp.sliceSplitAt",
        "CoreCallOp.numIsMultipleOf",
        "CoreCallOp.numCheckedAdd",
        "CoreCallOp.numCheckedMul",
        "CoreCallOp.numCheckedSub",
        "CoreCallOp.numSaturatingAdd",
        "CoreCallOp.numWrappingShl",
        "CoreCallOp.numWrappingShr",
        "CoreCallOp.numLeadingZeros",
        "CoreCallOp.numOverflowingAdd",
        "CoreCallOp.numOverflowingSub",
        "CoreCallOp.cmpMin",
        "CoreCallOp.memReplace",
        "CoreCallOp.optionIsSome",
        "CoreCallOp.optionIsNone",
        "CoreCallOp.optionTake",
        "CoreCallOp.optionUnwrap",
    ] {
        assert!(lean.contains(needle), "missing {needle} in:\n{lean}");
    }
}

#[test]
fn rejects_non_zst_integer_pointer_constant_in_profile_v2() {
    let src = b"\
        const BAD_PTR: *const u64 = 2 as *const u64;\n\
        pub fn read_bad_const_ptr() -> *const u64 {\n\
            BAD_PTR\n\
        }\n";
    let cap = Capture::new(src);
    let out = cap.command().arg("--scope=crate").output().unwrap();
    assert!(
        !out.status.success(),
        "expected non-ZST integer pointer constant to fail closed:\nstdout={}\nstderr={}",
        stdout(&out),
        stderr(&out)
    );
}

#[test]
fn captures_static_str_core_panicking_calls_and_refuses_panic_fmt() {
    let positive = br#"#![no_std]
pub fn assert_plain(c: bool) {
    assert!(c);
}
pub fn panic_plain() -> u32 {
    panic!();
}
pub fn unreachable_branch(c: bool) -> u32 {
    if c { 1 } else { unreachable!() }
}
pub fn ebpf_insn_new(code: u8, dst: u8, src: u8, offset: i16, imm: i32) -> u64 {
    assert!(dst < 16);
    assert!(src < 16);
    (code as u64)
        | ((dst as u64) << 8)
        | ((src as u64) << 12)
        | ((offset as u16 as u64) << 16)
        | ((imm as u32 as u64) << 32)
}
"#;
    let fix = Capture::new(positive);
    let out = fix
        .command()
        .args(["--panic=abort", "--scope=crate"])
        .output()
        .unwrap();
    assert!(out.status.success(), "{out:?}");
    let manifest = fix.manifest();
    assert_eq!(manifest["program"]["mir_profile_version"], 2);
    assert_eq!(manifest["program"]["panic"], "abort");
    let lean_path = fix.output.join("Captured.lean");
    let lean = std::fs::read_to_string(&lean_path).unwrap();
    let panic_count = lean
        .matches("Trusted.MirAst.CoreCallOp.panicAbort [")
        .count();
    assert_eq!(
        panic_count, 5,
        "expected all 5 static-&str panic/assert calls to lower to CoreCallOp.panicAbort:\n{lean}"
    );
    assert!(
        lean.contains("Trusted.MirAst.MirTy.str")
            && lean.contains("Trusted.MirAst.ConstLit.rodataRef")
            && !lean.contains("TerminatorKind.unsupported"),
        "static-&str core::panicking calls must preserve their &str rodataRef operand:\n{lean}"
    );
    compile_captured_lean_if_trusted_sources_present(&lean_path);

    // Rust 2015 `panic!("boom")` expands directly to
    // `core::panicking::panic("boom")` with a non-default `&'static str`
    // literal, exercising UTF-8 byte capture on arbitrary static messages.
    let panic_2015 = br#"#![no_std]
pub fn panic_2015_boom() -> u32 {
    panic!("boom");
}
"#;
    let fix_2015 = Capture::new(panic_2015);
    let out_2015 = fix_2015
        .command()
        .args(["--edition=2015", "--panic=abort", "--scope=crate"])
        .output()
        .unwrap();
    assert!(out_2015.status.success(), "{out_2015:?}");
    let lean_2015_path = fix_2015.output.join("Captured.lean");
    let lean_2015 = std::fs::read_to_string(&lean_2015_path).unwrap();
    assert!(
        lean_2015.contains("Trusted.MirAst.CoreCallOp.panicAbort [")
            && lean_2015.contains("RodataByte.init 98")
            && lean_2015.contains("RodataByte.init 109")
            && lean_2015.contains("(some 4)"),
        "expected 4-byte \"boom\" rodataRef &str operand:\n{lean_2015}"
    );
    compile_captured_lean_if_trusted_sources_present(&lean_2015_path);

    // Shared `&str` is also admitted as a Profile v2 parameter/local type,
    // while `&mut str`, `*const str`, and `*mut str` fail closed at capture.
    let str_local_src = br#"#![no_std]
pub fn str_id<'a>(s: &'a str) -> &'a str {
    s
}
"#;
    let str_local_fix = Capture::new(str_local_src);
    let str_local_out = str_local_fix
        .command()
        .args(["--panic=abort", "--scope=crate"])
        .output()
        .unwrap();
    assert!(
        str_local_out.status.success(),
        "shared &str parameter/local must capture cleanly:\n{}\n{}",
        stdout(&str_local_out),
        stderr(&str_local_out)
    );
    let str_local_lean_path = str_local_fix.output.join("Captured.lean");
    let str_local_lean = std::fs::read_to_string(&str_local_lean_path).unwrap();
    assert!(
        str_local_lean.contains(
            "Trusted.MirAst.MirTy.ref \
             Trusted.MirAst.Mutability.shared Trusted.MirAst.MirTy.str"
        ),
        "{str_local_lean}"
    );
    compile_captured_lean_if_trusted_sources_present(&str_local_lean_path);

    for (label, bad_str_src) in [
        ("mut_str_ref", &b"#![no_std]\npub fn f<'a>(s: &'a mut str) -> &'a mut str { s }\n"[..]),
        ("const_str_ptr", &b"#![no_std]\npub fn f(s: *const str) -> *const str { s }\n"[..]),
        ("mut_str_ptr", &b"#![no_std]\npub fn f(s: *mut str) -> *mut str { s }\n"[..]),
    ] {
        let bad_fix = Capture::new(bad_str_src);
        let bad_out = bad_fix
            .command()
            .args(["--panic=abort", "--scope=crate"])
            .output()
            .unwrap();
        assert!(
            !bad_out.status.success(),
            "{label} must fail closed at capture: {bad_out:?}"
        );
    }

    // All `panic_fmt` / `core::fmt::Arguments` forms — custom
    // `assert!(c, "msg")`, Rust 2021 `panic!("boom")`, and runtime formatted
    // `assert!(c, "x={}", x)` — must fail closed at capture without retyping
    // locals or erasing calls.
    for (label, src) in [
        ("assert_custom_msg", &b"pub fn f(c: bool) { assert!(c, \"bad cond\"); }\n"[..]),
        ("panic_2021_msg", &b"pub fn f() -> u32 { panic!(\"boom\") }\n"[..]),
        ("assert_runtime_fmt", &b"pub fn f(c: bool, x: u32) { assert!(c, \"x={}\", x); }\n"[..]),
    ] {
        let fmt_fix = Capture::new(src);
        let fmt_out = fmt_fix
            .command()
            .args(["--panic=abort", "--scope=crate"])
            .output()
            .unwrap();
        assert!(
            !fmt_out.status.success(),
            "{label} must fail closed at capture: {fmt_out:?}"
        );
        assert!(
            status(&fmt_out).to_string().contains("Arguments"),
            "{label} must refuse core::fmt::Arguments local: {:?}",
            status(&fmt_out)
        );
    }

    // Local spoof of `core::panicking::panic` must never lower to
    // `CoreCallOp.panicAbort`. The spoof takes the same `&'static str`
    // operand as the real function, so only the sysroot-`core` callee pinning
    // (not the operand-type check) can reject it.
    let spoof = br#"#![no_std]
mod core {
    pub mod panicking {
        pub fn panic(_msg: &'static str) -> ! {
            loop {}
        }
    }
}
pub fn call_spoof(c: bool) {
    if !c {
        self::core::panicking::panic("spoof");
    }
}
"#;
    let spoof_fix = Capture::new(spoof);
    let spoof_out = spoof_fix
        .command()
        .args(["--panic=abort", "--select=call_spoof"])
        .output()
        .unwrap();
    assert!(spoof_out.status.success(), "{spoof_out:?}");
    let spoof_lean = spoof_fix.lean_source();
    assert!(
        !spoof_lean.contains("CoreCallOp.panicAbort")
            && spoof_lean.contains("TerminatorKind.unsupported"),
        "local core::panicking spoof must stay TerminatorKind.unsupported:\n{spoof_lean}"
    );

    // Under default `--panic=unwind`, `core::panicking::panic` and
    // `panic_nounwind` calls stay `TerminatorKind.unsupported` instead of
    // lowering to Profile v2 `CoreCall`, so Profile v1 programs with
    // intra-crate calls remain Profile v1; `assert!(c, "bad cond")` still
    // fails closed at capture.
    let v1_unwind = br#"#![no_std]
fn helper(x: u32) -> u32 {
    x.wrapping_add(1)
}
pub fn assert_plain_v1(c: bool, x: u32) -> u32 {
    assert!(c);
    helper(x)
}
pub fn unreachable_v1(c: bool, x: u32) -> u32 {
    if c { helper(x) } else { unreachable!() }
}
pub fn panic_plain_v1() -> u32 {
    panic!();
}
"#;
    let unwind_fix = Capture::new(v1_unwind);
    let unwind_out = unwind_fix
        .command()
        .args(["--scope=crate"])
        .output()
        .unwrap();
    assert!(
        unwind_out.status.success(),
        "Profile v1 crate with intra-crate calls + panic/unreachable \
         must stay Profile v1 under --panic=unwind:\n{}\n{}",
        stdout(&unwind_out),
        stderr(&unwind_out)
    );
    let unwind_manifest = unwind_fix.manifest();
    assert_eq!(unwind_manifest["program"]["mir_profile_version"], 1, "{unwind_manifest}");
    assert_eq!(unwind_manifest["program"]["panic"], "unwind", "{unwind_manifest}");
    let unwind_lean_path = unwind_fix.output.join("Captured.lean");
    let unwind_lean = std::fs::read_to_string(&unwind_lean_path).unwrap();
    assert!(
        !unwind_lean.contains("CoreCallOp.panicAbort")
            && unwind_lean.contains("TerminatorKind.unsupported"),
        "unwind capture must keep core::panicking calls as \
         TerminatorKind.unsupported:\n{unwind_lean}"
    );
    compile_captured_lean_if_trusted_sources_present(&unwind_lean_path);

    let unwind_fmt = br#"#![no_std]
pub fn assert_msg(c: bool) {
    assert!(c, "bad cond");
}
"#;
    let unwind_fmt_fix = Capture::new(unwind_fmt);
    let unwind_fmt_out = unwind_fmt_fix
        .command()
        .args(["--scope=crate"])
        .output()
        .unwrap();
    assert!(
        !unwind_fmt_out.status.success(),
        "assert!(c, \"msg\") under --panic=unwind must stay refused at capture: {unwind_fmt_out:?}"
    );

    // A `#![no_std]` binary with a crate-local `#[panic_handler]` also keeps
    // `core::panicking::*` calls unlowered under `--panic=abort`, preserving
    // Profile v1 for intra-crate calls and refusing `core::fmt::Arguments`.
    let lh_v1 = br#"#![no_std]
#![no_main]
use core::panic::PanicInfo;
#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    loop {}
}
fn helper(x: u32) -> u32 {
    x.wrapping_add(1)
}
pub fn assert_plain_lh(c: bool, x: u32) -> u32 {
    assert!(c);
    helper(x)
}
"#;
    let lh_v1_fix = Capture::new(lh_v1);
    let lh_v1_out = lh_v1_fix
        .command()
        .args(["--crate-type=bin", "--panic=abort", "--select=assert_plain_lh"])
        .output()
        .unwrap();
    assert!(
        lh_v1_out.status.success(),
        "local #[panic_handler] crate with intra-crate call + assert!(c) \
         must stay Profile v1:\n{}\n{}",
        stdout(&lh_v1_out),
        stderr(&lh_v1_out)
    );
    let lh_v1_manifest = lh_v1_fix.manifest();
    assert_eq!(lh_v1_manifest["program"]["mir_profile_version"], 1, "{lh_v1_manifest}");
    assert_eq!(lh_v1_manifest["program"]["has_local_panic_handler"], true, "{lh_v1_manifest}");
    let lh_v1_lean_path = lh_v1_fix.output.join("Captured.lean");
    let lh_v1_lean = std::fs::read_to_string(&lh_v1_lean_path).unwrap();
    assert!(
        !lh_v1_lean.contains("CoreCallOp.panicAbort")
            && lh_v1_lean.contains("TerminatorKind.unsupported"),
        "local #[panic_handler] capture must keep core::panicking calls unlowered:\n{lh_v1_lean}"
    );
    compile_captured_lean_if_trusted_sources_present(&lh_v1_lean_path);

    let lh_fmt = br#"#![no_std]
#![no_main]
use core::panic::PanicInfo;
#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    loop {}
}
pub fn assert_msg_lh(c: bool) {
    assert!(c, "bad cond");
}
"#;
    let lh_fmt_fix = Capture::new(lh_fmt);
    let lh_fmt_out = lh_fmt_fix
        .command()
        .args(["--crate-type=bin", "--panic=abort", "--select=assert_msg_lh"])
        .output()
        .unwrap();
    assert!(
        !lh_fmt_out.status.success(),
        "assert!(c, \"msg\") with local #[panic_handler] must stay \
         refused at capture: {lh_fmt_out:?}"
    );
}

#[test]
fn preserves_primitive_divisor_asserts_verbatim_in_profile_v1() {
    let div_src = br#"#![no_std]
pub fn udiv16(x: u64) -> u64 {
    x / 16
}
pub fn urem16(x: u64) -> u64 {
    x % 16
}
pub fn idiv16(x: i64) -> i64 {
    x / 16
}
pub fn irem16(x: i64) -> i64 {
    x % 16
}
pub fn const_div(x: u64) -> u64 {
    const D: u64 = 16;
    x / D
}
#[allow(unconditional_panic)]
pub fn div_zero(x: u64) -> u64 {
    x / 0
}
pub fn div_neg_one(x: i64) -> i64 {
    x / -1
}
pub fn div_var(x: u64, d: u64) -> u64 {
    x / d
}
"#;
    let div_fix = Capture::new(div_src);
    let div_out = div_fix
        .command()
        .args(["--panic=abort", "--scope=crate"])
        .output()
        .unwrap();
    assert!(div_out.status.success(), "{div_out:?}");
    let div_manifest = div_fix.manifest();
    assert_eq!(
        div_manifest["program"]["mir_profile_version"], 1,
        "primitive divisor Asserts stay on Profile v1 without CFG folding: {div_manifest}"
    );
    let div_lean_path = div_fix.output.join("Captured.lean");
    let div_lean = std::fs::read_to_string(&div_lean_path).unwrap();
    assert!(
        div_lean.contains("AssertKind.divByZero")
            && div_lean.contains("AssertKind.remByZero")
            && div_lean.contains("AssertKind.overflow Trusted.MirAst.BinOp.div")
            && div_lean.contains("AssertKind.overflow Trusted.MirAst.BinOp.rem"),
        "all primitive divisor Asserts must be captured verbatim:\n{div_lean}"
    );
    compile_captured_lean_if_trusted_sources_present(&div_lean_path);
}

#[test]
fn captures_profile_v2_vec_and_box_operations_under_panic_abort() {
    let alloc_src = br#"
        use core::ops::{Deref, DerefMut};

        pub fn vec_with_cap_and_reserve(cap: usize) -> (usize, usize, Vec<u8>) {
            let mut v: Vec<u8> = Vec::with_capacity(cap);
            v.reserve(4);
            v.push(1);
            let n = v.len();
            let sl_len = DerefMut::deref_mut(&mut v).len();
            (n, sl_len, v)
        }

        pub fn vec_full_ops_to_box(ext: &[u8]) -> (usize, u8, Box<[u8]>, Box<[u8]>) {
            let mut v: Vec<u8> = Vec::new();
            v.push(10);
            v.push(20);
            v.resize(4, 7);
            v.extend_from_slice(ext);
            let x0 = v[0];
            v[1] = 42;
            let _sl: &[u8] = v.deref();
            let b: Box<[u8]> = Box::from(v);
            let c: Box<[u8]> = b.clone();
            let b_sl: &[u8] = &*b;
            let n = b_sl.len();
            let d_sl: &[u8] = Deref::deref(&c);
            let _m = d_sl.len();
            (n, x0, b, c)
        }

        pub fn box_new_and_deref(x: u64) -> (u64, Box<u64>) {
            let b: Box<u64> = Box::new(x);
            let y = *b;
            (y, b)
        }

        pub fn box_and_slice_shared_len(s: &[u8], b: &Box<[u8]>) -> (usize, usize) {
            (s.len(), b.len())
        }
    "#;
    let fixture = Capture::new(alloc_src);
    let out = fixture
        .command()
        .args(["--panic=abort", "--scope=crate"])
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "Profile v2 Vec/Box capture should succeed under --panic=abort:\n{}\n{}",
        stdout(&out),
        stderr(&out)
    );
    let manifest = fixture.manifest();
    assert_eq!(manifest["program"]["mir_profile_version"], 2, "{manifest}");
    assert_eq!(manifest["configuration"]["panic"], "abort", "{manifest}");
    let lean = std::fs::read_to_string(fixture.output.join("Captured.lean")).unwrap();
    for needle in [
        "MirTy.vec",
        "MirTy.box",
        "CastKind.boxAsRef",
        "CoreCallOp.vecNew",
        "CoreCallOp.vecWithCapacity",
        "CoreCallOp.vecLen",
        "CoreCallOp.vecPush",
        "CoreCallOp.vecResize",
        "CoreCallOp.vecExtendFromSlice",
        "CoreCallOp.vecIndex",
        "CoreCallOp.vecIndexMut",
        "CoreCallOp.vecDeref",
        "CoreCallOp.vecDerefMut",
        "CoreCallOp.vecReserve",
        "CoreCallOp.boxFromVec",
        "CoreCallOp.boxDeref",
        "CoreCallOp.boxClone",
        "CoreCallOp.boxNew",
    ] {
        assert!(lean.contains(needle), "missing {needle} in Captured.lean:\n{lean}");
    }
}

#[test]
fn profile_v2_refuses_nested_and_unsupported_vec_box_shapes() {
    for (name, source) in [
        (
            "vec-of-ref",
            "pub fn selected<'a>(v: Vec<&'a u8>) -> usize { v.len() }\n",
        ),
        (
            "box-of-ref",
            "pub fn selected<'a>(b: Box<&'a u8>) -> u8 { **b }\n",
        ),
        (
            "nested-vec",
            "pub fn selected(v: Vec<Vec<u8>>) -> usize { v.len() }\n",
        ),
        (
            "non-box-transmute",
            "pub unsafe fn selected(v: Vec<u8>) -> [u8; 24] {\n\
                 unsafe { core::mem::transmute::<Vec<u8>, [u8; 24]>(v) }\n\
             }\n",
        ),
    ] {
        let fixture = Capture::new(source.as_bytes());
        let output = fixture
            .selected_command()
            .arg("--panic=abort")
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        fixture.assert_no_capture_artifacts();
    }
}

/// Rust leaves the layout of `Vec` unspecified, so raw pointers to `Vec` or
/// `Box` handles (which could reinterpret the model's handle encoding) are
/// refused, as is `Vec` indexing by anything other than `usize`.
#[test]
fn profile_v2_refuses_vec_box_handle_raw_pointers_and_non_usize_index() {
    for (name, source, needle) in [
        (
            "vec-handle-reinterpret",
            "pub fn selected(v: Vec<u8>) -> (usize, Vec<u8>) {\n\
                 let x = unsafe { *(&raw const v as *const usize) };\n\
                 (x, v)\n\
             }\n",
            "outside the Profile v2 type fragment",
        ),
        (
            "box-handle-raw-ptr",
            "pub fn selected(b: Box<u8>) -> u8 {\n\
                 let p = &raw const b;\n\
                 unsafe { **p }\n\
             }\n",
            "outside the Profile v2 type fragment",
        ),
        (
            "vec-range-index",
            "pub fn selected(v: &Vec<u8>) -> usize { v[1..].len() }\n",
            "non-`usize` index type",
        ),
    ] {
        let fixture = Capture::new(source.as_bytes());
        let output = fixture
            .selected_command()
            .arg("--panic=abort")
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(failure.to_string().contains(needle), "{name}: {failure}");
        fixture.assert_no_capture_artifacts();
    }
}

/// `Vec::extend_from_slice`, `Vec::resize`, and `Box::clone` are modeled as
/// bitwise element copies, which matches Rust only for `TrivialClone`
/// elements. An enum with a hand-written `Clone` that returns another variant
/// is refused for each operation (`Box<T>` and `Box<[T]>` clones included),
/// with or without `#[derive(Copy)]`; the same enum with
/// `#[derive(Clone, Copy)]` is admitted.
#[test]
fn profile_v2_clone_based_alloc_ops_require_trivial_clone_elements() {
    let manual = "pub enum E { A, B }\n\
                  impl Clone for E { fn clone(&self) -> E { E::B } }\n";
    let derived = "#[derive(Clone, Copy)]\npub enum E { A, B }\n";
    let ops = [
        (
            "extend-from-slice",
            "pub fn selected(v: &mut Vec<E>, s: &[E]) { v.extend_from_slice(s) }\n",
        ),
        (
            "resize",
            "pub fn selected(v: &mut Vec<E>, x: E) { v.resize(3, x) }\n",
        ),
        (
            "box-clone",
            "pub fn selected(b: &Box<E>) -> Box<E> { b.clone() }\n",
        ),
        (
            "boxed-slice-clone",
            "pub fn selected(b: &Box<[E]>) -> Box<[E]> { b.clone() }\n",
        ),
    ];
    // `Copy` with a hand-written `Clone` is not `TrivialClone` either.
    let copy_manual = "#[derive(Copy)]\npub enum E { A, B }\n\
                       impl Clone for E { fn clone(&self) -> E { E::B } }\n";
    for (name, body) in ops {
        for prefix in [manual, copy_manual] {
            let refused = Capture::new(format!("{prefix}{body}").as_bytes());
            let output = refused.selected_command().arg("--panic=abort").output().unwrap();
            assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
            let failure = status(&output);
            assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
            assert!(
                failure.to_string().contains("which is not `TrivialClone`"),
                "{name}: {failure}"
            );
            refused.assert_no_capture_artifacts();
        }

        let admitted = Capture::new(format!("{derived}{body}").as_bytes());
        let out = admitted.selected_command().arg("--panic=abort").output().unwrap();
        assert!(
            out.status.success(),
            "{name}: derived Clone + Copy element should be admitted:\n{}\n{}",
            stdout(&out),
            stderr(&out)
        );
    }
}

/// Slices of every scalar element type are admitted local types, but the
/// modeled slice functions such as `<[T]>::len` still require integer
/// elements.
#[test]
fn profile_v2_admits_scalar_slices_but_slice_len_requires_int_elements() {
    let admitted = Capture::new(
        b"pub fn selected<'a>(s: &'a [bool]) -> &'a [bool] { s }\n",
    );
    let out = admitted.selected_command().arg("--panic=abort").output().unwrap();
    assert!(out.status.success(), "{}\n{}", stdout(&out), stderr(&out));
    let manifest = admitted.manifest();
    assert_eq!(manifest["program"]["mir_profile_version"], 2, "{manifest}");
    let lean = std::fs::read_to_string(admitted.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("MirTy.slice Trusted.MirAst.MirTy.bool"), "{lean}");

    let refused = Capture::new(b"pub fn selected(s: &[bool]) -> usize { s.len() }\n");
    let output = refused.selected_command().arg("--panic=abort").output().unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    let failure = status(&output);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    refused.assert_no_capture_artifacts();
}

#[test]
fn profile_v2_promotes_box_shared_deref_and_refuses_genuine_box_raw_ptr_mix() {
    let shared_src = br#"
        use core::ops::Deref;

        pub fn slice_and_box_len(s: &[u8], b: &Box<[u8]>) -> (usize, usize, usize) {
            let bs: &[u8] = &**b;
            let bd: &[u8] = b.deref();
            (s.len(), bs.len(), bd.len())
        }

        pub fn ref_and_box_u64(r: &u64, b: &Box<u64>) -> u64 {
            *r + **b
        }
    "#;
    let ok_fixture = Capture::new(shared_src);
    let ok_out = ok_fixture
        .command()
        .args(["--panic=abort", "--scope=crate"])
        .output()
        .unwrap();
    assert!(
        ok_out.status.success(),
        "shared Box deref alongside &T should succeed:\n{}\n{}",
        stdout(&ok_out),
        stderr(&ok_out)
    );
    let ok_lean = std::fs::read_to_string(ok_fixture.output.join("Captured.lean")).unwrap();
    assert!(ok_lean.contains("CastKind.boxAsRef"), "{ok_lean}");
    assert!(!ok_lean.contains("CastKind.boxAsRawPtr"), "{ok_lean}");
    assert!(!ok_lean.contains("MirTy.rawPtr"), "{ok_lean}");

    for (name, bad_src) in [
        (
            "ref-and-box-raw-cast",
            "pub fn selected(s: &[u8], b: &Box<u64>) -> (usize, *const u64) {\n\
                 (s.len(), &**b as *const u64)\n\
             }\n",
        ),
        (
            "ref-and-box-slice-raw-addr",
            "pub fn selected(s: &[u8], b: &Box<[u8]>) -> (usize, *const [u8]) {\n\
                 (s.len(), &raw const **b)\n\
             }\n",
        ),
        // A `Box` counts as a reference, so a raw pointer derived from it mixes
        // even without any `&T` local.
        (
            "box-raw-addr",
            "pub unsafe fn selected(b: Box<u64>) -> (u64, Box<u64>) {\n\
                 let p: *const u64 = &raw const (*b);\n\
                 (unsafe { *p }, b)\n\
             }\n",
        ),
        // Undefined behavior under Stacked and Tree Borrows: the write uses a
        // pointer derived from `b` after `b` was moved, through a `*const` to
        // `*mut` cast.
        (
            "box-write-after-move",
            "pub fn selected() -> Box<u8> {\n\
                 let b = Box::new(1u8);\n\
                 let p = &raw const *b as *mut u8;\n\
                 let c = b;\n\
                 unsafe { *p = 2; }\n\
                 c\n\
             }\n",
        ),
    ] {
        let bad_fixture = Capture::new(bad_src.as_bytes());
        let bad_out = bad_fixture
            .selected_command()
            .arg("--panic=abort")
            .output()
            .unwrap();
        assert_eq!(bad_out.status.code(), Some(1), "{name}: {bad_out:?}");
        let failure = status(&bad_out);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure.to_string().contains("body mixes reference and raw-pointer locals"),
            "{name}: {failure}"
        );
        bad_fixture.assert_no_capture_artifacts();
    }
}

#[test]
fn profile_v2_refuses_local_owned_box_lang_item_under_stdlib_crate() {
    // Under `--stdlib-crate=core` a crate may define its own
    // `#[lang = "owned_box"]` item. Only the sysroot `alloc::boxed::Box` is a
    // modeled `Box`, so this look-alike is an unsupported type.
    let source = b"\
        #![feature(no_core, lang_items, rustc_attrs)]\n\
        #![no_core]\n\
        #![rustc_coherence_is_core]\n\
        #[lang = \"pointee_sized\"] pub trait PointeeSized {}\n\
        #[lang = \"meta_sized\"] pub trait MetaSized: PointeeSized {}\n\
        #[lang = \"sized\"] pub trait Sized: MetaSized {}\n\
        #[lang = \"copy\"] pub trait Copy {}\n\
        impl Copy for u64 {}\n\
        #[lang = \"legacy_receiver\"] pub trait LegacyReceiver: PointeeSized {}\n\
        impl<T: PointeeSized> LegacyReceiver for &T {}\n\
        pub struct NonNull<T: ?Sized>(*const T);\n\
        pub struct Unique<T: ?Sized>(NonNull<T>);\n\
        #[lang = \"owned_box\"] pub struct FakeBox<T: ?Sized>(Unique<T>);\n\
        pub fn selected(_b: &FakeBox<u64>) -> u64 { 0 }\n";
    let fixture = Capture::new(source);
    let output = fixture
        .command_with("core", true)
        .args(["--stdlib-crate=core", "--select=selected", "--panic=abort"])
        .output()
        .unwrap();
    assert_refused("local owned_box lang item", &fixture, &output, "unsupported type");
}

#[test]
fn profile_v2_refuses_local_alloc_vec_look_alike_in_crate_named_alloc() {
    // The local crate is named `alloc` and defines its own `alloc::vec::Vec`.
    // Modeled library items must come from the real `alloc` crate, so this
    // look-alike is an unsupported type rather than a modeled `Vec`.
    let fixture = Capture::new(
        b"pub mod alloc {\n\
              pub mod vec {\n\
                  pub struct Vec<T>(pub T);\n\
                  impl<T> Vec<T> {\n\
                      pub fn new() -> Self where T: Default { Vec(T::default()) }\n\
                  }\n\
              }\n\
          }\n\
          pub fn selected() -> alloc::vec::Vec<u8> { alloc::vec::Vec::new() }\n",
    );
    let out = fixture
        .command_with("alloc", true)
        .args(["--select=selected", "--panic=abort"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1), "{out:?}");
    let failure = status(&out);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(failure.to_string().contains("unsupported type: alloc::vec::Vec<u8>"), "{failure}");
    fixture.assert_no_capture_artifacts();
}

fn body_terminator_kinds(manifest: &Value, identity: &str) -> Vec<String> {
    let body = manifest["program"]["bodies"]
        .as_array()
        .unwrap()
        .iter()
        .find(|body| body["identity"] == identity)
        .unwrap_or_else(|| panic!("missing body {identity} in {manifest}"));
    body["blocks"]
        .as_array()
        .unwrap()
        .iter()
        .map(|block| block["terminator"]["kind"].as_str().unwrap().to_owned())
        .collect()
}

#[test]
fn profile_v2_captures_structs_index_projections_and_intra_crate_calls() {
    let src = b"\
        #[derive(Clone, Copy, PartialEq)]\n\
        pub struct Pair { pub a: u8, pub b: u32 }\n\
        pub struct Unit;\n\
        pub struct Nested { pub pair: Pair, pub tag: u16, pub bytes: [u8; 3] }\n\
        pub struct Overrides(pub u8);\n\
        impl PartialEq for Overrides {\n\
            fn eq(&self, other: &Self) -> bool { self.0 == other.0 }\n\
            fn ne(&self, other: &Self) -> bool { self.0 != other.0 }\n\
        }\n\
        pub const ORIGIN: Pair = Pair { a: 1, b: 2 };\n\
        fn helper(x: u32) -> u32 { x ^ 1 }\n\
        pub fn make_pair(a: u8, b: u32) -> Pair { Pair { a, b: helper(b) } }\n\
        pub fn nest(pair: Pair) -> Nested { Nested { pair, tag: 7, bytes: [1, 2, 3] } }\n\
        pub fn get_b(p: Pair) -> u32 { p.b }\n\
        pub fn origin_b() -> u32 { ORIGIN.b }\n\
        pub const UNIT: Unit = Unit;\n\
        pub fn unit() -> Unit { Unit }\n\
        pub fn unit_const() -> Unit { UNIT }\n\
        pub fn index(arr: [u8; 4], i: usize) -> u8 { arr[i] }\n\
        pub fn index_pairs(arr: &[Pair; 2], i: usize) -> u8 { arr[i].a }\n\
        pub fn index_slice(s: &[u8], i: usize) -> u8 { s[i] }\n\
        pub fn differ(x: &Pair, y: &Pair) -> bool { *x != *y }\n\
        pub fn overridden(x: &Overrides, y: &Overrides) -> bool { *x != *y }\n\
        pub fn array_ne(a: &[u8; 4], b: &[u8; 4]) -> bool { *a != *b }\n";
    let cap = Capture::new(src);
    let out = cap.command().arg("--scope=crate").output().unwrap();
    assert!(
        out.status.success(),
        "struct/index/call crate capture should succeed:\n{}\n{}",
        stdout(&out),
        stderr(&out)
    );
    let manifest = cap.manifest();
    assert_eq!(manifest["program"]["mir_profile_version"], 2, "{manifest}");
    let lean = std::fs::read_to_string(cap.output.join("Captured.lean")).unwrap();
    for needle in [
        "Trusted.MirAst.MirTy.struct_ (Trusted.MirAst.StructLayout.mk ",
        "Trusted.MirAst.Rvalue.aggregateStruct",
        "Trusted.MirAst.ProjectionElem.index",
        "Trusted.MirAst.TerminatorKind.call\n",
        "Trusted.MirAst.TerminatorKind.callNe\n",
        "Trusted.MirAst.CoreCallOp.partialEqNe",
        "Trusted.MirAst.ConstLit.rodataBytes",
        "Trusted.MirAst.ConstLit.zeroSized",
    ] {
        assert!(lean.contains(needle), "missing {needle}:\n{lean}");
    }
    assert!(body_terminator_kinds(&manifest, "rust-path-v1::make_pair").contains(&"call".into()));
    assert!(body_terminator_kinds(&manifest, "rust-path-v1::differ").contains(&"call_ne".into()));
    let overridden = body_terminator_kinds(&manifest, "rust-path-v1::overridden");
    assert!(overridden.contains(&"call".into()), "{overridden:?}");
    assert!(!overridden.contains(&"call_ne".into()), "{overridden:?}");
    assert!(
        body_terminator_kinds(&manifest, "rust-path-v1::array_ne").contains(&"core_call".into())
    );
    // Every call names the captured body it executes.
    let bodies = manifest["program"]["bodies"].as_array().unwrap();
    let helper_index =
        bodies.iter().position(|body| body["identity"] == "rust-path-v1::helper").unwrap();
    let make_pair =
        bodies.iter().find(|body| body["identity"] == "rust-path-v1::make_pair").unwrap();
    assert!(
        make_pair["blocks"].as_array().unwrap().iter().any(|block| {
            block["terminator"]["kind"] == "call" && block["terminator"]["callee"] == helper_index
        }),
        "{make_pair}"
    );
}

/// Sharding (more than `shard_min_bodies = 20` bodies) reorders
/// `program.bodies`, and `CallNe::eq_callee` must follow its `eq` body. Here 18
/// `fake_caller_*` helpers push the crate to 21 bodies, and the reorder moves
/// `<Tag as AaaFake>::fake_eq`, which has the same signature as `Tag::eq` but
/// returns `false`, into the slot `Tag::eq` had before. A stale `eq_callee`
/// therefore still type-checks and would make `Tag::A != Tag::A` evaluate to
/// `true`.
#[test]
fn profile_v2_sharded_capture_keeps_call_ne_bound_to_partial_eq_eq() {
    let mut src = String::from(
        "pub enum Tag { A, B }\n\
         impl PartialEq for Tag {\n\
         \x20   fn eq(&self, other: &Self) -> bool {\n\
         \x20       match (self, other) { (Tag::A, Tag::A) | (Tag::B, Tag::B) => true, _ => false }\n\
         \x20   }\n\
         }\n\
         pub trait AaaFake { fn fake_eq(&self, other: &Self) -> bool; }\n\
         impl AaaFake for Tag { fn fake_eq(&self, _: &Self) -> bool { false } }\n\
         pub fn tag_ne(x: Tag, y: Tag) -> bool { x != y }\n",
    );
    for i in 0..18 {
        let _ = writeln!(
            src,
            "pub fn fake_caller_{i:02}(x: &Tag, y: &Tag) -> bool {{ \
             <Tag as AaaFake>::fake_eq(x, y) }}"
        );
    }
    let cap = Capture::new(src.as_bytes());
    let out = cap.command().arg("--scope=crate").output().unwrap();
    assert!(
        out.status.success(),
        "sharded witness capture should succeed:\n{}\n{}",
        stdout(&out),
        stderr(&out)
    );
    let shards: Value = serde_json::from_slice(
        &std::fs::read(cap.output.join("capture_shards.json")).expect("sharded capture"),
    )
    .unwrap();
    assert_eq!(shards["total_bodies"], 21, "{shards}");
    let manifest = cap.manifest();
    let bodies = manifest["program"]["bodies"].as_array().unwrap();
    assert_eq!(bodies.len(), 21, "{manifest}");
    let index_of = |identity: &str| {
        bodies
            .iter()
            .position(|b| b["identity"] == identity)
            .unwrap_or_else(|| panic!("missing body {identity} in {manifest}"))
    };
    let eq_index = index_of("rust-path-v1::<Tag as core::cmp::PartialEq>::eq");
    let fake_eq_index = index_of("rust-path-v1::<Tag as AaaFake>::fake_eq");
    let call_targets = |identity: &str, kind: &str, field: &str| -> Vec<u64> {
        bodies[index_of(identity)]["blocks"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|block| block["terminator"]["kind"] == kind)
            .map(|block| block["terminator"][field].as_u64().unwrap())
            .collect()
    };
    assert_eq!(
        call_targets("rust-path-v1::tag_ne", "call_ne", "eq_callee"),
        [eq_index as u64],
        "{manifest}"
    );
    for i in 0..18 {
        assert_eq!(
            call_targets(&format!("rust-path-v1::fake_caller_{i:02}"), "call", "callee"),
            [fake_eq_index as u64],
            "{manifest}"
        );
    }
}

#[test]
fn profile_v2_captures_no_drop_glue_drop_terminators_in_instantiations() {
    let src = b"pub fn consume<T>(_x: T) {}\n";
    // Under `panic=abort` the generic body's drop has no cleanup unwind.
    let cap = Capture::new(src);
    let out = cap
        .command()
        .arg("--panic=abort")
        .arg("--instantiate")
        .arg(r#"{"path":"consume","args":["u8"]}"#)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "no-drop-glue Drop capture should succeed:\n{}\n{}",
        stdout(&out),
        stderr(&out)
    );
    let lean = std::fs::read_to_string(cap.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("Trusted.MirAst.TerminatorKind.drop"), "{lean}");
    // The drop's real unwind action is emitted rather than a constant.
    assert!(
        lean.contains("1 Trusted.MirAst.UnwindAction.unreachable)"),
        "{lean}"
    );
    assert!(!lean.contains("Trusted.MirAst.UnwindAction.continue_"), "{lean}");

    // A body that drops a value with a custom `Drop` impl is refused.
    let bad = Capture::new(
        b"pub struct Guard(pub u8);\n\
          impl Drop for Guard { fn drop(&mut self) {} }\n\
          pub fn selected(g: Guard) -> u8 { g.0 }\n",
    );
    let out = bad.selected_command().arg("--panic=abort").output().unwrap();
    assert_eq!(out.status.code(), Some(1), "{out:?}");
    let failure = status(&out);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    assert!(failure.to_string().contains("structs with a Drop impl"), "{failure}");
    bad.assert_no_capture_artifacts();
}

#[test]
fn profile_v2_refuses_unsupported_structs_and_calls() {
    for (name, source, expected) in [
        (
            "drop-struct",
            "pub struct G(pub u8);\nimpl Drop for G { fn drop(&mut self) {} }\n\
             pub fn selected(g: &G) -> u8 { g.0 }\n",
            "structs with a Drop impl are unsupported",
        ),
        (
            "generic-struct",
            "pub struct W<T>(pub T);\npub fn selected(w: W<u8>) -> u8 { w.0 }\n",
            "unsupported type",
        ),
        (
            "lifetime-struct",
            "pub struct R<'a>(pub &'a u8);\npub fn selected(r: R<'_>) -> u8 { *r.0 }\n",
            "unsupported type",
        ),
        (
            "packed-struct",
            "#[repr(packed)] pub struct P { pub a: u8, pub b: u32 }\n\
             pub fn selected(p: P) -> u8 { p.a }\n",
            "packed",
        ),
        (
            "raw-pointer-field",
            "pub struct P(pub *const u8);\npub fn selected(p: P) -> usize { p.0 as usize }\n",
            "outside the Profile v2 data fragment",
        ),
        (
            "generic-callee",
            "fn id<T>(x: T) -> T { x }\npub fn selected(x: u8) -> u8 { id(x) }\n",
            "calls to generic or monomorphized functions",
        ),
    ] {
        let fixture = Capture::new(source.as_bytes());
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
fn profile_v2_refuses_recursive_structs_without_overflow() {
    // Structs that reach themselves through a pointer must fail closed under
    // both `--select` and `--scope=crate` instead of recursing without bound.
    let sources: [(&str, &[u8]); 4] = [
        (
            "self-raw-pointer",
            b"pub struct Node { pub next: *const Node, pub v: u8 }\n\
              pub fn selected(n: &Node) -> u8 { n.v }\n",
        ),
        (
            "self-static-ref",
            b"pub struct Node { pub next: &'static Node, pub v: u8 }\n\
              pub fn selected(n: &Node) -> u8 { n.v }\n",
        ),
        (
            "self-pointer-in-tuple",
            b"pub struct Node { pub link: (*const Node, u8) }\n\
              pub fn selected(n: &Node) -> u8 { n.link.1 }\n",
        ),
        (
            "mutual-raw-pointer",
            b"pub struct A { pub b: *const B, pub v: u8 }\n\
              pub struct B { pub a: *const A }\n\
              pub fn selected(a: &A) -> u8 { a.v }\n",
        ),
    ];
    for (name, source) in sources {
        let selected = Capture::new(source);
        let output = selected.selected_command().output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure.to_string().contains("outside the Profile v2 data fragment"),
            "{name}: {failure}"
        );
        selected.assert_no_capture_artifacts();

        let crate_scope = Capture::new(source);
        let output = crate_scope.command().arg("--scope=crate").output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name} (crate): {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name} (crate): {failure}");
        crate_scope.assert_no_capture_artifacts();
    }

    // Owning `Box`/`Vec` handles do not trip the pointer-field refusal, so
    // recursion through them must hit the re-entry check instead.
    let heap_sources: [(&str, &[u8]); 3] = [
        (
            "self-box",
            b"pub struct List { pub next: Box<List>, pub v: u8 }\n\
              pub fn selected(l: &List) -> u8 { l.v }\n",
        ),
        (
            "self-option-box",
            b"pub struct Node { pub next: Option<Box<Node>>, pub v: u8 }\n\
              pub fn selected(n: &Node) -> u8 { n.v }\n",
        ),
        (
            "self-vec",
            b"pub struct Tree { pub children: Vec<Tree>, pub v: u8 }\n\
              pub fn selected(t: &Tree) -> u8 { t.v }\n",
        ),
    ];
    for (name, source) in heap_sources {
        let selected = Capture::new(source);
        let output = selected.selected_command().output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name}: {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name}: {failure}");
        assert!(
            failure.to_string().contains("recursive struct types are unsupported"),
            "{name}: {failure}"
        );
        selected.assert_no_capture_artifacts();

        let crate_scope = Capture::new(source);
        let output = crate_scope.command().arg("--scope=crate").output().unwrap();
        assert_eq!(output.status.code(), Some(1), "{name} (crate): {output:?}");
        let failure = status(&output);
        assert_eq!(failure["status"], "unsupported", "{name} (crate): {failure}");
        crate_scope.assert_no_capture_artifacts();
    }
}

#[test]
fn profile_v2_captures_struct_index_and_drop_e2e_fixture_crates() {
    let lib = b"\
        #[derive(PartialEq)]\n\
        pub struct Digest(pub [u8; 4]);\n\
        pub struct Pair {\n\
            pub tag: u8,\n\
            pub value: u32,\n\
        }\n\
        pub fn make_pair(tag: u8, value: u32) -> Pair {\n\
            Pair { tag, value }\n\
        }\n\
        pub fn pair_tag(p: &Pair) -> u8 {\n\
            p.tag\n\
        }\n\
        pub fn digest_byte(d: &Digest, i: u8) -> u8 {\n\
            d.0[(i & 3) as usize]\n\
        }\n\
        pub fn digests_differ(a: &Digest, b: &Digest) -> bool {\n\
            *a != *b\n\
        }\n";
    let cap = Capture::new(lib);
    let out = cap.command().arg("--scope=crate").output().unwrap();
    assert!(
        out.status.success(),
        "struct/index fixture crate should capture:\n{}\n{}",
        stdout(&out),
        stderr(&out)
    );
    let manifest = cap.manifest();
    assert!(
        body_terminator_kinds(&manifest, "rust-path-v1::digests_differ")
            .contains(&"call_ne".into())
    );
    let lean = std::fs::read_to_string(cap.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("Trusted.MirAst.ProjectionElem.index"), "{lean}");
    assert!(lean.contains("Trusted.MirAst.CoreCallOp.arrayEq"), "{lean}");

    // Under `panic=unwind`, `drop(_2)` keeps an unwind edge to a cleanup
    // `resume` block, and cleanup blocks stay refused.
    let drop_src = b"pub fn first<T>(x: T, _y: T) -> T {\n    x\n}\n";
    let unwind = Capture::new(drop_src);
    let out = unwind
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"first","args":["u8"]}"#)
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1), "{out:?}");
    assert!(status(&out).to_string().contains("cleanup block"), "{out:?}");
    unwind.assert_no_capture_artifacts();
    let drop = Capture::new(drop_src);
    let out = drop
        .command()
        .arg("--panic=abort")
        .arg("--instantiate")
        .arg(r#"{"path":"first","args":["u8"]}"#)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "drop fixture instantiation should capture:\n{}\n{}",
        stdout(&out),
        stderr(&out)
    );
    let lean = std::fs::read_to_string(drop.output.join("Captured.lean")).unwrap();
    assert!(lean.contains("Trusted.MirAst.TerminatorKind.drop"), "{lean}");
}

#[test]
fn exclude_trait_captures_unreferenced_impls_and_nested_defs_in_crate_scope() {
    let source = b"\
        #[derive(Debug)]\n\
        pub enum Code { Ok, Err }\n\
        impl core::fmt::Display for Code {\n\
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
                const PAD: usize = 1;\n\
                let tag = || const { PAD + 1 };\n\
                let _ = tag();\n\
                match self {\n\
                    Code::Ok => f.write_str(\"ok\"),\n\
                    Code::Err => f.write_str(\"err\"),\n\
                }\n\
            }\n\
        }\n\
        impl core::error::Error for Code {}\n\
        pub fn zero() -> u64 { 0 }\n";
    let fixture = Capture::new(source);
    let output = fixture
        .command()
        .args([
            "--scope=crate",
            "--exclude-trait=core::fmt::Display",
            "--exclude-trait=core::fmt::Debug",
            "--exclude-trait=core::error::Error",
        ])
        .output()
        .expect("capture crate with excluded traits");
    assert!(
        output.status.success(),
        "expected capture success:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = fixture.manifest();
    assert_eq!(
        manifest["program"]["scope"],
        serde_json::json!({
            "kind": "crate",
            "excluded_traits": [
                "core::error::Error",
                "core::fmt::Debug",
                "core::fmt::Display",
            ]
        })
    );
    let bodies = manifest["program"]["bodies"].as_array().unwrap();
    assert_eq!(bodies.len(), 1, "{manifest}");
    assert_eq!(manifest["selected"][0]["path"], "zero");

    let census = manifest["census"].as_array().unwrap();
    let excluded: Vec<&Value> = census
        .iter()
        .filter(|item| item.get("excluded_by").is_some())
        .collect();
    assert!(
        excluded.len() >= 6,
        "expected derived Debug, Display + fmt + nested const/closure/inline-const, and Error impls in census: {excluded:?}"
    );
    for item in &excluded {
        assert_eq!(item["selected"], false, "excluded item must not be selected: {item}");
    }
    assert!(
        excluded.iter().any(|i| i["excluded_by"] == "core::fmt::Debug"),
        "missing Debug exclusion: {excluded:?}"
    );
    assert!(
        excluded.iter().any(|i| i["excluded_by"] == "core::fmt::Display"
            && i["path"].as_str().unwrap().contains("fmt")),
        "missing Display::fmt exclusion: {excluded:?}"
    );
    assert!(
        excluded.iter().any(|i| i["excluded_by"] == "core::fmt::Display"
            && i["kind"] == "Closure"),
        "missing nested closure exclusion: {excluded:?}"
    );
    assert!(
        excluded.iter().any(|i| i["excluded_by"] == "core::fmt::Display"
            && (i["kind"] == "InlineConst"
                || i["kind"].as_str().is_some_and(|k| k.starts_with("Const")))),
        "missing nested const exclusion: {excluded:?}"
    );
    assert!(
        excluded.iter().any(|i| i["excluded_by"] == "core::error::Error"),
        "missing Error exclusion: {excluded:?}"
    );

    // Without `--exclude-trait`, crate scope omits `excluded_traits` and
    // `excluded_by`.
    let plain = Capture::new(b"pub fn zero() -> u64 { 0 }\n");
    let plain_out = plain.command().arg("--scope=crate").output().unwrap();
    assert!(plain_out.status.success(), "{plain_out:?}");
    let plain_manifest = plain.manifest();
    assert_eq!(plain_manifest["program"]["scope"], serde_json::json!({"kind": "crate"}));
    for item in plain_manifest["census"].as_array().unwrap() {
        assert!(item.get("excluded_by").is_none(), "unexpected excluded_by: {item}");
    }
}

#[test]
fn exclude_trait_refuses_direct_transitive_and_default_method_references() {
    // Direct call to `<E as Display>::fmt`.
    let direct = Capture::new(
        b"pub enum E { A }\n\
          impl core::fmt::Display for E {\n\
              fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
                  f.write_str(\"a\")\n\
              }\n\
          }\n\
          pub fn calls_display(e: &E, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
              <E as core::fmt::Display>::fmt(e, f)\n\
          }\n",
    );
    let out = direct
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Display"])
        .output()
        .unwrap();
    assert_refused("direct Display::fmt call", &direct, &out, "excluded");
    assert!(status(&out).to_string().contains("core::fmt::Display"), "{out:?}");

    // Transitive call through an unexported helper.
    let transitive = Capture::new(
        b"pub enum E { A }\n\
          impl core::fmt::Display for E {\n\
              fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
                  f.write_str(\"a\")\n\
              }\n\
          }\n\
          fn helper(e: &E, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
              <E as core::fmt::Display>::fmt(e, f)\n\
          }\n\
          pub fn entry(e: &E, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
              helper(e, f)\n\
          }\n",
    );
    let out = transitive
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Display"])
        .output()
        .unwrap();
    assert_refused("transitive Display::fmt call", &transitive, &out, "excluded");

    // Inherited default method `<E as core::error::Error>::source` on an empty
    // impl.
    let inherited = Capture::new(
        b"#[derive(Debug)]\n\
          pub enum E { A }\n\
          impl core::fmt::Display for E {\n\
              fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
                  f.write_str(\"a\")\n\
              }\n\
          }\n\
          impl core::error::Error for E {}\n\
          pub fn check_source(e: &E) -> bool {\n\
              <E as core::error::Error>::source(e).is_none()\n\
          }\n",
    );
    let out = inherited
        .command()
        .args([
            "--scope=crate",
            "--exclude-trait=core::fmt::Debug",
            "--exclude-trait=core::fmt::Display",
            "--exclude-trait=core::error::Error",
        ])
        .output()
        .unwrap();
    assert_refused("inherited Error::source call", &inherited, &out, "excluded");
    assert!(status(&out).to_string().contains("core::error::Error"), "{out:?}");
}

#[test]
fn exclude_trait_refuses_fn_ptr_const_and_dyn_unsize_references() {
    // Fn-ptr reification of `<E as Debug>::fmt`.
    let fn_ptr = Capture::new(
        b"#[derive(Debug)]\n\
          pub enum E { A }\n\
          pub fn take_ptr() -> fn(&E, &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
              <E as core::fmt::Debug>::fmt\n\
          }\n",
    );
    let out = fn_ptr
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Debug"])
        .output()
        .unwrap();
    assert_refused("fn-ptr reification", &fn_ptr, &out, "excluded");

    // Fn-item reference inside a verified const item (CTFE MIR).
    let const_ref = Capture::new(
        b"#[derive(Debug)]\n\
          pub enum E { A }\n\
          pub const C: u64 = { let _ = <E as core::fmt::Debug>::fmt; 42 };\n\
          pub fn zero() -> u64 { C }\n",
    );
    let out = const_ref
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Debug"])
        .output()
        .unwrap();
    assert_refused("const fn-item reference", &const_ref, &out, "excluded");

    // Unsize coercion to `&dyn core::fmt::Debug`.
    let dyn_ref = Capture::new(
        b"#[derive(Debug)]\n\
          pub enum E { A }\n\
          pub fn as_dyn(e: &E) -> &dyn core::fmt::Debug {\n\
              e\n\
          }\n",
    );
    let out = dyn_ref
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Debug"])
        .output()
        .unwrap();
    assert_refused("dyn Debug unsize coercion", &dyn_ref, &out, "excluded");

    // Unsize coercion to a subtrait `&dyn SubDebug` whose supertrait is
    // `Debug`.
    let supertrait_dyn = Capture::new(
        b"#[derive(Debug)]\n\
          pub enum E { A }\n\
          pub trait SubDebug: core::fmt::Debug {}\n\
          impl SubDebug for E {}\n\
          pub fn as_sub(e: &E) -> &dyn SubDebug {\n\
              e\n\
          }\n",
    );
    let out = supertrait_dyn
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Debug"])
        .output()
        .unwrap();
    assert_refused("dyn SubDebug supertrait unsize", &supertrait_dyn, &out, "excluded");
}

#[test]
fn exclude_trait_refuses_non_allowlisted_select_spoof_and_unsafe_nested_items() {
    // Non-allowlisted traits are refused.
    for bad_trait in ["core::clone::Clone", "core::ops::Drop"] {
        let fixture = Capture::new(b"pub fn zero() -> u64 { 0 }\n");
        let out = fixture
            .command()
            .args(["--scope=crate", "--exclude-trait", bad_trait])
            .output()
            .unwrap();
        assert_refused(bad_trait, &fixture, &out, "not in the closed --exclude-trait allowlist");
    }

    // `--select` and `--instantiate` with `--exclude-trait` are refused.
    let sel_fixture = Capture::new(b"pub fn selected() -> u64 { 0 }\n");
    let out = sel_fixture
        .selected_command()
        .arg("--exclude-trait=core::fmt::Debug")
        .output()
        .unwrap();
    assert_refused("--select + --exclude-trait", &sel_fixture, &out, "--scope crate");

    let inst_fixture = Capture::new(b"pub fn poly<T>(x: T) -> T { x }\n");
    let out = inst_fixture
        .command()
        .args([
            "--instantiate={\"path\":\"poly\",\"args\":[\"u64\"]}",
            "--exclude-trait=core::fmt::Debug",
        ])
        .output()
        .unwrap();
    assert_refused("--instantiate + --exclude-trait", &inst_fixture, &out, "--scope crate");

    // Local look-alike `core::fmt::Debug` trait is NOT matched by diagnostic
    // item.
    let spoof = Capture::new(
        b"pub mod core {\n\
              pub mod fmt {\n\
                  pub trait Debug { fn bad(&self) -> f64; }\n\
              }\n\
          }\n\
          pub enum S { A }\n\
          impl crate::core::fmt::Debug for S {\n\
              fn bad(&self) -> f64 { 1.0 }\n\
          }\n\
          pub fn zero() -> u64 { 0 }\n",
    );
    let out = spoof
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Debug"])
        .output()
        .unwrap();
    assert_refused("local Debug trait spoof", &spoof, &out, "unsupported type: f64");

    // Crate-wide escape hatches nested inside an excluded impl stay refused.
    let smuggled_export = Capture::new(
        b"pub enum S { A }\n\
          impl core::fmt::Display for S {\n\
              fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
                  #[unsafe(no_mangle)]\n\
                  pub fn smuggled() -> u64 { 0 }\n\
                  f.write_str(\"s\")\n\
              }\n\
          }\n\
          pub fn zero() -> u64 { 0 }\n",
    );
    let out = smuggled_export
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Display"])
        .output()
        .unwrap();
    assert_refused("smuggled no_mangle inside excluded impl", &smuggled_export, &out, "smuggled");
    assert!(status(&out).to_string().contains("NO_MANGLE"), "{out:?}");

    // Nested `static` (including `#[used] static`) inside an excluded impl
    // stays required and fails closed.
    let nested_static = Capture::new(
        b"pub enum S { A }\n\
          impl core::fmt::Display for S {\n\
              fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
                  #[used]\n\
                  static KEEP: u64 = 1;\n\
                  let _ = KEEP;\n\
                  f.write_str(\"s\")\n\
              }\n\
          }\n\
          pub fn zero() -> u64 { 0 }\n",
    );
    let out = nested_static
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Display"])
        .output()
        .unwrap();
    assert_refused("nested #[used] static inside excluded impl", &nested_static, &out, "KEEP");
    assert!(status(&out).to_string().contains("Static"), "{out:?}");

    // Negative trait impl of an excluded trait stays refused by
    // `admit_safe_impl`. `negative_impls` must be explicitly allowed so the
    // capture gets past the feature allowlist and reaches that refusal.
    let neg_impl = Capture::new(
        b"#![feature(negative_impls)]\n\
          pub enum S { A }\n\
          impl !core::fmt::Display for S {}\n\
          pub fn zero() -> u64 { 0 }\n",
    );
    let out = neg_impl
        .command()
        .args([
            "--scope=crate",
            "--exclude-trait=core::fmt::Display",
            "--allow-unstable-feature=negative_impls",
        ])
        .output()
        .unwrap();
    assert_refused("negative excluded trait impl", &neg_impl, &out, "negative polarity");
    // Without the opt-in, the feature allowlist refuses the crate first.
    let out = neg_impl
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Display"])
        .output()
        .unwrap();
    assert_refused(
        "negative excluded trait impl without opt-in",
        &neg_impl,
        &out,
        "#![feature(negative_impls)] is unsupported",
    );
}

#[test]
fn exclude_trait_refuses_descendants_of_nested_impls_for_their_own_reason() {
    // Nested trait impl inside `<S as Display>::fmt`: its method must remain
    // required and fail for its own reason (not silently excluded).
    let nested_trait_impl = Capture::new(
        b"pub enum S { A }\n\
          pub trait Api { fn m(&self) -> u64; }\n\
          impl core::fmt::Display for S {\n\
              fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
                  impl Api for u64 {\n\
                      fn m(&self) -> u64 {\n\
                          unsafe { *(*self as usize as *const u64) }\n\
                      }\n\
                  }\n\
                  f.write_str(\"s\")\n\
              }\n\
          }\n\
          pub fn zero() -> u64 { 0 }\n",
    );
    let out = nested_trait_impl
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Display"])
        .output()
        .unwrap();
    assert_refused(
        "nested trait impl inside Display",
        &nested_trait_impl,
        &out,
        "mixes reference and raw-pointer locals",
    );
    assert!(!status(&out).to_string().contains("excluded"), "{out:?}");

    // Nested inherent impl inside `<S as Debug>::fmt`: its method must remain
    // required and fail for its own reason.
    let nested_inherent = Capture::new(
        b"pub enum S { A }\n\
          pub enum T { B }\n\
          impl core::fmt::Debug for S {\n\
              fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
                  impl T {\n\
                      pub fn evil(&self) -> u64 {\n\
                          unsafe { *(8usize as *const u64) }\n\
                      }\n\
                  }\n\
                  f.write_str(\"s\")\n\
              }\n\
          }\n\
          pub fn zero() -> u64 { 0 }\n",
    );
    let out = nested_inherent
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Debug"])
        .output()
        .unwrap();
    assert_refused(
        "nested inherent impl inside Debug",
        &nested_inherent,
        &out,
        "mixes reference and raw-pointer locals",
    );
    assert!(!status(&out).to_string().contains("excluded"), "{out:?}");

    // Nested `Drop` impl inside `<S as Debug>::fmt`: its `drop` method must
    // remain required and fail for its own reason.
    let nested_drop = Capture::new(
        b"pub enum S { A }\n\
          pub enum K { C }\n\
          impl core::fmt::Debug for S {\n\
              fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {\n\
                  impl Drop for K {\n\
                      fn drop(&mut self) {\n\
                          unsafe { *(8usize as *mut u64) = 0; }\n\
                      }\n\
                  }\n\
                  f.write_str(\"s\")\n\
              }\n\
          }\n\
          pub fn zero() -> u64 { 0 }\n",
    );
    let out = nested_drop
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Debug"])
        .output()
        .unwrap();
    assert_refused(
        "nested Drop impl inside Debug",
        &nested_drop,
        &out,
        "mixes reference and raw-pointer locals",
    );
    assert!(!status(&out).to_string().contains("excluded"), "{out:?}");
}

#[test]
fn exclude_trait_refuses_nonlocal_callee_predicates_and_promoted_mir() {
    // Non-local `FnDef` (`Result::unwrap`) whose elaborated predicates require
    // `E: core::fmt::Debug` fails closed with the trait-bound diagnostic.
    let nonlocal_pred = Capture::new(
        b"#[derive(Debug)]\n\
          pub enum E { A }\n\
          pub const C: u64 = { let _ = core::result::Result::<u64, E>::unwrap; 42 };\n\
          pub fn zero() -> u64 { C }\n",
    );
    let out = nonlocal_pred
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Debug"])
        .output()
        .unwrap();
    assert_refused("non-local Result::unwrap Debug bound", &nonlocal_pred, &out, "trait bound");
    assert!(status(&out).to_string().contains("core::fmt::Debug"), "{out:?}");

    // Promoted constant body referencing an excluded impl item fails closed
    // via `tcx.promoted_mir`.
    let promoted_const = Capture::new(
        b"#[derive(Debug)]\n\
          pub enum E { A }\n\
          pub const C: u64 = {\n\
              let _r: &'static fn(&E, &mut core::fmt::Formatter<'_>) -> core::fmt::Result =\n\
                  &(<E as core::fmt::Debug>::fmt\n\
                      as fn(&E, &mut core::fmt::Formatter<'_>) -> core::fmt::Result);\n\
              42\n\
          };\n\
          pub fn zero() -> u64 { C }\n",
    );
    let out = promoted_const
        .command()
        .args(["--scope=crate", "--exclude-trait=core::fmt::Debug"])
        .output()
        .unwrap();
    assert_refused("promoted MIR excluded item", &promoted_const, &out, "promoted");
    assert!(status(&out).to_string().contains("excluded"), "{out:?}");
}
