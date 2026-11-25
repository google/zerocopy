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
    path::PathBuf,
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
    assert_eq!(manifest["schema_version"], 4);
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

    let unsupported_ref = Capture::new(b"pub fn selected(x: &str) -> &str { x }\n");
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
        assert_eq!(manifest["schema_version"], 4, "{name}");
    }

    // Pure arithmetic array-length `AnonConst` (`2 + 2`) is admitted while the
    // surrounding function body still fails closed on the unsupported array
    // local / `.len()` call rather than on `AnonConst`.
    let array_len_fixture =
        Capture::new(b"pub fn len_only() -> usize { let a = [0u8; 2 + 2]; a.len() }\n");
    let array_len_out = array_len_fixture.command().arg("--scope=crate").output().unwrap();
    assert_eq!(array_len_out.status.code(), Some(1), "{array_len_out:?}");
    let array_len_failure = status(&array_len_out);
    assert_eq!(array_len_failure["status"], "unsupported", "{array_len_failure}");
    assert!(
        !array_len_failure.to_string().contains("AnonConst")
            && array_len_failure.to_string().contains("unsupported type"),
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
    assert_eq!(manifest["schema_version"], 4);
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

    // Aggregates other than `()` (`AggregateKind::Adt`), including direct
    // fieldless enum construction, payload-enum unit variants, 0-field
    // structs, and non-local enums, must all fail closed.
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
            "unit_struct",
            b"pub struct UnitStruct;\n\
              pub fn f() -> UnitStruct { UnitStruct }\n",
            &["--select=f"],
            "unsupported type",
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
            failure.to_string().contains("intrinsic `unreachable` is unsupported"),
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
    assert_eq!(fixture.manifest()["schema_version"], 4);

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
    assert_eq!(no_std_fixture.manifest()["schema_version"], 4);

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
    let source = br#"#![feature(core_intrinsics)]
#![allow(internal_features)]

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

pub fn ordering_and_cmp(x: i64, y: i64, c1: char, c2: char) -> i8 {
    let ord_i: core::cmp::Ordering = core::intrinsics::three_way_compare(x, y);
    let ord_c: core::cmp::Ordering = core::intrinsics::three_way_compare(c1, c2);
    let first = match ord_i {
        core::cmp::Ordering::Less => -1i8,
        core::cmp::Ordering::Equal => 0i8,
        core::cmp::Ordering::Greater => 1i8,
    };
    let second = match ord_c {
        core::cmp::Ordering::Less => -1i8,
        core::cmp::Ordering::Equal => 0i8,
        core::cmp::Ordering::Greater => 1i8,
    };
    !first ^ second
}

pub unsafe fn unchecked_div_rem(a: i64, b: i64, u: u128, v: u128) -> u128 {
    let q: i64 = unsafe { core::intrinsics::unchecked_div(a, b) };
    let r: i64 = unsafe { core::intrinsics::unchecked_rem(a, b) };
    let uq: u128 = unsafe { core::intrinsics::unchecked_div(u, v) };
    let ur: u128 = unsafe { core::intrinsics::unchecked_rem(u, v) };
    ((q ^ r) as u128) ^ uq ^ ur
}

pub fn overflow_pairs(a: u64, b: u64) -> (u64, bool) {
    let p_add: (u64, bool) = core::intrinsics::add_with_overflow(a, b);
    let _p_sub: (u64, bool) = core::intrinsics::sub_with_overflow(a, b);
    let p_mul: (u64, bool) = core::intrinsics::mul_with_overflow(a, b);
    let copied: (u64, bool) = p_add;
    if !false {
        copied
    } else {
        p_mul
    }
}
"#;

    let fixture = Capture::new(source);
    let output = fixture.command().arg("--scope=crate").output().unwrap();
    assert!(
        output.status.success(),
        "expected crate capture to succeed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = fixture.manifest();
    assert_eq!(manifest["schema_version"], 4);
    assert_eq!(manifest["program"]["bodies"].as_array().unwrap().len(), 5);

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
        "Trusted.MirAst.BinOp.div",
        "Trusted.MirAst.BinOp.rem",
        "Trusted.MirAst.BinOp.addWithOverflow",
        "Trusted.MirAst.BinOp.subWithOverflow",
        "Trusted.MirAst.BinOp.mulWithOverflow",
        "Trusted.MirAst.BinOp.cmp",
        "Trusted.MirAst.CastKind.intToInt",
        "BitVec.ofNat 128 340282366920938463463374607431768211455",
    ] {
        assert!(
            lean_src.contains(expected_token),
            "Captured.lean missing {expected_token:?}:\n{lean_src}"
        );
    }
    compile_captured_lean_if_trusted_sources_present(&lean_path);

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
            b"#![feature(core_intrinsics)]\n\
              #![allow(internal_features)]\n\
              pub fn selected(a: u32, b: u32) -> u32 {\n\
                  core::intrinsics::add_with_overflow(a, b).0\n\
              }\n",
        ),
        (
            "overflow_pair_field_1_projection",
            b"#![feature(core_intrinsics)]\n\
              #![allow(internal_features)]\n\
              pub fn selected(a: u32, b: u32) -> bool {\n\
                  core::intrinsics::add_with_overflow(a, b).1\n\
              }\n",
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
            "checked_div_assert_terminator",
            b"pub fn selected(a: u32, b: u32) -> u32 { a / b }\n",
        ),
    ];
    for (name, source) in v2_admitted_cases {
        let fixture = Capture::new(source);
        let output = fixture.selected_command().output().unwrap();
        assert!(output.status.success(), "{name}: {output:?}");
        assert_eq!(fixture.manifest()["program"]["mir_profile_version"], 2, "{name}");
    }

    let refused_cases: &[(&str, &[u8], &str)] = &[
        (
            "slice_index_projection",
            b"pub fn selected(s: &[u8], i: usize) -> u8 { s[i] }\n",
            "unsupported place projection",
        ),
        (
            "checked_add_option_call",
            b"pub fn selected(a: u32, b: u32) -> Option<u32> { a.checked_add(b) }\n",
            "unsupported type",
        ),
        (
            "transmute_cast_kind",
            b"pub unsafe fn selected(x: u32) -> i32 {\n\
                  unsafe { core::mem::transmute::<u32, i32>(x) }\n\
              }\n",
            "unsupported cast kind: Transmute",
        ),
        (
            "unchecked_add_bin_op",
            b"#![feature(core_intrinsics)]\n\
              #![allow(internal_features)]\n\
              pub unsafe fn selected(a: u32, b: u32) -> u32 {\n\
                  unsafe { core::intrinsics::unchecked_add(a, b) }\n\
              }\n",
            "unsupported binary operator: AddUnchecked",
        ),
        (
            "ptr_metadata_un_op_or_ptr_type",
            b"#![feature(ptr_metadata)]\n\
              pub fn selected(p: *const [u8]) -> usize { p.len() }\n",
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
}

#[test]
fn thousand_one_hundred_function_crate_compiles_in_lean_under_default_max_rec_depth() {
    let mut source = String::with_capacity(64 * 1024);
    for idx in 0..1_100usize {
        let _ = writeln!(source, "pub fn f_{idx}(x: u64) -> u64 {{ (x ^ {idx}u64) + 1u64 }}");
    }
    let fixture = Capture::new(source.as_bytes());
    let output = fixture.command().arg("--scope=crate").output().unwrap();
    assert!(
        output.status.success(),
        "expected 1,100-function crate capture to succeed:\n{}\n{}",
        stdout(&output),
        stderr(&output)
    );
    let manifest = fixture.manifest();
    assert_eq!(manifest["schema_version"], 4);
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
    // projected `PlaceMention((_3.0: u64))`. Without `-Zmir-preserve-ub`,
    // `RemovePlaceMention` would erase this statement and capture would succeed
    // silently; with `-Zmir-preserve-ub`, capture must fail closed explicitly.
    let projected = Capture::new(
        b"#![feature(core_intrinsics)]\n\
          #![allow(internal_features)]\n\
          pub fn selected(a: u64, b: u64) -> u64 {\n\
              let p: (u64, bool) = core::intrinsics::add_with_overflow(a, b);\n\
              let _ = p.0;\n\
              a\n\
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
    // external definition. The last two can carry no unsafe code at all:
    // exported macros stay refused regardless of their tokens.
    let cases: [(&str, &[u8]); 10] = [
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
        ("`macro` 2.0", b"#![feature(decl_macro)]\npub macro zero_v2() { 0u64 }\n"),
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
    let lean_path = fixture.output.join("Captured.lean");
    let lean_src = std::fs::read_to_string(&lean_path).unwrap();
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

    // 4. Returning calls (`target: Some(_)`) remain refused in both `bin` and `lib`.
    let returning_call = b"#[inline(never)] fn helper() -> u64 { 1 }\npub fn caller() -> u64 { helper() }\nfn main() {}\n";
    let call_bin = Capture::new(returning_call);
    let call_out =
        call_bin.command().args(["--crate-type=bin", "--select=caller"]).output().unwrap();
    assert_eq!(call_out.status.code(), Some(1), "{call_out:?}");
    assert_eq!(status(&call_out)["status"], "unsupported");
    call_bin.assert_no_capture_artifacts();

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
    // six impl items pass `whole_crate_item`. Profile v2 captures the `&self`
    // bodies of `clone` and `assert_receiver_is_total_eq`, leaving only
    // `PartialEq::eq`, which reads a discriminant through a reference.
    let derived_crate = b"\
        #[derive(Clone, Copy, PartialEq, Eq)]\n\
        pub enum Derived { A, B }\n\
        pub fn ok(x: Derived) -> u8 { match x { Derived::A => 0, Derived::B => 1 } }\n";
    let drv_fixture = Capture::new(derived_crate);
    let drv_out = drv_fixture.command().arg("--scope=crate").output().unwrap();
    assert_eq!(drv_out.status.code(), Some(1), "{drv_out:?}");
    let drv_failure = status(&drv_out);
    assert_eq!(drv_failure["status"], "unsupported", "{drv_failure}");
    let drv_unsup = drv_failure["unsupported"].as_array().unwrap();
    assert_eq!(drv_unsup.len(), 1, "{drv_failure}");
    assert!(
        drv_unsup[0]["path"].as_str().unwrap().contains("as std::cmp::PartialEq>::eq"),
        "{drv_failure}"
    );
    assert!(
        drv_unsup[0]["reason"].as_str().unwrap().contains("place projections are unsupported"),
        "{drv_failure}"
    );
    drv_fixture.assert_no_capture_artifacts();

    // Pure `Struct`-typed `Const` (`Hash([0; 32])`) and its `AnonConst` length
    // are admitted, leaving only the `Struct` definition itself unsupported.
    let struct_const_crate = b"\
        pub const HASH_SIZE: usize = 32;\n\
        pub struct Hash(pub [u8; HASH_SIZE]);\n\
        pub const EMPTY: Hash = Hash([0u8; HASH_SIZE]);\n\
        pub fn ok() -> u8 { 0 }\n";
    let sc_fixture = Capture::new(struct_const_crate);
    let sc_out = sc_fixture.command().arg("--scope=crate").output().unwrap();
    assert_eq!(sc_out.status.code(), Some(1), "{sc_out:?}");
    let sc_failure = status(&sc_out);
    let sc_unsup = sc_failure["unsupported"].as_array().unwrap();
    assert_eq!(sc_unsup.len(), 1, "expected only Struct refusal, got {sc_failure}");
    assert_eq!(sc_unsup[0]["path"], "Hash", "{sc_failure}");
    assert!(
        sc_unsup[0]["reason"]
            .as_str()
            .unwrap()
            .contains("whole-crate obligation is unsupported: Struct"),
        "{sc_failure}"
    );
    sc_fixture.assert_no_capture_artifacts();

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
            "whole-crate obligation is unsupported: Trait (auto trait)",
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
            "whole-crate obligation is unsupported: Impl { of_trait: true } (unsafe impl)",
        ),
        (
            "negative_impl",
            b"#![feature(negative_impls)]\n\
              pub enum E { A }\n\
              pub trait Tr {}\n\
              impl !Tr for E {}\n\
              pub fn ok() -> u8 { 0 }\n",
            "negative polarity",
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
            "linkage attribute WeakAny is unsupported",
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
            "#![feature(core_intrinsics)]\n#![allow(internal_features)]\n\
             pub unsafe fn selected(a: u8, b: u8) -> u8 {\n\
                 let pair = core::intrinsics::add_with_overflow(a, b);\n\
                 let p = &raw const pair;\n\
                 unsafe { *(p as *const u8) }\n\
             }\n",
        ),
        (
            "borrow-of-overflow-pair-local",
            "#![feature(core_intrinsics)]\n#![allow(internal_features)]\n\
             pub fn selected(a: u8, b: u8) -> bool {\n\
                 let pair = core::intrinsics::add_with_overflow(a, b);\n\
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
fn projected_moves_are_refused_at_capture() {
    // `t.0` of a non-`Copy` tuple field lowers to `move (_1.0)`. Moving out
    // of `*p` through a reference or raw pointer is a borrow-check error
    // (E0507), so the dereference form is covered by the `ir` unit test.
    let fixture = Capture::new(
        b"pub fn selected(t: (core::ops::RangeFrom<usize>, usize)) \
          -> core::ops::RangeFrom<usize> { t.0 }\n",
    );
    let output = fixture.selected_command().output().unwrap();
    assert_eq!(status(&output)["status"], "unsupported", "{output:?}");
    assert_refused("tuple-field-move", &fixture, &output, "projected move operands");
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
    for (name, source, expected) in [
        ("two-field struct RangeTo", &struct_spoof[..], "unsupported type"),
        ("payload enum RangeTo", &enum_spoof[..], "unsupported type"),
    ] {
        let fixture = Capture::new(source);
        let output = fixture.command_with("core", true).arg("--select=selected").output().unwrap();
        assert_refused(name, &fixture, &output, expected);
    }

    // Look-alike `core::slice::<impl [T]>::len` and
    // `core::ptr::const_ptr::<impl *const T>::add` cannot reach the call
    // table. While the sysroot `core` is linked, its inherent methods make
    // every call to a local look-alike ambiguous (E0034), so `rustc` fails.
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
        }\n\
        pub fn selected(s: &[u8]) -> usize { s.len() }\n\
        pub unsafe fn add(p: *const u8) -> *const u8 { unsafe { p.add(1) } }\n";
    let fixture = Capture::new(method_spoof);
    let output = fixture.command_with("core", true).arg("--select=selected").output().unwrap();
    assert_ne!(output.status.code(), Some(0), "method spoof: {output:?}");
    assert!(stderr(&output).contains("E0034"), "method spoof: {}", stderr(&output));
    fixture.assert_no_capture_artifacts();

    // Without the sysroot `core` (`#![no_core]`), the crate must define the
    // `Sized` lang item itself, which capture refuses before extraction.
    let no_core_spoof = b"\
        #![feature(no_core, lang_items, rustc_attrs)]\n\
        #![no_core]\n\
        #![rustc_coherence_is_core]\n\
        #[lang = \"pointee_sized\"] pub trait PointeeSized {}\n\
        #[lang = \"meta_sized\"] pub trait MetaSized: PointeeSized {}\n\
        #[lang = \"sized\"] pub trait Sized: MetaSized {}\n\
        #[lang = \"copy\"] pub trait Copy {}\n\
        impl Copy for usize {}\n\
        #[lang = \"legacy_receiver\"] pub trait LegacyReceiver: PointeeSized {}\n\
        impl<T: PointeeSized> LegacyReceiver for &T {}\n\
        pub mod core {\n\
            pub mod slice {\n\
                impl<T> [T] { pub fn len(&self) -> usize { 7 } }\n\
            }\n\
        }\n\
        pub fn selected(s: &[u8]) -> usize { s.len() }\n";
    let fixture = Capture::new(no_core_spoof);
    let output = fixture.command_with("core", true).arg("--select=selected").output().unwrap();
    assert_refused("no_core spoof", &fixture, &output, "crate-local language item");
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
