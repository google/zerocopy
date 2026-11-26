// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end tests for fail-closed Phase-0 capture tripwires.

#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use std::{
    path::PathBuf,
    process::{Command, Output},
};

use serde_json::Value;

fn sysroot() -> PathBuf {
    anneal_testkit::default_rust_sysroot().expect("resolve pinned compiler sysroot")
}

struct CaptureFixture {
    directory: tempfile::TempDir,
    source: PathBuf,
    output: PathBuf,
}

impl CaptureFixture {
    fn new(source: &[u8]) -> Self {
        let directory = tempfile::tempdir().expect("create tripwire capture fixture");
        let source_path = directory.path().join("input.rs");
        std::fs::write(&source_path, source).expect("write tripwire capture fixture");
        let output = directory.path().join("output");
        Self { directory, source: source_path, output }
    }

    fn command(&self) -> Command {
        self.command_for_crate("tripwire_demo")
    }

    fn command_for_crate(&self, crate_name: &str) -> Command {
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
            .arg(sysroot())
            .arg("--source-file")
            .arg(&self.source);
        command
    }

    fn manifest(&self) -> Value {
        serde_json::from_slice(&std::fs::read(self.output.join("capture.json")).unwrap())
            .expect("parse capture manifest JSON")
    }

    fn assert_no_capture_artifacts(&self) {
        for name in ["capture.json", "Captured.lean"] {
            assert!(
                std::fs::symlink_metadata(self.output.join(name)).is_err(),
                "capture artifact {name} exists after tripwire refusal"
            );
        }
    }
}

fn parse_status(output: &Output) -> Value {
    serde_json::from_slice(&output.stdout).expect("capture prints JSON status")
}

#[test]
fn synthetic_demo_tripwire_refuses_only_when_explicitly_enabled() {
    let source = b"pub fn selected(x: u32) -> u32 {\n    x.wrapping_add(1)\n}\n\npub fn generic_id<T: Copy>(x: T) -> T {\n    x\n}\n";

    // Default production execution captures cleanly with zero interference.
    let baseline = CaptureFixture::new(source);
    let ok_out = baseline.command().arg("--select=selected").output().unwrap();
    assert!(ok_out.status.success(), "{ok_out:?}");
    assert_eq!(parse_status(&ok_out)["status"], "captured");
    assert!(baseline.output.join("capture.json").is_file());
    assert!(baseline.output.join("Captured.lean").is_file());

    // Unrelated value does not activate the synthetic selftest trigger.
    let unrelated = CaptureFixture::new(source);
    let unrelated_out = unrelated
        .command()
        .args(["--select=selected", "--env", "ANNEAL_PHASE0_TRIPWIRE_SELFTEST=disabled"])
        .output()
        .unwrap();
    assert!(unrelated_out.status.success(), "{unrelated_out:?}");
    assert_eq!(parse_status(&unrelated_out)["status"], "captured");

    // Enabling the synthetic demo trigger refuses selected capture fail-closed
    // with the registered Phase-0 tripwire bug ID and emits zero artifacts.
    let tripped = CaptureFixture::new(source);
    let err_out = tripped
        .command()
        .args([
            "--select=selected",
            "--env",
            "ANNEAL_PHASE0_TRIPWIRE_SELFTEST=ITREE-DEMO-000000000001",
        ])
        .output()
        .unwrap();
    assert_eq!(err_out.status.code(), Some(1), "{err_out:?}");
    let failure = parse_status(&err_out);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    let reason = failure["unsupported"][0]["reason"].as_str().unwrap_or_default();
    assert!(
        reason.contains("[PHASE0_TRIPWIRE:ITREE-DEMO-000000000001]"),
        "expected structured tripwire tag, got: {reason}"
    );
    tripped.assert_no_capture_artifacts();

    // Instantiation path (`--instantiate`) captures cleanly by default and
    // refuses fail-closed when the per-body selftest trigger is active.
    let inst_spec = r#"{"path":"generic_id","args":["u32"]}"#;
    let inst_ok = CaptureFixture::new(source);
    let inst_ok_out = inst_ok.command().args(["--instantiate", inst_spec]).output().unwrap();
    assert!(inst_ok_out.status.success(), "{inst_ok_out:?}");
    assert_eq!(parse_status(&inst_ok_out)["status"], "captured");

    let tripped_inst = CaptureFixture::new(source);
    let inst_err_out = tripped_inst
        .command()
        .args([
            "--instantiate",
            inst_spec,
            "--env",
            "ANNEAL_PHASE0_TRIPWIRE_SELFTEST=ITREE-DEMO-000000000001",
        ])
        .output()
        .unwrap();
    assert_eq!(inst_err_out.status.code(), Some(1), "{inst_err_out:?}");
    let inst_failure = parse_status(&inst_err_out);
    assert_eq!(inst_failure["status"], "unsupported", "{inst_failure}");
    let inst_reason = inst_failure["unsupported"][0]["reason"].as_str().unwrap_or_default();
    assert!(
        inst_reason.contains("[PHASE0_TRIPWIRE:ITREE-DEMO-000000000001]"),
        "expected structured tripwire tag on --instantiate capture, got: {inst_reason}"
    );
    tripped_inst.assert_no_capture_artifacts();

    // Whole-crate capture also fails closed under the per-body trigger.
    let tripped_crate = CaptureFixture::new(source);
    let crate_err_out = tripped_crate
        .command()
        .args(["--scope=crate", "--env", "ANNEAL_PHASE0_TRIPWIRE_SELFTEST=ITREE-DEMO-000000000001"])
        .output()
        .unwrap();
    assert_eq!(crate_err_out.status.code(), Some(1), "{crate_err_out:?}");
    let crate_failure = parse_status(&crate_err_out);
    assert_eq!(crate_failure["status"], "unsupported", "{crate_failure}");
    let crate_reason = crate_failure["unsupported"][0]["reason"].as_str().unwrap_or_default();
    assert!(
        crate_reason.contains("[PHASE0_TRIPWIRE:ITREE-DEMO-000000000001]"),
        "expected structured tripwire tag on crate capture, got: {crate_reason}"
    );
    tripped_crate.assert_no_capture_artifacts();

    // Crate-level hook (`tripwires::check_crate`) fails closed before body
    // census when the crate selftest trigger is active.
    let tripped_crate_hook = CaptureFixture::new(source);
    let crate_hook_out = tripped_crate_hook
        .command()
        .args([
            "--scope=crate",
            "--env",
            "ANNEAL_PHASE0_TRIPWIRE_SELFTEST=ITREE-DEMO_CRATE-000000000001",
        ])
        .output()
        .unwrap();
    assert_eq!(crate_hook_out.status.code(), Some(1), "{crate_hook_out:?}");
    let crate_hook_failure = parse_status(&crate_hook_out);
    assert_eq!(crate_hook_failure["status"], "unsupported", "{crate_hook_failure}");
    let crate_hook_diag = crate_hook_failure["diagnostics"][0].as_str().unwrap_or_default();
    assert!(
        crate_hook_diag.contains("[PHASE0_TRIPWIRE:ITREE-DEMO_CRATE-000000000001]"),
        "expected structured crate-hook tripwire tag, got: {crate_hook_diag}"
    );
    tripped_crate_hook.assert_no_capture_artifacts();

    // Clean removal (omitting the trigger) restores normal capture cleanly.
    let restored = CaptureFixture::new(source);
    let restored_out = restored.command().arg("--select=selected").output().unwrap();
    assert!(restored_out.status.success(), "{restored_out:?}");
    assert_eq!(parse_status(&restored_out)["status"], "captured");
}

#[test]
fn stdlib_core_crate_tripwire_observes_unstable_features_without_manifest_taint() {
    let stdlib_source = br#"#![feature(no_core, lang_items, f16)]
#![no_core]
#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}
impl Copy for u8 {}
pub fn selected(x: u8) -> u8 { x }
"#;

    // Baseline `--stdlib-crate=core` capture succeeds while keeping
    // normal-crate manifest feature taint fields empty/omitted.
    let baseline = CaptureFixture::new(stdlib_source);
    let baseline_out = baseline
        .command_for_crate("core")
        .args(["--select=selected", "--stdlib-crate=core"])
        .output()
        .unwrap();
    assert!(baseline_out.status.success(), "{baseline_out:?}");
    assert_eq!(parse_status(&baseline_out)["status"], "captured");
    let baseline_cfg = &baseline.manifest()["configuration"];
    assert_eq!(baseline_cfg["stdlib_crate"], "core");
    for key in [
        "observed_unstable_features",
        "incomplete_observed_unstable_features",
        "stabilized_features_present",
    ] {
        assert!(baseline_cfg.get(key).is_none(), "unexpected stdlib manifest key {key}");
    }

    // Setting only the feature filter without activating the crate selftest
    // trigger has no effect.
    let filter_only = CaptureFixture::new(stdlib_source);
    let filter_only_out = filter_only
        .command_for_crate("core")
        .args([
            "--select=selected",
            "--stdlib-crate=core",
            "--env",
            "ANNEAL_PHASE0_TRIPWIRE_SELFTEST_FEATURE=f16",
        ])
        .output()
        .unwrap();
    assert!(filter_only_out.status.success(), "{filter_only_out:?}");
    assert_eq!(parse_status(&filter_only_out)["status"], "captured");

    // Activating the crate-level selftest filtered on an unstable feature
    // enabled by `--stdlib-crate=core` (`f16`) fails closed with zero
    // artifacts, proving `CrateFacts.observed_unstable_features` is populated
    // under stdlib captures.
    let tripped = CaptureFixture::new(stdlib_source);
    let tripped_out = tripped
        .command_for_crate("core")
        .args([
            "--select=selected",
            "--stdlib-crate=core",
            "--env",
            "ANNEAL_PHASE0_TRIPWIRE_SELFTEST=ITREE-DEMO_CRATE-000000000001",
            "--env",
            "ANNEAL_PHASE0_TRIPWIRE_SELFTEST_FEATURE=f16",
        ])
        .output()
        .unwrap();
    assert_eq!(tripped_out.status.code(), Some(1), "{tripped_out:?}");
    let failure = parse_status(&tripped_out);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    let diag = failure["diagnostics"][0].as_str().unwrap_or_default();
    assert!(
        diag.contains("[PHASE0_TRIPWIRE:ITREE-DEMO_CRATE-000000000001]"),
        "expected structured stdlib crate-hook tripwire tag, got: {diag}"
    );
    tripped.assert_no_capture_artifacts();

    // Filtering the same crate-level selftest on an allowed `core` feature not
    // enabled by the fixture (`adt_const_params`) admits capture while keeping
    // manifest feature taint fields empty.
    let non_matching = CaptureFixture::new(stdlib_source);
    let non_matching_out = non_matching
        .command_for_crate("core")
        .args([
            "--select=selected",
            "--stdlib-crate=core",
            "--env",
            "ANNEAL_PHASE0_TRIPWIRE_SELFTEST=ITREE-DEMO_CRATE-000000000001",
            "--env",
            "ANNEAL_PHASE0_TRIPWIRE_SELFTEST_FEATURE=adt_const_params",
        ])
        .output()
        .unwrap();
    assert!(non_matching_out.status.success(), "{non_matching_out:?}");
    assert_eq!(parse_status(&non_matching_out)["status"], "captured");
    let non_matching_cfg = &non_matching.manifest()["configuration"];
    assert_eq!(non_matching_cfg["stdlib_crate"], "core");
    for key in [
        "observed_unstable_features",
        "incomplete_observed_unstable_features",
        "stabilized_features_present",
    ] {
        assert!(non_matching_cfg.get(key).is_none(), "unexpected stdlib manifest key {key}");
    }
}

#[test]
fn whole_crate_const_assoc_const_and_anon_const_hit_body_tripwire() {
    let const_only_source = br#"
pub const NAMED_SUM: u32 = 1 + 2;

pub enum Tag {
    A = 1 + 1,
}

pub trait ValueProvider {
    const ASSOC_VAL: u32;
}

impl ValueProvider for Tag {
    const ASSOC_VAL: u32 = 3 + 4;
}

pub fn use_arr() -> [u8; 2 + 2] {
    [0; 2 + 2]
}
"#;
    let baseline = CaptureFixture::new(const_only_source);
    let ok_out = baseline.command().arg("--scope=crate").output().unwrap();
    assert!(ok_out.status.success(), "{ok_out:?}");
    assert_eq!(parse_status(&ok_out)["status"], "captured");

    // Under `--scope=crate` with an active per-body tripwire, `Const`,
    // `AssocConst`, and `AnonConst` CTFE MIR items must each enter
    // `unsupported` with `[PHASE0_TRIPWIRE:...]` alongside callable items.
    let tripped = CaptureFixture::new(const_only_source);
    let tripped_out = tripped
        .command()
        .args([
            "--scope=crate",
            "--env",
            "ANNEAL_PHASE0_TRIPWIRE_SELFTEST=ITREE-DEMO-000000000001",
        ])
        .output()
        .unwrap();
    assert_eq!(tripped_out.status.code(), Some(1), "{tripped_out:?}");
    let failure = parse_status(&tripped_out);
    assert_eq!(failure["status"], "unsupported", "{failure}");
    let unsupported = failure["unsupported"].as_array().expect("unsupported items array");
    for expected_path_substr in ["NAMED_SUM", "ASSOC_VAL", "{constant#"] {
        let matched = unsupported
            .iter()
            .find(|item| item["path"].as_str().is_some_and(|p| p.contains(expected_path_substr)));
        let item = matched.unwrap_or_else(|| {
            panic!("missing constant MIR refusal for {expected_path_substr:?} in {failure}")
        });
        let reason = item["reason"].as_str().unwrap_or_default();
        assert!(
            reason.contains("[PHASE0_TRIPWIRE:ITREE-DEMO-000000000001]"),
            "expected structured tripwire tag on constant MIR item {item}, got: {reason}"
        );
    }
    tripped.assert_no_capture_artifacts();
}
