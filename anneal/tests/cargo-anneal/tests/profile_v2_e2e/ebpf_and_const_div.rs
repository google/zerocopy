// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `ebpf_core` `assert!`s aborting under `--panic abort`, and a constant
//! divisor keeping its `assert` on Profile v1.

use super::*;

const EBPF_REG_PROOF: &str = include_str!("../fixtures/profile_v2_ebpf/RegProof.lean");
const EBPF_DIV16_PROOF: &str = include_str!("../fixtures/profile_v2_ebpf/Div16Proof.lean");

/// End-to-end verification of `assert!(dst < 16)` (`ebpf_core`
/// `EbpfInstruction::new` static `&str` `core::panicking::panic` pattern)
/// aborting under `--panic abort` (`CoreCallOp.panicAbort [rodataRef]`),
/// rejection under `--panic unwind`, `EffectMaskV2.noAbort`, crate-local
/// `#[panic_handler]`, and formatted `assert!(cond, "bad cond")`, plus
/// Profile v1 verification of `x / 16` with its verbatim preserved
/// `TerminatorKind.assert` (`AssertKind.divByZero`).
#[test]
fn verifies_ebpf_assert_aborts_under_panic_abort_and_const_div_stays_v1() {
    let tools = tools();
    let dir = TempDir::new().unwrap();

    // Check 1a: `check_ebpf_reg(dst: u8) -> u8` (`assert!(dst < 16); dst`)
    // verifies `SafeContractV2` under `--panic abort` (`dst >= 16` evaluates
    // the static `&str` `.rodataRef` message and steps to `.aborted cm`,
    // `dst < 16` returns `dst` with unchanged `cm`).
    let rust_dir = dir.path().join("ebpf-reg-rust");
    let lean_dir = dir.path().join("ebpf-reg-lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();
    fs::write(
        rust_dir.join("lib.rs"),
        "pub fn check_ebpf_reg(dst: u8) -> u8 {\n\
             assert!(dst < 16);\n\
             dst\n\
         }\n",
    )
    .unwrap();
    fs::write(
        lean_dir.join("Spec.lean"),
        r#"prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def ebpfRegAllowAbort : SafeContractV2 := {
  behaviorPre := fun _ => True
  effects := { allowAbort := true }
  postReturn := fun q out =>
    match q.args with
    | [.scalar v] =>
      v.bits.toNat < 16 ∧ out.ret = .scalar v ∧ out.callerMem = q.callerMem
    | _ => False
  postAbort := fun q cm =>
    match q.args with
    | [.scalar v] => 16 ≤ v.bits.toNat ∧ cm = q.callerMem
    | _ => False
}

def property (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | some body0 => BodySatisfiesSafeContractV2 p 0 body0 ebpfRegAllowAbort
  | none => False

def specs : SpecsV2 := ⟨fun _ _ => True, property⟩

end Spec
"#,
    )
    .unwrap();
    fs::write(lean_dir.join("Proof.lean"), EBPF_REG_PROOF).unwrap();
    let abort_request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "ebpf_reg_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "panic": "abort",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let abort_ok = run_request(dir.path(), "ebpf-reg-panic-abort", &abort_request);
    abort_ok.expect_ok("crate_verified");
    let VerifyReceipt::Verified(verified) = &abort_ok.receipt else {
        panic!("expected verified receipt, got {:?}", abort_ok.receipt);
    };
    assert!(verified.spec_warnings.is_empty(), "{verified:?}");
    assert!(
        verified.assumptions.iter().any(|a| a.contains("as .aborted")),
        "expected --panic abort assumption in receipt: {:?}",
        verified.assumptions
    );
    let captured_lean = fs::read_to_string(
        dir.path().join("artifacts-ebpf-reg-panic-abort/capture/Captured.lean"),
    )
    .unwrap();
    assert!(
        captured_lean.contains("Trusted.MirAst.CoreCallOp.panicAbort [")
            && captured_lean.contains("Trusted.MirAst.ConstLit.rodataRef")
            && !captured_lean.contains("TerminatorKind.assert"),
        "{captured_lean}"
    );

    // Check 1b: full `ebpf_core` `EbpfInstruction::new` shape
    // (`assert!(dst < 16); assert!(src < 16); ...`) captures cleanly under
    // `--panic abort` with two static `&str` `CoreCallOp.panicAbort`
    // terminators.
    let ebpf_full_dir = dir.path().join("ebpf-insn-full");
    fs::create_dir_all(&ebpf_full_dir).unwrap();
    let ebpf_full_src = ebpf_full_dir.join("lib.rs");
    fs::write(
        &ebpf_full_src,
        "pub fn ebpf_insn_new(code: u8, dst: u8, src: u8, offset: i16, imm: i32) -> u64 {\n\
             assert!(dst < 16);\n\
             assert!(src < 16);\n\
             (code as u64)\n\
                 | ((dst as u64) << 8)\n\
                 | ((src as u64) << 12)\n\
                 | ((offset as u16 as u64) << 16)\n\
                 | ((imm as u32 as u64) << 32)\n\
         }\n",
    )
    .unwrap();
    let ebpf_full_out = dir.path().join("ebpf-insn-full-capture");
    let ebpf_cap = Command::new(tools.capture.as_deref().expect("capture bin"))
        .args([
            "capture",
            "--crate-root",
            ebpf_full_src.to_str().unwrap(),
            "--crate-name",
            "ebpf_insn_full",
            "--crate-type",
            "lib",
            "--edition",
            "2021",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--panic",
            "abort",
            "--scope",
            "crate",
            "--out-dir",
            ebpf_full_out.to_str().unwrap(),
            "--sysroot",
            tools.sysroot.to_str().unwrap(),
            "--source-file",
            ebpf_full_src.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        ebpf_cap.status.success(),
        "ebpf_insn_new capture failed: {}",
        String::from_utf8_lossy(&ebpf_cap.stdout)
    );
    let ebpf_full_lean = fs::read_to_string(ebpf_full_out.join("Captured.lean")).unwrap();
    assert_eq!(
        ebpf_full_lean
            .matches("Trusted.MirAst.CoreCallOp.panicAbort [")
            .count(),
        2,
        "{ebpf_full_lean}"
    );

    // Check 2: under `--panic unwind`, `check_ebpf_reg` keeps the diverging
    // `core::panicking::panic` call as `TerminatorKind.unsupported` (selecting
    // Profile v1) and fails verification on the abort path.
    let mut unwind_request = abort_request.clone();
    unwind_request["compilation"]["panic"] = json!("unwind");
    run_request(dir.path(), "ebpf-reg-panic-unwind", &unwind_request)
        .expect_proof_failed();

    // Check 3: `EffectMaskV2.noAbort` rejects `check_ebpf_reg` without a
    // `dst < 16` precondition even under `--panic abort`.
    let no_abort_lean = dir.path().join("ebpf-reg-noabort-lean");
    fs::create_dir_all(&no_abort_lean).unwrap();
    let spec_src = fs::read_to_string(lean_dir.join("Spec.lean")).unwrap();
    fs::write(
        no_abort_lean.join("Spec.lean"),
        spec_src.replace("effects := { allowAbort := true }", "effects := EffectMaskV2.noAbort"),
    )
    .unwrap();
    fs::copy(lean_dir.join("Proof.lean"), no_abort_lean.join("Proof.lean")).unwrap();
    let mut no_abort_request = abort_request.clone();
    no_abort_request["proof"]["source_root"] = json!(no_abort_lean.to_str().unwrap());
    run_request(dir.path(), "ebpf-reg-no-abort", &no_abort_request).expect_proof_failed();

    // Check 4: `#![no_std]` binary with crate-local `#[panic_handler]` keeps
    // `assert!(dst < 16)` unlowered as `TerminatorKind.unsupported` even under
    // `--panic abort` and fails verification, while formatted
    // `assert!(cond, "bad cond")` is refused fail-closed at capture.
    let lh_rust = dir.path().join("ebpf-reg-lh-rust");
    fs::create_dir_all(&lh_rust).unwrap();
    fs::write(
        lh_rust.join("main.rs"),
        "#![no_std]\n\
         #![no_main]\n\
         use core::panic::PanicInfo;\n\
         #[panic_handler]\n\
         fn panic(_info: &PanicInfo<'_>) -> ! { loop {} }\n\
         pub fn check_ebpf_reg_lh(dst: u8) -> u8 {\n\
             assert!(dst < 16);\n\
             dst\n\
         }\n",
    )
    .unwrap();
    let lh_request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": lh_rust.to_str().unwrap(),
            "crate_root": "main.rs",
            "crate_name": "ebpf_reg_lh_demo",
            "crate_type": "bin",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "panic": "abort",
            "cfg": [],
            "source_files": ["main.rs"]
        },
        "scope": {"kind": "selected_unit", "roots": ["check_ebpf_reg_lh"]},
        "proof": {
            "source_root": lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    run_request(dir.path(), "ebpf-reg-local-handler", &lh_request)
        .expect_proof_failed();

    let fmt_rust = dir.path().join("assert-fmt-refused-rust");
    fs::create_dir_all(&fmt_rust).unwrap();
    fs::write(
        fmt_rust.join("lib.rs"),
        "pub fn assert_msg_refused(cond: bool, val: u8) -> u8 {\n\
             assert!(cond, \"bad cond\");\n\
             val\n\
         }\n",
    )
    .unwrap();
    let mut fmt_request = abort_request.clone();
    fmt_request["compilation"]["source_root"] = json!(fmt_rust.to_str().unwrap());
    fmt_request["compilation"]["crate_name"] = json!("assert_fmt_refused");
    run_request(dir.path(), "assert-fmt-refused", &fmt_request)
        .expect_capture_refused("Arguments");

    // Check 5: constant nonzero divisor `x / 16` preserves its primitive
    // `TerminatorKind.assert` (`AssertKind.divByZero`) verbatim without CFG
    // folding and still verifies cleanly on Profile v1 (`CrateTheorem`).
    let div16_rust = dir.path().join("div16-v1-rust");
    let div16_lean = dir.path().join("div16-v1-lean");
    fs::create_dir_all(&div16_rust).unwrap();
    fs::create_dir_all(&div16_lean).unwrap();
    fs::write(
        div16_rust.join("lib.rs"),
        "pub fn div_by_16(x: u64) -> u64 {\n\
             x / 16\n\
         }\n",
    )
    .unwrap();
    fs::write(
        div16_lean.join("Spec.lean"),
        r#"prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def property (p : Program) : Prop :=
  p.mirProfileVersion = 1

def specs : Specs := ⟨fun _ _ => True, property⟩

end Spec
"#,
    )
    .unwrap();
    fs::write(div16_lean.join("Proof.lean"), EBPF_DIV16_PROOF).unwrap();
    let div16_request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": div16_rust.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "div16_v1_demo",
            "edition": "2021",
            "target": "x86_64-unknown-linux-gnu",
            "panic": "abort",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": div16_lean.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let div16_ok = run_request(dir.path(), "div16-stays-v1", &div16_request);
    div16_ok.expect_ok("crate_verified");
    let div16_capture: Value = serde_json::from_slice(
        &fs::read(dir.path().join("artifacts-div16-stays-v1/capture/capture.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(div16_capture["program"]["mir_profile_version"], 1, "{div16_capture}");
    let div16_lean_captured = fs::read_to_string(
        dir.path().join("artifacts-div16-stays-v1/capture/Captured.lean"),
    )
    .unwrap();
    assert!(
        div16_lean_captured.contains("TerminatorKind.assert")
            && div16_lean_captured.contains("AssertKind.divByZero"),
        "expected verbatim preserved DivByZero Assert on Profile v1:\n{div16_lean_captured}"
    );
}
