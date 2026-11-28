// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Core library contracts, and their missing preconditions rejected.

use super::*;

/// Profile v2 E2E test for Slice 1B `core` contracts (`Range<usize>` subslice,
/// `Option` unwrap/is_some/take/discriminant/downcast, scalar checked,
/// saturating, min, shift, leading_zeros, and `is_multiple_of`,
/// `slice::is_empty`, and `core::mem::replace`).
#[test]
fn verifies_core_contracts_and_rejects_missing_preconditions() {
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    fs::write(rust_dir.join("lib.rs"), CORE_CONTRACTS_LIB).unwrap();
    fs::write(lean_dir.join("Spec.lean"), CORE_CONTRACTS_SPEC).unwrap();
    fs::write(lean_dir.join("Proof.lean"), CORE_CONTRACTS_PROOF).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "profile_v2_core_contracts",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": lean_dir.to_str().unwrap(),
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean",
                 "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });

    let ok = run_request(dir.path(), "core-contracts-ok", &request);
    ok.expect_ok("crate_verified");
    let cap_json_path = dir
        .path()
        .join("artifacts-core-contracts-ok/capture/capture.json");
    let capture_json: Value =
        serde_json::from_slice(&fs::read(cap_json_path).unwrap()).unwrap();
    assert_eq!(
        capture_json["program"]["mir_profile_version"], 2,
        "{capture_json}"
    );

    // Positive/negative twins for runtime `corePanicTrap` obligations: in each
    // pair `lib.rs` and `Proof.lean` are identical, Component 7
    // (`BodyVerifiedV2`) is fully discharged with zero metavariables against
    // `safetyPre := (· = okQuery)`, and only `Spec.testQuery` / `expectedOut`
    // changes from an admitted query (`expect_ok`) to a trapping query that
    // fails `rfl` on `BehaviorV2` (`corePanicTrap`).
    const TWIN_PROOF: &str = "\
prelude
import Spec
import Expected
import Anneal.MirWp
namespace Proof
open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp
theorem verify : Expected.claim := by
  have _ : ValidEntryArgsV2 Captured.body_0 Spec.okQuery :=
    ⟨rfl, rfl, rfl, rfl⟩
  have hOk :=
    spec_and_behaviorV2_of_exec_eq
      (p := entryProgForBody Captured.program 0)
      (q := Spec.okQuery)
      (out := Spec.okOut)
      (fuel := 30) rfl
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      cases hBody
      refine ⟨rfl, rfl, fun q _ hSafe => ?_⟩
      have hEq : q = Spec.okQuery := hSafe rfl
      cases hEq
      exact hOk.1
    | succ _ => cases hBody
  · refine ⟨0, Captured.body_0, rfl, rfl, ?_⟩
    exact (spec_and_behaviorV2_of_exec_eq
      (p := entryProgForBody Captured.program 0)
      (q := Spec.testQuery)
      (out := Spec.expectedOut)
      (fuel := 30) rfl).2.1
end Proof
";

    let run_trap_twin = |subdir: &str,
                         crate_name: &str,
                         rust_src: &str,
                         pos_name: &str,
                         pos_spec: &str,
                         neg_name: &str,
                         neg_spec: &str| {
        let sub_dir = dir.path().join(subdir);
        let sub_rust = sub_dir.join("rust");
        let sub_lean = sub_dir.join("lean");
        fs::create_dir_all(&sub_rust).unwrap();
        fs::create_dir_all(&sub_lean).unwrap();
        fs::write(sub_rust.join("lib.rs"), rust_src).unwrap();
        fs::write(sub_lean.join("Proof.lean"), TWIN_PROOF).unwrap();
        let req = json!({
            "schema_version": 1,
            "compilation": {
                "source_root": sub_rust.to_str().unwrap(),
                "crate_root": "lib.rs",
                "crate_name": crate_name,
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "cfg": [],
                "source_files": ["lib.rs"]
            },
            "scope": {"kind": "crate"},
            "proof": {
                "source_root": sub_lean.to_str().unwrap(),
                "specification": "Spec.specs",
                "theorem": "Proof.verify",
                "sources": [
                    {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                    {"module": "Proof", "path": "Proof.lean", "role": "proof"}
                ]
            }
        });
        fs::write(sub_lean.join("Spec.lean"), pos_spec).unwrap();
        run_request(dir.path(), pos_name, &req).expect_ok("crate_verified");

        fs::write(sub_lean.join("Spec.lean"), neg_spec).unwrap();
        let neg = run_request(dir.path(), neg_name, &req);
        neg.expect_proof_failed();
        let detail = match &neg.receipt {
            VerifyReceipt::Failed(failure) => failure.detail.as_str(),
            VerifyReceipt::Verified(_) => "",
        };
        assert!(
            !detail.contains("command parser error")
                && !detail.contains("don't know how to synthesize")
                && !detail.contains("unassigned")
                && !detail.contains("Spec.okQuery"),
            "{neg_name} failed outside Spec.testQuery evaluation:\n{:?}",
            neg.receipt
        );
        assert!(
            detail.contains("Spec.testQuery")
                && detail.contains("execProgV2")
                && (detail.contains("Application type mismatch")
                    || detail.contains("not definitionally equal")
                    || detail.contains("Tactic `rfl` failed")),
            "{neg_name} did not fail on `rfl` over Spec.testQuery:\n{:?}",
            neg.receipt
        );
    };

    const SUBSLICE_SPEC_TMPL: &str = "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def okQuery : Query :=
  { args :=
      [.slicePtr ⟨some 2, 0, .isize⟩ 2,
       .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩,
       .scalar ⟨.isize, false, BitVec.ofNat 128 1⟩],
    callerMem :=
      ⟨[{ allocId := 2, alignLog2 := 0, mutability := .shared,
          bytes := [AllocByte.init 10 none, AllocByte.init 20 none],
          live := true }]⟩ }
def okOut : TerminalOut :=
  TerminalOut.returned
    ⟨.slicePtr ⟨some 2, 0, .isize⟩ 1, okQuery.callerMem⟩
def testQuery : Query := __TEST_QUERY__
def expectedOut : TerminalOut :=
  TerminalOut.returned
    ⟨.slicePtr ⟨some 2, __OUT_OFF__, .isize⟩ 1, testQuery.callerMem⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::subslice\" ∧
    BehaviorV2 (entryProgForBody p defId) testQuery expectedOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
";
    let subslice_pos = SUBSLICE_SPEC_TMPL
        .replace("__TEST_QUERY__", "okQuery")
        .replace("__OUT_OFF__", "0");
    let subslice_oob = SUBSLICE_SPEC_TMPL
        .replace(
            "__TEST_QUERY__",
            "\n\
             \x20 { args :=\n\
             \x20     [.slicePtr ⟨some 2, 0, .isize⟩ 2,\n\
             \x20      .scalar ⟨.isize, false, BitVec.ofNat 128 3⟩,\n\
             \x20      .scalar ⟨.isize, false, BitVec.ofNat 128 4⟩],\n\
             \x20   callerMem := okQuery.callerMem }",
        )
        .replace("__OUT_OFF__", "3");
    run_trap_twin(
        "subslice_twin",
        "subslice_trap_twin",
        "pub unsafe fn subslice<'a>(s: &'a [u8], a: usize, b: usize) -> &'a [u8] {\n    &s[a..b]\n}\n",
        "core-contracts-inbounds-subslice",
        &subslice_pos,
        "core-contracts-oob-subslice",
        &subslice_oob,
    );

    const SUBSLICE_OPT_SPEC_TMPL: &str = "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def noneOptU64Bytes : List AllocByte :=
  List.replicate 8 (AllocByte.init 0 none) ++
    List.replicate 8 AllocByte.uninit
def some42OptU64Bytes : List AllocByte :=
  (AllocByte.init 1 none :: List.replicate 7 (AllocByte.init 0 none)) ++
    (AllocByte.init 42 none :: List.replicate 7 (AllocByte.init 0 none))
def okQuery : Query :=
  { args :=
      [.slicePtr ⟨some 2, 0, .isize⟩ 2,
       .scalar ⟨.isize, false, BitVec.ofNat 128 0⟩,
       .scalar ⟨.isize, false, BitVec.ofNat 128 1⟩],
    callerMem :=
      ⟨[{ allocId := 2, alignLog2 := 3, mutability := .shared,
          bytes := noneOptU64Bytes ++ some42OptU64Bytes,
          live := true }]⟩ }
def okOut : TerminalOut :=
  TerminalOut.returned
    ⟨.slicePtr ⟨some 2, 0, .isize⟩ 1, okQuery.callerMem⟩
def testQuery : Query := __TEST_QUERY__
def expectedOut : TerminalOut :=
  TerminalOut.returned
    ⟨.slicePtr ⟨some 2, __OUT_OFF__, .isize⟩ 1, testQuery.callerMem⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::subslice_opt\" ∧
    BehaviorV2 (entryProgForBody p defId) testQuery expectedOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
";
    let subslice_opt_pos = SUBSLICE_OPT_SPEC_TMPL
        .replace("__TEST_QUERY__", "okQuery")
        .replace("__OUT_OFF__", "0");
    let subslice_opt_oob = SUBSLICE_OPT_SPEC_TMPL
        .replace(
            "__TEST_QUERY__",
            "\n\
             \x20 { args :=\n\
             \x20     [.slicePtr ⟨some 2, 0, .isize⟩ 2,\n\
             \x20      .scalar ⟨.isize, false, BitVec.ofNat 128 2⟩,\n\
             \x20      .scalar ⟨.isize, false, BitVec.ofNat 128 3⟩],\n\
             \x20   callerMem := okQuery.callerMem }",
        )
        .replace("__OUT_OFF__", "32");
    run_trap_twin(
        "subslice_opt_twin",
        "subslice_opt_trap_twin",
        "pub unsafe fn subslice_opt<'a>(s: &'a [Option<u64>], a: usize, b: usize) -> &'a [Option<u64>] {\n    &s[a..b]\n}\n",
        "core-contracts-inbounds-subslice-opt-none",
        &subslice_opt_pos,
        "core-contracts-oob-subslice-opt-none",
        &subslice_opt_oob,
    );

    const UNWRAP_SPEC_TMPL: &str = "\
prelude
import Trusted.MirSemantics
namespace Spec
open Trusted.MirAst Trusted.MirSemantics
def okQuery : Query :=
  { args := [.optionVal (some (.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩))],
    callerMem := ⟨[]⟩ }
def okOut : TerminalOut :=
  TerminalOut.returned
    ⟨.scalar ⟨.i64, false, BitVec.ofNat 128 7⟩, ⟨[]⟩⟩
def testQuery : Query := __TEST_QUERY__
def expectedOut : TerminalOut :=
  TerminalOut.returned
    ⟨.scalar ⟨.i64, false, BitVec.ofNat 128 __OUT_VAL__⟩, ⟨[]⟩⟩
def safetyPre (_ : String) (q : Query) : Prop := q = okQuery
def property (p : Program) : Prop :=
  ∃ (defId : DefId) (body : Body),
    Trusted.MirSemantics.getElem? p.bodies defId = some body ∧
    body.identity = \"rust-path-v1::opt_unwrap\" ∧
    BehaviorV2 (entryProgForBody p defId) testQuery expectedOut
def specs : SpecsV2 := ⟨safetyPre, property⟩
end Spec
";
    let unwrap_pos = UNWRAP_SPEC_TMPL
        .replace("__TEST_QUERY__", "okQuery")
        .replace("__OUT_VAL__", "7");
    let unwrap_none = UNWRAP_SPEC_TMPL
        .replace("__TEST_QUERY__", "{ args := [.optionVal none], callerMem := ⟨[]⟩ }")
        .replace("__OUT_VAL__", "0");
    run_trap_twin(
        "unwrap_twin",
        "unwrap_trap_twin",
        "pub unsafe fn opt_unwrap(x: Option<u64>) -> u64 {\n    x.unwrap()\n}\n",
        "core-contracts-some-unwrap",
        &unwrap_pos,
        "core-contracts-none-unwrap",
        &unwrap_none,
    );

    // Negative 3: mutate `subslicePost` length (`b - a` -> `b - a + 1`) against
    // unmodified `Proof.lean`, failing purely on the unprovable postcondition.
    let bad_post = CORE_CONTRACTS_SPEC.replace(
        "UInt64.ofNat (bSv.bits.toNat - aSv.bits.toNat)",
        "UInt64.ofNat (bSv.bits.toNat - aSv.bits.toNat + 1)",
    );
    assert_ne!(bad_post, CORE_CONTRACTS_SPEC);
    fs::write(lean_dir.join("Spec.lean"), bad_post).unwrap();
    let neg3_name = "core-contracts-wrong-postcondition";
    run_request(dir.path(), neg3_name, &request).expect_proof_failed();
}
