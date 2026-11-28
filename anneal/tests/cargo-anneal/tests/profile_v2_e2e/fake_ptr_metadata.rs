// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Safe `&mut [u8]` slice patterns verified through fake pointer metadata.

use super::*;

/// Verifies a `#![forbid(unsafe_code)]` `&mut [u8]` slice pattern
/// (`matches!(s, [])`, lowered via `RawPtrKind::FakeForPtrMetadata` and
/// `UnOp::PtrMetadata`) end-to-end under `CrateTheoremV2` and
/// `BodySatisfiesSafeContractV2` (`["propext"]`, zero taint), while confirming
/// that a wrong functional postcondition fails audit and mixing `&mut [u8]`
/// with a real raw-pointer local is still refused at capture time.
#[test]
fn verifies_safe_mut_slice_pattern_via_fake_ptr_metadata() {
    let dir = TempDir::new().unwrap();
    let rust_dir = dir.path().join("rust");
    let lean_dir = dir.path().join("lean");
    fs::create_dir_all(&rust_dir).unwrap();
    fs::create_dir_all(&lean_dir).unwrap();

    let safe_rust = "#![no_std]\n\
                     #![forbid(unsafe_code)]\n\n\
                     pub fn is_empty_mut_slice(s: &mut [u8]) -> bool {\n\
                         matches!(s, [])\n\
                     }\n";
    let spec_src = r#"prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def isEmptyMutSliceContract : SafeContractV2 := {
  behaviorPre := fun _ => True
  effects := EffectMaskV2.noAbort
  postReturn := fun q out =>
    match q.args with
    | [.slicePtr _ len] =>
      out.ret = .bool (Nat.beq len.toNat 0) ∧
      out.callerMem = q.callerMem
    | _ => False
}

def property (p : Program) : Prop :=
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | some body0 => BodySatisfiesSafeContractV2 p 0 body0 isEmptyMutSliceContract
  | none => False

def specs : SpecsV2 := ⟨fun _ _ => True, property⟩

end Spec
"#;
    let proof_src = r#"prelude
import Init.SimpLemmas
import Init.Data.List.Basic
import Trusted.MirAst
import Trusted.MirSemantics
import Anneal.MirWp
import Anneal.MirWp.V2Memory
import Anneal.MirWp.V2StepShield
import Captured
import Spec
import Expected

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private theorem decodeScalar_isize_ofNat {n : Nat} (h : n < Nat.pow 2 64) :
    decodeScalar ⟨.isize, false, BitVec.ofNat 128 n⟩ = Int.ofNat n := by
  unfold decodeScalar
  dsimp only
  have hMod : (BitVec.ofNat 128 n).toNat = n :=
    toNat_bvOfNat_128 (Nat.lt_trans h (by decide))
  have hTr : truncateBits .isize (BitVec.ofNat 128 n) = BitVec.ofNat 128 n :=
    truncateBits_of_toNat_lt (by rw [hMod]; exact h)
  rw [hTr, hMod]
  rfl

private theorem int_ofNat_beq_eq_nat_beq (a b : Nat) :
    (Int.ofNat a == Int.ofNat b) = Nat.beq a b := by
  change decide (Int.ofNat a = Int.ofNat b) = Nat.beq a b
  cases hB : Nat.beq a b with
  | true =>
    have hEq : a = b := Nat.eq_of_beq_eq_true hB
    subst hEq
    exact decide_eq_true rfl
  | false =>
    exact decide_eq_false (fun hEq => by
      have hab : a = b := Int.ofNat.inj hEq
      subst hab
      rw [Nat.beq_refl] at hB
      cases hB)

private theorem evalBinOp_isize_eq {a b : Nat} (ha : a < Nat.pow 2 64)
    (hb : b < Nat.pow 2 64) :
    evalBinOp .eq
      (.scalar ⟨.isize, false, BitVec.ofNat 128 a⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 b⟩) =
      .ok (.bool (Nat.beq a b)) := by
  unfold evalBinOp
  dsimp only
  rw [ite_bool_false (rfl : BinOp.eq.isShift = false)]
  rw [ite_bool_false (rfl : (!(IntWidth.isize.beq IntWidth.isize && (false == false))) = false)]
  rw [decodeScalar_isize_ofNat ha, decodeScalar_isize_ofNat hb, int_ofNat_beq_eq_nat_beq]

private theorem initLocalsLoop_body0 (ptrAid : Option AllocId) (ptrOff len : UInt64) :
    initLocalsLoop Captured.body_0
      [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len]
      0 Captured.body_0.locals =
    [.immediate none,
     .immediate (some (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len)),
     .immediate none,
     .immediate none,
     .immediate none,
     .immediate none,
     .immediate none] :=
  rfl

private theorem is_empty_mut_slice_exec (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    execProgV2 (entryProgForBody Captured.program 0) 14 q
      (Spec.isEmptyMutSliceContract.post q) := by
  let ⟨hCM, hMatch, hRefs, _⟩ := hValid
  let ⟨v0, hArgs1, hCheck0⟩ := checkArgsMatchV2_singleton_inv hMatch
  let ⟨ptr0, len, hV0, hPtrW⟩ := checkValV2_slice_u8_inv hCheck0
  subst hV0
  cases ptr0 with
  | mk ptrAid ptrOff ptrW =>
    dsimp only at hPtrW
    subst hPtrW
    let ptr : PtrVal := ⟨ptrAid, ptrOff, .isize⟩
    let m : MemoryState := entryMemoryWithCaller q.callerMem
    have hQ : q = ⟨[.slicePtr ptr len], q.callerMem⟩ := by
      cases q; dsimp only at hArgs1; rw [hArgs1]
    have hRefValid0 :
        refValidInMem m .mut (.slice (.int .i8 false)) (.slicePtr ptr len) = .ok () := by
      have hRefs' :
          refsValidInMemList m
            [.ref .mut (.slice (.int .i8 false))]
            [.slicePtr ptr len] = true := by
        rw [← hArgs1]; exact hRefs
      dsimp only [refsValidInMemList, refsValidInMem] at hRefs'
      cases hR : refValidInMem m .mut (.slice (.int .i8 false)) (.slicePtr ptr len) with
      | error _ => rw [hR] at hRefs'; cases hRefs'
      | ok u => cases u; rfl
    have hLenLt64 : len.toNat < Nat.pow 2 64 := len.toBitVec.isLt
    have hTr : truncateBits .isize (BitVec.ofNat 128 len.toNat) = BitVec.ofNat 128 len.toNat :=
      truncateBits_ofNat_of_lt .isize hLenLt64
    have hWfLen :
        checkValV2 (.scalar ⟨.isize, false, BitVec.ofNat 128 len.toNat⟩)
          (.int .isize false) = true := by
      unfold checkValV2 checkVal Val.ty? ScalarVal.wf
      dsimp only
      rw [hTr, beq_self_eq_true]
      rfl
    have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
      extractCallerMemory_entry q.callerMem hCM
    let ctx : BodyCtx := ⟨Captured.program, 0, Captured.body_0⟩
    have h_body : ctx.HasBody := rfl
    have hValid' : ValidEntryArgsV2 Captured.body_0 ⟨[.slicePtr ptr len], q.callerMem⟩ := by
      rw [← hQ]; exact hValid
    have hInit :
        initStateV2 (entryProgForBody Captured.program 0)
          ⟨[.slicePtr ptr len], q.callerMem⟩ =
        .ok (State.mk [FrameState.mk 0 0 0
          [.immediate none,
           .immediate (some (.slicePtr ptr len)),
           .immediate none,
           .immediate none,
           .immediate none,
           .immediate none,
           .immediate none]
          none none none]
          q.callerMem m) := by
      have h0 := ctx.initStateV2_ok_of h_body (by decide) hValid'
      change initStateV2 ctx.entryProg _ = _
      rw [h0]
      change Except.ok (State.mk [FrameState.mk 0 0 0
        (initLocalsLoop Captured.body_0
          [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len]
          0 Captured.body_0.locals) none none none] q.callerMem m) = _
      rw [initLocalsLoop_body0]
    rw [hQ]
    unfold execProgV2
    rw [hInit]
    -- bb0 stmt 0: PlaceMention(_1) -> nop
    apply execOutcomeStateV2_step (by rfl)
    -- bb0 stmt 1: _3 = &raw const (fake) (*_1)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
        evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        checkAssignCopyHazardV2, evalRvalueV2,
        evalFakeAddressOfRvalueV2, writePlaceDestV2, checkValV2,
        Trusted.MirSemantics.getElem?, Trusted.MirSemantics.setElem?]
      rw [hRefValid0]
      rfl)
    -- bb0 stmt 2: _4 = PtrMetadata(move _3)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
        evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        checkAssignCopyHazardV2, evalRvalueV2,
        evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
      dsimp only
      rw [ite_bool_false (rfl : (!(MirTy.int IntWidth.isize false).beq (MirTy.int IntWidth.isize false)) = false)]
      rw [hTr]
      dsimp only
      rw [writePlaceDestV2_immediate_ok hWfLen (by rfl) (by rfl)])
    -- bb0 stmt 3: _2 = Use(move _4)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
        evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        checkAssignCopyHazardV2, isMemoryCopyReprTyV2, copyReprOfTyV2,
        evalRvalueV2, evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
      dsimp only
      rw [ite_bool_false (rfl : (!(MirTy.int IntWidth.isize false).beq (MirTy.int IntWidth.isize false)) = false)]
      dsimp only
      rw [writePlaceDestV2_immediate_ok hWfLen (by rfl) (by rfl)]
      rfl)
    -- bb0 stmt 4: _5 = Use(const 0_usize)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
        evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        checkAssignCopyHazardV2, evalRvalueV2,
        evalOperandToSlotV2, evalConstLit, Trusted.MirSemantics.getElem?]
      rw [ite_bool_false (by decide : (truncateBits .isize (BitVec.ofNat 128 0) != BitVec.ofNat 128 0) = false)]
      rw [truncateBits_ofNat_of_lt .isize (by decide : 0 < intWidthModulus .isize)]
      dsimp only
      rw [ite_bool_false (rfl : (!(MirTy.int IntWidth.isize false).beq (MirTy.int IntWidth.isize false)) = false)]
      dsimp only
      rw [writePlaceDestV2_immediate_ok (by decide) (by rfl) (by rfl)])
    -- bb0 stmt 5: _6 = Eq(move _2, move _5)
    apply execOutcomeStateV2_step (by
      dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
        evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
        checkAssignCopyHazardV2, evalRvalueV2,
        evalPrimitiveOperandV2, evalOperandToSlotV2,
        Trusted.MirSemantics.getElem?]
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
      dsimp only
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
      dsimp only
      rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
      dsimp only
      rw [ite_bool_false (rfl : (!isPrimitiveReadableTy (.int .isize false)) = false)]
      dsimp only
      rw [evalBinOp_isize_eq hLenLt64 (by decide)]
      dsimp only
      rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)])
    have hConst0 : evalConstLit .bool (.scalar (BitVec.ofNat 128 0)) = .ok (.bool false) := by
      unfold evalConstLit; dsimp only
      rw [ite_bool_false (by decide), ite_bool_true (by decide)]
    have hConst1 : evalConstLit .bool (.scalar (BitVec.ofNat 128 1)) = .ok (.bool true) := by
      unfold evalConstLit; dsimp only
      rw [ite_bool_false (by decide), ite_bool_false (by decide), ite_bool_true (by decide)]
    -- bb0 term: SwitchInt(move _6) -> [0: bb1, otherwise: bb2]
    cases hEmpty : Nat.beq len.toNat 0 with
    | false =>
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalTerminatorV2, evalPrimitiveOperandV2, evalOperandToSlotV2,
          evalBoolSwitchBranches, jumpToBlock, List.length, Trusted.MirSemantics.getElem?]
        rw [ite_bool_true (rfl : Nat.beq 6 6 = true)]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [ite_bool_false (rfl : (!isPrimitiveReadableTy .bool) = false)]
        dsimp only
        rw [hConst0]
        rfl)
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
          checkAssignCopyHazardV2, evalRvalueV2,
          evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
        rw [hConst0]
        dsimp only
        rw [ite_bool_false (rfl : (!MirTy.bool.beq MirTy.bool) = false)]
        dsimp only
        rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)])
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_done (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          Trusted.MirSemantics.getElem?]
        rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
          (by rfl) (by rfl) (by rfl),
          extractReturnMemoryV2_entryMemory, hExt]
        rfl)
      exact ⟨by rw [hEmpty], rfl⟩
    | true =>
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalTerminatorV2, evalPrimitiveOperandV2, evalOperandToSlotV2,
          evalBoolSwitchBranches, jumpToBlock, List.length, Trusted.MirSemantics.getElem?]
        rw [ite_bool_true (rfl : Nat.beq 6 6 = true)]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [ite_bool_false (rfl : (!isPrimitiveReadableTy .bool) = false)]
        dsimp only
        rw [hConst0]
        rfl)
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
          checkAssignCopyHazardV2, evalRvalueV2,
          evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
        rw [hConst1]
        dsimp only
        rw [ite_bool_false (rfl : (!MirTy.bool.beq MirTy.bool) = false)]
        dsimp only
        rw [writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)])
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_done (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          Trusted.MirSemantics.getElem?]
        rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl)
          (by rfl) (by rfl) (by rfl),
          extractReturnMemoryV2_entryMemory, hExt]
        rfl)
      exact ⟨by rw [hEmpty], rfl⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, fun q hValid _ => ?_⟩
      exact (wellFormed_and_spec_of_execV2_base
        (entryProgForBody Captured.program 0) q 14
        (Spec.isEmptyMutSliceContract.post q)
        (is_empty_mut_slice_exec q hValid)).1.1
    | succ _ =>
      change none = some body at hBody
      cases hBody
  · exact safeContract_soundness_of_execV2_base.2.1
      Captured.program 0 Captured.body_0 Spec.isEmptyMutSliceContract
      rfl (by decide)
      (fun q hValid _ => ⟨14, is_empty_mut_slice_exec q hValid⟩)

end Proof
"#;

    fs::write(rust_dir.join("lib.rs"), safe_rust).unwrap();
    fs::write(lean_dir.join("Spec.lean"), spec_src).unwrap();
    fs::write(lean_dir.join("Proof.lean"), proof_src).unwrap();

    let request = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust_dir.to_str().unwrap(),
            "crate_root": "lib.rs",
            "crate_name": "fake_ptr_meta_demo",
            "edition": "2021",
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
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });

    let ok = run_request(dir.path(), "fake-ptr-meta-ok", &request);
    ok.expect_ok("crate_verified");
    ok.expect_profile_v2_assumptions();
    let capture_dir = dir.path().join("artifacts-fake-ptr-meta-ok/capture");
    let capture_json: Value =
        serde_json::from_slice(&fs::read(capture_dir.join("capture.json")).unwrap()).unwrap();
    assert_eq!(capture_json["program"]["mir_profile_version"], 2, "{capture_json}");
    let captured_lean = fs::read_to_string(capture_dir.join("Captured.lean")).unwrap();
    assert!(
        captured_lean.contains("Trusted.MirAst.Rvalue.fakeAddressOf"),
        "expected Rvalue.fakeAddressOf in Captured.lean:\n{captured_lean}"
    );

    // Negative 1 (audit): inverted emptiness postcondition must fail closed.
    let bad_spec = spec_src.replace("Nat.beq len.toNat 0", "!(Nat.beq len.toNat 0)");
    assert_ne!(bad_spec, spec_src);
    fs::write(lean_dir.join("Spec.lean"), bad_spec).unwrap();
    run_request(dir.path(), "fake-ptr-meta-wrong-spec", &request).expect_proof_failed();

    // Negative 2 (capture): adding a real raw-pointer local alongside
    // `&mut [u8]` must still fail closed with the mixed-locals refusal. The
    // local is `*mut`: a non-argument `*const P` local may still be promoted
    // to `BoxAsRef`, so its mixing refusal runs only after call lowering,
    // which rejects `core::ptr::null` first.
    fs::write(lean_dir.join("Spec.lean"), spec_src).unwrap();
    fs::write(
        rust_dir.join("lib.rs"),
        "#![no_std]\n\
         pub fn is_empty_mut_slice(s: &mut [u8]) -> bool {\n\
             let _real_raw: *mut u8 = core::ptr::null_mut();\n\
             matches!(s, [])\n\
         }\n",
    )
    .unwrap();
    run_request(dir.path(), "fake-ptr-meta-real-raw-mixed", &request)
        .expect_capture_refused(MIXED_REFS_AND_RAW_PTRS);
}
