-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.List.Basic
public import Trusted
public import Trusted.Framework
public import Trusted.Framework.Instances
public import Trusted.Framework.Bridge
public import Trusted.MirSemantics.CanaryFixtures
public import Anneal.MirWp
public import Anneal.MirWp.V2Memory
public import Anneal.Framework

public section

namespace Anneal.Framework.Canaries

open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
open Anneal.MirWp Anneal.Framework

/-!
# Verification Envelope Pass-1 Canaries (`Anneal.Framework.Canaries`)

Decoupled Pass-1 canary suite (outside `theory/bundle-manifest.json` and domain
umbrellas, discovered dynamically by `anneal-audit`) exercising
`Trusted.Framework`, `MirProfileV1`, `MirProfileV2`, `OracleCertificate`, and
compatibility equivalences against positive and negative cases.
-/

/-- Forward-simulation-only MIR profile fixture used in `FrameworkCanaryClaim`
to verify that `.forwardSim` rejects existential `existsWitness` refutations
and `termination` transfer claims. -/
noncomputable abbrev canaryForwardSimMirModel :
    ExecutionModel Program Body MirSignature Query Val CallerMemory :=
  { MirProfileV1 with oracleGrade := .forwardSim "lean_miri_forward_only" }

/-- External-declaration MIR profile fixture marking zero-argument bodies as
external declarations (`bodyIsExternal := fun b => Nat.beq b.argumentCount 0`),
used to test `AssumedStub` admission and `StubRealizable` enforcement while
`MirProfileV1` and `MirProfileV2` forbid stubbing local captured bodies. -/
noncomputable abbrev canaryExternalStubModel :
    ExecutionModel Program Body MirSignature Query Val CallerMemory :=
  { MirProfileV1 with bodyIsExternal := fun b => Nat.beq b.argumentCount 0 }

/-- Profile v2 body taking a reference parameter (`&u8`) without raw-pointer
locals, admitted without `DisclosedGap.callerRawPtrAliasing`. -/
@[expose] noncomputable def canaryV2RefBody : Body := {
  argumentCount := 1
  locals := [.unit, .ref .shared u8Ty]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "canary::v2_ref"
}

/-- Profile v2 body with a raw-pointer local (`*const u8`) requiring
`DisclosedGap.callerRawPtrAliasing "mir_profile_v2"`. -/
@[expose] noncomputable def canaryV2RawPtrBody : Body := {
  argumentCount := 1
  locals := [.unit, .rawPtr .shared u8Ty]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "canary::v2_raw_ptr"
}

/-- Profile v2 body mixing reference (`&u8`) and raw-pointer (`*const u8`)
locals, which `BodyStaticAdmittedV2` must reject fail-closed. -/
@[expose] noncomputable def canaryV2MixedBody : Body := {
  argumentCount := 1
  locals := [.unit, .ref .shared u8Ty, .rawPtr .shared u8Ty]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "canary::v2_mixed"
}

/-- Profile v2 body returning `&u8` used to verify `StubRealizable` rejects
null (`allocId := none`) and dangling (`allocId := some 99`) reference stub
returns via `ValidMirReturnValV2`. -/
@[expose] noncomputable def canaryV2RetRefBody : Body := {
  argumentCount := 0
  locals := [.ref .shared u8Ty]
  basicBlocks := [{ statements := [], terminator := .unreachable }]
  isUnsafe := false
  identity := "canary::v2_ret_ref"
}

/-- Decompose `a ∈ b :: l` without requiring constructor-level string
unification during `cases`. -/
theorem mem_cons_elim {α : Type} {a b : α} {l : List α}
    (h : a ∈ b :: l) : a = b ∨ a ∈ l := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ hTail => exact Or.inr hTail

/-- Canary total normal-return `EffectMask` fixture. -/
@[expose] def canaryTotalEffects : Trusted.Framework.EffectMask :=
  { terminates := true, noUnwind := true, noAbort := true }

/-- Canary permissive partial `EffectMask` fixture. -/
@[expose] def canaryPartialEffects : Trusted.Framework.EffectMask :=
  { terminates := false, noUnwind := false, noAbort := false }

/-- Complete Pass-1 claim proposition for `framework_canary`, exercising wire
names, upper-triangular `OracleGrade.licenses`, `effectMaskLe`, `AbiKind.beq`,
`TerminalOutcome` distinctness, `decodeScalar`, positive `mkEnvelope` on both
`MirProfileV1` and `MirProfileV2` (scalar, ref-only without raw-pointer gap,
and raw-pointer with raw-pointer gap), rejection of vacuity / missing gaps
(including `defaultMirDownstreamGaps`) / mixed ref+raw-ptr Profile v2 bodies /
unlisted bodies / unrealizable stubs (including null and dangling `&u8` returns
under `ValidMirReturnValV2`) / unlicensed refutations & forward-sim termination
/ unsafe caller-misuse refutations, `OracleCertificate`, and
`CrateTheorem`/`UnitTheorem`/`V2` equivalences. -/
@[expose] def FrameworkCanaryClaim : Prop :=
  claimShapeWireName .existsWitness = "exists_witness" ∧
  claimShapeWireName .forallSafety = "forall_safety" ∧
  claimShapeWireName .generalHyper = "general_hyper" ∧
  claimShapeWireName .subsetHyper = "subset_hyper" ∧
  claimShapeWireName .termination = "termination" ∧
  (OracleGrade.unbridged "mir_profile_v2").licenses .forallSafety = true ∧
  (OracleGrade.unbridged "mir_profile_v2").licenses .termination = true ∧
  (OracleGrade.unbridged "mir_profile_v2").licenses .existsWitness = false ∧
  (OracleGrade.unbridged "mir_profile_v2").licenses .subsetHyper = false ∧
  (OracleGrade.unbridged "mir_profile_v2").licenses .generalHyper = false ∧
  (OracleGrade.forwardSim "miri").licenses .forallSafety = true ∧
  (OracleGrade.forwardSim "miri").licenses .subsetHyper = true ∧
  (OracleGrade.forwardSim "miri").licenses .termination = false ∧
  (OracleGrade.forwardSim "miri").licenses .existsWitness = false ∧
  (OracleGrade.forwardSim "miri").licenses .generalHyper = false ∧
  (OracleGrade.biFaultEquiv "miri").licenses .existsWitness = true ∧
  (OracleGrade.biFaultEquiv "miri").licenses .forallSafety = true ∧
  (OracleGrade.biFaultEquiv "miri").licenses .subsetHyper = true ∧
  (OracleGrade.biFaultEquiv "miri").licenses .termination = true ∧
  (OracleGrade.biFaultEquiv "miri").licenses .generalHyper = false ∧
  effectMaskLe canaryPartialEffects canaryTotalEffects ∧
  ¬ effectMaskLe canaryTotalEffects canaryPartialEffects ∧
  AbiKind.beq .rust .rust = true ∧
  (∀ (r : Val) (m : CallerMemory),
    TerminalOutcome.returned r m ≠ TerminalOutcome.unwound m ∧
    TerminalOutcome.returned r m ≠ TerminalOutcome.aborted m ∧
    TerminalOutcome.unwound (Ret := Val) m ≠ TerminalOutcome.aborted m) ∧
  decodeScalar
      { width := .i8, signed := true, bits := BitVec.ofNat 128 255 } =
    Int.negSucc 0 ∧
  Trusted.MirEnvelopeTheoremV1
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody, canaryNeverParamBody false,
                 canaryUnsafeGuardedBody true] }
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := {
          postReturn := fun _ r _ => r = .unit
          effects := canaryTotalEffects } },
      { identity := "canary::never_param"
        sig := { isUnsafe := false, abi := .rust, params := [.never],
                 ret := .unit }
        contract := { effects := canaryTotalEffects } },
      { identity := "canary::unsafe_guarded"
        sig := { isUnsafe := true, abi := .rust, params := [.bool],
                 ret := u32Ty }
        contract := {
          safetyPre := fun q => q.args = [.bool true]
          postReturn := fun _ r _ => r = u32Val 42
          effects := canaryTotalEffects } } ]
    []
    []
    [.forallSafety, .termination]
    defaultMirDownstreamGaps ∧
  Trusted.MirEnvelopeTheoremV2
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 2
      bodies := [canarySafeUnitBody] }
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := {
          postReturn := fun _ r _ => r = .unit
          effects := canaryTotalEffects } } ]
    []
    []
    [.forallSafety, .termination]
    (.unbridgedSemantics "mir_profile_v2" ::
     .callerMemoryThreadIsolation "mir_profile_v2" ::
     defaultMirDownstreamGaps) ∧
  EnvelopeTheorem (mkEnvelope
    MirProfileV2
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 2
      bodies := [canaryV2RefBody] }
    [ { identity := "canary::v2_ref"
        sig := { isUnsafe := false, abi := .rust,
                 params := [.ref .shared u8Ty], ret := .unit }
        contract := {
          postReturn := fun _ r _ => r = .unit
          effects := canaryTotalEffects } } ]
    []
    []
    [.forallSafety, .termination]
    (.unbridgedSemantics "mir_profile_v2" ::
     .callerMemoryThreadIsolation "mir_profile_v2" ::
     defaultMirDownstreamGaps)) ∧
  EnvelopeTheorem (mkEnvelope
    MirProfileV2
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 2
      bodies := [canaryV2RawPtrBody] }
    [ { identity := "canary::v2_raw_ptr"
        sig := { isUnsafe := false, abi := .rust,
                 params := [.rawPtr .shared u8Ty], ret := .unit }
        contract := {
          postReturn := fun _ r _ => r = .unit
          effects := canaryTotalEffects } } ]
    []
    []
    [.forallSafety, .termination]
    (.unbridgedSemantics "mir_profile_v2" ::
     .callerMemoryThreadIsolation "mir_profile_v2" ::
     .callerRawPtrAliasing "mir_profile_v2" ::
     defaultMirDownstreamGaps)) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV1
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryUnsafeGuardedBody false] }
    [ { identity := "canary::unsafe_guarded"
        sig := { isUnsafe := false, abi := .rust, params := [.bool],
                 ret := u32Ty }
        contract := {
          safetyPre := fun _ => False
          effects := canaryTotalEffects } } ]
    []
    []
    [.forallSafety, .termination]
    defaultMirDownstreamGaps) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV1
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody] }
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := {
          behaviorPre := fun _ => False
          effects := canaryTotalEffects }
        requireInhabited := false } ]
    []
    []
    [.forallSafety, .termination]
    defaultMirDownstreamGaps) ∧
  EnvelopeTheorem (mkEnvelope
    MirProfileV1
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody] }
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := {
          behaviorPre := fun _ => False
          effects := canaryTotalEffects }
        requireInhabited := false } ]
    []
    []
    [.forallSafety, .termination]
    (.waivedInhabitation "canary::safe_unit" :: defaultMirDownstreamGaps)) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV2
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 2
      bodies := [canarySafeUnitBody] }
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := { effects := canaryPartialEffects } } ]
    []
    []
    [.forallSafety]
    defaultMirDownstreamGaps) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV2
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 2
      bodies := [canarySafeUnitBody] }
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := { effects := canaryPartialEffects } } ]
    []
    []
    [.forallSafety]
    (.unbridgedSemantics "mir_profile_v2" :: defaultMirDownstreamGaps)) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV2
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 2
      bodies := [canaryV2RawPtrBody] }
    [ { identity := "canary::v2_raw_ptr"
        sig := { isUnsafe := false, abi := .rust,
                 params := [.rawPtr .shared u8Ty], ret := .unit }
        contract := { effects := canaryPartialEffects } } ]
    []
    []
    [.forallSafety]
    (.unbridgedSemantics "mir_profile_v2" ::
     .callerMemoryThreadIsolation "mir_profile_v2" ::
     defaultMirDownstreamGaps)) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV2
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 2
      bodies := [canaryV2MixedBody] }
    [ { identity := "canary::v2_mixed"
        sig := { isUnsafe := false, abi := .rust,
                 params := [.ref .shared u8Ty], ret := .unit }
        contract := { effects := canaryPartialEffects } } ]
    []
    []
    [.forallSafety]
    (.unbridgedSemantics "mir_profile_v2" ::
     .callerMemoryThreadIsolation "mir_profile_v2" ::
     .callerRawPtrAliasing "mir_profile_v2" :: defaultMirDownstreamGaps)) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV1
    { scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody] }
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := { effects := canaryPartialEffects } } ]
    []
    []
    [.forallSafety]
    defaultMirDownstreamGaps) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV1
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody, canaryUnsafeGuardedBody false] }
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := { effects := canaryPartialEffects } } ]
    []
    []
    [.forallSafety]
    defaultMirDownstreamGaps) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    canaryExternalStubModel
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody] }
    []
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := {
          postReturn := fun _ _ _ => False
          effects := canaryTotalEffects } } ]
    []
    [.forallSafety]
    (.assumedExternalCallee "canary::safe_unit" :: defaultMirDownstreamGaps)) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV1
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody] }
    []
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := { effects := canaryPartialEffects } } ]
    []
    []
    (.assumedExternalCallee "canary::safe_unit" :: defaultMirDownstreamGaps)) ∧
  ¬ StubRealizable MirProfileV2 canaryV2RetRefBody
      { postReturn := fun _ r _ => r = .ptr ⟨none, 0, .isize⟩
        effects := canaryTotalEffects } ∧
  ¬ StubRealizable MirProfileV2 canaryV2RetRefBody
      { postReturn := fun _ r m =>
          r = .ptr ⟨some 99, 0, .isize⟩ ∧ m = ⟨[]⟩
        effects := canaryTotalEffects } ∧
  ¬ StubRealizable MirProfileV1 canarySafeUnitBody
      { postReturn := fun _ r m => r = .unit ∧ m ≠ ⟨[]⟩
        effects := canaryTotalEffects } ∧
  ¬ StubRealizable MirProfileV2 canarySafeUnitBody
      { postReturn := fun _ _ _ => False
        postUnwind := fun _ m => validCallerMemory m = false
        effects := {
          terminates := true, noUnwind := false, noAbort := true } } ∧
  ¬ StubRealizable MirProfileV2 canarySafeUnitBody
      { postReturn := fun _ _ _ => False
        postAbort := fun _ m => validCallerMemory m = false
        effects := {
          terminates := true, noUnwind := true, noAbort := false } } ∧
  EnvelopeTheorem (mkEnvelope
    canaryExternalStubModel
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody, canaryUnsafeGuardedBody false] }
    []
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := {
          postReturn := fun _ r _ => r = .unit
          effects := canaryTotalEffects } } ]
    [ { identity := "canary::unsafe_guarded"
        sig := { isUnsafe := false, abi := .rust, params := [.bool],
                 ret := u32Ty }
        safetyPre := fun _ => True
        witnessPre := fun q => q.args = [.bool false] } ]
    [.existsWitness]
    (.configuredReferenceScope "lean_miri_v1_deinit_moved_place" ::
     .assumedExternalCallee "canary::safe_unit" ::
     defaultMirDownstreamGaps)) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV1
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryUnsafeGuardedBody false] }
    []
    []
    [ { identity := "canary::unsafe_guarded"
        sig := { isUnsafe := false, abi := .rust, params := [.bool],
                 ret := u32Ty }
        safetyPre := fun _ => True
        witnessPre := fun q => q.args = [.bool false] } ]
    [.existsWitness]
    defaultMirDownstreamGaps) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    canaryForwardSimMirModel
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryUnsafeGuardedBody false] }
    []
    []
    [ { identity := "canary::unsafe_guarded"
        sig := { isUnsafe := false, abi := .rust, params := [.bool],
                 ret := u32Ty }
        safetyPre := fun _ => True
        witnessPre := fun q => q.args = [.bool false] } ]
    [.existsWitness]
    defaultMirDownstreamGaps) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    canaryForwardSimMirModel
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody] }
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := { effects := canaryTotalEffects } } ]
    []
    []
    [.forallSafety, .termination]
    defaultMirDownstreamGaps) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV1
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canaryUnsafeGuardedBody true] }
    []
    []
    [ { identity := "canary::unsafe_guarded"
        sig := { isUnsafe := true, abi := .rust, params := [.bool],
                 ret := u32Ty }
        safetyPre := fun q => q.args = [.bool true]
        witnessPre := fun _ => True } ]
    [.existsWitness]
    (.configuredReferenceScope "lean_miri_v1_deinit_moved_place" ::
     defaultMirDownstreamGaps)) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV1
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody] }
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := {
          postReturn := fun _ r _ => r = .unit
          effects := canaryTotalEffects } } ]
    []
    []
    [.forallSafety, .termination]
    []) ∧
  ¬ EnvelopeTheorem (mkEnvelope
    MirProfileV2
    { scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 2
      bodies := [canarySafeUnitBody] }
    [ { identity := "canary::safe_unit"
        sig := { isUnsafe := false, abi := .rust, params := [], ret := .unit }
        contract := { effects := canaryPartialEffects } } ]
    []
    []
    [.forallSafety]
    [ .unbridgedSemantics "mir_profile_v2",
      .callerMemoryThreadIsolation "mir_profile_v2",
      .unverifiedDownstream "rustc_mir_opt",
      .unverifiedDownstream "linker",
      .unverifiedDownstream "microarch_timing" ]) ∧
  OracleCertificate MirProfileV1
      (.biFaultEquiv "lean_miri_v1_deinit_moved_place") True True ∧
  ¬ OracleCertificate MirProfileV2 (.unbridged "mir_profile_v2")
      True True ∧
  (∀ c : Crate, CrateEnvelopeTheorem c ↔ CrateTheorem c) ∧
  (∀ c : Crate, UnitEnvelopeTheorem c ↔ UnitTheorem c) ∧
  (∀ c : CrateV2, CrateEnvelopeTheoremV2 c ↔ CrateTheoremV2 c) ∧
  (∀ c : CrateV2, UnitEnvelopeTheoremV2 c ↔ UnitTheoremV2 c)

/-- Shared positive `EnvelopeTheorem` helper for single-argument Profile v2
bodies returning `.unit`. -/
theorem v2_unit_1arg_envelope_ok (idStr : String) (paramTy : MirTy)
    (gaps : List DisclosedGap)
    (hNonEmptyId : idStr ≠ "")
    (hAdmProg :
      MirProfileV2.programAdmitted {
        scope := .crate
        pointerWidthBits := 64
        mirProfileVersion := 2
        bodies := [{
          argumentCount := 1
          locals := [.unit, paramTy]
          basicBlocks := [{ statements := [], terminator := .return_ }]
          isUnsafe := false
          identity := idStr
        }] } = true)
    (hAdmBody :
      MirProfileV2.bodyAdmitted {
        scope := .crate
        pointerWidthBits := 64
        mirProfileVersion := 2
        bodies := [{
          argumentCount := 1
          locals := [.unit, paramTy]
          basicBlocks := [{ statements := [], terminator := .return_ }]
          isUnsafe := false
          identity := idStr
        }] } {
          argumentCount := 1
          locals := [.unit, paramTy]
          basicBlocks := [{ statements := [], terminator := .return_ }]
          isUnsafe := false
          identity := idStr
        } = true)
    (hUniq :
      MirProfileV2.uniqueIdentities {
        scope := .crate
        pointerWidthBits := 64
        mirProfileVersion := 2
        bodies := [{
          argumentCount := 1
          locals := [.unit, paramTy]
          basicBlocks := [{ statements := [], terminator := .return_ }]
          isUnsafe := false
          identity := idStr
        }] } = true)
    (hLocsSup :
      ([.unit, paramTy] : List MirTy).all isSupportedV2LocalTy = true)
    (hTyBeq : MirTy.beq paramTy paramTy = true)
    (hUnbridged : DisclosedGap.unbridgedSemantics "mir_profile_v2" ∈ gaps)
    (hDownstream : ∀ g, g ∈ defaultMirDownstreamGaps → g ∈ gaps)
    (hBodyGaps :
      ∀ g, g ∈ mirProfileV2RequiredGaps {
        argumentCount := 1
        locals := [.unit, paramTy]
        basicBlocks := [{ statements := [], terminator := .return_ }]
        isUnsafe := false
        identity := idStr
      } → g ∈ gaps)
    (hWitness :
      ∃ q0, ValidEntryArgsV2 {
        argumentCount := 1
        locals := [.unit, paramTy]
        basicBlocks := [{ statements := [], terminator := .return_ }]
        isUnsafe := false
        identity := idStr
      } q0) :
    EnvelopeTheorem (mkEnvelope
      MirProfileV2
      { scope := .crate
        pointerWidthBits := 64
        mirProfileVersion := 2
        bodies := [{
          argumentCount := 1
          locals := [.unit, paramTy]
          basicBlocks := [{ statements := [], terminator := .return_ }]
          isUnsafe := false
          identity := idStr
        }] }
      [ { identity := idStr
          sig := { isUnsafe := false, abi := .rust,
                   params := [paramTy], ret := .unit }
          contract := {
            postReturn := fun _ r _ => r = .unit
            effects := canaryTotalEffects } } ]
      []
      []
      [.forallSafety, .termination]
      gaps) := by
  let body : Body := {
    argumentCount := 1
    locals := [.unit, paramTy]
    basicBlocks := [{ statements := [], terminator := .return_ }]
    isUnsafe := false
    identity := idStr
  }
  let progV2 : Program := {
    scope := .crate
    pointerWidthBits := 64
    mirProfileVersion := 2
    bodies := [body]
  }
  have hExec :
      ∀ (v : Val) (callerMem : CallerMemory),
        ValidEntryArgsV2 body { args := [v], callerMem := callerMem } →
        execProgV2 (entryProgForBody progV2 0) 1
          { args := [v], callerMem := callerMem }
          (fun o => o = .returned ⟨.unit, callerMem⟩) := by
    intro v callerMem hDom
    have hValCm : validCallerMemory callerMem = true := hDom.1
    have hChk : checkArgsMatchV2 [v] [paramTy] = true := hDom.2.1
    have hRefs :
        refsValidInMemList (entryMemoryWithCaller callerMem)
          [paramTy] [v] = true := hDom.2.2.1
    have hDisj :
        spansPairwiseDisjoint
          (refAccessSpansList [paramTy] [v]) = true := hDom.2.2.2
    have hInit :
        initStateV2 (entryProgForBody progV2 0)
          { args := [v], callerMem := callerMem } =
        Except.ok {
          frames := [{
            defId := 0
            blockIdx := 0
            stmtIdx := 0
            locals := [LocalSlot.immediate (some .unit),
                       LocalSlot.immediate (some v)]
          }]
          callerMem := callerMem
          mem := entryMemoryForArgsV2 callerMem [paramTy] [v]
        } := by
      have hRefsForArgs :
          refsValidInMemList (entryMemoryForArgsV2 callerMem [paramTy] [v])
            [paramTy] [v] = true := by
        rw [Anneal.MirWp.refsValidInMemList_allocations_eq
          (Anneal.MirWp.entryMemoryForArgsV2_allocations_eq callerMem [paramTy] [v])]
        exact hRefs
      simp only [initStateV2, entryProgForBody, Trusted.MirSemantics.getElem?,
        progV2, body, List.drop, List.take,
        hValCm, hLocsSup, hChk, hRefsForArgs, hDisj]
      rfl
    have hRet :
        evalStepV2 (entryProgForBody progV2 0) {
          frames := [{
            defId := 0
            blockIdx := 0
            stmtIdx := 0
            locals := [LocalSlot.immediate (some .unit),
                       LocalSlot.immediate (some v)]
          }]
          callerMem := callerMem
          mem := entryMemoryForArgsV2 callerMem [paramTy] [v]
        } = StepResult.done (TerminalOut.returned ⟨.unit, callerMem⟩) := by
      have hExt :=
        extractCallerMemory_entryMemoryForArgsV2 callerMem [paramTy] [v] hValCm
      change
        StepResult.done (TerminalOut.returned ⟨.unit,
          extractCallerMemory callerMem
            (entryMemoryForArgsV2 callerMem [paramTy] [v])⟩) =
        StepResult.done (TerminalOut.returned ⟨.unit, callerMem⟩)
      rw [hExt]
    unfold execProgV2
    rw [hInit]
    change
      match evalStepV2 (entryProgForBody progV2 0) {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 0
          locals := [LocalSlot.immediate (some .unit),
                     LocalSlot.immediate (some v)]
        }]
        callerMem := callerMem
        mem := entryMemoryForArgsV2 callerMem [paramTy] [v]
      } with
      | StepResult.step _ => False
      | StepResult.done out => out = .returned ⟨.unit, callerMem⟩
      | StepResult.fault _ => False
    rw [hRet]
  refine ⟨⟨nonEmpty_profile_v2_id, hAdmProg, ?_, hUniq,
           fun h => Bool.noConfusion h, ⟨rfl, hUnbridged⟩, ?_, hDownstream⟩,
          ?_, ⟨hNonEmptyId, absurd_mem_nil, True.intro⟩,
          ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩
  · intro defId b hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact hAdmBody
    | succ _ =>
      dsimp [progV2, Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro cs hMem
    cases hMem with
    | head => exact ⟨rfl, absurd_mem_nil⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hNil => cases hNil
  · intro _ _
    exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
  · intro e hMem
    cases hMem with
    | head =>
      refine ⟨0, body, rfl, rfl, rfl, ?_, hBodyGaps, ?_, ?_, ?_⟩
      · unfold MirProfileV2 mkMirExecutionModel bodyMatchesMirSignature body
        dsimp only [MirSignature.isUnsafe, MirSignature.abi,
          MirSignature.params, MirSignature.ret]
        change true && true && true && (MirTy.beq paramTy paramTy && true) &&
          true = true
        rw [hTyBeq]
        rfl
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          have hChk := hDom.2.1
          cases args with
          | nil => exact Bool.noConfusion hChk
          | cons v rest =>
            cases rest with
            | cons w rs =>
              dsimp only [body, List.drop, List.take, checkArgsMatchV2] at hChk
              cases hCv : checkValV2 v paramTy <;>
                rw [hCv] at hChk <;> exact Bool.noConfusion hChk
            | nil =>
              exact (spec_and_behaviorV2_of_exec_eq
                (hExec v callerMem hDom)).1
      · intro q hDom _
        cases q with
        | mk args callerMem =>
          have hValCm : validCallerMemory callerMem = true := hDom.1
          have hChk := hDom.2.1
          cases args with
          | nil => exact Bool.noConfusion hChk
          | cons v rest =>
            cases rest with
            | cons w rs =>
              dsimp only [body, List.drop, List.take, checkArgsMatchV2] at hChk
              cases hCv : checkValV2 v paramTy <;>
                rw [hCv] at hChk <;> exact Bool.noConfusion hChk
            | nil =>
              have hSpec := spec_and_behaviorV2_of_exec_eq
                (hExec v callerMem hDom)
              refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
              · intro r m ⟨out, hBeh, hMap⟩
                have hSat := hSpec.2.2.2 _ rfl
                have hEq := hSat.2 out hBeh
                subst hEq
                injection hMap with hR hM
                subst hR hM
                dsimp only [MirProfileV2, mkMirExecutionModel,
                  ValidMirReturnValV2, body, Trusted.MirSemantics.getElem?,
                  checkValV2, refsStayInCallerMem, refAllocIds, List.all,
                  refsValidInMem, refAccessSpans, spansPairwiseDisjoint]
                refine And.intro
                  (And.intro rfl (And.intro hValCm
                    (And.intro rfl (And.intro rfl rfl))))
                  rfl
              · intro m ⟨out, hBeh, hMap⟩
                have hSat := hSpec.2.2.2 _ rfl
                have hEq := hSat.2 out hBeh
                subst hEq
                cases hMap
              · intro m ⟨out, hBeh, hMap⟩
                have hSat := hSpec.2.2.2 _ rfl
                have hEq := hSat.2 out hBeh
                subst hEq
                cases hMap
      · have ⟨q0, hQ0⟩ := hWitness
        exact Or.inl ⟨rfl, Or.inl ⟨q0, hQ0,
          ⟨fun h => Bool.noConfusion h, True.intro⟩⟩⟩
    | tail _ hNil => cases hNil
  · intro defId bodyAt hGet
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact List.Mem.head _
    | succ _ =>
      dsimp [progV2, Trusted.MirSemantics.getElem?] at hGet
      cases hGet

/-- Complete Pass-1 verification envelope canary proof. -/
theorem framework_canary : FrameworkCanaryClaim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl,
          ⟨fun h => Bool.noConfusion h,
           fun h => Bool.noConfusion h,
           fun h => Bool.noConfusion h⟩,
          fun h => Bool.noConfusion (h.1 rfl),
          rfl,
          fun r m => ⟨(fun h => by cases h),
                      (fun h => by cases h),
                      (fun h => by cases h)⟩,
          rfl,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          crateEnvelopeTheorem_iff_crateTheorem,
          unitEnvelopeTheorem_iff_unitTheorem,
          crateEnvelopeTheoremV2_iff_crateTheoremV2,
          unitEnvelopeTheoremV2_iff_unitTheoremV2⟩
  · let prog3 : Program := {
      scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody, canaryNeverParamBody false,
                 canaryUnsafeGuardedBody true] }
    refine ⟨⟨nonEmpty_profile_id, rfl, ?_, rfl,
             fun h => Bool.noConfusion h, nonEmpty_oracle_id, ?_,
             fun _ h => h⟩,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro defId body hGet
      cases defId with
      | zero =>
        injection hGet with hEq
        subst hEq
        rfl
      | succ n =>
        cases n with
        | zero =>
          injection hGet with hEq
          subst hEq
          rfl
        | succ m =>
          cases m with
          | zero =>
            injection hGet with hEq
            subst hEq
            rfl
          | succ _ =>
            dsimp [prog3, Trusted.MirSemantics.getElem?] at hGet
            cases hGet
    · intro cs hMem
      cases hMem with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hMem2 =>
        cases hMem2 with
        | head => exact ⟨rfl, absurd_mem_nil⟩
        | tail _ hNil => cases hNil
    · intro e hMem
      refine ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
    · refine ⟨ne_string_of_len_beq_false rfl, ?_,
              ne_string_of_len_beq_false rfl, ?_,
              ne_string_of_len_beq_false rfl,
              ⟨absurd_mem_nil, True.intro⟩⟩
      · intro t hMem
        cases hMem with
        | head => exact ne_string_of_len_beq_false rfl
        | tail _ hMem2 =>
          cases hMem2 with
          | head => exact ne_string_of_len_beq_false rfl
          | tail _ hNil => cases hNil
      · intro t hMem
        cases hMem with
        | head => exact ne_string_of_len_beq_false rfl
        | tail _ hNil => cases hNil
    · intro e hMem
      cases hMem with
      | head =>
        refine ⟨0, canarySafeUnitBody, rfl, rfl, rfl, rfl,
                absurd_mem_nil, ?_, ?_, ?_⟩
        · intro q hDom _
          cases q with
          | mk args callerMem =>
            dsimp at hDom
            rw [hDom.2]
            cases args with
            | nil =>
              exact (spec_and_behavior_of_wp_eq (p := entryProgForBody prog3 0)
                (q := { args := [] }) (fuel := 1)
                (out := .returned ⟨.unit, ⟨[]⟩⟩)
                (wpProg_of_execProg rfl)).1
            | cons _ _ => exact Bool.noConfusion hDom.1
        · intro q hDom _
          cases q with
          | mk args callerMem =>
            dsimp at hDom
            rw [hDom.2]
            cases args with
            | nil =>
              have hSpec :=
                spec_and_behavior_of_wp_eq (p := entryProgForBody prog3 0)
                  (q := { args := [] }) (fuel := 1)
                  (out := .returned ⟨.unit, ⟨[]⟩⟩)
                  (wpProg_of_execProg rfl)
              refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
              · intro r m ⟨out, hBeh, hMap⟩
                have hSat := hSpec.2.2.2 _ rfl
                have hEq := hSat.2 out hBeh
                subst hEq
                injection hMap with hR hM
                subst hR hM
                exact ⟨⟨rfl, rfl⟩, rfl⟩
              · intro m ⟨out, hBeh, hMap⟩
                have hSat := hSpec.2.2.2 _ rfl
                have hEq := hSat.2 out hBeh
                subst hEq
                cases hMap
              · intro m ⟨out, hBeh, hMap⟩
                have hSat := hSpec.2.2.2 _ rfl
                have hEq := hSat.2 out hBeh
                subst hEq
                cases hMap
            | cons _ _ => exact Bool.noConfusion hDom.1
        · exact Or.inl ⟨rfl, Or.inl ⟨{ args := [] }, ⟨rfl, rfl⟩,
            ⟨fun h => Bool.noConfusion h, True.intro⟩⟩⟩
      | tail _ hMem2 =>
        cases hMem2 with
        | head =>
          have hEmptyDom :
              ∀ q : Query,
                ¬ MirProfileV1.entryDom (canaryNeverParamBody false) q := by
            intro q hDom
            cases q with
            | mk args _ =>
              cases args with
              | nil => exact Bool.noConfusion hDom.1
              | cons v rest =>
                have hCheck : checkVal v .never = true := by
                  have h1 := hDom.1
                  revert h1
                  change
                    (checkVal v .never && checkArgsMatch rest []) = true → _
                  cases checkVal v .never <;> intro h <;>
                    first | rfl | exact Bool.noConfusion h
                rw [checkVal_never_false v] at hCheck
                exact Bool.noConfusion hCheck
          refine ⟨1, canaryNeverParamBody false, rfl, rfl, rfl, rfl,
                  absurd_mem_nil,
                  fun q hDom _ => False.elim (hEmptyDom q hDom),
                  fun q hDom _ => False.elim (hEmptyDom q hDom),
                  Or.inl ⟨rfl, Or.inr hEmptyDom⟩⟩
        | tail _ hMem3 =>
          cases hMem3 with
          | head =>
            refine ⟨2, canaryUnsafeGuardedBody true, rfl, rfl, rfl, rfl,
                    absurd_mem_nil, ?_, ?_, ?_⟩
            · intro q hDom hSafe
              cases q with
              | mk args callerMem =>
                dsimp at hDom hSafe
                have hArgs : args = [.bool true] := hSafe rfl
                subst hArgs
                rw [hDom.2]
                exact (spec_and_behavior_of_wp_eq
                  (p := entryProgForBody prog3 2)
                  (q := { args := [.bool true] }) (fuel := 3)
                  (out := .returned ⟨u32Val 42, ⟨[]⟩⟩)
                  (wpProg_of_execProg rfl)).1
            · intro q hDom hBeh
              cases q with
              | mk args callerMem =>
                dsimp at hDom hBeh
                have hArgs : args = [.bool true] := hBeh.1 rfl
                subst hArgs
                rw [hDom.2]
                have hSpec :=
                  spec_and_behavior_of_wp_eq
                    (p := entryProgForBody prog3 2)
                    (q := { args := [.bool true] }) (fuel := 3)
                    (out := .returned ⟨u32Val 42, ⟨[]⟩⟩)
                    (wpProg_of_execProg rfl)
                refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
                · intro r m ⟨out, hBehOut, hMap⟩
                  have hSat := hSpec.2.2.2 _ rfl
                  have hEq := hSat.2 out hBehOut
                  subst hEq
                  injection hMap with hR hM
                  subst hR hM
                  exact ⟨⟨rfl, rfl⟩, rfl⟩
                · intro m ⟨out, hBehOut, hMap⟩
                  have hSat := hSpec.2.2.2 _ rfl
                  have hEq := hSat.2 out hBehOut
                  subst hEq
                  cases hMap
                · intro m ⟨out, hBehOut, hMap⟩
                  have hSat := hSpec.2.2.2 _ rfl
                  have hEq := hSat.2 out hBehOut
                  subst hEq
                  cases hMap
            · exact Or.inl ⟨rfl, Or.inl ⟨{ args := [.bool true] }, ⟨rfl, rfl⟩,
                ⟨fun _ => rfl, True.intro⟩⟩⟩
          | tail _ hNil => cases hNil
    · intro _ hNil
      cases hNil
    · intro _ hNil
      cases hNil
    · intro defId body hGet
      cases defId with
      | zero =>
        injection hGet with hEq
        subst hEq
        exact List.Mem.head _
      | succ n =>
        cases n with
        | zero =>
          injection hGet with hEq
          subst hEq
          exact List.Mem.tail _ (List.Mem.head _)
        | succ m =>
          cases m with
          | zero =>
            injection hGet with hEq
            subst hEq
            exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
          | succ _ =>
            dsimp [prog3, Trusted.MirSemantics.getElem?] at hGet
            cases hGet
  · let progV2 : Program := {
      scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 2
      bodies := [canarySafeUnitBody] }
    have hExecSafeUnit :
        ∀ (callerMem : CallerMemory),
          validCallerMemory callerMem = true →
          execProgV2 (entryProgForBody progV2 0) 1
            { args := [], callerMem := callerMem }
            (fun o => o = .returned ⟨.unit, callerMem⟩) := by
      intro callerMem hValCm
      have hInit :
          initStateV2 (entryProgForBody progV2 0)
            { args := [], callerMem := callerMem } =
          Except.ok {
            frames := [{
              defId := 0
              blockIdx := 0
              stmtIdx := 0
              locals := [LocalSlot.immediate (some .unit)]
            }]
            callerMem := callerMem
            mem := entryMemoryWithCaller callerMem
          } := by
        unfold initStateV2 entryProgForBody
        dsimp only [progV2, Query.callerMem, Program.pointerWidthBits,
          Program.mirProfileVersion]
        rw [hValCm]
        rfl
      have hRet :
          evalStepV2 (entryProgForBody progV2 0) {
            frames := [{
              defId := 0
              blockIdx := 0
              stmtIdx := 0
              locals := [LocalSlot.immediate (some .unit)]
            }]
            callerMem := callerMem
            mem := entryMemoryWithCaller callerMem
          } = StepResult.done (TerminalOut.returned ⟨.unit, callerMem⟩) := by
        have hExt :=
          extractCallerMemory_entryMemoryWithCaller callerMem hValCm
        change
          StepResult.done (TerminalOut.returned ⟨.unit,
            extractCallerMemory callerMem
              (entryMemoryWithCaller callerMem)⟩) =
          StepResult.done (TerminalOut.returned ⟨.unit, callerMem⟩)
        rw [hExt]
      unfold execProgV2
      rw [hInit]
      change
        match evalStepV2 (entryProgForBody progV2 0) {
          frames := [{
            defId := 0
            blockIdx := 0
            stmtIdx := 0
            locals := [LocalSlot.immediate (some .unit)]
          }]
          callerMem := callerMem
          mem := entryMemoryWithCaller callerMem
        } with
        | StepResult.step _ => False
        | StepResult.done out => out = .returned ⟨.unit, callerMem⟩
        | StepResult.fault _ => False
      rw [hRet]
    refine ⟨⟨nonEmpty_profile_v2_id, rfl, ?_, rfl,
             fun h => Bool.noConfusion h, ⟨rfl, List.Mem.head _⟩, ?_,
             fun _ h => List.Mem.tail _ (List.Mem.tail _ h)⟩,
            ?_, ⟨ne_string_of_len_beq_false rfl, absurd_mem_nil, True.intro⟩,
            ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩
    · intro defId body hGet
      cases defId with
      | zero =>
        injection hGet with hEq
        subst hEq
        rfl
      | succ _ =>
        dsimp [progV2, Trusted.MirSemantics.getElem?] at hGet
        cases hGet
    · intro cs hMem
      cases hMem with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ h2 =>
        cases h2 with
        | head => exact ⟨rfl, absurd_mem_nil⟩
        | tail _ hNil => cases hNil
    · intro _ _
      exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
    · intro e hMem
      cases hMem with
      | head =>
        refine ⟨0, canarySafeUnitBody, rfl, rfl, rfl, rfl,
                (fun g hg => by
                  rw [eq_of_mem_singleton hg]
                  exact List.Mem.tail _ (List.Mem.head _)), ?_, ?_, ?_⟩
        · intro q hDom _
          cases q with
          | mk args callerMem =>
            have hValCm : validCallerMemory callerMem = true := hDom.1
            have hArgs : args = [] := by
              have hChk := hDom.2.1
              cases args with
              | nil => rfl
              | cons _ _ => exact Bool.noConfusion hChk
            subst hArgs
            exact (spec_and_behaviorV2_of_exec_eq
              (hExecSafeUnit callerMem hValCm)).1
        · intro q hDom _
          cases q with
          | mk args callerMem =>
            have hValCm : validCallerMemory callerMem = true := hDom.1
            have hArgs : args = [] := by
              have hChk := hDom.2.1
              cases args with
              | nil => rfl
              | cons _ _ => exact Bool.noConfusion hChk
            subst hArgs
            have hSpec := spec_and_behaviorV2_of_exec_eq
              (hExecSafeUnit callerMem hValCm)
            refine ⟨fun _ => hSpec.2.2.1, ?_, ?_, ?_⟩
            · intro r m ⟨out, hBeh, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBeh
              subst hEq
              injection hMap with hR hM
              subst hR hM
              dsimp only [MirProfileV2, mkMirExecutionModel,
                ValidMirReturnValV2, canarySafeUnitBody,
                Trusted.MirSemantics.getElem?, checkValV2,
                refsStayInCallerMem, refAllocIds, List.all,
                refsValidInMem, refAccessSpans, spansPairwiseDisjoint]
              refine And.intro
                (And.intro rfl (And.intro hValCm
                  (And.intro rfl (And.intro rfl rfl))))
                rfl
            · intro m ⟨out, hBeh, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBeh
              subst hEq
              cases hMap
            · intro m ⟨out, hBeh, hMap⟩
              have hSat := hSpec.2.2.2 _ rfl
              have hEq := hSat.2 out hBeh
              subst hEq
              cases hMap
        · exact Or.inl ⟨rfl, Or.inl ⟨{ args := [], callerMem := ⟨[]⟩ },
            ⟨rfl, rfl, rfl, rfl⟩,
            ⟨fun h => Bool.noConfusion h, True.intro⟩⟩⟩
      | tail _ hNil => cases hNil
    · intro defId body hGet
      cases defId with
      | zero =>
        injection hGet with hEq
        subst hEq
        exact List.Mem.head _
      | succ _ =>
        dsimp [progV2, Trusted.MirSemantics.getElem?] at hGet
        cases hGet
  · refine v2_unit_1arg_envelope_ok "canary::v2_ref" (.ref .shared u8Ty)
      (.unbridgedSemantics "mir_profile_v2" ::
       .callerMemoryThreadIsolation "mir_profile_v2" ::
       defaultMirDownstreamGaps)
      (ne_string_of_len_beq_false rfl) rfl rfl rfl rfl rfl
      (List.Mem.head _)
      (fun _ h => List.Mem.tail _ (List.Mem.tail _ h))
      (fun g hg => by
        rw [eq_of_mem_singleton hg]
        exact List.Mem.tail _ (List.Mem.head _))
      ⟨{ args := [.ptr ⟨some 1, 0, .isize⟩]
         callerMem := ⟨[{
           allocId := 1
           alignLog2 := 0
           mutability := .shared
           bytes := [.init 0]
           live := true }]⟩ },
       ⟨rfl, rfl, rfl, rfl⟩⟩
  · refine v2_unit_1arg_envelope_ok "canary::v2_raw_ptr"
      (.rawPtr .shared u8Ty)
      (.unbridgedSemantics "mir_profile_v2" ::
       .callerMemoryThreadIsolation "mir_profile_v2" ::
       .callerRawPtrAliasing "mir_profile_v2" ::
       defaultMirDownstreamGaps)
      (ne_string_of_len_beq_false rfl) rfl rfl rfl rfl rfl
      (List.Mem.head _)
      (fun _ h => List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ h)))
      (fun g hg => by
        cases hg with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ hTail =>
          rw [eq_of_mem_singleton hTail]
          exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
      ⟨{ args := [.ptr ⟨none, 1, .isize⟩], callerMem := ⟨[]⟩ },
       ⟨rfl, rfl, rfl, rfl⟩⟩
  · intro hEnv
    have ⟨defId, body, hGet, hSat⟩ := hEnv.2.2.2.1 _ (List.Mem.head _)
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      have hWf := hSat.2.2.2.2.1 { args := [.bool false] } ⟨rfl, rfl⟩
        (fun h => Bool.noConfusion h)
      have hNeg : NegativeCanaryClaim
          (entryProgForBody {
            scope := .crate
            pointerWidthBits := 64
            mirProfileVersion := 1
            bodies := [canaryUnsafeGuardedBody false] } 0)
          { args := [.bool false] } .undefined .unsupported :=
        negativeCanary_of_execFault (fuel := 2)
          (fun h => FaultKind.noConfusion h) rfl
      exact hNeg.2.2 hWf
    | succ _ =>
      dsimp [MirProfileV1, mkMirExecutionModel,
             Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro hEnv
    have ⟨defId, body, hGet, hSat⟩ := hEnv.2.2.2.1 _ (List.Mem.head _)
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      cases hSat.2.2.2.2.2.2 with
      | inl hReq => exact Bool.noConfusion hReq.1
      | inr hWaiv =>
        have hMem := hWaiv.2
        cases hMem with
        | tail _ h2 =>
          cases h2 with
          | tail _ h3 =>
            cases h3 with
            | tail _ h4 =>
              cases h4 with
              | tail _ h5 => cases h5
    | succ _ =>
      dsimp [MirProfileV1, mkMirExecutionModel,
             Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · let prog1 : Program := {
      scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody] }
    refine ⟨⟨nonEmpty_profile_id, rfl, ?_, rfl,
             fun h => Bool.noConfusion h, nonEmpty_oracle_id, ?_,
             fun _ h => List.Mem.tail _ h⟩,
            ?_, ⟨ne_string_of_len_beq_false rfl,
                 absurd_mem_nil, True.intro⟩,
            ?_, ?_, ?_, ?_⟩
    · intro defId body hGet
      cases defId with
      | zero =>
        injection hGet with hEq
        subst hEq
        rfl
      | succ _ =>
        dsimp [prog1, Trusted.MirSemantics.getElem?] at hGet
        cases hGet
    · intro cs hMem
      cases hMem with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ h2 =>
        cases h2 with
        | head => exact ⟨rfl, absurd_mem_nil⟩
        | tail _ hNil => cases hNil
    · intro _ _
      exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
    · intro e hMem
      cases hMem with
      | head =>
        refine ⟨0, canarySafeUnitBody, rfl, rfl, rfl, rfl,
                absurd_mem_nil, ?_, ?_,
                Or.inr ⟨rfl, List.Mem.head _⟩⟩
        · intro q hDom _
          cases q with
          | mk args callerMem =>
            dsimp at hDom
            rw [hDom.2]
            cases args with
            | nil =>
              exact (spec_and_behavior_of_wp_eq (p := entryProgForBody prog1 0)
                (q := { args := [] }) (fuel := 1)
                (out := .returned ⟨.unit, ⟨[]⟩⟩)
                (wpProg_of_execProg rfl)).1
            | cons _ _ => exact Bool.noConfusion hDom.1
        · intro _ _ hBeh
          exact False.elim hBeh.2
      | tail _ hNil => cases hNil
    · intro _ hNil; cases hNil
    · intro _ hNil; cases hNil
    · intro defId body hGet
      cases defId with
      | zero =>
        injection hGet with hEq
        subst hEq
        exact List.Mem.head _
      | succ _ =>
        dsimp [prog1, Trusted.MirSemantics.getElem?] at hGet
        cases hGet
  · intro hEnv
    have ⟨_, hGap⟩ :=
      unbridged_envelope_requires_gap _ "mir_profile_v2" rfl hEnv
    cases hGap with
    | tail _ h2 =>
      cases h2 with
      | tail _ h3 =>
        cases h3 with
        | tail _ h4 =>
          cases h4 with
          | tail _ h5 => cases h5
  · intro hEnv
    have ⟨defId, body, hGet, hSat⟩ := hEnv.2.2.2.1 _ (List.Mem.head _)
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      have hReq := hSat.2.2.2.1 (.callerMemoryThreadIsolation "mir_profile_v2")
        (List.Mem.head _)
      cases hReq with
      | tail _ h2 =>
        cases h2 with
        | tail _ h3 =>
          cases h3 with
          | tail _ h4 =>
            cases h4 with
            | tail _ h5 =>
              cases h5 with
              | tail _ h6 => cases h6
    | succ _ =>
      dsimp [MirProfileV2, mkMirExecutionModel,
             Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro hEnv
    have ⟨defId, body, hGet, hSat⟩ := hEnv.2.2.2.1 _ (List.Mem.head _)
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      have hReq := hSat.2.2.2.1 (.callerRawPtrAliasing "mir_profile_v2")
        (List.Mem.tail _ (List.Mem.head _))
      cases hReq with
      | tail _ h2 =>
        cases h2 with
        | tail _ h3 =>
          cases h3 with
          | tail _ h4 =>
            cases h4 with
            | tail _ h5 =>
              cases h5 with
              | tail _ h6 =>
                cases h6 with
                | tail _ h7 => cases h7
    | succ _ =>
      dsimp [MirProfileV2, mkMirExecutionModel,
             Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro hEnv
    have hBodyAdm := hEnv.1.2.2.1 0 canaryV2MixedBody rfl
    exact Bool.noConfusion hBodyAdm
  · intro hEnv
    have hGap := partial_scope_envelope_requires_gap _ rfl hEnv
    cases hGap with
    | tail _ h2 =>
      cases h2 with
      | tail _ h3 =>
        cases h3 with
        | tail _ h4 =>
          cases h4 with
          | tail _ h5 => cases h5
  · intro hEnv
    have hCov := hEnv.2.2.2.2.2.2 1 (canaryUnsafeGuardedBody false) rfl
    exact ne_string_of_len_beq_false rfl (eq_of_mem_singleton hCov).symm
  · intro hEnv
    have ⟨defId, body, hGet, hStub⟩ := hEnv.2.2.2.2.1 _ (List.Mem.head _)
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact stub_false_post_unrealizable canaryExternalStubModel
        canarySafeUnitBody { args := [] } ⟨rfl, rfl⟩ hStub.2.2.2.2.2
    | succ _ =>
      dsimp [canaryExternalStubModel, MirProfileV1, mkMirExecutionModel,
             Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro hEnv
    have hNil :=
      no_stubs_of_all_local_model MirProfileV1 (fun _ => rfl) _ _ _ _ _ _ hEnv
    cases hNil
  · intro hReal
    have hStep :=
      hReal { args := [], callerMem := ⟨[]⟩ } ⟨rfl, rfl, rfl, rfl⟩
        ⟨fun h => Bool.noConfusion h, True.intro⟩
    cases hStep with
    | inl hTerm => exact Bool.noConfusion hTerm
    | inr hRest =>
      cases hRest with
      | inl hRet =>
        cases hRet with
        | intro r hMem =>
          cases hMem with
          | intro m hAnd =>
            dsimp only [MirProfileV2, mkMirExecutionModel, ValidMirReturnValV2,
              canaryV2RetRefBody, Trusted.MirSemantics.getElem?] at hAnd
            have hEq : r = .ptr ⟨none, 0, .isize⟩ := hAnd.2
            have hValid := hAnd.1.2.2.2.1
            rw [hEq] at hValid
            unfold refsValidInMem refValidInMem layoutOfTyV2 u8Ty intLayout
              at hValid
            exact Bool.noConfusion hValid
      | inr hRest2 =>
        cases hRest2 with
        | inl hUnw => exact Bool.noConfusion hUnw.1
        | inr hAbt => exact Bool.noConfusion hAbt.1
  · intro hReal
    have hStep :=
      hReal { args := [], callerMem := ⟨[]⟩ } ⟨rfl, rfl, rfl, rfl⟩
        ⟨fun h => Bool.noConfusion h, True.intro⟩
    cases hStep with
    | inl hTerm => exact Bool.noConfusion hTerm
    | inr hRest =>
      cases hRest with
      | inl hRet =>
        cases hRet with
        | intro r hMem =>
          cases hMem with
          | intro m hAnd =>
            dsimp only [MirProfileV2, mkMirExecutionModel, ValidMirReturnValV2,
              canaryV2RetRefBody, Trusted.MirSemantics.getElem?] at hAnd
            have hEq : r = .ptr ⟨some 99, 0, .isize⟩ := hAnd.2.1
            have hMemEq : m = ⟨[]⟩ := hAnd.2.2
            have hValid := hAnd.1.2.2.2.1
            rw [hEq, hMemEq] at hValid
            unfold refsValidInMem refValidInMem layoutOfTyV2 u8Ty intLayout
              entryMemoryWithCaller findAllocation at hValid
            exact Bool.noConfusion hValid
      | inr hRest2 =>
        cases hRest2 with
        | inl hUnw => exact Bool.noConfusion hUnw.1
        | inr hAbt => exact Bool.noConfusion hAbt.1
  · intro hReal
    have hStep :=
      hReal { args := [] } ⟨rfl, rfl⟩
        ⟨fun h => Bool.noConfusion h, True.intro⟩
    cases hStep with
    | inl hTerm => exact Bool.noConfusion hTerm
    | inr hRest =>
      cases hRest with
      | inl hRet =>
        cases hRet with
        | intro _ hMem =>
          cases hMem with
          | intro _ hAnd => exact hAnd.2.2 hAnd.1.2
      | inr hRest2 =>
        cases hRest2 with
        | inl hUnw => exact Bool.noConfusion hUnw.1
        | inr hAbt => exact Bool.noConfusion hAbt.1
  · intro hReal
    have hStep :=
      hReal { args := [], callerMem := ⟨[]⟩ } ⟨rfl, rfl, rfl, rfl⟩
        ⟨fun h => Bool.noConfusion h, True.intro⟩
    cases hStep with
    | inl hTerm => exact Bool.noConfusion hTerm
    | inr hRest =>
      cases hRest with
      | inl hRet =>
        cases hRet with
        | intro _ hMem =>
          cases hMem with
          | intro _ hAnd => exact hAnd.2
      | inr hRest2 =>
        cases hRest2 with
        | inl hUnw =>
          cases hUnw.2 with
          | intro m hAnd =>
            have hVal : validCallerMemory m = true := hAnd.1
            have hBad : validCallerMemory m = false := hAnd.2
            rw [hVal] at hBad
            exact Bool.noConfusion hBad
        | inr hAbt => exact Bool.noConfusion hAbt.1
  · intro hReal
    have hStep :=
      hReal { args := [], callerMem := ⟨[]⟩ } ⟨rfl, rfl, rfl, rfl⟩
        ⟨fun h => Bool.noConfusion h, True.intro⟩
    cases hStep with
    | inl hTerm => exact Bool.noConfusion hTerm
    | inr hRest =>
      cases hRest with
      | inl hRet =>
        cases hRet with
        | intro _ hMem =>
          cases hMem with
          | intro _ hAnd => exact hAnd.2
      | inr hRest2 =>
        cases hRest2 with
        | inl hUnw => exact Bool.noConfusion hUnw.1
        | inr hAbt =>
          cases hAbt.2 with
          | intro m hAnd =>
            have hVal : validCallerMemory m = true := hAnd.1
            have hBad : validCallerMemory m = false := hAnd.2
            rw [hVal] at hBad
            exact Bool.noConfusion hBad
  · let progSR : Program := {
      scope := .crate
      pointerWidthBits := 64
      mirProfileVersion := 1
      bodies := [canarySafeUnitBody, canaryUnsafeGuardedBody false] }
    refine ⟨⟨nonEmpty_profile_id, rfl, ?_, rfl,
             fun h => Bool.noConfusion h, nonEmpty_oracle_id, ?_,
             fun _ h => List.Mem.tail _ (List.Mem.tail _ h)⟩,
            absurd_mem_nil,
            ⟨ne_string_of_len_beq_false rfl,
             ?_,
             ⟨ne_string_of_len_beq_false rfl,
              absurd_mem_nil, True.intro⟩⟩,
            absurd_mem_nil,
            ?_, ?_, ?_⟩
    · intro defId body hGet
      cases defId with
      | zero =>
        injection hGet with hEq
        subst hEq
        rfl
      | succ n =>
        cases n with
        | zero =>
          injection hGet with hEq
          subst hEq
          rfl
        | succ _ =>
          dsimp [progSR, Trusted.MirSemantics.getElem?] at hGet
          cases hGet
    · intro cs hMem
      cases hMem with
      | head =>
        refine ⟨rfl, fun g hg => ?_⟩
        rw [eq_of_mem_singleton hg]
        exact List.Mem.head _
      | tail _ hNil => cases hNil
    · intro t hMem
      cases hMem with
      | head => exact ne_string_of_len_beq_false rfl
      | tail _ hNil => cases hNil
    · intro s hMem
      cases hMem with
      | head =>
        refine ⟨0, canarySafeUnitBody, rfl, rfl, rfl, rfl,
                absurd_mem_nil, List.Mem.tail _ (List.Mem.head _), ?_⟩
        intro _ _ _
        exact Or.inr (Or.inl ⟨.unit, ⟨[]⟩, ⟨rfl, rfl⟩, rfl⟩)
      | tail _ hNil => cases hNil
    · intro r hMem
      cases hMem with
      | head =>
        refine ⟨List.Mem.head _, 1, canaryUnsafeGuardedBody false, rfl,
                rfl, rfl, rfl, absurd_mem_nil,
                { args := [.bool false] }, ⟨rfl, rfl⟩,
                (fun h => Bool.noConfusion h), rfl, ?_⟩
        have hNeg : NegativeCanaryClaim (entryProgForBody progSR 1)
            { args := [.bool false] } .undefined .unsupported :=
          negativeCanary_of_execFault (fuel := 2)
            (fun h => FaultKind.noConfusion h) rfl
        exact hNeg.1
      | tail _ hNil => cases hNil
    · intro defId body hGet
      cases defId with
      | zero =>
        injection hGet with hEq
        subst hEq
        exact List.Mem.head _
      | succ n =>
        cases n with
        | zero =>
          injection hGet with hEq
          subst hEq
          exact List.Mem.tail _ (List.Mem.head _)
        | succ _ =>
          dsimp [progSR, Trusted.MirSemantics.getElem?] at hGet
          cases hGet
  · intro hEnv
    have hReq :=
      (hEnv.1.2.2.2.2.2.2.1 .existsWitness (List.Mem.head _)).2
        (.configuredReferenceScope "lean_miri_v1_deinit_moved_place")
        (List.Mem.head _)
    cases hReq with
    | tail _ h2 =>
      cases h2 with
      | tail _ h3 =>
        cases h3 with
        | tail _ h4 =>
          cases h4 with
          | tail _ h5 => cases h5
  · intro hEnv
    have hLic := hEnv.1.2.2.2.2.2.2.1 .existsWitness (List.Mem.head _)
    exact Bool.noConfusion hLic.1
  · intro hEnv
    have hLic :=
      hEnv.1.2.2.2.2.2.2.1 .termination (List.Mem.tail _ (List.Mem.head _))
    exact Bool.noConfusion hLic.1
  · intro hEnv
    have ⟨_, defId, body, hGet, hRef⟩ :=
      hEnv.2.2.2.2.2.1 _ (List.Mem.head _)
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      have ⟨q, hDom, hSafe, _, hFault⟩ := hRef.2.2.2.2
      cases q with
      | mk args callerMem =>
        have hArgs : args = [.bool true] := hSafe rfl
        have hCm : callerMem = ⟨[]⟩ := hDom.2
        subst hArgs
        subst hCm
        have hWf :
            WellFormed (entryProgForBody {
              scope := .crate
              pointerWidthBits := 64
              mirProfileVersion := 1
              bodies := [canaryUnsafeGuardedBody true] } 0)
              { args := [.bool true] } :=
          (spec_and_behavior_of_wp_eq
            (p := entryProgForBody {
              scope := .crate
              pointerWidthBits := 64
              mirProfileVersion := 1
              bodies := [canaryUnsafeGuardedBody true] } 0)
            (q := { args := [.bool true] }) (fuel := 3)
            (out := .returned ⟨u32Val 42, ⟨[]⟩⟩)
            (wpProg_of_execProg rfl)).1
        exact hWf.2 .undefined hFault
    | succ _ =>
      dsimp [MirProfileV1, mkMirExecutionModel,
             Trusted.MirSemantics.getElem?] at hGet
      cases hGet
  · intro hEnv
    have hGap :=
      modelGaps_of_envelopeTheorem _ hEnv
        (.unverifiedDownstream "rustc_mir_opt") (List.Mem.head _)
    cases hGap
  · intro hEnv
    have hGap :=
      modelGaps_of_envelopeTheorem _ hEnv
        (.unverifiedDownstream "llvm_codegen")
        (List.Mem.tail _ (List.Mem.head _))
    cases hGap with
    | tail _ h2 =>
      cases h2 with
      | tail _ h3 =>
        cases mem_cons_elim h3 with
        | inl hEq =>
          injection hEq with hS
          exact ne_string_of_len_beq_false rfl hS
        | inr h4 =>
          cases mem_cons_elim h4 with
          | inl hEq =>
            injection hEq with hS
            exact ne_string_of_len_beq_false rfl hS
          | inr h5 =>
            cases mem_cons_elim h5 with
            | inl hEq =>
              injection hEq with hS
              exact ne_string_of_len_beq_false rfl hS
            | inr h6 => cases h6
  · exact ⟨rfl, fun _ h => OracleGrade.noConfusion h,
           True.intro, fun _ => True.intro⟩
  · intro hCert
    exact hCert.non_unbridged "mir_profile_v2" rfl

end Anneal.Framework.Canaries

end
