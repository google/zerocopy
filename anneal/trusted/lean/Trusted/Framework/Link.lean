-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:refinement
module
prelude
public import Init.NotationExtra
public import Init.Data.List.Basic
public import Trusted.Framework

@[expose] public section

namespace Trusted.Framework

/-!
# Language-Agnostic Cross-Language Linking Spine (`Trusted.Framework.Link`)

Thin, tactic-free cross-language linking interface parameterized strictly over
`Trusted.Framework` (`ExecutionModel`, `VerificationEnvelope`, `AssumedStub`,
`VerifiedEntry`, `DisclosedGap`) with zero dependency on `Trusted.MirSemantics`
or `Trusted.CppSemantics`:

1. **Frame-parametric ABI simulation convention (`SimConv`):** Relates caller
   and callee signatures (`abiCompat`), queries (`relQuery`), normal returns
   (`relReturn`), unwinds (`relUnwind`), and aborts (`relAbort`) across an
   arbitrary frame witness `Frame`.
2. **Stub discharge judgment (`StubDischargedByVerifiedCallee`):** Requires
   matching symbol identity, ABI compatibility (`abiCompat = true`), monotonic
   effect masks (`EffectMask.le`), safety-precondition transfer, and full
   behavioral pre/postcondition transfer across returns, unwinds, and aborts.
3. **Audited gap erasure (`eraseDischargedStubGap`, `CrossLangLinkedTheorem`):**
   Removes `.assumedExternalCallee sym` from the caller's gap ledger only when
   both envelopes satisfy `EnvelopeTheorem`, the callee entry discharges the
   caller stub via `StubDischargedByVerifiedCallee`, and the callee does not
   itself assume or disclose an external-callee gap for `sym`.

**Demonic relations.** A faithful ABI convention may relate one caller value
to many callee values (for example, unspecified padding bytes or concrete
addresses chosen at run time), and one callee outcome to many caller outcomes.
`StubDischargedByVerifiedCallee` therefore requires every related
`(frame, qb)` to satisfy the callee's preconditions and every related caller
outcome to satisfy the caller's postconditions, plus at least one related value
at each step so the obligations cannot hold vacuously through an empty
relation. It never lets a proof pick a favorable related value.

**Pinning requirement.** `SimConv` is a free parameter here, exactly as
`ExecutionModel` is a free parameter of `EnvelopeTheorem`. A convention that
is not faithful to the real ABI (for example, one relating every caller query
only to a single convenient callee query) would discharge stubs the real
callee does not implement. Soundness therefore requires that a future Pass-1
linking root pin `SimConv` (together with both execution models) inside
`Trusted.*` to a faithful, per-language-pair ABI and value/memory transport
convention; specification and proof modules must never supply `SimConv`.

**Scope.** `CrossLangLinkedTheorem` discharges exactly one stub edge, computing
`effectiveGaps` from the two raw envelope gap ledgers. It defines no
composition of multiple edges; in particular, chaining `effectiveGaps` across
mutually recursive stub edges would be circular and is not licensed here.
-/

/-- Product lattice order on `EffectMask`: `m2` guarantees every termination,
no-unwind, and no-abort restriction guaranteed by `m1`. -/
@[reducible] def EffectMask.le (m1 m2 : EffectMask) : Prop :=
  (m1.terminates = true → m2.terminates = true) ∧
  (m1.noUnwind = true → m2.noUnwind = true) ∧
  (m1.noAbort = true → m2.noAbort = true)

/-- Frame-parametric cross-language ABI and value/memory simulation convention
relating a caller stub profile `(SigA, QA, RA, MA)` to a verified callee
profile `(SigB, QB, RB, MB)`. Every relation may be one-to-many; see
`StubDischargedByVerifiedCallee` for how each is quantified. -/
structure SimConv (SigA QA RA MA SigB QB RB MB Frame : Type) where
  abiCompat : SigA → SigB → Bool
  relQuery  : Frame → QA → QB → Prop
  relReturn : Frame → RB → MB → RA → MA → Prop
  relUnwind : Frame → MB → MA → Prop
  relAbort  : Frame → MB → MA → Prop

/-- Discharge judgment proving that a verified callee contract `e` refines a
caller's external stub `s` under simulation convention `sim`:
1. Identical symbol identities (`s.identity = e.identity`);
2. Compatible calling-convention signatures
   (`sim.abiCompat s.sig e.sig = true`);
3. Compatible effect guarantees
   (`EffectMask.le s.contract.effects e.contract.effects`);
4. Safety-precondition transfer: every valid caller query satisfying the
   stub's effective safety precondition relates to at least one callee query,
   and every related callee query is valid and satisfies the callee's
   effective safety precondition; and
5. Behavioral transfer: every valid caller query satisfying the stub's
   effective behavioral precondition relates to at least one callee query, and
   every related callee query satisfies the callee's preconditions, and every
   callee return, unwind, or abort permitted by the callee contract relates to
   at least one caller outcome, every one of which satisfies the stub
   contract.

`callerStubIsUnsafe` and `calleeIsUnsafe` select whether each side's
`safetyPre` takes effect (`FnContract.effectiveSafetyPre`). -/
@[reducible] def StubDischargedByVerifiedCallee
    {SigA QA RA MA SigB QB RB MB Frame : Type}
    (sim : SimConv SigA QA RA MA SigB QB RB MB Frame)
    (callerStubIsUnsafe : Bool)
    (calleeIsUnsafe : Bool)
    (callerEntryDom : QA → Prop)
    (callerReturnValid : RA → MA → Prop)
    (callerMemValid : MA → Prop)
    (calleeEntryDom : QB → Prop)
    (calleeReturnValid : RB → MB → Prop)
    (calleeMemValid : MB → Prop)
    (s : AssumedStub SigA QA RA MA)
    (e : VerifiedEntry SigB QB RB MB) : Prop :=
  s.identity = e.identity ∧
  sim.abiCompat s.sig e.sig = true ∧
  EffectMask.le s.contract.effects e.contract.effects ∧
  (∀ qa : QA,
    callerEntryDom qa →
    s.contract.effectiveSafetyPre callerStubIsUnsafe qa →
    (∃ (frame : Frame) (qb : QB), sim.relQuery frame qa qb) ∧
    (∀ (frame : Frame) (qb : QB),
      sim.relQuery frame qa qb →
      calleeEntryDom qb ∧
      e.contract.effectiveSafetyPre calleeIsUnsafe qb)) ∧
  (∀ qa : QA,
    callerEntryDom qa →
    s.contract.effectiveBehaviorPre callerStubIsUnsafe qa →
    (∃ (frame : Frame) (qb : QB), sim.relQuery frame qa qb) ∧
    (∀ (frame : Frame) (qb : QB),
      sim.relQuery frame qa qb →
      calleeEntryDom qb ∧
      e.contract.effectiveBehaviorPre calleeIsUnsafe qb ∧
      (∀ rb mb,
        calleeReturnValid rb mb →
        e.contract.postReturn qb rb mb →
        (∃ ra ma, sim.relReturn frame rb mb ra ma) ∧
        (∀ ra ma,
          sim.relReturn frame rb mb ra ma →
          callerReturnValid ra ma ∧
          s.contract.postReturn qa ra ma)) ∧
      (e.contract.effects.noUnwind = false →
        ∀ mb,
          calleeMemValid mb →
          e.contract.postUnwind qb mb →
          (∃ ma, sim.relUnwind frame mb ma) ∧
          (∀ ma,
            sim.relUnwind frame mb ma →
            callerMemValid ma ∧
            s.contract.postUnwind qa ma)) ∧
      (e.contract.effects.noAbort = false →
        ∀ mb,
          calleeMemValid mb →
          e.contract.postAbort qb mb →
          (∃ ma, sim.relAbort frame mb ma) ∧
          (∀ ma,
            sim.relAbort frame mb ma →
            callerMemValid ma ∧
            s.contract.postAbort qa ma))))

/-- Remove `.assumedExternalCallee sym` entries from `gaps` while preserving
all other disclosed gaps unchanged. Marked `noncomputable` so Lean emits no
`._unsafe_rec` helper. -/
noncomputable def eraseDischargedStubGap (sym : String) :
    List DisclosedGap → List DisclosedGap
  | [] => []
  | .assumedExternalCallee id :: rest =>
    if id == sym then eraseDischargedStubGap sym rest
    else .assumedExternalCallee id :: eraseDischargedStubGap sym rest
  | .unbridgedSemantics p :: rest =>
    .unbridgedSemantics p :: eraseDischargedStubGap sym rest
  | .callerRawPtrAliasing p :: rest =>
    .callerRawPtrAliasing p :: eraseDischargedStubGap sym rest
  | .callerMemoryThreadIsolation p :: rest =>
    .callerMemoryThreadIsolation p :: eraseDischargedStubGap sym rest
  | .configuredReferenceScope o :: rest =>
    .configuredReferenceScope o :: eraseDischargedStubGap sym rest
  | .waivedInhabitation i :: rest =>
    .waivedInhabitation i :: eraseDischargedStubGap sym rest
  | .selectedUnitScope :: rest =>
    .selectedUnitScope :: eraseDischargedStubGap sym rest
  | .rawLegacySpec :: rest =>
    .rawLegacySpec :: eraseDischargedStubGap sym rest
  | .unverifiedDownstream s :: rest =>
    .unverifiedDownstream s :: eraseDischargedStubGap sym rest

/-- Combined cross-language linking theorem uniting a caller verification
envelope, a callee verification envelope, and a `StubDischargedByVerifiedCallee`
witness to erase `.assumedExternalCallee stub.identity` from the caller's gap
ledger into `effectiveGaps`. `stubBody` is the caller program's external
declaration body admitted by `BodySatisfiesStub`; every callee gap (including
the callee's own external-callee assumptions) is carried into `effectiveGaps`
unchanged. -/
@[reducible] def CrossLangLinkedTheorem
    {ProgA BodyA SigA QA RA MA_Mem : Type}
    {ProgB BodyB SigB QB RB MB_Mem Frame : Type}
    (MA : ExecutionModel ProgA BodyA SigA QA RA MA_Mem)
    (progA : ProgA)
    (entriesA : List (VerifiedEntry SigA QA RA MA_Mem))
    (stubsA : List (AssumedStub SigA QA RA MA_Mem))
    (refsA : List (RefutationEntry SigA QA))
    (shapesA : List ClaimShape)
    (gapsA : List DisclosedGap)
    (MB : ExecutionModel ProgB BodyB SigB QB RB MB_Mem)
    (progB : ProgB)
    (entriesB : List (VerifiedEntry SigB QB RB MB_Mem))
    (stubsB : List (AssumedStub SigB QB RB MB_Mem))
    (refsB : List (RefutationEntry SigB QB))
    (shapesB : List ClaimShape)
    (gapsB : List DisclosedGap)
    (sim : SimConv SigA QA RA MA_Mem SigB QB RB MB_Mem Frame)
    (stub : AssumedStub SigA QA RA MA_Mem)
    (calleeEntry : VerifiedEntry SigB QB RB MB_Mem)
    (effectiveGaps : List DisclosedGap) : Prop :=
  EnvelopeTheorem
      (mkEnvelope MA progA entriesA stubsA refsA shapesA gapsA) ∧
  EnvelopeTheorem
      (mkEnvelope MB progB entriesB stubsB refsB shapesB gapsB) ∧
  stub ∈ stubsA ∧
  calleeEntry ∈ entriesB ∧
  ¬ (calleeEntry.identity ∈ stubsB.map AssumedStub.identity) ∧
  ¬ (DisclosedGap.assumedExternalCallee calleeEntry.identity ∈ gapsB) ∧
  (∃ (stubDefId : Nat) (stubBody : BodyA)
     (calleeDefId : Nat) (calleeBody : BodyB),
    MA.bodyAt progA stubDefId = some stubBody ∧
    MB.bodyAt progB calleeDefId = some calleeBody ∧
    BodySatisfiesStub MA gapsA stubBody stub ∧
    BodySatisfiesEntry MB progB calleeDefId gapsB calleeBody calleeEntry ∧
    StubDischargedByVerifiedCallee
      sim
      (MA.bodyIsUnsafe stubBody)
      (MB.bodyIsUnsafe calleeBody)
      (MA.entryDom stubBody)
      (MA.returnValid stubBody)
      MA.memValid
      (MB.entryDom calleeBody)
      (MB.returnValid calleeBody)
      MB.memValid
      stub
      calleeEntry) ∧
  effectiveGaps = eraseDischargedStubGap stub.identity gapsA ++ gapsB

end Trusted.Framework

end
