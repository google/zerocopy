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
public import Trusted.Framework
public import Trusted.Framework.Link

public section

namespace Anneal.Framework.Link

open Trusted.Framework

/-!
# Cross-Language Linking Soundness, Refutations, and Canaries
(`Anneal.Framework.Link`)

Untrusted (`0`-TCB) proof theory over `Trusted.Framework.Link` with zero
dependency on `Trusted.MirSemantics` or any target-language semantics module:

1. `eraseDischargedStubGap_not_mem`: erasing `sym` removes every
   `.assumedExternalCallee sym` entry from a gap list.
2. `eraseDischargedStubGap_preserves_other`: erasing `sym` preserves every gap
   other than `.assumedExternalCallee sym`.
3. `link_erases_assumedExternalCallee`: a satisfied `CrossLangLinkedTheorem`
   eliminates `.assumedExternalCallee stub.identity` from `effectiveGaps`.
4. `link_unbridged_simConv_discloses_gap`: an unbridged `SimConv` forces
   `pid = sim.convId` and preserves `.unbridgedSemantics sim.convId` in
   `effectiveGaps`.
5. `link_transfers_postcondition`: a satisfied `CrossLangLinkedTheorem`
   anchors the stub and callee bodies in their programs and, for every
   safety-admissible caller query and every related callee query, transfers
   callee well-formedness, termination, non-unwinding/non-aborting effect
   bounds, caller return/memory validity, and—when `stub.contract.behaviorPre`
   holds—return, unwind, and abort postconditions back to every related caller
   outcome.
6. `stub_realizable_of_verified_callee`: any total verified callee that
   discharges `s` via `StubDischargedByVerifiedCallee` constructively witnesses
   `StubRealizable` for `s`.
7. Negative refutations: `abiCompat = false`, `noUnwind` / `terminates` /
   `noAbort` mismatches, related callee safety or behavioral precondition
   violations, safety-only invalid caller returns (`s.behaviorPre := False`),
   related caller postcondition violations, caller existential refutations
   (`ClaimShape.existsWitness ∈ shapesA` or `refsA ≠ []`), and missing unbridged
   convention gap disclosures each provably block linking.
8. `canary_cross_lang_link_inhabited`: constructive `0`-hypothesis positive
   canary instantiating two execution models, a `SimConv`, an `AssumedStub`, and
   a `VerifiedEntry` to witness `CrossLangLinkedTheorem`.
-/

/-- `String` `BEq` reflexivity helper. -/
theorem string_beq_self (s : String) : (s == s) = true := by
  exact beq_self_eq_true s

/-- Erasing `sym` removes every `.assumedExternalCallee sym` from `gaps`. -/
theorem eraseDischargedStubGap_not_mem (sym : String)
    (gaps : List DisclosedGap) :
    ¬ (DisclosedGap.assumedExternalCallee sym ∈
        eraseDischargedStubGap sym gaps) := by
  induction gaps with
  | nil =>
    intro h
    cases h
  | cons g rest ih =>
    intro hMem
    cases g with
    | assumedExternalCallee id =>
      unfold eraseDischargedStubGap at hMem
      cases hEq : (id == sym) with
      | true =>
        rw [hEq] at hMem
        exact ih hMem
      | false =>
        rw [hEq] at hMem
        cases hMem with
        | head =>
          rw [string_beq_self sym] at hEq
          exact Bool.noConfusion hEq
        | tail _ hTail =>
          exact ih hTail
    | unbridgedSemantics _
    | callerRawPtrAliasing _
    | callerMemoryThreadIsolation _
    | configuredReferenceScope _
    | waivedInhabitation _
    | selectedUnitScope
    | rawLegacySpec
    | unverifiedDownstream _ =>
      unfold eraseDischargedStubGap at hMem
      cases hMem with
      | tail _ hTail => exact ih hTail

/-- Erasing `sym` preserves every gap distinct from
`.assumedExternalCallee sym`. -/
theorem eraseDischargedStubGap_preserves_other (sym : String)
    (gaps : List DisclosedGap) (g : DisclosedGap)
    (hMem : g ∈ gaps) (hNe : g ≠ .assumedExternalCallee sym) :
    g ∈ eraseDischargedStubGap sym gaps := by
  induction gaps with
  | nil => cases hMem
  | cons x rest ih =>
    cases hMem with
    | head =>
      cases g with
      | assumedExternalCallee id =>
        unfold eraseDischargedStubGap
        cases hEq : (id == sym) with
        | true =>
          have hId : id = sym := eq_of_beq hEq
          subst hId
          exact False.elim (hNe rfl)
        | false =>
          exact List.Mem.head _
      | unbridgedSemantics _
      | callerRawPtrAliasing _
      | callerMemoryThreadIsolation _
      | configuredReferenceScope _
      | waivedInhabitation _
      | selectedUnitScope
      | rawLegacySpec
      | unverifiedDownstream _ =>
        unfold eraseDischargedStubGap
        exact List.Mem.head _
    | tail _ hTail =>
      have hRec := ih hTail
      cases x with
      | assumedExternalCallee id =>
        unfold eraseDischargedStubGap
        cases (id == sym) with
        | true => exact hRec
        | false => exact List.Mem.tail _ hRec
      | unbridgedSemantics _
      | callerRawPtrAliasing _
      | callerMemoryThreadIsolation _
      | configuredReferenceScope _
      | waivedInhabitation _
      | selectedUnitScope
      | rawLegacySpec
      | unverifiedDownstream _ =>
        unfold eraseDischargedStubGap
        exact List.Mem.tail _ hRec

theorem not_mem_append {α : Type} {x : α} {l1 l2 : List α}
    (h1 : ¬ (x ∈ l1)) (h2 : ¬ (x ∈ l2)) : ¬ (x ∈ l1 ++ l2) := by
  induction l1 with
  | nil => exact h2
  | cons a rest ih =>
    intro hMem
    cases hMem with
    | head => exact h1 (List.Mem.head _)
    | tail _ hTail =>
      exact ih (fun h => h1 (List.Mem.tail _ h)) hTail

theorem mem_append_right {α : Type} {x : α} (l1 l2 : List α)
    (h : x ∈ l2) : x ∈ l1 ++ l2 := by
  induction l1 with
  | nil => exact h
  | cons a _ ih => exact List.Mem.tail a ih

theorem not_assumedExternalCallee_mem_simDisclosedGaps
    {SigA QA RA MA SigB QB RB MB Frame : Type}
    (sim : SimConv SigA QA RA MA SigB QB RB MB Frame)
    (sym : String) :
    ¬ (DisclosedGap.assumedExternalCallee sym ∈ sim.disclosedGaps) := by
  unfold SimConv.disclosedGaps
  cases sim.grade with
  | unbridged _ =>
    intro hMem
    cases hMem with
    | tail _ hNil => cases hNil
  | forwardSim _ =>
    intro hMem
    cases hMem
  | biFaultEquiv _ =>
    intro hMem
    cases hMem

/-- Any satisfied `CrossLangLinkedTheorem` eliminates
`.assumedExternalCallee stub.identity` from `effectiveGaps`. -/
theorem link_erases_assumedExternalCallee
    {ProgA BodyA SigA QA RA MA_Mem : Type}
    {ProgB BodyB SigB QB RB MB_Mem Frame : Type}
    {MA : ExecutionModel ProgA BodyA SigA QA RA MA_Mem}
    {progA : ProgA}
    {entriesA : List (VerifiedEntry SigA QA RA MA_Mem)}
    {stubsA : List (AssumedStub SigA QA RA MA_Mem)}
    {refsA : List (RefutationEntry SigA QA)}
    {shapesA : List ClaimShape}
    {gapsA : List DisclosedGap}
    {MB : ExecutionModel ProgB BodyB SigB QB RB MB_Mem}
    {progB : ProgB}
    {entriesB : List (VerifiedEntry SigB QB RB MB_Mem)}
    {stubsB : List (AssumedStub SigB QB RB MB_Mem)}
    {refsB : List (RefutationEntry SigB QB)}
    {shapesB : List ClaimShape}
    {gapsB : List DisclosedGap}
    {sim : SimConv SigA QA RA MA_Mem SigB QB RB MB_Mem Frame}
    {stub : AssumedStub SigA QA RA MA_Mem}
    {calleeEntry : VerifiedEntry SigB QB RB MB_Mem}
    {effectiveGaps : List DisclosedGap}
    (hLink : CrossLangLinkedTheorem
      MA progA entriesA stubsA refsA shapesA gapsA
      MB progB entriesB stubsB refsB shapesB gapsB
      sim stub calleeEntry effectiveGaps) :
    ¬ (DisclosedGap.assumedExternalCallee stub.identity ∈ effectiveGaps) := by
  have ⟨_, _, _, _, _, _, _, _, _, _, _, hNoGapB, hWit, hEqGaps⟩ := hLink
  have ⟨_, _, _, _, _, _, _, _, _, hDisch⟩ := hWit
  have hIdEq : stub.identity = calleeEntry.identity := hDisch.1
  rw [hEqGaps]
  apply not_mem_append
  · apply not_mem_append
    · exact eraseDischargedStubGap_not_mem stub.identity gapsA
    · rw [hIdEq]
      exact hNoGapB
  · exact not_assumedExternalCallee_mem_simDisclosedGaps sim stub.identity

/-- Linking under an unbridged `SimConv` (`sim.grade = .unbridged pid`) forces
`pid = sim.convId` and preserves `.unbridgedSemantics sim.convId` in
`effectiveGaps`. -/
theorem link_unbridged_simConv_discloses_gap
    {ProgA BodyA SigA QA RA MA_Mem : Type}
    {ProgB BodyB SigB QB RB MB_Mem Frame : Type}
    {MA : ExecutionModel ProgA BodyA SigA QA RA MA_Mem}
    {progA : ProgA}
    {entriesA : List (VerifiedEntry SigA QA RA MA_Mem)}
    {stubsA : List (AssumedStub SigA QA RA MA_Mem)}
    {refsA : List (RefutationEntry SigA QA)}
    {shapesA : List ClaimShape}
    {gapsA : List DisclosedGap}
    {MB : ExecutionModel ProgB BodyB SigB QB RB MB_Mem}
    {progB : ProgB}
    {entriesB : List (VerifiedEntry SigB QB RB MB_Mem)}
    {stubsB : List (AssumedStub SigB QB RB MB_Mem)}
    {refsB : List (RefutationEntry SigB QB)}
    {shapesB : List ClaimShape}
    {gapsB : List DisclosedGap}
    {sim : SimConv SigA QA RA MA_Mem SigB QB RB MB_Mem Frame}
    {stub : AssumedStub SigA QA RA MA_Mem}
    {calleeEntry : VerifiedEntry SigB QB RB MB_Mem}
    {effectiveGaps : List DisclosedGap}
    {pid : String}
    (hGrade : sim.grade = .unbridged pid)
    (hLink : CrossLangLinkedTheorem
      MA progA entriesA stubsA refsA shapesA gapsA
      MB progB entriesB stubsB refsB shapesB gapsB
      sim stub calleeEntry effectiveGaps) :
    pid = sim.convId ∧
      DisclosedGap.unbridgedSemantics sim.convId ∈ effectiveGaps := by
  have ⟨_, _, _, _, _, hGradeDisc, _, _, _, _, _, _, _, hEqGaps⟩ := hLink
  unfold EnvelopeGradeDisclosed at hGradeDisc
  rw [hGrade] at hGradeDisc
  refine ⟨hGradeDisc.1, ?_⟩
  rw [hEqGaps, ← hGradeDisc.1]
  exact mem_append_right _ _ hGradeDisc.2

/-- A satisfied `CrossLangLinkedTheorem` anchors the caller's stub body
(`stubBody`, admitted by `BodySatisfiesStub` in `progA` with constructive
non-vacuity or explicit `.waivedInhabitation`) and the verified callee body
(`calleeBody` in `progB`). For every valid caller query satisfying the stub's
effective safety precondition, some callee query is related via `sim`, and every
related callee execution is valid, well-formed, honors the stub's termination,
`noUnwind`, and `noAbort` guarantees, and maps every permitted callee outcome to
at least one caller outcome, every one of which satisfies caller return/memory
validity and—whenever `stub.contract.behaviorPre` holds—the stub contract. -/
theorem link_transfers_postcondition
    {ProgA BodyA SigA QA RA MA_Mem : Type}
    {ProgB BodyB SigB QB RB MB_Mem Frame : Type}
    {MA : ExecutionModel ProgA BodyA SigA QA RA MA_Mem}
    {progA : ProgA}
    {entriesA : List (VerifiedEntry SigA QA RA MA_Mem)}
    {stubsA : List (AssumedStub SigA QA RA MA_Mem)}
    {refsA : List (RefutationEntry SigA QA)}
    {shapesA : List ClaimShape}
    {gapsA : List DisclosedGap}
    {MB : ExecutionModel ProgB BodyB SigB QB RB MB_Mem}
    {progB : ProgB}
    {entriesB : List (VerifiedEntry SigB QB RB MB_Mem)}
    {stubsB : List (AssumedStub SigB QB RB MB_Mem)}
    {refsB : List (RefutationEntry SigB QB)}
    {shapesB : List ClaimShape}
    {gapsB : List DisclosedGap}
    {sim : SimConv SigA QA RA MA_Mem SigB QB RB MB_Mem Frame}
    {stub : AssumedStub SigA QA RA MA_Mem}
    {calleeEntry : VerifiedEntry SigB QB RB MB_Mem}
    {effectiveGaps : List DisclosedGap}
    (hLink : CrossLangLinkedTheorem
      MA progA entriesA stubsA refsA shapesA gapsA
      MB progB entriesB stubsB refsB shapesB gapsB
      sim stub calleeEntry effectiveGaps) :
    ∃ (stubDefId : Nat) (stubBody : BodyA)
      (calleeDefId : Nat) (calleeBody : BodyB),
      MA.bodyAt progA stubDefId = some stubBody ∧
      BodySatisfiesStub MA gapsA stubBody stub ∧
      (NonVacuousEntry MA stubBody
          (stub.contract.effectiveBehaviorPre (MA.bodyIsUnsafe stubBody)) ∨
        DisclosedGap.waivedInhabitation stub.identity ∈ gapsA) ∧
      MB.bodyAt progB calleeDefId = some calleeBody ∧
      MB.bodyIdentity calleeBody = calleeEntry.identity ∧
      (∀ qa : QA,
        MA.entryDom stubBody qa →
        stub.contract.effectiveSafetyPre (MA.bodyIsUnsafe stubBody) qa →
        (∃ (frame : Frame) (qb : QB), sim.relQuery frame qa qb) ∧
        (∀ (frame : Frame) (qb : QB),
          sim.relQuery frame qa qb →
          MB.entryDom calleeBody qb ∧
          MB.wellFormed (MB.execForBody progB calleeDefId) qb ∧
          (stub.contract.effects.terminates = true →
            ¬ MB.diverges (MB.execForBody progB calleeDefId) qb) ∧
          (∀ rb mb,
            MB.produces (MB.execForBody progB calleeDefId) qb
              (.returned rb mb) →
            (∃ ra ma, sim.relReturn frame rb mb ra ma) ∧
            (∀ ra ma,
              sim.relReturn frame rb mb ra ma →
              MA.returnValid stubBody ra ma ∧
              (stub.contract.behaviorPre qa →
                stub.contract.postReturn qa ra ma))) ∧
          (∀ mb,
            MB.produces (MB.execForBody progB calleeDefId) qb (.unwound mb) →
            stub.contract.effects.noUnwind = false ∧
            (∃ ma, sim.relUnwind frame mb ma) ∧
            (∀ ma,
              sim.relUnwind frame mb ma →
              MA.memValid ma ∧
              (stub.contract.behaviorPre qa →
                stub.contract.postUnwind qa ma))) ∧
          (∀ mb,
            MB.produces (MB.execForBody progB calleeDefId) qb (.aborted mb) →
            stub.contract.effects.noAbort = false ∧
            (∃ ma, sim.relAbort frame mb ma) ∧
            (∀ ma,
              sim.relAbort frame mb ma →
              MA.memValid ma ∧
              (stub.contract.behaviorPre qa →
                stub.contract.postAbort qa ma))))) := by
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, hWit, _⟩ := hLink
  have ⟨stubDefId, stubBody, calleeDefId, calleeBody,
        hAtA, hAtB, hStub, hStubNonVac, hSatB, hDisch⟩ := hWit
  have hEff := hDisch.2.2.1
  refine ⟨stubDefId, stubBody, calleeDefId, calleeBody,
          hAtA, hStub, hStubNonVac, hAtB, hSatB.2.1, ?_⟩
  intro qa hDomA hSafeA
  have hStep := hDisch.2.2.2 qa hDomA hSafeA
  refine ⟨hStep.1, ?_⟩
  intro frame qb hRel
  have ⟨hDomB, hBehB, hRetTr, hUnwTr, hAbtTr⟩ := hStep.2 frame qb hRel
  have hWfB := hSatB.2.2.2.2.1 qb hDomB hBehB.1
  have hPostB := hSatB.2.2.2.2.2.1 qb hDomB hBehB
  refine ⟨hDomB, hWfB, ?_, ?_, ?_, ?_⟩
  · intro hTermA
    exact hPostB.1 (hEff.1 hTermA)
  · intro rb mb hProd
    have ⟨hValB, hPostRet⟩ := hPostB.2.1 rb mb hProd
    exact hRetTr rb mb hValB hPostRet
  · intro mb hProd
    have ⟨hMemB, hNoUnwB, hPostUnw⟩ := hPostB.2.2.1 mb hProd
    have hNoUnwA : stub.contract.effects.noUnwind = false := by
      cases hA : stub.contract.effects.noUnwind with
      | false => rfl
      | true =>
        have hBTrue := hEff.2.1 hA
        rw [hNoUnwB] at hBTrue
        exact Bool.noConfusion hBTrue
    exact ⟨hNoUnwA, hUnwTr hNoUnwB mb hMemB hPostUnw⟩
  · intro mb hProd
    have ⟨hMemB, hNoAbtB, hPostAbt⟩ := hPostB.2.2.2 mb hProd
    have hNoAbtA : stub.contract.effects.noAbort = false := by
      cases hA : stub.contract.effects.noAbort with
      | false => rfl
      | true =>
        have hBTrue := hEff.2.2 hA
        rw [hNoAbtB] at hBTrue
        exact Bool.noConfusion hBTrue
    exact ⟨hNoAbtA, hAbtTr hNoAbtB mb hMemB hPostAbt⟩

/-- Constructive stub realizability from a total verified callee discharging
the caller stub `s` via `StubDischargedByVerifiedCallee`. -/
theorem stub_realizable_of_verified_callee
    {ProgA BodyA SigA QA RA MA_Mem : Type}
    {ProgB BodyB SigB QB RB MB_Mem Frame : Type}
    (MA : ExecutionModel ProgA BodyA SigA QA RA MA_Mem)
    (stubBody : BodyA)
    (MB : ExecutionModel ProgB BodyB SigB QB RB MB_Mem)
    (progB : ProgB) (calleeDefId : Nat) (gapsB : List DisclosedGap)
    (calleeBody : BodyB)
    (sim : SimConv SigA QA RA MA_Mem SigB QB RB MB_Mem Frame)
    (s : AssumedStub SigA QA RA MA_Mem)
    (e : VerifiedEntry SigB QB RB MB_Mem)
    (hSatB : BodySatisfiesEntry MB progB calleeDefId gapsB calleeBody e)
    (hDisch : StubDischargedByVerifiedCallee
      sim
      (MA.bodyIsUnsafe stubBody)
      (MB.bodyIsUnsafe calleeBody)
      (MA.entryDom stubBody)
      (MA.returnValid stubBody)
      MA.memValid
      (MB.entryDom calleeBody)
      (MB.returnValid calleeBody)
      MB.memValid
      s e)
    (hTotalB : ∀ qb : QB,
      MB.entryDom calleeBody qb →
      e.contract.effectiveBehaviorPre (MB.bodyIsUnsafe calleeBody) qb →
      MB.wellFormed (MB.execForBody progB calleeDefId) qb →
      ¬ MB.diverges (MB.execForBody progB calleeDefId) qb →
      ∃ out : TerminalOutcome RB MB_Mem,
        MB.produces (MB.execForBody progB calleeDefId) qb out) :
    StubRealizable MA stubBody s.contract := by
  intro qa hDomA hBehA
  cases hTermA : s.contract.effects.terminates with
  | false => exact Or.inl rfl
  | true =>
    have hEff := hDisch.2.2.1
    have hTermB : e.contract.effects.terminates = true := hEff.1 hTermA
    have hStep := hDisch.2.2.2 qa hDomA hBehA.1
    have ⟨frame, qb, hRel⟩ := hStep.1
    have ⟨hDomB, hBehB, hRetTr, hUnwTr, hAbtTr⟩ := hStep.2 frame qb hRel
    have hWfB := hSatB.2.2.2.2.1 qb hDomB hBehB.1
    have hPostB := hSatB.2.2.2.2.2.1 qb hDomB hBehB
    have hNoDivB := hPostB.1 hTermB
    have hOut := hTotalB qb hDomB hBehB hWfB hNoDivB
    cases hOut with
    | intro out hProd =>
      cases out with
      | returned rb mb =>
        have ⟨hValB, hPostRet⟩ := hPostB.2.1 rb mb hProd
        have ⟨hExR, hAllR⟩ := hRetTr rb mb hValB hPostRet
        have ⟨ra, ma, hRelR⟩ := hExR
        have ⟨hValA, hPostImp⟩ := hAllR ra ma hRelR
        exact Or.inr (Or.inl ⟨ra, ma, hValA, hPostImp hBehA.2⟩)
      | unwound mb =>
        have ⟨hMemB, hNoUnwB, hPostUnw⟩ := hPostB.2.2.1 mb hProd
        have hNoUnwA : s.contract.effects.noUnwind = false := by
          cases hA : s.contract.effects.noUnwind with
          | false => rfl
          | true =>
            have hBTrue := hEff.2.1 hA
            rw [hNoUnwB] at hBTrue
            exact Bool.noConfusion hBTrue
        have ⟨hExU, hAllU⟩ := hUnwTr hNoUnwB mb hMemB hPostUnw
        have ⟨ma, hRelU⟩ := hExU
        have ⟨hMemA, hPostImp⟩ := hAllU ma hRelU
        exact Or.inr (Or.inr (Or.inl ⟨hNoUnwA, ma, hMemA, hPostImp hBehA.2⟩))
      | aborted mb =>
        have ⟨hMemB, hNoAbtB, hPostAbt⟩ := hPostB.2.2.2 mb hProd
        have hNoAbtA : s.contract.effects.noAbort = false := by
          cases hA : s.contract.effects.noAbort with
          | false => rfl
          | true =>
            have hBTrue := hEff.2.2 hA
            rw [hNoAbtB] at hBTrue
            exact Bool.noConfusion hBTrue
        have ⟨hExA, hAllA⟩ := hAbtTr hNoAbtB mb hMemB hPostAbt
        have ⟨ma, hRelA⟩ := hExA
        have ⟨hMemA, hPostImp⟩ := hAllA ma hRelA
        exact Or.inr (Or.inr (Or.inr ⟨hNoAbtA, ma, hMemA, hPostImp hBehA.2⟩))

/-- Negative refutation: ABI mismatch (`sim.abiCompat s.sig e.sig = false`)
blocks stub discharge unconditionally. -/
theorem stubDischarge_blocked_of_abiCompat_false
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
    (e : VerifiedEntry SigB QB RB MB)
    (hAbi : sim.abiCompat s.sig e.sig = false) :
    ¬ StubDischargedByVerifiedCallee
        sim callerStubIsUnsafe calleeIsUnsafe callerEntryDom callerReturnValid
        callerMemValid calleeEntryDom calleeReturnValid calleeMemValid s e := by
  intro hDisch
  have hTrue := hDisch.2.1
  rw [hAbi] at hTrue
  exact Bool.noConfusion hTrue

/-- Negative refutation: `noUnwind` mismatch (`s` guarantees `noUnwind = true`
while `e` only guarantees `noUnwind = false`) blocks stub discharge. -/
theorem stubDischarge_blocked_of_noUnwind_mismatch
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
    (e : VerifiedEntry SigB QB RB MB)
    (hCallerNoUnw : s.contract.effects.noUnwind = true)
    (hCalleeUnw : e.contract.effects.noUnwind = false) :
    ¬ StubDischargedByVerifiedCallee
        sim callerStubIsUnsafe calleeIsUnsafe callerEntryDom callerReturnValid
        callerMemValid calleeEntryDom calleeReturnValid calleeMemValid s e := by
  intro hDisch
  have hBTrue := hDisch.2.2.1.2.1 hCallerNoUnw
  rw [hCalleeUnw] at hBTrue
  exact Bool.noConfusion hBTrue

/-- Negative refutation: `terminates` mismatch (`s` guarantees
`terminates = true` while `e` allows divergence) blocks stub discharge. -/
theorem stubDischarge_blocked_of_terminates_mismatch
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
    (e : VerifiedEntry SigB QB RB MB)
    (hCallerTerm : s.contract.effects.terminates = true)
    (hCalleeDiv : e.contract.effects.terminates = false) :
    ¬ StubDischargedByVerifiedCallee
        sim callerStubIsUnsafe calleeIsUnsafe callerEntryDom callerReturnValid
        callerMemValid calleeEntryDom calleeReturnValid calleeMemValid s e := by
  intro hDisch
  have hBTrue := hDisch.2.2.1.1 hCallerTerm
  rw [hCalleeDiv] at hBTrue
  exact Bool.noConfusion hBTrue

/-- Negative refutation: `noAbort` mismatch (`s` guarantees `noAbort = true`
while `e` allows abort) blocks stub discharge. -/
theorem stubDischarge_blocked_of_noAbort_mismatch
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
    (e : VerifiedEntry SigB QB RB MB)
    (hCallerNoAbt : s.contract.effects.noAbort = true)
    (hCalleeAbt : e.contract.effects.noAbort = false) :
    ¬ StubDischargedByVerifiedCallee
        sim callerStubIsUnsafe calleeIsUnsafe callerEntryDom callerReturnValid
        callerMemValid calleeEntryDom calleeReturnValid calleeMemValid s e := by
  intro hDisch
  have hBTrue := hDisch.2.2.1.2.2 hCallerNoAbt
  rw [hCalleeAbt] at hBTrue
  exact Bool.noConfusion hBTrue

/-- Negative refutation: if a valid caller query satisfying the stub's
effective safety precondition relates via `sim` to any callee query violating
the callee's effective safety precondition, discharge is blocked, even when
other related callee queries would satisfy it. -/
theorem stubDischarge_blocked_of_related_unsafe_query
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
    (e : VerifiedEntry SigB QB RB MB)
    (qa : QA) (frame : Frame) (qb : QB)
    (hDom : callerEntryDom qa)
    (hSafe : s.contract.effectiveSafetyPre callerStubIsUnsafe qa)
    (hRel : sim.relQuery frame qa qb)
    (hBad : ¬ e.contract.effectiveSafetyPre calleeIsUnsafe qb) :
    ¬ StubDischargedByVerifiedCallee
        sim callerStubIsUnsafe calleeIsUnsafe callerEntryDom callerReturnValid
        callerMemValid calleeEntryDom calleeReturnValid calleeMemValid s e := by
  intro hDisch
  exact hBad (((hDisch.2.2.2 qa hDom hSafe).2 frame qb hRel).2.1).1

/-- Negative refutation: if a safety-admissible caller query relates via `sim`
to any callee query violating `e.contract.behaviorPre` (which would leave
callee unwinding, aborting, and return validity unconstrained by
`BodySatisfiesEntry`), discharge is blocked. -/
theorem stubDischarge_blocked_of_related_callee_behaviorPre_false
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
    (e : VerifiedEntry SigB QB RB MB)
    (qa : QA) (frame : Frame) (qb : QB)
    (hDom : callerEntryDom qa)
    (hSafe : s.contract.effectiveSafetyPre callerStubIsUnsafe qa)
    (hRel : sim.relQuery frame qa qb)
    (hBad : ¬ e.contract.behaviorPre qb) :
    ¬ StubDischargedByVerifiedCallee
        sim callerStubIsUnsafe calleeIsUnsafe callerEntryDom callerReturnValid
        callerMemValid calleeEntryDom calleeReturnValid calleeMemValid s e := by
  intro hDisch
  exact hBad (((hDisch.2.2.2 qa hDom hSafe).2 frame qb hRel).2.1).2

/-- Negative refutation: even on a safety-only call where
`s.contract.behaviorPre` is `False` (or does not hold on `qa`), if a callee
return permitted by `e` relates via `sim` to an invalid caller return
(`¬ callerReturnValid ra ma`), discharge is blocked. -/
theorem stubDischarge_blocked_of_safetyOnly_invalid_return
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
    (e : VerifiedEntry SigB QB RB MB)
    (qa : QA) (frame : Frame) (qb : QB) (rb : RB) (mb : MB) (ra : RA) (ma : MA)
    (hDom : callerEntryDom qa)
    (hSafe : s.contract.effectiveSafetyPre callerStubIsUnsafe qa)
    (hRel : sim.relQuery frame qa qb)
    (hValB : calleeReturnValid rb mb)
    (hPostB : e.contract.postReturn qb rb mb)
    (hRelR : sim.relReturn frame rb mb ra ma)
    (hBadValA : ¬ callerReturnValid ra ma) :
    ¬ StubDischargedByVerifiedCallee
        sim callerStubIsUnsafe calleeIsUnsafe callerEntryDom callerReturnValid
        callerMemValid calleeEntryDom calleeReturnValid calleeMemValid s e := by
  intro hDisch
  exact hBadValA
    ((((hDisch.2.2.2 qa hDom hSafe).2 frame qb hRel).2.2.1
      rb mb hValB hPostB).2 ra ma hRelR).1

/-- Negative refutation: if a callee return permitted by the callee contract
relates via `sim` to any caller outcome violating the stub's `postReturn` on a
query satisfying `s.contract.effectiveBehaviorPre`, discharge is blocked, even
when other related caller outcomes would satisfy it. -/
theorem stubDischarge_blocked_of_related_return_violation
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
    (e : VerifiedEntry SigB QB RB MB)
    (qa : QA) (frame : Frame) (qb : QB) (rb : RB) (mb : MB) (ra : RA) (ma : MA)
    (hDom : callerEntryDom qa)
    (hBeh : s.contract.effectiveBehaviorPre callerStubIsUnsafe qa)
    (hRel : sim.relQuery frame qa qb)
    (hValB : calleeReturnValid rb mb)
    (hPostB : e.contract.postReturn qb rb mb)
    (hRelR : sim.relReturn frame rb mb ra ma)
    (hBad : ¬ s.contract.postReturn qa ra ma) :
    ¬ StubDischargedByVerifiedCallee
        sim callerStubIsUnsafe calleeIsUnsafe callerEntryDom callerReturnValid
        callerMemValid calleeEntryDom calleeReturnValid calleeMemValid s e := by
  intro hDisch
  exact hBad
    (((((hDisch.2.2.2 qa hDom hBeh.1).2 frame qb hRel).2.2.1
      rb mb hValB hPostB).2 ra ma hRelR).2 hBeh.2)

/-- Negative refutation: one-way cross-language stub discharge rejects caller
envelopes claiming `ClaimShape.existsWitness`. -/
theorem link_blocked_of_existsWitness
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
    (effectiveGaps : List DisclosedGap)
    (hExists : ClaimShape.existsWitness ∈ shapesA) :
    ¬ CrossLangLinkedTheorem
        MA progA entriesA stubsA refsA shapesA gapsA
        MB progB entriesB stubsB refsB shapesB gapsB
        sim stub calleeEntry effectiveGaps := by
  intro hLink
  exact hLink.2.2.2.1 hExists

/-- Negative refutation: one-way cross-language stub discharge rejects caller
envelopes with non-empty `refsA`. -/
theorem link_blocked_of_nonempty_refsA
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
    (effectiveGaps : List DisclosedGap)
    (hNonEmpty : refsA ≠ []) :
    ¬ CrossLangLinkedTheorem
        MA progA entriesA stubsA refsA shapesA gapsA
        MB progB entriesB stubsB refsB shapesB gapsB
        sim stub calleeEntry effectiveGaps := by
  intro hLink
  exact hNonEmpty hLink.2.2.1

/-- Negative refutation: omitting `.unbridgedSemantics sim.convId` from
`effectiveGaps` when `sim.grade = .unbridged pid` blocks linking. -/
theorem link_blocked_of_missing_unbridged_simConv_gap
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
    (effectiveGaps : List DisclosedGap)
    (pid : String)
    (hGrade : sim.grade = .unbridged pid)
    (hMissing :
      ¬ (DisclosedGap.unbridgedSemantics sim.convId ∈ effectiveGaps)) :
    ¬ CrossLangLinkedTheorem
        MA progA entriesA stubsA refsA shapesA gapsA
        MB progB entriesB stubsB refsB shapesB gapsB
        sim stub calleeEntry effectiveGaps := by
  intro hLink
  exact hMissing (link_unbridged_simConv_discloses_gap hGrade hLink).2

theorem nat_ne_of_beq_false {m n : Nat} (h : Nat.beq m n = false) :
    m ≠ n := by
  intro hEq
  subst hEq
  have hRefl : ∀ k : Nat, Nat.beq k k = true := by
    intro k
    induction k with
    | zero => rfl
    | succ _ ih => exact ih
  rw [hRefl m] at h
  exact Bool.noConfusion h

theorem ne_string_of_len_beq_false {a b : String}
    (h : Nat.beq a.toByteArray.data.toList.length
           b.toByteArray.data.toList.length = false) :
    a ≠ b := by
  intro hEq
  exact nat_ne_of_beq_false h
    (congrArg (fun s => s.toByteArray.data.toList.length) hEq)

/-- Concrete caller `ExecutionModel` for `canary_cross_lang_link_inhabited`,
containing a local verified body (`false` -> `"caller_fn"`) and an external
callee stub (`true` -> `"ext_callee"`). -/
def canaryCallerModel : ExecutionModel Unit Bool Unit Unit Unit Unit :=
  { profileId        := "toy_caller_v1"
    oracleGrade      := .biFaultEquiv "toy_caller_ref"
    programAdmitted  := fun _ => true
    bodyAdmitted     := fun _ _ => true
    isPartialScope   := fun _ => false
    bodyAt           := fun _ n =>
      match n with
      | 0 => some false
      | 1 => some true
      | _ => none
    uniqueIdentities := fun _ => true
    bodyIdentity     := fun b =>
      match b with
      | false => "caller_fn"
      | true  => "ext_callee"
    bodyIsUnsafe     := fun _ => false
    bodyIsExternal   := fun b => b
    bodyMatchesSig   := fun _ _ => true
    modelGaps        := []
    requiredGaps     := fun _ => []
    claimShapeGaps   := fun _ => []
    entryDom         := fun _ _ => True
    returnValid      := fun _ _ _ => True
    memValid         := fun _ => True
    execForBody      := fun p _ => p
    wellFormed       := fun _ _ => True
    produces         := fun _ _ out => out = .returned () ()
    diverges         := fun _ _ => False
    faultsUB         := fun _ _ => False }

/-- Concrete callee `ExecutionModel` for `canary_cross_lang_link_inhabited`,
implementing `"ext_callee"` as a verified local entry under an unbridged
target-language profile. -/
def canaryCalleeModel : ExecutionModel Unit Unit Unit Unit Unit Unit :=
  { profileId        := "toy_callee_v1"
    oracleGrade      := .unbridged "toy_callee_v1"
    programAdmitted  := fun _ => true
    bodyAdmitted     := fun _ _ => true
    isPartialScope   := fun _ => false
    bodyAt           := fun _ n =>
      match n with
      | 0 => some ()
      | _ => none
    uniqueIdentities := fun _ => true
    bodyIdentity     := fun _ => "ext_callee"
    bodyIsUnsafe     := fun _ => false
    bodyIsExternal   := fun _ => false
    bodyMatchesSig   := fun _ _ => true
    modelGaps        := []
    requiredGaps     := fun _ => []
    claimShapeGaps   := fun _ => []
    entryDom         := fun _ _ => True
    returnValid      := fun _ _ _ => True
    memValid         := fun _ => True
    execForBody      := fun p _ => p
    wellFormed       := fun _ _ => True
    produces         := fun _ _ out => out = .returned () ()
    diverges         := fun _ _ => False
    faultsUB         := fun _ _ => False }

/-- Concrete unbridged ABI `SimConv` for `canary_cross_lang_link_inhabited`. -/
def canarySimConv : SimConv Unit Unit Unit Unit Unit Unit Unit Unit Unit :=
  { convId    := "toy_c_abi_v1"
    grade     := .unbridged "toy_c_abi_v1"
    abiCompat := fun _ _ => true
    relQuery  := fun _ _ _ => True
    relReturn := fun _ _ _ _ _ => True
    relUnwind := fun _ _ _ => True
    relAbort  := fun _ _ _ => True }

/-- Concrete caller `VerifiedEntry` for `canary_cross_lang_link_inhabited`. -/
def canaryCallerEntry : VerifiedEntry Unit Unit Unit Unit :=
  { identity := "caller_fn"
    sig      := ()
    contract := {
      effects := { terminates := true, noUnwind := true, noAbort := true } } }

/-- Concrete caller `AssumedStub` for `canary_cross_lang_link_inhabited`. -/
def canaryStub : AssumedStub Unit Unit Unit Unit :=
  { identity := "ext_callee"
    sig      := ()
    contract := {
      effects := { terminates := true, noUnwind := true, noAbort := true } } }

/-- Concrete callee `VerifiedEntry` for `canary_cross_lang_link_inhabited`. -/
def canaryCalleeEntry : VerifiedEntry Unit Unit Unit Unit :=
  { identity := "ext_callee"
    sig      := ()
    contract := {
      effects := { terminates := true, noUnwind := true, noAbort := true } } }

/-- Constructive `0`-hypothesis positive canary proving
`CrossLangLinkedTheorem` is jointly satisfiable across two concrete execution
models, erasing `.assumedExternalCallee "ext_callee"` while preserving both the
callee model's `.unbridgedSemantics` gap and `canarySimConv.disclosedGaps`. -/
theorem canary_cross_lang_link_inhabited :
    CrossLangLinkedTheorem
      canaryCallerModel ()
      [canaryCallerEntry] [canaryStub] []
      [.forallSafety, .termination]
      [.assumedExternalCallee "ext_callee"]
      canaryCalleeModel ()
      [canaryCalleeEntry] [] []
      [.forallSafety, .termination]
      [.unbridgedSemantics "toy_callee_v1"]
      canarySimConv canaryStub canaryCalleeEntry
      [.unbridgedSemantics "toy_callee_v1",
       .unbridgedSemantics "toy_c_abi_v1"] := by
  refine ⟨?_, ?_, rfl, ?_, ne_string_of_len_beq_false rfl,
          ⟨rfl, List.Mem.head _⟩, ?_, ?_, List.Mem.head _, List.Mem.head _,
          (fun h => by cases h), ?_, ?_, ?_⟩
  · refine ⟨⟨ne_string_of_len_beq_false rfl, rfl, (fun _ _ _ => rfl), rfl,
             (fun h => Bool.noConfusion h), ne_string_of_len_beq_false rfl,
             ?_, (fun _ h => by cases h)⟩,
            ?_, ?_, ?_, ?_, (fun _ h => by cases h), ?_⟩
    · intro cs hMem
      cases hMem with
      | head => exact ⟨rfl, fun _ h => by cases h⟩
      | tail _ h2 =>
        cases h2 with
        | head => exact ⟨rfl, fun _ h => by cases h⟩
        | tail _ hNil => cases hNil
    · intro _ _
      exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
    · refine ⟨ne_string_of_len_beq_false rfl, ?_,
              ne_string_of_len_beq_false rfl, (fun _ h => by cases h),
              True.intro⟩
      intro t hMem
      cases hMem with
      | head => exact ne_string_of_len_beq_false rfl
      | tail _ hNil => cases hNil
    · intro e hMem
      cases hMem with
      | head =>
        refine ⟨0, false, rfl, rfl, rfl, rfl, (fun _ h => by cases h),
                (fun _ _ _ => True.intro), ?_, ?_⟩
        · intro _ _ _
          refine ⟨(fun _ hDiv => hDiv),
                  (fun _ _ _ => ⟨True.intro, True.intro⟩),
                  (fun _ h => by cases h),
                  (fun _ h => by cases h)⟩
        · exact Or.inl ⟨rfl, Or.inl ⟨(), True.intro,
            ⟨(fun h => Bool.noConfusion h), True.intro⟩⟩⟩
      | tail _ hNil => cases hNil
    · intro s hMem
      cases hMem with
      | head =>
        refine ⟨1, true, rfl, rfl, rfl, rfl, (fun _ h => by cases h),
                List.Mem.head _, ?_⟩
        intro _ _ _
        exact Or.inr (Or.inl ⟨(), (), True.intro, True.intro⟩)
      | tail _ hNil => cases hNil
    · intro defId _ hGet
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
        | succ _ => cases hGet
  · refine ⟨⟨ne_string_of_len_beq_false rfl, rfl, (fun _ _ _ => rfl), rfl,
             (fun h => Bool.noConfusion h), ⟨rfl, List.Mem.head _⟩,
             ?_, (fun _ h => by cases h)⟩,
            ?_, ⟨ne_string_of_len_beq_false rfl, (fun _ h => by cases h),
                 True.intro⟩,
            ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩
    · intro cs hMem
      cases hMem with
      | head => exact ⟨rfl, fun _ h => by cases h⟩
      | tail _ h2 =>
        cases h2 with
        | head => exact ⟨rfl, fun _ h => by cases h⟩
        | tail _ hNil => cases hNil
    · intro _ _
      exact ⟨List.Mem.head _, fun _ => List.Mem.tail _ (List.Mem.head _)⟩
    · intro e hMem
      cases hMem with
      | head =>
        refine ⟨0, (), rfl, rfl, rfl, rfl, (fun _ h => by cases h),
                (fun _ _ _ => True.intro), ?_, ?_⟩
        · intro _ _ _
          refine ⟨(fun _ hDiv => hDiv),
                  (fun _ _ _ => ⟨True.intro, True.intro⟩),
                  (fun _ h => by cases h),
                  (fun _ h => by cases h)⟩
        · exact Or.inl ⟨rfl, Or.inl ⟨(), True.intro,
            ⟨(fun h => Bool.noConfusion h), True.intro⟩⟩⟩
      | tail _ hNil => cases hNil
    · intro defId _ hGet
      cases defId with
      | zero => exact List.Mem.head _
      | succ _ => cases hGet
  · intro hMem
    cases hMem with
    | tail _ h2 =>
      cases h2 with
      | tail _ hNil => cases hNil
  · intro cs hMem
    cases hMem with
    | head => rfl
    | tail _ h2 =>
      cases h2 with
      | head => rfl
      | tail _ hNil => cases hNil
  · intro hSub
    cases hSub with
    | tail _ h2 =>
      cases h2 with
      | tail _ hNil => cases hNil
  · intro hGapB
    cases hGapB with
    | tail _ hNil => cases hNil
  · refine ⟨1, true, 0, (), rfl, rfl,
            ⟨rfl, rfl, rfl, (fun _ h => by cases h), List.Mem.head _,
             (fun _ _ _ => Or.inr (Or.inl ⟨(), (), True.intro, True.intro⟩))⟩,
            Or.inl (Or.inl ⟨(), True.intro,
              ⟨(fun h => Bool.noConfusion h), True.intro⟩⟩),
            ⟨rfl, rfl, rfl, (fun _ h => by cases h), (fun _ _ _ => True.intro),
             (fun _ _ _ => ⟨(fun _ hDiv => hDiv),
                            (fun _ _ _ => ⟨True.intro, True.intro⟩),
                            (fun _ h => by cases h),
                            (fun _ h => by cases h)⟩),
             Or.inl ⟨rfl, Or.inl ⟨(), True.intro,
               ⟨(fun h => Bool.noConfusion h), True.intro⟩⟩⟩⟩,
            ⟨rfl, rfl, ⟨(fun h => h), (fun h => h), (fun h => h)⟩, ?_⟩⟩
    intro _ _ _
    refine ⟨⟨(), (), True.intro⟩, ?_⟩
    intro _ _ _
    refine ⟨True.intro, ⟨(fun h => Bool.noConfusion h), True.intro⟩,
            (fun _ _ _ _ =>
              ⟨⟨(), (), True.intro⟩,
               (fun _ _ _ => ⟨True.intro, (fun _ => True.intro)⟩)⟩),
            (fun hNoUnw => Bool.noConfusion hNoUnw),
            (fun hNoAbt => Bool.noConfusion hNoAbt)⟩
  · unfold canaryStub eraseDischargedStubGap
    dsimp only
    rw [string_beq_self "ext_callee"]
    rfl

end Anneal.Framework.Link

end
