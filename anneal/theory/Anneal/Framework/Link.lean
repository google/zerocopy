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
# Cross-Language Linking Soundness and Negative Refutations
(`Anneal.Framework.Link`)

Untrusted (`0`-TCB) proof theory over `Trusted.Framework.Link` with zero
dependency on `Trusted.MirSemantics` or `Trusted.CppSemantics`:

1. `eraseDischargedStubGap_not_mem`: erasing `sym` removes every
   `.assumedExternalCallee sym` entry from a gap list.
2. `eraseDischargedStubGap_preserves_other`: erasing `sym` preserves every gap
   other than `.assumedExternalCallee sym`.
3. `link_erases_assumedExternalCallee`: a satisfied `CrossLangLinkedTheorem`
   eliminates `.assumedExternalCallee stub.identity` from `effectiveGaps`.
4. `link_transfers_postcondition`: a satisfied `CrossLangLinkedTheorem`
   anchors the stub and callee bodies in their programs and, for every valid
   caller query and every related callee query, transfers callee
   well-formedness, termination, and return/unwind/abort postconditions back
   to every related caller outcome.
5. `stub_realizable_of_verified_callee`: any total verified callee that
   discharges `s` via `StubDischargedByVerifiedCallee` constructively witnesses
   `StubRealizable` for `s`.
6. Negative refutations: `abiCompat = false`, `noUnwind` / `terminates` /
   `noAbort` mismatches, a related callee query violating the callee's safety
   precondition, and a related caller outcome violating the stub's
   postcondition each provably block `StubDischargedByVerifiedCallee`.
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
  have hNoGapB := hLink.2.2.2.2.2.1
  have hWit := hLink.2.2.2.2.2.2.1
  have hEqGaps := hLink.2.2.2.2.2.2.2
  cases hWit with
  | intro _ h1 =>
    cases h1 with
    | intro _ h2 =>
      cases h2 with
      | intro _ h3 =>
        cases h3 with
        | intro _ h4 =>
          have hIdEq : stub.identity = calleeEntry.identity :=
            h4.2.2.2.2.1
          rw [hEqGaps]
          apply not_mem_append
          · exact eraseDischargedStubGap_not_mem stub.identity gapsA
          · rw [hIdEq]
            exact hNoGapB

/-- A satisfied `CrossLangLinkedTheorem` anchors the caller's stub body
(`stubBody`, admitted by `BodySatisfiesStub` in `progA`) and the verified callee
body (`calleeBody` in `progB`). For every valid caller query satisfying the
stub's effective safety precondition, some callee query is related via `sim`,
and every related callee query is valid and well-formed. For every valid caller
query satisfying the stub's effective behavioral precondition, some callee
query is related via `sim`, and every related callee execution is well-formed,
honors the stub's termination guarantee, and every callee return, unwind, or
abort relates to at least one caller outcome, every one of which satisfies the
stub contract. -/
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
      MB.bodyAt progB calleeDefId = some calleeBody ∧
      MB.bodyIdentity calleeBody = calleeEntry.identity ∧
      (∀ qa : QA,
        MA.entryDom stubBody qa →
        stub.contract.effectiveSafetyPre (MA.bodyIsUnsafe stubBody) qa →
        (∃ (frame : Frame) (qb : QB), sim.relQuery frame qa qb) ∧
        (∀ (frame : Frame) (qb : QB),
          sim.relQuery frame qa qb →
          MB.entryDom calleeBody qb ∧
          MB.wellFormed (MB.execForBody progB calleeDefId) qb)) ∧
      (∀ qa : QA,
        MA.entryDom stubBody qa →
        stub.contract.effectiveBehaviorPre (MA.bodyIsUnsafe stubBody) qa →
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
              stub.contract.postReturn qa ra ma)) ∧
          (∀ mb,
            MB.produces (MB.execForBody progB calleeDefId) qb (.unwound mb) →
            stub.contract.effects.noUnwind = false ∧
            (∃ ma, sim.relUnwind frame mb ma) ∧
            (∀ ma,
              sim.relUnwind frame mb ma →
              MA.memValid ma ∧
              stub.contract.postUnwind qa ma)) ∧
          (∀ mb,
            MB.produces (MB.execForBody progB calleeDefId) qb (.aborted mb) →
            stub.contract.effects.noAbort = false ∧
            (∃ ma, sim.relAbort frame mb ma) ∧
            (∀ ma,
              sim.relAbort frame mb ma →
              MA.memValid ma ∧
              stub.contract.postAbort qa ma)))) := by
  have hWit := hLink.2.2.2.2.2.2.1
  cases hWit with
  | intro stubDefId h1 =>
    cases h1 with
    | intro stubBody h2 =>
      cases h2 with
      | intro calleeDefId h3 =>
        cases h3 with
        | intro calleeBody h4 =>
          have hAtA := h4.1
          have hAtB := h4.2.1
          have hStub := h4.2.2.1
          have hSatB := h4.2.2.2.1
          have hDisch := h4.2.2.2.2
          have hEff := hDisch.2.2.1
          refine ⟨stubDefId, stubBody, calleeDefId, calleeBody,
                  hAtA, hStub, hAtB, hSatB.2.1, ?_, ?_⟩
          · intro qa hDomA hSafeA
            have hStep := hDisch.2.2.2.1 qa hDomA hSafeA
            refine ⟨hStep.1, ?_⟩
            intro frame qb hRel
            have ⟨hDomB, hSafeB⟩ := hStep.2 frame qb hRel
            exact ⟨hDomB, hSatB.2.2.2.2.1 qb hDomB hSafeB⟩
          · intro qa hDomA hBehA
            have hStep := hDisch.2.2.2.2 qa hDomA hBehA
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
    have hStep := hDisch.2.2.2.2 qa hDomA hBehA
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
        have ⟨hValA, hPostA⟩ := hAllR ra ma hRelR
        exact Or.inr (Or.inl ⟨ra, ma, hValA, hPostA⟩)
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
        have ⟨hMemA, hPostA⟩ := hAllU ma hRelU
        exact Or.inr (Or.inr (Or.inl ⟨hNoUnwA, ma, hMemA, hPostA⟩))
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
        have ⟨hMemA, hPostA⟩ := hAllA ma hRelA
        exact Or.inr (Or.inr (Or.inr ⟨hNoAbtA, ma, hMemA, hPostA⟩))

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
  exact hBad ((hDisch.2.2.2.1 qa hDom hSafe).2 frame qb hRel).2

/-- Negative refutation: if a callee return permitted by the callee contract
relates via `sim` to any caller outcome violating the stub's `postReturn`,
discharge is blocked, even when other related caller outcomes would satisfy
it. -/
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
    ((((hDisch.2.2.2.2 qa hDom hBeh).2 frame qb hRel).2.2.1
      rb mb hValB hPostB).2 ra ma hRelR).2

end Anneal.Framework.Link

end
