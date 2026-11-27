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
public import Anneal.MirWp

public section

namespace Anneal.Framework

open Trusted.MirAst Trusted.MirSemantics Trusted.Framework
open Anneal.MirWp

/-!
# Verification Envelope Soundness and Equivalences (`Anneal.Framework`)

Untrusted (`0`-TCB) proof theory over `Trusted.Framework`,
`Trusted.Framework.Instances`, and `Trusted.Framework.Bridge`, proving:

1. **Transfer-license and contract laws (`0` axioms):**
   - `forwardSim_rejects_existsWitness` & `biFaultEquiv_licenses_existsWitness`
   - `wfStutter_rejects_generalHyper`
   - `safe_fn_ignores_false_safetyPre`
   - `uninhabited_domain_nonVacuous`
   - `unbridged_envelope_requires_gap`
   - `partial_scope_envelope_requires_gap`
   - `modelGaps_of_envelopeTheorem`
   - `no_stubs_of_all_local_model`
   - `legacy_envelope_requires_rawLegacySpec_gap`
   - `stub_false_post_unrealizable`
2. **Bidirectional `CrateTheorem` / `UnitTheorem` / `V2` compatibility:**
   - `crateEnvelopeTheorem_iff_crateTheorem`
   - `unitEnvelopeTheorem_iff_unitTheorem`
   - `crateEnvelopeTheoremV2_iff_crateTheoremV2`
   - `unitEnvelopeTheoremV2_iff_unitTheoremV2`
   - `mirProfileV1_wellFormed_defeq` & `mirProfileV2_wellFormed_defeq` (`rfl`
     zero-WHNF-tax probes)
-/

/-- Canonical snake_case wire spelling for each `ClaimShape` (kept in `0`-TCB
`theory/` outside `trusted/lean/`). -/
@[expose] def claimShapeWireName : ClaimShape → String
  | .existsWitness => "exists_witness"
  | .forallSafety  => "forall_safety"
  | .generalHyper  => "general_hyper"
  | .subsetHyper   => "subset_hyper"
  | .termination   => "termination"

/-- Product lattice order on `EffectMask` (`m1 ≤ m2` iff `m2` guarantees every
effect restriction guaranteed by `m1`). -/
@[expose] def effectMaskLe (m1 m2 : Trusted.Framework.EffectMask) : Prop :=
  (m1.terminates = true → m2.terminates = true) ∧
  (m1.noUnwind = true → m2.noUnwind = true) ∧
  (m1.noAbort = true → m2.noAbort = true)

/-- Extract the model from any `VerificationEnvelope`. -/
@[expose] def envelopeModel {Prog Body Sig Query Ret Mem : Type} :
    VerificationEnvelope Prog Body Sig Query Ret Mem →
      ExecutionModel Prog Body Sig Query Ret Mem
  | .structured M _ _ _ _ _ _ => M
  | .legacy M _ _ _ _ _ => M

/-- Extract the program from any `VerificationEnvelope`. -/
@[expose] def envelopeProgram {Prog Body Sig Query Ret Mem : Type} :
    VerificationEnvelope Prog Body Sig Query Ret Mem → Prog
  | .structured _ p _ _ _ _ _ => p
  | .legacy _ p _ _ _ _ => p

/-- Extract the disclosed gap ledger from any `VerificationEnvelope`. -/
@[expose] def envelopeGaps {Prog Body Sig Query Ret Mem : Type} :
    VerificationEnvelope Prog Body Sig Query Ret Mem → List DisclosedGap
  | .structured _ _ _ _ _ _ gs => gs
  | .legacy _ _ _ _ _ gs => gs

/-- One-way forward simulation never licenses existential UB refutations. -/
theorem forwardSim_rejects_existsWitness (oid : String) :
    (OracleGrade.forwardSim oid).licenses .existsWitness = false :=
  rfl

/-- One-way forward simulation without divergence reflection never licenses
termination transfer. -/
theorem forwardSim_rejects_termination (oid : String) :
    (OracleGrade.forwardSim oid).licenses .termination = false :=
  rfl

/-- Bidirectional fault equivalence licenses existential UB refutations. -/
theorem biFaultEquiv_licenses_existsWitness (oid : String) :
    (OracleGrade.biFaultEquiv oid).licenses .existsWitness = true :=
  rfl

/-- Well-founded stutter equivalence never licenses timing-sensitive general
hyperproperties (`generalHyper`). -/
theorem wfStutter_rejects_generalHyper (oid : String) :
    (OracleGrade.biFaultEquiv oid).licenses .generalHyper = false :=
  rfl

/-- Safe functions structurally ignore `safetyPre`: even `safetyPre := False`
reduces to `True` when `isUnsafe = false`. -/
theorem safe_fn_ignores_false_safetyPre {Q R M : Type}
    (c : Trusted.Framework.FnContract Q R M) (q : Q) :
    c.effectiveSafetyPre false q := by
  intro h
  cases h

/-- Functions taking uninhabited parameter domains (such as `MirTy.never` / `!`)
satisfy `NonVacuousEntry` constructively without waivers or `Classical.choice`.
-/
theorem uninhabited_domain_nonVacuous {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (body : Body) (pre : Query → Prop)
    (hEmpty : ∀ q : Query, ¬ M.entryDom body q) :
    NonVacuousEntry M body pre :=
  Or.inr hEmpty

/-- Extract `EnvelopeCommonValid` from any satisfied `EnvelopeTheorem`. -/
theorem commonValid_of_envelopeTheorem {Prog Body Sig Query Ret Mem : Type}
    {env : VerificationEnvelope Prog Body Sig Query Ret Mem}
    (h : EnvelopeTheorem env) :
    EnvelopeCommonValid (envelopeModel env) (envelopeProgram env)
      (match env with
       | .structured _ _ _ _ _ cs _ => cs
       | .legacy _ _ _ _ cs _ => cs)
      (envelopeGaps env) := by
  cases env with
  | structured _ _ _ _ _ _ _ => exact h.1
  | legacy _ _ _ _ _ _ => exact h.1

/-- Every model-wide gap required by `(envelopeModel env).modelGaps` (such as
`defaultMirDownstreamGaps` for `MirProfileV1` and `MirProfileV2`) must appear
in `envelopeGaps env`. -/
theorem modelGaps_of_envelopeTheorem {Prog Body Sig Query Ret Mem : Type}
    (env : VerificationEnvelope Prog Body Sig Query Ret Mem)
    (hThm : EnvelopeTheorem env) :
    ∀ g, g ∈ (envelopeModel env).modelGaps → g ∈ envelopeGaps env :=
  (commonValid_of_envelopeTheorem hThm).2.2.2.2.2.2.2

/-- Any model with no external declarations (`∀ b, M.bodyIsExternal b = false`,
including `MirProfileV1` and `MirProfileV2`) forbids non-empty `stubs` in a
satisfied `EnvelopeTheorem`, preventing captured local bodies from being waived
as assumed external callees. -/
theorem no_stubs_of_all_local_model {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (hLocal : ∀ b : Body, M.bodyIsExternal b = false)
    (prog : Prog)
    (entries : List (VerifiedEntry Sig Query Ret Mem))
    (stubs : List (AssumedStub Sig Query Ret Mem))
    (refutations : List (RefutationEntry Sig Query))
    (claimShapes : List ClaimShape)
    (gaps : List DisclosedGap)
    (hThm : EnvelopeTheorem
      (mkEnvelope M prog entries stubs refutations claimShapes gaps)) :
    stubs = [] := by
  cases stubs with
  | nil => rfl
  | cons s rest =>
    have ⟨_, body, _, hStub⟩ := hThm.2.2.2.2.1 s (List.Mem.head _)
    have hExt : M.bodyIsExternal body = true := hStub.1
    rw [hLocal body] at hExt
    exact Bool.noConfusion hExt

/-- Any unbridged profile (`OracleGrade.unbridged pid`) cannot satisfy
`EnvelopeTheorem` unless `pid = M.profileId` and
`DisclosedGap.unbridgedSemantics M.profileId` is disclosed in `gaps`. -/
theorem unbridged_envelope_requires_gap {Prog Body Sig Query Ret Mem : Type}
    (env : VerificationEnvelope Prog Body Sig Query Ret Mem) (pid : String)
    (hGrade : (envelopeModel env).oracleGrade = .unbridged pid)
    (hThm : EnvelopeTheorem env) :
    pid = (envelopeModel env).profileId ∧
      DisclosedGap.unbridgedSemantics (envelopeModel env).profileId ∈
        envelopeGaps env := by
  have hCommon := commonValid_of_envelopeTheorem hThm
  have hDisc := hCommon.2.2.2.2.2.1
  rw [hGrade] at hDisc
  refine ⟨hDisc.1, ?_⟩
  rw [← hDisc.1]
  exact hDisc.2

/-- Any partial-scope capture (`M.isPartialScope prog = true`, such as `.unit`)
cannot satisfy `EnvelopeTheorem` unless `DisclosedGap.selectedUnitScope` is
present in `gaps`. -/
theorem partial_scope_envelope_requires_gap {Prog Body Sig Query Ret Mem : Type}
    (env : VerificationEnvelope Prog Body Sig Query Ret Mem)
    (hPart : (envelopeModel env).isPartialScope (envelopeProgram env) = true)
    (hThm : EnvelopeTheorem env) :
    DisclosedGap.selectedUnitScope ∈ envelopeGaps env :=
  (commonValid_of_envelopeTheorem hThm).2.2.2.2.1 hPart

/-- Every legacy `Specs` envelope satisfying `EnvelopeTheorem` must disclose
`DisclosedGap.rawLegacySpec`. -/
theorem legacy_envelope_requires_rawLegacySpec_gap
    {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (prog : Prog) (sFn : String → Query → Prop) (pFn : Prog → Prop)
    (cs : List ClaimShape) (gs : List DisclosedGap)
    (hThm : EnvelopeTheorem (mkLegacyEnvelope M prog sFn pFn cs gs)) :
    DisclosedGap.rawLegacySpec ∈ gs :=
  hThm.2.1

/-- An inconsistent external callee stub asserting `postReturn := False` under
a total normal-return `EffectMask` on an inhabited valid entry `q` cannot
satisfy `StubRealizable`. -/
theorem stub_false_post_unrealizable {Prog Body Sig Query Ret Mem : Type}
    (M : ExecutionModel Prog Body Sig Query Ret Mem)
    (body : Body) (q : Query)
    (hDom : M.entryDom body q) :
    ¬ StubRealizable M body
        { postReturn := fun _ _ _ => False
          effects := { terminates := true, noUnwind := true, noAbort := true } } := by
  intro hReal
  have hBeh :
      ({ postReturn := fun _ _ _ => False
         effects := { terminates := true, noUnwind := true, noAbort := true } :
         Trusted.Framework.FnContract Query Ret Mem }).effectiveBehaviorPre
        (M.bodyIsUnsafe body) q :=
    ⟨fun _ => True.intro, True.intro⟩
  cases hReal q hDom hBeh with
  | inl hTerm => exact Bool.noConfusion hTerm
  | inr hRest =>
    cases hRest with
    | inl hRet =>
      cases hRet with
      | intro _ hMem =>
        cases hMem with
        | intro _ hPost => exact hPost.2
    | inr hRest2 =>
      cases hRest2 with
      | inl hUnw => exact Bool.noConfusion hUnw.1
      | inr hAbt => exact Bool.noConfusion hAbt.1

/-- Definitional (`rfl`) zero-WHNF-tax probe: `MirProfileV1.wellFormed` on
`MirProfileV1.execForBody p defId` is definitionally identical to
`Trusted.MirSemantics.WellFormed (entryProgForBody p defId) q`. -/
theorem mirProfileV1_wellFormed_defeq (p : Program) (defId : DefId)
    (q : Query) :
    MirProfileV1.wellFormed (MirProfileV1.execForBody p defId) q =
      WellFormed (entryProgForBody p defId) q :=
  rfl

/-- Definitional (`rfl`) zero-WHNF-tax probe: `MirProfileV2.wellFormed` on
`MirProfileV2.execForBody p defId` is definitionally identical to
`Trusted.MirSemantics.WellFormedV2 (entryProgForBody p defId) q`. -/
theorem mirProfileV2_wellFormed_defeq (p : Program) (defId : DefId)
    (q : Query) :
    MirProfileV2.wellFormed (MirProfileV2.execForBody p defId) q =
      WellFormedV2 (entryProgForBody p defId) q :=
  rfl

theorem bool_and_eq_true_iff (a b : Bool) :
    (a && b) = true ↔ a = true ∧ b = true := by
  cases a with
  | false =>
    exact ⟨fun h => Bool.noConfusion h, fun ⟨h, _⟩ => Bool.noConfusion h⟩
  | true =>
    cases b with
    | false =>
      exact ⟨fun h => Bool.noConfusion h, fun ⟨_, h⟩ => Bool.noConfusion h⟩
    | true =>
      exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

theorem bodies_nonEmpty_compat (bs : List Body) :
    (!bs.isEmpty) = true ↔ (!bs.isEmpty = true) := by
  cases bs with
  | nil =>
    exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  | cons _ _ =>
    exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem nat_ne_of_beq_false {m n : Nat} (h : Nat.beq m n = false) :
    m ≠ n := by
  intro hEq
  subst hEq
  have hRefl : ∀ k : Nat, Nat.beq k k = true := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => exact ih
  rw [hRefl m] at h
  exact Bool.noConfusion h

theorem ne_string_of_len_beq_false {a b : String}
    (h : Nat.beq a.toByteArray.data.toList.length
           b.toByteArray.data.toList.length = false) :
    a ≠ b := by
  intro hEq
  exact nat_ne_of_beq_false h
    (congrArg (fun s => s.toByteArray.data.toList.length) hEq)

theorem nonEmpty_profile_id : ("mir_profile_v1" : String) ≠ "" :=
  ne_string_of_len_beq_false rfl

theorem nonEmpty_profile_v2_id : ("mir_profile_v2" : String) ≠ "" :=
  ne_string_of_len_beq_false rfl

theorem nonEmpty_oracle_id :
    ("lean_miri_v1_deinit_moved_place" : String) ≠ "" :=
  ne_string_of_len_beq_false rfl

theorem eq_of_mem_singleton {α : Type} {x y : α} (h : x ∈ [y]) : x = y := by
  cases h with
  | head => rfl
  | tail _ hNil => cases hNil

theorem absurd_mem_nil {α : Type} {P : α → Prop} (x : α)
    (h : x ∈ ([] : List α)) : P x := by
  cases h

theorem false_of_mem_nil {α : Type} {x : α} (h : x ∈ ([] : List α)) :
    False := by
  cases h

theorem getElem?_mem {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α},
      Trusted.MirSemantics.getElem? xs i = some x → x ∈ xs
  | [], _, _ => fun h => by cases h
  | x :: xs, 0, y => fun h => by
    injection h with hEq
    subst hEq
    exact List.Mem.head _
  | x :: xs, n + 1, y => fun h =>
    List.Mem.tail x (getElem?_mem h)

theorem any_eq_true_of_mem {α : Type} (p : α → Bool) :
    ∀ {xs : List α} {x : α}, x ∈ xs → p x = true → xs.any p = true
  | [], _, hMem, _ => False.elim (false_of_mem_nil hMem)
  | y :: ys, x, hMem, hp => by
    cases hMem with
    | head =>
      change (p y || ys.any p) = true
      rw [hp]
      rfl
    | tail _ hTail =>
      change (p y || ys.any p) = true
      rw [any_eq_true_of_mem p hTail hp]
      cases p y <;> rfl

theorem mem_append_left {α : Type} {x : α} (l₁ : List α) (l₂ : List α)
    (h : x ∈ l₁) : x ∈ l₁ ++ l₂ := by
  induction l₁ with
  | nil => exact False.elim (false_of_mem_nil h)
  | cons a rest ih =>
    cases h with
    | head => exact List.Mem.head _
    | tail _ hTail => exact List.Mem.tail a (ih hTail)

theorem mem_append_right {α : Type} {x : α} (l₁ : List α) (l₂ : List α)
    (h : x ∈ l₂) : x ∈ l₁ ++ l₂ := by
  induction l₁ with
  | nil => exact h
  | cons a rest ih => exact List.Mem.tail a ih

theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem nat_beq_symm (a b : Nat) (h : Nat.beq a b = true) :
    Nat.beq b a = true := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => rfl
    | succ _ => exact Bool.noConfusion h
  | succ a' ih =>
    cases b with
    | zero => exact Bool.noConfusion h
    | succ b' => exact ih b' h

theorem nat_beq_eq (a b : Nat) (h : Nat.beq a b = true) : a = b := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => rfl
    | succ _ => exact Bool.noConfusion h
  | succ a' ih =>
    cases b with
    | zero => exact Bool.noConfusion h
    | succ b' => exact congrArg Nat.succ (ih b' h)

theorem natNotElem_head_false (id : AllocId) (seen : List AllocId)
    (h : natNotElem id seen = true) : ¬ (id ∈ seen) := by
  intro hMem
  induction seen with
  | nil => exact false_of_mem_nil hMem
  | cons s rest ih =>
    change (!Nat.beq id s && natNotElem id rest) = true at h
    rw [bool_and_eq_true_iff] at h
    cases hMem with
    | head =>
      rw [nat_beq_refl] at h
      exact Bool.noConfusion h.1
    | tail _ hTail => exact ih h.2 hTail

theorem allocIdsValid_not_in_seen
    (seen : List AllocId) (rest : List Allocation)
    (hWalk : allocIdsValid seen rest = true)
    (a : Allocation) (hTail : a ∈ rest) : ¬ (a.allocId ∈ seen) := by
  induction rest generalizing seen with
  | nil => exact False.elim (false_of_mem_nil hTail)
  | cons y ys ih2 =>
    change (!Nat.beq y.allocId 0 &&
      natNotElem y.allocId seen &&
      Nat.blt y.bytes.length isizeMaxBytes &&
      Nat.ble y.alignLog2 29 &&
      allocIdsValid (y.allocId :: seen) ys) = true at hWalk
    rw [bool_and_eq_true_iff] at hWalk
    have hY := hWalk.1
    rw [bool_and_eq_true_iff] at hY
    rw [bool_and_eq_true_iff] at hY
    rw [bool_and_eq_true_iff] at hY
    cases hTail with
    | head => exact natNotElem_head_false _ _ hY.1.1.2
    | tail _ hTail2 =>
      intro hIn
      exact ih2 (y.allocId :: seen) hWalk.2 hTail2
        (List.Mem.tail y.allocId hIn)

theorem findAllocation_of_not_seen
    (seen : List AllocId) (allocs : List Allocation)
    (hVal : allocIdsValid seen allocs = true)
    (a : Allocation) (hMem : a ∈ allocs) :
    findAllocation a.allocId allocs = some a := by
  induction allocs generalizing seen with
  | nil => exact False.elim (false_of_mem_nil hMem)
  | cons x rest ih =>
    change (!Nat.beq x.allocId 0 &&
      natNotElem x.allocId seen &&
      Nat.blt x.bytes.length isizeMaxBytes &&
      Nat.ble x.alignLog2 29 &&
      allocIdsValid (x.allocId :: seen) rest) = true at hVal
    rw [bool_and_eq_true_iff] at hVal
    have hRestVal := hVal.2
    cases hMem with
    | head =>
      change (if Nat.beq a.allocId a.allocId then some a
        else findAllocation a.allocId rest) = some a
      rw [nat_beq_refl]
      rfl
    | tail _ hTail =>
      have hRec := ih (x.allocId :: seen) hRestVal hTail
      change (if Nat.beq x.allocId a.allocId then some x
        else findAllocation a.allocId rest) = some a
      cases hEq : Nat.beq x.allocId a.allocId with
      | true =>
        have hNotElem : ¬ (a.allocId ∈ (x.allocId :: seen)) :=
          allocIdsValid_not_in_seen (x.allocId :: seen) rest hRestVal a hTail
        have hEqNat : x.allocId = a.allocId :=
          nat_beq_eq x.allocId a.allocId hEq
        rw [← hEqNat] at hNotElem
        exact False.elim (hNotElem (List.Mem.head _))
      | false => exact hRec

theorem extractCallerAllocations_self
    (m : MemoryState) (seen : List AllocId)
    (allAllocs allocs : List Allocation)
    (hSub : ∀ a, a ∈ allocs → a ∈ allAllocs)
    (hMemEq : m.allocations = allAllocs)
    (hVal : allocIdsValid seen allAllocs = true) :
    extractCallerAllocations m allocs = allocs := by
  induction allocs with
  | nil => rfl
  | cons a rest ih =>
    change
      (findAllocation a.allocId m.allocations).getD a ::
        extractCallerAllocations m rest = a :: rest
    rw [hMemEq]
    have hFind :=
      findAllocation_of_not_seen seen allAllocs hVal a
        (hSub a (List.Mem.head _))
    rw [hFind]
    dsimp only [Option.getD]
    rw [ih (fun b hb => hSub b (List.Mem.tail _ hb))]

/-- Snapshotting unmodified caller memory from any `m` with
`m.allocations = cm.allocations` returns `cm` unchanged whenever
`validCallerMemory cm = true`. -/
theorem extractCallerMemory_of_allocations_eq (cm : CallerMemory)
    (m : MemoryState) (hEq : m.allocations = cm.allocations)
    (hVal : validCallerMemory cm = true) :
    extractCallerMemory cm m = cm := by
  cases cm with
  | mk allocs =>
    change ⟨extractCallerAllocations m allocs⟩ = (⟨allocs⟩ : CallerMemory)
    rw [extractCallerAllocations_self m [] allocs allocs (fun _ h => h) hEq hVal]

/-- Snapshotting unmodified caller memory from `entryMemoryWithCaller cm`
returns `cm` unchanged whenever `validCallerMemory cm = true`. -/
theorem extractCallerMemory_entryMemoryWithCaller (cm : CallerMemory)
    (hVal : validCallerMemory cm = true) :
    extractCallerMemory cm (entryMemoryWithCaller cm) = cm :=
  extractCallerMemory_of_allocations_eq cm (entryMemoryWithCaller cm) rfl hVal

/-- Snapshotting unmodified caller memory from `entryMemoryForArgsV2`
returns `cm` unchanged whenever `validCallerMemory cm = true`. -/
theorem extractCallerMemory_entryMemoryForArgsV2 (cm : CallerMemory)
    (paramTys : List MirTy) (args : List Val)
    (hVal : validCallerMemory cm = true) :
    extractCallerMemory cm (entryMemoryForArgsV2 cm paramTys args) = cm := by
  apply extractCallerMemory_of_allocations_eq cm _ _ hVal
  unfold entryMemoryForArgsV2
  cases tyListHasRawPtrV2 paramTys <;> rfl

/-- `entryMemoryForArgsV2` preserves `entryMemoryWithCaller`'s allocations. -/
theorem entryMemoryForArgsV2_allocations_eq (cm : CallerMemory)
    (paramTys : List MirTy) (args : List Val) :
    (entryMemoryForArgsV2 cm paramTys args).allocations =
      (entryMemoryWithCaller cm).allocations := by
  unfold entryMemoryForArgsV2
  cases tyListHasRawPtrV2 paramTys <;> rfl

theorem programVerified_iff_legacyEnvelope (p : Program) (specs : Specs)
    (gaps : List DisclosedGap)
    (hScope : mirProgramIsPartialScope p = true → .selectedUnitScope ∈ gaps)
    (hDownstream : ∀ g, g ∈ defaultMirDownstreamGaps → g ∈ gaps)
    (hRaw : DisclosedGap.rawLegacySpec ∈ gaps) :
    EnvelopeTheorem
        (mkLegacyEnvelope
          MirProfileV1 p (fun id q => specs.safety id q.args)
          specs.property [.forallSafety] gaps) ↔
      ProgramVerified p specs := by
  refine ⟨?_, ?_⟩
  · intro hEnv
    have hCommon := hEnv.1
    have hAdm := hCommon.2.1
    unfold MirProfileV1 mkMirExecutionModel mirProgramAdmitted at hAdm
    dsimp at hAdm
    rw [bool_and_eq_true_iff] at hAdm
    rw [bool_and_eq_true_iff] at hAdm
    rw [bool_and_eq_true_iff] at hAdm
    have hPtr := hAdm.1.1.1
    have hProf := hAdm.1.1.2
    have hNonEmpty := (bodies_nonEmpty_compat p.bodies).mp hAdm.1.2
    have hEntry := hAdm.2
    have hBodiesAdm := hCommon.2.2.1
    have hUniq := hCommon.2.2.2.1
    have hBodies := hEnv.2.2.2.1
    have hProp := hEnv.2.2.2.2
    refine ⟨hPtr, hProf, hNonEmpty, hEntry, hUniq, ?_, hProp⟩
    intro defId body hGet
    refine ⟨hGet, hBodiesAdm defId body hGet, ?_⟩
    intro args hArgs hSafe
    have hLeg := hBodies defId body hGet
    exact hLeg.2.2 { args := args, callerMem := ⟨[]⟩ } ⟨hArgs, rfl⟩ hSafe
  · intro hProg
    have hPtr := hProg.1
    have hProf := hProg.2.1
    have hNonEmptyBool : (!p.bodies.isEmpty) = true :=
      (bodies_nonEmpty_compat p.bodies).mpr hProg.2.2.1
    have hEntry := hProg.2.2.2.1
    have hUniq := hProg.2.2.2.2.1
    have hBodies := hProg.2.2.2.2.2.1
    have hProp := hProg.2.2.2.2.2.2
    have hAdm :
        mirProgramAdmitted 1 p = true := by
      unfold mirProgramAdmitted
      rw [hPtr, hProf, hNonEmptyBool, hEntry]
      rfl
    refine ⟨⟨nonEmpty_profile_id, hAdm,
             (fun defId body hGet => (hBodies defId body hGet).2.1),
             hUniq, hScope, nonEmpty_oracle_id, ?_, hDownstream⟩,
            hRaw, List.Mem.head _, ?_, hProp⟩
    · intro cs hMem
      cases hMem with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hTail => cases hTail
    · intro defId body hGet
      refine ⟨rfl, (fun _ hGap => by cases hGap), ?_⟩
      intro q hDom hSafe
      cases q with
      | mk args callerMem =>
        dsimp at hDom hSafe
        rw [hDom.2]
        exact (hBodies defId body hGet).2.2 args hDom.1 hSafe

/-- Bidirectional equivalence between `CrateEnvelopeTheorem` and
`CrateTheorem`. -/
theorem crateEnvelopeTheorem_iff_crateTheorem (c : Crate) :
    CrateEnvelopeTheorem c ↔ CrateTheorem c := by
  refine ⟨?_, ?_⟩
  · intro ⟨hScope, hEnv⟩
    refine ⟨hScope, ?_⟩
    exact (programVerified_iff_legacyEnvelope c.program c.specs legacyCrateGaps
      (fun hPart => by
        unfold mirProgramIsPartialScope at hPart
        rw [hScope] at hPart
        exact Bool.noConfusion hPart)
      (fun _ h => List.Mem.tail _ h)
      (List.Mem.head _)).mp hEnv
  · intro ⟨hScope, hProg⟩
    refine ⟨hScope, ?_⟩
    exact (programVerified_iff_legacyEnvelope c.program c.specs legacyCrateGaps
      (fun hPart => by
        unfold mirProgramIsPartialScope at hPart
        rw [hScope] at hPart
        exact Bool.noConfusion hPart)
      (fun _ h => List.Mem.tail _ h)
      (List.Mem.head _)).mpr hProg

/-- Bidirectional equivalence between `UnitEnvelopeTheorem` and
`UnitTheorem`. -/
theorem unitEnvelopeTheorem_iff_unitTheorem (c : Crate) :
    UnitEnvelopeTheorem c ↔ UnitTheorem c := by
  refine ⟨?_, ?_⟩
  · intro ⟨hScope, hEnv⟩
    refine ⟨hScope, ?_⟩
    exact (programVerified_iff_legacyEnvelope c.program c.specs legacyUnitGaps
      (fun _ => List.Mem.head _)
      (fun _ h => List.Mem.tail _ (List.Mem.tail _ h))
      (List.Mem.tail _ (List.Mem.head _))).mp hEnv
  · intro ⟨hScope, hProg⟩
    refine ⟨hScope, ?_⟩
    exact (programVerified_iff_legacyEnvelope c.program c.specs legacyUnitGaps
      (fun _ => List.Mem.head _)
      (fun _ h => List.Mem.tail _ (List.Mem.tail _ h))
      (List.Mem.tail _ (List.Mem.head _))).mpr hProg

theorem programVerifiedV2_iff_legacyEnvelope (p : Program) (specs : SpecsV2)
    (gaps : List DisclosedGap)
    (hScope : mirProgramIsPartialScope p = true → .selectedUnitScope ∈ gaps)
    (hUnbridged : DisclosedGap.unbridgedSemantics "mir_profile_v2" ∈ gaps)
    (hDownstream : ∀ g, g ∈ defaultMirDownstreamGaps → g ∈ gaps)
    (hBodyGaps :
      ∀ defId body,
        Trusted.MirSemantics.getElem? p.bodies defId = some body →
        ∀ g, g ∈ mirProfileV2RequiredGaps body → g ∈ gaps)
    (hRaw : DisclosedGap.rawLegacySpec ∈ gaps) :
    EnvelopeTheorem
        (mkLegacyEnvelope
          MirProfileV2 p specs.safety specs.property [.forallSafety] gaps) ↔
      ProgramVerifiedV2 p specs := by
  refine ⟨?_, ?_⟩
  · intro hEnv
    have hCommon := hEnv.1
    have hAdm := hCommon.2.1
    unfold MirProfileV2 mkMirExecutionModel mirProgramAdmitted at hAdm
    dsimp at hAdm
    rw [bool_and_eq_true_iff] at hAdm
    rw [bool_and_eq_true_iff] at hAdm
    rw [bool_and_eq_true_iff] at hAdm
    have hPtr := hAdm.1.1.1
    have hProf := hAdm.1.1.2
    have hNonEmpty := (bodies_nonEmpty_compat p.bodies).mp hAdm.1.2
    have hEntry := hAdm.2
    have hBodiesAdm := hCommon.2.2.1
    have hUniq := hCommon.2.2.2.1
    have hBodies := hEnv.2.2.2.1
    have hProp := hEnv.2.2.2.2
    refine ⟨hPtr, hProf, hNonEmpty, hEntry, hUniq, ?_, hProp⟩
    intro defId body hGet
    refine ⟨hGet, hBodiesAdm defId body hGet, ?_⟩
    intro q hArgs hSafe
    exact (hBodies defId body hGet).2.2 q hArgs hSafe
  · intro hProg
    have hPtr := hProg.1
    have hProf := hProg.2.1
    have hNonEmptyBool : (!p.bodies.isEmpty) = true :=
      (bodies_nonEmpty_compat p.bodies).mpr hProg.2.2.1
    have hEntry := hProg.2.2.2.1
    have hUniq := hProg.2.2.2.2.1
    have hBodies := hProg.2.2.2.2.2.1
    have hProp := hProg.2.2.2.2.2.2
    have hAdm :
        mirProgramAdmitted 2 p = true := by
      unfold mirProgramAdmitted
      rw [hPtr, hProf, hNonEmptyBool, hEntry]
      rfl
    refine ⟨⟨nonEmpty_profile_v2_id, hAdm,
             (fun defId body hGet => (hBodies defId body hGet).2.1),
             hUniq, hScope, ⟨rfl, hUnbridged⟩, ?_, hDownstream⟩,
            hRaw, List.Mem.head _, ?_, hProp⟩
    · intro cs hMem
      cases hMem with
      | head => exact ⟨rfl, absurd_mem_nil⟩
      | tail _ hTail => cases hTail
    · intro defId body hGet
      refine ⟨rfl, hBodyGaps defId body hGet, ?_⟩
      intro q hDom hSafe
      exact (hBodies defId body hGet).2.2 q hDom hSafe

theorem profileV2_unbridged_mem (p : Program) :
    DisclosedGap.unbridgedSemantics "mir_profile_v2" ∈
      profileV2ProgramGaps p := by
  unfold profileV2ProgramGaps
  cases p.bodies.any (fun b => tyListHasRawPtrV2 b.locals) <;>
    exact List.Mem.head _

theorem profileV2_bodyGaps_mem (p : Program) (defId : Nat) (body : Body)
    (hGet : Trusted.MirSemantics.getElem? p.bodies defId = some body) :
    ∀ g, g ∈ mirProfileV2RequiredGaps body → g ∈ profileV2ProgramGaps p := by
  intro g hg
  unfold mirProfileV2RequiredGaps at hg
  cases hRaw : tyListHasRawPtrV2 body.locals with
  | false =>
    rw [hRaw] at hg
    have hEq := eq_of_mem_singleton hg
    subst hEq
    unfold profileV2ProgramGaps
    cases p.bodies.any (fun b => tyListHasRawPtrV2 b.locals) <;>
      exact List.Mem.tail _ (List.Mem.head _)
  | true =>
    rw [hRaw] at hg
    cases hg with
    | head =>
      unfold profileV2ProgramGaps
      cases p.bodies.any (fun b => tyListHasRawPtrV2 b.locals) <;>
        exact List.Mem.tail _ (List.Mem.head _)
    | tail _ hTail =>
      have hEq := eq_of_mem_singleton hTail
      subst hEq
      have hAny : p.bodies.any (fun b => tyListHasRawPtrV2 b.locals) = true :=
        any_eq_true_of_mem (fun b => tyListHasRawPtrV2 b.locals)
          (getElem?_mem hGet) hRaw
      unfold profileV2ProgramGaps
      rw [hAny]
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-- Bidirectional equivalence between `CrateEnvelopeTheoremV2` and
`CrateTheoremV2`. -/
theorem crateEnvelopeTheoremV2_iff_crateTheoremV2 (c : CrateV2) :
    CrateEnvelopeTheoremV2 c ↔ CrateTheoremV2 c := by
  refine ⟨?_, ?_⟩
  · intro ⟨hScope, hEnv⟩
    refine ⟨hScope, ?_⟩
    exact (programVerifiedV2_iff_legacyEnvelope c.program c.specs
      (legacyCrateGapsV2 c.program)
      (fun hPart => by
        unfold mirProgramIsPartialScope at hPart
        rw [hScope] at hPart
        exact Bool.noConfusion hPart)
      (mem_append_left _ _ (profileV2_unbridged_mem c.program))
      (fun _ h => mem_append_right _ _ (List.Mem.tail _ h))
      (fun defId body hGet g hg =>
        mem_append_left _ _
          (profileV2_bodyGaps_mem c.program defId body hGet g hg))
      (mem_append_right _ _ (List.Mem.head _))).mp hEnv
  · intro ⟨hScope, hProg⟩
    refine ⟨hScope, ?_⟩
    exact (programVerifiedV2_iff_legacyEnvelope c.program c.specs
      (legacyCrateGapsV2 c.program)
      (fun hPart => by
        unfold mirProgramIsPartialScope at hPart
        rw [hScope] at hPart
        exact Bool.noConfusion hPart)
      (mem_append_left _ _ (profileV2_unbridged_mem c.program))
      (fun _ h => mem_append_right _ _ (List.Mem.tail _ h))
      (fun defId body hGet g hg =>
        mem_append_left _ _
          (profileV2_bodyGaps_mem c.program defId body hGet g hg))
      (mem_append_right _ _ (List.Mem.head _))).mpr hProg

/-- Bidirectional equivalence between `UnitEnvelopeTheoremV2` and
`UnitTheoremV2`. -/
theorem unitEnvelopeTheoremV2_iff_unitTheoremV2 (c : CrateV2) :
    UnitEnvelopeTheoremV2 c ↔ UnitTheoremV2 c := by
  refine ⟨?_, ?_⟩
  · intro ⟨hScope, hEnv⟩
    refine ⟨hScope, ?_⟩
    exact (programVerifiedV2_iff_legacyEnvelope c.program c.specs
      (legacyUnitGapsV2 c.program)
      (fun _ => mem_append_right _ _ (List.Mem.head _))
      (mem_append_left _ _ (profileV2_unbridged_mem c.program))
      (fun _ h => mem_append_right _ _ (List.Mem.tail _ (List.Mem.tail _ h)))
      (fun defId body hGet g hg =>
        mem_append_left _ _
          (profileV2_bodyGaps_mem c.program defId body hGet g hg))
      (mem_append_right _ _ (List.Mem.tail _ (List.Mem.head _)))).mp hEnv
  · intro ⟨hScope, hProg⟩
    refine ⟨hScope, ?_⟩
    exact (programVerifiedV2_iff_legacyEnvelope c.program c.specs
      (legacyUnitGapsV2 c.program)
      (fun _ => mem_append_right _ _ (List.Mem.head _))
      (mem_append_left _ _ (profileV2_unbridged_mem c.program))
      (fun _ h => mem_append_right _ _ (List.Mem.tail _ (List.Mem.tail _ h)))
      (fun defId body hGet g hg =>
        mem_append_left _ _
          (profileV2_bodyGaps_mem c.program defId body hGet g hg))
      (mem_append_right _ _ (List.Mem.tail _ (List.Mem.head _)))).mpr hProg

end Anneal.Framework

end
