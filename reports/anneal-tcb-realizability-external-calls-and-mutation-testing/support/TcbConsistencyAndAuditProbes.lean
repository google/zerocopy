-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# TCB Relative-Consistency, Vacuity, and Realizability Probes

This file mechanizes in Lean 4 (`v4.34.1`) the TCB relative-consistency,
vacuity, and realizability analysis across `trusted-core`
(`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) and `mir-to-x86`
(`4f45f0a391a921ced9c9dc773b9a040dbc215d14`):

1. **Pointwise `hTcb` Vacuity:** In `Trusted/Refinement.lean:444-456` and
   `Trusted/MirSemantics.lean:859-865`, `VerificationResultOn` places
   `AllHold (assumptions.map TrustedAssumption.meaning)` on the left-hand side
   of an implication (`→`). Any pointwise contradiction in `hTcb` at a single
   boundary query `q₀` (such as a PME-rejected monomorphization where `MirSem`
   is vacuously `.defined = True`, or a `steps = 0` query where `ReachesPrefix`
   is trivially `.running`) allows `Proof.verify_crate` to prove
   `Trusted.CrateTheorem` for an arbitrary UB-triggering crate with zero kernel
   axioms (`trustLevel := 0`).
2. **Inconsistency of Hidden `opaque` Witness Terms:** In
   `Trusted/MirSemantics.lean:690-716` (and
   `mir-to-x86:Trusted/X86Semantics.lean:716-742`), the underlying witness terms
   supplied to `opaque TargetSem := fun _ _ => Partial.ub` and
   `opaque π_c := fun b => b` are themselves inconsistent with
   `RustcCompiler.SoundOn body` at every query with `steps = 0`. Because
   `rustc`, `TargetSem`, and `π_c` are top-level `opaque` constants, `theory/`
   cannot instantiate them with a consistent model to prove a machine-checked
   realizability witness.
3. **Universal `TCBModel` + Realizability Witness Architecture:** Replacing
   top-level `opaque` constants with an explicit `TCBModel` structure and
   quantifying universally (`∀ M : TCBModel, CrateTheoremIn M c`) paired with a
   constructive realizability theorem
   (`∃ M : TCBModel, AllHold (c.tcb.map (TCBItem.meaningIn M))`) makes `hTcb`
   provably non-vacuous in Lean's base logic and makes UB-triggering crates
   provably refutable (`¬ CrateTheoremUniversal alwaysUbCrate`).
4. **`mir-to-x86` Architecture Comparison:** Mechanizes why `mir-to-x86`
   (`4f45f0a391a921ced9c9dc773b9a040dbc215d14`) retains the `opaque` assumption
   pattern at `TCBItem.assemblerLowering` and leaves `MirBody` and
   `compileStage0` disconnected from `Trusted.CrateTheorem`, and shows how to
   close that gap.
-/

namespace Anneal.TcbAuditProbes

-- ============================================================================
-- Section 1: Core Abstractions from `trusted-core` (`e6a0b2da5ec3`)
-- ============================================================================

/-- Partial observation cell from `Trusted/Refinement.lean:254-258`. -/
structure Partial (O : Type) : Type where
  defined : Prop
  val : defined → O

/-- The universally undefined observation cell (`Trusted/Refinement.lean:261`). -/
def Partial.ub {O : Type} : Partial O :=
  { defined := False, val := False.elim }

/-- The universally defined observation cell (`Trusted/Refinement.lean:264`). -/
def Partial.total {O : Type} (v : O) : Partial O :=
  { defined := True, val := fun _ => v }

/-- Forward-refinement ordering on partial observations
(`Trusted/Refinement.lean:269-277`). -/
instance instLEPartial {O : Type} [LE O] : LE (Partial O) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂

instance instLEProp : LE Prop where
  le P Q := P → Q

instance instLESet {α : Type} : LE (α → Prop) where
  le S₁ S₂ := ∀ a, S₁ a → S₂ a

/-- Query-indexed behavior (`Trusted/Refinement.lean:282`). -/
abbrev Behavior (Q O : Type) := Q → Partial O

instance instLEBehavior {Q O : Type} [LE O] : LE (Behavior Q O) where
  le b₁ b₂ := ∀ q, b₁ q ≤ b₂ q

/-- Monotonicity between preordered types (`Trusted/Refinement.lean:51-52`). -/
def Monotone {α β : Type} [LE α] [LE β] (f : α → β) : Prop :=
  ∀ a b, a ≤ b → f a ≤ f b

/-- Language bundle (`Trusted/Refinement.lean:293-305`). -/
structure Language where
  Prog : Type
  Query : Type
  Obs : Type
  [instLEObs : LE Obs]
  sem : Prog → Behavior Query Obs

attribute [instance] Language.instLEObs

abbrev Language.Behavior (L : Language) : Type :=
  Anneal.TcbAuditProbes.Behavior L.Query L.Obs

/-- Well-formedness specification over a query precondition
(`Trusted/Refinement.lean:321-323`). -/
def Language.WellFormedOn (L : Language) (pre : L.Query → Prop)
    (b : L.Behavior) : Prop :=
  ∀ q, pre q → (b q).defined

/-- Pointwise behavioral specification (`Trusted/Refinement.lean:334-336`). -/
def Language.Spec (L : Language) (P : L.Query → L.Obs → Prop)
    (b : L.Behavior) : Prop :=
  ∀ q, ∃ h : (b q).defined, P q ((b q).val h)

/-- Relational compiler bundle (`Trusted/Refinement.lean:345-351`). -/
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog → Prop
  π : L_src.Behavior → L_tgt.Behavior

/-- Total compiler constructor (`Trusted/Refinement.lean:354-359`). -/
def Compiler.ofTotal {L_src L_tgt : Language}
    (f : L_src.Prog → L_tgt.Prog)
    (π : L_src.Behavior → L_tgt.Behavior) : Compiler L_src L_tgt where
  compile p_src p_tgt := p_tgt = f p_src
  π := π

/-- Relational compilation soundness (`Trusted/Refinement.lean:369-371`). -/
def Compiler.Compiles {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (p_src : L_src.Prog) (p_tgt : L_tgt.Prog) :
    Prop :=
  C.compile p_src p_tgt ∧ Monotone C.π ∧ (L_tgt.sem p_tgt ≤ C.π (L_src.sem p_src))

/-- Existential compilation soundness (`Trusted/Refinement.lean:375-376`). -/
def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (p_src : L_src.Prog) : Prop :=
  ∃ p_tgt, C.Compiles p_src p_tgt

/-- Verified specification transport (`Trusted/Refinement.lean:383-388`). -/
def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (p_src : L_src.Prog)
    (spec : L_src.Behavior → Prop) : Prop :=
  ∃ p_tgt, C.Compiles p_src p_tgt ∧
    ∃ b_lift, L_tgt.sem p_tgt ≤ C.π b_lift ∧ spec b_lift

/-- Explicit TCB assumption class (`Trusted/Refinement.lean:423-425`). -/
class TrustedAssumption (α : Type) where
  meaning : α → Prop

/-- Explicit trust policy (`Trusted/Refinement.lean:429-431`). -/
structure TrustPolicy (α : Type) where
  isAllowed : α → Prop

/-- Conjunction of a list of propositions (`Trusted/Refinement.lean:434-437`). -/
def AllHold : List Prop → Prop
  | [] => True
  | P :: Ps => P ∧ AllHold Ps

/-- Conditioned verification theorem gate (`Trusted/Refinement.lean:444-456`). -/
def VerificationResultOn {L_src L_tgt : Language} {α : Type}
    [TrustedAssumption α]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy α)
    (assumptions : List α)
    (prog : L_src.Prog)
    (pre : L_src.Query → Prop)
    (specs : List (L_src.Behavior → Prop)) : Prop :=
  AllHold (assumptions.map policy.isAllowed) ∧
  (AllHold (assumptions.map TrustedAssumption.meaning) →
    AllHold ((L_src.WellFormedOn pre :: specs).map (C.Verified prog)))

-- Small-step operational machine (`Trusted/StepResult.lean:41-199`).

inductive StepResult (State Trace Ret : Type) where
  | running (next : State) (events : List Trace)
  | returned (ret : Ret) (events : List Trace)
  | diverged (events : List Trace)
  | failed

structure SmallStepMachine (Prog State Trace Ret : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Trace Ret → Prop

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

inductive ExecOut (Trace Ret : Type) where
  | running
  | returned (ret : Ret)
  | diverged
  | failed

inductive ReachesPrefix {Prog State Trace Ret : Type}
    (M : SmallStepMachine Prog State Trace Ret) (p : Prog) :
    Nat → State → List Trace → ExecOut Trace Ret → Prop where
  | zero (s : State) :
      ReachesPrefix M p 0 s [] .running
  | stepRunning {n : Nat} {s s' : State} {ev rest : List Trace}
      {out : ExecOut Trace Ret} :
      M.step p s (.running s' ev) →
      ReachesPrefix M p n s' rest out →
      ReachesPrefix M p (n + 1) s (ev ++ rest) out
  | stepReturned {n : Nat} {s : State} {ret : Ret} {ev : List Trace} :
      M.step p s (.returned ret ev) →
      ReachesPrefix M p (n + 1) s ev (.returned ret)
  | stepDiverged {n : Nat} {s : State} {ev : List Trace} :
      M.step p s (.diverged ev) →
      ReachesPrefix M p (n + 1) s ev .diverged
  | stepFailed {n : Nat} {s : State} :
      M.step p s .failed →
      ReachesPrefix M p (n + 1) s [] .failed

def BehaviorOf {Prog State Trace Ret : Type}
    (M : SmallStepMachine Prog State Trace Ret) (p : Prog) :
    Behavior (ExecQuery State) (ExecOut Trace Ret → Prop) :=
  fun q =>
    { defined := M.initState p q.init →
        ∀ tr out, ReachesPrefix M p q.steps q.init tr out → out ≠ .failed
      val := fun _ out =>
        M.initState p q.init ∧
        ∃ tr, ReachesPrefix M p q.steps q.init tr out }

-- Minimal faithful slice of `MirSemantics.lean` (`e6a0b2da5ec3:550-865`).

abbrev TyParamId := Nat

inductive MirBody where
  /-- A body with a post-monomorphization size-equality check
  (`tySizes 0 = tySizes 1`) that immediately returns `0` when admitted. -/
  | pmeSizeEqReturnZero
  /-- A body that is unconditionally admitted at entry (`MonoAdmitted = True`)
  but immediately triggers undefined behavior (`.failed`) at step 1. -/
  | alwaysUbAtStep1
  deriving DecidableEq

structure MirState where
  tySizes : TyParamId → Nat

/-- Post-monomorphization admissibility (`Trusted/MirSemantics.lean:560-564`). -/
def MonoAdmitted (tySizes : TyParamId → Nat) : MirBody → Prop
  | .pmeSizeEqReturnZero => tySizes 0 = tySizes 1
  | .alwaysUbAtStep1 => True

/-- Entry-state admissibility (`Trusted/MirSemantics.lean:611-612`). -/
def initMirState (body : MirBody) (s : MirState) : Prop :=
  MonoAdmitted s.tySizes body

inductive evalMirBody : MirBody → MirState → StepResult MirState Unit Nat → Prop where
  | pmeReturn (s : MirState) :
      evalMirBody .pmeSizeEqReturnZero s (.returned 0 [])
  | ubFail (s : MirState) :
      evalMirBody .alwaysUbAtStep1 s .failed

def MirMachine : SmallStepMachine MirBody MirState Unit Nat where
  initState := initMirState
  step := evalMirBody

def MirSem (body : MirBody) :
    Behavior (ExecQuery MirState) (ExecOut Unit Nat → Prop) :=
  BehaviorOf MirMachine body

def MirLang : Language where
  Prog := MirBody
  Query := ExecQuery MirState
  Obs := ExecOut Unit Nat → Prop
  sem := MirSem

-- ============================================================================
-- Section 2: Pointwise `hTcb` Contradictions & Vacuous `CrateTheorem` Proofs
-- ============================================================================

/-- **Theorem 2.1 (`pme_rejected_query_mirSem_defined`):**
When a query `q` violates `MonoAdmitted q.init.tySizes body`, `initMirState` is
`False`, so `(MirSem body q).defined` is vacuously `True`. -/
theorem pme_rejected_query_mirSem_defined (body : MirBody)
    (q : ExecQuery MirState) (hRej : ¬ MonoAdmitted q.init.tySizes body) :
    (MirSem body q).defined := by
  intro hInit _ _ _
  exact False.elim (hRej hInit)

/-- **Theorem 2.2 (`step0_query_mirSem_defined`):**
At `q.steps = 0`, `(MirSem body q).defined` is unconditionally `True` for every
`body : MirBody`—even for `.alwaysUbAtStep1`! -/
theorem step0_query_mirSem_defined (body : MirBody) (s : MirState) :
    (MirSem body ⟨s, 0⟩).defined := by
  intro _ tr out hReach
  cases hReach
  intro hEq
  cases hEq

/-- **Theorem 2.3 (`pme_rejected_target_undefined_soundOn_false`):**
Suppose a target semantics models post-monomorphization rejection as target
undefinedness (`(TargetSem' (rustc' body) q).defined ↔ MonoAdmitted ...`) while
using the identity behavior map `π = id`. Because `MirSem` makes rejected
monomorphizations vacuously `.defined = True` (Theorem 2.1), `Compiler.SoundOn`
for `.pmeSizeEqReturnZero` is inconsistent and implies `False` at a single
rejected layout query (`tySizes 0 = 4, tySizes 1 = 8`). -/
def PmeRejectingTargetLang : Language where
  Prog := MirBody
  Query := ExecQuery MirState
  Obs := ExecOut Unit Nat → Prop
  sem body q :=
    { defined := MonoAdmitted q.init.tySizes body ∧ (MirSem body q).defined
      val := fun h => (MirSem body q).val h.2 }

def PmeRejectingCompiler : Compiler MirLang PmeRejectingTargetLang :=
  Compiler.ofTotal id id

theorem pme_rejected_target_undefined_soundOn_false :
    Compiler.SoundOn PmeRejectingCompiler .pmeSizeEqReturnZero → False := by
  rintro ⟨p_tgt, hEq, _, hRef⟩
  subst hEq
  let badState : MirState :=
    { tySizes := fun
        | 0 => 4
        | _ => 8 }
  let q₀ : ExecQuery MirState := { init := badState, steps := 1 }
  have hRej : ¬ MonoAdmitted q₀.init.tySizes .pmeSizeEqReturnZero := by
    intro h
    cases h
  have hMirDef : (MirSem .pmeSizeEqReturnZero q₀).defined :=
    pme_rejected_query_mirSem_defined .pmeSizeEqReturnZero q₀ hRej
  obtain ⟨hTgtDef, _⟩ := hRef q₀ hMirDef
  exact hRej hTgtDef.1

/-- **Theorem 2.4 (`hidden_opaque_witness_soundOn_false`):**
In `Trusted/MirSemantics.lean:690-716`, the actual witness terms supplied to
`opaque rustc`, `opaque TargetSem`, and `opaque π_c` are:
- `rustc := fun _ => ()`
- `TargetSem := fun _ _ => Partial.ub`
- `π_c := fun b => b`
We prove that for *every* `body : MirBody`, `Compiler.SoundOn` instantiated with
those witness terms implies `False` (evaluated at any `steps = 0` query)! Thus
the witness terms inside `MirSemantics.lean` do not even inhabit a valid model
of `TCBItem.rustcLowering`. -/
def OpaqueWitnessTargetLang : Language where
  Prog := Unit
  Query := ExecQuery MirState
  Obs := ExecOut Unit Nat → Prop
  sem _ _ := Partial.ub

def OpaqueWitnessRustcCompiler : Compiler MirLang OpaqueWitnessTargetLang :=
  Compiler.ofTotal (fun _ => ()) (fun b => b)

theorem hidden_opaque_witness_soundOn_false (body : MirBody) :
    Compiler.SoundOn OpaqueWitnessRustcCompiler body → False := by
  rintro ⟨p_tgt, _, _, hRef⟩
  let s₀ : MirState := { tySizes := fun _ => 8 }
  let q₀ : ExecQuery MirState := { init := s₀, steps := 0 }
  have hMirDef : (MirSem body q₀).defined := step0_query_mirSem_defined body s₀
  obtain ⟨hTgtDef, _⟩ := hRef q₀ hMirDef
  exact hTgtDef

-- Now we show how `CrateTheorem` (`Trusted/MirSemantics.lean:839-865`) is
-- vacuously provable for `.alwaysUbAtStep1` whenever `hTcb` contains a single
-- inconsistent assumption.

inductive TCBItem where
  | rustcLowering (fnName : String) (body : MirBody)

def defaultTrustPolicy : TrustPolicy TCBItem where
  isAllowed
    | .rustcLowering _ _ => True

structure CapturedFn (L_src : Language) where
  name : String
  prog : L_src.Prog
  pre : L_src.Query → Prop
  specs : List (L_src.Behavior → Prop)

structure Crate where
  functions : List (CapturedFn MirLang)
  tcb : List TCBItem

def CrateTheoremFor {L_tgt : Language} (C : Compiler MirLang L_tgt)
    [TrustedAssumption TCBItem] (c : Crate) : Prop :=
  AllHold (c.functions.map fun f =>
    VerificationResultOn C defaultTrustPolicy c.tcb f.prog f.pre f.specs)

/-- A crate containing `.alwaysUbAtStep1` (which unconditionally triggers UB at
step 1) and claiming the contradictory specification
`MirLang.Spec (fun _ _ => False)`. -/
def alwaysUbCrate : Crate where
  functions :=
    [ { name := "always_ub"
        prog := .alwaysUbAtStep1
        pre := fun _ => True
        specs := [MirLang.Spec (fun _ _ => False)] } ]
  tcb := [.rustcLowering "always_ub" .pmeSizeEqReturnZero]

instance instTrustedAssumptionPmeRejecting : TrustedAssumption TCBItem where
  meaning
    | .rustcLowering _ body => Compiler.SoundOn PmeRejectingCompiler body

/-- **Theorem 2.5 (`contradictory_hTcb_proves_ub_crate`):**
Even though `alwaysUbCrate` executes `.alwaysUbAtStep1` (which fails at step 1)
and asserts `MirLang.Spec (fun _ _ => False)`, its `CrateTheorem` is provable
with **zero kernel axioms** whenever `hTcb` includes a single boundary-query
contradiction! -/
theorem contradictory_hTcb_proves_ub_crate :
    CrateTheoremFor PmeRejectingCompiler alwaysUbCrate := by
  refine ⟨⟨⟨trivial, trivial⟩, ?_⟩, trivial⟩
  intro hTcb
  exact False.elim (pme_rejected_target_undefined_soundOn_false hTcb.1)

-- ============================================================================
-- Section 3: Universal `TCBModel` + Realizability Witness Architecture
-- ============================================================================

/-- Explicit signature packaging the uninterpreted target/compiler symbols that
were previously declared as top-level `opaque` constants in
`Trusted/MirSemantics.lean:685-723`. -/
structure TCBModel where
  TargetProg : Type
  rustc : MirBody → TargetProg
  TargetSem : TargetProg → ExecQuery MirState → Partial (ExecOut Unit Nat → Prop)
  π_c : MirLang.Behavior → Behavior (ExecQuery MirState) (ExecOut Unit Nat → Prop)

/-- The target language induced by a `TCBModel`. -/
def TCBModel.targetLang (M : TCBModel) : Language where
  Prog := M.TargetProg
  Query := ExecQuery MirState
  Obs := ExecOut Unit Nat → Prop
  sem := M.TargetSem

/-- The compiler bundle induced by a `TCBModel`. -/
def TCBModel.compiler (M : TCBModel) : Compiler MirLang M.targetLang :=
  Compiler.ofTotal M.rustc M.π_c

/-- Model-parameterized meaning of a `TCBItem`. -/
def TCBItem.meaningIn (M : TCBModel) : TCBItem → Prop
  | .rustcLowering _ body => Compiler.SoundOn M.compiler body

abbrev instTrustedAssumptionIn (M : TCBModel) : TrustedAssumption TCBItem where
  meaning := TCBItem.meaningIn M

/-- Crate verification theorem parameterized by a specific `M : TCBModel`. -/
def CrateTheoremIn (M : TCBModel) (c : Crate) : Prop :=
  @CrateTheoremFor M.targetLang M.compiler (instTrustedAssumptionIn M) c

/-- **Universal Crate Theorem:** quantifies over all models `M : TCBModel`. -/
def CrateTheoremUniversal (c : Crate) : Prop :=
  ∀ M : TCBModel, CrateTheoremIn M c

/-- Constructive reference model in `theory/` (`TargetProg := MirBody`,
`rustc := id`, `TargetSem := MirSem`, `π_c := id`). -/
def refTCBModel : TCBModel where
  TargetProg := MirBody
  rustc := id
  TargetSem := MirSem
  π_c := id

/-- Every `MirBody` satisfies `Compiler.SoundOn refTCBModel.compiler body`
constructively with zero axioms. -/
theorem refTCBModel_soundOn (body : MirBody) :
    Compiler.SoundOn refTCBModel.compiler body := by
  refine ⟨body, rfl, ?_, ?_⟩
  · intro b₁ b₂ hle q hDef
    exact hle q hDef
  · intro q hDef
    exact ⟨hDef, fun out hout => hout⟩

/-- **Theorem 3.1 (`refTCBModel_realizes_tcb`):**
For any crate `c`, `refTCBModel` constructively satisfies every `TCBItem` in
`c.tcb` with zero axioms. -/
theorem refTCBModel_realizes_tcb (tcb : List TCBItem) :
    AllHold (tcb.map (TCBItem.meaningIn refTCBModel)) := by
  induction tcb with
  | nil => exact trivial
  | cons item rest ih =>
    cases item with
    | rustcLowering fnName body =>
      exact ⟨refTCBModel_soundOn body, ih⟩

/-- Existential realizability witness for any crate's TCB list. -/
theorem tcbModel_realizable (c : Crate) :
    ∃ M : TCBModel, AllHold (c.tcb.map (TCBItem.meaningIn M)) :=
  ⟨refTCBModel, refTCBModel_realizes_tcb c.tcb⟩

/-- **Theorem 3.2 (`relative_consistency_meta_theorem`):**
Any proposition `P` implied by `AllHold (c.tcb.map (TCBItem.meaningIn M))` across
all models `M : TCBModel` holds outright in Lean's base logic. In particular,
setting `P = False` proves that universal `hTcb` hypotheses can never be
contradictory (`¬ (∀ M, AllHold ... → False)`). -/
theorem relative_consistency_meta_theorem (c : Crate) (P : Prop)
    (hUniv : ∀ M : TCBModel, AllHold (c.tcb.map (TCBItem.meaningIn M)) → P) :
    P :=
  hUniv refTCBModel (refTCBModel_realizes_tcb c.tcb)

theorem universal_hTcb_never_contradictory (c : Crate) :
    ¬ (∀ M : TCBModel, AllHold (c.tcb.map (TCBItem.meaningIn M)) → False) :=
  fun hUniv => relative_consistency_meta_theorem c False hUniv

/-- **Theorem 3.3 (`alwaysUbCrate_unprovable_under_universal_tcb`):**
Unlike Theorem 2.5 (where `alwaysUbCrate` was provable from a pointwise `hTcb`
contradiction), `CrateTheoremUniversal alwaysUbCrate` is **provably false** in
Lean's base logic because instantiating `M := refTCBModel` discharges `hTcb` and
exposes that `.alwaysUbAtStep1` reaches `.failed` at step 1! -/
theorem alwaysUbCrate_unprovable_under_universal_tcb :
    ¬ CrateTheoremUniversal alwaysUbCrate := by
  intro hUniv
  have hRef : CrateTheoremIn refTCBModel alwaysUbCrate := hUniv refTCBModel
  have hFn := hRef.1
  have hObligations := hFn.2 (refTCBModel_realizes_tcb alwaysUbCrate.tcb)
  have hWfVerified :
      Compiler.Verified refTCBModel.compiler .alwaysUbAtStep1
        (MirLang.WellFormedOn (fun _ => True)) := hObligations.1
  rcases hWfVerified with ⟨p_tgt, ⟨hEq, _, hRefines⟩, b_lift, hLiftRef, hWfLift⟩
  subst hEq
  let s₀ : MirState := { tySizes := fun _ => 8 }
  let q₁ : ExecQuery MirState := { init := s₀, steps := 1 }
  have hLiftDef : (b_lift q₁).defined := hWfLift q₁ trivial
  obtain ⟨hTgtDef, _⟩ := hLiftRef q₁ hLiftDef
  have hInit : initMirState .alwaysUbAtStep1 q₁.init := trivial
  have hReachFail :
      ReachesPrefix MirMachine .alwaysUbAtStep1 1 q₁.init [] .failed :=
    ReachesPrefix.stepFailed (evalMirBody.ubFail s₀)
  exact hTgtDef hInit [] .failed hReachFail rfl

-- ============================================================================
-- Section 4: `mir-to-x86` (`4f45f0a391a9`) Comparison & End-to-End Closure
-- ============================================================================

/-- Minimal slice of `X86Body` from `mir-to-x86:Trusted/X86Semantics.lean`. -/
inductive X86Body where
  | retZero
  | ud2Trap
  deriving DecidableEq

structure X86State where
  dummy : Unit

def initX86State (_ : X86Body) (_ : X86State) : Prop := True

inductive evalX86Body : X86Body → X86State → StepResult X86State Unit Nat → Prop where
  | retZeroStep (s : X86State) :
      evalX86Body .retZero s (.returned 0 [])
  | ud2Step (s : X86State) :
      evalX86Body .ud2Trap s .failed

def X86Machine : SmallStepMachine X86Body X86State Unit Nat where
  initState := initX86State
  step := evalX86Body

def X86Sem (body : X86Body) :
    Behavior (ExecQuery X86State) (ExecOut Unit Nat → Prop) :=
  BehaviorOf X86Machine body

def X86Lang : Language where
  Prog := X86Body
  Query := ExecQuery X86State
  Obs := ExecOut Unit Nat → Prop
  sem := X86Sem

/-- In `mir-to-x86:Trusted/X86Semantics.lean:716-742`, the exact same hidden
`opaque` witness pattern is repeated for `AssemblerCompiler`:
- `opaque assemble : X86Body → TargetArtifact := fun _ => { unit := () }`
- `opaque TargetSem : TargetArtifact → ... := fun _ _ => Partial.ub`
- `opaque π_asm : X86Lang.Behavior → TargetLang.Behavior := fun b => b` -/
def X86OpaqueWitnessTargetLang : Language where
  Prog := Unit
  Query := ExecQuery X86State
  Obs := ExecOut Unit Nat → Prop
  sem _ _ := Partial.ub

def X86OpaqueWitnessAssemblerCompiler :
    Compiler X86Lang X86OpaqueWitnessTargetLang :=
  Compiler.ofTotal (fun _ => ()) (fun b => b)

/-- **Theorem 4.1 (`x86_hidden_opaque_witness_soundOn_false`):**
Just as in `MirSemantics.lean`, the underlying witness terms in
`mir-to-x86:Trusted/X86Semantics.lean:716-742` are contradictory with
`AssemblerCompiler.SoundOn body` for every `body : X86Body` at `steps = 0`. -/
theorem x86_hidden_opaque_witness_soundOn_false (body : X86Body) :
    Compiler.SoundOn X86OpaqueWitnessAssemblerCompiler body → False := by
  rintro ⟨p_tgt, _, _, hRef⟩
  let q₀ : ExecQuery X86State := { init := { dummy := () }, steps := 0 }
  have hX86Def : (X86Sem body q₀).defined := by
    intro _ tr out hReach
    cases hReach
    intro hEq
    cases hEq
  obtain ⟨hTgtDef, _⟩ := hRef q₀ hX86Def
  exact hTgtDef

/-- Verified MIR-to-x86 stage-0 compiler in `theory/` (analogous to
`Anneal.compileStage0` in `mir-to-x86:theory/Anneal/Compiler/NaiveCodegen.lean`). -/
def compileStage0 : MirBody → X86Body
  | .pmeSizeEqReturnZero => .retZero
  | .alwaysUbAtStep1 => .ud2Trap

/-- In `mir-to-x86:Trusted/X86Semantics.lean:865-895`, `Trusted.Crate` stores
`CapturedFn` over `X86Lang` (`prog : X86Body`), NOT `MirBody`! As a result,
`X86CrateTheorem` never checks that the `X86Body` in `Mir.crate` equals
`compileStage0 mirBody` for the source Rust function's `MirBody`. -/
structure X86Crate where
  functions : List (CapturedFn X86Lang)

/-- **Theorem 4.2 (`mir_to_x86_unverified_capture_gap`):**
Suppose the source Rust function is `.alwaysUbAtStep1` (whose verified compilation
`compileStage0 .alwaysUbAtStep1 = .ud2Trap` traps at step 1), OR suppose
`.anneal/Prog.s` contains `ud2`, while unverified Rust code in `Mir.lean` emits
`prog := .retZero`. Because `mir-to-x86` does not bind `MirBody` or
`compileStage0` inside `Trusted.CrateTheorem`, `.retZero` is accepted as
well-formed even though `compileStage0 .alwaysUbAtStep1 ≠ .retZero`! -/
theorem mir_to_x86_unverified_capture_gap :
    compileStage0 .alwaysUbAtStep1 ≠ .retZero ∧
    X86Lang.WellFormedOn (fun _ => True) (X86Sem .retZero) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨init, steps⟩ _ _ tr out hReach
  cases hReach with
  | zero => intro h; cases h
  | stepRunning hStep _ => cases hStep
  | stepReturned hStep => cases hStep; intro h; cases h
  | stepDiverged hStep => cases hStep
  | stepFailed hStep => cases hStep

/-- End-to-end verified compilation binding (`VerifiedCapturedFn`): pairs the
captured `MirBody` with the emitted `X86Body` and requires `CrateTheorem` to
verify `Compiler.Compiles` between `progMir` and `progX86` (with `tcb = []` for
MIR-to-x86 lowering). -/
structure VerifiedCapturedFn where
  name : String
  progMir : MirBody
  progX86 : X86Body
  pre : ExecQuery MirState → Prop

/-- Stage-0 compiler bundle from `MirLang` to `X86Lang`. -/
def Stage0Compiler : Compiler MirLang X86Lang where
  compile p_mir p_x86 := p_x86 = compileStage0 p_mir
  π b q :=
    let qMir : ExecQuery MirState :=
      { init := { tySizes := fun _ => 8 }, steps := q.steps }
    b qMir

/-- **Theorem 4.3 (`verified_pipeline_rejects_capture_mismatch`):**
When `CrateTheorem` checks `Stage0Compiler.Compiles fn.progMir fn.progX86`, any
mismatch between the captured `MirBody` (`.alwaysUbAtStep1`) and the emitted
`X86Body` (`.retZero`) is immediately rejected (`¬ Stage0Compiler.Compiles ...`). -/
theorem verified_pipeline_rejects_capture_mismatch :
    ¬ Stage0Compiler.Compiles .alwaysUbAtStep1 .retZero := by
  rintro ⟨hCompile, _, _⟩
  cases hCompile

#print axioms pme_rejected_target_undefined_soundOn_false
#print axioms hidden_opaque_witness_soundOn_false
#print axioms contradictory_hTcb_proves_ub_crate
#print axioms refTCBModel_realizes_tcb
#print axioms relative_consistency_meta_theorem
#print axioms universal_hTcb_never_contradictory
#print axioms alwaysUbCrate_unprovable_under_universal_tcb
#print axioms x86_hidden_opaque_witness_soundOn_false
#print axioms mir_to_x86_unverified_capture_gap
#print axioms verified_pipeline_rejects_capture_mismatch

end Anneal.TcbAuditProbes
