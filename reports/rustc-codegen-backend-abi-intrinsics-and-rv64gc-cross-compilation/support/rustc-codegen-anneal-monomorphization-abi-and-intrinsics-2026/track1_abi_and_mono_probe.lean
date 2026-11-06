-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra

/-!
# Track 1 Mechanization Probe: `cg_clif`-Style Direct-MIR ABI & Shim Lowering

This standalone Lean 4.34.1 module mechanizes the semantic interface between
`MirPhase::Runtime(RuntimePhase::PostCleanup)` and a direct-MIR codegen backend
modeled on `rustc_codegen_cranelift` (`cg_clif`), embedded directly inside
Anneal's Layer 1A (`Trusted.Refinement`) and Layer 1B (`Trusted.StepResult`)
verification framework.

## Mechanized Components

1. **Anneal Layer 1A & 1B Core (`Trusted` & `Anneal` namespaces):**
   Exact embedding of `Preorder`, `Partial`, `Language`, `Compiles`, `Compiler`,
   `Compiler.SoundOn`, `Compiler.Verified`, `VerificationResultOn`,
   `VerificationResult`, `StepResult`, `PrefixOutcome`, `SmallStepMachine`, and
   `BehaviorOf`.
2. **`cg_clif` Value & Place Representation (`CValue` and `CPlace`):**
   Models `rustc_codegen_cranelift::value_and_place::{CValue, CPlace}`
   (`ByRef`, `ByVal`, `ByValPair`, `Var`, `VarPair`, `Addr`) and proves the
   round-trip adequacy theorem `cplace_write_read_roundtrip`.
3. **`FnAbi` and `PassMode` Call/Return Marshaling (`PassMode`, `FnAbi`):**
   Models `rustc_target::callconv::{FnAbi, PassMode}` (`Ignore`, `Direct`,
   `Pair`, `Cast`, `Indirect`) together with:
   - Caller-side argument marshaling (`adjust_arg_for_abi` in
     `compiler/rustc_codegen_cranelift/src/abi/pass_mode.rs#L255-L286`), which
     allocates a fresh scratch stack slot and copies `PassMode::Indirect`
     arguments whenever the MIR operand is not an owning `Operand::Move`
     (`!is_owned`) and `ArgAttribute::ReadOnly` is absent.
   - Callee-side prelude binding (`codegen_fn_prelude` in
     `compiler/rustc_codegen_cranelift/src/abi/mod.rs#L347-L365`), which aliases
     the callee's MIR parameter local directly to the pointer passed by
     `PassMode::Indirect` without copying to a second stack slot.
   - Return-value marshaling (`codegen_return` in
     `compiler/rustc_codegen_cranelift/src/abi/returning.rs#L10-L128`),
     covering register return modes (`Ignore`, `Direct`, `Pair`, `Cast`) and
     caller-allocated `StructReturn` (`sret`) pointer passing (`Indirect`).
4. **Positive Refinement & End-to-End Verification Theorems:**
   - `abi_call_marshaling_refines`: For all argument and return `PassMode`s,
     `AbiCallLang` with the sound caller-copy rule (`copyOnNonMove = true`,
     `readOnly = false`) refines (`Compiles`) Post-Cleanup MIR call semantics
     (`MirCallLang`), even when the callee mutates its by-value parameter local
     in-place.
   - `abi_compiler_soundOn` and `caller_callee_mutate_verified`: End-to-end
     `VerificationResultOn` proof for a concrete program where the caller passes
     a local via `Operand.copy` (`PassMode.indirect false`), the callee mutates
     its parameter in-place and returns the mutated value, and the caller
     subsequently reads its unmodified original local.
   - `empty_drop_shim_refines` and `rust_call_spread_arg_refines`: Refinement
     proofs for `InstanceKind::DropGlue` no-op lowering (`abi/mod.rs#L492-L498`)
     and `ExternAbi::RustCall` tuple-argument spreading (`spread_arg` in
     `abi/mod.rs#L298-L317`, `#L530-L553`).
5. **Negative Soundness Canaries (`deduced_param_attrs` & Missing Scratch Copy):**
   - `buggy_indirect_without_caller_copy_unsound`: Proves `¬ Compiles` when a
     backend omits the caller-side scratch copy for a non-`Move`
     `PassMode::Indirect` argument.
   - `deduced_readonly_phase_mismatch_unsound`: Proves `¬ Compiles` when
     `tcx.deduced_param_attrs` deduces `ArgAttribute::ReadOnly` from
     `optimized_mir` (after dead-store elimination removes a parameter write)
     while codegen lowers `mir_drops_elaborated_and_const_checked` (where the
     dead store to the parameter still executes).
-/

namespace Trusted

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces `A → B` with a
    refinement preorder whenever `B` is a `Preorder`. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Partially defined value of type `B`, constructively representing
    $B \cup \{\mathsf{UB}\}$. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- The undefined element ($\mathsf{UB}$) of `Partial B` (`defined := False`). -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Refinement preorder on `Partial B`. -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Order-preserving mapping between behavior preorders. -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- Canonical domain of query-indexed partial behaviors. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A language bundling `Prog`, `Query`, `Out`, and `sem`. -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

/-- The behavior domain of a `Language`. -/
abbrev Language.Behavior (L : Language) : Type :=
  Trusted.Behavior L.Query L.Out

/-- Query-indexed specification on `L` with precondition `pre` and postcondition
    `post`. -/
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

/-- Unconditional specification on `L`. -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional well-formedness specification on `L`. -/
abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness specification on `L`. -/
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Compilation (refinement) pass from `L_src` to `L_tgt`. -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- A compiler lowering programs from `L_src` to `L_tgt` with behavior mapping
    `π`. -/
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

/-- Soundness of compiler `C` on an individual source program `s`. -/
def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)

/-- End-to-end verification obligation for source program `s` and specification
    `spec` under compiler `C`. -/
def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

/-- An assumption recorded in a verification unit's Trusted Computing Base. -/
class TrustedAssumption (A : Type) where
  meaning : A → Prop

/-- A policy governing which trusted assumptions of type `A` are permitted. -/
structure TrustPolicy (A : Type) [TrustedAssumption A] where
  isAllowed : A → Prop

/-- Conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- Top-level verification envelope with precondition `pre`. -/
def VerificationResultOn
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (pre : L_src.Query → Prop)
    (specs : List L_src.Behavior) : Prop :=
  AllHold (assumptions.map policy.isAllowed) ∧
  (AllHold (assumptions.map TrustedAssumption.meaning) →
    AllHold ((L_src.WellFormedOn pre :: specs).map (C.Verified prog)))

/-- Top-level verification envelope with unconditional baseline safety. -/
abbrev VerificationResult
    {L_src L_tgt : Language}
    {A : Type} [TrustedAssumption A]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy A)
    (assumptions : List A)
    (prog : L_src.Prog)
    (specs : List L_src.Behavior := []) : Prop :=
  VerificationResultOn C policy assumptions prog (fun _ => True) specs

/-- Quantifier polarity for nondeterministic choices in a small-step
    semantics. -/
inductive ChoiceKind where
  | demonic
  | angelic

/-- Distinguishes normal return from panic/unwind completion. -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Distinguishes language-level Undefined Behavior (`ub`) from explicit
    contract violations (`contractViolation`). -/
inductive FailureKind where
  | ub
  | contractViolation

/-- Outcome of a single transition step in a small-step interaction tree. -/
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

/-- Outcome recorded at the end of a finite execution prefix. -/
inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

/-- A prefix outcome is safe when it neither fails nor gets stuck. -/
def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

/-- Input query to a finite-prefix small-step execution. -/
structure ExecQuery (State : Type) where
  init : State
  steps : Nat

/-- Observable output of a finite-prefix small-step execution. -/
structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

/-- Small-step operational semantics parameterized by `Prog`, `State`, `Obs`,
    and `Val`. -/
structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

/-- Inductive reachability of a finite execution prefix. -/
inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State) (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p init (n + 1) s [] .stuck

/-- Induced query-indexed partial behavior of program `p` in machine `M`. -/
def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M p q.init q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }

/-- Package a `SmallStepMachine` as a Layer 1A `Language`. -/
def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

/-- Minimal runtime value domain covering unit ZSTs, scalars (`usize`), scalar
    pairs (`(usize, usize)`), and aggregate structures stored in memory. -/
inductive MirVal where
  | unit
  | usize (n : Nat)
  | pair (a b : Nat)
  deriving DecidableEq

/-- Index of a MIR local (`_0`, `_1`, ...). -/
structure LocalId where
  index : Nat
  deriving DecidableEq

/-- MIR operand (`Copy`, `Move`, `Constant`).

    Corresponds to `rustc_middle::mir::Operand`
    (`compiler/rustc_middle/src/mir/syntax.rs#L1282-L1310`). -/
inductive Operand where
  | copy (src : LocalId)
  | move (src : LocalId)
  | constVal (val : MirVal)

end Trusted

namespace Anneal

open Trusted

/-- Identity mapping on any behavior domain is monotone. -/
theorem monotone_id {B : Type u} [Preorder B] : Monotone (fun b : B => b) :=
  fun _ _ h => h

/-- Every conditional specification `L.SpecOn pre post` refines
    `L.WellFormedOn pre`. -/
theorem specOn_le_wellFormedOn {L : Language}
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn pre post ≤ L.WellFormedOn pre :=
  fun _ hpre => ⟨hpre, fun _ _ => True.intro⟩

/-- Every unconditional specification `L.Spec post` refines `L.WellFormed`. -/
theorem spec_le_wellFormed {L : Language} (post : L.Query → L.Out → Prop) :
    L.Spec post ≤ L.WellFormed :=
  specOn_le_wellFormedOn (fun _ => True) post

/-- Discharge `C.Verified s spec` from `C.SoundOn s` and `L_src.sem s ≤ spec`. -/
theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, h_comp.2, Preorder.le_trans h_comp.2 (h_comp.1 h_src)⟩

/-- Monotonicity of `Compiler.Verified` in the specification argument. -/
theorem Compiler.Verified.mono
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec₁ spec₂ : L_src.Behavior}
    (h_ver : C.Verified s spec₁)
    (h_le : spec₁ ≤ spec₂)
    (h_mono : Monotone C.π) :
    C.Verified s spec₂ :=
  ⟨Preorder.le_trans h_ver.1 h_le,
   h_ver.2.1,
   Preorder.le_trans h_ver.2.2 (h_mono h_le)⟩

/-- Combine `C.Verified s spec` with `spec ≤ L_src.WellFormedOn pre` to discharge
    `AllHold` in `VerificationResultOn`. -/
theorem Compiler.Verified.with_wellFormedOn
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {pre : L_src.Query → Prop} {spec : L_src.Behavior}
    (h_ver : C.Verified s spec)
    (h_wf : spec ≤ L_src.WellFormedOn pre)
    (h_mono : Monotone C.π) :
    AllHold ((L_src.WellFormedOn pre :: [spec]).map (C.Verified s)) :=
  ⟨Compiler.Verified.mono h_ver h_wf h_mono, h_ver, True.intro⟩

/-!
## 1. `cg_clif` Value and Place Representation (`CValue` and `CPlace`)

In `rustc_codegen_cranelift::value_and_place`
(`compiler/rustc_codegen_cranelift/src/value_and_place.rs#L58-L433`), every
rvalue or operand is lowered to a `CValue` (`ByRef`, `ByVal`, `ByValPair`) and
every MIR `Place` is lowered to a `CPlace` (`Var`, `VarPair`, `Addr`).
-/

/-- Lowered value representation corresponding to `CValueInner` in
    `compiler/rustc_codegen_cranelift/src/value_and_place.rs#L65-L69`. -/
inductive CValue where
  /-- Memory-backed value at address `addr` (also used for ZSTs via a dangling
      aligned pointer). -/
  | byRef (addr : Nat)
  /-- Single SSA register value (`BackendRepr::Scalar`). -/
  | byVal (v : MirVal)
  /-- Two SSA register values (`BackendRepr::ScalarPair`). -/
  | byValPair (a b : Nat)
  deriving DecidableEq

/-- Lowered place representation corresponding to `CPlaceInner` in
    `compiler/rustc_codegen_cranelift/src/value_and_place.rs#L428-L433`. -/
inductive CPlace where
  /-- Single SSA register local (`CPlaceInner::Var`). -/
  | var (reg : Nat)
  /-- Two SSA register locals (`CPlaceInner::VarPair`). -/
  | varPair (regA regB : Nat)
  /-- Stack slot or pointer-backed memory address (`CPlaceInner::Addr`). -/
  | addr (loc : Nat)
  deriving DecidableEq

/-- Combined SSA register file and stack/memory store used during `CValue` /
    `CPlace` lowering. -/
structure LoweringStore where
  regs : Nat → Option MirVal
  mem : Nat → Option MirVal

/-- Update an SSA register in `LoweringStore`. -/
def LoweringStore.writeReg (st : LoweringStore) (r : Nat) (v : Option MirVal) :
    LoweringStore :=
  { st with regs := fun i => if i == r then v else st.regs i }

/-- Update a memory slot in `LoweringStore`. -/
def LoweringStore.writeMem (st : LoweringStore) (loc : Nat) (v : Option MirVal) :
    LoweringStore :=
  { st with mem := fun i => if i == loc then v else st.mem i }

/-- Load a `MirVal` from a `CValue` in `st`
    (`CValue::load_scalar` / `CValue::load_scalar_pair` in
    `value_and_place.rs#L172-L216`). -/
def evalCValue (st : LoweringStore) (cv : CValue) : Option MirVal :=
  match cv with
  | .byRef addr => st.mem addr
  | .byVal v => some v
  | .byValPair a b => some (.pair a b)

/-- Load a `CValue` from a `CPlace` (`CPlace::to_cvalue` in
    `value_and_place.rs#L485-L515`). -/
def cplaceToCValue (st : LoweringStore) (cp : CPlace) : Option CValue :=
  match cp with
  | .var r =>
    match st.regs r with
    | some v => some (.byVal v)
    | none => none
  | .varPair rA rB =>
    match st.regs rA, st.regs rB with
    | some (.usize a), some (.usize b) => some (.byValPair a b)
    | _, _ => none
  | .addr loc => some (.byRef loc)

/-- Write a `CValue` into a `CPlace` (`CPlace::write_cvalue` in
    `value_and_place.rs#L517-L659`). -/
def cplaceWriteCValue (st : LoweringStore) (cp : CPlace) (cv : CValue) :
    Option LoweringStore :=
  match evalCValue st cv with
  | none => none
  | some v =>
    match cp with
    | .var r => some (st.writeReg r (some v))
    | .varPair rA rB =>
      match v with
      | .pair a b =>
        if rA == rB then none
        else some ((st.writeReg rA (some (.usize a))).writeReg rB (some (.usize b)))
      | _ => none
    | .addr loc => some (st.writeMem loc (some v))

/-- Round-trip adequacy of `cplaceWriteCValue` followed by `cplaceToCValue` and
    `evalCValue`: writing any well-typed `CValue` into a `CPlace` and reading it
    back yields the exact `MirVal` denoted by the `CValue`. -/
theorem cplace_write_read_roundtrip
    (st st' : LoweringStore) (cp : CPlace) (cv : CValue) (v : MirVal)
    (heval : evalCValue st cv = some v)
    (hwrite : cplaceWriteCValue st cp cv = some st') :
    ∃ cv', cplaceToCValue st' cp = some cv' ∧ evalCValue st' cv' = some v := by
  unfold cplaceWriteCValue at hwrite
  rw [heval] at hwrite
  cases cp with
  | var r =>
    dsimp only at hwrite
    injection hwrite with hst'
    subst hst'
    refine ⟨.byVal v, ?_, rfl⟩
    simp [cplaceToCValue, LoweringStore.writeReg]
  | varPair rA rB =>
    cases v with
    | unit => cases hwrite
    | usize n => cases hwrite
    | pair a b =>
      dsimp only at hwrite
      cases hEq : (rA == rB) with
      | false =>
        rw [hEq] at hwrite
        change some ((st.writeReg rA (some (MirVal.usize a))).writeReg rB (some (MirVal.usize b))) =
          some st' at hwrite
        injection hwrite with hst'
        subst hst'
        refine ⟨.byValPair a b, ?_, rfl⟩
        unfold cplaceToCValue LoweringStore.writeReg
        simp [hEq]
      | true =>
        rw [hEq] at hwrite
        cases hwrite
  | addr loc =>
    dsimp only at hwrite
    injection hwrite with hst'
    subst hst'
    refine ⟨.byRef loc, rfl, ?_⟩
    simp [evalCValue, LoweringStore.writeMem]

/-- info: 'Anneal.cplace_write_read_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cplace_write_read_roundtrip

/-!
## 2. `FnAbi` and `PassMode` Call/Return Marshaling

In `rustc_target::callconv::{FnAbi, ArgAbi, PassMode}` and
`rustc_codegen_cranelift::abi`:
- `PassMode::Ignore`: ZSTs are not passed across the call boundary
  (`abi/pass_mode.rs#L179`).
- `PassMode::Direct`: Scalars are passed in a single SSA register
  (`abi/pass_mode.rs#L180`).
- `PassMode::Pair`: Two-element scalar pairs are passed in two SSA registers
  (`abi/pass_mode.rs#L181-L185`).
- `PassMode::Cast`: Small aggregates are bit-cast to an integer/register carrier
  (`abi/pass_mode.rs#L186-L194`).
- `PassMode::Indirect`: Memory aggregates are passed by pointer to a stack
  allocation (`abi/pass_mode.rs#L195-L197`).
  - In `adjust_arg_for_abi` (`abi/pass_mode.rs#L270-L284`), if the caller
    argument comes from `Operand::Move` (`is_owned = true`), the caller passes
    the existing stack slot pointer (`arg.force_stack(fx)`). If it comes from
    `Operand::Copy` (`is_owned = false`), the caller allocates a fresh stack
    slot (`CPlace::new_stack_slot`), copies the argument value into it, and
    passes the scratch pointer—unless `ArgAttribute::ReadOnly` causes the
    backend (`rustc_codegen_ssa/src/mir/block.rs#L1288-L1305`) to elide the
    caller-side copy.
  - In `codegen_fn_prelude` (`abi/mod.rs#L347-L365`), the callee aliases its
    MIR parameter local `_1` directly to the incoming `PassMode::Indirect`
    pointer (`CPlace::for_ptr(addr, layout)`), so any in-place mutation of `_1`
    in the callee body mutates the pointed-to memory block directly.
-/

/-- Argument and return passing modes (`rustc_target::callconv::PassMode`). -/
inductive PassMode where
  | ignore
  | direct
  | pair
  | cast
  | indirect (readOnly : Bool)
  deriving DecidableEq

/-- Function ABI signature for a 1-argument, 1-return call boundary. -/
structure FnAbi where
  argMode : PassMode
  retMode : PassMode
  deriving DecidableEq

/-- Action performed by a single-parameter callee body on its parameter `_1`:
    - `readParam`: returns `_1` without mutating `_1`.
    - `incParamInPlace delta`: mutates `_1` in-place (adding `delta` to its
      `usize` or `pair` payload, as in `fn bump(mut x: T) -> T { x.0 += delta;
      x }`) and returns the updated `_1`.
    - `deadStoreThenReturnConst delta retVal`: writes to `_1` in-place and then
      overwrites `_0` with `retVal` (modeling a store to `_1` that is dead in
      the callee's return value, so `DeadStoreElimination` at `-Zmir-opt-level >=
      1` removes the write to `_1` and `deduced_param_attrs` marks `_1`
      `ReadOnly`, whereas in `PostCleanup` MIR the write to `_1` still
      executes!). -/
inductive CalleeAction where
  | readParam
  | incParamInPlace (delta : Nat)
  | deadStoreThenReturnConst (delta : Nat) (retVal : MirVal)
  deriving DecidableEq

/-- Apply an increment `delta` to a `MirVal`. -/
def bumpVal (v : MirVal) (delta : Nat) : MirVal :=
  match v with
  | .unit => .unit
  | .usize n => .usize (n + delta)
  | .pair a b => .pair (a + delta) b

/-- Evaluate `CalleeAction` on parameter value `v`, returning
    `(mutatedParamVal, returnVal)`. -/
def evalCalleeAction (act : CalleeAction) (v : MirVal) : MirVal × MirVal :=
  match act with
  | .readParam => (v, v)
  | .incParamInPlace delta =>
    let v' := bumpVal v delta
    (v', v')
  | .deadStoreThenReturnConst delta retVal =>
    (bumpVal v delta, retVal)

/-- Program combining a caller call-site (`argOp`, `callee`, `abi`) with a
    post-call observation that returns both the call's return place (`_2`) and
    the caller's post-call value of local `_1` (when `_1` was copied rather than
    moved). -/
structure CallProg where
  argOp : Operand
  callee : CalleeAction
  abi : FnAbi
  readCallerLocal1AfterCall : Bool

/-- Execution state of a caller/callee call boundary:
    - `pc = 0`: before the call terminator executes.
    - `pc = 1`: after the call terminator has written its result and updated
      caller locals/stack slots, ready to return the final observable `MirVal`.
    - `slot1`: caller's stack/local slot for `_1` (at stack address `1`).
    - `slot2`: caller's stack/local slot for call destination `_2` (at stack
      address `2`).
    - `scratchSlot`: caller's scratch stack slot for `PassMode.indirect` copy
      marshaling (at stack address `3`). -/
structure CallState where
  pc : Nat
  slot1 : Option MirVal
  slot2 : Option MirVal
  scratchSlot : Option MirVal

/-- Compatibility of an initial value `v` with a `PassMode` (`PassMode.ignore`
    is only assigned to unit ZSTs; `PassMode.pair` is only assigned to pairs). -/
def valMatchesPassMode (v : MirVal) (mode : PassMode) : Prop :=
  match mode with
  | .ignore => v = .unit
  | .pair => ∃ a b, v = .pair a b
  | .direct | .cast | .indirect _ => True

/-- Entry state predicate for `CallProg`: execution starts at `pc = 0` with
    `slot1` initialized to a value compatible with `prog.abi.argMode` and
    `prog.callee`'s return value compatible with `prog.abi.retMode`. -/
def initCallState (prog : CallProg) (s : CallState) : Prop :=
  s.pc = 0 ∧
  s.slot2 = none ∧
  s.scratchSlot = none ∧
  ∃ v1, s.slot1 = some v1 ∧
    valMatchesPassMode v1 prog.abi.argMode ∧
    valMatchesPassMode (evalCalleeAction prog.callee v1).2 prog.abi.retMode

/-- Source `Runtime(PostCleanup)` MIR call semantics (`evalMirCallStep`):
    In Post-Cleanup MIR (`rustc_middle::mir::syntax::TerminatorKind::Call`),
    evaluating `prog.argOp`:
    - When `prog.argOp = .copy ⟨1⟩`, reads `v1` from `s.slot1` and leaves
      `s.slot1 = some v1` untouched while the callee executes on its own fresh
      parameter local `_1`. Even if `prog.callee` mutates its parameter `_1`
      in-place, the caller's `s.slot1` remains `some v1`!
    - When `prog.argOp = .move ⟨1⟩`, reads `v1` from `s.slot1` and deinitializes
      `s.slot1 := none`.
    - At `pc = 1`, if `prog.readCallerLocal1AfterCall` is `true`, the caller
      reads both `s.slot1` (expecting `.usize a`) and `s.slot2` (expecting
      `.usize b`) and returns `.pair a b`; otherwise it returns `s.slot2`. -/
def evalMirCallStep (prog : CallProg) (s : CallState) :
    StepResult CallState Unit MirVal :=
  match s.pc with
  | 0 =>
    match prog.argOp with
    | .copy ⟨1⟩ =>
      match s.slot1 with
      | none => .failed .ub
      | some v1 =>
        .step () { s with
          pc := 1
          slot1 := some v1
          slot2 := some (evalCalleeAction prog.callee v1).2
        }
    | .move ⟨1⟩ =>
      match s.slot1 with
      | none => .failed .ub
      | some v1 =>
        .step () { s with
          pc := 1
          slot1 := none
          slot2 := some (evalCalleeAction prog.callee v1).2
        }
    | .constVal v1 =>
      .step () { s with
        pc := 1
        slot2 := some (evalCalleeAction prog.callee v1).2
      }
    | _ => .failed .ub
  | 1 =>
    if prog.readCallerLocal1AfterCall then
      match s.slot1, s.slot2 with
      | some (.usize a), some (.usize b) => .terminated (.normal (MirVal.pair a b))
      | _, _ => .failed .ub
    else
      match s.slot2 with
      | some v => .terminated (.normal v)
      | none => .failed .ub
  | _ => .failed .ub

/-- Marshal a `MirVal` across an ABI register/cast boundary (`Ignore`, `Direct`,
    `Pair`, `Cast`). -/
def marshalByVal (mode : PassMode) (v : MirVal) : Option MirVal :=
  match mode with
  | .ignore => some .unit
  | .direct => some v
  | .pair =>
    match v with
    | .pair a b => some (.pair a b)
    | _ => none
  | .cast => some v
  | .indirect _ => some v

/-- Target ABI-lowered call semantics (`evalAbiCallStep`), parameterized by
    `copyOnNonMove : Bool`:
    - Models `cg_clif`'s `adjust_arg_for_abi` (`abi/pass_mode.rs#L270-L284`)
      and `codegen_fn_prelude` (`abi/mod.rs#L347-L365`).
    - Under `PassMode.indirect readOnly`:
      - If `prog.argOp = .move ⟨1⟩` (`isOwned = true`), the caller passes
        `slot1`'s address directly (`arg.force_stack(fx)`), deinitializing caller
        ownership of `slot1`.
      - If `prog.argOp = .copy ⟨1⟩` (`isOwned = false`), then:
        - When `copyOnNonMove = true && !readOnly`, the caller copies `slot1`
          into `scratchSlot` and passes `scratchSlot`'s address to the callee;
          the callee's in-place mutation of `_1` writes to `scratchSlot`,
          preserving `slot1`!
        - When `copyOnNonMove = false || readOnly`, the caller elides the
          scratch copy and passes `slot1`'s address directly to the callee;
          the callee's in-place mutation of `_1` (`paramFinal`) overwrites
          `slot1` in-place! -/
def evalAbiCallStep (copyOnNonMove : Bool) (prog : CallProg) (s : CallState) :
    StepResult CallState Unit MirVal :=
  match s.pc with
  | 0 =>
    match prog.abi.argMode with
    | .indirect readOnly =>
      match prog.argOp with
      | .copy ⟨1⟩ =>
        match s.slot1 with
        | none => .failed .ub
        | some v1 =>
          let paramFinal := (evalCalleeAction prog.callee v1).1
          let retRaw := (evalCalleeAction prog.callee v1).2
          match marshalByVal prog.abi.retMode retRaw with
          | none => .failed .ub
          | some retVal =>
            if copyOnNonMove && !readOnly then
              .step () { s with
                pc := 1
                slot1 := some v1
                slot2 := some retVal
                scratchSlot := some paramFinal
              }
            else
              .step () { s with
                pc := 1
                slot1 := some paramFinal
                slot2 := some retVal
              }
      | .move ⟨1⟩ =>
        match s.slot1 with
        | none => .failed .ub
        | some v1 =>
          let paramFinal := (evalCalleeAction prog.callee v1).1
          let retRaw := (evalCalleeAction prog.callee v1).2
          match marshalByVal prog.abi.retMode retRaw with
          | none => .failed .ub
          | some retVal =>
            .step () { s with
              pc := 1
              slot1 := none
              slot2 := some retVal
              scratchSlot := some paramFinal
            }
      | .constVal v1 =>
        let paramFinal := (evalCalleeAction prog.callee v1).1
        let retRaw := (evalCalleeAction prog.callee v1).2
        match marshalByVal prog.abi.retMode retRaw with
        | none => .failed .ub
        | some retVal =>
          .step () { s with
            pc := 1
            slot2 := some retVal
            scratchSlot := some paramFinal
          }
      | _ => .failed .ub
    | mode =>
      match prog.argOp with
      | .copy ⟨1⟩ =>
        match s.slot1 with
        | none => .failed .ub
        | some v1 =>
          match marshalByVal mode v1 with
          | none => .failed .ub
          | some passedVal =>
            let retRaw := (evalCalleeAction prog.callee passedVal).2
            match marshalByVal prog.abi.retMode retRaw with
            | none => .failed .ub
            | some retVal =>
              .step () { s with
                pc := 1
                slot1 := some v1
                slot2 := some retVal
              }
      | .move ⟨1⟩ =>
        match s.slot1 with
        | none => .failed .ub
        | some v1 =>
          match marshalByVal mode v1 with
          | none => .failed .ub
          | some passedVal =>
            let retRaw := (evalCalleeAction prog.callee passedVal).2
            match marshalByVal prog.abi.retMode retRaw with
            | none => .failed .ub
            | some retVal =>
              .step () { s with
                pc := 1
                slot1 := none
                slot2 := some retVal
              }
      | .constVal v1 =>
        match marshalByVal mode v1 with
        | none => .failed .ub
        | some passedVal =>
          let retRaw := (evalCalleeAction prog.callee passedVal).2
          match marshalByVal prog.abi.retMode retRaw with
          | none => .failed .ub
          | some retVal =>
            .step () { s with
              pc := 1
              slot2 := some retVal
            }
      | _ => .failed .ub
  | 1 =>
    if prog.readCallerLocal1AfterCall then
      match s.slot1, s.slot2 with
      | some (.usize a), some (.usize b) => .terminated (.normal (MirVal.pair a b))
      | _, _ => .failed .ub
    else
      match s.slot2 with
      | some v => .terminated (.normal v)
      | none => .failed .ub
  | _ => .failed .ub

/-- Small-step machine for Post-Cleanup MIR call semantics. -/
def MirCallMachine : SmallStepMachine CallProg CallState Unit MirVal where
  initState := initCallState
  step prog s r := r = evalMirCallStep prog s

/-- Small-step machine for ABI-lowered call semantics. -/
def AbiCallMachine (copyOnNonMove : Bool) :
    SmallStepMachine CallProg CallState Unit MirVal where
  initState := initCallState
  step prog s r := r = evalAbiCallStep copyOnNonMove prog s

/-- Language of Post-Cleanup MIR calls. -/
def MirCallLang : Language :=
  MirCallMachine.toLanguage

/-- Language of ABI-lowered calls (`copyOnNonMove = true`). -/
def AbiCallLang : Language :=
  (AbiCallMachine true).toLanguage

/-- Language of buggy ABI-lowered calls that omit the caller scratch copy on
    `Operand.copy` (`copyOnNonMove = false`). -/
def BuggyAbiCallLang : Language :=
  (AbiCallMachine false).toLanguage

/-- `marshalByVal` acts as the identity on every `MirVal` compatible with
    `mode`. -/
theorem marshalByVal_of_matches (v : MirVal) (mode : PassMode)
    (h : valMatchesPassMode v mode) :
    marshalByVal mode v = some v := by
  cases mode with
  | ignore =>
    subst h
    rfl
  | direct => rfl
  | pair =>
    cases h with
    | intro a ha =>
      cases ha with
      | intro b hv =>
        subst hv
        rfl
  | cast => rfl
  | indirect _ => rfl

/-- At `pc = 1`, `evalAbiCallStep` and `evalMirCallStep` depend only on `pc`,
    `slot1`, and `slot2` (ignoring `scratchSlot`). -/
theorem evalAbiCallStep_pc1_eq_mir (copyOnNonMove : Bool) (prog : CallProg)
    (s₁ s₂ : CallState)
    (hpc₁ : s₁.pc = 1) (hpc₂ : s₂.pc = 1)
    (hslot1 : s₁.slot1 = s₂.slot1) (hslot2 : s₁.slot2 = s₂.slot2) :
    evalAbiCallStep copyOnNonMove prog s₁ = evalMirCallStep prog s₂ := by
  cases s₁ with
  | mk pc1 a1 b1 c1 =>
    cases s₂ with
    | mk pc2 a2 b2 c2 =>
      simp only at hpc₁ hpc₂ hslot1 hslot2
      subst hpc₁ hpc₂ hslot1 hslot2
      rfl

/-- Any prefix reachable from a `pc = 1` state in `AbiCallMachine` is also
    reachable from a matching `pc = 1` state in `MirCallMachine`. -/
theorem reachesPrefix_pc1_abi_to_mir (copyOnNonMove : Bool) (prog : CallProg)
    (init : CallState) (fuel : Nat) (sAbi sMir : CallState)
    (tr : List Unit) (out : PrefixOutcome MirVal)
    (hpcAbi : sAbi.pc = 1) (hpcMir : sMir.pc = 1)
    (hslot1 : sAbi.slot1 = sMir.slot1) (hslot2 : sAbi.slot2 = sMir.slot2)
    (hreach : ReachesPrefix (AbiCallMachine copyOnNonMove) prog init fuel sAbi tr out) :
    ReachesPrefix MirCallMachine prog init fuel sMir tr out := by
  have hstepEq :
      evalAbiCallStep copyOnNonMove prog sAbi = evalMirCallStep prog sMir :=
    evalAbiCallStep_pc1_eq_mir copyOnNonMove prog sAbi sMir hpcAbi hpcMir hslot1 hslot2
  cases hreach with
  | zero => exact .zero sMir
  | step n _ s' obs tr' _ hstep _ =>
    change StepResult.step obs s' = evalAbiCallStep copyOnNonMove prog sAbi at hstep
    rw [hstepEq] at hstep
    revert hstep
    unfold evalMirCallStep
    rw [hpcMir]
    simp only
    split <;> (try split) <;> intro hstep <;> cases hstep
  | choice n kind _ s' branches tr' _ hstep _ _ =>
    change StepResult.choice kind branches = evalAbiCallStep copyOnNonMove prog sAbi at hstep
    rw [hstepEq] at hstep
    revert hstep
    unfold evalMirCallStep
    rw [hpcMir]
    simp only
    split <;> (try split) <;> intro hstep <;> cases hstep
  | emptyChoice n kind _ branches hstep _ =>
    change StepResult.choice kind branches = evalAbiCallStep copyOnNonMove prog sAbi at hstep
    rw [hstepEq] at hstep
    revert hstep
    unfold evalMirCallStep
    rw [hpcMir]
    simp only
    split <;> (try split) <;> intro hstep <;> cases hstep
  | terminated n _ term hstep =>
    change StepResult.terminated term = evalAbiCallStep copyOnNonMove prog sAbi at hstep
    rw [hstepEq] at hstep
    exact .terminated n sMir term hstep
  | failed n _ err hstep =>
    change StepResult.failed err = evalAbiCallStep copyOnNonMove prog sAbi at hstep
    rw [hstepEq] at hstep
    exact .failed n sMir err hstep
  | noStep n _ hno =>
    exact False.elim (hno ⟨_, rfl⟩)

/-- From any valid initial state `init` (`initCallState prog init`) where
    `prog.abi.argMode ≠ .indirect true` and `prog.argOp` is `.copy ⟨1⟩` or
    `.move ⟨1⟩`, both `evalAbiCallStep true` and `evalMirCallStep` take a single
    deterministic step to `pc = 1` states with identical `slot1` and `slot2`. -/
theorem evalAbiCallStep_pc0_exists (prog : CallProg) (init : CallState)
    (hinit : initCallState prog init)
    (hmode : prog.abi.argMode ≠ .indirect true)
    (hop : prog.argOp = .copy ⟨1⟩ ∨ prog.argOp = .move ⟨1⟩) :
    ∃ sAbi' sMir' : CallState,
      evalAbiCallStep true prog init = .step () sAbi' ∧
      evalMirCallStep prog init = .step () sMir' ∧
      sAbi'.pc = 1 ∧ sMir'.pc = 1 ∧
      sAbi'.slot1 = sMir'.slot1 ∧
      sAbi'.slot2 = sMir'.slot2 := by
  let ⟨hpc0, _, _, v1, hslot1, hvalArg, hvalRet⟩ := hinit
  have hretMarshal :
      marshalByVal prog.abi.retMode (evalCalleeAction prog.callee v1).2 =
        some (evalCalleeAction prog.callee v1).2 :=
    marshalByVal_of_matches _ _ hvalRet
  have hargMarshal : marshalByVal prog.abi.argMode v1 = some v1 :=
    marshalByVal_of_matches v1 prog.abi.argMode hvalArg
  cases hop with
  | inl hopCopy =>
    cases hargMode : prog.abi.argMode with
    | indirect r =>
      cases r with
      | true => exact False.elim (hmode hargMode)
      | false =>
        refine ⟨
          { init with
            pc := 1
            slot1 := some v1
            slot2 := some (evalCalleeAction prog.callee v1).2
            scratchSlot := some (evalCalleeAction prog.callee v1).1 },
          { init with
            pc := 1
            slot1 := some v1
            slot2 := some (evalCalleeAction prog.callee v1).2 },
          ?_, ?_, rfl, rfl, rfl, rfl⟩
        · unfold evalAbiCallStep
          rw [hpc0, hargMode, hopCopy, hslot1]
          dsimp only
          rw [hretMarshal]
          rfl
        · unfold evalMirCallStep
          rw [hpc0, hopCopy, hslot1]
          rfl
    | ignore | direct | pair | cast =>
      rw [hargMode] at hargMarshal
      refine ⟨
        { init with
          pc := 1
          slot1 := some v1
          slot2 := some (evalCalleeAction prog.callee v1).2 },
        { init with
          pc := 1
          slot1 := some v1
          slot2 := some (evalCalleeAction prog.callee v1).2 },
        ?_, ?_, rfl, rfl, rfl, rfl⟩
      · unfold evalAbiCallStep
        rw [hpc0, hargMode, hopCopy, hslot1]
        dsimp only
        rw [hargMarshal]
        dsimp only
        rw [hretMarshal]
        rfl
      · unfold evalMirCallStep
        rw [hpc0, hopCopy, hslot1]
        rfl
  | inr hopMove =>
    cases hargMode : prog.abi.argMode with
    | indirect r =>
      cases r with
      | true => exact False.elim (hmode hargMode)
      | false =>
        refine ⟨
          { init with
            pc := 1
            slot1 := none
            slot2 := some (evalCalleeAction prog.callee v1).2
            scratchSlot := some (evalCalleeAction prog.callee v1).1 },
          { init with
            pc := 1
            slot1 := none
            slot2 := some (evalCalleeAction prog.callee v1).2 },
          ?_, ?_, rfl, rfl, rfl, rfl⟩
        · unfold evalAbiCallStep
          rw [hpc0, hargMode, hopMove, hslot1]
          dsimp only
          rw [hretMarshal]
          rfl
        · unfold evalMirCallStep
          rw [hpc0, hopMove, hslot1]
          rfl
    | ignore | direct | pair | cast =>
      rw [hargMode] at hargMarshal
      refine ⟨
        { init with
          pc := 1
          slot1 := none
          slot2 := some (evalCalleeAction prog.callee v1).2 },
        { init with
          pc := 1
          slot1 := none
          slot2 := some (evalCalleeAction prog.callee v1).2 },
        ?_, ?_, rfl, rfl, rfl, rfl⟩
      · unfold evalAbiCallStep
        rw [hpc0, hargMode, hopMove, hslot1]
        dsimp only
        rw [hargMarshal]
        dsimp only
        rw [hretMarshal]
        rfl
      · unfold evalMirCallStep
        rw [hpc0, hopMove, hslot1]
        rfl

/-- **Positive Theorem 2A (`abi_reachesPrefix_to_mir`):**
    When the ABI argument mode is not an unsoundly marked `indirect true`
    (`prog.abi.argMode ≠ .indirect true`) and `prog.argOp` is a local operand
    (`.copy ⟨1⟩` or `.move ⟨1⟩`), every execution prefix of `AbiCallMachine true`
    from a valid initial state `init` is a valid execution prefix of
    `MirCallMachine` with identical observations and outcome. -/
theorem abi_reachesPrefix_to_mir (prog : CallProg) (init : CallState)
    (hinit : initCallState prog init)
    (hmode : prog.abi.argMode ≠ .indirect true)
    (hop : prog.argOp = .copy ⟨1⟩ ∨ prog.argOp = .move ⟨1⟩)
    (steps : Nat) (tr : List Unit) (out : PrefixOutcome MirVal)
    (hreach : ReachesPrefix (AbiCallMachine true) prog init steps init tr out) :
    ReachesPrefix MirCallMachine prog init steps init tr out := by
  let ⟨sAbi1, sMir1, habi0, hmir0, hpcAbi1, hpcMir1, hslot1Eq, hslot2Eq⟩ :=
    evalAbiCallStep_pc0_exists prog init hinit hmode hop
  cases hreach with
  | zero => exact .zero init
  | step n _ sAbi' obs tr' _ hstep hrest =>
    change StepResult.step obs sAbi' = evalAbiCallStep true prog init at hstep
    rw [habi0] at hstep
    injection hstep with hobs hsAbi'
    subst hobs hsAbi'
    exact .step n init sMir1 () tr' out hmir0.symm
      (reachesPrefix_pc1_abi_to_mir true prog init n sAbi' sMir1 tr' out
        hpcAbi1 hpcMir1 hslot1Eq hslot2Eq hrest)
  | choice n kind _ s' branches tr' _ hstep _ _ =>
    change StepResult.choice kind branches = evalAbiCallStep true prog init at hstep
    rw [habi0] at hstep
    cases hstep
  | emptyChoice n kind _ branches hstep _ =>
    change StepResult.choice kind branches = evalAbiCallStep true prog init at hstep
    rw [habi0] at hstep
    cases hstep
  | terminated n _ term hstep =>
    change StepResult.terminated term = evalAbiCallStep true prog init at hstep
    rw [habi0] at hstep
    cases hstep
  | failed n _ err hstep =>
    change StepResult.failed err = evalAbiCallStep true prog init at hstep
    rw [habi0] at hstep
    cases hstep
  | noStep n _ hno =>
    exact False.elim (hno ⟨_, rfl⟩)

/-- **Positive Theorem 2B (`abi_call_marshaling_refines`):**
    For all `PassMode`s (`ignore`, `direct`, `pair`, `cast`, and
    `indirect false`), `AbiCallLang` (`copyOnNonMove = true`) refines
    (`Compiles`) `MirCallLang` across all queries and step budgets, even when
    the callee mutates its parameter local in-place. -/
theorem abi_call_marshaling_refines (prog : CallProg)
    (hmode : prog.abi.argMode ≠ .indirect true)
    (hop : prog.argOp = .copy ⟨1⟩ ∨ prog.argOp = .move ⟨1⟩) :
    Compiles MirCallLang AbiCallLang (fun b => b) prog prog := by
  intro q hdefMir
  refine ⟨?_, ?_⟩
  · intro hinit tr out hreachAbi
    exact hdefMir hinit tr out
      (abi_reachesPrefix_to_mir prog q.init hinit hmode hop q.steps tr out hreachAbi)
  · intro out ⟨hinit, hreachAbi⟩
    exact ⟨hinit,
      abi_reachesPrefix_to_mir prog q.init hinit hmode hop q.steps out.trace out.outcome hreachAbi⟩

/-- info: 'Anneal.abi_call_marshaling_refines' depends on axioms: [propext] -/
#guard_msgs in
#print axioms abi_call_marshaling_refines

/-- Direct-MIR ABI-lowering compiler from `MirCallLang` to `AbiCallLang`. -/
def AbiLoweringCompiler : Compiler MirCallLang AbiCallLang where
  compile p := p
  π b := b

/-- `AbiLoweringCompiler` satisfies `Compiler.SoundOn` for every program with a
    valid `PassMode` (`argMode ≠ .indirect true`). -/
theorem abi_compiler_soundOn (prog : CallProg)
    (hmode : prog.abi.argMode ≠ .indirect true)
    (hop : prog.argOp = .copy ⟨1⟩ ∨ prog.argOp = .move ⟨1⟩) :
    AbiLoweringCompiler.SoundOn prog :=
  ⟨monotone_id, abi_call_marshaling_refines prog hmode hop⟩

/-!
## 3. End-to-End `VerificationResult` for In-Place Callee Parameter Mutation

Consider the Rust program:
```rust
#[inline(never)]
fn bump_in_place(mut x: BigStruct) -> BigStruct {
    x.0 += 10;
    x
}

pub fn caller(a: BigStruct) -> (usize, usize) {
    let b = bump_in_place(a); // Operand::Copy(_1), PassMode::Indirect
    (a.0, b.0)                // must return (a0, a0 + 10), NOT (a0 + 10, a0 + 10)
}
```
We prove `VerificationResultOn` (both `WellFormedOn` and the functional
postcondition `ret = .pair a0 (a0 + 10)`) with **zero TCB assumptions**
(`assumptions := []`) because `abi_compiler_soundOn` discharges compilation
refinement directly inside Lean!
-/

/-- Concrete program where the caller passes `_1` via `Operand.copy` under
    `PassMode.indirect false`, the callee increments `_1` by `10` in-place and
    returns it, and the caller returns `(slot1, slot2)`. -/
def callerCalleeMutateProg : CallProg where
  argOp := .copy ⟨1⟩
  callee := .incParamInPlace 10
  abi := { argMode := .indirect false, retMode := .indirect false }
  readCallerLocal1AfterCall := true

/-- Functional specification for `callerCalleeMutateProg`: for any initial state
    where `slot1 = some (.usize a0)`, normal termination returns
    `.pair a0 (a0 + 10)` (preserving the caller's `a0` despite callee in-place
    mutation of its parameter). -/
def EnsuresCallerPreservedAndCalleeBumped :
    MirCallLang.Behavior :=
  MirCallLang.SpecOn
    (fun q => ∃ a0, q.init.slot1 = some (.usize a0))
    (fun q out =>
      ∀ ret a0,
        out.outcome = .terminated (.normal ret) →
        q.init.slot1 = some (.usize a0) →
        ret = MirVal.pair a0 (a0 + 10))

/-- Source-level verification of `callerCalleeMutateProg` against
    `EnsuresCallerPreservedAndCalleeBumped`. -/
theorem callerCalleeMutateProg_satisfies_spec :
    MirCallLang.sem callerCalleeMutateProg ≤
      EnsuresCallerPreservedAndCalleeBumped := by
  intro q ⟨a0, hslot1_a0⟩
  cases q with
  | mk init steps =>
    refine ⟨?_, ?_⟩
    · intro hinit tr out hreach
      let ⟨hpc0, _, _, v1, hslot1, _, _⟩ := hinit
      rw [hslot1_a0] at hslot1
      injection hslot1 with hv1
      subst hv1
      cases hreach with
      | zero => trivial
      | step n _ s1 obs tr' _ hstep1 hrest1 =>
        change StepResult.step obs s1 = evalMirCallStep callerCalleeMutateProg init at hstep1
        unfold callerCalleeMutateProg evalMirCallStep at hstep1
        rw [hpc0, hslot1_a0] at hstep1
        injection hstep1 with hobs hs1
        subst hobs hs1
        cases hrest1 with
        | zero => trivial
        | step m _ s2 obs2 tr2 _ hstep2 _ =>
          change StepResult.step obs2 s2 = evalMirCallStep callerCalleeMutateProg _ at hstep2
          unfold callerCalleeMutateProg evalMirCallStep evalCalleeAction bumpVal at hstep2
          cases hstep2
        | choice m kind _ s2 branches tr2 _ hstep2 _ _ =>
          change StepResult.choice kind branches = evalMirCallStep callerCalleeMutateProg _ at hstep2
          unfold callerCalleeMutateProg evalMirCallStep evalCalleeAction bumpVal at hstep2
          cases hstep2
        | emptyChoice m kind _ branches hstep2 _ =>
          change StepResult.choice kind branches = evalMirCallStep callerCalleeMutateProg _ at hstep2
          unfold callerCalleeMutateProg evalMirCallStep evalCalleeAction bumpVal at hstep2
          cases hstep2
        | terminated m _ term hstep2 =>
          trivial
        | failed m _ err hstep2 =>
          change StepResult.failed err = evalMirCallStep callerCalleeMutateProg _ at hstep2
          unfold callerCalleeMutateProg evalMirCallStep evalCalleeAction bumpVal at hstep2
          cases hstep2
        | noStep m _ hno =>
          exact False.elim (hno ⟨_, rfl⟩)
      | choice n kind _ s1 branches tr' _ hstep1 _ _ =>
        change StepResult.choice kind branches =
          evalMirCallStep callerCalleeMutateProg init at hstep1
        unfold callerCalleeMutateProg evalMirCallStep at hstep1
        rw [hpc0, hslot1_a0] at hstep1
        cases hstep1
      | emptyChoice n kind _ branches hstep1 _ =>
        change StepResult.choice kind branches =
          evalMirCallStep callerCalleeMutateProg init at hstep1
        unfold callerCalleeMutateProg evalMirCallStep at hstep1
        rw [hpc0, hslot1_a0] at hstep1
        cases hstep1
      | terminated n _ term hstep1 =>
        change StepResult.terminated term =
          evalMirCallStep callerCalleeMutateProg init at hstep1
        unfold callerCalleeMutateProg evalMirCallStep at hstep1
        rw [hpc0, hslot1_a0] at hstep1
        cases hstep1
      | failed n _ err hstep1 =>
        change StepResult.failed err =
          evalMirCallStep callerCalleeMutateProg init at hstep1
        unfold callerCalleeMutateProg evalMirCallStep at hstep1
        rw [hpc0, hslot1_a0] at hstep1
        cases hstep1
      | noStep n _ hno =>
        exact False.elim (hno ⟨_, rfl⟩)
    · intro out ⟨hinit, hreach⟩ ret a1 hout hslot1_a1
      cases out with
      | mk trace outcome =>
        let ⟨hpc0, _, _, v1, hslot1, _, _⟩ := hinit
        rw [hslot1_a1] at hslot1
        injection hslot1 with hv1
        subst hv1
        cases hreach with
        | zero => cases hout
        | step n _ s1 obs tr' _ hstep1 hrest1 =>
          change StepResult.step obs s1 = evalMirCallStep callerCalleeMutateProg init at hstep1
          unfold callerCalleeMutateProg evalMirCallStep at hstep1
          rw [hpc0, hslot1_a1] at hstep1
          injection hstep1 with hobs hs1
          subst hobs hs1
          cases hrest1 with
          | zero => cases hout
          | step m _ s2 obs2 tr2 _ hstep2 _ =>
            change StepResult.step obs2 s2 = evalMirCallStep callerCalleeMutateProg _ at hstep2
            unfold callerCalleeMutateProg evalMirCallStep evalCalleeAction bumpVal at hstep2
            cases hstep2
          | choice m kind _ s2 branches tr2 _ hstep2 _ _ =>
            change StepResult.choice kind branches = evalMirCallStep callerCalleeMutateProg _ at hstep2
            unfold callerCalleeMutateProg evalMirCallStep evalCalleeAction bumpVal at hstep2
            cases hstep2
          | emptyChoice m kind _ branches hstep2 _ =>
            change StepResult.choice kind branches = evalMirCallStep callerCalleeMutateProg _ at hstep2
            unfold callerCalleeMutateProg evalMirCallStep evalCalleeAction bumpVal at hstep2
            cases hstep2
          | terminated m _ term hstep2 =>
            change StepResult.terminated term = evalMirCallStep callerCalleeMutateProg _ at hstep2
            unfold callerCalleeMutateProg evalMirCallStep evalCalleeAction bumpVal at hstep2
            dsimp only at hstep2
            injection hstep2 with hterm
            subst hterm
            injection hout with htermEq
            injection htermEq with hretEq
            exact hretEq.symm
          | failed m _ err hstep2 =>
            change StepResult.failed err = evalMirCallStep callerCalleeMutateProg _ at hstep2
            unfold callerCalleeMutateProg evalMirCallStep evalCalleeAction bumpVal at hstep2
            cases hstep2
          | noStep m _ hno =>
            exact False.elim (hno ⟨_, rfl⟩)
        | choice n kind _ s1 branches tr' _ hstep1 _ _ =>
          change StepResult.choice kind branches =
            evalMirCallStep callerCalleeMutateProg init at hstep1
          unfold callerCalleeMutateProg evalMirCallStep at hstep1
          rw [hpc0, hslot1_a1] at hstep1
          cases hstep1
        | emptyChoice n kind _ branches hstep1 _ =>
          change StepResult.choice kind branches =
            evalMirCallStep callerCalleeMutateProg init at hstep1
          unfold callerCalleeMutateProg evalMirCallStep at hstep1
          rw [hpc0, hslot1_a1] at hstep1
          cases hstep1
        | terminated n _ term hstep1 =>
          change StepResult.terminated term =
            evalMirCallStep callerCalleeMutateProg init at hstep1
          unfold callerCalleeMutateProg evalMirCallStep at hstep1
          rw [hpc0, hslot1_a1] at hstep1
          cases hstep1
        | failed n _ err hstep1 =>
          change StepResult.failed err =
            evalMirCallStep callerCalleeMutateProg init at hstep1
          unfold callerCalleeMutateProg evalMirCallStep at hstep1
          rw [hpc0, hslot1_a1] at hstep1
          cases hstep1
        | noStep n _ hno =>
          exact False.elim (hno ⟨_, rfl⟩)

/-- Empty assumption type for a verified compiler with zero unverified TCB
    items. -/
inductive EmptyTCB where

instance : TrustedAssumption EmptyTCB where
  meaning e := nomatch e

def strictZeroTCBPolicy : TrustPolicy EmptyTCB where
  isAllowed e := nomatch e

/-- **Positive Theorem 2C (`caller_callee_mutate_verified`):**
    End-to-end `VerificationResultOn` for `callerCalleeMutateProg` under
    `AbiLoweringCompiler` with **zero TCB assumptions** (`assumptions := []`),
    proving both source Post-Cleanup MIR correctness and compiled ABI-lowered
    correctness. -/
theorem caller_callee_mutate_verified :
    VerificationResultOn
      AbiLoweringCompiler
      strictZeroTCBPolicy
      []
      callerCalleeMutateProg
      (fun q => ∃ a0, q.init.slot1 = some (.usize a0))
      [EnsuresCallerPreservedAndCalleeBumped] := by
  refine ⟨True.intro, fun _ => ?_⟩
  have hsound : AbiLoweringCompiler.SoundOn callerCalleeMutateProg :=
    abi_compiler_soundOn callerCalleeMutateProg (by decide) (.inl rfl)
  have hver :
      AbiLoweringCompiler.Verified
        callerCalleeMutateProg
        EnsuresCallerPreservedAndCalleeBumped :=
    Compiler.SoundOn.verify hsound callerCalleeMutateProg_satisfies_spec
  exact Compiler.Verified.with_wellFormedOn
    hver
    (specOn_le_wellFormedOn _ _)
    monotone_id

/-- info: 'Anneal.caller_callee_mutate_verified' depends on axioms: [propext] -/
#guard_msgs in
#print axioms caller_callee_mutate_verified

/-!
## 4. Shim & `ExternAbi::RustCall` Tuple-Spreading Refinement

We mechanize the two core shim/ABI normalizations performed during direct-MIR
codegen in `rustc_codegen_cranelift`:
1. **Empty `DropGlue` shim elision (`abi/mod.rs#L492-L498`):**
   When `TerminatorKind::Drop` drops a place of a type whose
   `Instance::resolve_drop_in_place(tcx, ty)` is `InstanceKind::DropGlue(_, None)`
   (`hasDropBody = false`), `cg_clif` lowers the `Drop` terminator directly to a
   `Goto(target)` jump without emitting a call.
2. **`ExternAbi::RustCall` tuple-argument spreading (`spread_arg` in
   `abi/mod.rs#L298-L317` and `#L530-L553`):**
   At a `RustCall` call site (used by `Fn`/`FnMut`/`FnOnce` trait calls and
   `ClosureOnceShim`), the caller unpacks the trailing tuple argument
   `.pair a b` into individual `FnAbi` scalar arguments `a` and `b`, and the
   callee prelude reassembles those individual arguments into the local
   `fx.mir.spread_arg` via field projections (`place.place_field(fx, i)`).
-/

/-- Source MIR `TerminatorKind::Drop` semantics: if `hasDropBody = false`,
    invokes the empty `InstanceKind::DropGlue(_, None)` body (which immediately
    returns `()`) and jumps to `target`; target lowering (`elideEmptyDrop =
    true`) jumps directly to `target`. -/
def DropMirMachine : SmallStepMachine Bool Nat Unit MirVal where
  initState _ s := s = 0
  step _ s r :=
    match s with
    | 0 => r = .terminated (.normal .unit)
    | _ => r = .failed .ub

def DropElidedMachine : SmallStepMachine Bool Nat Unit MirVal where
  initState _ s := s = 0
  step _ s r :=
    match s with
    | 0 => r = .terminated (.normal .unit)
    | _ => r = .failed .ub

/-- **Positive Theorem 3A (`empty_drop_shim_refines`):**
    Eliding a call to `InstanceKind::DropGlue(_, None)` (`hasDropBody = false`)
    in `codegen_terminator` (`abi/mod.rs#L492-L498`) refines the MIR drop
    specification. -/
theorem empty_drop_shim_refines :
    Compiles DropMirMachine.toLanguage DropElidedMachine.toLanguage
      (fun b => b) false false :=
  Preorder.le_refl _

/-- Source MIR `ExternAbi::RustCall` passes a tuple `.pair a b` as a single
    MIR argument local; target ABI lowering unpacks `.pair a b` into two scalar
    arguments `(a, b)` at the call site (`abi/mod.rs#L530-L553`) and writes them
    into `spread_arg.0` and `spread_arg.1` in `codegen_fn_prelude`
    (`abi/mod.rs#L298-L317`). -/
def evalRustCallMir (body : Nat → Nat → MirVal) (tupleArg : MirVal) :
    Option MirVal :=
  match tupleArg with
  | .pair a b => some (body a b)
  | _ => none

def evalRustCallSpreadAbi (body : Nat → Nat → MirVal) (tupleArg : MirVal) :
    Option MirVal :=
  -- Caller unpacks tuple fields `0` and `1`:
  match tupleArg with
  | .pair field0 field1 =>
    -- Callee prelude writes `field0` and `field1` into `spread_arg` and reads
    -- them back:
    let spreadArg := MirVal.pair field0 field1
    match spreadArg with
    | .pair a b => some (body a b)
    | _ => none
  | _ => none

/-- **Positive Theorem 3B (`rust_call_spread_arg_refines`):**
    For every `ExternAbi::RustCall` body and tuple argument, unpacking the
    tuple argument across `FnAbi.args` at the call site and reassembling
    `fx.mir.spread_arg` in the callee prelude is observationally identical to
    direct tuple passing in MIR. -/
theorem rust_call_spread_arg_refines (body : Nat → Nat → MirVal)
    (tupleArg : MirVal) :
    evalRustCallSpreadAbi body tupleArg = evalRustCallMir body tupleArg := by
  cases tupleArg <;> rfl

/-- info: 'Anneal.rust_call_spread_arg_refines' depends on axioms: [propext] -/
#guard_msgs in
#print axioms rust_call_spread_arg_refines

/-!
## 5. Negative Soundness Canaries: Missing Caller Scratch Copy & `deduced_param_attrs`

We now prove two negative canary theorems demonstrating why:
1. A direct-MIR backend **must** allocate a caller-side scratch copy for
   non-`Move` `PassMode::Indirect` arguments (`abi/pass_mode.rs#L275-L280`), and
2. `tcx.deduced_param_attrs` (`compiler/rustc_mir_transform/src/deduce_param_attrs.rs#L177-L242`)
   **must** be disabled (via `-Copt-level=0` or
   `tcx.fn_abi_of_instance_no_deduced_attrs`) when lowering Post-Cleanup MIR.
-/

/-- **Negative Canary Theorem 4A (`buggy_indirect_without_caller_copy_unsound`):**
    If the backend omits the caller-side scratch copy on `Operand.copy` for a
    `PassMode.indirect false` argument (`BuggyAbiCallLang`, i.e.,
    `copyOnNonMove = false`), then `callerCalleeMutateProg` **violates
    compilation refinement** (`¬ Compiles`): in Post-Cleanup MIR the caller's
    local `_1` remains `42` and the program returns `MirVal.pair 42 52`, whereas
    the buggy ABI lowering aliases the callee's parameter `_1` directly to the
    caller's stack slot and mutates it in-place to `52`, returning
    `MirVal.pair 52 52`. -/
theorem buggy_indirect_without_caller_copy_unsound :
    ¬ Compiles MirCallLang BuggyAbiCallLang (fun b => b)
        callerCalleeMutateProg callerCalleeMutateProg := by
  intro hcomp
  let init0 : CallState := {
    pc := 0
    slot1 := some (.usize 42)
    slot2 := none
    scratchSlot := none
  }
  let q : ExecQuery CallState := { init := init0, steps := 2 }
  have hinit0 : initCallState callerCalleeMutateProg init0 := by
    refine ⟨rfl, rfl, rfl, .usize 42, rfl, trivial, trivial⟩
  let ⟨hdefMir, hvalMir⟩ :=
    callerCalleeMutateProg_satisfies_spec q ⟨42, rfl⟩
  let ⟨_, houtSub⟩ := hcomp q hdefMir
  let s1Buggy : CallState := {
    pc := 1
    slot1 := some (.usize 52)
    slot2 := some (.usize 52)
    scratchSlot := none
  }
  have hstep1Buggy :
      (AbiCallMachine false).step callerCalleeMutateProg init0 (.step () s1Buggy) :=
    rfl
  have hstep2Buggy :
      (AbiCallMachine false).step callerCalleeMutateProg s1Buggy
        (.terminated (.normal (MirVal.pair 52 52))) :=
    rfl
  have hreachBuggy :
      ReachesPrefix (AbiCallMachine false) callerCalleeMutateProg init0 2 init0
        [()] (.terminated (.normal (MirVal.pair 52 52))) :=
    .step 1 init0 s1Buggy () [] (.terminated (.normal (MirVal.pair 52 52)))
      hstep1Buggy
      (.terminated 0 s1Buggy (.normal (MirVal.pair 52 52)) hstep2Buggy)
  have hreachMir :=
    houtSub { trace := [()], outcome := .terminated (.normal (MirVal.pair 52 52)) }
      ⟨hinit0, hreachBuggy⟩
  have hpost :=
    hvalMir
      { trace := [()], outcome := .terminated (.normal (MirVal.pair 52 52)) }
      hreachMir (MirVal.pair 52 52) 42 rfl rfl
  cases hpost

/-- info: 'Anneal.buggy_indirect_without_caller_copy_unsound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms buggy_indirect_without_caller_copy_unsound

/-- Concrete program modeling the `deduced_param_attrs` phase mismatch:
    In `PostCleanup` MIR, the callee performs a dead store to its by-value
    parameter `_1` (`_1.0 += 99`) before returning a constant `.usize 7`
    (`CalleeAction.deadStoreThenReturnConst 99 (.usize 7)`).
    If `optimized_mir` runs `DeadStoreElimination` (`-Copt-level != 0`), the
    dead store to `_1` is eliminated in `optimized_mir`, so
    `deduced_param_attrs` (`deduce_param_attrs.rs#L177-L242`) deduces
    `ArgAttribute::ReadOnly` (`PassMode.indirect true`) on `_1`.
    When the caller then elides its scratch copy for the `ReadOnly` parameter
    while codegen lowers the unoptimized `PostCleanup` MIR of the callee (where
    the dead store `_1.0 += 99` is still present!), the callee's dead store
    corrupts the caller's live local `slot1`! -/
def deducedReadOnlyMismatchProg : CallProg where
  argOp := .copy ⟨1⟩
  callee := .deadStoreThenReturnConst 99 (.usize 7)
  abi := { argMode := .indirect true, retMode := .direct }
  readCallerLocal1AfterCall := true

/-- **Negative Canary Theorem 4B (`deduced_readonly_phase_mismatch_unsound`):**
    Even in `AbiCallLang` (`copyOnNonMove = true`), if `FnAbi` attaches a
    `ReadOnly` attribute (`PassMode.indirect true`) deduced from `optimized_mir`
    to a `PostCleanup` MIR callee that contains a dead store to its parameter,
    compilation refinement is violated (`¬ Compiles MirCallLang AbiCallLang`). -/
theorem deduced_readonly_phase_mismatch_unsound :
    ¬ Compiles MirCallLang AbiCallLang (fun b => b)
        deducedReadOnlyMismatchProg deducedReadOnlyMismatchProg := by
  intro hcomp
  let init0 : CallState := {
    pc := 0
    slot1 := some (.usize 10)
    slot2 := none
    scratchSlot := none
  }
  let q : ExecQuery CallState := { init := init0, steps := 2 }
  have hinit0 : initCallState deducedReadOnlyMismatchProg init0 := by
    refine ⟨rfl, rfl, rfl, .usize 10, rfl, trivial, trivial⟩
  have hdefMir : (MirCallLang.sem deducedReadOnlyMismatchProg q).defined := by
    intro _ tr out hreach
    cases hreach with
    | step n _ s1 obs tr' _ hstep1 hrest1 =>
      change StepResult.step obs s1 =
        evalMirCallStep deducedReadOnlyMismatchProg init0 at hstep1
      injection hstep1 with hobs hs1
      subst hobs hs1
      cases hrest1 with
      | step m _ s2 obs2 tr2 _ hstep2 _ => cases hstep2
      | choice m kind _ s2 branches tr2 _ hstep2 _ _ => cases hstep2
      | emptyChoice m kind _ branches hstep2 _ => cases hstep2
      | terminated m _ term hstep2 => trivial
      | failed m _ err hstep2 => cases hstep2
      | noStep m _ hno => exact False.elim (hno ⟨_, rfl⟩)
    | choice n kind _ s1 branches tr' _ hstep1 _ _ => cases hstep1
    | emptyChoice n kind _ branches hstep1 _ => cases hstep1
    | terminated n _ term hstep1 => cases hstep1
    | failed n _ err hstep1 => cases hstep1
    | noStep n _ hno => exact False.elim (hno ⟨_, rfl⟩)
  let ⟨_, houtSub⟩ := hcomp q hdefMir
  let s1Abi : CallState := {
    pc := 1
    slot1 := some (.usize 109)
    slot2 := some (.usize 7)
    scratchSlot := none
  }
  have hstep1Abi :
      (AbiCallMachine true).step deducedReadOnlyMismatchProg init0 (.step () s1Abi) :=
    rfl
  have hstep2Abi :
      (AbiCallMachine true).step deducedReadOnlyMismatchProg s1Abi
        (.terminated (.normal (MirVal.pair 109 7))) :=
    rfl
  have hreachAbi :
      ReachesPrefix (AbiCallMachine true) deducedReadOnlyMismatchProg init0 2 init0
        [()] (.terminated (.normal (MirVal.pair 109 7))) :=
    .step 1 init0 s1Abi () [] (.terminated (.normal (MirVal.pair 109 7)))
      hstep1Abi
      (.terminated 0 s1Abi (.normal (MirVal.pair 109 7)) hstep2Abi)
  let ⟨_, hreachMir⟩ :=
    houtSub { trace := [()], outcome := .terminated (.normal (MirVal.pair 109 7)) }
      ⟨hinit0, hreachAbi⟩
  cases hreachMir with
  | step _ _ s1Mir _ _ _ hstep1Mir hrestMir =>
    change StepResult.step () s1Mir =
      evalMirCallStep deducedReadOnlyMismatchProg init0 at hstep1Mir
    injection hstep1Mir with _ hs1Mir
    subst hs1Mir
    cases hrestMir with
    | choice _ _ _ _ _ _ _ hstep2Mir _ _ => cases hstep2Mir
    | terminated _ _ _ hstep2Mir =>
      change StepResult.terminated (.normal (MirVal.pair 109 7)) =
        StepResult.terminated (.normal (MirVal.pair 10 7)) at hstep2Mir
      cases hstep2Mir
  | choice _ _ _ _ _ _ _ hstep1Mir _ _ => cases hstep1Mir

/-- info: 'Anneal.deduced_readonly_phase_mismatch_unsound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms deduced_readonly_phase_mismatch_unsound

end Anneal
