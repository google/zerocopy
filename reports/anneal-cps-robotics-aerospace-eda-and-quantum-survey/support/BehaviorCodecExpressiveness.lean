-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Variable-Step Stuttering and Partial Outcome Decoding in `BehaviorCodec`

This standalone Lean 4 mechanization formalizes variable-step stuttering and
partial outcome decoding for `BehaviorCodec`:

1. **Part I(1) — Step-Indexed `BehaviorCodec` Failure on Variable-Step Passes:**
   Constructs a concrete 2-statement MIR-like source program `s_var` where
   statement 0 (`Downcast`) lowers to `0` target instructions and statement 1
   (`NicheDecode`) lowers to `3` target instructions in `t_var`. Proves that at
   intermediate step budgets (`steps = 1` and `steps = 2`), `t_var` returns
   `PrefixOutcome.incomplete` while `s_var` has already terminated at
   `steps = 2`, refuting both 1-to-1 `ExecQuery` step mapping
   (`lockstep_codec_fails_on_s_var`) and any state-independent query step
   projection (`no_state_independent_step_map_for_variable_lowering`).
2. **Part I(2) — Constructive Variable-Step Architectures (A vs. B):**
   - **Architecture A (`DilationCodec`):** Equips step-indexed `ExecQuery`
     translation with monotone step-window bounds `[srcFloor n, srcCeil n]`
     satisfying `floor_unbounded`. Proves monotonicity, composition closure,
     strict rejection of `loopCodegen` (`bb0: jmp bb0`), and verification of
     `s_var → t_var` (`k = 0` and `k = 3`).
   - **Architecture B (`EventualBehaviorOf` + `TotalBehaviorCodec`):**
     Encapsulates step budgets inside `EventualBehaviorOf` (`Query := State`,
     `Out := EventualOut Obs Val`), preserving exact all-prefix UB-freedom in
     `.defined` (`eventual_wellFormed_iff_prefix_wellFormed`) while tracking
     eventual termination (`∃ n, ...`) and divergence (`∀ n, ...`) in `.val`.
     Proves that `∃ n : Nat, ...` in `Prop` requires zero `Classical.choice`,
     that `TotalBehaviorCodec` needs zero step-count synchronization, composes
     strictly under `id` and `comp`, strictly rejects `loopCodegen`, and
     verifies `s_var → t_var` and `s_fast → t_fast` under the exact same codec.
3. **Part II — Non-Surjectivity Obstruction and `PartialBehaviorCodec`:**
   - Proves `no_total_section_for_bool_in_uint8` and
     `no_total_section_for_bool_in_nat`: no total `(encodeOut, decodeOut)` pair
     can satisfy `∀ o₂, encodeOut (decodeOut o₂) = o₂` when
     `|L₂.Out| > |L₁.Out|`.
   - Mechanizes `PartialBehaviorCodec L₁ L₂` (`decodeOut : L₂.Out →
     Option L₁.Out` with `decode_encode_out` and `encode_of_decode_some`),
     proving injectivity, automatic rejection of invalid target bit patterns
     (`decodeOut o₂ = none`), monotonicity, definedness preservation, exact
     recovery on valid encodings, identity and composition closure
     (`(c₂.comp c₁).toMorphism = c₂.toMorphism ∘ c₁.toMorphism`), concrete
     `MirAbiVal ↔ X86RawVal` instantiation, and unified variable-step +
     partial-outcome verification.
-/

namespace Anneal.BehaviorCodecExpressiveness

/-!
## 1. Core Refinement Preorder and Small-Step Prefix Semantics
-/

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Partially defined value constructively representing `B ∪ {UB}`. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

abbrev Language.Behavior (L : Language) : Type :=
  Anneal.BehaviorCodecExpressiveness.Behavior L.Query L.Out

def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) :
    L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- Total behavior codec between two languages `L₁` and `L₂`. -/
structure TotalBehaviorCodec (L₁ L₂ : Language) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  encodeOut : L₁.Out → L₂.Out
  decodeOut : L₂.Out → L₁.Out
  decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = o₁
  encode_decode_out : ∀ o₂, encodeOut (decodeOut o₂) = o₂

/-- Induced monotone behavior morphism of a `TotalBehaviorCodec`. -/
def TotalBehaviorCodec.toMorphism {L₁ L₂ : Language}
    (c : TotalBehaviorCodec L₁ L₂) (b : L₁.Behavior) : L₂.Behavior :=
  fun q₂ =>
    let p := b (c.decodeQuery q₂)
    { defined := p.defined
      val := fun h o₂ => p.val h (c.decodeOut o₂) }

theorem TotalBehaviorCodec.monotone_toMorphism {L₁ L₂ : Language}
    (c : TotalBehaviorCodec L₁ L₂) : Monotone c.toMorphism := by
  intro b₁ b₂ hle q₂ hdef₂
  cases hle (c.decodeQuery q₂) hdef₂ with
  | intro hdef₁ hval =>
    exact ⟨hdef₁, fun o₂ ho₂ => hval (c.decodeOut o₂) ho₂⟩

/-- Identity `TotalBehaviorCodec`. -/
def TotalBehaviorCodec.id (L : Language) : TotalBehaviorCodec L L where
  encodeQuery q := q
  decodeQuery q := q
  decode_encode_query _ := rfl
  encodeOut o := o
  decodeOut o := o
  decode_encode_out _ := rfl
  encode_decode_out _ := rfl

/-- Composition of two `TotalBehaviorCodec`s. -/
def TotalBehaviorCodec.comp {L₁ L₂ L₃ : Language}
    (c₂ : TotalBehaviorCodec L₂ L₃) (c₁ : TotalBehaviorCodec L₁ L₂) :
    TotalBehaviorCodec L₁ L₃ where
  encodeQuery q₁ := c₂.encodeQuery (c₁.encodeQuery q₁)
  decodeQuery q₃ := c₁.decodeQuery (c₂.decodeQuery q₃)
  decode_encode_query q₁ := by
    rw [c₂.decode_encode_query, c₁.decode_encode_query]
  encodeOut o₁ := c₂.encodeOut (c₁.encodeOut o₁)
  decodeOut o₃ := c₁.decodeOut (c₂.decodeOut o₃)
  decode_encode_out o₁ := by
    rw [c₂.decode_encode_out, c₁.decode_encode_out]
  encode_decode_out o₃ := by
    rw [c₁.encode_decode_out, c₂.encode_decode_out]

/-- Small-step termination kind. -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Small-step single transition outcome. -/
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed

/-- Outcome of a finite execution prefix of length `steps`:
    - `incomplete`: step budget was exhausted before termination or failure.
    - `terminated term`: execution reached a terminal state within the budget.
    - `failed`: execution triggered Undefined Behavior within the budget.
    - `stuck`: execution reached a state with no outgoing transition. -/
inductive PrefixOutcome (Val : Type) where
  | incomplete
  | terminated (term : TerminationKind Val)
  | failed
  | stuck

def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .incomplete => True
  | .terminated _ => True
  | .failed => False
  | .stuck => False

structure ExecQuery (State : Type) where
  init : State
  steps : Nat

structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p 0 s [] .incomplete
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p n s' tr out →
      ReachesPrefix M p (n + 1) s (obs :: tr) out
  | choice (n : Nat) (s s' : State) (branches : State → Prop)
      (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice branches) →
      branches s' →
      ReachesPrefix M p n s' tr out →
      ReachesPrefix M p (n + 1) s tr out
  | emptyChoice (n : Nat) (s : State) (branches : State → Prop) :
      M.step p s (.choice branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) :
      M.step p s .failed →
      ReachesPrefix M p (n + 1) s [] .failed
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p (n + 1) s [] .stuck

def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M p q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.steps q.init out.trace out.outcome
  }

def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M

/-!
## 2. Concrete Variable-Step Lowering (`s_var → t_var`)

We model a concrete variable-step lowering pass from a MIR-like source language
(`VarMirProg`) to an x86-64 target language (`VarX86Prog`):
- `VarMirStmt.downcast`: a type-level enum variant downcast
  (`PlaceElem::Downcast`), which takes 1 step in MIR and lowers to `0` target
  instructions (`[]`).
- `VarMirStmt.nicheDecodeRet`: a niche-encoded discriminant decode and return
  (`TagEncoding::Niche`), which takes 1 step in MIR (returning `val + 3`) and
  lowers to `3` sequential target instructions
  (`incAcc`, `incAcc`, `incAccRet`).
-/

inductive VarMirStmt where
  | downcast
  | nicheDecodeRet
  | retNow

abbrev VarMirProg := List VarMirStmt

structure VarState where
  pc : Nat
  acc : Nat

def evalVarMirStep (p : VarMirProg) (s : VarState) :
    StepResult VarState Unit Nat :=
  match p[s.pc]? with
  | none => .failed
  | some .downcast => .step () { pc := s.pc + 1, acc := s.acc }
  | some .nicheDecodeRet => .terminated (.normal (s.acc + 3))
  | some .retNow => .terminated (.normal s.acc)

def VarMirMachine : SmallStepMachine VarMirProg VarState Unit Nat where
  initState _ s := s.pc = 0
  step p s r := r = evalVarMirStep p s

def VarMirLang : Language := VarMirMachine.toLanguage

inductive VarX86Instr where
  | incAcc
  | incAccRet
  | retNow
  | jmpSelf

abbrev VarX86Prog := List VarX86Instr

def evalVarX86Step (p : VarX86Prog) (s : VarState) :
    StepResult VarState Unit Nat :=
  match p[s.pc]? with
  | none => .failed
  | some .incAcc => .step () { pc := s.pc + 1, acc := s.acc + 1 }
  | some .incAccRet => .terminated (.normal (s.acc + 1))
  | some .retNow => .terminated (.normal s.acc)
  | some .jmpSelf => .step () s

def VarX86Machine : SmallStepMachine VarX86Prog VarState Unit Nat where
  initState _ s := s.pc = 0
  step p s r := r = evalVarX86Step p s

def VarX86Lang : Language := VarX86Machine.toLanguage

/-- Variable-step instruction selection:
    - `.downcast` lowers to `0` target instructions (`k = 0`),
    - `.nicheDecodeRet` lowers to `3` target instructions (`k = 3`),
    - `.retNow` lowers to `1` target instruction (`k = 1`). -/
def compileVarStmt : VarMirStmt → List VarX86Instr
  | .downcast => []
  | .nicheDecodeRet => [.incAcc, .incAcc, .incAccRet]
  | .retNow => [.retNow]

def compileVarProg (p : VarMirProg) : VarX86Prog :=
  p.flatMap compileVarStmt

/-- Concrete 2-statement source program `s_var`:
    Statement 0 is `Downcast` ($k = 0$) and Statement 1 is `NicheDecode`
    ($k = 3$). -/
def s_var : VarMirProg := [.downcast, .nicheDecodeRet]

/-- Compiled target program `t_var = compileVarProg s_var`, consisting of 3
    target instructions `[.incAcc, .incAcc, .incAccRet]`. -/
def t_var : VarX86Prog := compileVarProg s_var

/-- Infinite-loop target program `loopX86Prog` (`bb0: jmp bb0`). -/
def loopX86Prog : VarX86Prog := [.jmpSelf]

theorem evalVarMirStep_not_choice (p : VarMirProg) (s : VarState)
    (branches : VarState → Prop) :
    StepResult.choice branches ≠ evalVarMirStep p s := by
  dsimp [evalVarMirStep]
  cases p[s.pc]? with
  | none => intro h; cases h
  | some st => cases st <;> intro h <;> cases h

theorem evalVarX86Step_not_choice (p : VarX86Prog) (s : VarState)
    (branches : VarState → Prop) :
    StepResult.choice branches ≠ evalVarX86Step p s := by
  dsimp [evalVarX86Step]
  cases p[s.pc]? with
  | none => intro h; cases h
  | some ins => cases ins <;> intro h <;> cases h

theorem reachesPrefix_varMir_zero {p : VarMirProg} {s : VarState}
    {tr : List Unit} {out : PrefixOutcome Nat}
    (h : ReachesPrefix VarMirMachine p 0 s tr out) :
    tr = [] ∧ out = .incomplete := by
  cases h
  exact ⟨rfl, rfl⟩

theorem reachesPrefix_varMir_succ {p : VarMirProg} {k : Nat} {s : VarState}
    {tr : List Unit} {out : PrefixOutcome Nat}
    (h : ReachesPrefix VarMirMachine p (k + 1) s tr out) :
    match evalVarMirStep p s with
    | .step obs s' =>
      ∃ tr', tr = obs :: tr' ∧ ReachesPrefix VarMirMachine p k s' tr' out
    | .terminated term => tr = [] ∧ out = .terminated term
    | .failed => tr = [] ∧ out = .failed
    | .choice _ => False := by
  cases h with
  | step _ _ s' obs tr' out hstep hr =>
    dsimp [VarMirMachine] at hstep
    rw [← hstep]
    exact ⟨tr', rfl, hr⟩
  | choice _ _ _ branches _ _ hstep =>
    exact False.elim (evalVarMirStep_not_choice p s branches hstep)
  | emptyChoice _ _ branches hstep =>
    exact False.elim (evalVarMirStep_not_choice p s branches hstep)
  | terminated _ _ term hstep =>
    dsimp [VarMirMachine] at hstep
    rw [← hstep]
    exact ⟨rfl, rfl⟩
  | failed _ _ hstep =>
    dsimp [VarMirMachine] at hstep
    rw [← hstep]
    exact ⟨rfl, rfl⟩
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, rfl⟩)

theorem reachesPrefix_varX86_zero {p : VarX86Prog} {s : VarState}
    {tr : List Unit} {out : PrefixOutcome Nat}
    (h : ReachesPrefix VarX86Machine p 0 s tr out) :
    tr = [] ∧ out = .incomplete := by
  cases h
  exact ⟨rfl, rfl⟩

theorem reachesPrefix_varX86_succ {p : VarX86Prog} {k : Nat} {s : VarState}
    {tr : List Unit} {out : PrefixOutcome Nat}
    (h : ReachesPrefix VarX86Machine p (k + 1) s tr out) :
    match evalVarX86Step p s with
    | .step obs s' =>
      ∃ tr', tr = obs :: tr' ∧ ReachesPrefix VarX86Machine p k s' tr' out
    | .terminated term => tr = [] ∧ out = .terminated term
    | .failed => tr = [] ∧ out = .failed
    | .choice _ => False := by
  cases h with
  | step _ _ s' obs tr' out hstep hr =>
    dsimp [VarX86Machine] at hstep
    rw [← hstep]
    exact ⟨tr', rfl, hr⟩
  | choice _ _ _ branches _ _ hstep =>
    exact False.elim (evalVarX86Step_not_choice p s branches hstep)
  | emptyChoice _ _ branches hstep =>
    exact False.elim (evalVarX86Step_not_choice p s branches hstep)
  | terminated _ _ term hstep =>
    dsimp [VarX86Machine] at hstep
    rw [← hstep]
    exact ⟨rfl, rfl⟩
  | failed _ _ hstep =>
    dsimp [VarX86Machine] at hstep
    rw [← hstep]
    exact ⟨rfl, rfl⟩
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, rfl⟩)

/-- Exact characterization of `s_var` prefixes from any valid initial state
    `s = ⟨0, acc⟩`:
    - `n = 0`: `tr = [] ∧ out = .incomplete`
    - `n = 1`: `tr = [()] ∧ out = .incomplete`
    - `n ≥ 2`: `tr = [()] ∧ out = .terminated (.normal (acc + 3))` -/
theorem s_var_reaches_iff (n : Nat) (acc : Nat) (tr : List Unit)
    (out : PrefixOutcome Nat) :
    ReachesPrefix VarMirMachine s_var n { pc := 0, acc := acc } tr out ↔
      match n with
      | 0 => tr = [] ∧ out = .incomplete
      | 1 => tr = [()] ∧ out = .incomplete
      | _ + 2 => tr = [()] ∧ out = .terminated (.normal (acc + 3)) := by
  constructor
  · intro h
    cases n with
    | zero => exact reachesPrefix_varMir_zero h
    | succ n₁ =>
      have h₁ := reachesPrefix_varMir_succ h
      dsimp [evalVarMirStep, s_var] at h₁
      rcases h₁ with ⟨tr₁, rfl, hr₁⟩
      cases n₁ with
      | zero =>
        rcases reachesPrefix_varMir_zero hr₁ with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
      | succ n₂ =>
        have h₂ := reachesPrefix_varMir_succ hr₁
        dsimp [evalVarMirStep, s_var] at h₂
        rcases h₂ with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
  · intro h
    cases n with
    | zero =>
      rcases h with ⟨rfl, rfl⟩
      exact ReachesPrefix.zero _
    | succ n₁ =>
      cases n₁ with
      | zero =>
        rcases h with ⟨rfl, rfl⟩
        exact ReachesPrefix.step 0
          (VarState.mk 0 acc) (VarState.mk 1 acc) () [] .incomplete rfl
          (ReachesPrefix.zero _)
      | succ n₂ =>
        rcases h with ⟨rfl, rfl⟩
        exact ReachesPrefix.step (n₂ + 1)
          (VarState.mk 0 acc) (VarState.mk 1 acc) () []
          (.terminated (.normal (acc + 3))) rfl
          (ReachesPrefix.terminated n₂ (VarState.mk 1 acc)
            (.normal (acc + 3)) rfl)

/-- Exact characterization of `t_var` prefixes from any valid initial state
    `s = ⟨0, acc⟩`:
    - `n = 0`: `tr = [] ∧ out = .incomplete`
    - `n = 1`: `tr = [()] ∧ out = .incomplete`
    - `n = 2`: `tr = [(), ()] ∧ out = .incomplete`
    - `n ≥ 3`: `tr = [(), ()] ∧ out = .terminated (.normal (acc + 3))` -/
theorem t_var_reaches_iff (n : Nat) (acc : Nat) (tr : List Unit)
    (out : PrefixOutcome Nat) :
    ReachesPrefix VarX86Machine t_var n { pc := 0, acc := acc } tr out ↔
      match n with
      | 0 => tr = [] ∧ out = .incomplete
      | 1 => tr = [()] ∧ out = .incomplete
      | 2 => tr = [(), ()] ∧ out = .incomplete
      | _ + 3 => tr = [(), ()] ∧ out = .terminated (.normal (acc + 3)) := by
  constructor
  · intro h
    cases n with
    | zero => exact reachesPrefix_varX86_zero h
    | succ n₁ =>
      have h₁ := reachesPrefix_varX86_succ h
      dsimp [evalVarX86Step, t_var, compileVarProg, s_var, compileVarStmt] at h₁
      rcases h₁ with ⟨tr₁, rfl, hr₁⟩
      cases n₁ with
      | zero =>
        rcases reachesPrefix_varX86_zero hr₁ with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
      | succ n₂ =>
        have h₂ := reachesPrefix_varX86_succ hr₁
        dsimp [evalVarX86Step, t_var, compileVarProg, s_var,
          compileVarStmt] at h₂
        rcases h₂ with ⟨tr₂, rfl, hr₂⟩
        cases n₂ with
        | zero =>
          rcases reachesPrefix_varX86_zero hr₂ with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
        | succ n₃ =>
          have h₃ := reachesPrefix_varX86_succ hr₂
          dsimp [evalVarX86Step, t_var, compileVarProg, s_var,
            compileVarStmt] at h₃
          rcases h₃ with ⟨rfl, rfl⟩
          have hadd : acc + 1 + 1 + 1 = acc + 3 := by omega
          rw [hadd]
          exact ⟨rfl, rfl⟩
  · intro h
    cases n with
    | zero =>
      rcases h with ⟨rfl, rfl⟩
      exact ReachesPrefix.zero _
    | succ n₁ =>
      cases n₁ with
      | zero =>
        rcases h with ⟨rfl, rfl⟩
        exact ReachesPrefix.step 0
          (VarState.mk 0 acc) (VarState.mk 1 (acc + 1)) () [] .incomplete rfl
          (ReachesPrefix.zero _)
      | succ n₂ =>
        cases n₂ with
        | zero =>
          rcases h with ⟨rfl, rfl⟩
          exact ReachesPrefix.step 1
            (VarState.mk 0 acc) (VarState.mk 1 (acc + 1)) () [()]
            .incomplete rfl
            (ReachesPrefix.step 0
              (VarState.mk 1 (acc + 1)) (VarState.mk 2 (acc + 1 + 1)) () []
              .incomplete rfl (ReachesPrefix.zero _))
        | succ n₃ =>
          rcases h with ⟨rfl, rfl⟩
          have hterm : evalVarX86Step t_var { pc := 2, acc := acc + 1 + 1 } =
              .terminated (.normal (acc + 3)) := by
            change StepResult.terminated (.normal (acc + 1 + 1 + 1)) =
              StepResult.terminated (.normal (acc + 3))
            have hadd : acc + 1 + 1 + 1 = acc + 3 := by omega
            rw [hadd]
          exact ReachesPrefix.step (n₃ + 2)
            (VarState.mk 0 acc) (VarState.mk 1 (acc + 1)) () [()]
            (.terminated (.normal (acc + 3))) rfl
            (ReachesPrefix.step (n₃ + 1)
              (VarState.mk 1 (acc + 1)) (VarState.mk 2 (acc + 1 + 1)) () []
              (.terminated (.normal (acc + 3))) rfl
              (ReachesPrefix.terminated n₃ (VarState.mk 2 (acc + 1 + 1))
                (.normal (acc + 3)) hterm))

/-- At `steps = 1` and `steps = 2`, `t_var` returns `PrefixOutcome.incomplete`,
    whereas `s_var` has already terminated at `steps = 2`! -/
theorem s_var_vs_t_var_step_mismatch (acc : Nat) :
    ReachesPrefix VarX86Machine t_var 1 { pc := 0, acc := acc } [()]
      .incomplete ∧
    ReachesPrefix VarX86Machine t_var 2 { pc := 0, acc := acc } [(), ()]
      .incomplete ∧
    ReachesPrefix VarMirMachine s_var 2 { pc := 0, acc := acc } [()]
      (.terminated (.normal (acc + 3))) ∧
    (∀ tr,
      ¬ ReachesPrefix VarMirMachine s_var 2 { pc := 0, acc := acc }
          tr .incomplete) := by
  refine ⟨(t_var_reaches_iff 1 acc [()] .incomplete).mpr ⟨rfl, rfl⟩,
          (t_var_reaches_iff 2 acc [(), ()] .incomplete).mpr ⟨rfl, rfl⟩,
          (s_var_reaches_iff 2 acc [()] (.terminated (.normal (acc + 3)))).mpr
            ⟨rfl, rfl⟩,
          ?_⟩
  intro tr h
  have h2 := (s_var_reaches_iff 2 acc tr .incomplete).mp h
  cases h2.2

/-- Because silent internal step counts (`List Unit`) differ when 1 MIR step
    expands to 3 x86 steps, we project observation traces to `Unit` (external
    I/O trace) so that any failure is purely due to `steps` synchronization. -/
def collapseUnitTrace (M : SmallStepMachine Prog State Unit Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := PrefixOutcome Val
  sem p q := {
    defined :=
      M.initState p q.init →
        ∀ tr out, ReachesPrefix M p q.steps q.init tr out → out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ∃ tr, ReachesPrefix M p q.steps q.init tr out
  }

def VarMirCollapsedLang : Language := collapseUnitTrace VarMirMachine
def VarX86CollapsedLang : Language := collapseUnitTrace VarX86Machine

/-- Naive 1-to-1 lockstep `TotalBehaviorCodec` mapping `q.steps ↦ q.steps`. -/
def lockstepCodec :
    TotalBehaviorCodec VarMirCollapsedLang VarX86CollapsedLang where
  encodeQuery q := q
  decodeQuery q := q
  decode_encode_query _ := rfl
  encodeOut o := o
  decodeOut o := o
  decode_encode_out _ := rfl
  encode_decode_out _ := rfl

/-- **Theorem (`lockstep_codec_fails_on_s_var`):**
    The 1-to-1 step-indexed `TotalBehaviorCodec` rejects the valid variable-step
    lowering `s_var → t_var` because at `steps = 2`, `t_var` produces
    `PrefixOutcome.incomplete` while `s_var` has already terminated! -/
theorem lockstep_codec_fails_on_s_var :
    ¬ Compiles VarMirCollapsedLang VarX86CollapsedLang
        lockstepCodec.toMorphism s_var t_var := by
  intro hcomp
  let q₂ : ExecQuery VarState := { init := { pc := 0, acc := 0 }, steps := 2 }
  have hdef_src :
      (lockstepCodec.toMorphism
        (VarMirCollapsedLang.sem s_var) q₂).defined := by
    intro _ tr out hr
    have h2 := (s_var_reaches_iff 2 0 tr out).mp hr
    rw [h2.2]
    exact True.intro
  rcases hcomp q₂ hdef_src with ⟨hdef_tgt, hval_tgt⟩
  have ht2 : (VarX86CollapsedLang.sem t_var q₂).val hdef_tgt .incomplete := by
    exact ⟨rfl, [(), ()],
      (t_var_reaches_iff 2 0 [(), ()] .incomplete).mpr ⟨rfl, rfl⟩⟩
  have hs2 := hval_tgt .incomplete ht2
  rcases hs2.2 with ⟨tr, hr_src⟩
  exact (s_var_vs_t_var_step_mismatch 0).2.2.2 tr hr_src

/-- Second 2-statement source program `s_fast`:
    Statement 0 is `Downcast` ($k = 0$) and Statement 1 is `RetNow` ($k = 1$).
    `s_fast` takes 2 source steps to terminate, while
    `t_fast = compileVarProg s_fast` (`[.retNow]`) terminates in `1` target
    step! -/
def s_fast : VarMirProg := [.downcast, .retNow]
def t_fast : VarX86Prog := compileVarProg s_fast

/-- **Theorem (`no_state_independent_step_map_for_variable_lowering`):**
    No state-independent query step projection `stepMap : Nat → Nat` that maps
    `PrefixOutcome.incomplete` to `PrefixOutcome.incomplete` and `.terminated`
    to `.terminated` can simultaneously validate both `s_fast → t_fast`
    ($2$ source steps $\to 1$ target step) and `s_var → t_var` ($2$ source steps
    $\to 3$ target steps):
    - At target budget `steps = 1`, `t_fast` has already terminated, forcing
      `stepMap 1 ≥ 2`.
    - At target budget `steps = 1`, `t_var` is still `.incomplete`, whereas
      `s_var` has terminated for all `m ≥ 2`, forcing `stepMap 1 < 2`. -/
theorem no_state_independent_step_map_for_variable_lowering
    (stepMap : Nat → Nat) :
    let π_step (b : VarMirCollapsedLang.Behavior) :
        VarX86CollapsedLang.Behavior :=
      fun q =>
        let p := b { init := q.init, steps := stepMap q.steps }
        { defined := p.defined, val := p.val }
    ¬ (Compiles VarMirCollapsedLang VarX86CollapsedLang π_step
         s_fast t_fast ∧
       Compiles VarMirCollapsedLang VarX86CollapsedLang π_step
         s_var t_var) := by
  intro π_step ⟨hfast, hvar⟩
  let q₁ : ExecQuery VarState := { init := { pc := 0, acc := 0 }, steps := 1 }
  -- 1. Evaluate `s_var` at `stepMap 1`: since `t_var` at `steps = 1` is
  -- `.incomplete`, `s_var` at `stepMap 1` must also produce `.incomplete`.
  have hdef_var :
      (VarMirCollapsedLang.sem s_var
        ⟨{ pc := 0, acc := 0 }, stepMap 1⟩).defined := by
    intro _ tr out hr
    have hiff := (s_var_reaches_iff (stepMap 1) 0 tr out).mp hr
    revert hiff
    cases stepMap 1 with
    | zero => intro h; rw [h.2]; exact True.intro
    | succ m₁ =>
      cases m₁ with
      | zero => intro h; rw [h.2]; exact True.intro
      | succ m₂ => intro h; rw [h.2]; exact True.intro
  rcases hvar q₁ hdef_var with ⟨hdef_tvar, hval_tvar⟩
  have htvar1 : (VarX86CollapsedLang.sem t_var q₁).val hdef_tvar .incomplete :=
    ⟨rfl, [()], (t_var_reaches_iff 1 0 [()] .incomplete).mpr ⟨rfl, rfl⟩⟩
  rcases (hval_tvar .incomplete htvar1).2 with ⟨tr_v, hr_v⟩
  -- 2. Evaluate `s_fast` at `stepMap 1`: since `t_fast` at `steps = 1` is
  -- `.terminated`, `s_fast` at `stepMap 1` must produce `.terminated`.
  have hdef_fast :
      (VarMirCollapsedLang.sem s_fast
        ⟨{ pc := 0, acc := 0 }, stepMap 1⟩).defined := by
    intro _ tr out hr
    cases h_m : stepMap 1 with
    | zero =>
      rw [h_m] at hr
      rw [(reachesPrefix_varMir_zero hr).2]
      exact True.intro
    | succ m₁ =>
      rw [h_m] at hr
      have h₁ := reachesPrefix_varMir_succ hr
      dsimp [evalVarMirStep, s_fast] at h₁
      rcases h₁ with ⟨tr₁, _, hr₁⟩
      cases m₁ with
      | zero =>
        rw [(reachesPrefix_varMir_zero hr₁).2]
        exact True.intro
      | succ m₂ =>
        have h₂ := reachesPrefix_varMir_succ hr₁
        dsimp [evalVarMirStep, s_fast] at h₂
        rw [h₂.2]
        exact True.intro
  rcases hfast q₁ hdef_fast with ⟨hdef_tfast, hval_tfast⟩
  have htfast1 : (VarX86CollapsedLang.sem t_fast q₁).val hdef_tfast
      (.terminated (.normal 0)) :=
    ⟨rfl, [], ReachesPrefix.terminated 0 (VarState.mk 0 0) (.normal 0) rfl⟩
  rcases (hval_tfast (.terminated (.normal 0)) htfast1).2 with ⟨tr_f, hr_f⟩
  -- 3. Case-split on `stepMap 1`: `< 2` refutes `hr_f`, `≥ 2` refutes `hr_v`.
  cases h_m : stepMap 1 with
  | zero =>
    rw [h_m] at hr_f
    have h0 := (reachesPrefix_varMir_zero hr_f).2
    cases h0
  | succ m₁ =>
    cases m₁ with
    | zero =>
      rw [h_m] at hr_f
      have h₁ := reachesPrefix_varMir_succ hr_f
      dsimp [evalVarMirStep, s_fast] at h₁
      rcases h₁ with ⟨tr₁, _, hr₁⟩
      have h0 := (reachesPrefix_varMir_zero hr₁).2
      cases h0
    | succ m₂ =>
      rw [h_m] at hr_v
      have h2 := (s_var_reaches_iff (m₂ + 2) 0 tr_v .incomplete).mp hr_v
      cases h2.2

/-!
## 3. Architecture A — Bounded-Dilation Codec (`DilationCodec`)

Architecture A retains `ExecQuery State` (`init` + `steps`) as the language
query type and generalizes `BehaviorCodec` to a `DilationCodec` equipped with a
monotone, unbounded step-dilation window `[srcFloor n, srcCeil n]`.
-/

/-- A step-dilated behavior codec between step-indexed languages `L₁`
    (`Query = ExecQuery State₁`) and `L₂` (`Query = ExecQuery State₂`). -/
structure DilationCodec (State₁ Out₁ State₂ Out₂ : Type) where
  encodeInit : State₁ → State₂
  decodeInit : State₂ → State₁
  decode_encode_init : ∀ s₁, decodeInit (encodeInit s₁) = s₁
  encodeOut : Out₁ → Out₂
  decodeOut : Out₂ → Out₁
  decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = o₁
  encode_decode_out : ∀ o₂, encodeOut (decodeOut o₂) = o₂
  srcFloor : Nat → Nat
  srcCeil : Nat → Nat
  floor_le_ceil : ∀ n, srcFloor n ≤ srcCeil n
  floor_mono : ∀ ⦃n₁ n₂⦄, n₁ ≤ n₂ → srcFloor n₁ ≤ srcFloor n₂
  ceil_mono : ∀ ⦃n₁ n₂⦄, n₁ ≤ n₂ → srcCeil n₁ ≤ srcCeil n₂
  floor_unbounded : ∀ M, ∃ N, ∀ n, N ≤ n → M ≤ srcFloor n

/-- Induced behavior morphism of a `DilationCodec`:
    - `defined`: requires source definedness across every source step budget
      `m ∈ [srcFloor q₂.steps, srcCeil q₂.steps]`.
    - `val`: requires the decoded target outcome `c.decodeOut o₂` to be matched
      by the source at some source step budget `m` within the dilation window
      `[srcFloor q₂.steps, srcCeil q₂.steps]`. -/
def DilationCodec.toMorphism {State₁ Out₁ State₂ Out₂ : Type}
    (c : DilationCodec State₁ Out₁ State₂ Out₂)
    (b : Behavior (ExecQuery State₁) Out₁) :
    Behavior (ExecQuery State₂) Out₂ :=
  fun q₂ => {
    defined :=
      ∀ m, c.srcFloor q₂.steps ≤ m → m ≤ c.srcCeil q₂.steps →
        (b ⟨c.decodeInit q₂.init, m⟩).defined
    val := fun h o₂ =>
      ∃ (m : Nat) (hlo : c.srcFloor q₂.steps ≤ m)
        (hhi : m ≤ c.srcCeil q₂.steps),
        (b ⟨c.decodeInit q₂.init, m⟩).val (h m hlo hhi) (c.decodeOut o₂)
  }

/-- `DilationCodec.toMorphism` is monotone with zero axioms. -/
theorem DilationCodec.monotone_toMorphism {State₁ Out₁ State₂ Out₂ : Type}
    (c : DilationCodec State₁ Out₁ State₂ Out₂) :
    Monotone c.toMorphism := by
  intro b₁ b₂ hle q₂ hdef₂
  refine ⟨fun m hlo hhi =>
    (hle ⟨c.decodeInit q₂.init, m⟩ (hdef₂ m hlo hhi)).1, ?_⟩
  intro o₂ ⟨m, hlo, hhi, hval₁⟩
  rcases hle ⟨c.decodeInit q₂.init, m⟩ (hdef₂ m hlo hhi) with ⟨hdef₁_m, hsub⟩
  exact ⟨m, hlo, hhi, hsub (c.decodeOut o₂) hval₁⟩

/-- Identity `DilationCodec` (`srcFloor n = n`, `srcCeil n = n`). -/
def DilationCodec.id (State Out : Type) :
    DilationCodec State Out State Out where
  encodeInit s := s
  decodeInit s := s
  decode_encode_init _ := rfl
  encodeOut o := o
  decodeOut o := o
  decode_encode_out _ := rfl
  encode_decode_out _ := rfl
  srcFloor n := n
  srcCeil n := n
  floor_le_ceil n := Nat.le_refl n
  floor_mono _ _ h := h
  ceil_mono _ _ h := h
  floor_unbounded M := ⟨M, fun _ h => h⟩

/-- Composition of two `DilationCodec`s. -/
def DilationCodec.comp {State₁ Out₁ State₂ Out₂ State₃ Out₃ : Type}
    (c₂ : DilationCodec State₂ Out₂ State₃ Out₃)
    (c₁ : DilationCodec State₁ Out₁ State₂ Out₂) :
    DilationCodec State₁ Out₁ State₃ Out₃ where
  encodeInit s₁ := c₂.encodeInit (c₁.encodeInit s₁)
  decodeInit s₃ := c₁.decodeInit (c₂.decodeInit s₃)
  decode_encode_init s₁ := by
    rw [c₂.decode_encode_init, c₁.decode_encode_init]
  encodeOut o₁ := c₂.encodeOut (c₁.encodeOut o₁)
  decodeOut o₃ := c₁.decodeOut (c₂.decodeOut o₃)
  decode_encode_out o₁ := by
    rw [c₂.decode_encode_out, c₁.decode_encode_out]
  encode_decode_out o₃ := by
    rw [c₁.encode_decode_out, c₂.encode_decode_out]
  srcFloor n := c₁.srcFloor (c₂.srcFloor n)
  srcCeil n := c₁.srcCeil (c₂.srcCeil n)
  floor_le_ceil n :=
    Nat.le_trans
      (c₁.floor_mono (c₂.floor_le_ceil n))
      (c₁.floor_le_ceil (c₂.srcCeil n))
  floor_mono _ _ h := c₁.floor_mono (c₂.floor_mono h)
  ceil_mono _ _ h := c₁.ceil_mono (c₂.ceil_mono h)
  floor_unbounded M := by
    rcases c₁.floor_unbounded M with ⟨N₁, hN₁⟩
    rcases c₂.floor_unbounded N₁ with ⟨N₂, hN₂⟩
    exact ⟨N₂, fun n hn => hN₁ (c₂.srcFloor n) (hN₂ n hn)⟩

/-- Lax functoriality of `DilationCodec.comp`:
    `c₂.toMorphism (c₁.toMorphism b) ≤ (c₂.comp c₁).toMorphism b`. -/
theorem DilationCodec.comp_toMorphism_le
    {State₁ Out₁ State₂ Out₂ State₃ Out₃ : Type}
    (c₂ : DilationCodec State₂ Out₂ State₃ Out₃)
    (c₁ : DilationCodec State₁ Out₁ State₂ Out₂)
    (b : Behavior (ExecQuery State₁) Out₁) :
    c₂.toMorphism (c₁.toMorphism b) ≤ (c₂.comp c₁).toMorphism b := by
  intro q₃ hdef_comp
  have hdef_seq : (c₂.toMorphism (c₁.toMorphism b) q₃).defined := by
    intro m₂ hlo₂ hhi₂ m₁ hlo₁ hhi₁
    exact hdef_comp m₁
      (Nat.le_trans (c₁.floor_mono hlo₂) hlo₁)
      (Nat.le_trans hhi₁ (c₁.ceil_mono hhi₂))
  refine ⟨hdef_seq, ?_⟩
  intro o₃ ⟨m₂, hlo₂, hhi₂, m₁, hlo₁, hhi₁, hval⟩
  exact ⟨m₁,
    Nat.le_trans (c₁.floor_mono hlo₂) hlo₁,
    Nat.le_trans hhi₁ (c₁.ceil_mono hhi₂),
    hval⟩

/-- Transitive compilation under `DilationCodec.comp`. -/
theorem DilationCodec.compiles_comp
    {State₁ Out₁ State₂ Out₂ State₃ Out₃ : Type}
    (c₁ : DilationCodec State₁ Out₁ State₂ Out₂)
    (c₂ : DilationCodec State₂ Out₂ State₃ Out₃)
    {b₁ : Behavior (ExecQuery State₁) Out₁}
    {b₂ : Behavior (ExecQuery State₂) Out₂}
    {b₃ : Behavior (ExecQuery State₃) Out₃}
    (h₁₂ : b₂ ≤ c₁.toMorphism b₁)
    (h₂₃ : b₃ ≤ c₂.toMorphism b₂) :
    b₃ ≤ (c₂.comp c₁).toMorphism b₁ :=
  Preorder.le_trans h₂₃
    (Preorder.le_trans (c₂.monotone_toMorphism h₁₂)
      (DilationCodec.comp_toMorphism_le c₂ c₁ b₁))

/-- Concrete `DilationCodec` for the variable-step pass ($k = 0$ and $k = 3$):
    `srcFloor n = n / 3` and `srcCeil n = n + 1`. -/
def varDilationCodec :
    DilationCodec VarState (PrefixOutcome Nat)
      VarState (PrefixOutcome Nat) where
  encodeInit s := s
  decodeInit s := s
  decode_encode_init _ := rfl
  encodeOut o := o
  decodeOut o := o
  decode_encode_out _ := rfl
  encode_decode_out _ := rfl
  srcFloor n := n / 3
  srcCeil n := n + 1
  floor_le_ceil n := by omega
  floor_mono _ _ h := by omega
  ceil_mono _ _ h := by omega
  floor_unbounded M := ⟨3 * M, fun n hn => by omega⟩

/-- Every step of `loopX86Prog` (`[.jmpSelf]`) from `⟨0, acc⟩` stays at
    `⟨0, acc⟩` and finishes in `PrefixOutcome.incomplete`. -/
theorem loopX86Prog_reaches_incomplete (n : Nat) (acc : Nat) :
    ∃ tr,
      ReachesPrefix VarX86Machine loopX86Prog n
        { pc := 0, acc := acc } tr .incomplete := by
  induction n with
  | zero => exact ⟨[], ReachesPrefix.zero _⟩
  | succ k ih =>
    rcases ih with ⟨tr, hr⟩
    exact ⟨() :: tr,
      ReachesPrefix.step k (VarState.mk 0 acc) (VarState.mk 0 acc)
        () tr .incomplete rfl hr⟩

/-- **Theorem (`dilationCodec_rejects_loopCodegen`):**
    For *every* `DilationCodec` `c` (with any dilation bounds satisfying
    `floor_unbounded`) that maps `⟨0, 0⟩` to `⟨0, 0⟩` and `.incomplete` to
    `.incomplete`, `c` strictly rejects compiling `s_var` to `loopX86Prog`
    (`bb0: jmp bb0`). -/
theorem dilationCodec_rejects_loopCodegen
    (c : DilationCodec VarState (PrefixOutcome Nat)
      VarState (PrefixOutcome Nat))
    (hinit : c.decodeInit { pc := 0, acc := 0 } = { pc := 0, acc := 0 })
    (hinc : c.decodeOut .incomplete = .incomplete) :
    ¬ Compiles VarMirCollapsedLang VarX86CollapsedLang
        c.toMorphism s_var loopX86Prog := by
  intro hcomp
  rcases c.floor_unbounded 2 with ⟨N, hN⟩
  let q₂ : ExecQuery VarState := { init := { pc := 0, acc := 0 }, steps := N }
  have hdef_src :
      (c.toMorphism (VarMirCollapsedLang.sem s_var) q₂).defined := by
    intro m _ _ _ tr out hr
    rw [hinit] at hr
    have hiff := (s_var_reaches_iff m 0 tr out).mp hr
    revert hiff
    cases m with
    | zero => intro h; rw [h.2]; exact True.intro
    | succ m₁ =>
      cases m₁ with
      | zero => intro h; rw [h.2]; exact True.intro
      | succ m₂ => intro h; rw [h.2]; exact True.intro
  rcases hcomp q₂ hdef_src with ⟨hdef_loop, hval_loop⟩
  have hloop_inc :
      (VarX86CollapsedLang.sem loopX86Prog q₂).val hdef_loop .incomplete :=
    ⟨rfl, loopX86Prog_reaches_incomplete N 0⟩
  rcases hval_loop .incomplete hloop_inc with ⟨m, hlo, _, _, tr, hr_src⟩
  rw [hinit, hinc] at hr_src
  have hm2 : 2 ≤ m := Nat.le_trans (hN N (Nat.le_refl N)) hlo
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have h2 := (s_var_reaches_iff (k + 2) 0 tr .incomplete).mp hr_src
  cases h2.2

/-- **Theorem (`dilationCodec_verifies_s_var`):**
    `varDilationCodec` cleanly verifies the variable-step ($k = 0$ and $k = 3$)
    compilation `s_var → t_var`
    (`Compiles VarMirCollapsedLang VarX86CollapsedLang
    varDilationCodec.toMorphism s_var t_var`)! -/
theorem dilationCodec_verifies_s_var :
    Compiles VarMirCollapsedLang VarX86CollapsedLang
      varDilationCodec.toMorphism s_var t_var := by
  intro q₂ hdef_src
  rcases q₂ with ⟨⟨pc, acc⟩, n⟩
  have hdef_tgt : (VarX86CollapsedLang.sem t_var ⟨⟨pc, acc⟩, n⟩).defined := by
    intro hpc tr out hr
    dsimp [VarX86Machine] at hpc
    subst hpc
    have hiff := (t_var_reaches_iff n acc tr out).mp hr
    revert hiff
    cases n with
    | zero => intro h; rw [h.2]; exact True.intro
    | succ n₁ =>
      cases n₁ with
      | zero => intro h; rw [h.2]; exact True.intro
      | succ n₂ =>
        cases n₂ with
        | zero => intro h; rw [h.2]; exact True.intro
        | succ n₃ => intro h; rw [h.2]; exact True.intro
  refine ⟨hdef_tgt, ?_⟩
  intro out ⟨hpc, tr, hr⟩
  dsimp [VarX86Machine] at hpc
  subst hpc
  have hiff := (t_var_reaches_iff n acc tr out).mp hr
  revert hiff
  cases n with
  | zero =>
    intro ⟨_, hout⟩
    subst hout
    have hlo0 : varDilationCodec.srcFloor 0 ≤ 0 := Nat.le_refl 0
    have hhi0 : 0 ≤ varDilationCodec.srcCeil 0 := Nat.zero_le 1
    refine ⟨0, hlo0, hhi0, rfl, [], ?_⟩
    exact (s_var_reaches_iff 0 acc [] .incomplete).mpr ⟨rfl, rfl⟩
  | succ n₁ =>
    cases n₁ with
    | zero =>
      intro ⟨_, hout⟩
      subst hout
      have hlo1 : varDilationCodec.srcFloor 1 ≤ 1 := Nat.zero_le 1
      have hhi1 : 1 ≤ varDilationCodec.srcCeil 1 := Nat.le_succ 1
      refine ⟨1, hlo1, hhi1, rfl, [()], ?_⟩
      exact (s_var_reaches_iff 1 acc [()] .incomplete).mpr ⟨rfl, rfl⟩
    | succ n₂ =>
      cases n₂ with
      | zero =>
        intro ⟨_, hout⟩
        subst hout
        have hlo2 : varDilationCodec.srcFloor 2 ≤ 1 := Nat.zero_le 1
        have hhi2 : 1 ≤ varDilationCodec.srcCeil 2 :=
          Nat.le_trans (Nat.le_succ 1) (Nat.le_succ 2)
        refine ⟨1, hlo2, hhi2, rfl, [()], ?_⟩
        exact (s_var_reaches_iff 1 acc [()] .incomplete).mpr ⟨rfl, rfl⟩
      | succ n₃ =>
        intro ⟨_, hout⟩
        subst hout
        have hlo3 : (n₃ + 3) / 3 ≤ n₃ + 4 := by omega
        have hhi3 : n₃ + 4 ≤ (n₃ + 3) + 1 := by omega
        refine ⟨n₃ + 4, hlo3, hhi3, rfl, [()], ?_⟩
        exact (s_var_reaches_iff (n₃ + 2 + 2) acc [()]
          (.terminated (.normal (acc + 3)))).mpr ⟨rfl, rfl⟩

/-!
## 4. Architecture B — Eventual Semantics (`EventualBehaviorOf`)

Through the lens of `model-refinement`, `steps : Nat` in `ExecQuery State` is an
internal operational fuel coordinate, not a semantic query parameter of the
language interface. Encapsulating `steps : Nat` inside `EventualBehaviorOf`:
1. `Query := State` (only the initial state).
2. `Out := EventualOut Obs Val`, distinguishing eventual termination
   (`.terminated trace term`) from divergence (`.diverges`).
3. `.defined` universally quantifies over all finite step budgets `n : Nat`,
   preserving exact all-prefix UB-freedom.
4. `TotalBehaviorCodec` (and `PartialBehaviorCodec`) translates only initial
   states and outcomes—eliminating step-count synchronization completely while
   requiring **zero `Classical.choice`** and **zero coinduction**.
-/

/-- Explicit canary proving that existential quantification `∃ n : Nat, P n` and
    `∀ n : Nat, ∃ tr, Q n tr` in `Prop` require **zero `Classical.choice`**. -/
theorem exists_nat_no_choice_canary (P : Nat → Prop) (k : Nat) (hk : P k) :
    ∃ n : Nat, P n :=
  ⟨k, hk⟩

/-- Observable outcome of a step-decoupled execution from an initial state:
    - `terminated trace term`: execution reaches `.terminated term` at some
      finite step budget `n : Nat` with accumulated trace `trace`.
    - `diverges`: at every finite step budget `n : Nat`, execution has a
      running prefix of length `n` (`PrefixOutcome.incomplete`). -/
inductive EventualOut (Obs Val : Type) where
  | terminated (trace : List Obs) (term : TerminationKind Val)
  | diverges

/-- Step-decoupled partial behavior of program `p` in small-step machine `M`:
    - `defined`: all-prefix safety across *every* finite step budget `n : Nat`.
    - `val`: reachable `EventualOut Obs Val` outcomes from `init`. -/
def EventualBehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    State → Partial (EventualOut Obs Val → Prop) :=
  fun init => {
    defined :=
      M.initState p init →
        ∀ (n : Nat) (tr : List Obs) (out : PrefixOutcome Val),
          ReachesPrefix M p n init tr out →
          out.isSafe
    val := fun _ ev =>
      M.initState p init ∧
      match ev with
      | .terminated tr term =>
        ∃ (n : Nat), ReachesPrefix M p n init tr (.terminated term)
      | .diverges =>
        ∀ (n : Nat), ∃ (tr : List Obs),
          ReachesPrefix M p n init tr .incomplete
  }

/-- Package a `SmallStepMachine` as an eventual-outcome `Language` with
    `Query := State` and `Out := EventualOut Obs Val`. -/
def SmallStepMachine.toEventualLanguage
    (M : SmallStepMachine Prog State Obs Val) : Language where
  Prog := Prog
  Query := State
  Out := EventualOut Obs Val
  sem := EventualBehaviorOf M

/-- **Theorem (`eventual_wellFormed_iff_prefix_wellFormed`):**
    Unconditional well-formedness (`WellFormed`) in `M.toEventualLanguage` is
    logically equivalent to unconditional all-prefix well-formedness in
    `M.toLanguage`. Moving `steps : Nat` out of `Query` loses zero safety
    guarantees! -/
theorem eventual_wellFormed_iff_prefix_wellFormed
    (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    EventualBehaviorOf M p ≤ (M.toEventualLanguage).WellFormed ↔
      BehaviorOf M p ≤ (M.toLanguage).WellFormed := by
  constructor
  · intro hev q _
    refine ⟨fun hinit tr out hr => ?_, fun _ _ => True.intro⟩
    rcases hev q.init True.intro with ⟨hdef, _⟩
    exact hdef hinit q.steps tr out hr
  · intro hpfx init _
    refine ⟨fun hinit n tr out hr => ?_, fun _ _ => True.intro⟩
    rcases hpfx ⟨init, n⟩ True.intro with ⟨hdef, _⟩
    exact hdef hinit tr out hr

/-- Collapsed-trace eventual language (where internal step ticks `Unit` are
    silent). -/
inductive SilentEventualOut (Val : Type) where
  | terminated (term : TerminationKind Val)
  | diverges

def SilentEventualBehaviorOf (M : SmallStepMachine Prog State Unit Val)
    (p : Prog) : State → Partial (SilentEventualOut Val → Prop) :=
  fun init => {
    defined :=
      M.initState p init →
        ∀ (n : Nat) (tr : List Unit) (out : PrefixOutcome Val),
          ReachesPrefix M p n init tr out →
          out.isSafe
    val := fun _ ev =>
      M.initState p init ∧
      match ev with
      | .terminated term =>
        ∃ (n : Nat) (tr : List Unit),
          ReachesPrefix M p n init tr (.terminated term)
      | .diverges =>
        ∀ (n : Nat), ∃ (tr : List Unit),
          ReachesPrefix M p n init tr .incomplete
  }

def toSilentEventualLanguage (M : SmallStepMachine Prog State Unit Val) :
    Language where
  Prog := Prog
  Query := State
  Out := SilentEventualOut Val
  sem := SilentEventualBehaviorOf M

def VarMirEventualLang : Language := toSilentEventualLanguage VarMirMachine
def VarX86EventualLang : Language := toSilentEventualLanguage VarX86Machine

/-- Under Architecture B, the codec between `VarMirEventualLang` and
    `VarX86EventualLang` is the trivial identity codec on `VarState` and
    `SilentEventualOut Nat`—requiring **zero step-dilation arithmetic**! -/
def eventualVarCodec :
    TotalBehaviorCodec VarMirEventualLang VarX86EventualLang where
  encodeQuery q := q
  decodeQuery q := q
  decode_encode_query _ := rfl
  encodeOut o := o
  decodeOut o := o
  decode_encode_out _ := rfl
  encode_decode_out _ := rfl

/-- **Theorem (`eventual_rejects_loopCodegen`):**
    Architecture B (`SilentEventualBehaviorOf` + `eventualVarCodec`) strictly
    rejects compiling `s_var` to `loopX86Prog` (`bb0: jmp bb0`), because
    `loopX86Prog` produces `.diverges` while `s_var` terminates at `n = 2`. -/
theorem eventual_rejects_loopCodegen :
    ¬ Compiles VarMirEventualLang VarX86EventualLang
        eventualVarCodec.toMorphism s_var loopX86Prog := by
  intro hcomp
  let init₀ : VarState := { pc := 0, acc := 0 }
  have hdef_src :
      (eventualVarCodec.toMorphism
        (VarMirEventualLang.sem s_var) init₀).defined := by
    intro _ n tr out hr
    have hiff := (s_var_reaches_iff n 0 tr out).mp hr
    revert hiff
    cases n with
    | zero => intro h; rw [h.2]; exact True.intro
    | succ n₁ =>
      cases n₁ with
      | zero => intro h; rw [h.2]; exact True.intro
      | succ n₂ => intro h; rw [h.2]; exact True.intro
  rcases hcomp init₀ hdef_src with ⟨hdef_loop, hval_loop⟩
  have hloop_div :
      (VarX86EventualLang.sem loopX86Prog init₀).val hdef_loop .diverges :=
    ⟨rfl, fun n => loopX86Prog_reaches_incomplete n 0⟩
  have hs_div := hval_loop .diverges hloop_div
  dsimp [eventualVarCodec, VarMirEventualLang, toSilentEventualLanguage,
    SilentEventualBehaviorOf] at hs_div
  rcases hs_div.2 2 with ⟨tr, hr2⟩
  exact (s_var_vs_t_var_step_mismatch 0).2.2.2 tr hr2

/-- **Theorem (`eventual_verifies_s_var`):**
    Architecture B (`SilentEventualBehaviorOf` + `eventualVarCodec`) cleanly
    verifies both the `k = 0, 3` variable-step compilation `s_var → t_var` AND
    the `k = 0, 1` compilation `s_fast → t_fast` under the **exact same**
    step-free `eventualVarCodec`! -/
theorem eventual_verifies_s_var :
    Compiles VarMirEventualLang VarX86EventualLang
      eventualVarCodec.toMorphism s_var t_var := by
  intro ⟨pc, acc⟩ hdef_src
  have hdef_tgt : (VarX86EventualLang.sem t_var ⟨pc, acc⟩).defined := by
    intro hpc n tr out hr
    dsimp [VarX86Machine] at hpc
    subst hpc
    have hiff := (t_var_reaches_iff n acc tr out).mp hr
    revert hiff
    cases n with
    | zero => intro h; rw [h.2]; exact True.intro
    | succ n₁ =>
      cases n₁ with
      | zero => intro h; rw [h.2]; exact True.intro
      | succ n₂ =>
        cases n₂ with
        | zero => intro h; rw [h.2]; exact True.intro
        | succ n₃ => intro h; rw [h.2]; exact True.intro
  refine ⟨hdef_tgt, ?_⟩
  intro ev ⟨hpc, hev⟩
  dsimp [VarX86Machine] at hpc
  subst hpc
  cases ev with
  | terminated term =>
    rcases hev with ⟨n, tr, hr⟩
    have hiff := (t_var_reaches_iff n acc tr (.terminated term)).mp hr
    revert hiff
    cases n with
    | zero => intro ⟨_, h⟩; cases h
    | succ n₁ =>
      cases n₁ with
      | zero => intro ⟨_, h⟩; cases h
      | succ n₂ =>
        cases n₂ with
        | zero => intro ⟨_, h⟩; cases h
        | succ n₃ =>
          intro ⟨_, h⟩
          injection h with hterm
          subst hterm
          dsimp [eventualVarCodec, TotalBehaviorCodec.toMorphism,
            VarMirEventualLang, toSilentEventualLanguage,
            SilentEventualBehaviorOf]
          exact ⟨rfl, 2, [()],
            (s_var_reaches_iff 2 acc [()]
              (.terminated (.normal (acc + 3)))).mpr ⟨rfl, rfl⟩⟩
  | diverges =>
    rcases hev 3 with ⟨tr, hr3⟩
    have hiff := (t_var_reaches_iff 3 acc tr .incomplete).mp hr3
    cases hiff.2

theorem eventual_verifies_s_fast :
    Compiles VarMirEventualLang VarX86EventualLang
      eventualVarCodec.toMorphism s_fast t_fast := by
  intro ⟨pc, acc⟩ _
  have hdef_tgt : (VarX86EventualLang.sem t_fast ⟨pc, acc⟩).defined := by
    intro hpc n tr out hr
    dsimp [VarX86Machine] at hpc
    subst hpc
    cases n with
    | zero =>
      rw [(reachesPrefix_varX86_zero hr).2]
      exact True.intro
    | succ k =>
      have hk := reachesPrefix_varX86_succ hr
      dsimp [evalVarX86Step, t_fast, compileVarProg, s_fast,
        compileVarStmt] at hk
      rw [hk.2]
      exact True.intro
  refine ⟨hdef_tgt, ?_⟩
  intro ev ⟨hpc, hev⟩
  dsimp [VarX86Machine] at hpc
  subst hpc
  cases ev with
  | terminated term =>
    rcases hev with ⟨n, tr, hr⟩
    cases n with
    | zero =>
      have h0 := (reachesPrefix_varX86_zero hr).2
      cases h0
    | succ k =>
      have hk := reachesPrefix_varX86_succ hr
      dsimp [evalVarX86Step, t_fast, compileVarProg, s_fast,
        compileVarStmt] at hk
      injection hk.2 with hterm
      subst hterm
      dsimp [eventualVarCodec, TotalBehaviorCodec.toMorphism,
        VarMirEventualLang, toSilentEventualLanguage, SilentEventualBehaviorOf]
      exact ⟨rfl, 2, [()],
        ReachesPrefix.step 1
          (VarState.mk 0 acc) (VarState.mk 1 acc) () []
          (.terminated (.normal acc)) rfl
          (ReachesPrefix.terminated 0 (VarState.mk 1 acc)
            (.normal acc) rfl)⟩
  | diverges =>
    rcases hev 1 with ⟨tr, hr1⟩
    have hk := reachesPrefix_varX86_succ hr1
    dsimp [evalVarX86Step, t_fast, compileVarProg, s_fast,
      compileVarStmt] at hk
    cases hk.2

/-!
## 5. Non-Surjectivity Obstruction and `PartialBehaviorCodec`

On real hardware (`X86Val` / `X86AbiVal`), an 8-bit or 64-bit register holding a
Rust `bool` can contain bit patterns `2 .. 2^64 - 1` that do not correspond to
any valid `MirVal.bool b`. We first prove that no total `(encodeOut, decodeOut)`
can satisfy `∀ o₂, encodeOut (decodeOut o₂) = o₂` when `|L₂.Out| > |L₁.Out|`,
and then mechanize `PartialBehaviorCodec L₁ L₂`.
-/

/-- **Theorem (`no_total_section_for_bool_in_uint8`):**
    No pair of functions `encodeOut : Bool → UInt8` and
    `decodeOut : UInt8 → Bool` can satisfy
    `∀ o₂ : UInt8, encodeOut (decodeOut o₂) = o₂`. -/
theorem no_total_section_for_bool_in_uint8 :
    ¬ ∃ (encodeOut : Bool → UInt8) (decodeOut : UInt8 → Bool),
        ∀ (o₂ : UInt8), encodeOut (decodeOut o₂) = o₂ := by
  intro ⟨encodeOut, decodeOut, hsec⟩
  have h0 := hsec 0
  have h1 := hsec 1
  have h2 := hsec 2
  cases hb0 : decodeOut 0 <;>
    cases hb1 : decodeOut 1 <;>
    cases hb2 : decodeOut 2
  · rw [hb0] at h0; rw [hb1] at h1
    have h01 : (0 : UInt8) = 1 := h0.symm.trans h1
    revert h01; decide
  · rw [hb0] at h0; rw [hb1] at h1
    have h01 : (0 : UInt8) = 1 := h0.symm.trans h1
    revert h01; decide
  · rw [hb0] at h0; rw [hb2] at h2
    have h02 : (0 : UInt8) = 2 := h0.symm.trans h2
    revert h02; decide
  · rw [hb1] at h1; rw [hb2] at h2
    have h12 : (1 : UInt8) = 2 := h1.symm.trans h2
    revert h12; decide
  · rw [hb1] at h1; rw [hb2] at h2
    have h12 : (1 : UInt8) = 2 := h1.symm.trans h2
    revert h12; decide
  · rw [hb0] at h0; rw [hb2] at h2
    have h02 : (0 : UInt8) = 2 := h0.symm.trans h2
    revert h02; decide
  · rw [hb0] at h0; rw [hb1] at h1
    have h01 : (0 : UInt8) = 1 := h0.symm.trans h1
    revert h01; decide
  · rw [hb0] at h0; rw [hb1] at h1
    have h01 : (0 : UInt8) = 1 := h0.symm.trans h1
    revert h01; decide

/-- **Theorem (`no_total_section_for_bool_in_nat`):**
    No pair of functions `encodeOut : Bool → Nat` and `decodeOut : Nat → Bool`
    can satisfy `∀ o₂ : Nat, encodeOut (decodeOut o₂) = o₂`. -/
theorem no_total_section_for_bool_in_nat :
    ¬ ∃ (encodeOut : Bool → Nat) (decodeOut : Nat → Bool),
        ∀ (o₂ : Nat), encodeOut (decodeOut o₂) = o₂ := by
  intro ⟨encodeOut, decodeOut, hsec⟩
  have h0 := hsec 0
  have h1 := hsec 1
  have h2 := hsec 2
  cases hb0 : decodeOut 0 <;>
    cases hb1 : decodeOut 1 <;>
    cases hb2 : decodeOut 2
  · rw [hb0] at h0; rw [hb1] at h1
    have h01 : (0 : Nat) = 1 := h0.symm.trans h1; cases h01
  · rw [hb0] at h0; rw [hb1] at h1
    have h01 : (0 : Nat) = 1 := h0.symm.trans h1; cases h01
  · rw [hb0] at h0; rw [hb2] at h2
    have h02 : (0 : Nat) = 2 := h0.symm.trans h2; cases h02
  · rw [hb1] at h1; rw [hb2] at h2
    have h12 : (1 : Nat) = 2 := h1.symm.trans h2; cases h12
  · rw [hb1] at h1; rw [hb2] at h2
    have h12 : (1 : Nat) = 2 := h1.symm.trans h2; cases h12
  · rw [hb0] at h0; rw [hb2] at h2
    have h02 : (0 : Nat) = 2 := h0.symm.trans h2; cases h02
  · rw [hb0] at h0; rw [hb1] at h1
    have h01 : (0 : Nat) = 1 := h0.symm.trans h1; cases h01
  · rw [hb0] at h0; rw [hb1] at h1
    have h01 : (0 : Nat) = 1 := h0.symm.trans h1; cases h01

/-- Partial outcome behavior codec (`PartialBehaviorCodec L₁ L₂`):
    - `decodeOut : L₂.Out → Option L₁.Out` returns `some o₁` on valid target
      representations and `none` on invalid target bit patterns (such as
      `2..255` for a `bool` or `.stuck`).
    - `decode_encode_out`: `decodeOut` is a left inverse of `encodeOut`.
    - `encode_of_decode_some`: `decodeOut` is the exact partial inverse of
      `encodeOut` on its `some` domain, preventing two distinct target outcomes
      `o₂ ≠ o₂'` from decoding to the same `some o₁`. -/
structure PartialBehaviorCodec (L₁ L₂ : Language) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  encodeOut : L₁.Out → L₂.Out
  decodeOut : L₂.Out → Option L₁.Out
  decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  encode_of_decode_some : ∀ o₂ o₁, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂

/-- Induced behavior morphism of a `PartialBehaviorCodec`:
    At target query `q₂`, `toMorphism` preserves definedness of
    `b (c.decodeQuery q₂)` and permits a target outcome `o₂` if and only if
    `c.decodeOut o₂ = some o₁` for some source outcome `o₁` permitted by
    `b (c.decodeQuery q₂)`. -/
def PartialBehaviorCodec.toMorphism {L₁ L₂ : Language}
    (c : PartialBehaviorCodec L₁ L₂) (b : L₁.Behavior) : L₂.Behavior :=
  fun q₂ =>
    let p := b (c.decodeQuery q₂)
    { defined := p.defined
      val := fun h o₂ => ∃ o₁, c.decodeOut o₂ = some o₁ ∧ p.val h o₁ }

/-- Every `TotalBehaviorCodec` embeds into `PartialBehaviorCodec` with the exact
    same `toMorphism` (up to propositional equivalence). -/
def TotalBehaviorCodec.toPartialCodec {L₁ L₂ : Language}
    (c : TotalBehaviorCodec L₁ L₂) : PartialBehaviorCodec L₁ L₂ where
  encodeQuery := c.encodeQuery
  decodeQuery := c.decodeQuery
  decode_encode_query := c.decode_encode_query
  encodeOut := c.encodeOut
  decodeOut o₂ := some (c.decodeOut o₂)
  decode_encode_out o₁ := congrArg some (c.decode_encode_out o₁)
  encode_of_decode_some o₂ o₁ h := by
    injection h with h'
    rw [← h', c.encode_decode_out]

/-- **Theorem (`encodeOut_injective`):**
    `c.encodeOut` is injective. -/
theorem PartialBehaviorCodec.encodeOut_injective {L₁ L₂ : Language}
    (c : PartialBehaviorCodec L₁ L₂) :
    ∀ ⦃o₁ o₁' : L₁.Out⦄, c.encodeOut o₁ = c.encodeOut o₁' → o₁ = o₁' := by
  intro o₁ o₁' heq
  have h := congrArg c.decodeOut heq
  rw [c.decode_encode_out, c.decode_encode_out] at h
  injection h

/-- **Theorem (`decodeOut_injective_on_some`):**
    `c.decodeOut` is injective on `{ o₂ | (c.decodeOut o₂).isSome }`: two
    distinct target outcomes `o₂ ≠ o₂'` can never decode to the same
    `some o₁`. -/
theorem PartialBehaviorCodec.decodeOut_injective_on_some {L₁ L₂ : Language}
    (c : PartialBehaviorCodec L₁ L₂) :
    ∀ ⦃o₂ o₂' : L₂.Out⦄ ⦃o₁ : L₁.Out⦄,
      c.decodeOut o₂ = some o₁ →
      c.decodeOut o₂' = some o₁ →
      o₂ = o₂' := by
  intro o₂ o₂' o₁ h₁ h₂
  have he₁ := c.encode_of_decode_some o₂ o₁ h₁
  have he₂ := c.encode_of_decode_some o₂' o₁ h₂
  exact he₁.symm.trans he₂

/-- **Theorem (`invalid_target_out_rejected`):**
    If `c.decodeOut o₂ = none`, then `(c.toMorphism b q₂).val h o₂` is
    `False`. -/
theorem PartialBehaviorCodec.invalid_target_out_rejected {L₁ L₂ : Language}
    (c : PartialBehaviorCodec L₁ L₂) (b : L₁.Behavior) (q₂ : L₂.Query)
    (h : (c.toMorphism b q₂).defined) {o₂ : L₂.Out}
    (hnone : c.decodeOut o₂ = none) :
    ¬ (c.toMorphism b q₂).val h o₂ := by
  intro ⟨o₁, hsome, _⟩
  rw [hnone] at hsome
  cases hsome

/-- **Theorem (`compiles_rejects_invalid_target_out`):**
    If a source program `s` is defined at `c.decodeQuery q₂` and a target
    program `t` produces an invalid outcome `o₂` (`c.decodeOut o₂ = none`) at
    `q₂`, then `Compiles L₁ L₂ c.toMorphism s t` automatically rejects `t`! -/
theorem PartialBehaviorCodec.compiles_rejects_invalid_target_out
    {L₁ L₂ : Language} (c : PartialBehaviorCodec L₁ L₂)
    (s : L₁.Prog) (t : L₂.Prog) (q₂ : L₂.Query) (o₂ : L₂.Out)
    (hdef_src : (L₁.sem s (c.decodeQuery q₂)).defined)
    (ht_out : ∀ hdef_tgt : (L₂.sem t q₂).defined, (L₂.sem t q₂).val hdef_tgt o₂)
    (hnone : c.decodeOut o₂ = none) :
    ¬ Compiles L₁ L₂ c.toMorphism s t := by
  intro hcomp
  rcases hcomp q₂ hdef_src with ⟨hdef_tgt, hval⟩
  exact c.invalid_target_out_rejected (L₁.sem s) q₂ hdef_src hnone
    (hval o₂ (ht_out hdef_tgt))

/-- **Theorem (`monotone_toMorphism`):**
    `c.toMorphism` is monotone with respect to the refinement preorder. -/
theorem PartialBehaviorCodec.monotone_toMorphism {L₁ L₂ : Language}
    (c : PartialBehaviorCodec L₁ L₂) :
    Monotone c.toMorphism := by
  intro b₁ b₂ hle q₂ hdef₂
  rcases hle (c.decodeQuery q₂) hdef₂ with ⟨hdef₁, hsub⟩
  refine ⟨hdef₁, ?_⟩
  intro o₂ ⟨o₁, hdec, hval₁⟩
  exact ⟨o₁, hdec, hsub o₁ hval₁⟩

/-- **Theorem (`toMorphism_defined`):**
    `c.toMorphism` preserves definedness at every target query `q₂`. -/
theorem PartialBehaviorCodec.toMorphism_defined {L₁ L₂ : Language}
    (c : PartialBehaviorCodec L₁ L₂) (b : L₁.Behavior) (q₂ : L₂.Query) :
    (c.toMorphism b q₂).defined ↔ (b (c.decodeQuery q₂)).defined :=
  ⟨fun h => h, fun h => h⟩

/-- **Theorem (`toMorphism_encodeQuery_defined`):**
    At `c.encodeQuery q₁`, definedness of `c.toMorphism b` coincides with
    `(b q₁).defined`. -/
theorem PartialBehaviorCodec.toMorphism_encodeQuery_defined {L₁ L₂ : Language}
    (c : PartialBehaviorCodec L₁ L₂) (b : L₁.Behavior) (q₁ : L₁.Query) :
    (c.toMorphism b (c.encodeQuery q₁)).defined ↔ (b q₁).defined := by
  dsimp [PartialBehaviorCodec.toMorphism]
  rw [c.decode_encode_query]

/-- **Theorem (`toMorphism_val_encodeOut`):**
    On any valid encoded outcome `c.encodeOut o₁`, `(c.toMorphism b q₂).val`
    recovers `(b (c.decodeQuery q₂)).val h o₁` exactly. -/
theorem PartialBehaviorCodec.toMorphism_val_encodeOut {L₁ L₂ : Language}
    (c : PartialBehaviorCodec L₁ L₂) (b : L₁.Behavior) (q₂ : L₂.Query)
    (h : (c.toMorphism b q₂).defined) (o₁ : L₁.Out) :
    (c.toMorphism b q₂).val h (c.encodeOut o₁) ↔
      (b (c.decodeQuery q₂)).val h o₁ := by
  constructor
  · intro ⟨o₁', hdec, hval⟩
    rw [c.decode_encode_out] at hdec
    injection hdec with heq
    subst heq
    exact hval
  · intro hval
    exact ⟨o₁, c.decode_encode_out o₁, hval⟩

/-- **Identity `PartialBehaviorCodec`.** -/
def PartialBehaviorCodec.id (L : Language) : PartialBehaviorCodec L L where
  encodeQuery q := q
  decodeQuery q := q
  decode_encode_query _ := rfl
  encodeOut o := o
  decodeOut o := some o
  decode_encode_out _ := rfl
  encode_of_decode_some _ _ h := by
    injection h with h'
    exact h'.symm

/-- **Composition of `PartialBehaviorCodec`s via
    `Option.bind`.** -/
def PartialBehaviorCodec.comp {L₁ L₂ L₃ : Language}
    (c₂ : PartialBehaviorCodec L₂ L₃) (c₁ : PartialBehaviorCodec L₁ L₂) :
    PartialBehaviorCodec L₁ L₃ where
  encodeQuery q₁ := c₂.encodeQuery (c₁.encodeQuery q₁)
  decodeQuery q₃ := c₁.decodeQuery (c₂.decodeQuery q₃)
  decode_encode_query q₁ := by
    rw [c₂.decode_encode_query, c₁.decode_encode_query]
  encodeOut o₁ := c₂.encodeOut (c₁.encodeOut o₁)
  decodeOut o₃ := (c₂.decodeOut o₃).bind c₁.decodeOut
  decode_encode_out o₁ := by
    rw [c₂.decode_encode_out]
    exact c₁.decode_encode_out o₁
  encode_of_decode_some o₃ o₁ h := by
    cases h₂ : c₂.decodeOut o₃ with
    | none =>
      rw [h₂] at h
      cases h
    | some o₂ =>
      rw [h₂] at h
      dsimp [Option.bind] at h
      have he₁ := c₁.encode_of_decode_some o₂ o₁ h
      have he₂ := c₂.encode_of_decode_some o₃ o₂ h₂
      rw [he₁, he₂]

/-- Zero-axiom mutual refinement between `(c₂.comp c₁).toMorphism b` and
    `c₂.toMorphism (c₁.toMorphism b)`. -/
theorem PartialBehaviorCodec.comp_toMorphism_iff {L₁ L₂ L₃ : Language}
    (c₂ : PartialBehaviorCodec L₂ L₃) (c₁ : PartialBehaviorCodec L₁ L₂)
    (b : L₁.Behavior) (q₃ : L₃.Query)
    (h : ((c₂.comp c₁).toMorphism b q₃).defined) (o₃ : L₃.Out) :
    ((c₂.comp c₁).toMorphism b q₃).val h o₃ ↔
      (c₂.toMorphism (c₁.toMorphism b) q₃).val h o₃ := by
  constructor
  · intro ⟨o₁, hbind, hval⟩
    dsimp [PartialBehaviorCodec.comp] at hbind
    cases h₂ : c₂.decodeOut o₃ with
    | none =>
      rw [h₂] at hbind
      cases hbind
    | some o₂ =>
      rw [h₂] at hbind
      dsimp [Option.bind] at hbind
      exact ⟨o₂, h₂, o₁, hbind, hval⟩
  · intro ⟨o₂, h₂, o₁, h₁, hval⟩
    refine ⟨o₁, ?_, hval⟩
    dsimp [PartialBehaviorCodec.comp]
    rw [h₂]
    exact h₁

/-- **Theorem (`id_toMorphism` and `comp_toMorphism`):**
    `PartialBehaviorCodec.toMorphism` is a strict functor from
    `PartialBehaviorCodec` to behavior morphisms (`id` maps to `id` and `comp`
    maps to `∘`). -/
theorem PartialBehaviorCodec.id_toMorphism (L : Language) :
    (PartialBehaviorCodec.id L).toMorphism = fun b => b := by
  funext b q
  cases h : b q with
  | mk def_p val_p =>
    dsimp [PartialBehaviorCodec.id, PartialBehaviorCodec.toMorphism]
    rw [h]
    congr
    funext hdef o
    exact propext
      ⟨fun ⟨o', heq, hv⟩ => by injection heq with h'; subst h'; exact hv,
       fun hv => ⟨o, rfl, hv⟩⟩

theorem PartialBehaviorCodec.comp_toMorphism {L₁ L₂ L₃ : Language}
    (c₂ : PartialBehaviorCodec L₂ L₃) (c₁ : PartialBehaviorCodec L₁ L₂) :
    (c₂.comp c₁).toMorphism = c₂.toMorphism ∘ c₁.toMorphism := by
  funext b q₃
  dsimp [Function.comp, PartialBehaviorCodec.toMorphism]
  congr
  funext h o₃
  exact propext (PartialBehaviorCodec.comp_toMorphism_iff c₂ c₁ b q₃ h o₃)

/-!
## 6. Concrete `MirAbiVal ↔ X86RawVal` Instantiation

We instantiate `PartialBehaviorCodec` for high-level typed `MirAbiVal` values
(`bool`, `usize`, `unit`) lowered into raw 64-bit x86-64 register values
`X86RawVal` where a `bool` return is stored in an 8/64-bit register (`0` for
`false`, `1` for `true`, and raw bit patterns `n ≥ 2` decode to `none`).
-/

/-- Source-level typed ABI value in MIR. -/
inductive MirAbiVal where
  | bool (b : Bool)
  | usize (n : UInt64)
  | unit
  deriving DecidableEq

/-- Target-level raw x86-64 ABI value before validity decoding:
    - `boolWord raw`: an 8-bit/64-bit register holding a raw `UInt64` word for a
      `bool`-typed return (`0` = `false`, `1` = `true`, `raw ≥ 2` = invalid bit
      pattern).
    - `usizeWord n`: a 64-bit `usize` register word.
    - `unitVal`: zero-sized `()` return. -/
inductive X86RawVal where
  | boolWord (raw : UInt64)
  | usizeWord (n : UInt64)
  | unitVal
  deriving DecidableEq

/-- Encode a valid `MirAbiVal` into its canonical `X86RawVal` representation. -/
def encodeMirAbiVal : MirAbiVal → X86RawVal
  | .bool false => .boolWord 0
  | .bool true => .boolWord 1
  | .usize n => .usizeWord n
  | .unit => .unitVal

/-- Partially decode a raw `X86RawVal` back to `Option MirAbiVal`, rejecting
    invalid boolean bit patterns (`raw ≥ 2`) with `none`. -/
def decodeX86RawVal : X86RawVal → Option MirAbiVal
  | .boolWord w =>
    if w = 0 then some (.bool false)
    else if w = 1 then some (.bool true)
    else none
  | .usizeWord n => some (.usize n)
  | .unitVal => some .unit

theorem decodeX86RawVal_encodeMirAbiVal (v : MirAbiVal) :
    decodeX86RawVal (encodeMirAbiVal v) = some v := by
  cases v with
  | bool b => cases b <;> rfl
  | usize _ => rfl
  | unit => rfl

theorem encodeMirAbiVal_of_decodeX86RawVal_some
    (raw : X86RawVal) (v : MirAbiVal)
    (h : decodeX86RawVal raw = some v) :
    encodeMirAbiVal v = raw := by
  cases raw with
  | boolWord w =>
    dsimp [decodeX86RawVal] at h
    split at h
    · rename_i hw0
      injection h with hv
      subst hv hw0
      rfl
    · split at h
      · rename_i _ hw1
        injection h with hv
        subst hv hw1
        rfl
      · cases h
  | usizeWord n =>
    dsimp [decodeX86RawVal] at h
    injection h with hv
    subst hv
    rfl
  | unitVal =>
    dsimp [decodeX86RawVal] at h
    injection h with hv
    subst hv
    rfl

/-- Lift `encodeMirAbiVal` to `SilentEventualOut`. -/
def encodeEventualAbiOut :
    SilentEventualOut MirAbiVal → SilentEventualOut X86RawVal
  | .terminated (.normal v) => .terminated (.normal (encodeMirAbiVal v))
  | .terminated .unwind => .terminated .unwind
  | .diverges => .diverges

/-- Lift `decodeX86RawVal` to `Option (SilentEventualOut MirAbiVal)`. -/
def decodeEventualRawOut :
    SilentEventualOut X86RawVal → Option (SilentEventualOut MirAbiVal)
  | .terminated (.normal raw) =>
    (decodeX86RawVal raw).map (fun v => .terminated (.normal v))
  | .terminated .unwind => some (.terminated .unwind)
  | .diverges => some .diverges

theorem decodeEventualRawOut_encode (o : SilentEventualOut MirAbiVal) :
    decodeEventualRawOut (encodeEventualAbiOut o) = some o := by
  cases o with
  | terminated t =>
    cases t with
    | normal v =>
      dsimp [encodeEventualAbiOut, decodeEventualRawOut]
      rw [decodeX86RawVal_encodeMirAbiVal]
      rfl
    | unwind => rfl
  | diverges => rfl

theorem encodeEventualAbiOut_of_decode_some (o₂ : SilentEventualOut X86RawVal)
    (o₁ : SilentEventualOut MirAbiVal)
    (h : decodeEventualRawOut o₂ = some o₁) :
    encodeEventualAbiOut o₁ = o₂ := by
  cases o₂ with
  | terminated t₂ =>
    cases t₂ with
    | normal raw =>
      dsimp [decodeEventualRawOut] at h
      cases hdec : decodeX86RawVal raw with
      | none =>
        rw [hdec] at h
        cases h
      | some v =>
        rw [hdec] at h
        dsimp [Option.map] at h
        injection h with ho₁
        subst ho₁
        dsimp [encodeEventualAbiOut]
        rw [encodeMirAbiVal_of_decodeX86RawVal_some raw v hdec]
    | unwind =>
      dsimp [decodeEventualRawOut] at h
      injection h with ho₁
      subst ho₁
      rfl
  | diverges =>
    dsimp [decodeEventualRawOut] at h
    injection h with ho₁
    subst ho₁
    rfl

/-- Simple MIR and x86-64 ABI languages for testing `MirAbiVal ↔ X86RawVal`
    under `PartialBehaviorCodec`. -/
def MirBoolLang : Language where
  Prog := Bool → MirAbiVal
  Query := Bool
  Out := SilentEventualOut MirAbiVal
  sem f q := Partial.pure (fun out => out = .terminated (.normal (f q)))

def X86RawBoolLang : Language where
  Prog := Bool → X86RawVal
  Query := Bool
  Out := SilentEventualOut X86RawVal
  sem f q := Partial.pure (fun out => out = .terminated (.normal (f q)))

/-- Concrete `PartialBehaviorCodec` between `MirBoolLang` and
    `X86RawBoolLang`. -/
def mirToX86AbiCodec : PartialBehaviorCodec MirBoolLang X86RawBoolLang where
  encodeQuery q := q
  decodeQuery q := q
  decode_encode_query _ := rfl
  encodeOut := encodeEventualAbiOut
  decodeOut := decodeEventualRawOut
  decode_encode_out := decodeEventualRawOut_encode
  encode_of_decode_some := encodeEventualAbiOut_of_decode_some

/-- **Theorem (`valid_bool_negation_compiles`):**
    A valid x86-64 implementation of boolean negation (`xor al, 1`, returning
    `1` on `false` and `0` on `true`) compiles `fun b => MirAbiVal.bool (!b)`
    under `mirToX86AbiCodec`. -/
theorem valid_bool_negation_compiles :
    Compiles MirBoolLang X86RawBoolLang mirToX86AbiCodec.toMorphism
      (fun b => .bool (!b))
      (fun b => if b then .boolWord 0 else .boolWord 1) := by
  intro b _
  refine ⟨True.intro, ?_⟩
  intro out hout
  dsimp [X86RawBoolLang] at hout
  subst hout
  cases b with
  | false =>
    exact ⟨.terminated (.normal (.bool true)), rfl, rfl⟩
  | true =>
    exact ⟨.terminated (.normal (.bool false)), rfl, rfl⟩

/-- **Theorem (`corrupt_bool_bitpattern_2_rejected`):**
    A buggy x86-64 implementation (`not al` without masking, returning raw word
    `2` for a `bool`) is **automatically rejected** by
    `Compiles MirBoolLang X86RawBoolLang mirToX86AbiCodec.toMorphism` because
    `decodeX86RawVal (.boolWord 2) = none`! -/
theorem corrupt_bool_bitpattern_2_rejected (s : MirBoolLang.Prog) :
    ¬ Compiles MirBoolLang X86RawBoolLang mirToX86AbiCodec.toMorphism
        s (fun _ => .boolWord 2) := by
  refine mirToX86AbiCodec.compiles_rejects_invalid_target_out
    s (fun _ => .boolWord 2) true (.terminated (.normal (.boolWord 2)))
    True.intro
    (fun _ => rfl)
    rfl

/-!
## 7. Kernel Axiom Audit (`#print axioms`)
-/

#print axioms s_var_vs_t_var_step_mismatch
#print axioms lockstep_codec_fails_on_s_var
#print axioms no_state_independent_step_map_for_variable_lowering
#print axioms DilationCodec.monotone_toMorphism
#print axioms DilationCodec.comp_toMorphism_le
#print axioms DilationCodec.compiles_comp
#print axioms dilationCodec_rejects_loopCodegen
#print axioms dilationCodec_verifies_s_var
#print axioms exists_nat_no_choice_canary
#print axioms eventual_wellFormed_iff_prefix_wellFormed
#print axioms eventual_rejects_loopCodegen
#print axioms eventual_verifies_s_var
#print axioms eventual_verifies_s_fast
#print axioms no_total_section_for_bool_in_uint8
#print axioms no_total_section_for_bool_in_nat
#print axioms PartialBehaviorCodec.encodeOut_injective
#print axioms PartialBehaviorCodec.decodeOut_injective_on_some
#print axioms PartialBehaviorCodec.invalid_target_out_rejected
#print axioms PartialBehaviorCodec.compiles_rejects_invalid_target_out
#print axioms PartialBehaviorCodec.monotone_toMorphism
#print axioms PartialBehaviorCodec.toMorphism_defined
#print axioms PartialBehaviorCodec.toMorphism_encodeQuery_defined
#print axioms PartialBehaviorCodec.toMorphism_val_encodeOut
#print axioms PartialBehaviorCodec.comp_toMorphism_iff
#print axioms PartialBehaviorCodec.id_toMorphism
#print axioms PartialBehaviorCodec.comp_toMorphism
#print axioms decodeX86RawVal_encodeMirAbiVal
#print axioms encodeMirAbiVal_of_decodeX86RawVal_some
#print axioms valid_bool_negation_compiles
#print axioms corrupt_bool_bitpattern_2_rejected

end Anneal.BehaviorCodecExpressiveness
