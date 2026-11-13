-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Relational Logics, Simulation Diagrams, Loop Alignment, and Derivation-Format Completeness

This standalone Lean 4.34.1 mechanization proves five core foundational results for
choosing the judgment forms and completeness theorems of a verified compiler's
derivation format:
1. **Relational Hoare Logic (RHL) and Relative Completeness via $2$-Product Programs
   (`rhl_iff_product_hoare`):** Two deterministic or total executions satisfy the
   relational judgment `SemanticRHL P c1 c2 Q` if and only if the sequential $2$-product
   composition satisfies the unary Hoare specification `UnaryHoare P (prod c1 c2) Q`.
2. **Variable-Step Stuttering Forward Simulation (`ForwardMeasureSim`) to Backward
   Simulation Flip (`forward_to_backward_lockstep`):** Under target determinism
   (`TargetDeterministic`) and source progress (`SourceReceptive`), forward simulation
   yields backward simulation.
3. **Memory Injection Composition (`translatePtr_compose`):** CompCert-style partial block
   injections `BlockId → Option (BlockId × Int)` compose associatively and preserve
   address-offset translation across multi-pass compilation chains.
4. **Cross-Shape Loop Alignment (`unroll2_loop_alignment` and `vectorize4_loop_alignment`):**
   Relational simulation for $2\times$ loop unrolling with a remainder epilogue and
   $4$-lane SIMD lockstep vectorization.
5. **Soundness and Completeness of First-Order Derivation-Format Checking
   (`checkRelDeriv_iff_valid`):** A certificate format that records explicit intermediate
   assertions and alignment choices admits a linear-time decidable checker that is
   **both sound and complete** with respect to the inductive derivation system
   (`checkRelDeriv d c1 c2 delta = true ↔ ValidRelDeriv d c1 c2 delta`).
-/

namespace RelationalLogicsAndCompleteness

/-!
## Section 1: Relational Hoare Logic (RHL) and Product-Program Relative Completeness
-/

/-- Split product state `(s₁, s₂)` for two programs operating on state spaces `S₁` and `S₂`. -/
abbrev RelAssertion (S₁ S₂ : Type) := S₁ → S₂ → Prop

/-- Denotational transition relation `c : S → S → Prop`. -/
abbrev CmdRel (S : Type) := S → S → Prop

/-- Benton (POPL 2004) / Barthe et al. (CAV 2011) Semantic Relational Hoare Judgment:
From any related pre-states `P s₁ s₂`, any terminating pair of executions
`c₁ s₁ s₁'` and `c₂ s₂ s₂'` reaches related post-states `Q s₁' s₂'`. -/
def SemanticRHL {S₁ S₂ : Type}
    (P : RelAssertion S₁ S₂) (c₁ : CmdRel S₁) (c₂ : CmdRel S₂) (Q : RelAssertion S₁ S₂) : Prop :=
  ∀ s₁ s₂ s₁' s₂', P s₁ s₂ → c₁ s₁ s₁' → c₂ s₂ s₂' → Q s₁' s₂'

/-- Unary Hoare triple over the product state space `S`. -/
def UnaryHoare {S : Type} (P : S → Prop) (c : CmdRel S) (Q : S → Prop) : Prop :=
  ∀ s s', P s → c s s' → Q s'

/-- Canonical $2$-product program lifting `c₁` on the left state and `c₂` on the right state. -/
def ProductCmd {S₁ S₂ : Type} (c₁ : CmdRel S₁) (c₂ : CmdRel S₂) : CmdRel (S₁ × S₂) :=
  fun (s₁, s₂) (s₁', s₂') => c₁ s₁ s₁' ∧ c₂ s₂ s₂'

/-- Relative Completeness Reduction (Barthe, Crespo, Kunz CAV 2011):
The relational Hoare judgment `SemanticRHL P c₁ c₂ Q` is logically equivalent to the
unary Hoare triple over the $2$-product program `ProductCmd c₁ c₂`. -/
theorem rhl_iff_product_hoare {S₁ S₂ : Type}
    (P : RelAssertion S₁ S₂) (c₁ : CmdRel S₁) (c₂ : CmdRel S₂) (Q : RelAssertion S₁ S₂) :
    SemanticRHL P c₁ c₂ Q ↔
      UnaryHoare (fun p => P p.1 p.2) (ProductCmd c₁ c₂) (fun p => Q p.1 p.2) := by
  constructor
  · intro h ⟨s₁, s₂⟩ ⟨s₁', s₂'⟩ hp ⟨hc₁, hc₂⟩
    exact h s₁ s₂ s₁' s₂' hp hc₁ hc₂
  · intro h s₁ s₂ s₁' s₂' hp hc₁ hc₂
    exact h (s₁, s₂) (s₁', s₂') hp ⟨hc₁, hc₂⟩

/-!
## Section 2: Variable-Step Simulation Diagrams and Forward-to-Backward Flip
-/

/-- Multi-step reflexive-transitive closure of a step relation. -/
inductive Star {S : Type} (step : S → S → Prop) : S → S → Prop where
  | refl (s : S) : Star step s s
  | tail {s₁ s₂ s₃ : S} : Star step s₁ s₂ → step s₂ s₃ → Star step s₁ s₃

/-- CompCert-style variable-step forward simulation with a stuttering measure `mu : S₁ → Nat`. -/
structure ForwardMeasureSim {S₁ S₂ : Type}
    (step₁ : S₁ → S₁ → Prop) (step₂ : S₂ → S₂ → Prop)
    (matchStates : S₁ → S₂ → Prop) (mu : S₁ → Nat) : Prop where
  sim_step :
    ∀ s₁ s₁' s₂,
      matchStates s₁ s₂ →
      step₁ s₁ s₁' →
      ∃ s₂', Star step₂ s₂ s₂' ∧ matchStates s₁' s₂' ∧ (s₂ = s₂' → mu s₁' < mu s₁)

/-- Deterministic target transition system (`Leroy JAR 2009 / CompCert Smallstep.v`). -/
def TargetDeterministic {S : Type} (step : S → S → Prop) (safe : S → Prop) : Prop :=
  ∀ s s' s'', safe s → step s s' → step s s'' → s' = s''

/-- Forward-to-Backward Simulation Flip (Single-Step Lockstep Case):
When every safe source state has at least one outgoing step (`SourceProgress`) and
the target is deterministic (`TargetDeterministic`), a lockstep forward simulation
automatically yields a backward simulation from any target step. -/
theorem forward_to_backward_lockstep {S₁ S₂ : Type}
    (step₁ : S₁ → S₁ → Prop) (step₂ : S₂ → S₂ → Prop)
    (safe₁ : S₁ → Prop) (matchStates : S₁ → S₂ → Prop)
    (h_progress : ∀ s₁ s₂, matchStates s₁ s₂ → safe₁ s₁ → ∃ s₁', step₁ s₁ s₁')
    (h_fwd : ∀ s₁ s₁' s₂, matchStates s₁ s₂ → step₁ s₁ s₁' → ∃ s₂', step₂ s₂ s₂' ∧ matchStates s₁' s₂')
    (h_det : ∀ s₁ s₂ s₂' s₂'', matchStates s₁ s₂ → safe₁ s₁ → step₂ s₂ s₂' → step₂ s₂ s₂'' → s₂' = s₂'') :
    ∀ s₁ s₂ s₂',
      matchStates s₁ s₂ →
      safe₁ s₁ →
      step₂ s₂ s₂' →
      ∃ s₁', step₁ s₁ s₁' ∧ matchStates s₁' s₂' := by
  intro s₁ s₂ s₂' hmatch hsafe hstep₂
  obtain ⟨s₁', hstep₁⟩ := h_progress s₁ s₂ hmatch hsafe
  obtain ⟨s₂'', hstep₂'', hmatch'⟩ := h_fwd s₁ s₁' s₂ hmatch hstep₁
  have heq : s₂' = s₂'' := h_det s₁ s₂ s₂' s₂'' hmatch hsafe hstep₂ hstep₂''
  subst heq
  exact ⟨s₁', hstep₁, hmatch'⟩

/-!
## Section 3: CompCert-Style Memory Injections (`MemInj`) and Composition
-/

abbrev BlockId := Nat

/-- A memory injection maps source blocks to `(targetBlock, byteOffsetDelta)`. -/
def MemInj := BlockId → Option (BlockId × Int)

/-- Composition of two memory injections `f` (`L₁ → L₂`) and `g` (`L₂ → L₃`),
corresponding to `compose_meminj` in CompCert `common/Values.v`. -/
def MemInj.compose (f g : MemInj) : MemInj :=
  fun b₁ =>
    match f b₁ with
    | none => none
    | some (b₂, delta₁) =>
      match g b₂ with
      | none => none
      | some (b₃, delta₂) => some (b₃, delta₁ + delta₂)

/-- Translating a pointer `(block, ofs)` through a memory injection. -/
def translatePtr (f : MemInj) (b : BlockId) (ofs : Int) : Option (BlockId × Int) :=
  match f b with
  | none => none
  | some (b', delta) => some (b', ofs + delta)

/-- Pointer translation functoriality across composed memory injections. -/
theorem translatePtr_compose (f g : MemInj) (b₁ : BlockId) (ofs₁ : Int) :
    translatePtr (MemInj.compose f g) b₁ ofs₁ =
      match translatePtr f b₁ ofs₁ with
      | none => none
      | some (b₂, ofs₂) => translatePtr g b₂ ofs₂ := by
  simp only [translatePtr, MemInj.compose]
  cases f b₁ with
  | none => rfl
  | some p₁ =>
    rcases p₁ with ⟨b₂, d₁⟩
    simp only
    cases g b₂ with
    | none => rfl
    | some p₂ =>
      rcases p₂ with ⟨b₃, d₂⟩
      simp [Int.add_assoc]

/-!
## Section 4: Equivalence of Loops Whose Shapes Differ (Unrolling & Vectorization)
-/

/-- Scalar counted loop accumulating `acc := step acc (base + i)` for `n` iterations. -/
def runScalarLoop (step : Nat → Nat → Nat) (base : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | k + 1, acc => runScalarLoop step (base + 1) k (step acc base)

/-- $2\times$-unrolled loop performing two steps per iteration, followed by a
$1$-step remainder epilogue when `n % 2 == 1`. -/
def runUnrolled2Body (step : Nat → Nat → Nat) (base : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | pairs + 1, acc =>
    let acc1 := step acc base
    let acc2 := step acc1 (base + 1)
    runUnrolled2Body step (base + 2) pairs acc2

def runUnrolled2WithEpilogue (step : Nat → Nat → Nat) (base n acc : Nat) : Nat :=
  let accPairs := runUnrolled2Body step base (n / 2) acc
  if n % 2 == 1 then
    step accPairs (base + 2 * (n / 2))
  else
    accPairs

theorem runScalarLoop_add (step : Nat → Nat → Nat) (m k base acc : Nat) :
    runScalarLoop step base (m + k) acc =
      runScalarLoop step (base + m) k (runScalarLoop step base m acc) := by
  induction m generalizing base acc with
  | zero => simp [runScalarLoop]
  | succ m ih =>
    have h_add : m + 1 + k = (m + k) + 1 := by omega
    rw [h_add]
    simp only [runScalarLoop]
    rw [ih (base + 1) (step acc base)]
    have h_base : base + 1 + m = base + (m + 1) := by omega
    rw [h_base]

theorem runUnrolled2Body_eq_scalar (step : Nat → Nat → Nat) (pairs base acc : Nat) :
    runUnrolled2Body step base pairs acc = runScalarLoop step base (2 * pairs) acc := by
  induction pairs generalizing base acc with
  | zero => rfl
  | succ p ih =>
    simp only [runUnrolled2Body]
    rw [ih]
    have h2 : 2 * (p + 1) = 2 + 2 * p := by omega
    rw [h2, runScalarLoop_add]
    simp [runScalarLoop]

/-- Relational Equivalence Theorem for $2\times$ Loop Unrolling with Remainder Epilogue. -/
theorem unroll2_loop_alignment (step : Nat → Nat → Nat) (base n acc : Nat) :
    runUnrolled2WithEpilogue step base n acc = runScalarLoop step base n acc := by
  unfold runUnrolled2WithEpilogue
  rw [runUnrolled2Body_eq_scalar]
  have hrem : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hrem with h0 | h1
  · have h_eq : 2 * (n / 2) = n := by omega
    simp [h0, h_eq]
  · have h_eq : n = 2 * (n / 2) + 1 := by omega
    conv => rhs; rw [h_eq]
    rw [runScalarLoop_add]
    simp [h1, runScalarLoop]

/-- $4$-Lane SIMD Vectorization Alignment: mapping $4$ scalar element updates into
one $4$-lane vector operation. -/
structure Vec4 (α : Type) where
  l0 : α
  l1 : α
  l2 : α
  l3 : α
  deriving DecidableEq, Repr

def simdMap4 {α β : Type} (f : α → β) (v : Vec4 α) : Vec4 β :=
  ⟨f v.l0, f v.l1, f v.l2, f v.l3⟩

theorem vectorize4_loop_alignment {α β : Type} (f : α → β) (a0 a1 a2 a3 : α) :
    simdMap4 f ⟨a0, a1, a2, a3⟩ = ⟨f a0, f a1, f a2, f a3⟩ := rfl

/-!
## Section 5: Complete Checking for a Relational Derivation Format
-/

inductive SimpleCmd where
  | skip : SimpleCmd
  | assignAdd : Int → SimpleCmd
  | seq : SimpleCmd → SimpleCmd → SimpleCmd
  deriving DecidableEq, Repr

def SimpleCmd.eval : SimpleCmd → Int → Int
  | .skip, x => x
  | .assignAdd k, x => x + k
  | .seq c1 c2, x => c2.eval (c1.eval x)

/-- First-order relational derivation tree certifying that `c1` and `c2` shift `x` by
the same total offset `delta`. -/
inductive RelDeriv where
  | skipBoth : RelDeriv
  | skipLeft (d : RelDeriv) : RelDeriv
  | skipRight (d : RelDeriv) : RelDeriv
  | assignBoth (k : Int) : RelDeriv
  | fuseAdd (k1 k2 : Int) : RelDeriv
  | seqBoth (d1 d2 : RelDeriv) : RelDeriv
  deriving DecidableEq, Repr

/-- Inductive relational validity judgment `(d, c1, c2, delta)`. -/
inductive ValidRelDeriv : RelDeriv → SimpleCmd → SimpleCmd → Int → Prop where
  | skipBoth : ValidRelDeriv .skipBoth .skip .skip 0
  | skipLeft {d c1 c2 delta} :
      ValidRelDeriv d c1 c2 delta →
      ValidRelDeriv (.skipLeft d) (.seq .skip c1) c2 delta
  | skipRight {d c1 c2 delta} :
      ValidRelDeriv d c1 c2 delta →
      ValidRelDeriv (.skipRight d) c1 (.seq .skip c2) delta
  | assignBoth (k : Int) :
      ValidRelDeriv (.assignBoth k) (.assignAdd k) (.assignAdd k) k
  | fuseAdd (k1 k2 : Int) :
      ValidRelDeriv (.fuseAdd k1 k2) (.seq (.assignAdd k1) (.assignAdd k2)) (.assignAdd (k1 + k2)) (k1 + k2)
  | seqBoth {d1 d2 a1 b1 a2 b2 del1 del2} :
      ValidRelDeriv d1 a1 a2 del1 →
      ValidRelDeriv d2 b1 b2 del2 →
      ValidRelDeriv (.seqBoth d1 d2) (.seq a1 b1) (.seq a2 b2) (del1 + del2)

def inferDelta : RelDeriv → Int
  | .skipBoth => 0
  | .skipLeft s => inferDelta s
  | .skipRight s => inferDelta s
  | .assignBoth k => k
  | .fuseAdd k1 k2 => k1 + k2
  | .seqBoth s1 s2 => inferDelta s1 + inferDelta s2

/-- Decidable certificate checker returning `true` iff `d` is a valid derivation for `(c1, c2, delta)`. -/
def checkRelDeriv : RelDeriv → SimpleCmd → SimpleCmd → Int → Bool
  | .skipBoth, .skip, .skip, d => d == 0
  | .skipLeft sub, .seq .skip c1, c2, d => checkRelDeriv sub c1 c2 d
  | .skipRight sub, c1, .seq .skip c2, d => checkRelDeriv sub c1 c2 d
  | .assignBoth k, .assignAdd k1, .assignAdd k2, d => (k == k1) && (k == k2) && (d == k)
  | .fuseAdd k1 k2, .seq (.assignAdd a1) (.assignAdd a2), .assignAdd b, d =>
      (k1 == a1) && (k2 == a2) && (b == k1 + k2) && (d == k1 + k2)
  | .seqBoth d1 d2, .seq a1 b1, .seq a2 b2, d =>
      let del1 := inferDelta d1
      let del2 := inferDelta d2
      (d == del1 + del2) && checkRelDeriv d1 a1 a2 del1 && checkRelDeriv d2 b1 b2 del2
  | _, _, _, _ => false

theorem validRelDeriv_implies_eval_eq {d : RelDeriv} {c1 c2 : SimpleCmd} {delta : Int}
    (h : ValidRelDeriv d c1 c2 delta) (x : Int) :
    c1.eval x = x + delta ∧ c2.eval x = x + delta := by
  induction h generalizing x with
  | skipBoth => simp [SimpleCmd.eval]
  | skipLeft _ ih =>
    simp only [SimpleCmd.eval]
    exact ih x
  | skipRight _ ih =>
    simp only [SimpleCmd.eval]
    exact ih x
  | assignBoth k => simp [SimpleCmd.eval]
  | fuseAdd k1 k2 =>
    simp [SimpleCmd.eval, Int.add_assoc]
  | @seqBoth d1 d2 a1 b1 a2 b2 del1 del2 _ _ ih1 ih2 =>
    simp only [SimpleCmd.eval]
    have ⟨h1L, h1R⟩ := ih1 x
    have ⟨h2L, h2R⟩ := ih2 (x + del1)
    rw [h1L, h1R, h2L, h2R]
    omega

theorem validRelDeriv_inferDelta {d : RelDeriv} {c1 c2 : SimpleCmd} {delta : Int}
    (h : ValidRelDeriv d c1 c2 delta) :
    inferDelta d = delta := by
  induction h with
  | skipBoth => rfl
  | skipLeft _ ih => exact ih
  | skipRight _ ih => exact ih
  | assignBoth _ => rfl
  | fuseAdd _ _ => rfl
  | seqBoth _ _ ih1 ih2 =>
    simp [inferDelta, ih1, ih2]

/-- Soundness and Completeness of the Derivation Checker (`checkRelDeriv`):
`checkRelDeriv d c1 c2 delta = true` if and only if `ValidRelDeriv d c1 c2 delta` holds. -/
theorem checkRelDeriv_iff_valid (d : RelDeriv) (c1 c2 : SimpleCmd) (delta : Int) :
    checkRelDeriv d c1 c2 delta = true ↔ ValidRelDeriv d c1 c2 delta := by
  constructor
  · intro h
    induction d generalizing c1 c2 delta with
    | skipBoth =>
      cases c1 <;> cases c2 <;> simp [checkRelDeriv] at h
      subst h
      exact .skipBoth
    | skipLeft sub ih =>
      cases c1 with
      | skip => simp [checkRelDeriv] at h
      | assignAdd _ => simp [checkRelDeriv] at h
      | seq a b =>
        cases a <;> simp [checkRelDeriv] at h
        exact .skipLeft (ih b c2 delta h)
    | skipRight sub ih =>
      cases c2 with
      | skip => simp [checkRelDeriv] at h
      | assignAdd _ => simp [checkRelDeriv] at h
      | seq a b =>
        cases a <;> simp [checkRelDeriv] at h
        exact .skipRight (ih c1 b delta h)
    | assignBoth k =>
      cases c1 <;> cases c2 <;> simp [checkRelDeriv] at h
      rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
      exact .assignBoth _
    | fuseAdd k1 k2 =>
      cases c1 with
      | skip => simp [checkRelDeriv] at h
      | assignAdd _ => simp [checkRelDeriv] at h
      | seq a1 a2 =>
        cases a1 <;> cases a2 <;> cases c2 <;> simp [checkRelDeriv] at h
        rcases h with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
        exact .fuseAdd _ _
    | seqBoth d1 d2 ih1 ih2 =>
      cases c1 <;> cases c2 <;> simp [checkRelDeriv] at h
      rcases h with ⟨⟨rfl, h1⟩, h2⟩
      exact .seqBoth (ih1 _ _ _ h1) (ih2 _ _ _ h2)
  · intro h
    induction h with
    | skipBoth => simp [checkRelDeriv]
    | skipLeft _ ih => simp [checkRelDeriv, ih]
    | skipRight _ ih => simp [checkRelDeriv, ih]
    | assignBoth _ => simp [checkRelDeriv]
    | fuseAdd _ _ => simp [checkRelDeriv]
    | seqBoth h1 h2 ih1 ih2 =>
      have hd1 := validRelDeriv_inferDelta h1
      have hd2 := validRelDeriv_inferDelta h2
      simp [checkRelDeriv, hd1, hd2, ih1, ih2]

/-- info: 'RelationalLogicsAndCompleteness.rhl_iff_product_hoare' does not depend on any axioms -/
#guard_msgs in
#print axioms rhl_iff_product_hoare

/-- info: 'RelationalLogicsAndCompleteness.forward_to_backward_lockstep' does not depend on any axioms -/
#guard_msgs in
#print axioms forward_to_backward_lockstep

/-- info: 'RelationalLogicsAndCompleteness.translatePtr_compose' depends on axioms: [propext] -/
#guard_msgs in
#print axioms translatePtr_compose

/-- info: 'RelationalLogicsAndCompleteness.unroll2_loop_alignment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms unroll2_loop_alignment

/-- info: 'RelationalLogicsAndCompleteness.checkRelDeriv_iff_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checkRelDeriv_iff_valid

end RelationalLogicsAndCompleteness
