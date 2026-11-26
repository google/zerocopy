-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core

public section

/-!
# WHNF and Rewrite Firewalls (`Anneal.Firewall`)

Pass-1-portable (`prelude` + `Init.Core` only, zero axioms, zero
`._unsafe_rec`, zero `noncomputable`) barriers that stop Lean's kernel `whnf`
and tactic `rw` / `simp` traversals from penetrating large symbolic
weakest-precondition or MIR state expressions.

Three complementary mechanisms are provided:

1. **`Firewall tag P` (1-Field `Prop` Structure):**
   In Lean 4's kernel, a structure type constructor is never delta-unfolded,
   so `Firewall t₁ P` and `Firewall t₂ P` are not definitionally equal for
   distinct tags (`tag : Nat`), unlike a `def`/`abbrev` wrapper. Use
   `Firewall` to wrap intermediate symbolic obligations with an explicit tag
   separator.

2. **`IndexedCut` (Zero-`Prop`-Argument Indexed Step-Cut Combinator):**
   Even when `Firewall tag P` blocks head delta-unfolding, `P` still appears in
   the goal type's `Expr` arguments, so tactics like `rw` traverse `P` searching
   for redexes. Binding a stepped predicate `cutAt : Nat → σ → Prop` inside an
   `IndexedCut` (or marking a concrete `def myCut (stage : Nat) (st : σ) : Prop`
   `@[irreducible]` *after* proving its `seal`/`open`/`step` lemmas) keeps the
   expanded `Prop` expression out of the outer goal signature.

3. **Goal-Directed `ite` Branch Eliminators (`ite_*_imp`, `ite_eq_*_imp`):**
   Applying an eliminator to a hypothesis `h : if P then T else F` (as in
   `have h' := elim h`) makes the elaborator unify `h`'s type with the
   eliminator's premise, which can put it in weak head normal form and
   evaluate an expensive guard `P`. Reverting `h` and refining the goal
   `(if P then T else F) → G` with one of these eliminators instead matches
   `@ite` structurally and leaves `P` unreduced. Each eliminator is a term-mode
   `Decidable.casesOn` on the guard's `Decidable` instance.
-/

namespace Anneal.Firewall

/-! ## 1. Tagged 1-Field `Prop` Structure (`Firewall`) -/

/-- Wrap `P : Prop` inside a kernel-opaque 1-field structure indexed by an
explicit `tag : Nat` separator. -/
structure Firewall (tag : Nat) (P : Prop) : Prop where
  /-- Extract the underlying proposition `P`. -/
  val : P

/-- Wrap a proof of `P` inside `Firewall tag P`. -/
theorem wrap (tag : Nat) {P : Prop} (h : P) : Firewall tag P :=
  ⟨h⟩

/-- Extract a proof of `P` from `Firewall tag P`. -/
theorem unwrap {tag : Nat} {P : Prop} (h : Firewall tag P) : P :=
  h.val

/-- Transform the proposition wrapped inside `Firewall tag P` while preserving
`tag`. -/
theorem map (tag : Nat) {P Q : Prop} (f : P → Q) (h : Firewall tag P) :
    Firewall tag Q :=
  ⟨f h.val⟩

/-- Combine two firewalled propositions `Firewall tag P` and `Firewall tag Q`
under `f : P → Q → R`. -/
theorem map2 (tag : Nat) {P Q R : Prop} (f : P → Q → R)
    (hp : Firewall tag P) (hq : Firewall tag Q) : Firewall tag R :=
  ⟨f hp.val hq.val⟩

/-- Re-tag a firewalled obligation from `tag1` to `tag2`. -/
theorem trans_tag (tag1 tag2 : Nat) {P : Prop} (h : Firewall tag1 P) :
    Firewall tag2 P :=
  ⟨h.val⟩

/-! ## 2. Zero-`Prop`-Argument Indexed Step-Cut Combinator (`IndexedCut`) -/

/-- Wrap a state-indexed family of propositions `cutAt : Nat → σ → Prop`
without exposing expanded `Prop` bodies in the outer goal signature when
`cutAt` is bound to a top-level named definition. -/
structure IndexedCut {σ : Type u} (cutAt : Nat → σ → Prop)
    (stage : Nat) (st : σ) : Prop where
  /-- Unseal the underlying stage obligation `cutAt stage st`. -/
  runCut : cutAt stage st

/-- Seal `cutAt stage st` into an `IndexedCut cutAt stage st` wrapper. -/
theorem seal_cut {σ : Type u} {cutAt : Nat → σ → Prop}
    {stage : Nat} {st : σ} (h : cutAt stage st) :
    IndexedCut cutAt stage st :=
  ⟨h⟩

/-- Extract `cutAt stage st` from `IndexedCut cutAt stage st`. -/
theorem open_cut {σ : Type u} {cutAt : Nat → σ → Prop}
    {stage : Nat} {st : σ} (h : IndexedCut cutAt stage st) :
    cutAt stage st :=
  h.runCut

/-- Advance a sealed `IndexedCut` backward from `(stage2, st2)` to
`(stage1, st1)` along `hAdv`. -/
theorem step_cut {σ : Type u} {cutAt : Nat → σ → Prop}
    {stage1 stage2 : Nat} {st1 st2 : σ}
    (hAdv : cutAt stage2 st2 → cutAt stage1 st1)
    (hNext : IndexedCut cutAt stage2 st2) :
    IndexedCut cutAt stage1 st1 :=
  ⟨hAdv hNext.runCut⟩

/-- Discharge final goal `post` from a sealed `IndexedCut` via `hDone`. -/
theorem finish_cut {σ : Type u} {cutAt : Nat → σ → Prop}
    {stage : Nat} {st : σ} {post : Prop}
    (hDone : cutAt stage st → post)
    (hCut : IndexedCut cutAt stage st) : post :=
  hDone hCut.runCut

/-! ## 3. Goal-Directed `ite` Branch Eliminators -/

/-- Case split on `@ite Prop P inst T F` at the head of the goal. Use it as
`revert h; refine ite_elim_imp ?_ ?_` when `P` is expensive to reduce, so Lean
matches `@ite` structurally without putting `P` in weak head normal form. -/
theorem ite_elim_imp {P : Prop} {inst : Decidable P} {T F G : Prop}
    (hT : P → T → G) (hF : ¬ P → F → G) : @ite Prop P inst T F → G :=
  @Decidable.casesOn P (fun d => @ite Prop P d T F → G) inst hF hT

/-- Eliminate `@ite Prop P inst T F → G` through the `then` branch, given a
proof of the guard `P`. -/
theorem ite_true_imp {P : Prop} {inst : Decidable P} {T F G : Prop}
    (hP : P) (hT : T → G) : @ite Prop P inst T F → G :=
  ite_elim_imp (fun _ h => hT h) (fun hNP _ => False.elim (hNP hP))

/-- Eliminate `@ite Prop P inst T F → G` through the `else` branch, given a
proof of `¬ P`. -/
theorem ite_false_imp {P : Prop} {inst : Decidable P} {T F G : Prop}
    (hNP : ¬ P) (hF : F → G) : @ite Prop P inst T F → G :=
  ite_elim_imp (fun hP _ => False.elim (hNP hP)) (fun _ h => hF h)

/-- Eliminate `@ite Prop P inst T F → G` when the `then` branch `T` is absurd,
without reducing the guard `P`. -/
theorem ite_absurd_left_imp {P : Prop} {inst : Decidable P} {T F G : Prop}
    (hAbs : T → False) (hF : F → G) : @ite Prop P inst T F → G :=
  ite_elim_imp (fun _ h => False.elim (hAbs h)) (fun _ h => hF h)

/-- Eliminate `@ite Prop P inst T F → G` when the `else` branch `F` is absurd,
without reducing the guard `P`. -/
theorem ite_absurd_right_imp {P : Prop} {inst : Decidable P} {T F G : Prop}
    (hT : T → G) (hAbs : F → False) : @ite Prop P inst T F → G :=
  ite_elim_imp (fun _ h => hT h) (fun _ h => False.elim (hAbs h))

/-- Value-level counterpart of `ite_elim_imp` for `@ite α P inst t f = r → G`,
for branch hypotheses over values such as `Except`, `Option`, or step
results. -/
theorem ite_eq_elim_imp {α : Type u} {P : Prop} {inst : Decidable P}
    {t f r : α} {G : Prop}
    (hT : P → t = r → G) (hF : ¬ P → f = r → G) :
    @ite α P inst t f = r → G :=
  @Decidable.casesOn P (fun d => @ite α P d t f = r → G) inst hF hT

/-- Eliminate `@ite α P inst t f = r → G` through the `then` branch, given a
proof of the guard `P`. -/
theorem ite_eq_true_imp {α : Type u} {P : Prop} {inst : Decidable P}
    {t f r : α} {G : Prop} (hP : P) (hT : t = r → G) :
    @ite α P inst t f = r → G :=
  ite_eq_elim_imp (fun _ h => hT h) (fun hNP _ => False.elim (hNP hP))

/-- Eliminate `@ite α P inst t f = r → G` through the `else` branch, given a
proof of `¬ P`. -/
theorem ite_eq_false_imp {α : Type u} {P : Prop} {inst : Decidable P}
    {t f r : α} {G : Prop} (hNP : ¬ P) (hF : f = r → G) :
    @ite α P inst t f = r → G :=
  ite_eq_elim_imp (fun hP _ => False.elim (hNP hP)) (fun _ h => hF h)

/-- Eliminate `@ite α P inst t f = r → G` when `t ≠ r`, so only the `else`
branch can hold, without reducing the guard `P`. -/
theorem ite_eq_absurd_left_imp {α : Type u} {P : Prop} {inst : Decidable P}
    {t f r : α} {G : Prop} (hNe : t ≠ r) (hF : f = r → G) :
    @ite α P inst t f = r → G :=
  ite_eq_elim_imp (fun _ h => False.elim (hNe h)) (fun _ h => hF h)

/-- Eliminate `@ite α P inst t f = r → G` when `f ≠ r`, so only the `then`
branch can hold, without reducing the guard `P`. -/
theorem ite_eq_absurd_right_imp {α : Type u} {P : Prop} {inst : Decidable P}
    {t f r : α} {G : Prop} (hT : t = r → G) (hNe : f ≠ r) :
    @ite α P inst t f = r → G :=
  ite_eq_elim_imp (fun _ h => hT h) (fun _ h => False.elim (hNe h))

/-! ## 4. Kernel-Checked Canaries -/

/-- Exercise `wrap`, `trans_tag`, and `unwrap` on a conjunctive proposition. -/
theorem canary_wrap_unwrap_tag {P Q : Prop} (hp : P) (hq : Q) : P ∧ Q :=
  let h0 : Firewall 0 (P ∧ Q) := wrap 0 ⟨hp, hq⟩
  let h7 : Firewall 7 (P ∧ Q) := trans_tag 0 7 h0
  unwrap h7

/-- Exercise `map` and `map2` combining independently firewalled inputs. -/
theorem canary_map_and_map2 {P Q R : Prop}
    (fp : P → Q) (hp : Firewall 3 P) (hr : Firewall 3 R) : Q ∧ R :=
  let hq : Firewall 3 Q := map 3 fp hp
  unwrap (map2 3 And.intro hq hr)

private def sampleStageCut (stage st : Nat) : Prop :=
  match stage with
  | 0 => st = 0
  | 1 => st = 0 ∧ True
  | _ + 2 => st = 0 ∧ True ∧ True

/-- Exercise `seal_cut`, `step_cut`, `open_cut`, and `finish_cut` over a
concrete 3-stage `IndexedCut` chain. -/
theorem canary_indexed_cut_chain {n : Nat} (hn : n = 0) : n = 0 :=
  let h2 : IndexedCut sampleStageCut 2 n :=
    seal_cut ⟨hn, True.intro, True.intro⟩
  let h1 : IndexedCut sampleStageCut 1 n :=
    step_cut (cutAt := sampleStageCut) (stage1 := 1) (stage2 := 2)
      (st1 := n) (st2 := n) (fun h => ⟨h.1, h.2.1⟩) h2
  let h0 : IndexedCut sampleStageCut 0 n :=
    step_cut (cutAt := sampleStageCut) (stage1 := 0) (stage2 := 1)
      (st1 := n) (st2 := n) (fun h => h.1) h1
  let _opened : sampleStageCut 0 n := open_cut h0
  finish_cut (cutAt := sampleStageCut) (stage := 0) (st := n) (fun h => h) h0

private def sampleIrrCut (stage st : Nat) : Prop :=
  match stage with
  | 0 => st = 0
  | _ + 1 => st = 0 ∧ True

private theorem sampleIrrCut_init {st : Nat} (h : st = 0) :
    sampleIrrCut 1 st :=
  ⟨h, True.intro⟩

private theorem sampleIrrCut_step {st : Nat} :
    sampleIrrCut 1 st → sampleIrrCut 0 st :=
  fun h => h.1

private theorem sampleIrrCut_done {st : Nat} :
    sampleIrrCut 0 st → st = 0 :=
  fun h => h

attribute [irreducible] sampleIrrCut

/-- Verify `seal_cut`, `step_cut`, `open_cut`, and `finish_cut` compose over a
predicate marked `@[irreducible]` after its step lemmas are proved. -/
theorem canary_irreducible_indexed_cut {st : Nat} (h : st = 0) : st = 0 :=
  let h1 : IndexedCut sampleIrrCut 1 st := seal_cut (sampleIrrCut_init h)
  let h0 : IndexedCut sampleIrrCut 0 st := step_cut sampleIrrCut_step h1
  let _opened : sampleIrrCut 0 st := open_cut h0
  finish_cut sampleIrrCut_done h0

/-- Guard for the `ite` canaries. It is marked `@[irreducible]` below, so the
elaborator cannot unfold it while checking them. It is public because the
canary statements mention it. -/
def iteCanaryGuard (n : Nat) : Prop := n = 0

/-- `Decidable` instance for `iteCanaryGuard`, passed to `@ite` explicitly. -/
def iteCanaryGuardDec (n : Nat) : Decidable (iteCanaryGuard n) :=
  Nat.decEq n 0

attribute [irreducible] iteCanaryGuard

/-- Exercise `ite_elim_imp` through the goal-directed
`revert h; refine ... ?_; intro h` pattern on the irreducible
`iteCanaryGuard`. -/
theorem canary_ite_elim_imp {n : Nat} {T F : Prop}
    (h : @ite Prop (iteCanaryGuard n) (iteCanaryGuardDec n) T F) :
    (iteCanaryGuard n ∧ T) ∨ (¬ iteCanaryGuard n ∧ F) := by
  revert h
  refine ite_elim_imp (fun hP hT => Or.inl ⟨hP, hT⟩) ?_
  intro hNP hF
  exact Or.inr ⟨hNP, hF⟩

/-- Exercise `ite_true_imp` on the irreducible `iteCanaryGuard`. -/
theorem canary_ite_true_imp {n : Nat} {T F : Prop} (hP : iteCanaryGuard n)
    (h : @ite Prop (iteCanaryGuard n) (iteCanaryGuardDec n) T F) : T := by
  revert h
  refine ite_true_imp hP ?_
  intro hT
  exact hT

/-- Exercise `ite_false_imp` on the irreducible `iteCanaryGuard`. -/
theorem canary_ite_false_imp {n : Nat} {T F : Prop} (hNP : ¬ iteCanaryGuard n)
    (h : @ite Prop (iteCanaryGuard n) (iteCanaryGuardDec n) T F) : F := by
  revert h
  refine ite_false_imp hNP ?_
  intro hF
  exact hF

/-- Exercise `ite_absurd_left_imp` on the irreducible `iteCanaryGuard`. -/
theorem canary_ite_absurd_left_imp {n : Nat} {Q : Prop}
    (h : @ite Prop (iteCanaryGuard n) (iteCanaryGuardDec n) False Q) : Q := by
  revert h
  refine ite_absurd_left_imp (fun hAbs => hAbs) ?_
  intro hQ
  exact hQ

/-- Exercise `ite_absurd_right_imp` on the irreducible `iteCanaryGuard`. -/
theorem canary_ite_absurd_right_imp {n : Nat} {Q : Prop}
    (h : @ite Prop (iteCanaryGuard n) (iteCanaryGuardDec n) Q False) : Q := by
  revert h
  refine ite_absurd_right_imp ?_ (fun hAbs => hAbs)
  intro hQ
  exact hQ

/-- Exercise `ite_eq_elim_imp` on the irreducible `iteCanaryGuard`: a value
`ite` that evaluates to its `else` value `1` refutes the guard. -/
theorem canary_ite_eq_elim_imp {n : Nat}
    (h : @ite Nat (iteCanaryGuard n) (iteCanaryGuardDec n) 0 1 = 1) :
    ¬ iteCanaryGuard n := by
  have h01 : (0 : Nat) ≠ 1 := by decide
  revert h
  refine ite_eq_elim_imp (fun _ h => False.elim (h01 h)) ?_
  intro hNP _
  exact hNP

/-- Exercise `ite_eq_true_imp` on the irreducible `iteCanaryGuard`. -/
theorem canary_ite_eq_true_imp {n m r : Nat} (hP : iteCanaryGuard n)
    (h : @ite Nat (iteCanaryGuard n) (iteCanaryGuardDec n) m 1 = r) :
    m = r := by
  revert h
  refine ite_eq_true_imp hP ?_
  intro hm
  exact hm

/-- Exercise `ite_eq_false_imp` on the irreducible `iteCanaryGuard`. -/
theorem canary_ite_eq_false_imp {n m r : Nat} (hNP : ¬ iteCanaryGuard n)
    (h : @ite Nat (iteCanaryGuard n) (iteCanaryGuardDec n) 0 m = r) :
    m = r := by
  revert h
  refine ite_eq_false_imp hNP ?_
  intro hm
  exact hm

/-- Exercise `ite_eq_absurd_left_imp` on the irreducible `iteCanaryGuard`. -/
theorem canary_ite_eq_absurd_left_imp {n m : Nat}
    (h : @ite Nat (iteCanaryGuard n) (iteCanaryGuardDec n) 0 m = 1) :
    m = 1 := by
  have h01 : (0 : Nat) ≠ 1 := by decide
  revert h
  refine ite_eq_absurd_left_imp h01 ?_
  intro hm
  exact hm

/-- Exercise `ite_eq_absurd_right_imp` on the irreducible `iteCanaryGuard`. -/
theorem canary_ite_eq_absurd_right_imp {n m : Nat}
    (h : @ite Nat (iteCanaryGuard n) (iteCanaryGuardDec n) m 0 = 1) :
    m = 1 := by
  have h01 : (0 : Nat) ≠ 1 := by decide
  revert h
  refine ite_eq_absurd_right_imp ?_ h01
  intro hm
  exact hm

end Anneal.Firewall

end
