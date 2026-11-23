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

Two complementary mechanisms are provided:

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

/-! ## 3. Kernel-Checked Canaries -/

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

end Anneal.Firewall

end
