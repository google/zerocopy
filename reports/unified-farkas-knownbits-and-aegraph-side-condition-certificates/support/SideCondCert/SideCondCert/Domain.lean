-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

namespace SideCondCert

/-- Semantic value domain with explicit deferred undefinedness (`poison`),
modeling LLVM / `MiniSSA` `nuw`/`nsw`/`exact` poison propagation and `freeze`. -/
inductive PoisonOr (α : Type) where
  | val (v : α)
  | poison
  deriving DecidableEq, Repr

/-- Directed poison-refinement relation `vSrc ⊑_poison vTgt`:
the target expression is at least as defined as the source expression (if `vSrc`
is a defined value `.val v`, `vTgt` must also evaluate to `.val v`; if `vSrc` is
`.poison`, `vTgt` may refine it to any value or remain `.poison`). -/
def refinesPoison {α : Type} (vSrc vTgt : PoisonOr α) : Prop :=
  vSrc = .poison ∨ vTgt = vSrc

theorem refinesPoison_refl {α : Type} (v : PoisonOr α) : refinesPoison v v :=
  Or.inr rfl

theorem refinesPoison_trans {α : Type} {v1 v2 v3 : PoisonOr α}
    (h12 : refinesPoison v1 v2) (h23 : refinesPoison v2 v3) : refinesPoison v1 v3 := by
  rcases h12 with rfl | rfl
  · exact Or.inl rfl
  · exact h23

theorem refinesPoison_of_eq {α : Type} {v1 v2 : PoisonOr α} (h : v1 = v2) :
    refinesPoison v1 v2 :=
  Or.inr h.symm

/-- Lift a binary operation onto `PoisonOr α` (strictly propagating `.poison`). -/
def liftPoison2 {α : Type} (f : α → α → PoisonOr α) (x y : PoisonOr α) : PoisonOr α :=
  match x, y with
  | .val a, .val b => f a b
  | _, _           => .poison

/-- Monotonicity law: any binary operation lifted via `liftPoison2` is automatically
monotonic with respect to `refinesPoison` in both arguments! -/
theorem liftPoison2_mono {α : Type} (f : α → α → PoisonOr α)
    {x1 x2 y1 y2 : PoisonOr α}
    (hx : refinesPoison x1 x2) (hy : refinesPoison y1 y2) :
    refinesPoison (liftPoison2 f x1 y1) (liftPoison2 f x2 y2) := by
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · rcases hy with rfl | rfl
    · cases x2 <;> exact Or.inl rfl
    · exact Or.inr rfl

/-- `freeze` operator: maps `.poison` to a deterministic default value `defaultVal`
while preserving all non-poison values `.val a`. -/
def freezePoison {α : Type} (defaultVal : α) : PoisonOr α → PoisonOr α
  | .val a  => .val a
  | .poison => .val defaultVal

/-- `freeze (val a)` simplifies directly to `val a`. -/
theorem freezePoison_val {α : Type} (d a : α) :
    freezePoison d (.val a) = .val a := rfl

/-- Any expression `v` is poison-refined by `freezePoison d v`? Wait: if `v = .poison`,
`freezePoison d v = .val d`, so `refinesPoison v (freezePoison d v)` holds for ALL `v`! -/
theorem refinesPoison_freeze {α : Type} (d : α) (v : PoisonOr α) :
    refinesPoison v (freezePoison d v) := by
  cases v with
  | val a  => exact Or.inr rfl
  | poison => exact Or.inl rfl

end SideCondCert
