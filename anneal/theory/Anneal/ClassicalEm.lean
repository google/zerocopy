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
public import Init.NotationExtra
public import Init.Tactics

public section

/-!
# Foundation-Locked Classical Excluded Middle & Choice (`Anneal.ClassicalEm`)

Anneal's 51 locked `Init.*` foundation modules exclude `Init.Classical`, and
`TrustedBoundary.allowedTheoryTacticKinds` excludes `by_cases`. This module
derives Diaconescu's theorem (`prop_em : p ∨ ¬ p`), double-negation elimination
(`of_not_not`), proof by contradiction (`by_contra`), classical logical bridges
(`imp_iff_not_or`, `not_and_iff_or_not`), and existential witness selection
(`chooseExists` / `chooseExists_spec`) directly from `Init.Core` using only
`[propext, Classical.choice, Quot.sound]` (`Quot.sound` via `funext`) and
allowed Pass-1 tactics (`0` `._unsafe_rec`).

Usage in Pass-1 proofs (replacing `by_cases h : P`):
```lean
cases prop_em P with
| inl h => ...
| inr h => ...
```
-/

namespace Anneal.ClassicalEm

/-! ## 1. Classical Choice and Excluded Middle -/

/-- Extracts a witness from `Nonempty (Subtype P)` using `Classical.choice`. -/
@[expose] noncomputable def chooseSub {α : Sort u} {P : α → Prop}
    (h : Nonempty (Subtype P)) : α :=
  (Classical.choice h).1

/-- Specification of `chooseSub`: the chosen witness satisfies `P`. -/
theorem chooseSub_spec {α : Sort u} {P : α → Prop}
    (h : Nonempty (Subtype P)) : P (chooseSub h) :=
  (Classical.choice h).2

private noncomputable def chooseBool (P : Bool → Prop)
    (h : Nonempty (Subtype P)) : Bool :=
  (Classical.choice h).1

private theorem chooseBool_spec (P : Bool → Prop)
    (h : Nonempty (Subtype P)) : P (chooseBool P h) :=
  (Classical.choice h).2

private theorem chooseBool_congr {P Q : Bool → Prop} (hPQ : P = Q)
    (hP : Nonempty (Subtype P)) (hQ : Nonempty (Subtype Q)) :
    chooseBool P hP = chooseBool Q hQ := by
  subst hPQ
  rfl

private theorem bool_eq_or_ne (a b : Bool) : a = b ∨ a ≠ b := by
  cases a with
  | false =>
    cases b with
    | false => exact Or.inl rfl
    | true => exact Or.inr (fun h => by nomatch h)
  | true =>
    cases b with
    | false => exact Or.inr (fun h => by nomatch h)
    | true => exact Or.inl rfl

/-- Diaconescu's theorem (`p ∨ ¬ p`) over `prelude` + `Init.Core` without
`Init.Classical`, replacing banned `by_cases` via `cases prop_em p`. -/
theorem prop_em (p : Prop) : p ∨ ¬ p := by
  let U (x : Bool) : Prop := x = true ∨ p
  let V (x : Bool) : Prop := x = false ∨ p
  have exU : Nonempty (Subtype U) := ⟨⟨true, Or.inl rfl⟩⟩
  have exV : Nonempty (Subtype V) := ⟨⟨false, Or.inl rfl⟩⟩
  have hu : U (chooseBool U exU) := chooseBool_spec U exU
  have hv : V (chooseBool V exV) := chooseBool_spec V exV
  cases bool_eq_or_ne (chooseBool U exU) (chooseBool V exV) with
  | inr hne =>
    refine Or.inr ?_
    intro hp
    have hUV : U = V := by
      funext x
      exact propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
    exact hne (chooseBool_congr hUV exU exV)
  | inl heq =>
    cases hu with
    | inr hp => exact Or.inl hp
    | inl hut =>
      cases hv with
      | inr hp => exact Or.inl hp
      | inl hvf =>
        rw [hut, hvf] at heq
        nomatch heq

/-- Classical double-negation elimination derived from `prop_em`. -/
theorem of_not_not {p : Prop} (hnn : ¬ ¬ p) : p := by
  cases prop_em p with
  | inl hp => exact hp
  | inr hnp => exact False.elim (hnn hnp)

/-- Classical proof by contradiction (`(¬ p → False) → p`). -/
theorem by_contra {p : Prop} (h : ¬ p → False) : p :=
  of_not_not h

/-- Classical equivalence between `p → q` and `¬ p ∨ q`. -/
theorem imp_iff_not_or (p q : Prop) : (p → q) ↔ (¬ p ∨ q) := by
  constructor
  · intro hpq
    cases prop_em p with
    | inl hp => exact Or.inr (hpq hp)
    | inr hnp => exact Or.inl hnp
  · intro h hp
    cases h with
    | inl hnp => exact False.elim (hnp hp)
    | inr hq => exact hq

/-- Classical De Morgan equivalence (`¬ (p ∧ q) ↔ (¬ p ∨ ¬ q)`). -/
theorem not_and_iff_or_not (p q : Prop) : ¬ (p ∧ q) ↔ (¬ p ∨ ¬ q) := by
  constructor
  · intro hna
    cases prop_em p with
    | inr hnp => exact Or.inl hnp
    | inl hp =>
      exact Or.inr (fun hq => hna ⟨hp, hq⟩)
  · intro hor hpq
    cases hor with
    | inl hnp => exact hnp hpq.1
    | inr hnq => exact hnq hpq.2

/-- Selects a witness from an existential proof using `Classical.choice`.

Uses a pure elimination term rather than a `by` block so Lean can export the
`@[expose]` body cleanly in `module` mode without stuck metavariables. -/
@[expose] noncomputable def chooseExists {α : Sort u} {P : α → Prop}
    (h : ∃ x : α, P x) : α :=
  chooseSub (Exists.elim h fun w hw => ⟨⟨w, hw⟩⟩)

/-- Specification of `chooseExists`: the selected witness satisfies `P`. -/
theorem chooseExists_spec {α : Sort u} {P : α → Prop}
    (h : ∃ x : α, P x) : P (chooseExists h) :=
  chooseSub_spec (Exists.elim h fun w hw => ⟨⟨w, hw⟩⟩)

/-! ## 2. Kernel-Checked Canaries -/

/-- Canary exercising `prop_em` on concrete propositions `True` and `False`. -/
theorem canary_prop_em_concrete : (True ∨ ¬ True) ∧ (False ∨ ¬ False) :=
  ⟨prop_em True, prop_em False⟩

/-- Canary exercising `of_not_not` and `by_contra` on an arbitrary `Prop`. -/
theorem canary_not_not_by_contra (p : Prop) :
    (¬ ¬ p → p) ∧ ((¬ p → False) → p) :=
  ⟨of_not_not, by_contra⟩

/-- Canary exercising `imp_iff_not_or` and `not_and_iff_or_not`. -/
theorem canary_logic_bridges (p q : Prop) :
    ((p → q) ↔ (¬ p ∨ q)) ∧ (¬ (p ∧ q) ↔ (¬ p ∨ ¬ q)) :=
  ⟨imp_iff_not_or p q, not_and_iff_or_not p q⟩

/-- Canary exercising `chooseExists` on an inhabited positive `Nat` witness. -/
theorem canary_chooseExists_pos :
    0 < chooseExists (⟨1, Nat.zero_lt_succ 0⟩ : ∃ n : Nat, 0 < n) :=
  chooseExists_spec ⟨1, Nat.zero_lt_succ 0⟩

/-- Canary refuting an unsatisfiable existential via `chooseExists`. -/
theorem canary_chooseExists_false_rejected : ¬ ∃ n : Nat, n < n :=
  fun h => Nat.lt_irrefl (chooseExists h) (chooseExists_spec h)

end Anneal.ClassicalEm

end
