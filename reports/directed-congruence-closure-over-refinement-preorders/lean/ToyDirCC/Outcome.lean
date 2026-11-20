import ToyDirCC.Basic

/-!
# A set-of-outcomes model with choice operators

The carrier is `List Nat`, read as a finite set of possible outcomes of a nondeterministic
computation (order and multiplicity are representation only). The relation is
reverse inclusion: `OLe S T` ("`T` refines `S`") iff every outcome of `T` is an outcome of
`S` — a target may only remove behaviours. This mirrors the outcome-list semantics of
undef/poison models of LLVM-style IRs, without memory, UB or bit widths.

Operators (`OOp`):
* `lit n` — the single outcome `n`;
* `choose` — demonic nondeterministic choice between arguments 0 and 1 (union);
* `add` — all sums of an outcome of argument 0 and an outcome of argument 1, chosen
  independently;
* `pickMin` — commit to the least outcome of argument 0 (a deterministic resolution of
  nondeterminism, as an implementation of `freeze` may perform: it depends only on the
  outcome *set*, but refining the argument can change the committed outcome);
* `pickFirst` — commit to the first-listed outcome of argument 0 (depends on the
  representation, not only on the outcome set; it is definable only because outcome lists
  are not quotiented to sets).

Missing arguments are read as the empty list `[]`, which refines every outcome list
(`oLe_nil`).

`oProfile` declares `pickMin`'s argument `eqOnly`, `pickFirst`'s argument `opaqueArg`, and
every other position `mono`. `oModel` satisfies all four laws for `oProfile`
(`oModel_refl`, `oModel_trans`, `oModel_monoAt`, `oModel_kerAt`), while declaring
`pickMin` monotone or `pickFirst` equality-only is false (`oModel_not_monoAt_allMono`,
`oModel_not_kerAt_oProfileEq`).
-/

namespace Toy.DirCC

/-- Operators of the outcome model. -/
inductive OOp where
  | lit (n : Nat)
  | choose
  | add
  | pickMin
  | pickFirst
deriving Repr, DecidableEq

/-- Reverse inclusion of outcome lists: `OLe S T` iff every outcome of `T` is one of `S`
("`T` refines `S`"). -/
def OLe (S T : List Nat) : Prop := ∀ v, v ∈ T → v ∈ S

instance (S T : List Nat) : Decidable (OLe S T) :=
  inferInstanceAs (Decidable (∀ v, v ∈ T → v ∈ S))

/-- All sums `a + b` with `a ∈ S`, `b ∈ T` (independent choices). -/
def sums (S T : List Nat) : List Nat := S.flatMap (fun a => T.map (a + ·))

theorem mem_sums {S T : List Nat} {v : Nat} : v ∈ sums S T ↔ ∃ a ∈ S, ∃ b ∈ T, a + b = v := by
  simp [sums, List.mem_flatMap, List.mem_map]

/-- Commit to the least outcome (empty if there is none). -/
def leastOutcome (S : List Nat) : List Nat := S.min?.toList

/-- Commit to the first-listed outcome (empty if there is none). -/
def firstOutcome (S : List Nat) : List Nat := S.head?.toList

/-- Interpretation of the outcome operators (missing arguments read as the empty list). -/
def oInterp : OOp → List (List Nat) → List Nat
  | .lit n, _ => [n]
  | .choose, as => as.getD 0 [] ++ as.getD 1 []
  | .add, as => sums (as.getD 0 []) (as.getD 1 [])
  | .pickMin, as => leastOutcome (as.getD 0 [])
  | .pickFirst, as => firstOutcome (as.getD 0 [])

/-- The outcome model. -/
abbrev oModel : Model OOp where
  C := List Nat
  le := OLe
  interp := oInterp

/-- The intended profile of the outcome model. -/
def oProfile : Profile OOp
  | .pickMin, 0 => .eqOnly
  | .pickFirst, 0 => .opaqueArg
  | _, _ => .mono

/-- A mis-declared profile: as `oProfile`, but `pickFirst`'s argument is declared
`eqOnly`. -/
def oProfileEq : Profile OOp
  | .pickMin, 0 => .eqOnly
  | .pickFirst, 0 => .eqOnly
  | _, _ => .mono

theorem oModel_refl : LeRefl oModel := fun _ _ h => h

theorem oModel_trans : LeTrans oModel := fun _ _ _ h1 h2 v hv => h1 v (h2 v hv)

theorem olE_getD_hole {pre post : List (List Nat)} {x y : List Nat} (hxy : OLe x y) (j : Nat) :
    OLe ((pre ++ x :: post).getD j []) ((pre ++ y :: post).getD j []) := by
  by_cases h : j = pre.length
  · subst h; rw [getD_hole_self, getD_hole_self]; exact hxy
  · rw [getD_hole_ne pre post x y [] h]; exact fun _ hv => hv

theorem leastOutcome_congr {x y : List Nat} (hxy : OLe x y) (hyx : OLe y x) :
    leastOutcome x = leastOutcome y := by
  unfold leastOutcome
  cases hx : x.min? with
  | none =>
    rw [List.min?_eq_none_iff] at hx
    subst hx
    have : y = [] := by
      cases y with
      | nil => rfl
      | cons a _ => exact absurd (hxy a (List.mem_cons_self ..)) (by simp)
    subst this; rfl
  | some a =>
    rw [List.min?_eq_some_iff] at hx
    have hy : y.min? = some a := by
      rw [List.min?_eq_some_iff]
      exact ⟨hyx a hx.1, fun b hb => hx.2 b (hxy b hb)⟩
    rw [hy]

/-- Positive example for `MonoAt`: the outcome model is monotone at every position
`oProfile` declares `mono`. -/
theorem oModel_monoAt : MonoAt oProfile oModel := by
  intro f pre post x y hP hxy
  have hj := @olE_getD_hole pre post x y hxy
  cases f with
  | lit n => exact fun _ hv => hv
  | choose =>
    intro v hv
    simp only [oInterp, List.mem_append] at hv ⊢
    rcases hv with hv | hv
    · exact Or.inl (hj 0 v hv)
    · exact Or.inr (hj 1 v hv)
  | add =>
    intro v hv
    simp only [oInterp, mem_sums] at hv ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := hv
    exact ⟨a, hj 0 a ha, b, hj 1 b hb, rfl⟩
  | pickMin =>
    have h0 : 0 ≠ pre.length := by
      intro h; rw [← h] at hP; simp [oProfile] at hP
    show OLe (leastOutcome _) (leastOutcome _)
    rw [getD_hole_ne pre post x y [] h0]
    exact fun _ hv => hv
  | pickFirst =>
    have h0 : 0 ≠ pre.length := by
      intro h; rw [← h] at hP; simp [oProfile] at hP
    show OLe (firstOutcome _) (firstOutcome _)
    rw [getD_hole_ne pre post x y [] h0]
    exact fun _ hv => hv

/-- Positive example for `KerAt`: `pickMin` respects mutual refinement. -/
theorem oModel_kerAt : KerAt oProfile oModel := by
  intro f pre post x y hP hxy hyx
  cases f with
  | pickMin =>
    have h0 : pre = [] := by
      cases pre with
      | nil => rfl
      | cons _ _ => simp [oProfile] at hP
    subst h0
    show OLe (leastOutcome _) (leastOutcome _)
    simp only [List.nil_append, List.getD_cons_zero]
    rw [leastOutcome_congr hxy hyx]
    exact fun _ hv => hv
  | lit n => simp [oProfile] at hP
  | choose => simp [oProfile] at hP
  | add => simp [oProfile] at hP
  | pickFirst =>
    cases pre with
    | nil => simp [oProfile] at hP
    | cons _ _ => simp [oProfile] at hP

/-- Negative example for `MonoAt`: declaring every position monotone is false for the
outcome model, because `pickMin` is not monotone: `[1]` refines `[0, 1]` but the committed
outcome `[1]` does not refine `[0]`. -/
theorem oModel_not_monoAt_allMono : ¬ MonoAt (allMono OOp) oModel := by
  intro h
  have := h .pickMin [] [] [0, 1] [1] rfl (by decide)
  exact absurd this (by decide)

/-- Negative example for `KerAt`: declaring `pickFirst`'s argument `eqOnly` is false,
because `[0, 1]` and `[1, 0]` refine each other while their first outcomes do not. -/
theorem oModel_not_kerAt_oProfileEq : ¬ KerAt oProfileEq oModel := by
  intro h
  have := h .pickFirst [] [] [0, 1] [1, 0] rfl (by decide) (by decide)
  exact absurd this (by decide)

/-- The outcome relation is not antisymmetric, so mutual refinement is coarser than
equality and `opaqueArg` differs from `eqOnly` in this model. -/
theorem oModel_not_antisymm : OLe [0, 1] [1, 0] ∧ OLe [1, 0] [0, 1] ∧ ([0, 1] : List Nat) ≠ [1, 0] := by
  decide

/-- The empty outcome list refines every outcome list: it is the top element of the
refinement order (no behaviour at all), not a model of undefined behaviour (which would be
the set of all behaviours, refined by everything and not representable by a finite list).
Missing operator arguments are read as `[]`. -/
theorem oLe_nil (S : List Nat) : OLe S [] := fun _ h => by simp at h

/-- Example: `[]` refines `[0]`, but `[0]` does not refine `[]`. -/
theorem oLe_nil_example : OLe [0] [] ∧ ¬ OLe [] [0] := by decide

end Toy.DirCC
