import ToyProphecy.Calls

/-!
# Borrows selected at run time: the example `selIncr`

`selIncr` is `r0 = if x2 ≠ 0 { &mut x0 } else { &mut x1 }; *r0 = *r0 + 1; end r0`.
Both translations are proved correct on it for every initial store, and the
shapes of their specifications are stated exactly. Nothing beyond this example
is claimed here.
-/

namespace Toy.Prophecy

open Expr Op Stmt

/-- The lenders' values `(x, y)` as a function of a value `v` handed to the
chosen lender: the chosen lender gets `v`, the other keeps its value. This one
conditional map appears in both translations: the backward-function translation
applies it to the borrow's final value when the borrow *ends*; the prophecy
translation applies it to the borrow's prophecy when the borrow is *created*. -/
def selLenders (b : Bool) (x0 y0 : Int) (v : Int) : Int × Int :=
  if b then (v, y0) else (x0, v)

/-- Shape of a backward-function specification of a borrow selected at run time
between two locals with values `x0`, `y0`: the borrow's current value, and a
functional equation, universally quantified over the final value `v`, for the
backward function. -/
def SelBackSpec (b : Bool) (x0 y0 cur : Int) (back : Int → Int × Int) : Prop :=
  cur = (if b then x0 else y0) ∧ ∀ v, back v = selLenders b x0 y0 v

/-- Shape of a prophecy specification of the same borrow: its current value, and
a quantifier-free equation giving the lenders' values `(x', y')` in terms of the
single prophecy `fin`. -/
def SelProphSpec (b : Bool) (x0 y0 cur fin x' y' : Int) : Prop :=
  cur = (if b then x0 else y0) ∧ (x', y') = selLenders b x0 y0 fin

/-- The outcome of `selIncr` from store `σ`. -/
def selIncrOut (σ : Store) : Store :=
  if σ 2 ≠ 0 then σ.set 0 (σ 0 + 1) else σ.set 1 (σ 1 + 1)

theorem refSem_selIncr (σ : Store) : refSem selIncr σ = some (selIncrOut σ) := by
  by_cases h : σ 2 = 0 <;>
  simp [refSem, selIncr, runR, stepR, stepOpR, evalR, RState.init, fupd, selIncrOut, h]

theorem backSem_selIncr (σ : Store) : backSem selIncr σ = some (selIncrOut σ) := by
  by_cases h : σ 2 = 0 <;>
  · simp [backSem, selIncr, runB, stepB, stepOpB, evalB, BState.init, fupd, selIncrOut, h,
      selBack, applyBack]
    funext y
    by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;> simp_all [Store.set]

/-- **Both translations are correct on `selIncr`.** For every initial store, the
backward-function translation of `selIncr` computes the reference semantics'
outcome, and the prophecy translation admits exactly that outcome. -/
theorem selIncr_both_translations_correct (σ : Store) :
    backSem selIncr σ = refSem selIncr σ ∧
    ∀ σ', ProphOutcome selIncr σ σ' ↔ refSem selIncr σ = some σ' := by
  refine ⟨by rw [backSem_selIncr, refSem_selIncr], fun σ' => ?_⟩
  rw [refSem_selIncr]
  constructor
  · rintro ⟨φ, s, hrun, hsat, rfl⟩
    by_cases h : σ 2 = 0 <;>
    · simp [selIncr, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std, fupd,
        h] at hrun
      subst hrun
      simp [Sat] at hsat
      congr 1
      funext y
      by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;> simp_all [selIncrOut, Store.set]
  · intro hs
    cases hs
    by_cases h : σ 2 = 0
    · refine ⟨phiOf [σ 1 + 1], ?_⟩
      simp [selIncr, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std, fupd,
        h, Sat, phiOf]
      funext y
      by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;> simp_all [selIncrOut, Store.set]
    · refine ⟨phiOf [σ 0 + 1], ?_⟩
      simp [selIncr, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std, fupd,
        h, Sat, phiOf]
      funext y
      by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;> simp_all [selIncrOut, Store.set]

/-- The values of locals `x0` and `x1` after performing the lender assignments
`q.back v` of borrow `q` (backward function applied to final value `v`) on a
state with store `σ` and no live borrows; `(0, 0)` if performing them is stuck
(which happens only when `q.back v` writes to a borrow). -/
def backLenders01 (σ : Store) (q : BRef) (v : Int) : Int × Int :=
  ((applyBack { store := σ, refs := fun _ => none } (q.back v)).map
    fun s => (s.store 0, s.store 1)).getD (0, 0)

/-- **Backward-function shape on `selIncr`.** After the selection, the
backward-function translation holds one borrow whose current value is the chosen
lender's value and whose backward function, applied to any final value `v`, gives
the lenders `selLenders b (σ 0) (σ 1) v` (with `b` the condition); the store is
unchanged until the borrow ends. So its specification has the shape
`SelBackSpec`: a functional equation quantified over all final values. The
lender assignments `q.back v` succeed on every state (any store `τ`, any borrow
slots `refs`) and set the lenders to exactly `selLenders b (σ 0) (σ 1) v`. After
the whole program (the write and `end r0`), the lenders are exactly that backward
function applied to the borrow's final value `(chosen lender's value) + 1`. -/
theorem selIncr_backward_shape (σ : Store) :
    (∃ s q, runB (BState.init σ) [op (borrowSel 0 (var 2) 0 1)] = some s ∧
      s.refs 0 = some q ∧ s.store = σ ∧
      SelBackSpec (decide (σ 2 ≠ 0)) (σ 0) (σ 1) q.cur (backLenders01 σ q) ∧
      ∀ (τ : Store) (refs : RefVar → Option BRef) (v : Int),
        (applyBack { store := τ, refs := refs } (q.back v)).map
            (fun s' => (s'.store 0, s'.store 1)) =
          some (selLenders (decide (σ 2 ≠ 0)) (σ 0) (σ 1) v)) ∧
    (∃ s, runB (BState.init σ) selIncr = some s ∧
      (s.store 0, s.store 1) =
        selLenders (decide (σ 2 ≠ 0)) (σ 0) (σ 1) ((if σ 2 ≠ 0 then σ 0 else σ 1) + 1)) := by
  by_cases h : σ 2 = 0 <;>
  · simp [selIncr, runB, stepB, stepOpB, evalB, BState.init, fupd, h, SelBackSpec, selBack,
      applyBack, selLenders, Store.set, backLenders01]

/-- **Prophecy shape on `selIncr`.** After the selection, the prophecy translation
(any prophecy assignment `φ`) holds one borrow `(chosen lender's value, φ 0)`, has
drawn exactly one prophecy, and the lenders are `selLenders b (σ 0) (σ 1) (φ 0)`;
so the borrow satisfies `SelProphSpec` with the single prophecy `φ 0`. After the
whole program exactly one prophecy has been drawn and the only constraint is the
resolution `(final current value, φ 0)`, the same form for both values of the
condition. -/
theorem selIncr_prophecy_shape (σ : Store) (φ : Nat → Int) :
    (∃ s q, runP ResPolicy.std φ 0 (PState.init σ) [op (borrowSel 0 (var 2) 0 1)] = some s ∧
      s.next = 1 ∧ s.cs = [] ∧ s.refs 0 = some q ∧ q.fin = φ 0 ∧
      SelProphSpec (decide (σ 2 ≠ 0)) (σ 0) (σ 1) q.cur q.fin (s.store 0) (s.store 1)) ∧
    (∃ s, runP ResPolicy.std φ 0 (PState.init σ) selIncr = some s ∧ s.next = 1 ∧
      s.cs = [((if σ 2 ≠ 0 then σ 0 else σ 1) + 1, φ 0)]) := by
  by_cases h : σ 2 = 0 <;>
  · simp [selIncr, runP, stepP, stepOpP, evalP, PState.init, earlyCs, ResPolicy.std, fupd, h,
      SelProphSpec, selLenders, Store.set]

/-- **The case split cannot be avoided by either translation.** For any lender
values `x0`, `y0`, no single map `g` independent of the condition agrees with
`selLenders b x0 y0` for both values of `b`. In the backward-function translation
this map is the backward function (applied at the end); in the prophecy
translation it is the hand-over of the prophecy to the lenders (applied at
creation). -/
theorem selLenders_depends_on_condition (x0 y0 : Int) :
    ¬ ∃ g : Int → Int × Int, ∀ b v, g v = selLenders b x0 y0 v := by
  rintro ⟨g, hg⟩
  have h1 := hg true (x0 + 1)
  have h2 := hg false (x0 + 1)
  rw [h1] at h2
  simp [selLenders] at h2
  omega

end Toy.Prophecy
