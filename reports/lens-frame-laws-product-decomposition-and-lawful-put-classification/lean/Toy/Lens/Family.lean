/-
Toy.Lens.Family
===============

Families of lenses `l : (i : ι) → Lens S (A i)` on one state type: pairwise
cross-independence and joint extensionality, with proved positive and negative
examples.
-/
import Toy.Lens.Pair

namespace Toy

namespace Lens

universe u v w

variable {S : Type u} {ι : Type w} {A : ι → Type v}

/-! ## Pointwise update (core Lean has no `Function.update`) -/

/--
`update f i a` is the dependent function that agrees with `f` everywhere
except at index `i`, where it takes the value `a`.

Meant to capture "overwrite coordinate `i`".  `DecidableEq ι` is needed to
*state* `update`, and therefore `coord` and the conclusion `IsPiDecomposition`
of the indexed decomposition theorems.  The laws `PairwiseIndep` and
`FamJointExt` and the derived-law lemmas for families do not use it.
-/
def update [DecidableEq ι] (f : (i : ι) → A i) (i : ι) (a : A i) : (j : ι) → A j :=
  fun j => if h : j = i then h ▸ a else f j

/-- Positive example for `update`: it returns the new value at the updated index. -/
theorem update_same [DecidableEq ι] (f : (i : ι) → A i) (i : ι) (a : A i) :
    update f i a i = a := by
  simp [update]

/-- Positive example for `update`: it does not touch the other indices. -/
theorem update_of_ne [DecidableEq ι] (f : (i : ι) → A i) {i j : ι} (h : j ≠ i) (a : A i) :
    update f i a j = f j := by
  simp [update, h]

/-- Negative example for `update`: an update is in general *not* the identity. -/
theorem update_ne_self :
    update (fun _ : Bool => false) true true ≠ (fun _ : Bool => false) :=
  fun h => absurd (congrFun h true) (by decide)

/-! ## Definitions -/

/--
**Pairwise cross-independence** of a family: for all *distinct* indices `i`
and `j`, writing through `l i` leaves the view of `l j` unchanged.

Meant to capture the frame law "setting field `i` does not change any other
field".  Because it quantifies over ordered pairs `(i, j)`, it contains both
directions of `PutIndep` for every unordered pair.

Terminology note: as for `PutIndep`, this does *not* include commuting puts,
unlike pairwise lens independence (`⋈`) in the Isabelle AFP *Optics* entry.
-/
def PairwiseIndep (l : (i : ι) → Lens S (A i)) : Prop :=
  ∀ i j, i ≠ j → PutIndep (l i) (l j)

/--
**Joint extensionality** of a family: the views of all the lenses together
determine the state.

Meant to capture "the record has no component other than the listed fields".
It is exactly injectivity of `famGet l`.
-/
def FamJointExt (l : (i : ι) → Lens S (A i)) : Prop :=
  ∀ s t, (∀ i, (l i).get s = (l i).get t) → s = t

/--
The tuple of all views: the candidate isomorphism `S → (i : ι) → A i`
(the `ι`-indexed analogue of `pairGet`).
-/
def famGet (l : (i : ι) → Lens S (A i)) : S → (i : ι) → A i :=
  fun s i => (l i).get s

/--
The intended model for families: the `i`-th coordinate lens on the full
dependent product `(j : ι) → A j`.
-/
def coord [DecidableEq ι] (i : ι) : Lens ((j : ι) → A j) (A i) where
  get f := f i
  put f a := update f i a

/-! ## The coordinate lenses are very well-behaved -/

theorem coord_putGet [DecidableEq ι] (i : ι) : (coord (A := A) i).PutGet :=
  fun f a => update_same f i a

theorem coord_getPut [DecidableEq ι] (i : ι) : (coord (A := A) i).GetPut := by
  intro f
  funext j
  show update f i (f i) j = f j
  by_cases h : j = i
  · subst h
    exact update_same f j (f j)
  · exact update_of_ne f h (f i)

theorem coord_putPut [DecidableEq ι] (i : ι) : (coord (A := A) i).PutPut := by
  intro f a a'
  funext j
  show update (update f i a) i a' j = update f i a' j
  by_cases h : j = i
  · subst h
    rw [update_same, update_same]
  · rw [update_of_ne _ h, update_of_ne _ h, update_of_ne _ h]

theorem coord_veryWellBehaved [DecidableEq ι] (i : ι) : (coord (A := A) i).VeryWellBehaved :=
  ⟨coord_getPut i, coord_putGet i, coord_putPut i⟩

/-! ## `PairwiseIndep`: positive and negative examples -/

/-- Positive example for `PairwiseIndep`: the coordinate lenses. -/
theorem coord_pairwiseIndep [DecidableEq ι] :
    PairwiseIndep (fun i => coord (A := A) i) := by
  intro i j hij f a
  show update f i a j = f j
  exact update_of_ne f (fun h => hij h.symm) a

/-- Negative example for `PairwiseIndep`: an **aliasing** family, the same
lens `fst` at both indices. -/
theorem const_fst_not_pairwiseIndep :
    ¬ PairwiseIndep (fun _ : Bool => (fst : Lens (Bool × Bool) Bool)) :=
  fun h => absurd (h false true (by decide) (false, false) true) (by decide)

/-! ## `FamJointExt`: positive and negative examples -/

/-- Positive example for `FamJointExt`: the coordinate lenses. -/
theorem coord_famJointExt [DecidableEq ι] :
    FamJointExt (fun i => coord (A := A) i) :=
  fun _ _ h => funext h

/-- A two-field family on a record with a ghost third component. -/
def ghostFam : (i : Bool) → Lens (Bool × Bool × Bool) Bool
  | false => ghostFst
  | true => ghostSnd

/-- Negative example for `FamJointExt`: a family on a record with a **ghost**
component. -/
theorem ghostFam_not_famJointExt : ¬ FamJointExt ghostFam := by
  intro h
  have h' := h (false, false, false) (false, false, true) (fun i => by cases i <;> rfl)
  exact absurd h' (by decide)

/-! ## `famGet`: positive and negative examples -/

/-- Positive example for `famGet`: for the coordinate lenses it is the
identity. -/
theorem famGet_coord [DecidableEq ι] (f : (j : ι) → A j) :
    famGet (fun i => coord (A := A) i) f = f :=
  rfl

/-- Negative example for `famGet`: for the ghost family it forgets the ghost
component (it is not injective). -/
theorem famGet_ghostFam_not_injective : ¬ Function.Injective (famGet ghostFam) := by
  intro h
  have h' : ((false, false, false) : Bool × Bool × Bool) = (false, false, true) :=
    h (funext fun i => by cases i <;> rfl)
  exact absurd h' (by decide)

end Lens

end Toy
