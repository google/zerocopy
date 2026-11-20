/-
# Where fixpoint principles come from: Lawvere's diagonal and an abstract recursion theorem

Two short, fully proved diagonal arguments, each stated with its witness exposed.

* `lawvere_fixedPoint_of_represents_diagonal`: Lawvere's fixed-point theorem, stated for a class
  `G` of maps `A → Y` (the plain set-level theorem is the case `G = everything`). The fixed point
  is `φ a a` for any `a` representing the diagonal map.
* `diagonalFixedPoint_of_represents_diagonal_precompClosed`: an abstract form of Kleene's second
  recursion theorem. If every admissible transformer is computed by some code, `d` is a
  *diagonal* transformer, and precomposition with `d` preserves admissibility, then every
  admissible `f` has the semantic fixed point `d e` for any code `e` computing `f ∘ d`.

Neither result constructs a real computability model; see the module documentation of the
small models in `ToyRice.Models`.
-/
import ToyRice.Basic

namespace Toy.Rice

universe u v

/-! ## Lawvere's fixed-point theorem -/

/-- Witness form of Lawvere's argument: if code `a` represents the map `x ↦ t (φ x x)`, then
`φ a a` is a fixed point of `t`. -/
theorem lawvere_witness {A : Type u} {Y : Type v} (φ : A → A → Y) (t : Y → Y) {a : A}
    (ha : ∀ x, φ a x = t (φ x x)) : t (φ a a) = φ a a :=
  (ha a).symm

/-- **Lawvere's fixed-point theorem (class form, witness exposed).** Let `φ : A → A → Y`
represent every map in a class `G` (for each `g ∈ G` some `a` has `φ a = g` pointwise). If
`t : Y → Y` is such that the diagonal map `x ↦ t (φ x x)` is in `G`, then some `a` represents
that diagonal map, and for *every* such `a`, `φ a a` is a fixed point of `t`. -/
theorem lawvere_fixedPoint_of_represents_diagonal {A : Type u} {Y : Type v} (φ : A → A → Y)
    (G : (A → Y) → Prop) (hrep : ∀ g, G g → ∃ a, ∀ x, φ a x = g x) (t : Y → Y)
    (hdiag : G (fun x => t (φ x x))) :
    (∃ a, ∀ x, φ a x = t (φ x x)) ∧ (∀ a, (∀ x, φ a x = t (φ x x)) → t (φ a a) = φ a a) :=
  ⟨hrep _ hdiag, fun _ ha => lawvere_witness φ t ha⟩

/-- The bare existence form of Lawvere's theorem: `t` has a fixed point. A corollary. -/
theorem exists_fixedPoint_of_represents_diagonal {A : Type u} {Y : Type v} (φ : A → A → Y)
    (G : (A → Y) → Prop) (hrep : ∀ g, G g → ∃ a, ∀ x, φ a x = g x) (t : Y → Y)
    (hdiag : G (fun x => t (φ x x))) : ∃ y, t y = y := by
  obtain ⟨⟨a, ha⟩, hw⟩ := lawvere_fixedPoint_of_represents_diagonal φ G hrep t hdiag
  exact ⟨φ a a, hw a ha⟩

/-- For types and arbitrary functions, a weakly point-surjective `φ : A → A → Y` forces `Y` to
have at most one element (Cantor's theorem in Lawvere's form). Uses classical logic. -/
theorem subsingleton_of_weaklyPointSurjective {A : Type u} {Y : Type v} (φ : A → A → Y)
    (hsurj : ∀ g : A → Y, ∃ a, ∀ x, φ a x = g x) : ∀ y y' : Y, y = y' := by
  intro y y'
  apply Classical.byContradiction
  intro hne
  let t : Y → Y := fun z => @ite _ (z = y) (Classical.propDecidable _) y' y
  obtain ⟨z, hz⟩ := exists_fixedPoint_of_represents_diagonal φ (fun _ => True) (fun g _ => hsurj g)
    t trivial
  by_cases h : z = y
  · have : t z = y' := by simp [t, h]
    rw [hz, h] at this
    exact hne this
  · have : t z = y := by simp [t, h]
    rw [hz] at this
    exact h this

/-- **Cantor's theorem in Lawvere's form, sharp.** For types and arbitrary functions, a weakly
point-surjective `φ : A → A → Y` forces `Y` to have exactly one element: `Y` is nonempty and any
two elements are equal. Uses classical logic. -/
theorem nonempty_subsingleton_of_weaklyPointSurjective {A : Type u} {Y : Type v} (φ : A → A → Y)
    (hsurj : ∀ g : A → Y, ∃ a, ∀ x, φ a x = g x) : Nonempty Y ∧ ∀ y y' : Y, y = y' := by
  refine ⟨?_, subsingleton_of_weaklyPointSurjective φ hsurj⟩
  apply Classical.byContradiction
  intro hne
  have hempty : A → False := fun a => hne ⟨φ a a⟩
  obtain ⟨a, _⟩ := hsurj (fun a => (hempty a).elim)
  exact hempty a

/-! ## An abstract recursion theorem -/

variable {S : System.{u, v}}

/-- Every admissible transformer is *computed by a code* under the partial application
`app : Code → Code → Option Code` (`app e x = some z`: code `e` run on input `x` halts with
output code `z`; `none`: it diverges). In an acceptable numbering this is "every total
computable function has an index". -/
def Represents (S : System.{u, v}) (app : S.Code → S.Code → Option S.Code) : Prop :=
  ∀ f : S.Code → S.Code, S.Adm f → ∃ e, ∀ x, app e x = some (f x)

/-- `d` is a **diagonal** transformer for `app`: whenever `app x x` halts with output `z`, the
code `d x` behaves like `z`. In an acceptable numbering, the s-m-n theorem gives such a total
computable `d`: `d x` is an index of `y ↦ φ_{φ_x(x)}(y)`. -/
def IsDiagonal (S : System.{u, v}) (app : S.Code → S.Code → Option S.Code)
    (d : S.Code → S.Code) : Prop :=
  ∀ x z, app x x = some z → S.sem (d x) = S.sem z

/-- Closure law: precomposing an admissible transformer with `d` gives an admissible
transformer. -/
def PrecompClosed (S : System.{u, v}) (d : S.Code → S.Code) : Prop :=
  ∀ f : S.Code → S.Code, S.Adm f → S.Adm (f ∘ d)

/-- `PrecompClosed` follows from closure under composition when `d` is itself admissible. -/
theorem precompClosed_of_compClosed_adm {d : S.Code → S.Code} (hcomp : CompClosed S)
    (hd : S.Adm d) : PrecompClosed S d :=
  fun f hf => hcomp f d hf hd

/-- Witness form of the recursion theorem: if `e` computes `f ∘ d`, then `d e` is a semantic
fixed point of `f`. Uses only the diagonal property of `d`. -/
theorem kleene_witness {app : S.Code → S.Code → Option S.Code} {d : S.Code → S.Code}
    (hd : IsDiagonal S app d) (f : S.Code → S.Code) {e : S.Code}
    (he : ∀ x, app e x = some (f (d x))) : S.sem (f (d e)) = S.sem (d e) :=
  (hd e (f (d e)) (he e)).symm

/-- **Abstract recursion theorem (witness exposed).** If every admissible transformer is computed
by some code, `d` is a diagonal transformer, and precomposition with `d` preserves
admissibility, then for every admissible `f`: some code `e` computes `f ∘ d`, and for *every*
such `e` the code `d e` is a semantic fixed point of `f`. -/
theorem diagonalFixedPoint_of_represents_diagonal_precompClosed
    (app : S.Code → S.Code → Option S.Code) (d : S.Code → S.Code)
    (hrep : Represents S app) (hdiag : IsDiagonal S app d) (hpre : PrecompClosed S d) :
    ∀ f : S.Code → S.Code, S.Adm f →
      (∃ e, ∀ x, app e x = some (f (d x))) ∧
      (∀ e, (∀ x, app e x = some (f (d x))) → S.sem (f (d e)) = S.sem (d e)) :=
  fun f hf => ⟨hrep (f ∘ d) (hpre f hf), fun _ he => kleene_witness hdiag f he⟩

/-- The fixpoint principle follows (a corollary of the witness form). -/
theorem fixpointPrinciple_of_represents_diagonal_precompClosed
    (app : S.Code → S.Code → Option S.Code) (d : S.Code → S.Code)
    (hrep : Represents S app) (hdiag : IsDiagonal S app d) (hpre : PrecompClosed S d) :
    FixpointPrinciple S := by
  intro f hf
  obtain ⟨⟨e, he⟩, hw⟩ := diagonalFixedPoint_of_represents_diagonal_precompClosed app d hrep hdiag
    hpre f hf
  exact ⟨d e, hw e he⟩

/-- The abstract recursion theorem in its textbook shape: admissible transformers compose, every
admissible transformer is computed by a code, and there is an *admissible* diagonal
transformer. -/
theorem fixpointPrinciple_of_compClosed_represents_diagonal
    (app : S.Code → S.Code → Option S.Code) (d : S.Code → S.Code)
    (hcomp : CompClosed S) (hrep : Represents S app) (hdiag : IsDiagonal S app d)
    (hd : S.Adm d) : FixpointPrinciple S :=
  fixpointPrinciple_of_represents_diagonal_precompClosed app d hrep hdiag
    (precompClosed_of_compClosed_adm hcomp hd)

end Toy.Rice
