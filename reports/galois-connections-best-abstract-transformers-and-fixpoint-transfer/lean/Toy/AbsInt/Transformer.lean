/-
Toy.AbsInt.Transformer
======================

Best abstract transformers (cards `R2-best-sound`, `R2-best-least`,
`R2-best-mono`) and the precision loss of composing them (cards `R3-comp-le`,
`R3-comp-strict`), with definition examples, tightness counterexamples,
non-vacuity witnesses and boundary examples.
-/
import Toy.AbsInt.Sign

namespace Toy.AbsInt

section Defs
variable {σ A : Type} [LE A]

/-- The best abstract transformer `f♯ = α ∘ f ∘ γ` of a concrete transformer
`f` (Cousot & Cousot 1979): concretize, apply the concrete transformer, and
abstract the result. -/
def bestTransformer (α : Pred σ → A) (γ : A → Pred σ) (f : Pred σ → Pred σ) : A → A :=
  fun a => α (f (γ a))

/-- Soundness of an abstract transformer `fs` for a concrete transformer `f`,
stated through `γ` only: for every abstract input `a`, the concrete image
`f (γ a)` of the *whole* set described by `a` is described by `fs a`
(`f ∘ γ ⊆ γ ∘ fs`, pointwise).

This constrains `f` only on sets of the form `γ a`.  For monotone `f` it implies
soundness on every subset `x ⊆ γ a` (`sound_le_of_le_gamma_of_monotone`); for
non-monotone `f` it need not (`sound_not_subset_of_not_monotone`). -/
def Sound (γ : A → Pred σ) (f : Pred σ → Pred σ) (fs : A → A) : Prop :=
  ∀ a, f (γ a) ≤ γ (fs a)

end Defs

/-- Concrete transformer of a deterministic assignment `s := h s`: the image
(strongest postcondition) of a set of states. -/
def post {σ : Type} (h : σ → σ) (x : Pred σ) : Pred σ := fun t' => ∃ s, x s ∧ h s = t'

theorem post_monotone {σ : Type} (h : σ → σ) : Monotone (post h) :=
  fun _ _ hxy _ ⟨s, hs, he⟩ => ⟨s, hxy s hs, he⟩

/-- Complement of a predicate: a non-monotone concrete transformer used in
counterexamples. -/
def compl {σ : Type} (x : Pred σ) : Pred σ := fun s => ¬ x s

/-- Increment and decrement of an integer variable. -/
def incr (n : Int) : Int := n + 1
def decr (n : Int) : Int := n - 1

/-! ## Main results -/

section Main
variable {σ A : Type} [LE A]

/-- **Soundness of the best transformer** (card `R2-best-sound`).  If `α`, `γ`
form a Galois connection and the abstract order is reflexive, the best
transformer `α ∘ f ∘ γ` is `γ`-sound (`Sound`) for any concrete transformer `f`;
monotonicity of `f` is not needed for this `γ`-form, but is needed to lift it to
subsets of `γ a` (see `Sound`). -/
theorem bestTransformer_sound_of_galoisConnection_of_refl
    (hrefl : IsRefl A) {α : Pred σ → A} {γ : A → Pred σ}
    (hgc : GaloisConnection α γ) (f : Pred σ → Pred σ) :
    Sound γ f (bestTransformer α γ f) :=
  fun _ => (hgc _ _).mp (hrefl _)

/-- **Sound iff above the best transformer** (card `R2-best-least`).  If `α`, `γ`
form a Galois connection, an abstract transformer `fs` is `γ`-sound for `f`
exactly when it lies pointwise above `α ∘ f ∘ γ`.  Hence `α ∘ f ∘ γ` is a
pointwise lower bound of all `γ`-sound transformers; it is guaranteed to be sound
itself (hence a least sound transformer) when the order is also reflexive
(`R2-best-sound`), and without reflexivity it can fail to be sound.  No
order law and no monotonicity of `f` or `fs` is assumed. -/
theorem sound_iff_bestTransformer_le_of_galoisConnection
    {α : Pred σ → A} {γ : A → Pred σ} (hgc : GaloisConnection α γ)
    (f : Pred σ → Pred σ) (fs : A → A) :
    Sound γ f fs ↔ ∀ a, bestTransformer α γ f a ≤ fs a :=
  ⟨fun h a => (hgc _ _).mpr (h a), fun h a => (hgc _ _).mp (h a)⟩

/-- **Monotonicity of the best transformer** (card `R2-best-mono`).  If `α`, `γ`
form a Galois connection over a reflexive, transitive abstract order and `f` is
monotone, the best transformer `α ∘ f ∘ γ` is monotone. -/
theorem bestTransformer_monotone_of_galoisConnection_of_refl_of_trans_of_monotone
    (hrefl : IsRefl A) (htrans : IsTrans A) {α : Pred σ → A} {γ : A → Pred σ}
    (hgc : GaloisConnection α γ) {f : Pred σ → Pred σ} (hf : Monotone f) :
    Monotone (bestTransformer α γ f) := by
  have hext : Extensive α γ := fun x => (hgc x (α x)).mp (hrefl (α x))
  have hred : Reductive α γ := fun a => (hgc (γ a) a).mpr (Pred.le_refl (γ a))
  have hα : Monotone α := fun _ _ hxy => (hgc _ _).mpr (Pred.le_trans hxy (hext _))
  have hγ : Monotone γ := fun _ _ hab => (hgc _ _).mp (htrans _ _ _ (hred _) hab)
  exact fun _ _ hab => hα _ _ (hf _ _ (hγ _ _ hab))

/-! ## Composition of best transformers (fully proved) -/

/-- **Composition is no more precise** (card `R3-comp-le`).  If `α`, `γ` form a
Galois connection over a reflexive abstract order and `f` is monotone, the best
transformer of a composition is below the composition of best transformers:
`(f ∘ g)♯ a ≤ f♯ (g♯ a)` for every `g` and every `a`.  Transitivity of the order
and monotonicity of `g` are not needed. -/
theorem bestTransformer_comp_le_of_galoisConnection_of_refl_of_monotone
    (hrefl : IsRefl A) {α : Pred σ → A} {γ : A → Pred σ}
    (hgc : GaloisConnection α γ) {f : Pred σ → Pred σ} (hf : Monotone f)
    (g : Pred σ → Pred σ) (a : A) :
    bestTransformer α γ (f ∘ g) a ≤ bestTransformer α γ f (bestTransformer α γ g a) := by
  have ext : ∀ x, x ≤ γ (α x) := fun x => (hgc x (α x)).mp (hrefl _)
  show α (f (g (γ a))) ≤ α (f (γ (α (g (γ a)))))
  exact (hgc _ _).mpr (Pred.le_trans (hf _ _ (ext _)) (ext _))

end Main

/-! ## Further fixtures -/

/-- A two-point non-emptiness abstraction of `Pred Bool`: `lo` for the empty set,
`hi` for every non-empty set.  It is not exact: a non-empty proper subset such as
`{true}` is abstracted to `hi`, whose concretization is the full set. -/
noncomputable def boolAlpha (x : Pred Bool) : B2 :=
  open Classical in if x ≤ Pred.empty Bool then .lo else .hi

def boolGamma : B2 → Pred Bool
  | .lo => Pred.empty Bool
  | .hi => Pred.univ Bool

theorem bool_gc : GaloisConnection boolAlpha boolGamma := by
  intro x a
  unfold boolAlpha
  by_cases hx : x ≤ Pred.empty Bool
  · simp only [hx, ite_true]
    exact ⟨fun _ => fun s hs => (hx s hs).elim, fun _ => by cases a <;> decide⟩
  · simp only [hx, ite_false]
    cases a
    · exact ⟨fun h => absurd h (by decide), fun h => absurd h hx⟩
    · exact ⟨fun _ => le_U x, fun _ => by decide⟩

theorem boolAlpha_of_mem {x : Pred Bool} (s : Bool) (hs : x s) : boolAlpha x = .hi := by
  unfold boolAlpha
  have hx : ¬ x ≤ Pred.empty Bool := fun h => h s hs
  simp only [hx, ite_false]

theorem boolAlpha_of_empty {x : Pred Bool} (h : ∀ s, ¬ x s) : boolAlpha x = .lo := by
  unfold boolAlpha
  have hx : x ≤ Pred.empty Bool := fun s hs => h s hs
  simp only [hx, ite_true]

/-! ## Definition examples (proved) -/

theorem sound_example_pos : Sound signGamma (post incr) (fun _ => Sign.top) :=
  fun _ _ _ => trivial

/-- Negative example: the transformer that always answers `bot` is not sound for
`x := x + 1` (from `pos` the concrete result contains `2`). -/
theorem sound_example_neg : ¬ Sound signGamma (post incr) (fun _ => Sign.bot) :=
  fun h => h Sign.pos 2 ⟨1, by show (0:Int) < 1; omega, rfl⟩

theorem post_example_pos : post incr (signGamma .zero) 1 := ⟨0, rfl, rfl⟩

theorem post_example_neg : ¬ post incr (signGamma .zero) 0 := by
  intro ⟨s, hs, he⟩
  have h1 : s = 0 := hs
  have h2 : s + 1 = 0 := he
  omega

theorem bestTransformer_incr_pos :
    bestTransformer signAlpha signGamma (post incr) .pos = .pos := by
  apply signAlpha_eq_pos
  · exact ⟨2, 1, by show (0:Int) < 1; omega, rfl⟩
  · intro t ⟨s, hs, he⟩
    have h1 : (0:Int) < s := hs
    have h2 : s + 1 = t := he
    omega

theorem bestTransformer_decr_pos :
    bestTransformer signAlpha signGamma (post decr) .pos = .top := by
  apply signAlpha_eq_top
  · exact ⟨1, by show (0:Int) < 1; omega, rfl⟩
  · exact ⟨1, ⟨2, by show (0:Int) < 2; omega, rfl⟩, by omega⟩

theorem bestTransformer_decr_comp_incr_pos :
    bestTransformer signAlpha signGamma (post decr ∘ post incr) .pos = .pos := by
  apply signAlpha_eq_pos
  · exact ⟨1, 2, ⟨1, by show (0:Int) < 1; omega, rfl⟩, rfl⟩
  · intro t ⟨s, ⟨r, hr, hrs⟩, hst⟩
    have h1 : (0:Int) < r := hr
    have h2 : r + 1 = s := hrs
    have h3 : s - 1 = t := hst
    omega

/-- Positive example: the best transformer of `x := x + 1` maps `pos` to `pos`. -/
theorem bestTransformer_example_pos :
    bestTransformer signAlpha signGamma (post incr) .pos = .pos := bestTransformer_incr_pos

/-- Negative example: the best transformer of `x := x - 1` does **not** map
`pos` to `pos` (decrementing `1` gives `0`); it maps it to `top`. -/
theorem bestTransformer_example_neg :
    bestTransformer signAlpha signGamma (post decr) .pos ≠ .pos := by
  rw [bestTransformer_decr_pos]; decide

/-! ## Non-vacuity witnesses (proved) -/

/-- Non-vacuity for `R1-gc-iff` and `R1-gc-forward`: the sign domain is
reflexive, transitive, and forms a Galois connection with `Pred Int`. -/
theorem gc_nonvacuous :
    IsRefl Sign ∧ IsTrans Sign ∧ GaloisConnection signAlpha signGamma :=
  ⟨Sign.isRefl, Sign.isTrans, signGC⟩

/-- Non-vacuity for `R1-gc-backward`: the sign domain satisfies all hypotheses
(derived directly from the proved connection `signGC`). -/
theorem gcBackward_nonvacuous :
    IsTrans Sign ∧ Monotone signAlpha ∧ Monotone signGamma ∧
      Extensive signAlpha signGamma ∧ Reductive signAlpha signGamma := by
  have ext : Extensive signAlpha signGamma :=
    fun x => (signGC x (signAlpha x)).mp (Sign.isRefl _)
  refine ⟨Sign.isTrans, ?_, signGamma_monotone, ext, ?_⟩
  · intro x y hxy
    exact (signGC x (signAlpha y)).mpr (Pred.le_trans hxy (ext y))
  · intro a
    exact (signGC (signGamma a) a).mpr (Pred.le_refl _)

/-- Non-vacuity for `R2-best-sound` and `R2-best-least`: hypotheses hold for the
sign domain. -/
theorem bestSound_nonvacuous : IsRefl Sign ∧ GaloisConnection signAlpha signGamma :=
  ⟨Sign.isRefl, signGC⟩

/-- Non-vacuity for `R2-best-mono`: hypotheses hold for the sign domain with
`x := x + 1`. -/
theorem bestMono_nonvacuous :
    IsRefl Sign ∧ IsTrans Sign ∧ GaloisConnection signAlpha signGamma ∧
      Monotone (post incr) :=
  ⟨Sign.isRefl, Sign.isTrans, signGC, post_monotone _⟩

/-- Non-vacuity for `R3-comp-le`: hypotheses hold for the sign domain with `f`
the concrete transformer of `x := x - 1`. -/
theorem compLe_nonvacuous :
    IsRefl Sign ∧ GaloisConnection signAlpha signGamma ∧ Monotone (post decr) :=
  ⟨Sign.isRefl, signGC, post_monotone _⟩

/-! ## Strict precision loss in the sign domain (proved) -/

/-- **Composition can lose precision strictly** (card `R3-comp-strict`).  In the
sign domain, for `g` = `x := x + 1` and `f` = `x := x - 1`, every hypothesis of
`R3-comp-le` holds, `(f ∘ g)♯ pos = pos`, but `f♯ (g♯ pos) = top`, so
`(f ∘ g)♯ pos < f♯ (g♯ pos)` strictly. -/
theorem bestTransformer_comp_strict_sign :
    GaloisConnection signAlpha signGamma ∧ IsRefl Sign ∧ IsTrans Sign ∧
      Monotone (post decr) ∧ Monotone (post incr) ∧
      bestTransformer signAlpha signGamma (post incr) .pos = .pos ∧
      bestTransformer signAlpha signGamma (post decr) .pos = .top ∧
      bestTransformer signAlpha signGamma (post decr ∘ post incr) .pos = .pos ∧
      StrictLt (bestTransformer signAlpha signGamma (post decr ∘ post incr) .pos)
        (bestTransformer signAlpha signGamma (post decr)
          (bestTransformer signAlpha signGamma (post incr) .pos)) := by
  refine ⟨signGC, Sign.isRefl, Sign.isTrans, post_monotone _, post_monotone _,
    bestTransformer_incr_pos, bestTransformer_decr_pos, bestTransformer_decr_comp_incr_pos, ?_⟩
  rw [bestTransformer_incr_pos, bestTransformer_decr_pos, bestTransformer_decr_comp_incr_pos]
  decide

/-- Positive control for `R3-comp-strict`: in the same sign domain, composing
`x := x + 1` with itself loses nothing at `pos`:
`(incr ∘ incr)♯ pos = pos = incr♯ (incr♯ pos)`.  Strictness is a property of
particular instances, not of composition as such. -/
theorem bestTransformer_comp_exact_sign_incr :
    bestTransformer signAlpha signGamma (post incr ∘ post incr) .pos = .pos ∧
      bestTransformer signAlpha signGamma (post incr)
        (bestTransformer signAlpha signGamma (post incr) .pos) = .pos := by
  refine ⟨?_, ?_⟩
  · apply signAlpha_eq_pos
    · exact ⟨3, 2, ⟨1, by show (0:Int) < 1; omega, rfl⟩, rfl⟩
    · intro t ⟨s, ⟨r, hr, hrs⟩, hst⟩
      have h1 : (0:Int) < r := hr
      have h2 : r + 1 = s := hrs
      have h3 : s + 1 = t := hst
      omega
  · rw [bestTransformer_incr_pos, bestTransformer_incr_pos]

/-! ## Tightness counterexamples (proved) -/

/-- `R2-best-sound` needs reflexivity: over the transitive, non-reflexive `NR2`, the
best transformer of the constant-full transformer is unsound. -/
theorem bestSound_tight_refl :
    ¬ IsRefl NR2 ∧ GaloisConnection nr2Alpha nr2Gamma ∧
      ¬ Sound nr2Gamma (fun _ => U) (bestTransformer nr2Alpha nr2Gamma (fun _ => U)) :=
  ⟨NR2.not_isRefl, nr2_gc, fun h => not_U_le_E (h NR2.lo)⟩

/-- `R2-best-sound` needs the Galois connection: over the reflexive `B2`, constant
`α = lo` and constant `γ = ∅` give an unsound best transformer. -/
theorem bestSound_tight_gc :
    IsRefl B2 ∧ ¬ GaloisConnection (fun _ : Pred Unit => B2.lo) (fun _ : B2 => E) ∧
      ¬ Sound (fun _ : B2 => E) (fun _ => U)
          (bestTransformer (fun _ : Pred Unit => B2.lo) (fun _ : B2 => E) (fun _ => U)) :=
  ⟨B2.isRefl, galoisConnection_example_neg, fun h => not_U_le_E (h B2.lo)⟩

/-- `R2-best-least` needs the Galois connection: with `α` constantly `hi` and `γ`
constantly `{()}` on `B2`, the constant-`lo` transformer is sound for the
identity but not above the "best" transformer. -/
theorem soundIff_tight_gc :
    IsRefl B2 ∧ IsTrans B2 ∧
      ¬ GaloisConnection (fun _ : Pred Unit => B2.hi) (fun _ : B2 => U) ∧
      ¬ (Sound (fun _ : B2 => U) id (fun _ => B2.lo) ↔
          ∀ a, bestTransformer (fun _ : Pred Unit => B2.hi) (fun _ : B2 => U) id a ≤
            (fun _ => B2.lo) a) :=
  ⟨B2.isRefl, B2.isTrans, gcBackward_tight_reductive.2.2.2.2.2,
    fun h => absurd (h.mp (fun _ => Pred.le_refl _) B2.lo) (by decide)⟩

/-- `R2-best-mono` needs monotone `f`: for the exact two-point instance and `f` the
complement, the best transformer swaps `lo` and `hi`. -/
theorem bestMono_tight_monoF :
    IsRefl B2 ∧ IsTrans B2 ∧ GaloisConnection b2Alpha b2Gamma ∧
      ¬ Monotone (compl : Pred Unit → Pred Unit) ∧
      ¬ Monotone (bestTransformer b2Alpha b2Gamma compl) := by
  refine ⟨B2.isRefl, B2.isTrans, b2_gc, ?_, ?_⟩
  · intro h
    exact h E U (le_U E) () (fun h' => h') trivial
  · intro h
    have := h B2.lo B2.hi (by decide)
    have e1 : bestTransformer b2Alpha b2Gamma compl B2.lo = B2.hi :=
      unitAlpha_pos _ _ (fun h' => h')
    have e2 : bestTransformer b2Alpha b2Gamma compl B2.hi = B2.lo :=
      unitAlpha_neg _ _ (fun h' => h' trivial)
    rw [e1, e2] at this
    exact absurd this (by decide)

/-- `R2-best-mono` needs reflexivity: over `NR2`, the best transformer of the
constant-full transformer is constantly `hi`, which is not monotone because
`hi ≤ hi` fails. -/
theorem bestMono_tight_refl :
    IsTrans NR2 ∧ ¬ IsRefl NR2 ∧ GaloisConnection nr2Alpha nr2Gamma ∧
      Monotone (fun _ : Pred Unit => U) ∧
      ¬ Monotone (bestTransformer nr2Alpha nr2Gamma (fun _ => U)) := by
  refine ⟨NR2.isTrans, NR2.not_isRefl, nr2_gc, fun _ _ _ => Pred.le_refl _, ?_⟩
  intro h
  have := h NR2.lo NR2.lo (by decide)
  have e : bestTransformer nr2Alpha nr2Gamma (fun _ => U) NR2.lo = NR2.hi := unitAlpha_U _ _
  rw [e] at this
  exact absurd this (by decide)

/-- `R2-best-mono` needs transitivity: over the reflexive, non-transitive `NT4`, the
best transformer of the identity is not monotone (`q ≤ r` but `p ≰ z`). -/
theorem bestMono_tight_trans :
    IsRefl NT4 ∧ ¬ IsTrans NT4 ∧ GaloisConnection nt4Alpha nt4Gamma ∧
      Monotone (id : Pred Unit → Pred Unit) ∧
      ¬ Monotone (bestTransformer nt4Alpha nt4Gamma id) := by
  refine ⟨NT4.isRefl, NT4.not_isTrans, nt4_gc, fun _ _ h => h, ?_⟩
  intro h
  have := h NT4.q NT4.r (by decide)
  have e1 : bestTransformer nt4Alpha nt4Gamma id NT4.q = NT4.p := unitAlpha_U _ _
  have e2 : bestTransformer nt4Alpha nt4Gamma id NT4.r = NT4.z := unitAlpha_E _ _
  rw [e1, e2] at this
  exact absurd this (by decide)

/-- `R2-best-mono` needs the Galois connection: over `B2` with the order-reversing
`b2GammaRev`, the best transformer of the identity swaps `lo` and `hi`. -/
theorem bestMono_tight_gc :
    IsRefl B2 ∧ IsTrans B2 ∧ Monotone (id : Pred Unit → Pred Unit) ∧
      ¬ GaloisConnection b2Alpha b2GammaRev ∧
      ¬ Monotone (bestTransformer b2Alpha b2GammaRev id) := by
  refine ⟨B2.isRefl, B2.isTrans, fun _ _ h => h, ?_, ?_⟩
  · intro h
    have := (h U B2.hi).mp (B2.le_hi _)
    exact not_U_le_E this
  · intro h
    have := h B2.lo B2.hi (by decide)
    have e1 : bestTransformer b2Alpha b2GammaRev id B2.lo = B2.hi := unitAlpha_U _ _
    have e2 : bestTransformer b2Alpha b2GammaRev id B2.hi = B2.lo := unitAlpha_E _ _
    rw [e1, e2] at this
    exact absurd this (by decide)

/-! ## Tightness counterexamples for `R3-comp-le` (proved) -/

/-- A non-monotone transformer on `Pred Bool`: `x ↦ {s | ¬ x false}`. -/
def notAtFalse (x : Pred Bool) : Pred Bool := fun _ => ¬ x false

/-- The constant transformer on `Pred Bool` with value `{true}`. -/
def constTrue (_ : Pred Bool) : Pred Bool := fun s => s = true

/-- `R3-comp-le` needs monotone `f`: on `Pred Bool` with the two-point non-emptiness
abstraction `boolAlpha`/`boolGamma`,
`g = constTrue` and `f = notAtFalse` (not monotone) give `(f ∘ g)♯ lo = hi` but
`f♯ (g♯ lo) = lo`. -/
theorem compLe_tight_monoF :
    IsRefl B2 ∧ GaloisConnection boolAlpha boolGamma ∧
      ¬ Monotone notAtFalse ∧
      ¬ (bestTransformer boolAlpha boolGamma (notAtFalse ∘ constTrue) B2.lo ≤
          bestTransformer boolAlpha boolGamma notAtFalse
            (bestTransformer boolAlpha boolGamma constTrue B2.lo)) := by
  refine ⟨B2.isRefl, bool_gc, ?_, ?_⟩
  · intro h
    exact h (Pred.empty Bool) (Pred.univ Bool) (fun _ h => h.elim) true (fun h' => h') trivial
  · have e1 : bestTransformer boolAlpha boolGamma (notAtFalse ∘ constTrue) B2.lo = B2.hi :=
      boolAlpha_of_mem true (fun h => Bool.noConfusion h)
    have e2 : bestTransformer boolAlpha boolGamma constTrue B2.lo = B2.hi :=
      boolAlpha_of_mem true rfl
    have e3 : bestTransformer boolAlpha boolGamma notAtFalse B2.hi = B2.lo :=
      boolAlpha_of_empty (fun _ h => h trivial)
    rw [e1, e2, e3]
    decide

/-- `R3-comp-le` needs reflexivity: over `NR2` with `f = id` and `g` constantly `{()}`,
`(f ∘ g)♯ lo = hi` but `f♯ (g♯ lo) = lo`, and `hi ≤ lo` fails. -/
theorem compLe_tight_refl :
    ¬ IsRefl NR2 ∧ GaloisConnection nr2Alpha nr2Gamma ∧
      Monotone (id : Pred Unit → Pred Unit) ∧
      ¬ (bestTransformer nr2Alpha nr2Gamma (id ∘ (fun _ => U)) NR2.lo ≤
          bestTransformer nr2Alpha nr2Gamma id
            (bestTransformer nr2Alpha nr2Gamma (fun _ => U) NR2.lo)) := by
  refine ⟨NR2.not_isRefl, nr2_gc, fun _ _ h => h, ?_⟩
  have e1 : bestTransformer nr2Alpha nr2Gamma (id ∘ (fun _ => U)) NR2.lo = NR2.hi :=
    unitAlpha_U _ _
  rw [e1]
  intro h
  exact absurd h (by decide)

/-- `R3-comp-le` needs the Galois connection: over the reflexive `B2` with `γ`
constantly `∅`, `α = b2Alpha`, `f = id`, `g` constantly `{()}`. -/
theorem compLe_tight_gc :
    IsRefl B2 ∧ Monotone (id : Pred Unit → Pred Unit) ∧
      ¬ GaloisConnection b2Alpha (fun _ : B2 => E) ∧
      ¬ (bestTransformer b2Alpha (fun _ : B2 => E) (id ∘ (fun _ => U)) B2.lo ≤
          bestTransformer b2Alpha (fun _ : B2 => E) id
            (bestTransformer b2Alpha (fun _ : B2 => E) (fun _ => U) B2.lo)) := by
  refine ⟨B2.isRefl, fun _ _ h => h, ?_, ?_⟩
  · intro h
    exact not_U_le_E ((h U B2.hi).mp (B2.le_hi _))
  · have e1 : bestTransformer b2Alpha (fun _ : B2 => E) (id ∘ (fun _ => U)) B2.lo = B2.hi :=
      unitAlpha_U _ _
    have e2 : bestTransformer b2Alpha (fun _ : B2 => E) id
        (bestTransformer b2Alpha (fun _ : B2 => E) (fun _ => U) B2.lo) = B2.lo :=
      unitAlpha_E _ _
    rw [e1, e2]
    decide

/-! ## Boundary examples (proved) -/

/-- For a monotone concrete transformer, `γ`-soundness lifts to every subset of a
concretization: `x ⊆ γ a` implies `f x ⊆ γ (fs a)`. -/
theorem sound_le_of_le_gamma_of_monotone {σ A : Type} [LE A] {γ : A → Pred σ}
    {f : Pred σ → Pred σ} {fs : A → A} (hf : Monotone f) (hs : Sound γ f fs)
    {x : Pred σ} {a : A} (hx : x ≤ γ a) : f x ≤ γ (fs a) :=
  Pred.le_trans (hf _ _ hx) (hs a)

/-- Without monotonicity of `f`, `γ`-soundness need not lift to subsets: for the
two-point non-emptiness abstraction `boolAlpha`/`boolGamma` of `Pred Bool` and the
non-monotone `notAtFalse`,
the best transformer is `γ`-sound, `{true} ⊆ γ hi` (written `constTrue ∅`), yet
`notAtFalse {true} = univ ⊄ ∅ = γ (notAtFalse♯ hi)`. -/
theorem sound_not_subset_of_not_monotone :
    IsRefl B2 ∧ GaloisConnection boolAlpha boolGamma ∧ ¬ Monotone notAtFalse ∧
      Sound boolGamma notAtFalse (bestTransformer boolAlpha boolGamma notAtFalse) ∧
      (constTrue (Pred.empty Bool) : Pred Bool) ≤ boolGamma B2.hi ∧
      ¬ (notAtFalse (constTrue (Pred.empty Bool)) ≤
          boolGamma (bestTransformer boolAlpha boolGamma notAtFalse B2.hi)) := by
  refine ⟨B2.isRefl, bool_gc, compLe_tight_monoF.2.2.1,
    fun a => (bool_gc _ _).mp (B2.isRefl _), fun _ _ => trivial, ?_⟩
  have e : bestTransformer boolAlpha boolGamma notAtFalse B2.hi = B2.lo :=
    boolAlpha_of_empty (fun _ h => h trivial)
  rw [e]
  intro h
  exact h true (fun h' => Bool.noConfusion h')

/-- Without reflexivity, the best transformer is only a lower bound of the
`γ`-sound transformers: on the transitive, non-reflexive `NR3` with a Galois
connection, a sound transformer exists and every sound transformer lies above
`α ∘ f ∘ γ`, but `α ∘ f ∘ γ` is itself unsound and not even `≤` itself. -/
theorem bestTransformer_lowerBound_not_sound_without_refl :
    IsTrans NR3 ∧ ¬ IsRefl NR3 ∧ GaloisConnection nr3Alpha nr3Gamma ∧
      Sound nr3Gamma (fun _ => U) (fun _ => NR3.hi) ∧
      (∀ fs : NR3 → NR3, Sound nr3Gamma (fun _ => U) fs →
          ∀ a, bestTransformer nr3Alpha nr3Gamma (fun _ => U) a ≤ fs a) ∧
      ¬ Sound nr3Gamma (fun _ => U) (bestTransformer nr3Alpha nr3Gamma (fun _ => U)) ∧
      ¬ (bestTransformer nr3Alpha nr3Gamma (fun _ => U) NR3.lo ≤
          bestTransformer nr3Alpha nr3Gamma (fun _ => U) NR3.lo) := by
  have em : ∀ a, bestTransformer nr3Alpha nr3Gamma (fun _ => U) a = NR3.mid :=
    fun _ => unitAlpha_U _ _
  refine ⟨NR3.isTrans, NR3.not_isRefl, nr3_gc, fun _ => Pred.le_refl _,
    fun fs hs a => (nr3_gc _ _).mpr (hs a), ?_, ?_⟩
  · intro hs
    have hlo := hs NR3.lo
    rw [em] at hlo
    exact not_U_le_E hlo
  · rw [em]; decide

end Toy.AbsInt
