import ToyUpTo.Basic

/-!
# Counterexamples, examples and non-vacuity for the abstract theory

All proofs here are complete.  The tiny relation lattices used are relations
over `Unit` (two elements, isomorphic to `Prop`) and over `Bool` (four pairs).
-/

namespace Toy.UpTo

/-! ### Small functionals and up-to functions used as witnesses -/

/-- An antitone functional on relations over `Unit`: `negB R` relates `()` to
`()` exactly when `R` does not. -/
def negB : Rel Unit → Rel Unit := fun R _ _ => ¬ R () ()

/-- Pointwise complement, a non-monotone up-to function. -/
def negF : Rel Unit → Rel Unit := fun R p q => ¬ R p q

/-- The constant-empty functional on relations over `Unit`. -/
def botFun : Rel Unit → Rel Unit := fun _ => botRel

/-- The constant-total up-to function on relations over `Unit`. -/
def topFunU : Rel Unit → Rel Unit := fun _ => topRel

/-- The pair `(false, false)` as a relation on `Bool`. -/
def relX : Rel Bool := fun p q => p = false ∧ q = false

/-- The pair `(true, true)` as a relation on `Bool`. -/
def relY : Rel Bool := fun p q => p = true ∧ q = true

/-- A non-monotone functional on relations over `Bool`: it returns `R` itself,
except that it returns the empty relation once `R` contains both
`(false, false)` and `(true, true)`. -/
def killB : Rel Bool → Rel Bool :=
  fun R p q => R p q ∧ ¬ (R false false ∧ R true true)

/-- A monotone functional on relations over `Bool`: if `(false, true)` is
related, return `{(false, false), (true, false)}`, otherwise the empty
relation. -/
def shiftB : Rel Bool → Rel Bool := fun R _ q => R false true ∧ q = false

/-- A non-monotone up-to function on relations over `Bool`: it maps exactly
the relation `{(false, false)}` to `{(false, true)}`, and every other relation
to the empty relation. -/
def pickF : Rel Bool → Rel Bool :=
  fun R p q => (∀ p' q', R p' q' ↔ (p' = false ∧ q' = false)) ∧ p = false ∧ q = true

/-- A non-monotone up-to function on relations over `Bool`: it adds the pair
`(false, false)` to the empty relation and leaves every non-empty relation
unchanged. -/
def fillE : Rel Bool → Rel Bool :=
  fun R p q => R p q ∨ (p = false ∧ q = false ∧ ∀ p' q', ¬ R p' q')

/-! ### Definition examples -/

/-- `Incl`, positive: the empty relation is included in every relation. -/
theorem incl_example_pos : (botRel : Rel Unit) ⊑ topRel := botRel_incl _

/-- `Incl`, negative: the total relation is not included in the empty one. -/
theorem incl_example_neg : ¬ (topRel : Rel Unit) ⊑ botRel :=
  fun h => h () () trivial

/-- `MonoRel`, positive: the identity up-to function is monotone. -/
theorem monoRel_example_pos : MonoRel (fun R : Rel Unit => R) := monoRel_id

/-- `MonoRel`, negative: pointwise complement is not monotone. -/
theorem monoRel_example_neg : ¬ MonoRel negF := by
  intro h
  exact h botRel topRel (botRel_incl _) () () (fun hb => hb) trivial

/-- `gfp`, positive: for the identity functional every relation is a
post-fixpoint, so `gfp` is total. -/
theorem gfp_example_pos : gfp (fun R : Rel Unit => R) () () :=
  ⟨topRel, Incl.refl _, trivial⟩

/-- `gfp`, negative: for the constant-empty functional `gfp` is empty. -/
theorem gfp_example_neg : ¬ gfp botFun () () := by
  rintro ⟨R, hR, h⟩
  exact hR () () h

/-- `Progresses`, positive: the empty relation progresses to anything. -/
theorem progresses_example_pos : Progresses botFun botRel topRel :=
  botRel_incl _

/-- `Progresses`, negative: the total relation does not progress under the
constant-empty functional. -/
theorem progresses_example_neg : ¬ Progresses botFun topRel topRel :=
  fun h => h () () trivial

/-- `Sound`, positive: the identity up-to function is sound for any
functional. -/
theorem sound_example_pos : Sound negB (fun R => R) := sound_id negB

/-- `Sound`, negative: the constant-empty up-to function is unsound for the
antitone functional `negB` (this is also a tightness counterexample below). -/
theorem sound_example_neg : ¬ Sound negB (fun _ => botRel) := by
  intro h
  obtain ⟨W, hW, hw⟩ := h topRel (fun _ _ _ hb => hb) () () trivial
  exact hW () () hw hw

/-- `Commutes`, positive: every function commutes with the identity
functional. -/
theorem commutes_example_pos : Commutes (fun R : Rel Unit => R) negF :=
  fun _ => Incl.refl _

/-- `Commutes`, negative: the constant-total function does not commute with
the constant-empty functional. -/
theorem commutes_example_neg : ¬ Commutes botFun topFunU :=
  fun h => h botRel () () trivial

/-- `Compatible`, positive: the identity is compatible with any functional. -/
theorem compatible_example_pos : Compatible negB (fun R => R) := compatible_id negB

/-- `Compatible`, negative: complement is not compatible even with the
identity functional (it is not monotone). -/
theorem compatible_example_neg : ¬ Compatible (fun R : Rel Unit => R) negF :=
  fun h => monoRel_example_neg h.mono

/-- `comp`, positive/negative: composing complement with itself gives back the
original relation pointwise (up to double negation); `comp negF negF` relates
`()` to `()` on the total relation but `comp negF (fun R => R)` does not. -/
theorem comp_example : comp negF negF topRel () () ∧ ¬ comp negF (fun R => R) topRel () () :=
  ⟨fun h => h trivial, fun h => h trivial⟩

/-- `iSup`, positive: a family containing the constant-total function relates
every pair. -/
theorem iSup_example_pos : iSup (fun b : Bool => if b then topFunU else botFun) botRel () () :=
  ⟨true, trivial⟩

/-- `iSup`, negative: the empty family relates nothing. -/
theorem iSup_example_neg : ¬ iSup (fun e : Empty => (e.elim : Rel Unit → Rel Unit)) topRel () () :=
  fun ⟨e, _⟩ => e.elim

/-- `omega`, positive: `f^ω R` contains `R` (the `n = 0` term). -/
theorem omega_example_pos : omega botFun topRel () () := ⟨0, trivial⟩

/-- `omega`, negative: for the constant-empty function, `f^ω ⊥ = ⊥`. -/
theorem omega_example_neg : ¬ omega botFun botRel () () := by
  rintro ⟨n, h⟩
  cases n with
  | zero => exact h
  | succ n => exact h

/-! ### Tightness counterexamples for `sound_of_compatible_of_monotone_functional`

Canonical form: all other hypotheses hold and the conclusion fails. -/

/-- Dropping `MonoRel b`: with the antitone functional `negB` and the
constant-empty up-to function, `f` is monotone and commutes with `b`, yet `f`
is unsound. -/
theorem sound_counterexample_nonmonotone_functional :
    MonoRel (fun _ : Rel Unit => (botRel : Rel Unit)) ∧
    Commutes negB (fun _ => botRel) ∧
    ¬ Sound negB (fun _ => botRel) :=
  ⟨fun _ _ _ => Incl.refl _, fun _ _ _ h => h.elim, sound_example_neg⟩

/-- `shiftB` is monotone. -/
theorem shiftB_mono : MonoRel shiftB := fun _ _ h _ _ ⟨h1, h2⟩ => ⟨h _ _ h1, h2⟩

/-- `pickF` commutes with `shiftB`: the image of `shiftB` is never exactly
`{(false, false)}`, so the left-hand side is always empty. -/
theorem pickF_commutes : Commutes shiftB pickF := by
  intro R p q ⟨hiff, _, _⟩
  have h1 : shiftB R false false := (hiff false false).2 ⟨rfl, rfl⟩
  have h2 : shiftB R true false := ⟨h1.1, rfl⟩
  exact absurd ((hiff true false).1 h2).1 (by decide)

/-- Dropping `MonoRel f`: the functional `shiftB` is monotone and the
non-monotone `pickF` commutes with it, yet `pickF` is unsound for `shiftB`. -/
theorem sound_counterexample_nonmonotone_upto :
    MonoRel shiftB ∧ Commutes shiftB pickF ∧ ¬ Sound shiftB pickF := by
  refine ⟨shiftB_mono, pickF_commutes, ?_⟩
  intro hs
  have hprog : Progresses shiftB relX (pickF relX) := by
    intro p q ⟨_, hq⟩
    exact ⟨⟨fun _ _ => Iff.rfl, rfl, rfl⟩, hq⟩
  obtain ⟨W, hW, hw⟩ := hs relX hprog false false ⟨rfl, rfl⟩
  have hy : W false true := (hW false false hw).1
  exact absurd (hW false true hy).2 (by decide)

/-! ### Tightness counterexamples for `compatible_comp` -/

/-- Dropping `MonoRel f` in `compatible_comp`: with the identity functional,
`f = negF`, `g = id`.  Since every function commutes with the identity
functional, this refutes only the monotonicity half of `Compatible`; the
commutation half is refuted separately by
`comp_counterexample_nonmonotone_left_commutation`. -/
theorem comp_counterexample_nonmonotone_left :
    MonoRel (fun R : Rel Unit => R) ∧ Commutes (fun R : Rel Unit => R) negF ∧
    Commutes (fun R : Rel Unit => R) (fun R => R) ∧
    ¬ Compatible (fun R : Rel Unit => R) (comp negF (fun R => R)) :=
  ⟨monoRel_id, fun _ => Incl.refl _, fun _ => Incl.refl _,
    fun h => monoRel_example_neg h.mono⟩

/-- Dropping `MonoRel g` in `compatible_comp`: with the identity functional,
`f = id`, `g = negF` (refutes the monotonicity half of `Compatible`). -/
theorem comp_counterexample_nonmonotone_right :
    MonoRel (fun R : Rel Unit => R) ∧ Commutes (fun R : Rel Unit => R) (fun R => R) ∧
    Commutes (fun R : Rel Unit => R) negF ∧
    ¬ Compatible (fun R : Rel Unit => R) (comp (fun R => R) negF) :=
  ⟨monoRel_id, fun _ => Incl.refl _, fun _ => Incl.refl _,
    fun h => monoRel_example_neg h.mono⟩

/-- Dropping `MonoRel f` in `compatible_comp`, commutation half: with the
monotone constant functional `b = const {(true,true)}`, the non-monotone
`f = fillE` and the monotone `g = const ∅` both commute with `b`, yet
`f ∘ g` does not commute with `b`.  So `MonoRel f` is needed for the
commutation of the composite, not only for its monotonicity. -/
theorem comp_counterexample_nonmonotone_left_commutation :
    MonoRel (fun _ : Rel Bool => relY) ∧ MonoRel (fun _ : Rel Bool => (botRel : Rel Bool)) ∧
    Commutes (fun _ : Rel Bool => relY) fillE ∧
    Commutes (fun _ : Rel Bool => relY) (fun _ => botRel) ∧
    ¬ Commutes (fun _ : Rel Bool => relY) (comp fillE (fun _ => botRel)) := by
  refine ⟨fun _ _ _ => Incl.refl _, fun _ _ _ => Incl.refl _, ?_, ?_, ?_⟩
  · intro R p q h
    rcases h with h | ⟨_, _, hall⟩
    · exact h
    · exact absurd ⟨rfl, rfl⟩ (hall true true)
  · intro R p q h
    exact h.elim
  · intro hc
    have hmem : comp fillE (fun _ => botRel) relY false false :=
      Or.inr ⟨rfl, rfl, fun _ _ h => h⟩
    exact absurd (hc botRel false false hmem).1 (by decide)

/-- Dropping `Commutes b f` in `compatible_comp`: `b` constant-empty,
`f` constant-total, `g = id`. -/
theorem comp_counterexample_noncommuting_left :
    MonoRel topFunU ∧ MonoRel (fun R : Rel Unit => R) ∧ Commutes botFun (fun R => R) ∧
    ¬ Compatible botFun (comp topFunU (fun R => R)) :=
  ⟨fun _ _ _ => Incl.refl _, monoRel_id, fun _ => Incl.refl _,
    fun h => h.comm botRel () () trivial⟩

/-- Dropping `Commutes b g` in `compatible_comp`: `b` constant-empty,
`f = id`, `g` constant-total. -/
theorem comp_counterexample_noncommuting_right :
    MonoRel (fun R : Rel Unit => R) ∧ MonoRel topFunU ∧ Commutes botFun (fun R => R) ∧
    ¬ Compatible botFun (comp (fun R => R) topFunU) :=
  ⟨monoRel_id, fun _ _ _ => Incl.refl _, fun _ => Incl.refl _,
    fun h => h.comm botRel () () trivial⟩

/-! ### Tightness counterexamples for `compatible_iSup_of_monotone_functional` -/

/-- The two-member family `{const {(false,false)}, const {(true,true)}}`. -/
def xyFamily : Bool → Rel Bool → Rel Bool := fun i _ => if i then relX else relY

theorem killB_relX : killB relX = relX := by
  funext p q
  apply propext
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun ⟨_, h2⟩ => absurd h2.1 (by decide)⟩

theorem killB_relY : killB relY = relY := by
  funext p q
  apply propext
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, fun ⟨h1, _⟩ => absurd h1.1 (by decide)⟩

/-- Each member of `xyFamily` commutes with `killB`. -/
theorem xyFamily_commutes : ∀ i, Commutes killB (xyFamily i) := by
  intro i R
  cases i
  · show relY ⊑ killB relY
    rw [killB_relY]; exact Incl.refl _
  · show relX ⊑ killB relX
    rw [killB_relX]; exact Incl.refl _

/-- Dropping `MonoRel b` in `compatible_iSup_of_monotone_functional`: the
non-monotone `killB` commutes with `const {(false,false)}` and with
`const {(true,true)}`, but not with their union. -/
theorem iSup_counterexample_nonmonotone_functional :
    (∀ i, MonoRel (xyFamily i)) ∧ (∀ i, Commutes killB (xyFamily i)) ∧
    ¬ Compatible killB (iSup xyFamily) := by
  refine ⟨fun _ _ _ _ => Incl.refl _, xyFamily_commutes, ?_⟩
  intro h
  have := h.comm botRel false false ⟨true, ⟨rfl, rfl⟩⟩
  exact this.2 ⟨⟨true, ⟨rfl, rfl⟩⟩, ⟨false, ⟨rfl, rfl⟩⟩⟩

/-- Dropping `∀ i, MonoRel (F i)`: the singleton family `{negF}` commutes with
the identity functional, but its union is not monotone (this refutes the
monotonicity half of `Compatible`). -/
theorem iSup_counterexample_nonmonotone_member :
    MonoRel (fun R : Rel Unit => R) ∧ (∀ _ : Unit, Commutes (fun R : Rel Unit => R) negF) ∧
    ¬ Compatible (fun R : Rel Unit => R) (iSup (fun _ : Unit => negF)) := by
  refine ⟨monoRel_id, fun _ _ => Incl.refl _, ?_⟩
  intro h
  obtain ⟨_, hn⟩ := h.mono botRel topRel (botRel_incl _) () () ⟨(), fun hb => hb⟩
  exact hn trivial

/-- Dropping `∀ i, Commutes b (F i)`: the singleton family `{const ⊤}` with the
constant-empty functional. -/
theorem iSup_counterexample_noncommuting_member :
    MonoRel botFun ∧ (∀ _ : Unit, MonoRel topFunU) ∧
    ¬ Compatible botFun (iSup (fun _ : Unit => topFunU)) :=
  ⟨fun _ _ _ => Incl.refl _, fun _ _ _ _ => Incl.refl _,
    fun h => h.comm botRel () () ⟨(), trivial⟩⟩

/-! ### Tightness counterexamples for `compatible_omega_of_monotone_functional` -/

/-- Dropping `MonoRel b`: `const {(false,false)}` commutes with the
non-monotone `killB`, but its ω-iteration `R ↦ R ∪ {(false,false)}` does not
(take `R = {(true,true)}`). -/
theorem omega_counterexample_nonmonotone_functional :
    MonoRel (fun _ : Rel Bool => relX) ∧ Commutes killB (fun _ => relX) ∧
    ¬ Compatible killB (omega (fun _ => relX)) := by
  refine ⟨fun _ _ _ => Incl.refl _, xyFamily_commutes true, ?_⟩
  intro h
  have := h.comm relY false false ⟨1, ⟨rfl, rfl⟩⟩
  exact this.2 ⟨⟨1, ⟨rfl, rfl⟩⟩, ⟨0, ⟨rfl, rfl⟩⟩⟩

theorem iter_fillE_relY_tt : ∀ n, iter fillE n relY true true
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => Or.inl (iter_fillE_relY_tt n)

theorem iter_fillE_relY : ∀ n p q, iter fillE n relY p q → relY p q
  | 0, _, _, h => h
  | n + 1, p, q, h => by
    rcases h with h | ⟨_, _, hall⟩
    · exact iter_fillE_relY n p q h
    · exact absurd (iter_fillE_relY_tt n) (hall true true)

/-- Dropping `MonoRel f`: the non-monotone `fillE` commutes with the identity
functional, but its ω-iteration is not monotone (`∅ ⊑ {(true,true)}`, yet
`(false,false)` is in `fillE^ω ∅` and not in `fillE^ω {(true,true)}`).  This
refutes the monotonicity half of `Compatible`. -/
theorem omega_counterexample_nonmonotone_upto :
    MonoRel (fun R : Rel Bool => R) ∧ Commutes (fun R : Rel Bool => R) fillE ∧
    ¬ Compatible (fun R : Rel Bool => R) (omega fillE) := by
  refine ⟨monoRel_id, fun _ => Incl.refl _, ?_⟩
  intro h
  have h0 : omega fillE botRel false false := ⟨1, Or.inr ⟨rfl, rfl, fun _ _ hb => hb⟩⟩
  obtain ⟨n, hn⟩ := h.mono botRel relY (botRel_incl _) false false h0
  exact absurd (iter_fillE_relY n false false hn).1 (by decide)

/-- Dropping `Commutes b f`: constant-total `f` with the constant-empty
functional. -/
theorem omega_counterexample_noncommuting :
    MonoRel botFun ∧ MonoRel topFunU ∧ ¬ Compatible botFun (omega topFunU) :=
  ⟨fun _ _ _ => Incl.refl _, fun _ _ _ => Incl.refl _,
    fun h => h.comm botRel () () ⟨1, trivial⟩⟩

/-! ### A second non-monotone functional on relations over `Bool` -/

/-- A non-monotone functional on relations over `Bool`: it relates
`(false,false)` when `R` contains both `(false,false)` and `(true,true)`, and
relates `(true,true)` when `R` contains `(true,true)` but not `(false,false)`. -/
def swapB : Rel Bool → Rel Bool :=
  fun W p q => W true true ∧
    ((W false false ∧ p = false ∧ q = false) ∨ (¬ W false false ∧ p = true ∧ q = true))

/-- `const {(true,true)}` commutes with `swapB`. -/
theorem const_relY_commutes_swapB : Commutes swapB (fun _ => relY) := by
  intro _ p q ⟨hp, hq⟩
  subst hp; subst hq
  exact ⟨⟨rfl, rfl⟩, Or.inr ⟨fun hff => Bool.noConfusion hff.1, rfl, rfl⟩⟩

/-- No post-fixpoint of `swapB` relates `(false,false)`. -/
theorem not_gfp_swapB_ff : ¬ gfp swapB false false := by
  rintro ⟨W, hW, hff⟩
  have htt : W true true := (hW false false hff).1
  rcases (hW true true htt).2 with ⟨_, htf, _⟩ | ⟨hnff, _, _⟩
  · exact Bool.noConfusion htf
  · exact hnff hff

/-- `relY = {(true,true)}` is a post-fixpoint of `swapB`. -/
theorem gfp_swapB_tt : gfp swapB true true :=
  ⟨relY, fun p q h => by
    obtain ⟨hp, hq⟩ := h
    subst hp; subst hq
    exact ⟨⟨rfl, rfl⟩, Or.inr ⟨fun hff => Bool.noConfusion hff.1, rfl, rfl⟩⟩, rfl, rfl⟩

/-! ### Tightness counterexample for `compatible_union_gfp_of_monotone_functional` -/

/-- Dropping `MonoRel b` (there are no other hypotheses): for the
non-monotone `swapB`, union with `gfp swapB` is neither compatible nor sound.
`gfp swapB = {(true,true)}`, and `{(false,false)}` progresses to
`swapB ({(false,false)} ∪ gfp swapB)` although `(false,false) ∉ gfp swapB`. -/
theorem union_gfp_counterexample_nonmonotone_functional :
    ¬ Compatible swapB (unionGfp swapB) ∧ ¬ Sound swapB (unionGfp swapB) := by
  refine ⟨fun h => ?_, fun hs => ?_⟩
  · obtain ⟨_, h2⟩ := h.comm topRel true true (Or.inr gfp_swapB_tt)
    rcases h2 with ⟨_, htf, _⟩ | ⟨hn, _, _⟩
    · exact Bool.noConfusion htf
    · exact hn (Or.inl trivial)
  · have hprog : Progresses swapB relX (unionGfp swapB relX) := by
      rintro p q ⟨rfl, rfl⟩
      exact ⟨Or.inr gfp_swapB_tt, Or.inl ⟨Or.inl ⟨rfl, rfl⟩, rfl, rfl⟩⟩
    exact not_gfp_swapB_ff (hs relX hprog false false ⟨rfl, rfl⟩)

/-- `gfp killB` relates `(false,false)` (via the post-fixpoint `relX`). -/
theorem gfp_killB_ff : gfp killB false false :=
  ⟨relX, by rw [killB_relX]; exact Incl.refl _, rfl, rfl⟩

/-- `gfp killB` relates `(true,true)` (via the post-fixpoint `relY`). -/
theorem gfp_killB_tt : gfp killB true true :=
  ⟨relY, by rw [killB_relY]; exact Incl.refl _, rfl, rfl⟩

/-- For the non-monotone `killB`, union with `gfp killB` is not compatible
either (`gfp killB` contains both `(false,false)` and `(true,true)`). -/
theorem union_gfp_not_compatible_killB : ¬ Compatible killB (unionGfp killB) := by
  intro h
  have := h.comm botRel false false (Or.inr gfp_killB_ff)
  exact this.2 ⟨Or.inr gfp_killB_ff, Or.inr gfp_killB_tt⟩

end Toy.UpTo
