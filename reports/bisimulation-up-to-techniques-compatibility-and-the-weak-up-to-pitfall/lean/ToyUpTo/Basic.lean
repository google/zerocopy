/-!
# Up-to techniques over an abstract monotone functional on relations

Toy, Mathlib-free setting.  Relations on a state type `S` are `Prop`-valued
binary predicates, ordered by inclusion `⊑`.  A *functional* `b` (for example
the strong or weak bisimulation functional of a labelled transition system)
maps a relation `R` to the relation "the pairs whose one-step behaviour lands
in `R`".  Its greatest fixpoint is defined, without any lattice library, as the
union of all post-fixpoints.

An *up-to function* `f` lets one prove `R ⊑ gfp b` from the weaker progression
`R ⊑ b (f R)`.  `Sound b f` says this inference is valid for every `R`.
`Commutes b f` (`f ∘ b ⊑ b ∘ f`) together with `MonoRel f` is Pous's notion of
`b`-compatibility.
-/

namespace Toy.UpTo

universe u v

/-- A `Prop`-valued binary relation on `S`.  Relations are *homogeneous*: both
sides range over the same state type.  Simulations between two different
transition systems (`S₁ → S₂ → Prop`) are not modelled; some closures used
below (equivalence closure, symmetric closure) are not even well typed in the
heterogeneous setting. -/
abbrev Rel (S : Type u) : Type u := S → S → Prop

section Lattice

variable {S : Type u}

/-- Relational inclusion `R ⊑ R'`: every pair related by `R` is related by `R'`. -/
def Incl (R R' : Rel S) : Prop := ∀ p q, R p q → R' p q

@[inherit_doc] scoped infix:50 " ⊑ " => Incl

/-- The empty relation. -/
def botRel : Rel S := fun _ _ => False

/-- The total relation. -/
def topRel : Rel S := fun _ _ => True

/-- The identity (diagonal) relation. -/
def idRel : Rel S := fun p q => p = q

/-- `F` is monotone with respect to relational inclusion. -/
def MonoRel (F : Rel S → Rel S) : Prop := ∀ R R', R ⊑ R' → F R ⊑ F R'

/-- The union of all post-fixpoints of `b` (relations `R` with `R ⊑ b R`).
When `b` is monotone this is the greatest fixpoint of `b` (Knaster–Tarski);
for non-monotone `b` it is still well defined but need not be a fixpoint. -/
def gfp (b : Rel S → Rel S) : Rel S := fun p q => ∃ R, R ⊑ b R ∧ R p q

/-- `R` *progresses to* `R'` with respect to `b`: `R ⊑ b R'`. -/
def Progresses (b : Rel S → Rel S) (R R' : Rel S) : Prop := R ⊑ b R'

/-- The up-to function `f` is *sound* for `b`: every relation that progresses
to `f R` is contained in the greatest fixpoint of `b`. -/
def Sound (b f : Rel S → Rel S) : Prop := ∀ R, Progresses b R (f R) → R ⊑ gfp b

/-- The commutation half of compatibility: `f (b R) ⊑ b (f R)` for every `R`. -/
def Commutes (b f : Rel S → Rel S) : Prop := ∀ R, f (b R) ⊑ b (f R)

/-- `f` is `b`-compatible (Pous): monotone and `f ∘ b ⊑ b ∘ f`.  The two
components are also available as the separate properties `MonoRel` and
`Commutes`, which the theorems below use individually.

This is the first-order notion.  Sangiorgi's *respectful* functions
(compatibility with `R ↦ b R ∩ R` instead of `b`) form a strictly larger class
(Sangiorgi 1998; for strong bisimilarity it contains prefix contexts), and
second-order notions such as "below the companion" are larger still; neither
is formalized here. -/
structure Compatible (b f : Rel S → Rel S) : Prop where
  mono : MonoRel f
  comm : Commutes b f

/-- Composition of up-to functions, `(comp f g) R = f (g R)`. -/
def comp (f g : Rel S → Rel S) : Rel S → Rel S := fun R => f (g R)

/-- Pointwise union of a family of up-to functions. -/
def iSup {ι : Type v} (F : ι → Rel S → Rel S) : Rel S → Rel S :=
  fun R p q => ∃ i, F i R p q

/-- `n`-fold iteration of `f`; `iter f 0 R = R`. -/
def iter (f : Rel S → Rel S) : Nat → Rel S → Rel S
  | 0, R => R
  | n + 1, R => f (iter f n R)

/-- The ω-iteration `f^ω R = ⋃ₙ fⁿ R` (including `f⁰ R = R`). -/
def omega (f : Rel S → Rel S) : Rel S → Rel S := fun R p q => ∃ n, iter f n R p q

/-- The constant up-to function returning the greatest fixpoint of `b`. -/
def constGfp (b : Rel S → Rel S) : Rel S → Rel S := fun _ => gfp b

/-! ### Basic facts (fully proved infrastructure) -/

theorem Incl.refl (R : Rel S) : R ⊑ R := fun _ _ h => h

theorem Incl.trans {R₁ R₂ R₃ : Rel S} (h₁ : R₁ ⊑ R₂) (h₂ : R₂ ⊑ R₃) : R₁ ⊑ R₃ :=
  fun p q h => h₂ p q (h₁ p q h)

theorem botRel_incl (R : Rel S) : (botRel : Rel S) ⊑ R := fun _ _ h => h.elim

/-- Every post-fixpoint is below `gfp b` (no monotonicity needed). -/
theorem incl_gfp_of_postfixed {b : Rel S → Rel S} {R : Rel S} (h : R ⊑ b R) :
    R ⊑ gfp b :=
  fun _ _ hpq => ⟨R, h, hpq⟩

/-- For monotone `b`, `gfp b` is itself a post-fixpoint. -/
theorem gfp_postfixed {b : Rel S → Rel S} (hb : MonoRel b) : gfp b ⊑ b (gfp b) := by
  intro p q ⟨R, hR, hpq⟩
  exact hb R (gfp b) (incl_gfp_of_postfixed hR) p q (hR p q hpq)

theorem monoRel_id : MonoRel (fun R : Rel S => R) := fun _ _ h => h

theorem commutes_id (b : Rel S → Rel S) : Commutes b (fun R => R) := fun _ => Incl.refl _

/-- The identity up-to function is compatible with every functional. -/
theorem compatible_id (b : Rel S → Rel S) : Compatible b (fun R => R) :=
  ⟨monoRel_id, commutes_id b⟩

/-- The constant-`gfp` up-to function ("up to the greatest fixpoint") is
compatible with every monotone functional. -/
theorem compatible_constGfp {b : Rel S → Rel S} (hb : MonoRel b) :
    Compatible b (constGfp b) :=
  ⟨fun _ _ _ => Incl.refl _, fun _ => gfp_postfixed hb⟩

/-- The identity up-to function is sound for every functional (definitional). -/
theorem sound_id (b : Rel S → Rel S) : Sound b (fun R => R) :=
  fun _ h => incl_gfp_of_postfixed h

theorem iter_zero (f : Rel S → Rel S) (R : Rel S) : iter f 0 R = R := rfl

theorem iter_succ (f : Rel S → Rel S) (n : Nat) (R : Rel S) :
    iter f (n + 1) R = f (iter f n R) := rfl

/-- Each iterate `fⁿ` of a monotone `f` is monotone. -/
theorem iter_mono {f : Rel S → Rel S} (hf : MonoRel f) : ∀ n, MonoRel (iter f n)
  | 0 => fun _ _ h => h
  | n + 1 => fun R R' h => hf _ _ (iter_mono hf n R R' h)

/-- Each iterate `fⁿ` of a monotone `f` commuting with `b` commutes with `b`
(no monotonicity of `b` needed). -/
theorem iter_commutes {b f : Rel S → Rel S} (hf : MonoRel f) (hc : Commutes b f) :
    ∀ n, Commutes b (iter f n)
  | 0 => fun _ => Incl.refl _
  | n + 1 => fun R => Incl.trans (hf _ _ (iter_commutes hf hc n R)) (hc _)

/-- Reflexive closure `R ∪ id`. -/
def reflClo (R : Rel S) : Rel S := fun p q => R p q ∨ p = q

/-- Symmetric closure `R ∪ R⁻¹`. -/
def symClo (R : Rel S) : Rel S := fun p q => R p q ∨ R q p

/-- One step of relational squaring, `R ∪ (R ; R)`. -/
def stepSq (R : Rel S) : Rel S := fun p q => R p q ∨ ∃ r, R p r ∧ R r q

/-- Union with the greatest fixpoint, `R ↦ R ∪ gfp b`. -/
def unionGfp (b : Rel S → Rel S) : Rel S → Rel S := fun R p q => R p q ∨ gfp b p q

/-! ### Main results -/

/-- **Compatibility implies soundness.**  For a monotone functional `b`, an
up-to function `f` that is monotone and satisfies `f ∘ b ⊑ b ∘ f` is sound:
`R ⊑ b (f R)` implies `R ⊑ gfp b`. -/
theorem sound_of_compatible_of_monotone_functional {b f : Rel S → Rel S}
    (hb : MonoRel b) (hf : MonoRel f) (hc : Commutes b f) : Sound b f := by
  intro R hR
  have key : ∀ n, iter f n R ⊑ b (iter f (n + 1) R) := by
    intro n
    induction n with
    | zero => exact hR
    | succ n ih => exact Incl.trans (hf _ _ ih) (hc _)
  have post : omega f R ⊑ b (omega f R) :=
    fun p q ⟨n, h⟩ => hb _ _ (fun _ _ h => ⟨n + 1, h⟩) p q (key n p q h)
  exact Incl.trans (fun _ _ h => ⟨0, h⟩) (incl_gfp_of_postfixed post)

/-- **Compatible functions are closed under composition.**  No monotonicity
of `b` is needed. -/
theorem compatible_comp {b f g : Rel S → Rel S}
    (hf : MonoRel f) (hg : MonoRel g) (hcf : Commutes b f) (hcg : Commutes b g) :
    Compatible b (comp f g) :=
  ⟨fun _ _ h => hf _ _ (hg _ _ h), fun R => Incl.trans (hf _ _ (hcg R)) (hcf _)⟩

/-- **Compatible functions are closed under arbitrary pointwise unions**, for a
monotone functional `b` (the empty family gives the constant-empty function). -/
theorem compatible_iSup_of_monotone_functional {ι : Type v} {b : Rel S → Rel S}
    {F : ι → Rel S → Rel S}
    (hb : MonoRel b) (hF : ∀ i, MonoRel (F i)) (hcF : ∀ i, Commutes b (F i)) :
    Compatible b (iSup F) :=
  ⟨fun R R' h p q ⟨i, hi⟩ => ⟨i, hF i R R' h p q hi⟩,
   fun R p q ⟨i, hi⟩ => hb _ _ (fun _ _ h => ⟨i, h⟩) p q (hcF i R p q hi)⟩

/-- **Compatible functions are closed under ω-iteration** `f^ω = ⋃ₙ fⁿ`, for a
monotone functional `b`. -/
theorem compatible_omega_of_monotone_functional {b f : Rel S → Rel S}
    (hb : MonoRel b) (hf : MonoRel f) (hc : Commutes b f) :
    Compatible b (omega f) :=
  ⟨fun R R' h p q ⟨n, hn⟩ => ⟨n, iter_mono hf n R R' h p q hn⟩,
   fun R p q ⟨n, hn⟩ => hb _ _ (fun _ _ h => ⟨n, h⟩) p q (iter_commutes hf hc n R p q hn)⟩

/-- **Up to union with the greatest fixpoint** (`R ↦ R ∪ gfp b`) is compatible
with every monotone functional `b`.  Instances: `R ∪ ~` for the strong
functional, `R ∪ ≈` for the weak functional. -/
theorem compatible_union_gfp_of_monotone_functional {b : Rel S → Rel S} (hb : MonoRel b) :
    Compatible b (unionGfp b) := by
  refine ⟨fun R R' h p q hpq => hpq.elim (fun hr => Or.inl (h _ _ hr)) Or.inr, ?_⟩
  intro R p q hpq
  rcases hpq with hr | hg
  · exact hb R _ (fun _ _ h => Or.inl h) _ _ hr
  · exact hb _ _ (fun _ _ h => Or.inr h) _ _ (gfp_postfixed hb _ _ hg)

/-- **Up to union with the greatest fixpoint is sound** for every monotone
functional `b` (corollary of the two previous results). -/
theorem sound_union_gfp_of_monotone_functional {b : Rel S → Rel S} (hb : MonoRel b) :
    Sound b (unionGfp b) :=
  let h := compatible_union_gfp_of_monotone_functional hb
  sound_of_compatible_of_monotone_functional hb h.mono h.comm

end Lattice

end Toy.UpTo
