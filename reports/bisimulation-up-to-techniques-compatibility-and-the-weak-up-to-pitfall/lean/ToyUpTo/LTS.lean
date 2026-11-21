import ToyUpTo.Basic

/-!
# Labelled transition systems, strong and weak bisimilarity, expansion

Toy, Mathlib-free.  A labelled transition system over states `S` has labels
`Option L`, where `none` is the silent action τ.  Strong bisimilarity,
weak bisimilarity and the expansion preorder are greatest fixpoints (in the
sense of `gfp`: unions of post-fixpoints) of the functionals `sb`, `wb` and
`ex`.

The weak functional `wb` uses the standard "strong challenge, weak response"
form: a challenger move `p -l→ p'` is answered by a weak move `q =l̂⇒ q'`,
where `=τ̂⇒` is `τ*` and `=â⇒` is `τ* a τ*`.
-/

namespace Toy.UpTo

universe u v

/-- A labelled transition system over states `S` with visible labels `L`;
the label `none` is the silent action τ. -/
abbrev LTS (S : Type u) (L : Type v) : Type (max u v) := S → Option L → S → Prop

section LTSDefs

variable {S : Type u} {L : Type v}

/-- The strong bisimulation functional: `sb T R p q` holds when every move of
`p` is matched by an equally labelled move of `q` into `R`, and vice versa. -/
def sb (T : LTS S L) (R : Rel S) : Rel S := fun p q =>
  (∀ l p', T p l p' → ∃ q', T q l q' ∧ R p' q') ∧
  (∀ l q', T q l q' → ∃ p', T p l p' ∧ R p' q')

/-- Strong bisimilarity `~`: the union of all strong bisimulations. -/
def bisim (T : LTS S L) : Rel S := gfp (sb T)

/-- Reflexive–transitive closure of τ-steps, `p =τ*⇒ p'`. -/
inductive TauStar (T : LTS S L) : S → S → Prop
  | refl (p : S) : TauStar T p p
  | step {p p' p'' : S} : T p none p' → TauStar T p' p'' → TauStar T p p''

/-- The weak transition `p =l̂⇒ p'`: `τ*` for `l = none` (possibly no move),
and `τ* a τ*` for `l = some a`. -/
def WStep (T : LTS S L) : S → Option L → S → Prop
  | p, none, p' => TauStar T p p'
  | p, some a, p' => ∃ p₁ p₂, TauStar T p p₁ ∧ T p₁ (some a) p₂ ∧ TauStar T p₂ p'

/-- Left half of the weak bisimulation functional: every move of `p` is
answered by a weak move of `q` into `R`. -/
def wsimL (T : LTS S L) (R : Rel S) : Rel S := fun p q =>
  ∀ l p', T p l p' → ∃ q', WStep T q l q' ∧ R p' q'

/-- Right half of the weak bisimulation functional: every move of `q` is
answered by a weak move of `p` into `R`. -/
def wsimR (T : LTS S L) (R : Rel S) : Rel S := fun p q =>
  ∀ l q', T q l q' → ∃ p', WStep T p l p' ∧ R p' q'

/-- The weak bisimulation functional (Milner's strong-challenge /
weak-response form).  The challenger makes one strong step; the defender
answers with a weak step.  A variant in which the challenger also makes weak
steps (`wbWeak`, in `WeakFacts`) has the same greatest fixpoint.

Weak bisimilarity defined this way is *divergence-insensitive*: a state with
an infinite silent loop and no other transitions is weakly bisimilar to a
state with no transitions at all (`divergence_insensitive`, in `WeakFacts`). -/
def wb (T : LTS S L) (R : Rel S) : Rel S := fun p q => wsimL T R p q ∧ wsimR T R p q

/-- Weak bisimilarity `≈`: the union of all weak bisimulations. -/
def wbisim (T : LTS S L) : Rel S := gfp (wb T)

/-- `p -l̂→ p'`: one `l`-step, or, only when `l = τ`, no step at all. -/
def StepHat (T : LTS S L) (p : S) (l : Option L) (p' : S) : Prop :=
  T p l p' ∨ (l = none ∧ p' = p)

/-- `p =l⇒ p'` with at least one `l`: `τ⁺` for `l = none`, `τ* a τ*` for
`l = some a`. -/
def WStepPlus (T : LTS S L) : S → Option L → S → Prop
  | p, none, p' => ∃ p₁, T p none p₁ ∧ TauStar T p₁ p'
  | p, some a, p' => WStep T p (some a) p'

/-- The expansion functional, in the form used by Sangiorgi and Milner for
"weak bisimulation up to expansion" (a bisimulation variant of the efficiency
preorder of Arun-Kumar and Hennessy).  The clauses match Definition 2.5 of
Sakayori–Sangiorgi (LMCS 21(3), 2025), which writes the relation with the
symbols reversed (`q ≲ p` for our `expands T p q`).

`ex T R p q` holds when every move of `p` is matched by `q` with at most one
step (`q -l̂→ q'`), and every move of `q` is matched by `p` with a weak move
containing at least one step of the same label (`p =l⇒ p'`).  The intended
reading of `expands T p q` is "`p` expands `q`", written `p ≳ q`: the left
state `p` is the slower one (for example `τ.a.0 ≳ a.0`).

**Symbol convention.**  Arun-Kumar and Hennessy write `p ≲ q` for "`q` is at
least as fast as `p`", the opposite orientation of the symbols.  Reading the
up-to function `≳ R ≲` with the symbols reversed gives an unsound technique
(`weak_upto_reversed_expansion_unsound`, in `Weak`).

**Divergence.**  "`p` does at least as many τ-steps as `q`" includes
infinitely many: a silent loop expands a dead state
(`divergence_insensitive`, in `WeakFacts`). -/
def ex (T : LTS S L) (R : Rel S) : Rel S := fun p q =>
  (∀ l p', T p l p' → ∃ q', StepHat T q l q' ∧ R p' q') ∧
  (∀ l q', T q l q' → ∃ p', WStepPlus T p l p' ∧ R p' q')

/-- The expansion preorder `≳`: the union of all expansions. -/
def expands (T : LTS S L) : Rel S := gfp (ex T)

/-! ### Up-to functions -/

/-- Up to union with strong bisimilarity: `R ∪ ~`. -/
def unionBisim (T : LTS S L) (R : Rel S) : Rel S := fun p q => R p q ∨ bisim T p q

/-- Up to union with weak bisimilarity: `R ∪ ≈`. -/
def unionWbisim (T : LTS S L) (R : Rel S) : Rel S := fun p q => R p q ∨ wbisim T p q

/-- Up to strong bisimilarity on both sides: `~ R ~`. -/
def strongUpTo (T : LTS S L) (R : Rel S) : Rel S :=
  fun p q => ∃ p₁ q₁, bisim T p p₁ ∧ R p₁ q₁ ∧ bisim T q₁ q

/-- Up to weak bisimilarity on both sides: `≈ R ≈`.  Like the other
two-sided closures below, this is relational composition: it needs a middle
`R`-pair, so `weakUpTo T ∅ = ∅`. -/
def weakUpTo (T : LTS S L) (R : Rel S) : Rel S :=
  fun p q => ∃ p₁ q₁, wbisim T p p₁ ∧ R p₁ q₁ ∧ wbisim T q₁ q

/-- Up to expansion: `≳ R ≲`, i.e. `p ≳ p₁`, `p₁ R q₁` and `q ≳ q₁`. -/
def expUpTo (T : LTS S L) (R : Rel S) : Rel S :=
  fun p q => ∃ p₁ q₁, expands T p p₁ ∧ R p₁ q₁ ∧ expands T q q₁

/-- Expansion on the left, weak bisimilarity on the right: `≳ R ≈`. -/
def expWeakUpTo (T : LTS S L) (R : Rel S) : Rel S :=
  fun p q => ∃ p₁ q₁, expands T p p₁ ∧ R p₁ q₁ ∧ wbisim T q₁ q

/-- Weak bisimilarity on the left, (converse) expansion on the right:
`≈ R ≲`, i.e. `p ≈ p₁`, `p₁ R q₁` and `q ≳ q₁`. -/
def weakExpUpTo (T : LTS S L) (R : Rel S) : Rel S :=
  fun p q => ∃ p₁ q₁, wbisim T p p₁ ∧ R p₁ q₁ ∧ expands T q q₁

/-- Reflexive, symmetric and transitive (equivalence) closure. -/
inductive EqvClo (R : Rel S) : Rel S
  | base {p q : S} : R p q → EqvClo R p q
  | refl (p : S) : EqvClo R p p
  | symm {p q : S} : EqvClo R p q → EqvClo R q p
  | trans {p q r : S} : EqvClo R p q → EqvClo R q r → EqvClo R p r

/-! ### Basic facts (fully proved infrastructure) -/

theorem sb_mono (T : LTS S L) : MonoRel (sb T) := by
  intro R R' h p q ⟨h1, h2⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨q', hq, hr⟩ := h1 l p' hs
    exact ⟨q', hq, h _ _ hr⟩
  · obtain ⟨p', hp, hr⟩ := h2 l q' hs
    exact ⟨p', hp, h _ _ hr⟩

theorem wsimL_mono (T : LTS S L) : MonoRel (wsimL T) := by
  intro R R' h p q h1 l p' hs
  obtain ⟨q', hq, hr⟩ := h1 l p' hs
  exact ⟨q', hq, h _ _ hr⟩

theorem wsimR_mono (T : LTS S L) : MonoRel (wsimR T) := by
  intro R R' h p q h1 l q' hs
  obtain ⟨p', hp, hr⟩ := h1 l q' hs
  exact ⟨p', hp, h _ _ hr⟩

theorem wb_mono (T : LTS S L) : MonoRel (wb T) :=
  fun R R' h p q ⟨h1, h2⟩ => ⟨wsimL_mono T R R' h p q h1, wsimR_mono T R R' h p q h2⟩

theorem ex_mono (T : LTS S L) : MonoRel (ex T) := by
  intro R R' h p q ⟨h1, h2⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨q', hq, hr⟩ := h1 l p' hs
    exact ⟨q', hq, h _ _ hr⟩
  · obtain ⟨p', hp, hr⟩ := h2 l q' hs
    exact ⟨p', hp, h _ _ hr⟩

/-- A single step is a weak step. -/
theorem WStep.single {T : LTS S L} {p p' : S} {l : Option L} (h : T p l p') :
    WStep T p l p' := by
  cases l with
  | none => exact TauStar.step h (TauStar.refl _)
  | some a => exact ⟨p, p', TauStar.refl _, h, TauStar.refl _⟩

/-- Doing nothing is a weak τ-step. -/
theorem WStep.refl_none (T : LTS S L) (p : S) : WStep T p none p := TauStar.refl p

/-- A τ-step followed by a weak step is a weak step. -/
theorem WStep.tau_cons {T : LTS S L} {p p₁ p' : S} {l : Option L}
    (h : T p none p₁) (h' : WStep T p₁ l p') : WStep T p l p' := by
  cases l with
  | none => exact TauStar.step h h'
  | some a =>
    obtain ⟨x, y, h1, h2, h3⟩ := h'
    exact ⟨x, y, TauStar.step h h1, h2, h3⟩

/-- From a state without τ-successors, `τ*` stays put. -/
theorem TauStar.eq_of_noTau {T : LTS S L} {p q : S} (hp : ∀ p', ¬ T p none p')
    (h : TauStar T p q) : q = p := by
  cases h with
  | refl => rfl
  | step hs _ => exact absurd hs (hp _)

/-- Weak τ-steps from a state without τ-successors stay put. -/
theorem WStep.none_of_noTau {T : LTS S L} {p q : S} (hp : ∀ p', ¬ T p none p')
    (h : WStep T p none q) : q = p :=
  TauStar.eq_of_noTau hp h

/-- Weak visible steps from a state without τ-successors start with a strong
visible step. -/
theorem WStep.some_of_noTau {T : LTS S L} {p q : S} {a : L} (hp : ∀ p', ¬ T p none p')
    (h : WStep T p (some a) q) : ∃ p₂, T p (some a) p₂ ∧ TauStar T p₂ q := by
  obtain ⟨p₁, p₂, h1, h2, h3⟩ := h
  have := TauStar.eq_of_noTau hp h1
  subst this
  exact ⟨p₂, h2, h3⟩

/-- A state without any transitions has no weak visible transition. -/
theorem WStep.not_some_of_dead {T : LTS S L} {p q : S} {a : L} (hp : ∀ l p', ¬ T p l p')
    : ¬ WStep T p (some a) q := by
  intro h
  obtain ⟨_, h2, _⟩ := WStep.some_of_noTau (hp none) h
  exact hp _ _ h2

theorem StepHat.single {T : LTS S L} {p p' : S} {l : Option L} (h : T p l p') :
    StepHat T p l p' := Or.inl h

theorem WStepPlus.single {T : LTS S L} {p p' : S} {l : Option L} (h : T p l p') :
    WStepPlus T p l p' := by
  cases l with
  | none => exact ⟨p', h, TauStar.refl _⟩
  | some a => exact WStep.single h

theorem idRel_sb (T : LTS S L) : (idRel : Rel S) ⊑ sb T idRel := by
  intro p q (h : p = q)
  subst h
  exact ⟨fun l p' hs => ⟨p', hs, rfl⟩, fun l q' hs => ⟨q', hs, rfl⟩⟩

theorem idRel_wb (T : LTS S L) : (idRel : Rel S) ⊑ wb T idRel := by
  intro p q (h : p = q)
  subst h
  exact ⟨fun l p' hs => ⟨p', WStep.single hs, rfl⟩,
    fun l q' hs => ⟨q', WStep.single hs, rfl⟩⟩

theorem idRel_ex (T : LTS S L) : (idRel : Rel S) ⊑ ex T idRel := by
  intro p q (h : p = q)
  subst h
  exact ⟨fun l p' hs => ⟨p', StepHat.single hs, rfl⟩,
    fun l q' hs => ⟨q', WStepPlus.single hs, rfl⟩⟩

theorem bisim_refl (T : LTS S L) (p : S) : bisim T p p :=
  ⟨idRel, idRel_sb T, rfl⟩

theorem wbisim_refl (T : LTS S L) (p : S) : wbisim T p p :=
  ⟨idRel, idRel_wb T, rfl⟩

theorem expands_refl (T : LTS S L) (p : S) : expands T p p :=
  ⟨idRel, idRel_ex T, rfl⟩

/-- If `R` progresses to `R ∪ id` for a monotone functional admitting the
identity as a post-fixpoint, then `R ∪ id` is a post-fixpoint. -/
theorem postfixed_union_id {b : Rel S → Rel S} (hb : MonoRel b) (hid : (idRel : Rel S) ⊑ b idRel)
    {R : Rel S} (h : R ⊑ b (fun p q => R p q ∨ p = q)) :
    (fun p q => R p q ∨ p = q) ⊑ b (fun p q => R p q ∨ p = q) := by
  intro p q hpq
  rcases hpq with hr | he
  · exact h p q hr
  · exact hb idRel _ (fun _ _ h => Or.inr h) p q (hid p q he)

end LTSDefs

end Toy.UpTo
