import ToyUpTo.LTS

/-!
# Algebra of weak transitions, strong and weak bisimilarity, and expansion

Fully proved infrastructure used by the main results: transitivity and
symmetry facts, lifting of weak transitions across `~`, `≈` and `≳`, the
weak-challenge variant `wbWeak` of the weak functional, divergence
insensitivity, and the behaviour of the functionals on transition systems
without silent steps or without visible labels.
-/

namespace Toy.UpTo

universe u v

section WeakFacts

variable {S : Type u} {L : Type v}

/-! ### Weak transitions -/

theorem TauStar.trans {T : LTS S L} {p q r : S}
    (h1 : TauStar T p q) (h2 : TauStar T q r) : TauStar T p r := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact TauStar.step hs (ih h2)

/-- `τ*` followed by a weak step is a weak step. -/
theorem WStep.tauStar_left {T : LTS S L} {p p₁ p₂ : S} {l : Option L}
    (h1 : TauStar T p p₁) (h2 : WStep T p₁ l p₂) : WStep T p l p₂ := by
  cases l with
  | none => exact TauStar.trans h1 h2
  | some _ => obtain ⟨x, y, a1, a2, a3⟩ := h2; exact ⟨x, y, TauStar.trans h1 a1, a2, a3⟩

/-- A weak step followed by `τ*` is a weak step. -/
theorem WStep.tauStar_right {T : LTS S L} {p p₁ p₂ : S} {l : Option L}
    (h1 : WStep T p l p₁) (h2 : TauStar T p₁ p₂) : WStep T p l p₂ := by
  cases l with
  | none => exact TauStar.trans h1 h2
  | some _ => obtain ⟨x, y, a1, a2, a3⟩ := h1; exact ⟨x, y, a1, a2, TauStar.trans a3 h2⟩

theorem WStepPlus.toWStep {T : LTS S L} {p p' : S} {l : Option L}
    (h : WStepPlus T p l p') : WStep T p l p' := by
  cases l with
  | none => obtain ⟨_, h1, h2⟩ := h; exact TauStar.step h1 h2
  | some _ => exact h

theorem StepHat.toWStep {T : LTS S L} {p p' : S} {l : Option L}
    (h : StepHat T p l p') : WStep T p l p' := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact WStep.single h
  · exact WStep.refl_none _ _

/-! ### Strong bisimilarity -/

theorem bisim_symm {T : LTS S L} {p q : S} (h : bisim T p q) : bisim T q p := by
  obtain ⟨W, hW, hw⟩ := h
  exact ⟨fun x y => W y x, fun x y hxy => ⟨(hW y x hxy).2, (hW y x hxy).1⟩, hw⟩

/-- Every strong step is a weak step, so `sb T R ⊑ wb T R`. -/
theorem sb_incl_wb (T : LTS S L) (R : Rel S) : sb T R ⊑ wb T R := by
  intro p q ⟨h1, h2⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨q', hq, hr⟩ := h1 l p' hs; exact ⟨q', WStep.single hq, hr⟩
  · obtain ⟨p', hp, hr⟩ := h2 l q' hs; exact ⟨p', WStep.single hp, hr⟩

/-- Strong bisimilarity is included in weak bisimilarity. -/
theorem bisim_incl_wbisim (T : LTS S L) : bisim T ⊑ wbisim T :=
  fun _ _ ⟨W, hW, hw⟩ => ⟨W, Incl.trans hW (sb_incl_wb T W), hw⟩

/-- Every strong step is an expansion step, so `sb T R ⊑ ex T R`. -/
theorem sb_incl_ex (T : LTS S L) (R : Rel S) : sb T R ⊑ ex T R := by
  intro p q ⟨h1, h2⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨q', hq, hr⟩ := h1 l p' hs; exact ⟨q', StepHat.single hq, hr⟩
  · obtain ⟨p', hp, hr⟩ := h2 l q' hs; exact ⟨p', WStepPlus.single hp, hr⟩

/-- Strong bisimilarity is included in expansion. -/
theorem bisim_incl_expands (T : LTS S L) : bisim T ⊑ expands T :=
  fun _ _ ⟨W, hW, hw⟩ => ⟨W, Incl.trans hW (sb_incl_ex T W), hw⟩

theorem bisim_lift_tauStar {T : LTS S L} {q₁ q₁' q : S}
    (ht : TauStar T q₁ q₁') (hb : bisim T q₁ q) : ∃ q', TauStar T q q' ∧ bisim T q₁' q' := by
  induction ht generalizing q with
  | refl => exact ⟨q, TauStar.refl _, hb⟩
  | step hs _ ih =>
    obtain ⟨n, hn, hbn⟩ := (gfp_postfixed (sb_mono T) _ _ hb).1 none _ hs
    obtain ⟨q', h1, h2⟩ := ih hbn
    exact ⟨q', TauStar.step hn h1, h2⟩

/-- Weak transitions lift across strong bisimilarity. -/
theorem bisim_lift_wstep {T : LTS S L} {q₁ q₁' q : S}
    {l : Option L} (hw : WStep T q₁ l q₁') (hb : bisim T q₁ q) :
    ∃ q', WStep T q l q' ∧ bisim T q₁' q' := by
  cases l with
  | none => exact bisim_lift_tauStar hw hb
  | some a =>
    obtain ⟨x₁, x₂, h1, h2, h3⟩ := hw
    obtain ⟨y₁, hy1, hb1⟩ := bisim_lift_tauStar h1 hb
    obtain ⟨y₂, hy2, hb2⟩ := (gfp_postfixed (sb_mono T) _ _ hb1).1 (some a) _ h2
    obtain ⟨q', hy3, hb3⟩ := bisim_lift_tauStar h3 hb2
    exact ⟨q', ⟨y₁, y₂, hy1, hy2, hy3⟩, hb3⟩

/-! ### Weak bisimilarity -/

/-- Weak bisimilarity is symmetric. -/
theorem wbisim_symm {T : LTS S L} {p q : S} (h : wbisim T p q) : wbisim T q p := by
  obtain ⟨W, hW, hw⟩ := h
  refine ⟨fun x y => W y x, ?_, hw⟩
  intro x y hxy
  obtain ⟨h1, h2⟩ := hW y x hxy
  exact ⟨fun l x' hs => h2 l x' hs, fun l y' hs => h1 l y' hs⟩

theorem wbisim_lift_tauStar {T : LTS S L} {p p' q : S}
    (ht : TauStar T p p') (hw : wbisim T p q) : ∃ q', TauStar T q q' ∧ wbisim T p' q' := by
  induction ht generalizing q with
  | refl => exact ⟨q, TauStar.refl _, hw⟩
  | step hs _ ih =>
    obtain ⟨q₁, hq1, hw1⟩ := (gfp_postfixed (wb_mono T) _ _ hw).1 none _ hs
    obtain ⟨q', h1, h2⟩ := ih hw1
    exact ⟨q', TauStar.trans hq1 h1, h2⟩

/-- Weak transitions lift across weak bisimilarity. -/
theorem wbisim_lift_wstep {T : LTS S L} {p p' q : S} {l : Option L}
    (hs : WStep T p l p') (hw : wbisim T p q) : ∃ q', WStep T q l q' ∧ wbisim T p' q' := by
  cases l with
  | none => exact wbisim_lift_tauStar hs hw
  | some a =>
    obtain ⟨p₁, p₂, h1, h2, h3⟩ := hs
    obtain ⟨q₁, hq1, hw1⟩ := wbisim_lift_tauStar h1 hw
    obtain ⟨q₂, hq2, hw2⟩ := (gfp_postfixed (wb_mono T) _ _ hw1).1 (some a) _ h2
    obtain ⟨q', hq3, hw3⟩ := wbisim_lift_tauStar h3 hw2
    exact ⟨q', WStep.tauStar_left hq1 (WStep.tauStar_right hq2 hq3), hw3⟩

/-- Weak bisimilarity is transitive. -/
theorem wbisim_trans {T : LTS S L} {p r q : S}
    (h1 : wbisim T p r) (h2 : wbisim T r q) : wbisim T p q := by
  refine ⟨fun p q => ∃ r, wbisim T p r ∧ wbisim T r q, ?_, r, h1, h2⟩
  intro p q ⟨r, hpr, hrq⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨r', hr, hpr'⟩ := (gfp_postfixed (wb_mono T) _ _ hpr).1 l p' hs
    obtain ⟨q', hq, hrq'⟩ := wbisim_lift_wstep hr hrq
    exact ⟨q', hq, r', hpr', hrq'⟩
  · obtain ⟨r', hr, hrq'⟩ := (gfp_postfixed (wb_mono T) _ _ hrq).2 l q' hs
    obtain ⟨p', hp, hrp'⟩ := wbisim_lift_wstep hr (wbisim_symm hpr)
    exact ⟨p', hp, r', wbisim_symm hrp', hrq'⟩

/-! ### Expansion -/

theorem expands_lift_tauStar {T : LTS S L} {p r r' : S}
    (ht : TauStar T r r') (he : expands T p r) : ∃ p', TauStar T p p' ∧ expands T p' r' := by
  induction ht generalizing p with
  | refl => exact ⟨p, TauStar.refl _, he⟩
  | step hs _ ih =>
    obtain ⟨_, ⟨p₀, h0, h01⟩, he1⟩ := (gfp_postfixed (ex_mono T) _ _ he).2 none _ hs
    obtain ⟨p', h1, h2⟩ := ih he1
    exact ⟨p', TauStar.step h0 (TauStar.trans h01 h1), h2⟩

/-- Moves of the faster (right) state lift to the slower (left) state with at
least one step. -/
theorem expands_lift_wstepPlus {T : LTS S L} {p r r' : S} {l : Option L}
    (hw : WStepPlus T r l r') (he : expands T p r) :
    ∃ p', WStepPlus T p l p' ∧ expands T p' r' := by
  cases l with
  | none =>
    obtain ⟨m, hm, ht⟩ := hw
    obtain ⟨_, ⟨p₀, h0, h01⟩, he1⟩ := (gfp_postfixed (ex_mono T) _ _ he).2 none _ hm
    obtain ⟨p', h1, h2⟩ := expands_lift_tauStar ht he1
    exact ⟨p', ⟨p₀, h0, TauStar.trans h01 h1⟩, h2⟩
  | some a =>
    obtain ⟨r₁, r₂, h1, h2, h3⟩ := hw
    obtain ⟨p₁, hp1, he1⟩ := expands_lift_tauStar h1 he
    obtain ⟨p₂, hp2, he2⟩ := (gfp_postfixed (ex_mono T) _ _ he1).2 (some a) _ h2
    obtain ⟨p', hp3, he3⟩ := expands_lift_tauStar h3 he2
    exact ⟨p', WStep.tauStar_left hp1 (WStep.tauStar_right (l := some a) hp2 hp3), he3⟩

/-- Expansion is transitive. -/
theorem expands_trans {T : LTS S L} {p r q : S}
    (h1 : expands T p r) (h2 : expands T r q) : expands T p q := by
  refine ⟨fun p q => ∃ r, expands T p r ∧ expands T r q, ?_, r, h1, h2⟩
  intro p q ⟨r, hpr, hrq⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨r', hsh, hpr'⟩ := (gfp_postfixed (ex_mono T) _ _ hpr).1 l p' hs
    rcases hsh with hr | ⟨rfl, rfl⟩
    · obtain ⟨q', hq, hrq'⟩ := (gfp_postfixed (ex_mono T) _ _ hrq).1 _ r' hr
      exact ⟨q', hq, r', hpr', hrq'⟩
    · exact ⟨q, Or.inr ⟨rfl, rfl⟩, r', hpr', hrq⟩
  · obtain ⟨r', hr, hrq'⟩ := (gfp_postfixed (ex_mono T) _ _ hrq).2 l q' hs
    obtain ⟨p', hp, hpr'⟩ := expands_lift_wstepPlus hr hpr
    exact ⟨p', hp, r', hpr', hrq'⟩

/-- Expansion is included in weak bisimilarity. -/
theorem expands_incl_wbisim {T : LTS S L} {p q : S}
    (h : expands T p q) : wbisim T p q := by
  refine ⟨expands T, ?_, h⟩
  intro p q hpq
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨q', h1, h2⟩ := (gfp_postfixed (ex_mono T) _ _ hpq).1 l p' hs
    exact ⟨q', StepHat.toWStep h1, h2⟩
  · obtain ⟨p', h1, h2⟩ := (gfp_postfixed (ex_mono T) _ _ hpq).2 l q' hs
    exact ⟨p', WStepPlus.toWStep h1, h2⟩

/-! ### The weak-challenge functional -/

/-- The weak bisimulation functional with *weak* challenges: every weak move
`p =l̂⇒ p'` is answered by a weak move `q =l̂⇒ q'` into `R`, and vice versa. -/
def wbWeak (T : LTS S L) (R : Rel S) : Rel S := fun p q =>
  (∀ l p', WStep T p l p' → ∃ q', WStep T q l q' ∧ R p' q') ∧
  (∀ l q', WStep T q l q' → ∃ p', WStep T p l p' ∧ R p' q')

theorem wbWeak_mono (T : LTS S L) : MonoRel (wbWeak T) := by
  intro R R' h p q ⟨h1, h2⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨q', hq, hr⟩ := h1 l p' hs; exact ⟨q', hq, h _ _ hr⟩
  · obtain ⟨p', hp, hr⟩ := h2 l q' hs; exact ⟨p', hp, h _ _ hr⟩

/-- Weak challenges include strong ones: `wbWeak T R ⊑ wb T R`. -/
theorem wbWeak_incl_wb (T : LTS S L) (R : Rel S) : wbWeak T R ⊑ wb T R :=
  fun _ _ ⟨h1, h2⟩ => ⟨fun l p' hs => h1 l p' (WStep.single hs),
    fun l q' hs => h2 l q' (WStep.single hs)⟩

/-- The weak-challenge functional has the same greatest fixpoint as `wb`:
`gfp (wbWeak T) ⊑ ≈` and `≈ ⊑ gfp (wbWeak T)`. -/
theorem gfp_wbWeak_eq_wbisim (T : LTS S L) :
    gfp (wbWeak T) ⊑ wbisim T ∧ wbisim T ⊑ gfp (wbWeak T) := by
  refine ⟨fun _ _ ⟨W, hW, hw⟩ => ⟨W, Incl.trans hW (wbWeak_incl_wb T W), hw⟩, ?_⟩
  refine incl_gfp_of_postfixed ?_
  intro p q hpq
  refine ⟨fun l p' hs => wbisim_lift_wstep hs hpq, fun l q' hs => ?_⟩
  obtain ⟨p', hp, hw⟩ := wbisim_lift_wstep hs (wbisim_symm hpq)
  exact ⟨p', hp, wbisim_symm hw⟩

/-- **Up to weak bisimilarity is compatible with the weak-challenge
functional.**  With weak challenges, `≈ R ≈` is a sound technique; the
Sangiorgi–Milner pitfall is specific to strong (single-step) challenges. -/
theorem weak_challenge_upto_weak_bisim_compatible (T : LTS S L) :
    Compatible (wbWeak T) (weakUpTo T) := by
  refine ⟨fun R R' h p q ⟨p₁, q₁, h1, h2, h3⟩ => ⟨p₁, q₁, h1, h _ _ h2, h3⟩, ?_⟩
  intro R p q ⟨p₁, q₁, hp, hr, hq⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · obtain ⟨p₁', hw1, hb1⟩ := wbisim_lift_wstep hs hp
    obtain ⟨q₁', hw2, hr2⟩ := hr.1 l p₁' hw1
    obtain ⟨q', hw3, hb3⟩ := wbisim_lift_wstep hw2 hq
    exact ⟨q', hw3, p₁', q₁', hb1, hr2, hb3⟩
  · obtain ⟨q₁', hw1, hb1⟩ := wbisim_lift_wstep hs (wbisim_symm hq)
    obtain ⟨p₁', hw2, hr2⟩ := hr.2 l q₁' hw1
    obtain ⟨p', hw3, hb3⟩ := wbisim_lift_wstep hw2 (wbisim_symm hp)
    exact ⟨p', hw3, p₁', q₁', wbisim_symm hb3, hr2, wbisim_symm hb1⟩

/-- Corollary: with weak challenges, `≈ R ≈` is sound, and its conclusion is
weak bisimilarity itself. -/
theorem weak_challenge_upto_weak_bisim_sound (T : LTS S L) (R : Rel S)
    (h : R ⊑ wbWeak T (weakUpTo T R)) : R ⊑ wbisim T :=
  let hc := weak_challenge_upto_weak_bisim_compatible T
  Incl.trans (sound_of_compatible_of_monotone_functional (wbWeak_mono T) hc.mono hc.comm R h)
    (gfp_wbWeak_eq_wbisim T).1

/-! ### Divergence insensitivity -/

/-- A two-state system: `true` has a silent self-loop, `false` is dead. -/
def loopLTS : LTS Bool Unit := fun p l p' => p = true ∧ l = none ∧ p' = true

/-- **Divergence insensitivity.**  A silently diverging state is weakly
bisimilar to, and expands, a dead state; strong bisimilarity distinguishes
them. -/
theorem divergence_insensitive :
    wbisim loopLTS true false ∧ expands loopLTS true false ∧ ¬ bisim loopLTS true false := by
  refine ⟨⟨fun p q => p = true ∧ q = false, ?_, rfl, rfl⟩,
    ⟨fun p q => p = true ∧ q = false, ?_, rfl, rfl⟩, ?_⟩
  · rintro p q ⟨rfl, rfl⟩
    refine ⟨fun l p' ⟨_, hl, hp'⟩ => ?_, fun l q' ⟨h, _, _⟩ => absurd h (by decide)⟩
    subst hl; subst hp'
    exact ⟨false, WStep.refl_none _ _, rfl, rfl⟩
  · rintro p q ⟨rfl, rfl⟩
    refine ⟨fun l p' ⟨_, hl, hp'⟩ => ?_, fun l q' ⟨h, _, _⟩ => absurd h (by decide)⟩
    subst hl; subst hp'
    exact ⟨false, Or.inr ⟨rfl, rfl⟩, rfl, rfl⟩
  · rintro ⟨W, hW, hw⟩
    obtain ⟨_, ⟨h, _, _⟩, _⟩ := (hW _ _ hw).1 none true ⟨rfl, rfl, rfl⟩
    exact absurd h (by decide)

/-! ### Transition systems without silent steps or without visible labels -/

/-- `T` has no silent transitions. -/
def NoTau (T : LTS S L) : Prop := ∀ p p', ¬ T p none p'

theorem WStep.some_of_noTau' {T : LTS S L} (hT : NoTau T) {p q : S} {a : L}
    (h : WStep T p (some a) q) : T p (some a) q := by
  obtain ⟨p₁, p₂, h1, h2, h3⟩ := h
  have e1 := TauStar.eq_of_noTau (hT p) h1
  have e2 := TauStar.eq_of_noTau (hT p₂) h3
  subst e1; subst e2
  exact h2

/-- Without silent steps, the weak functional is below the strong one. -/
theorem wb_incl_sb_of_noTau {T : LTS S L} (hT : NoTau T) (R : Rel S) : wb T R ⊑ sb T R := by
  intro p q ⟨h1, h2⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · cases l with
    | none => exact absurd hs (hT p p')
    | some a =>
      obtain ⟨q', hq, hr⟩ := h1 (some a) p' hs
      exact ⟨q', WStep.some_of_noTau' hT hq, hr⟩
  · cases l with
    | none => exact absurd hs (hT q q')
    | some a =>
      obtain ⟨p', hp, hr⟩ := h2 (some a) q' hs
      exact ⟨p', WStep.some_of_noTau' hT hp, hr⟩

/-- Without silent steps, weak bisimilarity is strong bisimilarity. -/
theorem wbisim_incl_bisim_of_noTau {T : LTS S L} (hT : NoTau T) : wbisim T ⊑ bisim T :=
  fun _ _ ⟨W, hW, hw⟩ => ⟨W, Incl.trans hW (wb_incl_sb_of_noTau hT W), hw⟩

/-- Without silent steps, the expansion functional is below the strong one. -/
theorem ex_incl_sb_of_noTau {T : LTS S L} (hT : NoTau T) (R : Rel S) : ex T R ⊑ sb T R := by
  intro p q ⟨h1, h2⟩
  refine ⟨fun l p' hs => ?_, fun l q' hs => ?_⟩
  · cases l with
    | none => exact absurd hs (hT p p')
    | some a =>
      obtain ⟨q', hq, hr⟩ := h1 (some a) p' hs
      rcases hq with hq | ⟨h, _⟩
      · exact ⟨q', hq, hr⟩
      · cases h
  · cases l with
    | none => exact absurd hs (hT q q')
    | some a =>
      obtain ⟨p', hp, hr⟩ := h2 (some a) q' hs
      exact ⟨p', WStep.some_of_noTau' hT hp, hr⟩

/-- Without silent steps, expansion is strong bisimilarity. -/
theorem expands_incl_bisim_of_noTau {T : LTS S L} (hT : NoTau T) : expands T ⊑ bisim T :=
  fun _ _ ⟨W, hW, hw⟩ => ⟨W, Incl.trans hW (ex_incl_sb_of_noTau hT W), hw⟩

/-- Without visible labels, weak bisimilarity is the total relation: every
move is silent and can be answered by standing still. -/
theorem wbisim_total_of_no_visible {T : LTS S L} (hL : L → False) (p q : S) :
    wbisim T p q := by
  refine ⟨topRel, ?_, trivial⟩
  intro p q _
  refine ⟨fun l p' _ => ?_, fun l q' _ => ?_⟩
  · cases l with
    | none => exact ⟨q, WStep.refl_none _ _, trivial⟩
    | some a => exact (hL a).elim
  · cases l with
    | none => exact ⟨p, WStep.refl_none _ _, trivial⟩
    | some a => exact (hL a).elim

/-- Without visible labels, every up-to function is sound for `wb`. -/
theorem sound_wb_of_no_visible {T : LTS S L} (hL : L → False) (f : Rel S → Rel S) :
    Sound (wb T) f :=
  fun _ _ p q _ => wbisim_total_of_no_visible hL p q

end WeakFacts

end Toy.UpTo
