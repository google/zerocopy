import ToySim.Simulation

/-!
# Basic facts (all fully proved)

Elementary lemmas about executions, the refinement preorder, and two ready-made
forward simulations (the identity, and the "measure on source states" form).
-/

namespace Toy.Sim

variable {E Res : Type}

/-! ## Traces and executions -/

theorem obs_eq_nil {e : Option E} : obs e = [] ↔ e = none := by
  cases e <;> simp [obs]

theorem Star.single {L : LTS E Res} {s s' : L.State} {e : Option E}
    (h : L.step s e s') : Star L s (obs e) s' :=
  Star.step h (Star.refl s') (by simp)

theorem Star.trans {L : LTS E Res} {s s' s'' : L.State} {t t' : List E}
    (h₁ : Star L s t s') (h₂ : Star L s' t' s'') : Star L s (t ++ t') s'' := by
  induction h₁ with
  | refl s => simpa using h₂
  | step h _ ht ih => exact Star.step h (ih h₂) (by simp [ht, List.append_assoc])

/-- Inversion of an execution: it is empty, or starts with a step. -/
theorem Star.inv {L : LTS E Res} {s s'' : L.State} {t : List E} (h : Star L s t s'') :
    (t = [] ∧ s'' = s) ∨
      ∃ e s' t', L.step s e s' ∧ Star L s' t' s'' ∧ t = obs e ++ t' := by
  cases h with
  | refl => exact Or.inl ⟨rfl, rfl⟩
  | step h hs ht => exact Or.inr ⟨_, _, _, h, hs, ht⟩

theorem Plus.star {L : LTS E Res} {s s' : L.State} {t : List E}
    (h : Plus L s t s') : Star L s t s' := by
  obtain ⟨e, s₁, t₁, hstep, hstar, rfl⟩ := h
  exact Star.step hstep hstar rfl

theorem Plus.single {L : LTS E Res} {s s' : L.State} {e : Option E}
    (h : L.step s e s') : Plus L s (obs e) s' :=
  ⟨e, s', [], h, Star.refl s', by simp⟩

/-- An execution is either a `Plus` or empty. -/
theorem Star.plus_or_refl {L : LTS E Res} {s s' : L.State} {t : List E}
    (h : Star L s t s') : Plus L s t s' ∨ (t = [] ∧ s' = s) := by
  rcases h.inv with h | ⟨e, s₁, t₁, hstep, hstar, ht⟩
  · exact Or.inr h
  · exact Or.inl ⟨e, s₁, t₁, hstep, hstar, ht⟩

/-- From a state with no outgoing step, the only execution is the empty one. -/
theorem Star.of_noStep {L : LTS E Res} {s s' : L.State} {t : List E}
    (hno : ∀ e s₁, ¬ L.step s e s₁) (h : Star L s t s') : t = [] ∧ s' = s := by
  rcases h.inv with h | ⟨e, s₁, _, hstep, _, _⟩
  · exact h
  · exact absurd hstep (hno e s₁)

/-- A property closed under steps holds along every execution. -/
theorem Star.invariant {L : LTS E Res} (P : L.State → Prop)
    (hP : ∀ s e s', P s → L.step s e s' → P s')
    {s s' : L.State} {t : List E} (h : Star L s t s') (hs : P s) : P s' := by
  induction h with
  | refl s => exact hs
  | step h _ _ ih => exact ih (hP _ _ _ hs h)

/-! ## Stuck and safe states -/

theorem Stuck.not_safe {L : LTS E Res} {s : L.State} (h : Stuck L s) : ¬ Safe L s := by
  intro hsafe
  rcases hsafe s (Star.refl s) with ⟨r, hr⟩ | ⟨e, s', hs⟩
  · exact h.2 r hr
  · exact h.1 e s' hs

/-- If no state is stuck, every state is safe. -/
theorem safe_of_no_stuck {L : LTS E Res} (h : ∀ s, ¬ Stuck L s) (s : L.State) : Safe L s := by
  intro s' _
  apply Classical.byContradiction
  intro hn
  refine h s' ⟨?_, ?_⟩
  · intro e s'' hs
    exact hn (Or.inr ⟨e, s'', hs⟩)
  · intro r hr
    exact hn (Or.inl ⟨r, hr⟩)

/-! ## The refinement preorder -/

theorem Improves.refl (b : Behavior E Res) : Improves b b := Or.inl rfl

/-- A source that goes wrong immediately permits every behaviour. -/
theorem improves_goesWrong_nil (b : Behavior E Res) : Improves (.goesWrong []) b :=
  Or.inr ⟨[], rfl, List.nil_prefix⟩

theorem Improves.trans {b₁ b₂ b₃ : Behavior E Res}
    (h₁₂ : Improves b₁ b₂) (h₂₃ : Improves b₂ b₃) : Improves b₁ b₃ := by
  rcases h₁₂ with rfl | ⟨t, rfl, hpre⟩
  · exact h₂₃
  · rcases h₂₃ with rfl | ⟨t', rfl, hpre'⟩
    · exact Or.inr ⟨t, rfl, hpre⟩
    · exact Or.inr ⟨t, rfl, List.IsPrefix.trans hpre hpre'⟩

/-- `Improves` is antisymmetric: it is a partial order on behaviours. -/
theorem Improves.antisymm {b₁ b₂ : Behavior E Res}
    (h₁₂ : Improves b₁ b₂) (h₂₁ : Improves b₂ b₁) : b₁ = b₂ := by
  rcases h₁₂ with rfl | ⟨t, rfl, hpre⟩
  · rfl
  · rcases h₂₁ with h | ⟨t', rfl, hpre'⟩
    · exact h.symm
    · have hlen : t.length = t'.length :=
        Nat.le_antisymm hpre.length_le hpre'.length_le
      obtain ⟨u, hu⟩ := hpre
      simp only [Behavior.trace] at hu
      have hu' : u = [] := by
        have := congrArg List.length hu
        simp only [List.length_append] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst hu'
      simp at hu
      rw [hu]

theorem RefinedBy.refl (L : LTS E Res) : RefinedBy L L :=
  fun b hb => ⟨b, hb, Improves.refl b⟩

theorem RefinedBy.trans {L₁ L₂ L₃ : LTS E Res}
    (h₁₂ : RefinedBy L₁ L₂) (h₂₃ : RefinedBy L₂ L₃) : RefinedBy L₁ L₃ := by
  intro b₃ hb₃
  obtain ⟨b₂, hb₂, h₂₃'⟩ := h₂₃ b₃ hb₃
  obtain ⟨b₁, hb₁, h₁₂'⟩ := h₁₂ b₂ hb₂
  exact ⟨b₁, hb₁, h₁₂'.trans h₂₃'⟩

/-- A program with no going-wrong behaviour has an initial state. -/
theorem NeverGoesWrong.exists_init {L : LTS E Res} (h : NeverGoesWrong L) :
    ∃ s, L.init s := by
  apply Classical.byContradiction
  intro hn
  exact h [] (Or.inr ⟨rfl, fun s hs => hn ⟨s, hs⟩⟩)

/-- For a source that never goes wrong, refinement is behaviour inclusion:
every target behaviour is a source behaviour. -/
theorem refinedBy_neverGoesWrong_behaviors_subset {L₁ L₂ : LTS E Res}
    (href : RefinedBy L₁ L₂) (hsafe : NeverGoesWrong L₁)
    {b : Behavior E Res} (hb : HasBehavior L₂ b) : HasBehavior L₁ b := by
  obtain ⟨b₁, hb₁, himp⟩ := href b hb
  rcases himp with rfl | ⟨t, rfl, _⟩
  · exact hb₁
  · exact absurd hb₁ (hsafe t)

/-! ## Ready-made forward simulations -/

/-- The identity is a forward simulation of a system by itself, with a
one-point index and the empty order. -/
theorem isForwardSim_id (L : LTS E Res) :
    IsForwardSim L L (fun (_ _ : Unit) => False) (fun _ s s' => s = s') where
  wf := ⟨fun a => Acc.intro a (fun _ h => h.elim)⟩
  init := fun s hs => ⟨(), s, hs, rfl⟩
  final := by
    intro _ s₁ s₂ r hR hfin
    subst hR
    exact hfin
  step := by
    intro _ s₁ s₂ e s₁' hR hstep
    subst hR
    exact ⟨(), s₁', Or.inl (Plus.single hstep), rfl⟩

/-- The "measure on source states" form of a forward simulation: a plain
relation `R` between states together with a natural-number measure `m` on
source states that decreases whenever the target stutters.  It induces an
indexed forward simulation whose index is the source state itself.

The measure takes values in `Nat`, so this form only covers stuttering bounds
of order type at most `ω`; the indexed form allows any well-founded order.
The stuttering alternative is "`Star` with the same trace and a smaller
measure" (as in CompCert's `forward_simulation_star_wf`); CompCert's
`forward_simulation_star` uses the zero-step variant instead. -/
theorem isForwardSim_of_measure {L₁ L₂ : LTS E Res}
    (R : L₁.State → L₂.State → Prop) (m : L₁.State → Nat)
    (hinit : ∀ s₁, L₁.init s₁ → ∃ s₂, L₂.init s₂ ∧ R s₁ s₂)
    (hfinal : ∀ s₁ s₂ r, R s₁ s₂ → L₁.final s₁ r → L₂.final s₂ r)
    (hstep : ∀ s₁ s₂ e s₁', R s₁ s₂ → L₁.step s₁ e s₁' →
      ∃ s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ m s₁' < m s₁)) ∧
        R s₁' s₂') :
    IsForwardSim L₁ L₂ (fun i' i : L₁.State => m i' < m i)
      (fun i s₁ s₂ => i = s₁ ∧ R s₁ s₂) where
  wf := InvImage.wf m Nat.lt_wfRel.wf
  init := by
    intro s₁ hs₁
    obtain ⟨s₂, hs₂, hR⟩ := hinit s₁ hs₁
    exact ⟨s₁, s₂, hs₂, rfl, hR⟩
  final := by
    intro i s₁ s₂ r hR hfin
    exact hfinal s₁ s₂ r hR.2 hfin
  step := by
    intro i s₁ s₂ e s₁' hR hs
    obtain ⟨rfl, hR⟩ := hR
    obtain ⟨s₂', hmove, hR'⟩ := hstep _ s₂ e s₁' hR hs
    exact ⟨s₁', s₂', hmove, rfl, hR'⟩

/-- The "measure on source states" form is exactly an indexed forward
simulation of the corresponding shape: the three measure-form clauses hold if
and only if the induced indexed relation and order form a forward
simulation. -/
theorem isForwardSim_measure_iff {L₁ L₂ : LTS E Res}
    (R : L₁.State → L₂.State → Prop) (m : L₁.State → Nat) :
    IsForwardSim L₁ L₂ (fun i' i : L₁.State => m i' < m i)
        (fun i s₁ s₂ => i = s₁ ∧ R s₁ s₂) ↔
      (∀ s₁, L₁.init s₁ → ∃ s₂, L₂.init s₂ ∧ R s₁ s₂) ∧
      (∀ s₁ s₂ r, R s₁ s₂ → L₁.final s₁ r → L₂.final s₂ r) ∧
      (∀ s₁ s₂ e s₁', R s₁ s₂ → L₁.step s₁ e s₁' →
        ∃ s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ m s₁' < m s₁)) ∧
          R s₁' s₂') := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro s₁ hs₁
      obtain ⟨_, s₂, hs₂, _, hR⟩ := h.init s₁ hs₁
      exact ⟨s₂, hs₂, hR⟩
    · intro s₁ s₂ r hR hfin
      exact h.final s₁ s₁ s₂ r ⟨rfl, hR⟩ hfin
    · intro s₁ s₂ e s₁' hR hstep
      obtain ⟨i', s₂', hmove, hi', hR'⟩ := h.step s₁ s₁ s₂ e s₁' ⟨rfl, hR⟩ hstep
      subst hi'
      exact ⟨s₂', hmove, hR'⟩
  · rintro ⟨hinit, hfinal, hstep⟩
    exact isForwardSim_of_measure R m hinit hfinal hstep

/-! ## Chains -/

/-- A single forward simulation is a one-pass chain. -/
theorem fsimChain_of_isForwardSim {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop} (h : IsForwardSim L₁ L₂ ord R) :
    FSimChain L₁ L₂ :=
  FSimChain.cons ord R h (FSimChain.nil L₂)

/-! ## Receptiveness and determinacy: elementary facts -/

/-- Every system is receptive when events only match themselves. -/
theorem receptive_eq (L : LTS E Res) : Receptive Eq L := by
  intro s a s₁ b h hab
  subst hab
  exact ⟨s₁, h⟩

/-- Receptiveness is antitone in the matching relation. -/
theorem Receptive.anti {M M' : E → E → Prop} {L : LTS E Res}
    (h : Receptive M L) (hsub : ∀ a b, M' a b → M a b) : Receptive M' L :=
  fun s a s₁ b hstep hab => h s a s₁ b hstep (hsub a b hab)

/-- Label matching is monotone in the matching relation. -/
theorem LabelMatch.mono {M M' : E → E → Prop} (hsub : ∀ a b, M a b → M' a b)
    {e₁ e₂ : Option E} (h : LabelMatch M e₁ e₂) : LabelMatch M' e₁ e₂ := by
  cases e₁ <;> cases e₂
  · trivial
  · exact h
  · exact h
  · exact hsub _ _ h

/-- Determinacy is monotone in the matching relation.  Together with
`Receptive.anti`, this means the flip lemma also applies when the source is
receptive for `M₁`, the target determinate for `M₂`, and `M₂ ⊆ M₁`. -/
theorem Determinate.mono {M M' : E → E → Prop} {L : LTS E Res}
    (h : Determinate M L) (hsub : ∀ a b, M a b → M' a b) : Determinate M' L where
  labels := fun s e₁ s₁ e₂ s₂ h₁ h₂ => LabelMatch.mono hsub (h.labels s e₁ s₁ e₂ s₂ h₁ h₂)
  functional := h.functional
  init := h.init
  finalNoStep := h.finalNoStep
  finalDet := h.finalDet

/-- `StepLabelsMatch M L` constrains `M` on the events of `L`: `M` is
reflexive on every event `L` can emit, and symmetric on any two events offered
by the same state.  So although no algebraic axiom on `M` appears in the flip
lemma, determinacy of an event-emitting target is impossible for an
irreflexive `M`. -/
theorem StepLabelsMatch.refl_symm {M : E → E → Prop} {L : LTS E Res}
    (h : StepLabelsMatch M L) {s s₁ s₂ : L.State} {a b : E}
    (h₁ : L.step s (some a) s₁) (h₂ : L.step s (some b) s₂) :
    M a a ∧ M a b ∧ M b a :=
  ⟨h s (some a) s₁ (some a) s₁ h₁ h₁, h s (some a) s₁ (some b) s₂ h₁ h₂,
    h s (some b) s₂ (some a) s₁ h₂ h₁⟩

/-! ## The composite order when the second order is transitive -/

/-- The transitive closure of a transitive relation is the relation itself. -/
theorem transGen_of_transitive {α : Type} {r : α → α → Prop}
    (htrans : ∀ a b c, r a b → r b c → r a c) {a b : α} (h : Relation.TransGen r a b) :
    r a b := by
  induction h with
  | single h => exact h
  | tail _ h ih => exact htrans _ _ _ ih h

/-- If the second-pass order `ord₂` is already transitive (for example `<` on
`Nat`), the composite order `compOrd ord₁ ord₂` is the plain lexicographic
order on `I₂ × I₁`: the transitive closure in `compOrd` only matters for
non-transitive `ord₂`. -/
theorem compOrd_iff_lex_of_transitive {I₁ I₂ : Type} {ord₁ : I₁ → I₁ → Prop}
    {ord₂ : I₂ → I₂ → Prop} (htrans : ∀ a b c, ord₂ a b → ord₂ b c → ord₂ a c)
    (p q : I₂ × I₁) :
    compOrd ord₁ ord₂ p q ↔ (ord₂ p.1 q.1 ∨ (p.1 = q.1 ∧ ord₁ p.2 q.2)) := by
  constructor
  · rintro (h | h)
    · exact Or.inl (transGen_of_transitive htrans h)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Relation.TransGen.single h)
    · exact Or.inr h

end Toy.Sim
