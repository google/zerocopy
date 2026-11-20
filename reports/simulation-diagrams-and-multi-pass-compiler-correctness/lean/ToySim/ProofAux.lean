import ToySim.Basic

/-!
# Auxiliary lemmas for the main proofs

Lemmas and proof-internal definitions used by the proofs in
`ToySim.Statements`.  Nothing in this file is part of any stated result: the
definitions here (`DivF`, `DivB`, `StarN`, `FIdx`, `FOrd`, `FRel`) appear only
inside proofs.

* `fsim_star`: a forward step diagram simulates a finite run.
* `silentDiv_of_coind`: a set of states closed under "has a silent successor
  in the set" yields an infinite silent run (uses a choice principle).
* `star_sim₂`, `plus_sim₂`: the second pass of a composition simulates a run of
  the middle language, recording whether the index stayed put or decreased in
  the transitive closure of the order.
* `bsim_star`, `bsim_diverge`: a backward simulation simulates a target run,
  or the source gets stuck along the way.
* `f2b_trans`, `FIdx`, `FOrd`, `FRel`: the backward relation built from a
  forward simulation for the flip lemma.  `FRel (.after n)` relates a source
  state to a target state that reaches a forward-related state in `n` silent
  steps; `FRel (.before n)` relates a source state that can emit an event `a`
  to a target state that is between a forward-related state and the emission
  of `a`, with `n` steps (one of them emitting `a`) left to go.
-/

namespace Toy.Sim.ProofAux
open Toy.Sim

variable {E Res : Type}

theorem obs_append_eq_nil {e : Option E} {t : List E} (h : ([] : List E) = obs e ++ t) :
    e = none ∧ t = [] := by
  cases e with
  | none => exact ⟨rfl, by simpa using h.symm⟩
  | some a => simp [obs] at h

theorem Plus.trans_star {L : LTS E Res} {s s' s'' : L.State} {t t' : List E}
    (h₁ : Plus L s t s') (h₂ : Star L s' t' s'') : Plus L s (t ++ t') s'' := by
  obtain ⟨e, s₁, t₁, hstep, hstar, rfl⟩ := h₁
  exact ⟨e, s₁, t₁ ++ t', hstep, hstar.trans h₂, by simp [List.append_assoc]⟩

theorem Star.trans_plus {L : LTS E Res} {s s' s'' : L.State} {t t' : List E}
    (h₁ : Star L s t s') (h₂ : Plus L s' t' s'') : Plus L s (t ++ t') s'' := by
  rcases h₁.plus_or_refl with hp | ⟨rfl, rfl⟩
  · exact Plus.trans_star hp h₂.star
  · simpa using h₂

/-! ## Forward simulation of runs and of silent divergence -/

theorem fsim_star {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hstep : FSimStep L₁ L₂ ord R) {s₁ s₁' : L₁.State} {t : List E}
    (hrun : Star L₁ s₁ t s₁') :
    ∀ i s₂, R i s₁ s₂ → ∃ i' s₂', Star L₂ s₂ t s₂' ∧ R i' s₁' s₂' := by
  induction hrun with
  | refl s => exact fun i s₂ hR => ⟨i, s₂, Star.refl _, hR⟩
  | @step _ _ _ e _ _ h _ ht ih =>
    intro i s₂ hR
    obtain ⟨i', s₂', hmove, hR'⟩ := hstep i _ s₂ e _ hR h
    have hstar : Star L₂ s₂ (obs e) s₂' := by
      rcases hmove with hp | ⟨hs, _⟩
      · exact hp.star
      · exact hs
    obtain ⟨i'', s₂'', hstar', hR''⟩ := ih i' s₂' hR'
    exact ⟨i'', s₂'', by rw [ht]; exact hstar.trans hstar', hR''⟩

theorem silentDiv_of_coind {L : LTS E Res} (D : L.State → Prop)
    (hD : ∀ s, D s → ∃ s', L.step s none s' ∧ D s') {s : L.State} (hs : D s) :
    SilentDiv L s := by
  have hchoice : ∀ x : {s // D s}, ∃ y : {s // D s}, L.step x.1 none y.1 := by
    intro ⟨s, hs⟩
    obtain ⟨s', hstep, hs'⟩ := hD s hs
    exact ⟨⟨s', hs'⟩, hstep⟩
  obtain ⟨next, hnext⟩ := Classical.axiomOfChoice hchoice
  let g : Nat → {s // D s} := fun n => Nat.rec ⟨s, hs⟩ (fun _ x => next x) n
  exact ⟨fun n => (g n).1, rfl, fun n => hnext (g n)⟩

/-- Target states that silently reach a state forward-related to some point
of the source run `f`. -/
def DivF {L₁ : LTS E Res} (L₂ : LTS E Res) {I : Type} (R : I → L₁.State → L₂.State → Prop)
    (f : Nat → L₁.State) (s₂ : L₂.State) : Prop :=
  ∃ n i s₂', Star L₂ s₂ [] s₂' ∧ R i (f n) s₂'

/-- Source states silently reachable from `s₁` that silently reach a state
backward-related to some point of the target run `g`. -/
def DivB (L₁ : LTS E Res) {L₂ : LTS E Res} {I : Type} (R : I → L₁.State → L₂.State → Prop)
    (g : Nat → L₂.State) (s₁ : L₁.State) (s : L₁.State) : Prop :=
  Star L₁ s₁ [] s ∧ ∃ n i sx, Star L₁ s [] sx ∧ R i sx (g n)

/-! ## Vertical composition -/

theorem star_sim₂ {L₂ L₃ : LTS E Res} {I₂ : Type} {ord₂ : I₂ → I₂ → Prop}
    {R₂ : I₂ → L₂.State → L₃.State → Prop}
    (h₂ : FSimStep L₂ L₃ ord₂ R₂) {s₂ s₂' : L₂.State} {t : List E}
    (hrun : Star L₂ s₂ t s₂') :
    ∀ i₂ s₃, R₂ i₂ s₂ s₃ → ∃ i₂' s₃', R₂ i₂' s₂' s₃' ∧
      (Plus L₃ s₃ t s₃' ∨
        (Star L₃ s₃ t s₃' ∧ (i₂' = i₂ ∨ Relation.TransGen ord₂ i₂' i₂))) := by
  induction hrun with
  | refl s => exact fun i₂ s₃ hR => ⟨i₂, s₃, hR, Or.inr ⟨Star.refl _, Or.inl rfl⟩⟩
  | @step _ _ _ e _ _ h _ ht ih =>
    intro i₂ s₃ hR
    obtain ⟨j, sy, hmove, hRj⟩ := h₂ i₂ _ s₃ e _ hR h
    obtain ⟨i₂', s₃', hR', hrest⟩ := ih j sy hRj
    refine ⟨i₂', s₃', hR', ?_⟩
    subst ht
    rcases hmove with hp | ⟨hs, hord⟩
    · left
      rcases hrest with hp' | ⟨hs', _⟩
      · exact Plus.trans_star hp hp'.star
      · exact Plus.trans_star hp hs'
    · rcases hrest with hp' | ⟨hs', hidx⟩
      · left; exact Star.trans_plus hs hp'
      · right
        refine ⟨hs.trans hs', Or.inr ?_⟩
        rcases hidx with rfl | htg
        · exact Relation.TransGen.single hord
        · exact Relation.TransGen.tail htg hord

theorem plus_sim₂ {L₂ L₃ : LTS E Res} {I₂ : Type} {ord₂ : I₂ → I₂ → Prop}
    {R₂ : I₂ → L₂.State → L₃.State → Prop}
    (h₂ : FSimStep L₂ L₃ ord₂ R₂) {s₂ s₂' : L₂.State} {t : List E}
    (hp : Plus L₂ s₂ t s₂') {i₂ : I₂} {s₃ : L₃.State} (hR : R₂ i₂ s₂ s₃) :
    ∃ i₂' s₃', R₂ i₂' s₂' s₃' ∧
      (Plus L₃ s₃ t s₃' ∨ (Star L₃ s₃ t s₃' ∧ Relation.TransGen ord₂ i₂' i₂)) := by
  obtain ⟨e, sx, t₁, hstep, hstar, rfl⟩ := hp
  obtain ⟨j, sy, hmove, hRj⟩ := h₂ i₂ _ s₃ e _ hR hstep
  obtain ⟨i₂', s₃', hR', hrest⟩ := star_sim₂ h₂ hstar j sy hRj
  refine ⟨i₂', s₃', hR', ?_⟩
  rcases hmove with hp | ⟨hs, hord⟩
  · left
    rcases hrest with hp' | ⟨hs', _⟩
    · exact Plus.trans_star hp hp'.star
    · exact Plus.trans_star hp hs'
  · rcases hrest with hp' | ⟨hs', hidx⟩
    · left; exact Star.trans_plus hs hp'
    · right
      refine ⟨hs.trans hs', ?_⟩
      rcases hidx with rfl | htg
      · exact Relation.TransGen.single hord
      · exact Relation.TransGen.tail htg hord

/-! ## Backward simulation of runs -/

theorem Safe.star {L : LTS E Res} {s s' : L.State} (h : Safe L s) (hs : Star L s [] s') :
    Safe L s' := by
  intro s'' hs'
  exact h s'' (by simpa using hs.trans hs')

theorem exists_stuck_of_not_safe {L : LTS E Res} {s : L.State} (h : ¬ Safe L s) :
    ∃ s', Star L s [] s' ∧ Stuck L s' := by
  apply Classical.byContradiction
  intro hn
  apply h
  intro s' hs
  apply Classical.byContradiction
  intro hn'
  apply hn
  refine ⟨s', hs, ?_, ?_⟩
  · intro e s'' hstep; exact hn' (Or.inr ⟨e, s'', hstep⟩)
  · intro r hr; exact hn' (Or.inl ⟨r, hr⟩)

theorem bsim_star {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hsim : IsBackwardSim L₁ L₂ ord R) {s₂ s₂' : L₂.State} {t : List E}
    (hrun : Star L₂ s₂ t s₂') :
    ∀ i s₁, R i s₁ s₂ →
      (∃ i' s₁', Star L₁ s₁ t s₁' ∧ R i' s₁' s₂') ∨
      (∃ t₁ s₁', t₁ <+: t ∧ Star L₁ s₁ t₁ s₁' ∧ Stuck L₁ s₁') := by
  induction hrun with
  | refl s => exact fun i s₁ hR => Or.inl ⟨i, s₁, Star.refl _, hR⟩
  | @step _ _ _ e _ _ h _ ht ih =>
    intro i s₁ hR
    subst ht
    by_cases hsafe : Safe L₁ s₁
    · obtain ⟨i', s₁x, hmove, hR'⟩ := hsim.step i s₁ _ e _ hR hsafe h
      have hstar : Star L₁ s₁ (obs e) s₁x := by
        rcases hmove with hp | ⟨hs, _⟩
        · exact hp.star
        · exact hs
      rcases ih i' s₁x hR' with ⟨i'', s₁', hstar', hR''⟩ | ⟨t₁, s₁', hpre, hstar', hstuck⟩
      · exact Or.inl ⟨i'', s₁', hstar.trans hstar', hR''⟩
      · refine Or.inr ⟨obs e ++ t₁, s₁', ?_, hstar.trans hstar', hstuck⟩
        obtain ⟨u, rfl⟩ := hpre
        exact ⟨u, by simp [List.append_assoc]⟩
    · obtain ⟨s₁', hstar, hstuck⟩ := exists_stuck_of_not_safe hsafe
      exact Or.inr ⟨[], s₁', List.nil_prefix, hstar, hstuck⟩

theorem bsim_diverge {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hsim : IsBackwardSim L₁ L₂ ord R) {i : I} {s₁ : L₁.State} {s₂ : L₂.State}
    (hR : R i s₁ s₂) (hdiv : SilentDiv L₂ s₂)
    (hsafeAll : ∀ s, Star L₁ s₁ [] s → Safe L₁ s) : SilentDiv L₁ s₁ := by
  obtain ⟨g, hg0, hg⟩ := hdiv
  have stepOf : ∀ {s sx : L₁.State} {n : Nat} {i : I}, Star L₁ s₁ [] s → Plus L₁ s [] sx →
      R i sx (g n) → ∃ s', L₁.step s none s' ∧ DivB L₁ R g s₁ s' := by
    intro s sx n i hreach hp hR
    obtain ⟨e, s₃, t', hs, hstar, ht⟩ := hp
    obtain ⟨rfl, rfl⟩ := obs_append_eq_nil ht
    exact ⟨s₃, hs, by simpa using hreach.trans (Star.single hs), n, i, sx, hstar, hR⟩
  have claimA : ∀ i, ∀ n sx, Star L₁ s₁ [] sx → R i sx (g n) →
      ∃ s', L₁.step sx none s' ∧ DivB L₁ R g s₁ s' := by
    intro i
    induction i using hsim.wf.induction with
    | _ i ih =>
      intro n sx hreach hR
      obtain ⟨i', sy, hmove, hR'⟩ :=
        hsim.step i sx (g n) none (g (n+1)) hR (hsafeAll sx hreach) (hg n)
      rcases hmove with hp | ⟨hs, hord⟩
      · exact stepOf hreach hp hR'
      · rcases hs.plus_or_refl with hp | ⟨_, hEq⟩
        · exact stepOf hreach hp hR'
        · exact ih i' hord (n+1) sx hreach (hEq ▸ hR')
  have claimB : ∀ s, DivB L₁ R g s₁ s → ∃ s', L₁.step s none s' ∧ DivB L₁ R g s₁ s' := by
    intro s ⟨hreach, n, i, sx, hstar, hR⟩
    rcases hstar.plus_or_refl with hp | ⟨_, hEq⟩
    · exact stepOf hreach hp hR
    · exact claimA i n s hreach (hEq ▸ hR)
  exact silentDiv_of_coind (DivB L₁ R g s₁) claimB
    ⟨Star.refl _, 0, i, s₁, Star.refl _, by rw [hg0]; exact hR⟩

/-! ## Flip lemma: the backward relation -/

/-- `Star` with an explicit step count. -/
inductive StarN (L : LTS E Res) : Nat → L.State → List E → L.State → Prop where
  | refl (s : L.State) : StarN L 0 s [] s
  | step {n : Nat} {s s' s'' : L.State} {e : Option E} {t t' : List E}
      (h : L.step s e s') (hs : StarN L n s' t s'') (ht : t' = obs e ++ t) :
      StarN L (n+1) s t' s''

theorem StarN.star {L : LTS E Res} {n : Nat} {s s' : L.State} {t : List E}
    (h : StarN L n s t s') : Star L s t s' := by
  induction h with
  | refl s => exact Star.refl s
  | step h _ ht ih => exact Star.step h ih ht

theorem starN_of_star {L : LTS E Res} {s s' : L.State} {t : List E}
    (h : Star L s t s') : ∃ n, StarN L n s t s' := by
  induction h with
  | refl s => exact ⟨0, StarN.refl s⟩
  | step h _ ht ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n+1, StarN.step h hn ht⟩

/-- Index of the backward simulation built by the flip lemma. -/
inductive FIdx where
  | before (n : Nat)
  | after (n : Nat)

/-- Order on `FIdx`: `<` within each kind, and every `before` below every
`after`. -/
inductive FOrd : FIdx → FIdx → Prop where
  | before {n' n : Nat} : n' < n → FOrd (.before n') (.before n)
  | after {n' n : Nat} : n' < n → FOrd (.after n') (.after n)
  | switch {n' n : Nat} : FOrd (.before n') (.after n)

theorem FOrd.wf : WellFounded FOrd := by
  have accB : ∀ n, Acc FOrd (.before n) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      constructor
      intro y hy
      cases hy with
      | before h => exact ih _ h
  have accA : ∀ n, Acc FOrd (.after n) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      constructor
      intro y hy
      cases hy with
      | after h => exact ih _ h
      | switch => exact accB _
  exact ⟨fun a => by
    cases a with
    | before n => exact accB n
    | after n => exact accA n⟩

/-- The backward relation built by the flip lemma from a forward relation
`R`. -/
inductive FRel (L₁ L₂ : LTS E Res) {I : Type} (R : I → L₁.State → L₂.State → Prop) :
    FIdx → L₁.State → L₂.State → Prop where
  | after {n : Nat} {i : I} {s₁ : L₁.State} {s₂ s₂a : L₂.State} :
      StarN L₂ n s₂ [] s₂a → R i s₁ s₂a → FRel L₁ L₂ R (.after n) s₁ s₂
  | before {n : Nat} {i : I} {s₁ : L₁.State} {a : E} {s₁' : L₁.State} {s₂b s₂ s₂a : L₂.State} :
      L₁.step s₁ (some a) s₁' → R i s₁ s₂b → Star L₂ s₂b [] s₂ → StarN L₂ n s₂ [a] s₂a →
      FRel L₁ L₂ R (.before n) s₁ s₂

section Flip
variable {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
  {R : I → L₁.State → L₂.State → Prop} {M : E → E → Prop}

theorem det_silent (hdet : Determinate M L₂) {s s' s'' : L₂.State} {e : Option E}
    (h₁ : L₂.step s none s') (h₂ : L₂.step s e s'') : e = none ∧ s'' = s' := by
  have hl := hdet.labels s none s' e s'' h₁ h₂
  cases e with
  | none => exact ⟨rfl, hdet.functional s none s'' s' h₂ h₁⟩
  | some a => exact hl.elim

theorem det_event (hdet : Determinate M L₂) {s s' s'' : L₂.State} {a : E} {e : Option E}
    (h₁ : L₂.step s (some a) s') (h₂ : L₂.step s e s'') : ∃ b, e = some b ∧ M a b := by
  have hl := hdet.labels s (some a) s' e s'' h₁ h₂
  cases e with
  | none => exact hl.elim
  | some b => exact ⟨b, rfl, hl⟩

theorem det_star_event_aux (hdet : Determinate M L₂) {s s' : L₂.State} {t : List E}
    (hsil : Star L₂ s t s') (ht : t = []) :
    ∀ {b : E} {s'' sc : L₂.State}, L₂.step s' (some b) s'' → Star L₂ s [b] sc →
      Star L₂ s'' [] sc := by
  induction hsil with
  | refl s =>
    intro b s'' sc hstep hrun
    rcases hrun.inv with ⟨h, _⟩ | ⟨e, sx, t', hs, hrest, htr⟩
    · cases h
    · obtain ⟨c, rfl, _⟩ := det_event hdet hstep hs
      have hbc : b = c ∧ t' = [] := by
        simp only [obs_some, List.singleton_append, List.cons.injEq] at htr
        exact ⟨htr.1, htr.2.symm⟩
      obtain ⟨rfl, rfl⟩ := hbc
      have hEq := hdet.functional _ _ _ _ hstep hs
      exact hEq ▸ hrest
  | @step s₀ s₁ s₂ e t₁ t₂ h hs' ht' ih =>
    intro b s'' sc hstep hrun
    rw [ht] at ht'
    obtain ⟨he, ht₁⟩ := obs_append_eq_nil ht'
    subst he
    rcases hrun.inv with ⟨h', _⟩ | ⟨e', sx, t', hs₁, hrest, htr⟩
    · cases h'
    · obtain ⟨he', hsx⟩ := det_silent hdet h hs₁
      subst he'
      have htr' : [b] = t' := by simpa using htr
      subst htr'
      exact ih ht₁ hstep (hsx ▸ hrest)

theorem det_star_event (hdet : Determinate M L₂) {s s' : L₂.State}
    (hsil : Star L₂ s [] s') {b : E} {s'' sc : L₂.State}
    (hstep : L₂.step s' (some b) s'') (hrun : Star L₂ s [b] sc) : Star L₂ s'' [] sc :=
  det_star_event_aux hdet hsil rfl hstep hrun

/-- From a forward-related pair whose source state is safe, the source
silently reaches a forward-related state that is either final (and then so is
the target, with the same result) or takes a step matched by at least one
target step. -/
theorem f2b_trans (hsim : IsForwardSim L₁ L₂ ord R) :
    ∀ i s₁ s₂, R i s₁ s₂ → Safe L₁ s₁ →
      (∃ s₁a j r, Star L₁ s₁ [] s₁a ∧ R j s₁a s₂ ∧ L₁.final s₁a r ∧ L₂.final s₂ r) ∨
      (∃ s₁a j e s₁b i' s₂a, Star L₁ s₁ [] s₁a ∧ R j s₁a s₂ ∧ L₁.step s₁a e s₁b ∧
          Plus L₂ s₂ (obs e) s₂a ∧ R i' s₁b s₂a) := by
  intro i
  induction i using hsim.wf.induction with
  | _ i ih =>
    intro s₁ s₂ hR hsafe
    rcases hsafe s₁ (Star.refl _) with ⟨r, hr⟩ | ⟨e, s₁x, hstep⟩
    · exact Or.inl ⟨s₁, i, r, Star.refl _, hR, hr, hsim.final i s₁ s₂ r hR hr⟩
    · obtain ⟨i', s₂', hmove, hR'⟩ := hsim.step i s₁ s₂ e s₁x hR hstep
      rcases hmove with hp | ⟨hs, hord⟩
      · exact Or.inr ⟨s₁, i, e, s₁x, i', s₂', Star.refl _, hR, hstep, hp, hR'⟩
      · rcases hs.plus_or_refl with hp | ⟨he, hEq⟩
        · exact Or.inr ⟨s₁, i, e, s₁x, i', s₂', Star.refl _, hR, hstep, hp, hR'⟩
        · have he' : e = none := obs_eq_nil.1 he
          subst he'
          have hstar1 : Star L₁ s₁ [] s₁x := Star.single hstep
          have hsafe' : Safe L₁ s₁x := Safe.star hsafe hstar1
          rcases ih i' hord s₁x s₂ (hEq ▸ hR') hsafe' with
            ⟨s₁a, j, r, hst, hRj, hf₁, hf₂⟩ | ⟨s₁a, j, e, s₁b, i'', s₂a, hst, hRj, hstp, hp, hR''⟩
          · exact Or.inl ⟨s₁a, j, r, by simpa using hstar1.trans hst, hRj, hf₁, hf₂⟩
          · exact Or.inr ⟨s₁a, j, e, s₁b, i'', s₂a, by simpa using hstar1.trans hst, hRj,
              hstp, hp, hR''⟩

end Flip

end Toy.Sim.ProofAux
