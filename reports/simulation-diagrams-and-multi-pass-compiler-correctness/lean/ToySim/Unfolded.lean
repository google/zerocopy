import ToySim.Statements

/-!
# Main statements with the named clauses unfolded

Each theorem here is a theorem of `ToySim.Statements` in which the named
simulation, receptiveness, determinacy, safety and refinement clauses are
replaced by their definitions.  Each is obtained from the corresponding theorem by
unfolding definitions only, so the two forms say the same thing.  They are
meant for reading.
-/

namespace Toy.Sim.Unfolded
open Toy.Sim

variable {E Res : Type}

/-- `fsimInit_fsimStep_partial_run_simulated`, unfolded. -/
theorem partial_run_simulated
    (L₁ L₂ : LTS E Res) (I : Type) (ord : I → I → Prop)
    (R : I → L₁.State → L₂.State → Prop)
    (hinit : ∀ s₁, L₁.init s₁ → ∃ i s₂, L₂.init s₂ ∧ R i s₁ s₂)
    (hstep : ∀ i s₁ s₂ e s₁', R i s₁ s₂ → L₁.step s₁ e s₁' →
      ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord i' i)) ∧
        R i' s₁' s₂')
    (s₀ s : L₁.State) (t : List E) (h₀ : L₁.init s₀) (hrun : Star L₁ s₀ t s) :
    ∃ i₀ i s₀' s', L₂.init s₀' ∧ R i₀ s₀ s₀' ∧ Star L₂ s₀' t s' ∧ R i s s' :=
  fsimInit_fsimStep_partial_run_simulated hinit hstep h₀ hrun

/-- `fsimInit_fsimStep_fsimFinal_preserve_terminates`, unfolded. -/
theorem terminating_behaviours_preserved
    (L₁ L₂ : LTS E Res) (I : Type) (ord : I → I → Prop)
    (R : I → L₁.State → L₂.State → Prop)
    (hinit : ∀ s₁, L₁.init s₁ → ∃ i s₂, L₂.init s₂ ∧ R i s₁ s₂)
    (hstep : ∀ i s₁ s₂ e s₁', R i s₁ s₂ → L₁.step s₁ e s₁' →
      ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord i' i)) ∧
        R i' s₁' s₂')
    (hfinal : ∀ i s₁ s₂ r, R i s₁ s₂ → L₁.final s₁ r → L₂.final s₂ r)
    (t : List E) (r : Res)
    (hb : ∃ s₀ s, L₁.init s₀ ∧ Star L₁ s₀ t s ∧ L₁.final s r) :
    ∃ s₀' s', L₂.init s₀' ∧ Star L₂ s₀' t s' ∧ L₂.final s' r :=
  fsimInit_fsimStep_fsimFinal_preserve_terminates hinit hstep hfinal hb

/-- `wf_fsimInit_fsimStep_preserve_diverges`, unfolded. -/
theorem silent_divergence_preserved
    (L₁ L₂ : LTS E Res) (I : Type) (ord : I → I → Prop)
    (R : I → L₁.State → L₂.State → Prop)
    (hwf : WellFounded ord)
    (hinit : ∀ s₁, L₁.init s₁ → ∃ i s₂, L₂.init s₂ ∧ R i s₁ s₂)
    (hstep : ∀ i s₁ s₂ e s₁', R i s₁ s₂ → L₁.step s₁ e s₁' →
      ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord i' i)) ∧
        R i' s₁' s₂')
    (t : List E)
    (hb : ∃ s₀ s, L₁.init s₀ ∧ Star L₁ s₀ t s ∧
      ∃ f : Nat → L₁.State, f 0 = s ∧ ∀ n, L₁.step (f n) none (f (n + 1))) :
    ∃ s₀' s', L₂.init s₀' ∧ Star L₂ s₀' t s' ∧
      ∃ g : Nat → L₂.State, g 0 = s' ∧ ∀ n, L₂.step (g n) none (g (n + 1)) :=
  wf_fsimInit_fsimStep_preserve_diverges hwf hinit hstep hb

/-- `fsimStep_comp`, unfolded (including the composite relation and order). -/
theorem step_diagrams_compose
    (L₁ L₂ L₃ : LTS E Res) (I₁ I₂ : Type)
    (ord₁ : I₁ → I₁ → Prop) (ord₂ : I₂ → I₂ → Prop)
    (R₁ : I₁ → L₁.State → L₂.State → Prop) (R₂ : I₂ → L₂.State → L₃.State → Prop)
    (h₁ : ∀ i s₁ s₂ e s₁', R₁ i s₁ s₂ → L₁.step s₁ e s₁' →
      ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord₁ i' i)) ∧
        R₁ i' s₁' s₂')
    (h₂ : ∀ i s₂ s₃ e s₂', R₂ i s₂ s₃ → L₂.step s₂ e s₂' →
      ∃ i' s₃', (Plus L₃ s₃ (obs e) s₃' ∨ (Star L₃ s₃ (obs e) s₃' ∧ ord₂ i' i)) ∧
        R₂ i' s₂' s₃') :
    ∀ (i : I₂ × I₁) (s₁ : L₁.State) (s₃ : L₃.State) (e : Option E) (s₁' : L₁.State),
      (∃ s₂, R₁ i.2 s₁ s₂ ∧ R₂ i.1 s₂ s₃) → L₁.step s₁ e s₁' →
      ∃ (i' : I₂ × I₁) (s₃' : L₃.State),
        (Plus L₃ s₃ (obs e) s₃' ∨
          (Star L₃ s₃ (obs e) s₃' ∧
            (Relation.TransGen ord₂ i'.1 i.1 ∨ (i'.1 = i.1 ∧ ord₁ i'.2 i.2)))) ∧
        ∃ s₂', R₁ i'.2 s₁' s₂' ∧ R₂ i'.1 s₂' s₃' :=
  fsimStep_comp h₁ h₂

/-- `forwardSim_receptive_determinate_gives_backwardSim`, unfolded. -/
theorem flip_forward_to_backward
    (M : E → E → Prop) (L₁ L₂ : LTS E Res) (I : Type) (ord : I → I → Prop)
    (R : I → L₁.State → L₂.State → Prop)
    -- forward simulation
    (hwf : WellFounded ord)
    (hinit : ∀ s₁, L₁.init s₁ → ∃ i s₂, L₂.init s₂ ∧ R i s₁ s₂)
    (hfinal : ∀ i s₁ s₂ r, R i s₁ s₂ → L₁.final s₁ r → L₂.final s₂ r)
    (hstep : ∀ i s₁ s₂ e s₁', R i s₁ s₂ → L₁.step s₁ e s₁' →
      ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord i' i)) ∧
        R i' s₁' s₂')
    -- receptive source
    (hrec : ∀ s a s₁ b, L₁.step s (some a) s₁ → M a b → ∃ s₂, L₁.step s (some b) s₂)
    -- determinate target
    (hlabels : ∀ s e₁ s₁ e₂ s₂, L₂.step s e₁ s₁ → L₂.step s e₂ s₂ → LabelMatch M e₁ e₂)
    (hfunctional : ∀ s e s₁ s₂, L₂.step s e s₁ → L₂.step s e s₂ → s₁ = s₂)
    (hinitDet : ∀ s s', L₂.init s → L₂.init s' → s = s')
    (hfinalNoStep : ∀ s r, L₂.final s r → ∀ e s', ¬ L₂.step s e s')
    (hfinalDet : ∀ s r r', L₂.final s r → L₂.final s r' → r = r') :
    ∃ (I' : Type) (ord' : I' → I' → Prop) (R' : I' → L₁.State → L₂.State → Prop),
      -- backward simulation, clause by clause
      WellFounded ord' ∧
      ((∃ s₁, L₁.init s₁) → ∃ s₂, L₂.init s₂) ∧
      (∀ s₁ s₂, L₁.init s₁ → L₂.init s₂ → ∃ i s₁', L₁.init s₁' ∧ R' i s₁' s₂) ∧
      -- (`Safe L₁ s₁` is unfolded: `s₁` cannot get stuck before its next event)
      (∀ i s₁ s₂ r, R' i s₁ s₂ →
        (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
        L₂.final s₂ r → ∃ s₁', Star L₁ s₁ [] s₁' ∧ L₁.final s₁' r) ∧
      (∀ i s₁ s₂, R' i s₁ s₂ →
        (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
        (∃ r, L₂.final s₂ r) ∨ (∃ e s₂', L₂.step s₂ e s₂')) ∧
      (∀ i s₁ s₂ e s₂', R' i s₁ s₂ →
        (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
        L₂.step s₂ e s₂' →
        ∃ i' s₁', (Plus L₁ s₁ (obs e) s₁' ∨ (Star L₁ s₁ (obs e) s₁' ∧ ord' i' i)) ∧
          R' i' s₁' s₂') ∧
      -- the backward relation contains the forward relation
      (∀ i s₁ s₂, R i s₁ s₂ → ∃ i', R' i' s₁ s₂) := by
  obtain ⟨I', ord', R', hb, hext⟩ :=
    forwardSim_receptive_determinate_gives_backwardSim M
      (IsForwardSim.mk hwf hinit hfinal hstep) hrec
      (Determinate.mk hlabels hfunctional hinitDet hfinalNoStep hfinalDet)
  exact ⟨I', ord', R', hb.wf, hb.initExists, hb.initMatch, hb.final, hb.progress, hb.step,
    hext⟩

/-- `backwardSim_gives_refinedBy`, unfolded. -/
theorem backward_sim_gives_refinement
    (L₁ L₂ : LTS E Res) (I : Type) (ord : I → I → Prop)
    (R : I → L₁.State → L₂.State → Prop)
    (hwf : WellFounded ord)
    (hinitExists : (∃ s₁, L₁.init s₁) → ∃ s₂, L₂.init s₂)
    (hinitMatch : ∀ s₁ s₂, L₁.init s₁ → L₂.init s₂ → ∃ i s₁', L₁.init s₁' ∧ R i s₁' s₂)
    -- (`Safe L₁ s₁` is unfolded: `s₁` cannot get stuck before its next event)
    (hfinal : ∀ i s₁ s₂ r, R i s₁ s₂ →
      (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
      L₂.final s₂ r → ∃ s₁', Star L₁ s₁ [] s₁' ∧ L₁.final s₁' r)
    (hprogress : ∀ i s₁ s₂, R i s₁ s₂ →
      (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
      (∃ r, L₂.final s₂ r) ∨ (∃ e s₂', L₂.step s₂ e s₂'))
    (hstep : ∀ i s₁ s₂ e s₂', R i s₁ s₂ →
      (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
      L₂.step s₂ e s₂' →
      ∃ i' s₁', (Plus L₁ s₁ (obs e) s₁' ∨ (Star L₁ s₁ (obs e) s₁' ∧ ord i' i)) ∧
        R i' s₁' s₂') :
    ∀ b₂, HasBehavior L₂ b₂ →
      ∃ b₁, HasBehavior L₁ b₁ ∧ (b₁ = b₂ ∨ ∃ t, b₁ = .goesWrong t ∧ t <+: b₂.trace) :=
  backwardSim_gives_refinedBy (IsBackwardSim.mk hwf hinitExists hinitMatch hfinal hprogress hstep)

/-- `fsimChain_receptive_first_determinate_last_gives_refinedBy`, unfolded. -/
theorem pipeline_end_to_end_refinement
    (M : E → E → Prop) (L L' : LTS E Res)
    (hchain : FSimChain L L')
    -- the first language is receptive
    (hrec : ∀ s a s₁ b, L.step s (some a) s₁ → M a b → ∃ s₂, L.step s (some b) s₂)
    -- the last language is determinate
    (hlabels : ∀ s e₁ s₁ e₂ s₂, L'.step s e₁ s₁ → L'.step s e₂ s₂ → LabelMatch M e₁ e₂)
    (hfunctional : ∀ s e s₁ s₂, L'.step s e s₁ → L'.step s e s₂ → s₁ = s₂)
    (hinitDet : ∀ s s', L'.init s → L'.init s' → s = s')
    (hfinalNoStep : ∀ s r, L'.final s r → ∀ e s', ¬ L'.step s e s')
    (hfinalDet : ∀ s r r', L'.final s r → L'.final s r' → r = r') :
    ∀ b', HasBehavior L' b' →
      ∃ b, HasBehavior L b ∧ (b = b' ∨ ∃ t, b = .goesWrong t ∧ t <+: b'.trace) :=
  fsimChain_receptive_first_determinate_last_gives_refinedBy M hchain hrec
    (Determinate.mk hlabels hfunctional hinitDet hfinalNoStep hfinalDet)

end Toy.Sim.Unfolded
