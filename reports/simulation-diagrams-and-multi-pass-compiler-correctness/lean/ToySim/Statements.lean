import ToySim.ProofAux

/-!
# Main results

Statements and proofs of the main results.  Five core results
(`fsimInit_fsimStep_partial_run_simulated`,
`wf_fsimInit_fsimStep_preserve_diverges`, `fsimStep_comp`,
`forwardSim_receptive_determinate_gives_backwardSim`,
`backwardSim_gives_refinedBy`) are proved directly, using the auxiliary
lemmas of `ToySim.ProofAux`; every other theorem in this file is derived from
them (or proved outright), which shows how the statements fit together.

Reading guide: `L₁` is always the source side and `L₂` the target side of a
single pass.
-/

namespace Toy.Sim

variable {E Res : Type}

/-! ## 1. Forward simulation preserves behaviours -/

/-- **Partial runs are simulated (no well-foundedness, no final clause).**
With the forward initial-state clause and the forward step diagram, every
finite partial run of the source from an initial state `s₀` is matched by a
run of the target, with the same trace, from an initial target state `s₀'`
that is related to `s₀`, ending in a state related to the end of the source
run.

This is all a forward simulation says about a source run that then goes
wrong: the target can reach a related state with the same trace, and nothing
is claimed about what the target does afterwards. -/
theorem fsimInit_fsimStep_partial_run_simulated
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hinit : FSimInit L₁ L₂ R) (hstep : FSimStep L₁ L₂ ord R)
    {s₀ s : L₁.State} {t : List E} (h₀ : L₁.init s₀) (hrun : Star L₁ s₀ t s) :
    ∃ i₀ i s₀' s', L₂.init s₀' ∧ R i₀ s₀ s₀' ∧ Star L₂ s₀' t s' ∧ R i s s' := by
  obtain ⟨i, s₂, h₂, hR⟩ := hinit s₀ h₀
  obtain ⟨i', s₂', hstar, hR'⟩ := ProofAux.fsim_star hstep hrun i s₂ hR
  exact ⟨i, i', s₂, s₂', h₂, hR, hstar, hR'⟩

/-- **Terminating behaviours are preserved (no well-foundedness needed).**
With the three forward clauses, every terminating behaviour of the source is
a terminating behaviour of the target, with the same trace and result. -/
theorem fsimInit_fsimStep_fsimFinal_preserve_terminates
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hinit : FSimInit L₁ L₂ R) (hstep : FSimStep L₁ L₂ ord R)
    (hfinal : FSimFinal L₁ L₂ R)
    {t : List E} {r : Res} (hb : HasBehavior L₁ (.terminates t r)) :
    HasBehavior L₂ (.terminates t r) := by
  obtain ⟨s₀, s, h₀, hrun, hfin⟩ := hb
  obtain ⟨_, i, s₀', s', h₀', _, hrun', hR⟩ :=
    fsimInit_fsimStep_partial_run_simulated hinit hstep h₀ hrun
  exact ⟨s₀', s', h₀', hrun', hfinal i s s' r hR hfin⟩

/-- **Silently diverging behaviours are preserved when the index order is
well-founded (no final clause needed).**  With a well-founded index order,
the forward initial-state clause and the forward step diagram, every
behaviour "emit `t`, then diverge silently" of the source is a behaviour of
the target. -/
theorem wf_fsimInit_fsimStep_preserve_diverges
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hwf : WellFounded ord)
    (hinit : FSimInit L₁ L₂ R) (hstep : FSimStep L₁ L₂ ord R)
    {t : List E} (hb : HasBehavior L₁ (.diverges t)) :
    HasBehavior L₂ (.diverges t) := by
  obtain ⟨s₀, s, h₀, hrun, f, hf0, hf⟩ := hb
  obtain ⟨_, i, s₀', s', h₀', _, hrun', hR⟩ :=
    fsimInit_fsimStep_partial_run_simulated hinit hstep h₀ hrun
  refine ⟨s₀', s', h₀', hrun', ?_⟩
  -- Every target state that silently reaches a state related to some point
  -- `f n` of the source's silent run has a silent successor with the same
  -- property; by well-founded induction on the index, a related state cannot
  -- stutter forever.
  have stepOf : ∀ {s₂ s₂' : L₂.State} {n : Nat} {i : I}, Plus L₂ s₂ [] s₂' → R i (f n) s₂' →
      ∃ s₂'', L₂.step s₂ none s₂'' ∧ ProofAux.DivF L₂ R f s₂'' := by
    intro s₂ s₂' n i hp hR
    obtain ⟨e, s₃, t', hs, hstar, ht⟩ := hp
    obtain ⟨rfl, rfl⟩ := ProofAux.obs_append_eq_nil ht
    exact ⟨s₃, hs, n, i, s₂', hstar, hR⟩
  have claimA : ∀ i, ∀ n s₂', R i (f n) s₂' →
      ∃ s₂'', L₂.step s₂' none s₂'' ∧ ProofAux.DivF L₂ R f s₂'' := by
    intro i
    induction i using hwf.induction with
    | _ i ih =>
      intro n s₂' hR
      obtain ⟨i', s₂x, hmove, hR'⟩ := hstep i (f n) s₂' none (f (n+1)) hR (hf n)
      rcases hmove with hp | ⟨hs, hord⟩
      · exact stepOf hp hR'
      · rcases hs.plus_or_refl with hp | ⟨_, hEq⟩
        · exact stepOf hp hR'
        · exact ih i' hord (n+1) s₂' (hEq ▸ hR')
  have claimB : ∀ s₂, ProofAux.DivF L₂ R f s₂ →
      ∃ s₂'', L₂.step s₂ none s₂'' ∧ ProofAux.DivF L₂ R f s₂'' := by
    intro s₂ ⟨n, i, s₂', hstar, hR⟩
    rcases hstar.plus_or_refl with hp | ⟨_, hEq⟩
    · exact stepOf hp hR
    · exact claimA i n s₂ (hEq ▸ hR)
  exact ProofAux.silentDiv_of_coind (ProofAux.DivF L₂ R f) claimB
    ⟨0, i, s', Star.refl _, by rw [hf0]; exact hR⟩

/-- Bundled form: a forward simulation preserves every behaviour of the
source that is not a going-wrong behaviour. -/
theorem isForwardSim_preserves_non_goesWrong_behaviors
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hsim : IsForwardSim L₁ L₂ ord R)
    {b : Behavior E Res} (hb : HasBehavior L₁ b) (hnw : ∀ t, b ≠ .goesWrong t) :
    HasBehavior L₂ b := by
  cases b with
  | terminates t r =>
    exact fsimInit_fsimStep_fsimFinal_preserve_terminates hsim.init hsim.step hsim.final hb
  | diverges t =>
    exact wf_fsimInit_fsimStep_preserve_diverges hsim.wf hsim.init hsim.step hb
  | goesWrong t => exact absurd rfl (hnw t)

/-! ## 2. Vertical composition -/

/-- The forward initial-state clause composes. -/
theorem fsimInit_comp {L₁ L₂ L₃ : LTS E Res} {I₁ I₂ : Type}
    {R₁ : I₁ → L₁.State → L₂.State → Prop} {R₂ : I₂ → L₂.State → L₃.State → Prop}
    (h₁ : FSimInit L₁ L₂ R₁) (h₂ : FSimInit L₂ L₃ R₂) :
    FSimInit L₁ L₃ (compRel R₁ R₂) := by
  intro s₁ hs₁
  obtain ⟨i₁, s₂, hs₂, hR₁⟩ := h₁ s₁ hs₁
  obtain ⟨i₂, s₃, hs₃, hR₂⟩ := h₂ s₂ hs₂
  exact ⟨(i₂, i₁), s₃, hs₃, s₂, hR₁, hR₂⟩

/-- The forward final-state clause composes. -/
theorem fsimFinal_comp {L₁ L₂ L₃ : LTS E Res} {I₁ I₂ : Type}
    {R₁ : I₁ → L₁.State → L₂.State → Prop} {R₂ : I₂ → L₂.State → L₃.State → Prop}
    (h₁ : FSimFinal L₁ L₂ R₁) (h₂ : FSimFinal L₂ L₃ R₂) :
    FSimFinal L₁ L₃ (compRel R₁ R₂) := by
  intro i s₁ s₃ r hR hfin
  obtain ⟨s₂, hR₁, hR₂⟩ := hR
  exact h₂ _ s₂ s₃ r hR₂ (h₁ _ s₁ s₂ r hR₁ hfin)

/-- The composite index order is well-founded when both orders are. -/
theorem compOrd_wf {I₁ I₂ : Type} {ord₁ : I₁ → I₁ → Prop} {ord₂ : I₂ → I₂ → Prop}
    (h₁ : WellFounded ord₁) (h₂ : WellFounded ord₂) :
    WellFounded (compOrd ord₁ ord₂) := by
  have hlex : WellFounded (Prod.Lex (Relation.TransGen ord₂) ord₁) :=
    (Prod.lex ⟨_, h₂.transGen⟩ ⟨_, h₁⟩).wf
  refine Subrelation.wf (r := Prod.Lex (Relation.TransGen ord₂) ord₁) ?_ hlex
  intro p q h
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  rcases h with h | ⟨heq, h⟩
  · exact Prod.Lex.left _ _ h
  · have heq' : p1 = q1 := heq
    subst heq'
    exact Prod.Lex.right _ h

/-- **Step diagrams compose (no well-foundedness needed).**  If `R₁` satisfies
the forward step diagram from `L₁` to `L₂` with index order `ord₁`, and `R₂`
satisfies it from `L₂` to `L₃` with `ord₂`, then the relational composite
`compRel R₁ R₂` satisfies the forward step diagram from `L₁` to `L₃` with the
lexicographic order `compOrd ord₁ ord₂`. -/
theorem fsimStep_comp {L₁ L₂ L₃ : LTS E Res} {I₁ I₂ : Type}
    {ord₁ : I₁ → I₁ → Prop} {ord₂ : I₂ → I₂ → Prop}
    {R₁ : I₁ → L₁.State → L₂.State → Prop} {R₂ : I₂ → L₂.State → L₃.State → Prop}
    (h₁ : FSimStep L₁ L₂ ord₁ R₁) (h₂ : FSimStep L₂ L₃ ord₂ R₂) :
    FSimStep L₁ L₃ (compOrd ord₁ ord₂) (compRel R₁ R₂) := by
  intro i s₁ s₃ e s₁' hR hstep
  obtain ⟨s₂, hR₁, hR₂⟩ := hR
  obtain ⟨i₁', s₂', hmove, hR₁'⟩ := h₁ i.2 s₁ s₂ e s₁' hR₁ hstep
  -- If the first pass makes at least one middle step, the second pass
  -- simulates the whole middle run (index decreasing in `TransGen ord₂` if it
  -- stutters throughout).
  have viaPlus : Plus L₂ s₂ (obs e) s₂' →
      ∃ i' s₃', (Plus L₃ s₃ (obs e) s₃' ∨
        (Star L₃ s₃ (obs e) s₃' ∧ compOrd ord₁ ord₂ i' i)) ∧ compRel R₁ R₂ i' s₁' s₃' := by
    intro hp
    obtain ⟨i₂', s₃', hR₂', hrest⟩ := ProofAux.plus_sim₂ h₂ hp hR₂
    refine ⟨(i₂', i₁'), s₃', ?_, s₂', hR₁', hR₂'⟩
    rcases hrest with hp' | ⟨hs', htg⟩
    · exact Or.inl hp'
    · exact Or.inr ⟨hs', Or.inl htg⟩
  rcases hmove with hp | ⟨hs, hord⟩
  · exact viaPlus hp
  · rcases hs.plus_or_refl with hp | ⟨he, hs₂⟩
    · exact viaPlus hp
    · -- The first pass stutters with zero middle steps: keep the second
      -- index and decrease the first.
      subst hs₂
      refine ⟨(i.1, i₁'), s₃, Or.inr ⟨?_, Or.inr ⟨rfl, hord⟩⟩, _, hR₁', hR₂⟩
      rw [he]; exact Star.refl _

/-- **Vertical composition of forward simulations**, with the composite
relation and order exposed: `compRel R₁ R₂` with `compOrd ord₁ ord₂`. -/
theorem isForwardSim_comp {L₁ L₂ L₃ : LTS E Res} {I₁ I₂ : Type}
    {ord₁ : I₁ → I₁ → Prop} {ord₂ : I₂ → I₂ → Prop}
    {R₁ : I₁ → L₁.State → L₂.State → Prop} {R₂ : I₂ → L₂.State → L₃.State → Prop}
    (h₁ : IsForwardSim L₁ L₂ ord₁ R₁) (h₂ : IsForwardSim L₂ L₃ ord₂ R₂) :
    IsForwardSim L₁ L₃ (compOrd ord₁ ord₂) (compRel R₁ R₂) where
  wf := compOrd_wf h₁.wf h₂.wf
  init := fsimInit_comp h₁.init h₂.init
  final := fsimFinal_comp h₁.final h₂.final
  step := fsimStep_comp h₁.step h₂.step

/-! ## 3. Flipping a forward simulation into a backward simulation -/

/-- **Flip lemma.**  A forward simulation from a source that is receptive to a
target that is determinate (both with respect to the same event-matching
relation `M`) yields a backward simulation between the same two systems,
whose relation contains every pair related by the forward simulation.

The backward relation itself is not exposed: only its existence and the fact
that it extends the forward relation are claimed. -/
theorem forwardSim_receptive_determinate_gives_backwardSim
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop} (M : E → E → Prop)
    (hsim : IsForwardSim L₁ L₂ ord R)
    (hrec : Receptive M L₁) (hdet : Determinate M L₂) :
    ∃ (I' : Type) (ord' : I' → I' → Prop) (R' : I' → L₁.State → L₂.State → Prop),
      IsBackwardSim L₁ L₂ ord' R' ∧ ∀ i s₁ s₂, R i s₁ s₂ → ∃ i', R' i' s₁ s₂ := by
  -- The backward relation is `ProofAux.FRel L₁ L₂ R` with index order
  -- `ProofAux.FOrd`: a source state is related to every target state on the
  -- (deterministic) silent path towards a forward-related target state, and,
  -- when the source can emit an event, to every target state on the path to
  -- the matching target emission.
  refine ⟨ProofAux.FIdx, ProofAux.FOrd, ProofAux.FRel L₁ L₂ R,
    ⟨ProofAux.FOrd.wf, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- initExists
    rintro ⟨s₁, hs₁⟩
    obtain ⟨i, s₂, hs₂, _⟩ := hsim.init s₁ hs₁
    exact ⟨s₂, hs₂⟩
  · -- initMatch
    intro s₁ s₂ hs₁ hs₂
    obtain ⟨i, s₂', hs₂', hR⟩ := hsim.init s₁ hs₁
    have hEq := hdet.init s₂' s₂ hs₂' hs₂
    exact ⟨.after 0, s₁, hs₁, ProofAux.FRel.after (ProofAux.StarN.refl _) (hEq ▸ hR)⟩
  · -- final
    intro idx s₁ s₂ r hrel hsafe hfin
    cases hrel with
    | @after n i _ _ s₂a hN hR =>
      cases hN with
      | refl =>
        rcases ProofAux.f2b_trans hsim i s₁ s₂ hR hsafe with
          ⟨s₁a, j, r', hst, _, hf₁, hf₂⟩ | ⟨s₁a, j, e, s₁b, i', s₂a', _, _, _, hp, _⟩
        · have hEq := hdet.finalDet s₂ r r' hfin hf₂
          exact ⟨s₁a, hst, hEq ▸ hf₁⟩
        · obtain ⟨e₀, sx, _, hs, _, _⟩ := hp
          exact absurd hs (hdet.finalNoStep s₂ r hfin e₀ sx)
      | step hs _ _ => exact absurd hs (hdet.finalNoStep s₂ r hfin _ _)
    | @before n i _ a s₁' s₂b _ s₂a hstep hR hsil hN =>
      cases hN with
      | step hs _ _ => exact absurd hs (hdet.finalNoStep s₂ r hfin _ _)
  · -- progress
    intro idx s₁ s₂ hrel hsafe
    cases hrel with
    | @after n i _ _ s₂a hN hR =>
      cases hN with
      | refl =>
        rcases ProofAux.f2b_trans hsim i s₁ s₂ hR hsafe with
          ⟨_, _, r', _, _, _, hf₂⟩ | ⟨_, _, e, _, _, _, _, _, _, hp, _⟩
        · exact Or.inl ⟨r', hf₂⟩
        · obtain ⟨e₀, sx, _, hs, _, _⟩ := hp
          exact Or.inr ⟨e₀, sx, hs⟩
      | step hs _ _ => exact Or.inr ⟨_, _, hs⟩
    | @before n i _ a s₁' s₂b _ s₂a hstep hR hsil hN =>
      cases hN with
      | step hs _ _ => exact Or.inr ⟨_, _, hs⟩
  · -- step
    intro idx s₁ s₂ e'' s₂'' hrel hsafe htgt
    cases hrel with
    | @after n i _ _ s₂a hN hR =>
      cases hN with
      | refl =>
        rcases ProofAux.f2b_trans hsim i s₁ s₂ hR hsafe with
          ⟨_, _, r', _, _, _, hf₂⟩ | ⟨s₁a, j, e, s₁b, i', s₂a', hst, hRj, hstp, hp, hR'⟩
        · exact absurd htgt (hdet.finalNoStep s₂ r' hf₂ e'' s₂'')
        · obtain ⟨e₀, sx, t', hs, hrest, htr⟩ := hp
          cases e₀ with
          | none =>
            obtain ⟨he'', hsx⟩ := ProofAux.det_silent hdet hs htgt
            subst he''
            have htr' : obs e = t' := by simpa using htr
            subst htr'
            have hrest' : Star L₂ s₂'' (obs e) s₂a' := hsx ▸ hrest
            cases e with
            | none =>
              obtain ⟨m, hm⟩ := ProofAux.starN_of_star hrest'
              exact ⟨.after m, s₁b,
                Or.inl (by simpa using ProofAux.Star.trans_plus hst (Plus.single hstp)),
                ProofAux.FRel.after hm hR'⟩
            | some a =>
              obtain ⟨m, hm⟩ := ProofAux.starN_of_star hrest'
              exact ⟨.before m, s₁a, Or.inr ⟨hst, ProofAux.FOrd.switch⟩,
                ProofAux.FRel.before hstp hRj (Star.single htgt) hm⟩
          | some c =>
            have hec : e = some c ∧ t' = [] := by
              cases e with
              | none => simp [obs] at htr
              | some a =>
                simp only [obs_some, List.singleton_append, List.cons.injEq] at htr
                exact ⟨by rw [htr.1], htr.2.symm⟩
            obtain ⟨he, ht'⟩ := hec
            subst he
            obtain ⟨b, he'', hM⟩ := ProofAux.det_event hdet hs htgt
            subst he''
            obtain ⟨s₁c, hstpb⟩ := hrec s₁a c s₁b b hstp hM
            obtain ⟨i'', s₂c, hmove, hR''⟩ := hsim.step j s₁a s₂ (some b) s₁c hRj hstpb
            have hrun : Star L₂ s₂ [b] s₂c := by
              rcases hmove with hp | ⟨hs', _⟩
              · exact hp.star
              · exact hs'
            have hsil := ProofAux.det_star_event hdet (Star.refl s₂) htgt hrun
            obtain ⟨m, hm⟩ := ProofAux.starN_of_star hsil
            exact ⟨.after m, s₁c,
              Or.inl (by simpa using ProofAux.Star.trans_plus hst (Plus.single hstpb)),
              ProofAux.FRel.after hm hR''⟩
      | @step m _ sx _ e₀ t' _ hs hrest htr =>
        obtain ⟨he₀, ht'⟩ := ProofAux.obs_append_eq_nil htr
        subst he₀ ht'
        obtain ⟨he'', hsx⟩ := ProofAux.det_silent hdet hs htgt
        subst he''
        exact ⟨.after m, s₁, Or.inr ⟨Star.refl _, ProofAux.FOrd.after (Nat.lt_succ_self m)⟩,
          ProofAux.FRel.after (hsx ▸ hrest) hR⟩
    | @before n i _ a s₁' s₂b _ s₂a hstep hR hsil hN =>
      cases hN with
      | @step m _ sx _ e₀ t' _ hs hrest htr =>
        cases e₀ with
        | none =>
          have htr' : [a] = t' := by simpa using htr
          subst htr'
          obtain ⟨he'', hsx⟩ := ProofAux.det_silent hdet hs htgt
          subst he''
          exact ⟨.before m, s₁, Or.inr ⟨Star.refl _, ProofAux.FOrd.before (Nat.lt_succ_self m)⟩,
            ProofAux.FRel.before hstep hR (by simpa using hsil.trans (Star.single htgt))
              (hsx ▸ hrest)⟩
        | some c =>
          have hca : a = c ∧ t' = [] := by
            simp only [obs_some, List.singleton_append, List.cons.injEq] at htr
            exact ⟨htr.1, htr.2.symm⟩
          obtain ⟨hac, ht'⟩ := hca
          subst hac
          obtain ⟨b, he'', hM⟩ := ProofAux.det_event hdet hs htgt
          subst he''
          obtain ⟨s₁c, hstpb⟩ := hrec s₁ a s₁' b hstep hM
          obtain ⟨i'', s₂c, hmove, hR''⟩ := hsim.step i s₁ s₂b (some b) s₁c hR hstpb
          have hrun : Star L₂ s₂b [b] s₂c := by
            rcases hmove with hp | ⟨hs', _⟩
            · exact hp.star
            · exact hs'
          have hsil' := ProofAux.det_star_event hdet hsil htgt hrun
          obtain ⟨m', hm'⟩ := ProofAux.starN_of_star hsil'
          exact ⟨.after m', s₁c, Or.inl (Plus.single hstpb), ProofAux.FRel.after hm' hR''⟩
  · intro i s₁ s₂ hR
    exact ⟨.after 0, ProofAux.FRel.after (ProofAux.StarN.refl _) hR⟩

/-- **Flip lemma, deterministic target.**  Special case `M = Eq`: every
source is receptive, and `Determinate Eq L₂` says that `L₂` is deterministic
outright. -/
theorem forwardSim_deterministic_target_gives_backwardSim
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hsim : IsForwardSim L₁ L₂ ord R) (hdet : Determinate Eq L₂) :
    ∃ (I' : Type) (ord' : I' → I' → Prop) (R' : I' → L₁.State → L₂.State → Prop),
      IsBackwardSim L₁ L₂ ord' R' ∧ ∀ i s₁ s₂, R i s₁ s₂ → ∃ i', R' i' s₁ s₂ :=
  forwardSim_receptive_determinate_gives_backwardSim Eq hsim (receptive_eq L₁) hdet

/-! ## 4. Backward simulation gives refinement -/

/-- **A backward simulation gives behaviour refinement.**  If there is a
backward simulation from `L₁` to `L₂`, then every behaviour of `L₂` improves
on some behaviour of `L₁`. -/
theorem backwardSim_gives_refinedBy
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hsim : IsBackwardSim L₁ L₂ ord R) : RefinedBy L₁ L₂ := by
  intro b₂ hb₂
  by_cases hinit : ∃ s₁, L₁.init s₁
  case neg =>
    -- No initial source state: the source has behaviour `goesWrong []`,
    -- which permits everything.
    exact ⟨.goesWrong [], Or.inr ⟨rfl, fun s hs => hinit ⟨s, hs⟩⟩, improves_goesWrong_nil b₂⟩
  obtain ⟨s₁i, hs₁i⟩ := hinit
  -- A target run from an initial state is simulated by a source run from an
  -- initial state, or the source goes wrong after a prefix of its trace.
  have run : ∀ {s₂z s₂ : L₂.State} {t : List E}, L₂.init s₂z → Star L₂ s₂z t s₂ →
      (∃ s₁z i' s₁', L₁.init s₁z ∧ Star L₁ s₁z t s₁' ∧ R i' s₁' s₂) ∨
      (∃ t₁, t₁ <+: t ∧ HasBehavior L₁ (.goesWrong t₁)) := by
    intro s₂z s₂ t h₀ hrun
    obtain ⟨i, s₁z, hs₁z, hR⟩ := hsim.initMatch s₁i s₂z hs₁i h₀
    rcases ProofAux.bsim_star hsim hrun i s₁z hR with
      ⟨i', s₁', hstar, hR'⟩ | ⟨t₁, s₁', hpre, hstar, hstuck⟩
    · exact Or.inl ⟨s₁z, i', s₁', hs₁z, hstar, hR'⟩
    · exact Or.inr ⟨t₁, hpre, Or.inl ⟨s₁z, s₁', hs₁z, hstar, hstuck⟩⟩
  have wrongAt : ∀ {s₁z s₁' : L₁.State} {t : List E}, L₁.init s₁z → Star L₁ s₁z t s₁' →
      ¬ Safe L₁ s₁' → HasBehavior L₁ (.goesWrong t) := by
    intro s₁z s₁' t h₀ hstar hns
    obtain ⟨s₁'', hstar', hstuck⟩ := ProofAux.exists_stuck_of_not_safe hns
    exact Or.inl ⟨s₁z, s₁'', h₀, by simpa using hstar.trans hstar', hstuck⟩
  cases b₂ with
  | terminates t r =>
    obtain ⟨s₂z, s₂, h₀, hrun, hfin⟩ := hb₂
    rcases run h₀ hrun with ⟨s₁z, i', s₁', hs₁z, hstar, hR'⟩ | ⟨t₁, hpre, hw⟩
    · by_cases hsafe : Safe L₁ s₁'
      · obtain ⟨s₁'', hstar', hfin'⟩ := hsim.final i' s₁' s₂ r hR' hsafe hfin
        exact ⟨.terminates t r,
          ⟨s₁z, s₁'', hs₁z, by simpa using hstar.trans hstar', hfin'⟩, Improves.refl _⟩
      · exact ⟨.goesWrong t, wrongAt hs₁z hstar hsafe, Or.inr ⟨t, rfl, List.prefix_refl t⟩⟩
    · exact ⟨.goesWrong t₁, hw, Or.inr ⟨t₁, rfl, hpre⟩⟩
  | diverges t =>
    obtain ⟨s₂z, s₂, h₀, hrun, hdiv⟩ := hb₂
    rcases run h₀ hrun with ⟨s₁z, i', s₁', hs₁z, hstar, hR'⟩ | ⟨t₁, hpre, hw⟩
    · by_cases hstk : ∃ s, Star L₁ s₁' [] s ∧ Stuck L₁ s
      · obtain ⟨s, hstar', hstuck⟩ := hstk
        exact ⟨.goesWrong t,
          Or.inl ⟨s₁z, s, hs₁z, by simpa using hstar.trans hstar', hstuck⟩,
          Or.inr ⟨t, rfl, List.prefix_refl t⟩⟩
      · have hsafeAll : ∀ s, Star L₁ s₁' [] s → Safe L₁ s := by
          intro s hs
          apply Classical.byContradiction
          intro hns
          obtain ⟨s', hs', hstuck⟩ := ProofAux.exists_stuck_of_not_safe hns
          exact hstk ⟨s', by simpa using hs.trans hs', hstuck⟩
        exact ⟨.diverges t,
          ⟨s₁z, s₁', hs₁z, hstar, ProofAux.bsim_diverge hsim hR' hdiv hsafeAll⟩,
          Improves.refl _⟩
    · exact ⟨.goesWrong t₁, hw, Or.inr ⟨t₁, rfl, hpre⟩⟩
  | goesWrong t =>
    rcases hb₂ with ⟨s₂z, s₂, h₀, hrun, hstuck⟩ | ⟨rfl, hno⟩
    · rcases run h₀ hrun with ⟨s₁z, i', s₁', hs₁z, hstar, hR'⟩ | ⟨t₁, hpre, hw⟩
      · by_cases hsafe : Safe L₁ s₁'
        · rcases hsim.progress i' s₁' s₂ hR' hsafe with ⟨r, hr⟩ | ⟨e, s₂', hs⟩
          · exact absurd hr (hstuck.2 r)
          · exact absurd hs (hstuck.1 e s₂')
        · exact ⟨.goesWrong t, wrongAt hs₁z hstar hsafe, Improves.refl _⟩
      · exact ⟨.goesWrong t₁, hw, Or.inr ⟨t₁, rfl, hpre⟩⟩
    · obtain ⟨s₂, hs₂⟩ := hsim.initExists ⟨s₁i, hs₁i⟩
      exact absurd hs₂ (hno s₂)

/-- For a source that never goes wrong, a backward simulation gives behaviour
inclusion: every target behaviour is a source behaviour. -/
theorem backwardSim_neverGoesWrong_behaviors_subset
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hsim : IsBackwardSim L₁ L₂ ord R) (hsafe : NeverGoesWrong L₁)
    {b : Behavior E Res} (hb : HasBehavior L₂ b) : HasBehavior L₁ b :=
  refinedBy_neverGoesWrong_behaviors_subset (backwardSim_gives_refinedBy hsim) hsafe hb

/-! ## 5. End-to-end correctness of a pipeline -/

/-- A chain of forward simulations collapses to a single forward simulation
between its endpoints. -/
theorem fsimChain_collapse {L L' : LTS E Res} (h : FSimChain L L') :
    ∃ (I : Type) (ord : I → I → Prop) (R : I → L.State → L'.State → Prop),
      IsForwardSim L L' ord R := by
  induction h with
  | nil L => exact ⟨Unit, _, _, isForwardSim_id L⟩
  | cons ord R hsim _ ih =>
    obtain ⟨I', ord', R', h'⟩ := ih
    exact ⟨_, _, _, isForwardSim_comp hsim h'⟩

/-- **End-to-end refinement for a pipeline.**  If every pass of a pipeline
from `L` to `L'` has a forward simulation, the *first* language `L` is
receptive and the *last* language `L'` is determinate (with respect to the
same event-matching relation `M`), then `L'` refines `L`.  Nothing is assumed
about the intermediate languages. -/
theorem fsimChain_receptive_first_determinate_last_gives_refinedBy
    {L L' : LTS E Res} (M : E → E → Prop)
    (hchain : FSimChain L L') (hrec : Receptive M L) (hdet : Determinate M L') :
    RefinedBy L L' := by
  obtain ⟨I, ord, R, hf⟩ := fsimChain_collapse hchain
  obtain ⟨I', ord', R', hb, _⟩ :=
    forwardSim_receptive_determinate_gives_backwardSim M hf hrec hdet
  exact backwardSim_gives_refinedBy hb

/-- **End-to-end refinement, deterministic last language.**  Special case
`M = Eq`: no receptiveness hypothesis is needed. -/
theorem fsimChain_deterministic_last_gives_refinedBy
    {L L' : LTS E Res} (hchain : FSimChain L L') (hdet : Determinate Eq L') :
    RefinedBy L L' :=
  fsimChain_receptive_first_determinate_last_gives_refinedBy Eq hchain (receptive_eq L) hdet

/-- A pipeline of forward simulations preserves every behaviour of the first
language that is not a going-wrong behaviour (no receptiveness or determinacy
needed for this direction). -/
theorem fsimChain_preserves_non_goesWrong_behaviors {L L' : LTS E Res}
    (hchain : FSimChain L L')
    {b : Behavior E Res} (hb : HasBehavior L b) (hnw : ∀ t, b ≠ .goesWrong t) :
    HasBehavior L' b := by
  induction hchain with
  | nil L => exact hb
  | cons ord R hsim _ ih =>
    exact ih (isForwardSim_preserves_non_goesWrong_behaviors hsim hb hnw)

/-- **End-to-end behaviour equality when the first language never goes
wrong.**  If every pass of a pipeline from `L` to `L'` has a forward
simulation, the first language `L` is receptive and the last language `L'` is
determinate (for the same event-matching relation `M`), and `L` has no
going-wrong behaviour, then `L` and `L'` have exactly the same behaviours. -/
theorem fsimChain_receptive_first_determinate_last_neverGoesWrong_first_behaviors_iff
    {L L' : LTS E Res} (M : E → E → Prop)
    (hchain : FSimChain L L') (hrec : Receptive M L) (hdet : Determinate M L')
    (hsafe : NeverGoesWrong L) (b : Behavior E Res) :
    HasBehavior L' b ↔ HasBehavior L b := by
  constructor
  · intro hb
    exact refinedBy_neverGoesWrong_behaviors_subset
      (fsimChain_receptive_first_determinate_last_gives_refinedBy M hchain hrec hdet) hsafe hb
  · intro hb
    refine fsimChain_preserves_non_goesWrong_behaviors hchain hb ?_
    intro t ht
    subst ht
    exact hsafe t hb

end Toy.Sim
