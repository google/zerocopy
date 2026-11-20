import ToyGhost.Congruence

/-!
# Results 1 and 2: erasure soundness, graded by restriction, and its tightness

Throughout, `P` is the original program (with ghost code), `erase P` the erased
program, `σ` the initial store of `P` and `τ` an initial store of `erase P` with the
same real part (its ghost part is arbitrary). The restrictions are
R1 `GhostWritesGhost P`, R2 `RealReadsReal P`, R3a `GhostNoDivergeFrom P σ`,
R3b `GhostNoFailFrom P σ`.

Direction: in every refinement statement the *erased* program is the concrete side
and the *original* is the abstract side: every real behaviour of `erase P` is a real
behaviour of `P`, unless `P` has a behaviour in the stated bottom set.
-/

namespace Toy.Ghost

/-! ## Simulation lemmas used by Result 1 -/

/-- Executing a statement satisfying `WritesOnlyGhost` preserves `realPart`. -/
theorem writesOnlyGhost_preserves_realPart {n : Nat} :
    ∀ {s : Stmt} {σ σ' : Store},
      WritesOnlyGhost s → run n s σ = some (.ok σ') → realPart σ' = realPart σ := by
  induction n with
  | zero => intro s σ σ' _ h; simp [run] at h
  | succ n ih =>
    intro s σ σ' hw h
    cases s with
    | skip => simp [run] at h; subst h; rfl
    | assign v e =>
      cases v with
      | real _ => exact hw.elim
      | ghost j => simp [run] at h; subst h; exact realPart_update_ghost σ j (e.eval σ)
    | assert e =>
      simp only [run] at h
      split at h
      · cases h
      · cases h; rfl
    | seq s t =>
      simp only [run] at h
      rcases Outcome.bind_eq_some h with ⟨σ1, h1, h2⟩ | ⟨_, h2⟩
      · exact (ih hw.2 h2).trans (ih hw.1 h1)
      · cases h2
    | ite c s t =>
      simp only [run] at h
      split at h
      · exact ih hw.2 h
      · exact ih hw.1 h
    | loop c b =>
      simp only [run] at h
      split at h
      · cases h; rfl
      · rcases Outcome.bind_eq_some h with ⟨σ1, h1, h2⟩ | ⟨_, h2⟩
        · exact (ih (s := .loop c b) hw h2).trans (ih (s := b) hw h1)
        · cases h2
    | ghost s => exact ih (s := s) hw h

/-- Lockstep fuel simulation (used for 1.A–1.C): a terminating run of `P` in fuel `n` is matched by a
terminating run of `erase P` in the same fuel `n` with equal final `realPart`. -/
theorem run_erase_ok_of_run_ok {n : Nat} :
    ∀ {P : Stmt} {σ σ' τ : Store},
      GhostWritesGhost P → RealReadsReal P → realPart σ = realPart τ →
      run n P σ = some (.ok σ') →
      ∃ τ', run n (erase P) τ = some (.ok τ') ∧ realPart σ' = realPart τ' := by
  induction n with
  | zero => intro P σ σ' τ _ _ _ h; simp [run] at h
  | succ n ih =>
    intro P σ σ' τ hW hR hστ h
    cases P with
    | skip =>
      simp [run] at h; subst h
      exact ⟨τ, rfl, hστ⟩
    | assign v e =>
      cases v with
      | real i =>
        simp [run] at h; subst h
        refine ⟨τ.update (.real i) (e.eval τ), rfl, ?_⟩
        rw [← Expr.eval_congr_of_readsOnlyReal hR hστ]
        exact realPart_update_congr hστ (.real i) (e.eval σ)
      | ghost j =>
        simp [run] at h; subst h
        exact ⟨τ, rfl, (realPart_update_ghost σ j (e.eval σ)).trans hστ⟩
    | assert e =>
      have hev := Expr.eval_congr_of_readsOnlyReal hR hστ
      simp only [run] at h
      split at h
      · cases h
      · rename_i hne
        cases h
        have hne' : ¬ e.eval τ = 0 := hev ▸ hne
        exact ⟨τ, by simp [erase, run, hne'], hστ⟩
    | seq s t =>
      simp only [run] at h
      rcases Outcome.bind_eq_some h with ⟨σ1, h1, h2⟩ | ⟨_, h2⟩
      · obtain ⟨τ1, ht1, hr1⟩ := ih hW.1 hR.1 hστ h1
        obtain ⟨τ2, ht2, hr2⟩ := ih hW.2 hR.2 hr1 h2
        exact ⟨τ2, by simp [erase, run, ht1, ht2, Outcome.bind], hr2⟩
      · cases h2
    | ite c s t =>
      have hcev := Expr.eval_congr_of_readsOnlyReal hR.1 hστ
      simp only [run] at h
      split at h
      · rename_i hc
        have hc' : c.eval τ = 0 := hcev ▸ hc
        obtain ⟨τ', ht', hr'⟩ := ih hW.2 hR.2.2 hστ h
        exact ⟨τ', by simp [erase, run, hc', ht'], hr'⟩
      · rename_i hc
        have hc' : ¬ c.eval τ = 0 := hcev ▸ hc
        obtain ⟨τ', ht', hr'⟩ := ih hW.1 hR.2.1 hστ h
        exact ⟨τ', by simp [erase, run, hc', ht'], hr'⟩
    | loop c b =>
      have hcev := Expr.eval_congr_of_readsOnlyReal hR.1 hστ
      simp only [run] at h
      split at h
      · rename_i hc
        cases h
        have hc' : c.eval τ = 0 := hcev ▸ hc
        exact ⟨τ, by simp [erase, run, hc'], hστ⟩
      · rename_i hc
        have hc' : ¬ c.eval τ = 0 := hcev ▸ hc
        rcases Outcome.bind_eq_some h with ⟨σ1, h1, h2⟩ | ⟨_, h2⟩
        · obtain ⟨τ1, ht1, hr1⟩ := ih (P := b) hW hR.2 hστ h1
          obtain ⟨τ2, ht2, hr2⟩ := ih (P := .loop c b) hW hR hr1 h2
          exact ⟨τ2, by simp [erase, run, hc', ht1, Outcome.bind]; exact ht2, hr2⟩
        · cases h2
    | ghost s =>
      have hr := writesOnlyGhost_preserves_realPart hW h
      exact ⟨τ, rfl, hr.trans hστ⟩

/-- Anti-monotonicity of `GhostReach` in fuel: fewer steps reach a subset of ghost blocks. -/
theorem ghostReach_pred_of_succ {Q : Stmt → Store → Prop} :
    ∀ {n : Nat} {P : Stmt} {σ : Store}, GhostReach Q (n + 1) P σ → GhostReach Q n P σ
  | 0, _, _, _ => trivial
  | n + 1, .skip, _, _ => trivial
  | n + 1, .assign _ _, _, _ => trivial
  | n + 1, .assert _, _, _ => trivial
  | n + 1, .ghost _, _, h => h
  | n + 1, .seq s t, σ, h =>
      ⟨ghostReach_pred_of_succ h.1,
        fun σ' hs => ghostReach_pred_of_succ (h.2 σ' (run_succ_of_eq_some hs))⟩
  | n + 1, .ite c s t, σ, h => by
      simp only [GhostReach] at h ⊢
      split at h <;> simp_all [ghostReach_pred_of_succ]
  | n + 1, .loop c b, σ, h => by
      simp only [GhostReach] at h ⊢
      split at h
      · rename_i hc; simp [hc]
      · rename_i hc; simp only [hc, ↓reduceIte]
        exact ⟨ghostReach_pred_of_succ h.1,
          fun σ' hb => ghostReach_pred_of_succ (h.2 σ' (run_succ_of_eq_some hb))⟩

theorem ghostReach_anti {Q : Stmt → Store → Prop} {n m : Nat} (hnm : n ≤ m)
    {P : Stmt} {σ : Store} (h : GhostReach Q m P σ) : GhostReach Q n P σ := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact ih (ghostReach_pred_of_succ h)

/-- Backward termination/failure simulation (used for 1.B): if `erase P` finishes (either `.ok` or `.fail`)
in fuel `m`, and `P` satisfies R1, R2, R3a from `σ`, then `P` finishes from `σ` (does not diverge). -/
theorem exists_run_of_erase_finishes {m : Nat} :
    ∀ {P : Stmt} {σ τ : Store} {o : Outcome},
      GhostWritesGhost P → RealReadsReal P → realPart σ = realPart τ →
      GhostNoDivergeFrom P σ →
      run m (erase P) τ = some o →
      ∃ N o', run N P σ = some o' := by
  induction m with
  | zero => intro P σ τ o _ _ _ _ h; simp [run] at h
  | succ m ih =>
    intro P σ τ o hW hR hστ hT h
    cases P with
    | skip => exact ⟨1, .ok σ, rfl⟩
    | assign x e => exact ⟨1, .ok (σ.update x (e.eval σ)), rfl⟩
    | assert e =>
      by_cases he : e.eval σ = 0
      · exact ⟨1, .fail, by simp [run, he]⟩
      · exact ⟨1, .ok σ, by simp [run, he]⟩
    | ghost s =>
      have hnd : ¬ Diverges s σ := hT 1
      obtain ⟨b, hb⟩ := Behaves.exists s σ
      cases b with
      | term σ' =>
        obtain ⟨K, hK⟩ := hb
        exact ⟨K + 1, .ok σ', hK⟩
      | fail =>
        obtain ⟨K, hK⟩ := hb
        exact ⟨K + 1, .fail, hK⟩
      | diverge => exact (hnd hb).elim
    | seq s t =>
      have hTs : GhostNoDivergeFrom s σ := fun n => (hT (n + 1)).1
      simp only [erase, run] at h
      rcases Outcome.bind_eq_some h with ⟨τ1, h1, h2⟩ | ⟨h1, _⟩
      · obtain ⟨N1, o1, ho1⟩ := ih hW.1 hR.1 hστ hTs h1
        cases o1 with
        | fail => exact ⟨N1 + 1, .fail, by simp [run, ho1, Outcome.bind]⟩
        | ok σ1 =>
          obtain ⟨τ1', ht1', hr1⟩ := run_erase_ok_of_run_ok hW.1 hR.1 hστ ho1
          cases run_det h1 ht1'
          have hTt : GhostNoDivergeFrom t σ1 := fun n => by
            have hm := (hT (Nat.max N1 n + 1)).2 σ1 (run_mono ho1 (Nat.le_max_left N1 n))
            exact ghostReach_anti (Nat.le_max_right N1 n) hm
          obtain ⟨N2, o2, ho2⟩ := ih hW.2 hR.2 hr1 hTt h2
          refine ⟨Nat.max N1 N2 + 1, o2, ?_⟩
          simp [run, run_mono ho1 (Nat.le_max_left N1 N2),
            run_mono ho2 (Nat.le_max_right N1 N2), Outcome.bind]
      · obtain ⟨N1, o1, ho1⟩ := ih hW.1 hR.1 hστ hTs h1
        cases o1 with
        | fail => exact ⟨N1 + 1, .fail, by simp [run, ho1, Outcome.bind]⟩
        | ok σ1 =>
          obtain ⟨τ1', ht1', _⟩ := run_erase_ok_of_run_ok hW.1 hR.1 hστ ho1
          cases run_det h1 ht1'
    | ite c s t =>
      have hcev := Expr.eval_congr_of_readsOnlyReal hR.1 hστ
      simp only [erase, run] at h
      split at h
      · rename_i hc'
        have hc : c.eval σ = 0 := hcev.trans hc'
        have hTt : GhostNoDivergeFrom t σ := fun n => by
          have := hT (n + 1); simpa [GhostReach, hc] using this
        obtain ⟨N, o', ho'⟩ := ih hW.2 hR.2.2 hστ hTt h
        exact ⟨N + 1, o', by simp [run, hc, ho']⟩
      · rename_i hc'
        have hc : ¬ c.eval σ = 0 := fun h0 => hc' (hcev.symm.trans h0)
        have hTs : GhostNoDivergeFrom s σ := fun n => by
          have := hT (n + 1); simpa [GhostReach, hc] using this
        obtain ⟨N, o', ho'⟩ := ih hW.1 hR.2.1 hστ hTs h
        exact ⟨N + 1, o', by simp [run, hc, ho']⟩
    | loop c b =>
      have hcev := Expr.eval_congr_of_readsOnlyReal hR.1 hστ
      simp only [erase, run] at h
      split at h
      · rename_i hc'
        have hc : c.eval σ = 0 := hcev.trans hc'
        exact ⟨1, .ok σ, by simp [run, hc]⟩
      · rename_i hc'
        have hc : ¬ c.eval σ = 0 := fun h0 => hc' (hcev.symm.trans h0)
        have hTb : GhostNoDivergeFrom b σ := fun n => by
          have := hT (n + 1); simp only [GhostReach, hc, ↓reduceIte] at this; exact this.1
        rcases Outcome.bind_eq_some h with ⟨τ1, h1, h2⟩ | ⟨h1, _⟩
        · obtain ⟨N1, o1, ho1⟩ := ih (P := b) hW hR.2 hστ hTb h1
          cases o1 with
          | fail => exact ⟨N1 + 1, .fail, by simp [run, hc, ho1, Outcome.bind]⟩
          | ok σ1 =>
            obtain ⟨τ1', ht1', hr1⟩ := run_erase_ok_of_run_ok (P := b) hW hR.2 hστ ho1
            cases run_det h1 ht1'
            have hTl : GhostNoDivergeFrom (.loop c b) σ1 := fun n => by
              have hm := hT (Nat.max N1 n + 1)
              simp only [GhostReach, hc, ↓reduceIte] at hm
              exact ghostReach_anti (Nat.le_max_right N1 n)
                (hm.2 σ1 (run_mono ho1 (Nat.le_max_left N1 n)))
            obtain ⟨N2, o2, ho2⟩ := ih (P := .loop c b) hW hR hr1 hTl h2
            refine ⟨Nat.max N1 N2 + 1, o2, ?_⟩
            simp [run, hc, run_mono ho1 (Nat.le_max_left N1 N2),
              run_mono ho2 (Nat.le_max_right N1 N2), Outcome.bind]
        · obtain ⟨N1, o1, ho1⟩ := ih (P := b) hW hR.2 hστ hTb h1
          cases o1 with
          | fail => exact ⟨N1 + 1, .fail, by simp [run, hc, ho1, Outcome.bind]⟩
          | ok σ1 =>
            obtain ⟨τ1', ht1', _⟩ := run_erase_ok_of_run_ok (P := b) hW hR.2 hστ ho1
            cases run_det h1 ht1'

/-! Failure propagation through `seq` and `loop`. -/

theorem fails_seq_left {s t : Stmt} {σ : Store} (h : Fails s σ) : Fails (.seq s t) σ := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m + 1, by simp [run, hm, Outcome.bind]⟩

theorem fails_seq_right {s t : Stmt} {σ σ' : Store} {n : Nat} (hs : run n s σ = some (.ok σ'))
    (h : Fails t σ') : Fails (.seq s t) σ := by
  obtain ⟨m, hm⟩ := h
  refine ⟨Nat.max n m + 1, ?_⟩
  simp [run, run_mono hs (Nat.le_max_left n m), run_mono hm (Nat.le_max_right n m), Outcome.bind]

theorem fails_loop_body {c : Expr} {b : Stmt} {σ : Store} (hc : ¬ c.eval σ = 0)
    (h : Fails b σ) : Fails (.loop c b) σ := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m + 1, by simp [run, hc, hm, Outcome.bind]⟩

theorem fails_loop_next {c : Expr} {b : Stmt} {σ σ' : Store} {n : Nat} (hc : ¬ c.eval σ = 0)
    (hb : run n b σ = some (.ok σ')) (h : Fails (.loop c b) σ') : Fails (.loop c b) σ := by
  obtain ⟨m, hm⟩ := h
  refine ⟨Nat.max n m + 1, ?_⟩
  simp [run, hc, run_mono hb (Nat.le_max_left n m), run_mono hm (Nat.le_max_right n m),
    Outcome.bind]

/-- Forward failure simulation (used for 1.C): if `P` fails in fuel `n` and satisfies R1, R2, R3b from
`σ`, then `erase P` fails from `τ`. -/
theorem fails_erase_of_run_fail {n : Nat} :
    ∀ {P : Stmt} {σ τ : Store},
      GhostWritesGhost P → RealReadsReal P → realPart σ = realPart τ →
      GhostReach (fun g ρ => ¬ Fails g ρ) n P σ →
      run n P σ = some .fail →
      Fails (erase P) τ := by
  induction n with
  | zero => intro P σ τ _ _ _ _ h; simp [run] at h
  | succ n ih =>
    intro P σ τ hW hR hστ hF h
    cases P with
    | skip => simp [run] at h
    | assign _ _ => simp [run] at h
    | assert e =>
      have hev := Expr.eval_congr_of_readsOnlyReal hR hστ
      simp only [run] at h
      split at h
      · rename_i he0
        have he0' : e.eval τ = 0 := hev ▸ he0
        exact ⟨1, by simp [erase, run, he0']⟩
      · cases h
    | ghost s => exact (hF ⟨n, h⟩).elim
    | seq s t =>
      simp only [run] at h
      rcases Outcome.bind_eq_some h with ⟨σ1, h1, h2⟩ | ⟨h1, _⟩
      · obtain ⟨τ1, ht1, hr1⟩ := run_erase_ok_of_run_ok hW.1 hR.1 hστ h1
        exact fails_seq_right ht1 (ih hW.2 hR.2 hr1 (hF.2 σ1 h1) h2)
      · exact fails_seq_left (ih hW.1 hR.1 hστ hF.1 h1)
    | ite c s t =>
      have hcev := Expr.eval_congr_of_readsOnlyReal hR.1 hστ
      simp only [run] at h
      simp only [GhostReach] at hF
      split at h
      · rename_i hc
        simp only [hc, ↓reduceIte] at hF
        have hc' : c.eval τ = 0 := hcev ▸ hc
        obtain ⟨m, hm⟩ := ih hW.2 hR.2.2 hστ hF h
        exact ⟨m + 1, by simp [erase, run, hc', hm]⟩
      · rename_i hc
        simp only [hc, ↓reduceIte] at hF
        have hc' : ¬ c.eval τ = 0 := hcev ▸ hc
        obtain ⟨m, hm⟩ := ih hW.1 hR.2.1 hστ hF h
        exact ⟨m + 1, by simp [erase, run, hc', hm]⟩
    | loop c b =>
      have hcev := Expr.eval_congr_of_readsOnlyReal hR.1 hστ
      simp only [run] at h
      simp only [GhostReach] at hF
      split at h
      · cases h
      · rename_i hc
        simp only [hc, ↓reduceIte] at hF
        have hc' : ¬ c.eval τ = 0 := hcev ▸ hc
        rcases Outcome.bind_eq_some h with ⟨σ1, h1, h2⟩ | ⟨h1, _⟩
        · obtain ⟨τ1, ht1, hr1⟩ := run_erase_ok_of_run_ok (P := b) hW hR.2 hστ h1
          exact fails_loop_next hc' ht1
            (ih (P := .loop c b) hW hR hr1 (hF.2 σ1 h1) h2)
        · exact fails_loop_body hc' (ih (P := b) hW hR.2 hστ hF.1 h1)

/-! ## Result 1: erasure soundness, graded by restriction -/

/-- **1.A** Under R1 and R2 alone, `erase P` from `τ` refines `P` from `σ` up to
failure and divergence: if `P` terminates normally, `erase P` terminates normally
with the same final real store; if `P` fails or diverges, nothing is promised. -/
theorem erase_refinesUpTo_abortBot_of_ghostWritesGhost_of_realReadsReal
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    {σ τ : Store} (hστ : realPart σ = realPart τ) :
    RefinesUpTo abortBot P σ (erase P) τ := by
  rw [refinesUpTo_abortBot_iff]
  intro σ' ⟨n, hn⟩
  obtain ⟨τ', hτ', hr⟩ := run_erase_ok_of_run_ok hW hR hστ hn
  exact ⟨τ', ⟨n, hτ'⟩, hr.symm⟩

/-- **1.B** Adding R3a (no ghost block reached on the run of `P` from `σ` diverges),
`erase P` refines `P` up to failure only: unless `P` fails from `σ`, every real
behaviour of `erase P` from `τ` is one of `P` from `σ`. -/
theorem erase_refinesUpTo_failBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    {σ τ : Store} (hστ : realPart σ = realPart τ) (hT : GhostNoDivergeFrom P σ) :
    RefinesUpTo failBot P σ (erase P) τ := by
  obtain ⟨bp, hbp⟩ := Behaves.exists P σ
  cases bp with
  | term σ' =>
    right
    obtain ⟨m, hm⟩ := hbp
    obtain ⟨τ', hτ', hr⟩ := run_erase_ok_of_run_ok hW hR hστ hm
    intro b hb
    rw [(RBehaves.iff_of_behaves (b0 := .term τ') ⟨m, hτ'⟩ b).1 hb, Behaviour.real, ← hr]
    exact RBehaves.of_behaves (b := .term σ') ⟨m, hm⟩
  | fail =>
    exact Or.inl ⟨.fail, rfl, RBehaves.of_behaves hbp⟩
  | diverge =>
    right
    have hediv : Diverges (erase P) τ := by
      intro m
      match hm : run m (erase P) τ with
      | none => rfl
      | some o =>
        obtain ⟨N, o', hN⟩ := exists_run_of_erase_finishes hW hR hστ hT hm
        rw [hbp N] at hN
        cases hN
    intro b hb
    rw [(RBehaves.iff_of_behaves hediv b).1 hb]
    exact RBehaves.of_behaves hbp

/-- **1.C** Adding R3b (no ghost block reached on the run of `P` from `σ` fails),
`erase P` refines `P` up to divergence only: unless `P` diverges from `σ`, every real
behaviour of `erase P` from `τ` is one of `P` from `σ`. -/
theorem erase_refinesUpTo_divBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoFailFrom
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    {σ τ : Store} (hστ : realPart σ = realPart τ) (hF : GhostNoFailFrom P σ) :
    RefinesUpTo divBot P σ (erase P) τ := by
  obtain ⟨bp, hbp⟩ := Behaves.exists P σ
  cases bp with
  | term σ' =>
    right
    obtain ⟨n, hn⟩ := hbp
    obtain ⟨τ', hτ', hr⟩ := run_erase_ok_of_run_ok hW hR hστ hn
    intro b hb
    rw [(RBehaves.iff_of_behaves (b0 := .term τ') ⟨n, hτ'⟩ b).1 hb, Behaviour.real, ← hr]
    exact RBehaves.of_behaves (b := .term σ') ⟨n, hn⟩
  | fail =>
    right
    obtain ⟨n, hn⟩ := hbp
    have hefail := fails_erase_of_run_fail hW hR hστ (hF n) hn
    intro b hb
    rw [(RBehaves.iff_of_behaves hefail b).1 hb]
    exact RBehaves.of_behaves (b := .fail) ⟨n, hn⟩
  | diverge =>
    exact Or.inl ⟨.diverge, rfl, RBehaves.of_behaves hbp⟩

/-- **1.D** Under R1, R2, R3a, and R3b, `P` from `σ` and `erase P` from `τ` have
exactly the same real-observable behaviours (final real store, failure,
divergence). Derived from 1.B and 1.C. -/
theorem erase_rbehaves_iff_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    {σ τ : Store} (hστ : realPart σ = realPart τ)
    (hT : GhostNoDivergeFrom P σ) (hF : GhostNoFailFrom P σ) :
    ∀ b, RBehaves P σ b ↔ RBehaves (erase P) τ b :=
  rbehaves_iff_of_refinesUpTo_failBot_of_refinesUpTo_divBot
    (erase_refinesUpTo_failBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom hW hR hστ hT)
    (erase_refinesUpTo_divBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoFailFrom hW hR hστ hF)

/-- Global form of 1.D (a corollary): if R3a and R3b hold for runs from every
initial state, then `ErasureExact P`. -/
theorem erasureExact_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (hT : ∀ σ, GhostNoDivergeFrom P σ) (hF : ∀ σ, GhostNoFailFrom P σ) :
    ErasureExact P :=
  fun σ _ hστ =>
    erase_rbehaves_iff_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom
      hW hR hστ (hT σ) (hF σ)

/-! ## Facts about the counterexample programs (fully proved) -/

theorem ceGhostWritesReal_behaves (σ : Store) :
    Behaves ceGhostWritesReal σ (.term (σ.update x 1)) := ⟨2, rfl⟩

theorem ceImplicitFlow_behaves_σ0 :
    Behaves ceImplicitFlow σ0 (.term ((σ0.update g 1).update x 1)) := ⟨3, rfl⟩

theorem erase_ceImplicitFlow_behaves_σ0 : Behaves (erase ceImplicitFlow) σ0 (.term σ0) := ⟨3, rfl⟩

theorem realPart_ceImplicitFlow_ne : realPart ((σ0.update g 1).update x 1) ≠ realPart σ0 := by
  intro he
  have := congrFun he 0
  simp [realPart, Store.update, x, σ0] at this

theorem realPart_ceGhostWritesReal_ne : realPart (σ0.update x 1) ≠ realPart σ0 :=
  realPart_update_x_ne rfl

theorem ghostBlocksNoDiverge_ceGhostWritesReal : GhostBlocksNoDiverge ceGhostWritesReal :=
  fun σ => not_diverges_of_term (σ' := σ.update x 1) ⟨1, rfl⟩

theorem ghostBlocksNoFail_ceGhostWritesReal : GhostBlocksNoFail ceGhostWritesReal :=
  fun σ => not_fails_of_term (σ' := σ.update x 1) ⟨1, rfl⟩

theorem ghostWritesGhost_ceImplicitFlow : GhostWritesGhost ceImplicitFlow :=
  ⟨trivial, trivial, trivial⟩

theorem ghostBlocksNoDiverge_ceImplicitFlow : GhostBlocksNoDiverge ceImplicitFlow :=
  ⟨fun σ => not_diverges_of_term (σ' := σ.update g 1) ⟨1, rfl⟩, trivial, trivial⟩

theorem ghostBlocksNoFail_ceImplicitFlow : GhostBlocksNoFail ceImplicitFlow :=
  ⟨fun σ => not_fails_of_term (σ' := σ.update g 1) ⟨1, rfl⟩, trivial, trivial⟩

theorem ghostWritesGhost_ceGhostDiverges : GhostWritesGhost ceGhostDiverges := trivial
theorem realReadsReal_ceGhostDiverges : RealReadsReal ceGhostDiverges := trivial
theorem ghostBlocksNoFail_ceGhostDiverges : GhostBlocksNoFail ceGhostDiverges :=
  fun σ => spin_not_fails σ

theorem ghostWritesGhost_ceGhostFails : GhostWritesGhost ceGhostFails := trivial
theorem realReadsReal_ceGhostFails : RealReadsReal ceGhostFails := trivial
theorem ghostBlocksNoDiverge_ceGhostFails : GhostBlocksNoDiverge ceGhostFails :=
  fun _ => not_diverges_of_fails (s := .assert (.lit 0)) ⟨1, rfl⟩

/-- The R1 counterexample, as a refinement failure (strongest form). -/
theorem ceGhostWritesReal_not_refinesUpTo_abortBot :
    ¬ RefinesUpTo abortBot ceGhostWritesReal σ0 (erase ceGhostWritesReal) σ0 :=
  not_refinesUpTo_of_behaves (ceGhostWritesReal_behaves σ0) (behaves_skip σ0)
    (term_real_ne realPart_ceGhostWritesReal_ne.symm)
    (by rintro (h | h) <;> cases h)

/-- The R2 counterexample, as a refinement failure (strongest form). -/
theorem ceImplicitFlow_not_refinesUpTo_abortBot :
    ¬ RefinesUpTo abortBot ceImplicitFlow σ0 (erase ceImplicitFlow) σ0 :=
  not_refinesUpTo_of_behaves ceImplicitFlow_behaves_σ0 erase_ceImplicitFlow_behaves_σ0
    (term_real_ne realPart_ceImplicitFlow_ne.symm)
    (by rintro (h | h) <;> cases h)

theorem ceGhostDiverges_not_refinesUpTo_failBot :
    ¬ RefinesUpTo failBot ceGhostDiverges σ0 (erase ceGhostDiverges) σ0 :=
  not_refinesUpTo_of_behaves (ceGhostDiverges_diverges σ0) (behaves_skip σ0)
    (fun h => by cases h) (fun h => by cases h)

theorem ceGhostFails_not_refinesUpTo_divBot :
    ¬ RefinesUpTo divBot ceGhostFails σ0 (erase ceGhostFails) σ0 :=
  not_refinesUpTo_of_behaves (ceGhostFails_fails σ0) (behaves_skip σ0)
    (fun h => by cases h) (fun h => by cases h)

/-- Distinct real starting stores: `skip` from `σ0` versus `skip` from `σ0` with
`x := 1`. -/
theorem skip_not_refinesUpTo_abortBot_of_real_ne :
    ¬ RefinesUpTo abortBot .skip σ0 (erase .skip) (σ0.update x 1) :=
  not_refinesUpTo_of_behaves (behaves_skip σ0) (behaves_skip (σ0.update x 1))
    (term_real_ne realPart_ceGhostWritesReal_ne)
    (by rintro (h | h) <;> cases h)

theorem trivial_ghost_hyps_skip :
    GhostWritesGhost .skip ∧ RealReadsReal .skip ∧ GhostNoDivergeFrom .skip σ0 ∧
      GhostNoFailFrom .skip σ0 :=
  ⟨trivial, trivial, ghostNoDivergeFrom_of_ghostBlocksNoDiverge (P := .skip) trivial σ0,
    ghostNoFailFrom_of_ghostBlocksNoFail (P := .skip) trivial σ0⟩

/-! ## Non-vacuity witness (fully proved) -/

theorem ghostBlocksNoDiverge_demo : GhostBlocksNoDiverge demo :=
  ⟨trivial, ⟨fun σ => assign_not_diverges _ _ σ, ⟨trivial, fun σ => assert_not_diverges _ σ⟩⟩⟩

/-- The ghost assertion of `demo` holds on every run of `demo`. -/
theorem ghostNoFailFrom_demo (σ : Store) : GhostNoFailFrom demo σ :=
  ghostReach_seq (ghostReach_assign _ _ _ σ) ⟨1, rfl⟩
    (ghostReach_seq (ghostReach_ghost (assign_not_fails _ _ _)) ⟨2, rfl⟩
      (ghostReach_seq (ghostReach_assign _ _ _ _) ⟨1, rfl⟩
        (ghostReach_ghost (not_fails_of_term ⟨1, rfl⟩))))

/-- ...but the same ghost assertion fails from some states, so the static
all-states condition `GhostBlocksNoFail` rejects `demo`. -/
theorem demo_not_ghostBlocksNoFail : ¬ GhostBlocksNoFail demo :=
  fun h => h.2.2.2 σ0 ⟨1, rfl⟩

theorem ghostWritesGhost_demo : GhostWritesGhost demo :=
  ⟨trivial, ⟨trivial, ⟨trivial, trivial⟩⟩⟩

theorem realReadsReal_demo : RealReadsReal demo :=
  ⟨trivial, ⟨trivial, ⟨⟨trivial, trivial⟩, trivial⟩⟩⟩

/-- **Non-vacuity of 1.A–1.D.** `demo` (which contains a ghost update and a ghost
assertion) satisfies R1, R2, R3a and R3b from `σ0`, and the erased program is run
from `σ0g`, whose ghost part differs from that of `σ0`. -/
theorem demo_satisfies_erasure_hypotheses :
    GhostWritesGhost demo ∧ RealReadsReal demo ∧ realPart σ0 = realPart σ0g ∧
      GhostNoDivergeFrom demo σ0 ∧ GhostNoFailFrom demo σ0 :=
  ⟨ghostWritesGhost_demo, realReadsReal_demo, realPart_σ0g.symm,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_demo σ0, ghostNoFailFrom_demo σ0⟩

/-- **Non-vacuity of the global form of 1.D** (`erasureExact_of_...`). `demo` satisfies
the global hypotheses. -/
theorem demo_satisfies_global_erasure_hypotheses :
    GhostWritesGhost demo ∧ RealReadsReal demo ∧ (∀ σ, GhostNoDivergeFrom demo σ) ∧
      (∀ σ, GhostNoFailFrom demo σ) :=
  ⟨ghostWritesGhost_demo, realReadsReal_demo,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_demo, ghostNoFailFrom_demo⟩

/-! ## Result 2: tightness counterexamples in canonical form (fully proved)

Each theorem exhibits a concrete instance satisfying all hypotheses of the named
result except one, for which the conclusion fails. -/

theorem not_rbehaves_iff_of_not_refinesUpTo_abortBot {A C : Stmt} {σ τ : Store}
    (h : ¬ RefinesUpTo abortBot A σ C τ) : ¬ ∀ b, RBehaves A σ b ↔ RBehaves C τ b :=
  fun h' => h (refinesUpTo_of_rbehaves_iff h')

theorem not_refinesUpTo_failBot_of_not_abortBot {A C : Stmt} {σ τ : Store}
    (h : ¬ RefinesUpTo abortBot A σ C τ) : ¬ RefinesUpTo failBot A σ C τ :=
  fun h' => h (h'.mono fun _ hb => Or.inl hb)

theorem not_refinesUpTo_divBot_of_not_abortBot {A C : Stmt} {σ τ : Store}
    (h : ¬ RefinesUpTo abortBot A σ C τ) : ¬ RefinesUpTo divBot A σ C τ :=
  fun h' => h (h'.mono fun _ hb => Or.inr hb)

-- 1.A
theorem erase_refinesUpTo_abortBot_needs_ghostWritesGhost :
    RealReadsReal ceGhostWritesReal ∧ realPart σ0 = realPart σ0 ∧
      ¬ RefinesUpTo abortBot ceGhostWritesReal σ0 (erase ceGhostWritesReal) σ0 :=
  ⟨trivial, rfl, ceGhostWritesReal_not_refinesUpTo_abortBot⟩

theorem erase_refinesUpTo_abortBot_needs_realReadsReal :
    GhostWritesGhost ceImplicitFlow ∧ realPart σ0 = realPart σ0 ∧
      ¬ RefinesUpTo abortBot ceImplicitFlow σ0 (erase ceImplicitFlow) σ0 :=
  ⟨ghostWritesGhost_ceImplicitFlow, rfl, ceImplicitFlow_not_refinesUpTo_abortBot⟩

theorem erase_refinesUpTo_abortBot_needs_same_realPart :
    GhostWritesGhost .skip ∧ RealReadsReal .skip ∧
      ¬ RefinesUpTo abortBot .skip σ0 (erase .skip) (σ0.update x 1) :=
  ⟨trivial, trivial, skip_not_refinesUpTo_abortBot_of_real_ne⟩

-- 1.B
theorem erase_refinesUpTo_failBot_needs_ghostWritesGhost :
    RealReadsReal ceGhostWritesReal ∧ realPart σ0 = realPart σ0 ∧
      GhostNoDivergeFrom ceGhostWritesReal σ0 ∧
      ¬ RefinesUpTo failBot ceGhostWritesReal σ0 (erase ceGhostWritesReal) σ0 :=
  ⟨trivial, rfl, ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceGhostWritesReal σ0,
    not_refinesUpTo_failBot_of_not_abortBot ceGhostWritesReal_not_refinesUpTo_abortBot⟩

theorem erase_refinesUpTo_failBot_needs_realReadsReal :
    GhostWritesGhost ceImplicitFlow ∧ realPart σ0 = realPart σ0 ∧
      GhostNoDivergeFrom ceImplicitFlow σ0 ∧
      ¬ RefinesUpTo failBot ceImplicitFlow σ0 (erase ceImplicitFlow) σ0 :=
  ⟨ghostWritesGhost_ceImplicitFlow, rfl,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceImplicitFlow σ0,
    not_refinesUpTo_failBot_of_not_abortBot ceImplicitFlow_not_refinesUpTo_abortBot⟩

theorem erase_refinesUpTo_failBot_needs_ghostNoDivergeFrom :
    GhostWritesGhost ceGhostDiverges ∧ RealReadsReal ceGhostDiverges ∧ realPart σ0 = realPart σ0 ∧
      ¬ RefinesUpTo failBot ceGhostDiverges σ0 (erase ceGhostDiverges) σ0 :=
  ⟨trivial, trivial, rfl, ceGhostDiverges_not_refinesUpTo_failBot⟩

theorem erase_refinesUpTo_failBot_needs_same_realPart :
    GhostWritesGhost .skip ∧ RealReadsReal .skip ∧ GhostNoDivergeFrom .skip σ0 ∧
      ¬ RefinesUpTo failBot .skip σ0 (erase .skip) (σ0.update x 1) :=
  ⟨trivial, trivial, trivial_ghost_hyps_skip.2.2.1,
    not_refinesUpTo_failBot_of_not_abortBot skip_not_refinesUpTo_abortBot_of_real_ne⟩

-- 1.C
theorem erase_refinesUpTo_divBot_needs_ghostWritesGhost :
    RealReadsReal ceGhostWritesReal ∧ realPart σ0 = realPart σ0 ∧
      GhostNoFailFrom ceGhostWritesReal σ0 ∧
      ¬ RefinesUpTo divBot ceGhostWritesReal σ0 (erase ceGhostWritesReal) σ0 :=
  ⟨trivial, rfl, ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceGhostWritesReal σ0,
    not_refinesUpTo_divBot_of_not_abortBot ceGhostWritesReal_not_refinesUpTo_abortBot⟩

theorem erase_refinesUpTo_divBot_needs_realReadsReal :
    GhostWritesGhost ceImplicitFlow ∧ realPart σ0 = realPart σ0 ∧
      GhostNoFailFrom ceImplicitFlow σ0 ∧
      ¬ RefinesUpTo divBot ceImplicitFlow σ0 (erase ceImplicitFlow) σ0 :=
  ⟨ghostWritesGhost_ceImplicitFlow, rfl,
    ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceImplicitFlow σ0,
    not_refinesUpTo_divBot_of_not_abortBot ceImplicitFlow_not_refinesUpTo_abortBot⟩

theorem erase_refinesUpTo_divBot_needs_ghostNoFailFrom :
    GhostWritesGhost ceGhostFails ∧ RealReadsReal ceGhostFails ∧ realPart σ0 = realPart σ0 ∧
      ¬ RefinesUpTo divBot ceGhostFails σ0 (erase ceGhostFails) σ0 :=
  ⟨trivial, trivial, rfl, ceGhostFails_not_refinesUpTo_divBot⟩

theorem erase_refinesUpTo_divBot_needs_same_realPart :
    GhostWritesGhost .skip ∧ RealReadsReal .skip ∧ GhostNoFailFrom .skip σ0 ∧
      ¬ RefinesUpTo divBot .skip σ0 (erase .skip) (σ0.update x 1) :=
  ⟨trivial, trivial, trivial_ghost_hyps_skip.2.2.2,
    not_refinesUpTo_divBot_of_not_abortBot skip_not_refinesUpTo_abortBot_of_real_ne⟩

-- 1.D
theorem erase_rbehaves_iff_needs_ghostWritesGhost :
    RealReadsReal ceGhostWritesReal ∧ realPart σ0 = realPart σ0 ∧
      GhostNoDivergeFrom ceGhostWritesReal σ0 ∧ GhostNoFailFrom ceGhostWritesReal σ0 ∧
      ¬ ∀ b, RBehaves ceGhostWritesReal σ0 b ↔ RBehaves (erase ceGhostWritesReal) σ0 b :=
  ⟨trivial, rfl, ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceGhostWritesReal σ0,
    ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceGhostWritesReal σ0,
    not_rbehaves_iff_of_not_refinesUpTo_abortBot ceGhostWritesReal_not_refinesUpTo_abortBot⟩

theorem erase_rbehaves_iff_needs_realReadsReal :
    GhostWritesGhost ceImplicitFlow ∧ realPart σ0 = realPart σ0 ∧
      GhostNoDivergeFrom ceImplicitFlow σ0 ∧ GhostNoFailFrom ceImplicitFlow σ0 ∧
      ¬ ∀ b, RBehaves ceImplicitFlow σ0 b ↔ RBehaves (erase ceImplicitFlow) σ0 b :=
  ⟨ghostWritesGhost_ceImplicitFlow, rfl,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceImplicitFlow σ0,
    ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceImplicitFlow σ0,
    not_rbehaves_iff_of_not_refinesUpTo_abortBot ceImplicitFlow_not_refinesUpTo_abortBot⟩

theorem erase_rbehaves_iff_needs_ghostNoDivergeFrom :
    GhostWritesGhost ceGhostDiverges ∧ RealReadsReal ceGhostDiverges ∧ realPart σ0 = realPart σ0 ∧
      GhostNoFailFrom ceGhostDiverges σ0 ∧
      ¬ ∀ b, RBehaves ceGhostDiverges σ0 b ↔ RBehaves (erase ceGhostDiverges) σ0 b :=
  ⟨trivial, trivial, rfl, ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceGhostDiverges σ0,
    not_rbehaves_iff_of_behaves (ceGhostDiverges_diverges σ0) (behaves_skip σ0) (fun h => by cases h)⟩

theorem erase_rbehaves_iff_needs_ghostNoFailFrom :
    GhostWritesGhost ceGhostFails ∧ RealReadsReal ceGhostFails ∧ realPart σ0 = realPart σ0 ∧
      GhostNoDivergeFrom ceGhostFails σ0 ∧
      ¬ ∀ b, RBehaves ceGhostFails σ0 b ↔ RBehaves (erase ceGhostFails) σ0 b :=
  ⟨trivial, trivial, rfl, ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceGhostFails σ0,
    not_rbehaves_iff_of_behaves (ceGhostFails_fails σ0) (behaves_skip σ0) (fun h => by cases h)⟩

theorem erase_rbehaves_iff_needs_same_realPart :
    GhostWritesGhost .skip ∧ RealReadsReal .skip ∧ GhostNoDivergeFrom .skip σ0 ∧
      GhostNoFailFrom .skip σ0 ∧
      ¬ ∀ b, RBehaves .skip σ0 b ↔ RBehaves (erase .skip) (σ0.update x 1) b :=
  ⟨trivial, trivial, trivial_ghost_hyps_skip.2.2.1, trivial_ghost_hyps_skip.2.2.2,
    not_rbehaves_iff_of_not_refinesUpTo_abortBot skip_not_refinesUpTo_abortBot_of_real_ne⟩

-- global form of 1.D (`ErasureExact`)
theorem erasureExact_needs_ghostWritesGhost :
    RealReadsReal ceGhostWritesReal ∧ (∀ σ, GhostNoDivergeFrom ceGhostWritesReal σ) ∧
      (∀ σ, GhostNoFailFrom ceGhostWritesReal σ) ∧ ¬ ErasureExact ceGhostWritesReal :=
  ⟨trivial, ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceGhostWritesReal,
    ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceGhostWritesReal,
    fun h => erase_rbehaves_iff_needs_ghostWritesGhost.2.2.2.2 (h σ0 σ0 rfl)⟩

theorem erasureExact_needs_realReadsReal :
    GhostWritesGhost ceImplicitFlow ∧ (∀ σ, GhostNoDivergeFrom ceImplicitFlow σ) ∧
      (∀ σ, GhostNoFailFrom ceImplicitFlow σ) ∧ ¬ ErasureExact ceImplicitFlow :=
  ⟨ghostWritesGhost_ceImplicitFlow,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceImplicitFlow,
    ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceImplicitFlow,
    fun h => erase_rbehaves_iff_needs_realReadsReal.2.2.2.2 (h σ0 σ0 rfl)⟩

theorem erasureExact_needs_ghostNoDivergeFrom :
    GhostWritesGhost ceGhostDiverges ∧ RealReadsReal ceGhostDiverges ∧
      (∀ σ, GhostNoFailFrom ceGhostDiverges σ) ∧ ¬ ErasureExact ceGhostDiverges :=
  ⟨trivial, trivial, ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceGhostDiverges,
    fun h => erase_rbehaves_iff_needs_ghostNoDivergeFrom.2.2.2.2 (h σ0 σ0 rfl)⟩

theorem erasureExact_needs_ghostNoFailFrom :
    GhostWritesGhost ceGhostFails ∧ RealReadsReal ceGhostFails ∧
      (∀ σ, GhostNoDivergeFrom ceGhostFails σ) ∧ ¬ ErasureExact ceGhostFails :=
  ⟨trivial, trivial, ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceGhostFails,
    fun h => erase_rbehaves_iff_needs_ghostNoFailFrom.2.2.2.2 (h σ0 σ0 rfl)⟩

/-! ## Result 2: the four violations, stated as standalone facts (fully proved) -/

/-- **2.1 Ghost write to a real variable.** `ghost { x := 1 }` satisfies R2, R3a, R3b
from every state, but `erase` changes its final real store: from `σ0` the original
ends with `x = 1`, the erased program with `x = 0`. So even the weakest guarantee,
refinement up to failure and divergence (1.A), fails. -/
theorem ghostWriteToReal_breaks_erasure :
    RealReadsReal ceGhostWritesReal ∧ (∀ σ, GhostNoDivergeFrom ceGhostWritesReal σ) ∧
      (∀ σ, GhostNoFailFrom ceGhostWritesReal σ) ∧
      RBehaves ceGhostWritesReal σ0 (.term (realPart (σ0.update x 1))) ∧
      RBehaves (erase ceGhostWritesReal) σ0 (.term (realPart σ0)) ∧
      realPart (σ0.update x 1) ≠ realPart σ0 ∧
      ¬ RefinesUpTo abortBot ceGhostWritesReal σ0 (erase ceGhostWritesReal) σ0 :=
  ⟨trivial, erasureExact_needs_ghostWritesGhost.2.1, erasureExact_needs_ghostWritesGhost.2.2.1,
    RBehaves.of_behaves (ceGhostWritesReal_behaves σ0), RBehaves.of_behaves (behaves_skip σ0),
    realPart_ceGhostWritesReal_ne, ceGhostWritesReal_not_refinesUpTo_abortBot⟩

/-- **2.2 Implicit flow.** `ghost { g := 1 }; if g then x := 1 else skip` satisfies
R1, R3a, R3b from every state; from `σ0` the original ends with `x = 1` and the
erased program (whose `if` now reads the stale ghost value `0`) with `x = 0`. So
refinement up to failure and divergence (1.A) fails, and erasure is not exact. -/
theorem implicitFlow_breaks_erasure :
    GhostWritesGhost ceImplicitFlow ∧ (∀ σ, GhostNoDivergeFrom ceImplicitFlow σ) ∧
      (∀ σ, GhostNoFailFrom ceImplicitFlow σ) ∧
      RBehaves ceImplicitFlow σ0 (.term (realPart ((σ0.update g 1).update x 1))) ∧
      RBehaves (erase ceImplicitFlow) σ0 (.term (realPart σ0)) ∧
      realPart ((σ0.update g 1).update x 1) ≠ realPart σ0 ∧
      ¬ RefinesUpTo abortBot ceImplicitFlow σ0 (erase ceImplicitFlow) σ0 ∧
      ¬ ErasureExact ceImplicitFlow :=
  ⟨ghostWritesGhost_ceImplicitFlow, erasureExact_needs_realReadsReal.2.1,
    erasureExact_needs_realReadsReal.2.2.1, RBehaves.of_behaves ceImplicitFlow_behaves_σ0,
    RBehaves.of_behaves erase_ceImplicitFlow_behaves_σ0, realPart_ceImplicitFlow_ne,
    ceImplicitFlow_not_refinesUpTo_abortBot, erasureExact_needs_realReadsReal.2.2.2⟩

theorem ceGhostDiverges_not_behaviour_inclusion (σ : Store) :
    ¬ (∀ b, RBehaves (erase ceGhostDiverges) σ b → RBehaves ceGhostDiverges σ b) := by
  intro h
  have := h _ (RBehaves.of_behaves (behaves_skip σ))
  rw [RBehaves.iff_of_behaves (ceGhostDiverges_diverges σ)] at this
  cases this

/-- **2.3 Non-terminating ghost code.** `ghost { while 1 do skip }` satisfies R1, R2,
R3b; from every state the original diverges while the erased program terminates.
So the erased program has a behaviour the original lacks: behaviour inclusion
`beh(erase P) ⊆ beh(P)` fails, refinement up to failure fails, and exactness fails,
although refinement up to divergence holds. -/
theorem ghostDivergence_breaks_erasure (σ : Store) :
    GhostWritesGhost ceGhostDiverges ∧ RealReadsReal ceGhostDiverges ∧
      GhostNoFailFrom ceGhostDiverges σ ∧
      Diverges ceGhostDiverges σ ∧ Behaves (erase ceGhostDiverges) σ (.term σ) ∧
      ¬ (∀ b, RBehaves (erase ceGhostDiverges) σ b → RBehaves ceGhostDiverges σ b) ∧
      ¬ RefinesUpTo failBot ceGhostDiverges σ (erase ceGhostDiverges) σ ∧
      ¬ ErasureExact ceGhostDiverges ∧
      RefinesUpTo divBot ceGhostDiverges σ (erase ceGhostDiverges) σ :=
  ⟨trivial, trivial, ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceGhostDiverges σ,
    ceGhostDiverges_diverges σ, behaves_skip σ,
    ceGhostDiverges_not_behaviour_inclusion σ,
    not_refinesUpTo_of_behaves (ceGhostDiverges_diverges σ) (behaves_skip σ)
      (fun h => by cases h) (fun h => by cases h),
    erasureExact_needs_ghostNoDivergeFrom.2.2.2,
    Or.inl ⟨.diverge, rfl, RBehaves.of_behaves (ceGhostDiverges_diverges σ)⟩⟩

/-- **2.4 Failing ghost assertion.** `ghost { assert 0 }` satisfies R1, R2, R3a; from
every state the original fails while the erased program terminates. Refinement up
to failure still holds; refinement up to divergence and exactness do not. -/
theorem ghostFailure_breaks_erasure (σ : Store) :
    GhostWritesGhost ceGhostFails ∧ RealReadsReal ceGhostFails ∧
      GhostNoDivergeFrom ceGhostFails σ ∧
      Fails ceGhostFails σ ∧ Behaves (erase ceGhostFails) σ (.term σ) ∧
      ¬ RefinesUpTo divBot ceGhostFails σ (erase ceGhostFails) σ ∧
      ¬ ErasureExact ceGhostFails ∧
      RefinesUpTo failBot ceGhostFails σ (erase ceGhostFails) σ :=
  ⟨trivial, trivial, ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceGhostFails σ,
    ceGhostFails_fails σ, behaves_skip σ,
    not_refinesUpTo_of_behaves (ceGhostFails_fails σ) (behaves_skip σ)
      (fun h => by cases h) (fun h => by cases h),
    erasureExact_needs_ghostNoFailFrom.2.2.2,
    Or.inl ⟨.fail, rfl, RBehaves.of_behaves (ceGhostFails_fails σ)⟩⟩

theorem realPart_ceDataFlow_ne :
    realPart (σ0.update x 0) ≠ realPart ((σ0.update g 1).update x 1) := by
  intro he
  have := congrFun he 0
  simp [realPart, Store.update, x] at this

/-- **2.2 (data-flow variant)** `ghost { g := 1 }; x := g` satisfies R1, R3a, R3b
everywhere; from `σ0` the original ends with `x = 1` and the erased program, which
reads the initial ghost value `0`, with `x = 0`. These two runs are evaluated in the
proof; the statement records only that refinement up to failure and divergence (1.A)
fails and that erasure is not exact. -/
theorem dataFlow_breaks_erasure :
    GhostWritesGhost ceDataFlow ∧ (∀ σ, GhostNoDivergeFrom ceDataFlow σ) ∧
      (∀ σ, GhostNoFailFrom ceDataFlow σ) ∧
      ¬ RefinesUpTo abortBot ceDataFlow σ0 (erase ceDataFlow) σ0 ∧
      ¬ ErasureExact ceDataFlow := by
  have hP : Behaves ceDataFlow σ0 (.term ((σ0.update g 1).update x 1)) := ⟨3, rfl⟩
  have hE : Behaves (erase ceDataFlow) σ0 (.term (σ0.update x 0)) := ⟨3, rfl⟩
  have hne := term_real_ne realPart_ceDataFlow_ne
  refine ⟨⟨trivial, trivial⟩,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge
      ⟨fun σ => assign_not_diverges _ _ σ, trivial⟩,
    ghostNoFailFrom_of_ghostBlocksNoFail ⟨fun σ => assign_not_fails _ _ σ, trivial⟩,
    not_refinesUpTo_of_behaves hP hE hne (by rintro (h | h) <;> cases h), ?_⟩
  intro h
  exact not_rbehaves_iff_of_behaves hP hE hne (h σ0 σ0 rfl)

/-! ## Positive controls for result 2 (fully proved)

Removing each violation restores exact erasure, proved directly for the concrete
program without appeal to result 1. -/

/-- Control for 2.1: a ghost write to a *ghost* variable is erased exactly. -/
theorem pcGhostWritesGhost_erasureExact : ErasureExact pcGhostWritesGhost :=
  erasureExact_of_term (fun σ => σ.update g 1) id (fun _ => ⟨2, rfl⟩) (fun _ => ⟨1, rfl⟩)
    (fun σ _ h => (realPart_update_ghost σ 0 1).trans h)

/-- Control for 2.2: branching on a *real* value after ghost code is erased exactly. -/
theorem pcRealBranch_erasureExact : ErasureExact pcRealBranch := by
  refine erasureExact_of_term
    (fun σ => if σ x = 0 then σ.update g 1 else (σ.update g 1).update x 1)
    (fun τ => if τ x = 0 then τ else τ.update x 1) ?_ ?_ ?_
  · intro σ
    refine ⟨3, ?_⟩
    by_cases h : σ (Var.real 0) = 0 <;> simp [pcRealBranch, run, Outcome.bind, Expr.eval, Store.update, h, x, g]
  · intro τ
    refine ⟨3, ?_⟩
    by_cases h : τ (Var.real 0) = 0 <;> simp [pcRealBranch, erase, run, Outcome.bind, Expr.eval, h, x]
  · intro σ τ hστ
    have hx : σ x = τ x := congrFun hστ 0
    by_cases h : σ x = 0
    · have h' : τ x = 0 := hx ▸ h
      simp only [h, h', ↓reduceIte]
      exact (realPart_update_ghost σ 0 1).trans hστ
    · have h' : ¬ τ x = 0 := hx ▸ h
      simp only [h, h', ↓reduceIte]
      exact realPart_update_congr ((realPart_update_ghost σ 0 1).trans hστ) x 1

/-- Control for 2.3: a *terminating* ghost loop is erased exactly. -/
theorem pcGhostTerminatingLoop_erasureExact : ErasureExact pcGhostTerminatingLoop :=
  erasureExact_of_term id id (fun _ => ⟨2, rfl⟩) (fun _ => ⟨1, rfl⟩) (fun _ _ h => h)

/-- Control for 2.4: a *passing* ghost assertion is erased exactly. -/
theorem pcGhostPassingAssert_erasureExact : ErasureExact pcGhostPassingAssert :=
  erasureExact_of_term id id (fun _ => ⟨2, rfl⟩) (fun _ => ⟨1, rfl⟩) (fun _ _ h => h)

/-- Control for the data-flow variant of 2.2: copying a *real* value after ghost code
is erased exactly. -/
theorem pcRealDataFlow_erasureExact : ErasureExact pcRealDataFlow := by
  refine erasureExact_of_term (fun σ => (σ.update g 1).update x ((σ.update g 1) y))
    (fun τ => τ.update x (τ y)) (fun _ => ⟨3, rfl⟩) (fun _ => ⟨3, rfl⟩) ?_
  intro σ τ hστ
  have h1 : realPart (σ.update g 1) = realPart τ := (realPart_update_ghost σ 0 1).trans hστ
  have h2 : (σ.update g 1) y = τ y := congrFun h1 1
  simp only [h2]
  exact realPart_update_congr h1 x (τ y)

/-! ## Further non-vacuity witnesses for result 1 (fully proved)

`demo` terminates normally, so it does not exercise the diverging case of 1.B or the
failing case of 1.C. The two programs below satisfy every restriction and diverge,
respectively fail at a real run-time check. -/

theorem ghostThenSpin_diverges (σ : Store) : Diverges ghostThenSpin σ := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    show Outcome.bind (run n pcGhostWritesGhost σ) (run n spin) = none
    match h : run n pcGhostWritesGhost σ with
    | none => rfl
    | some .fail =>
      exact absurd ⟨n, h⟩ (not_fails_of_term (s := pcGhostWritesGhost) (σ' := σ.update g 1) ⟨2, rfl⟩)
    | some (.ok σ') => exact run_spin n σ'

/-- **Non-vacuity of 1.B (diverging case).** `ghost { g := 1 }; while 1 do skip`
satisfies R1, R2, R3a, R3b from `σ0` and diverges. -/
theorem ghostThenSpin_satisfies_erasure_hypotheses :
    GhostWritesGhost ghostThenSpin ∧ RealReadsReal ghostThenSpin ∧ realPart σ0 = realPart σ0g ∧
      GhostNoDivergeFrom ghostThenSpin σ0 ∧ GhostNoFailFrom ghostThenSpin σ0 ∧
      Diverges ghostThenSpin σ0 :=
  ⟨⟨trivial, trivial⟩, ⟨trivial, trivial, trivial⟩, realPart_σ0g.symm,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge (P := ghostThenSpin)
      ⟨fun σ => assign_not_diverges _ _ σ, trivial⟩ σ0,
    ghostNoFailFrom_of_ghostBlocksNoFail (P := ghostThenSpin)
      ⟨fun σ => assign_not_fails _ _ σ, trivial⟩ σ0,
    ghostThenSpin_diverges σ0⟩

/-- **Non-vacuity of 1.C (failing case).** `ghost { g := 1 }; assert 0` satisfies R1,
R2, R3a, R3b from `σ0` and fails at its real assertion. -/
theorem ghostThenRealFail_satisfies_erasure_hypotheses :
    GhostWritesGhost ghostThenRealFail ∧ RealReadsReal ghostThenRealFail ∧
      realPart σ0 = realPart σ0g ∧
      GhostNoDivergeFrom ghostThenRealFail σ0 ∧ GhostNoFailFrom ghostThenRealFail σ0 ∧
      Fails ghostThenRealFail σ0 :=
  ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, realPart_σ0g.symm,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge (P := ghostThenRealFail)
      ⟨fun σ => assign_not_diverges _ _ σ, trivial⟩ σ0,
    ghostNoFailFrom_of_ghostBlocksNoFail (P := ghostThenRealFail)
      ⟨fun σ => assign_not_fails _ _ σ, trivial⟩ σ0,
    ⟨3, rfl⟩⟩

end Toy.Ghost
