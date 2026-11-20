import ToyGhost.Tools

/-!
# Programs that mention no ghost variable ignore the ghost part of the store
(fully proved)

If `NoGhostVars s`, then runs of `s` from two stores with the same real part agree
step for step on the real part. With `noGhostVars_erase_of_realReadsReal` this shows
that, under R2, the erased program behaves as a program over real stores only.
-/

namespace Toy.Ghost

/-- Two partial results that agree up to the real part. -/
def OutRel : Option Outcome → Option Outcome → Prop
  | none, none => True
  | some .fail, some .fail => True
  | some (.ok σ), some (.ok τ) => realPart σ = realPart τ
  | _, _ => False

theorem OutRel.bind {o₁ o₂ : Option Outcome} {k₁ k₂ : Store → Option Outcome}
    (h : OutRel o₁ o₂) (hk : ∀ σ τ, realPart σ = realPart τ → OutRel (k₁ σ) (k₂ τ)) :
    OutRel (Outcome.bind o₁ k₁) (Outcome.bind o₂ k₂) := by
  match o₁, o₂, h with
  | none, none, _ => trivial
  | some .fail, some .fail, _ => trivial
  | some (.ok σ), some (.ok τ), h => exact hk σ τ h

theorem run_congr_of_noGhostVars (n : Nat) :
    ∀ (s : Stmt) (σ τ : Store), NoGhostVars s → realPart σ = realPart τ →
      OutRel (run n s σ) (run n s τ) := by
  induction n with
  | zero => intro s σ τ _ _; trivial
  | succ n ih =>
    intro s σ τ hs h
    cases s with
    | skip => exact h
    | assign v e =>
      cases v with
      | real i =>
        show realPart (σ.update (.real i) (e.eval σ)) = realPart (τ.update (.real i) (e.eval τ))
        rw [Expr.eval_congr_of_readsOnlyReal hs h]
        exact realPart_update_congr h _ _
      | ghost i => exact hs.elim
    | assert e =>
      simp only [run, Expr.eval_congr_of_readsOnlyReal (σ := σ) (τ := τ) hs h]
      split
      · trivial
      · exact h
    | seq s t =>
      exact OutRel.bind (ih s σ τ hs.1 h) (fun σ' τ' h' => ih t σ' τ' hs.2 h')
    | ite c s t =>
      simp only [run, Expr.eval_congr_of_readsOnlyReal (σ := σ) (τ := τ) hs.1 h]
      split
      · exact ih t σ τ hs.2.2 h
      · exact ih s σ τ hs.2.1 h
    | loop c b =>
      simp only [run, Expr.eval_congr_of_readsOnlyReal (σ := σ) (τ := τ) hs.1 h]
      split
      · exact h
      · exact OutRel.bind (ih b σ τ hs.2 h) (fun σ' τ' h' => ih (.loop c b) σ' τ' hs h')
    | ghost s => exact ih s σ τ hs h

/-- A program that mentions no ghost variable has the same real-observable
behaviours from any two stores with the same real part. -/
theorem rbehaves_congr_of_noGhostVars {s : Stmt} (hs : NoGhostVars s) {σ τ : Store}
    (h : realPart σ = realPart τ) (b : RBehaviour) : RBehaves s σ b ↔ RBehaves s τ b := by
  obtain ⟨b₀, hb₀⟩ := Behaves.exists s σ
  have key : ∃ c₀, Behaves s τ c₀ ∧ c₀.real = b₀.real := by
    cases b₀ with
    | term σ' =>
      obtain ⟨n, hn⟩ := hb₀
      have hr := run_congr_of_noGhostVars n s σ τ hs h
      rw [hn] at hr
      match hrun : run n s τ, hr with
      | some (.ok τ'), hr' =>
        exact ⟨.term τ', ⟨n, hrun⟩,
          congrArg RBehaviour.term (show realPart σ' = realPart τ' from hr').symm⟩
    | fail =>
      obtain ⟨n, hn⟩ := hb₀
      have hr := run_congr_of_noGhostVars n s σ τ hs h
      rw [hn] at hr
      match hrun : run n s τ, hr with
      | some .fail, _ => exact ⟨.fail, ⟨n, hrun⟩, rfl⟩
    | diverge =>
      refine ⟨.diverge, fun n => ?_, rfl⟩
      have hr := run_congr_of_noGhostVars n s σ τ hs h
      rw [hb₀ n] at hr
      match hrun : run n s τ, hr with
      | none, _ => rfl
  obtain ⟨c₀, hc₀, hcr⟩ := key
  rw [RBehaves.iff_of_behaves hb₀, RBehaves.iff_of_behaves hc₀, hcr]

/-- Under R2 the erased program's real behaviour depends only on the real part of
its initial store: it can be read as a program over real stores. -/
theorem erase_rbehaves_congr_of_realReadsReal {P : Stmt} (hR : RealReadsReal P)
    {σ τ : Store} (h : realPart σ = realPart τ) (b : RBehaviour) :
    RBehaves (erase P) σ b ↔ RBehaves (erase P) τ b :=
  rbehaves_congr_of_noGhostVars (noGhostVars_erase_of_realReadsReal hR) h b

end Toy.Ghost
