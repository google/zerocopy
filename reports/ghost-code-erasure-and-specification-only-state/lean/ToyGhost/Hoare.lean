import ToyGhost.Erasure

/-!
# Result 3: proofs about real variables survive erasure

A Hoare triple whose pre- and postcondition mention only real variables, valid
for the original program `P` (which may use ghost code to establish it), remains
valid for `erase P`.

* Partial correctness with safety (`SafePartialTriple`): needs R1, R2 and, for each
  real precondition state, one initial store with that real part from which no ghost
  block of the run diverges (R3a). R3b is not a separate hypothesis: on precondition
  states it follows from the triple's own no-failure clause
  (`ghostNoFailFrom_of_safePartialTriple`).
* Weak partial correctness (`WeakPartialTriple`, failure vacuous): needs R1, R2, and
  R3a together with R3b at a common initial store.
* Total correctness (`TotalTriple`): needs only R1 and R2; both parts of R3 follow
  from the triple on precondition states (`ghostTotalFrom_of_totalTriple`).

All triples here are semantic validity statements, not derivability in a Hoare
logic or a verification-condition generator.
-/

namespace Toy.Ghost

/-! ## Derivability of R3 on non-failing / non-diverging runs (fully proved) -/

/-- If the run of `P` from `σ` does not fail, no ghost block it starts fails. -/
theorem ghostNoFailFrom_of_not_fails {P : Stmt} {σ : Store} (h : ¬ Fails P σ) :
    GhostNoFailFrom P σ := by
  intro n
  induction n generalizing P σ with
  | zero => trivial
  | succ n ih =>
    cases P with
    | skip => trivial
    | assign v e => trivial
    | assert e => trivial
    | seq s t =>
      exact ⟨ih fun hf => h (fails_seq_left hf),
        fun σ' hs => ih fun hf => h (fails_seq_right hs hf)⟩
    | ite c s t =>
      simp only [GhostReach]
      split
      · rename_i hc
        exact ih fun ⟨m, hm⟩ => h ⟨m + 1, by simp [run, hc, hm]⟩
      · rename_i hc
        exact ih fun ⟨m, hm⟩ => h ⟨m + 1, by simp [run, hc, hm]⟩
    | loop c b =>
      simp only [GhostReach]
      split
      · trivial
      · rename_i hc
        exact ⟨ih fun hf => h (fails_loop_body hc hf),
          fun σ' hb => ih (P := .loop c b) fun hf => h (fails_loop_next hc hb hf)⟩
    | ghost s =>
      exact fun ⟨m, hm⟩ => h ⟨m + 1, by simp [run, hm]⟩

theorem diverges_seq_left {s t : Stmt} {σ : Store} (h : Diverges s σ) : Diverges (.seq s t) σ := by
  intro m
  cases m with
  | zero => rfl
  | succ m => simp [run, h m, Outcome.bind]

theorem diverges_seq_right {s t : Stmt} {σ σ' : Store} {n : Nat} (hs : run n s σ = some (.ok σ'))
    (h : Diverges t σ') : Diverges (.seq s t) σ := by
  intro m
  cases m with
  | zero => rfl
  | succ m =>
    simp only [run]
    match hr : run m s σ with
    | none => rfl
    | some o =>
      cases run_det hr hs
      exact h m

theorem diverges_loop_body {c : Expr} {b : Stmt} {σ : Store} (hc : ¬ c.eval σ = 0)
    (h : Diverges b σ) : Diverges (.loop c b) σ := by
  intro m
  cases m with
  | zero => rfl
  | succ m => simp [run, hc, h m, Outcome.bind]

theorem diverges_loop_next {c : Expr} {b : Stmt} {σ σ' : Store} {n : Nat} (hc : ¬ c.eval σ = 0)
    (hb : run n b σ = some (.ok σ')) (h : Diverges (.loop c b) σ') : Diverges (.loop c b) σ := by
  intro m
  cases m with
  | zero => rfl
  | succ m =>
    simp only [run, hc, ↓reduceIte]
    match hr : run m b σ with
    | none => rfl
    | some o =>
      cases run_det hr hb
      exact h m

/-- If the run of `P` from `σ` does not diverge, no ghost block it starts diverges. -/
theorem ghostNoDivergeFrom_of_not_diverges {P : Stmt} {σ : Store} (h : ¬ Diverges P σ) :
    GhostNoDivergeFrom P σ := by
  intro n
  induction n generalizing P σ with
  | zero => trivial
  | succ n ih =>
    cases P with
    | skip => trivial
    | assign v e => trivial
    | assert e => trivial
    | seq s t =>
      exact ⟨ih fun hd => h (diverges_seq_left hd),
        fun σ' hs => ih fun hd => h (diverges_seq_right hs hd)⟩
    | ite c s t =>
      simp only [GhostReach]
      split
      · rename_i hc
        refine ih fun hd => h fun m => ?_
        cases m with
        | zero => rfl
        | succ m => simp [run, hc, hd m]
      · rename_i hc
        refine ih fun hd => h fun m => ?_
        cases m with
        | zero => rfl
        | succ m => simp [run, hc, hd m]
    | loop c b =>
      simp only [GhostReach]
      split
      · trivial
      · rename_i hc
        exact ⟨ih fun hd => h (diverges_loop_body hc hd),
          fun σ' hb => ih (P := .loop c b) fun hd => h (diverges_loop_next hc hb hd)⟩
    | ghost s =>
      refine fun hd => h fun m => ?_
      cases m with
      | zero => rfl
      | succ m => exact hd m

/-- R3b on precondition states is derivable from a partial-correctness triple. -/
theorem ghostNoFailFrom_of_safePartialTriple {Pre Post : RStore → Prop} {P : Stmt} {σ : Store}
    (h : SafePartialTriple Pre P Post) (hpre : Pre (realPart σ)) : GhostNoFailFrom P σ :=
  ghostNoFailFrom_of_not_fails (h σ hpre).1

/-- R3a and R3b on precondition states are derivable from a total-correctness triple. -/
theorem ghostTotalFrom_of_totalTriple {Pre Post : RStore → Prop} {P : Stmt} {σ : Store}
    (h : TotalTriple Pre P Post) (hpre : Pre (realPart σ)) :
    GhostNoDivergeFrom P σ ∧ GhostNoFailFrom P σ := by
  obtain ⟨σ', hσ', _⟩ := h σ hpre
  exact ⟨ghostNoDivergeFrom_of_not_diverges (not_diverges_of_term hσ'),
    ghostNoFailFrom_of_not_fails (not_fails_of_term hσ')⟩

/-! ## Result 3 (derived from result 1) -/

/-- An all-states obligation on precondition states yields one witness store per
real precondition state (with ghost part `0`). -/
theorem exists_of_forall_pre {Pre : RStore → Prop} {Q : Store → Prop}
    (h : ∀ σ, Pre (realPart σ) → Q σ) : ∀ r, Pre r → ∃ σ, realPart σ = r ∧ Q σ :=
  fun r hr => ⟨Store.ofReal r, realPart_ofReal r, h _ ((realPart_ofReal r).symm ▸ hr)⟩

/-- **3.A** Partial correctness with safety transfers to the erased program under R1,
R2, and R3a for one initial store per real precondition state. The triple
`SafePartialTriple` includes safety (no assertion fails from precondition states);
that clause is what makes R3b unnecessary here (compare 3.D). -/
theorem safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom
    {Pre Post : RStore → Prop} {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (hT : ∀ r, Pre r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom P σ)
    (h : SafePartialTriple Pre P Post) : SafePartialTriple Pre (erase P) Post := by
  intro τ hpre
  obtain ⟨σ, hστ, hTσ⟩ := hT (realPart τ) hpre
  obtain ⟨hnf, hpost⟩ := h σ (hστ ▸ hpre)
  rcases erase_refinesUpTo_failBot_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom
      hW hR hστ hTσ with ⟨a, ha, hAa⟩ | hsub
  · simp only [failBot] at ha
    subst ha
    exact absurd (rbehaves_fail_iff.1 hAa) hnf
  · refine ⟨fun hf => hnf (rbehaves_fail_iff.1 (hsub _ (rbehaves_fail_iff.2 hf))), ?_⟩
    intro τ' hτ'
    obtain ⟨σ', hσ', hr⟩ := rbehaves_term_iff.1 (hsub _ (RBehaves.of_behaves hτ'))
    rw [← hr]
    exact hpost σ' hσ'

/-- Corollary of 3.A with the simpler, stronger obligation that R3a hold from *every*
initial store whose real part satisfies `Pre`. -/
theorem safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom
    {Pre Post : RStore → Prop} {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (hT : ∀ σ, Pre (realPart σ) → GhostNoDivergeFrom P σ)
    (h : SafePartialTriple Pre P Post) : SafePartialTriple Pre (erase P) Post :=
  safePartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom
    hW hR (exists_of_forall_pre hT) h

/-- **3.B** Total correctness transfers to the erased program under R1 and R2 alone. -/
theorem totalTriple_erase_of_ghostWritesGhost_of_realReadsReal
    {Pre Post : RStore → Prop} {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (h : TotalTriple Pre P Post) : TotalTriple Pre (erase P) Post := by
  intro τ hpre
  obtain ⟨σ', hσ', hpost⟩ := h τ hpre
  obtain ⟨τ', hτ', hr⟩ := refinesUpTo_abortBot_iff.1
    (erase_refinesUpTo_abortBot_of_ghostWritesGhost_of_realReadsReal hW hR rfl) σ' hσ'
  exact ⟨τ', hτ', hr ▸ hpost⟩

/-- **3.D** Weak partial correctness (failure is vacuous) transfers to the erased
program under R1, R2, and, for one initial store per real precondition state, both
R3a and R3b at that store. -/
theorem weakPartialTriple_erase_of_ghostWritesGhost_of_realReadsReal_of_exists_ghostNoDivergeFrom_ghostNoFailFrom
    {Pre Post : RStore → Prop} {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (hG : ∀ r, Pre r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom P σ ∧ GhostNoFailFrom P σ)
    (h : WeakPartialTriple Pre P Post) : WeakPartialTriple Pre (erase P) Post := by
  intro τ hpre τ' hτ'
  obtain ⟨σ, hστ, hTσ, hFσ⟩ := hG (realPart τ) hpre
  have hiff :=
    erase_rbehaves_iff_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom
      hW hR hστ hTσ hFσ
  obtain ⟨σ', hσ', hr⟩ := rbehaves_term_iff.1 ((hiff _).2 (RBehaves.of_behaves hτ'))
  rw [← hr]
  exact h σ (hστ ▸ hpre) σ' hσ'

end Toy.Ghost
