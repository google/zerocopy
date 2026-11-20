import ToyGhost.Hoare

/-!
# Result 3: counterexamples, non-vacuity witnesses, and a dispensable restriction
(all fully proved)
-/

namespace Toy.Ghost

/-- Precondition `True`. -/
def preTrue : RStore → Prop := fun _ => True
/-- Postcondition `x = 1`. -/
def postX1 : RStore → Prop := fun r => r 0 = 1
/-- Postcondition `False`. -/
def postFalse : RStore → Prop := fun _ => False
/-- Postcondition `y = 6`. -/
def postY6 : RStore → Prop := fun r => r 1 = 6
/-- Precondition `x = 0`. -/
def preX0 : RStore → Prop := fun r => r 0 = 0
/-- Postcondition `True`. -/
def postTrue : RStore → Prop := fun _ => True

theorem demo_behaves (σ : Store) :
    Behaves demo σ (.term (((σ.update x 3).update g 4).update y 6)) := ⟨5, rfl⟩

theorem ceImplicitFlow_behaves (σ : Store) :
    Behaves ceImplicitFlow σ (.term ((σ.update g 1).update x 1)) := ⟨3, rfl⟩

theorem safePartialTriple_demo : SafePartialTriple preTrue demo postY6 := by
  intro σ _
  refine ⟨not_fails_of_term (demo_behaves σ), fun σ' h => ?_⟩
  cases Behaves.unique h (demo_behaves σ)
  rfl

theorem totalTriple_demo : TotalTriple preTrue demo postY6 :=
  fun σ _ => ⟨_, demo_behaves σ, rfl⟩

/-! ## 3.A: non-vacuity and canonical counterexamples -/

/-- **Non-vacuity of 3.A.** `demo`, which contains ghost code, satisfies
`{True} demo {y = 6}` (partial correctness with safety), R1, R2, and R3a for one
initial store per real state. -/
theorem safePartialTriple_erase_hypotheses_satisfiable :
    GhostWritesGhost demo ∧ RealReadsReal demo ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom demo σ) ∧
      SafePartialTriple preTrue demo postY6 :=
  ⟨ghostWritesGhost_demo, realReadsReal_demo,
    exists_of_forall_pre fun σ _ => ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_demo σ,
    safePartialTriple_demo⟩

theorem safePartialTriple_erase_needs_ghostWritesGhost :
    RealReadsReal ceGhostWritesReal ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom ceGhostWritesReal σ) ∧
      SafePartialTriple preTrue ceGhostWritesReal postX1 ∧
      ¬ SafePartialTriple preTrue (erase ceGhostWritesReal) postX1 := by
  refine ⟨trivial,
    exists_of_forall_pre fun σ _ => ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceGhostWritesReal σ,
    ?_, ?_⟩
  · intro σ _
    refine ⟨not_fails_of_term (ceGhostWritesReal_behaves σ), fun σ' h => ?_⟩
    cases Behaves.unique h (ceGhostWritesReal_behaves σ)
    rfl
  · intro h
    have := (h σ0 trivial).2 σ0 (behaves_skip σ0)
    cases this

theorem safePartialTriple_erase_needs_realReadsReal :
    GhostWritesGhost ceImplicitFlow ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom ceImplicitFlow σ) ∧
      SafePartialTriple preTrue ceImplicitFlow postX1 ∧
      ¬ SafePartialTriple preTrue (erase ceImplicitFlow) postX1 := by
  refine ⟨ghostWritesGhost_ceImplicitFlow,
    exists_of_forall_pre fun σ _ => ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceImplicitFlow σ,
    ?_, ?_⟩
  · intro σ _
    refine ⟨not_fails_of_term (ceImplicitFlow_behaves σ), fun σ' h => ?_⟩
    cases Behaves.unique h (ceImplicitFlow_behaves σ)
    rfl
  · intro h
    have := (h σ0 trivial).2 σ0 erase_ceImplicitFlow_behaves_σ0
    cases this

/-- A diverging ghost "lemma" makes `{True} P {False}` hold in partial correctness,
and the erased program refutes the triple. The program violates even the
existential form of R3a: no initial store avoids the divergence. -/
theorem safePartialTriple_erase_needs_ghostNoDivergeFrom :
    GhostWritesGhost ceGhostDiverges ∧ RealReadsReal ceGhostDiverges ∧
      SafePartialTriple preTrue ceGhostDiverges postFalse ∧
      ¬ (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom ceGhostDiverges σ) ∧
      ¬ SafePartialTriple preTrue (erase ceGhostDiverges) postFalse := by
  refine ⟨trivial, trivial, ?_, ?_, ?_⟩
  · intro σ _
    refine ⟨not_fails_of_diverges (ceGhostDiverges_diverges σ), fun σ' h => ?_⟩
    cases Behaves.unique h (ceGhostDiverges_diverges σ)
  · intro h
    obtain ⟨σ, _, hT⟩ := h (realPart σ0) trivial
    exact hT 1 (spin_diverges σ)
  · intro h
    exact (h σ0 trivial).2 σ0 (behaves_skip σ0)

theorem safePartialTriple_erase_needs_safePartialTriple :
    GhostWritesGhost .skip ∧ RealReadsReal .skip ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom .skip σ) ∧
      ¬ SafePartialTriple preTrue (erase .skip) postFalse :=
  ⟨trivial, trivial,
    exists_of_forall_pre fun σ _ => ghostNoDivergeFrom_of_ghostBlocksNoDiverge (P := .skip) trivial σ,
    fun h => (h σ0 trivial).2 σ0 (behaves_skip σ0)⟩

/-- `ghost { assert x = 0 }`. -/
def ghostAssertX0 : Stmt := .ghost (.assert (.eq (.var x) (.lit 0)))

/-- **R3b is not needed as a separate hypothesis of 3.A.** `ghost { assert x = 0 }`
satisfies the hypotheses of 3.A for `{x = 0} · {True}` although its ghost assertion
fails from states violating the precondition, so it violates R3b globally; the
conclusion holds (checked directly here). -/
theorem safePartialTriple_transfer_without_global_ghostNoFail :
    GhostWritesGhost ghostAssertX0 ∧ RealReadsReal ghostAssertX0 ∧
      (∀ r, preX0 r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom ghostAssertX0 σ) ∧
      SafePartialTriple preX0 ghostAssertX0 postTrue ∧
      ¬ (∀ σ, GhostNoFailFrom ghostAssertX0 σ) ∧
      SafePartialTriple preX0 (erase ghostAssertX0) postTrue := by
  refine ⟨trivial, trivial,
    exists_of_forall_pre fun σ _ => ghostNoDivergeFrom_of_ghostBlocksNoDiverge (P := ghostAssertX0)
      (fun τ => assert_not_diverges _ τ) σ, ?_, ?_, ?_⟩
  · intro σ hσ
    have hx : σ (.real 0) = 0 := hσ
    have hb : Behaves ghostAssertX0 σ (.term σ) := ⟨2, by simp [ghostAssertX0, run, Expr.eval, x, hx]⟩
    exact ⟨not_fails_of_term hb, fun _ _ => trivial⟩
  · intro h
    exact h (σ0.update x 1) 1 ⟨1, rfl⟩
  · intro σ _
    exact ⟨not_fails_of_term (behaves_skip σ), fun _ _ => trivial⟩

/-- **The existential form of R3a in 3.A is strictly weaker than the all-states form.**
`ghost { while g do skip }; x := 1` satisfies R1, R2, `{True} · {x = 1}` and the
existential R3a, violates the all-states R3a (from `σ0g`, where `g = 1`), and its
erasure satisfies the triple (checked directly). -/
theorem safePartialTriple_exists_ghostNoDivergeFrom_strictly_weaker :
    GhostWritesGhost ghostSpinThenSetX ∧ RealReadsReal ghostSpinThenSetX ∧
      SafePartialTriple preTrue ghostSpinThenSetX postX1 ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom ghostSpinThenSetX σ) ∧
      ¬ (∀ σ, preTrue (realPart σ) → GhostNoDivergeFrom ghostSpinThenSetX σ) ∧
      SafePartialTriple preTrue (erase ghostSpinThenSetX) postX1 := by
  refine ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ?_, ?_, ?_, ?_⟩
  · intro σ _
    by_cases hg : σ (.ghost 0) = 0
    · have hb : Behaves ghostSpinThenSetX σ (.term (σ.update x 1)) :=
        ⟨3, by simp [ghostSpinThenSetX, ghostSpinOnG, run, Outcome.bind, Expr.eval, g, hg]⟩
      refine ⟨not_fails_of_term hb, fun σ' h => ?_⟩
      cases Behaves.unique h hb
      rfl
    · have hd : Diverges ghostSpinThenSetX σ :=
        diverges_seq_left fun n => by
          cases n with
          | zero => rfl
          | succ n => exact run_loop_skip_none (c := .var g) hg n
      refine ⟨not_fails_of_diverges hd, fun σ' h => ?_⟩
      cases Behaves.unique h hd
  · intro r _
    refine ⟨Store.ofReal r, realPart_ofReal r, ?_⟩
    exact ghostReach_seq
      (ghostReach_ghost (not_diverges_of_term (σ' := Store.ofReal r) ⟨1, rfl⟩))
      ⟨2, rfl⟩ (ghostReach_assign _ _ _ _)
  · intro h
    exact (h σ0g trivial 2).1 (run_loop_skip_none (by decide))
  · intro σ _
    have hb : Behaves (erase ghostSpinThenSetX) σ (.term (σ.update x 1)) := ⟨2, rfl⟩
    refine ⟨not_fails_of_term hb, fun σ' h => ?_⟩
    cases Behaves.unique h hb
    rfl

/-! ## 3.B: non-vacuity and canonical counterexamples -/

/-- **Non-vacuity of 3.B.** -/
theorem totalTriple_erase_hypotheses_satisfiable :
    GhostWritesGhost demo ∧ RealReadsReal demo ∧ TotalTriple preTrue demo postY6 :=
  ⟨ghostWritesGhost_demo, realReadsReal_demo, totalTriple_demo⟩

theorem not_totalTriple_skip_postX1 : ¬ TotalTriple preTrue .skip postX1 := by
  intro h
  obtain ⟨τ', hτ', hp⟩ := h σ0 trivial
  cases Behaves.unique hτ' (behaves_skip σ0)
  cases hp

theorem totalTriple_erase_needs_ghostWritesGhost :
    RealReadsReal ceGhostWritesReal ∧ TotalTriple preTrue ceGhostWritesReal postX1 ∧
      ¬ TotalTriple preTrue (erase ceGhostWritesReal) postX1 :=
  ⟨trivial, fun σ _ => ⟨_, ceGhostWritesReal_behaves σ, rfl⟩, not_totalTriple_skip_postX1⟩

theorem totalTriple_erase_needs_realReadsReal :
    GhostWritesGhost ceImplicitFlow ∧ TotalTriple preTrue ceImplicitFlow postX1 ∧
      ¬ TotalTriple preTrue (erase ceImplicitFlow) postX1 := by
  refine ⟨ghostWritesGhost_ceImplicitFlow, fun σ _ => ⟨_, ceImplicitFlow_behaves σ, rfl⟩, ?_⟩
  intro h
  obtain ⟨τ', hτ', hp⟩ := h σ0 trivial
  cases Behaves.unique hτ' erase_ceImplicitFlow_behaves_σ0
  cases hp

theorem totalTriple_erase_needs_totalTriple :
    GhostWritesGhost .skip ∧ RealReadsReal .skip ∧ ¬ TotalTriple preTrue (erase .skip) postFalse :=
  ⟨trivial, trivial, fun h => by obtain ⟨_, _, hp⟩ := h σ0 trivial; exact hp⟩

/-- `totalTriple_erase_...` transfers one way only: the erased programs of the R3a and
R3b counterexamples satisfy `{True} · {True}` in total correctness, the originals do
not. -/
theorem totalTriple_erase_not_converse :
    GhostWritesGhost ceGhostDiverges ∧ RealReadsReal ceGhostDiverges ∧
      TotalTriple preTrue (erase ceGhostDiverges) postTrue ∧
      ¬ TotalTriple preTrue ceGhostDiverges postTrue ∧
      GhostWritesGhost ceGhostFails ∧ RealReadsReal ceGhostFails ∧
      TotalTriple preTrue (erase ceGhostFails) postTrue ∧
      ¬ TotalTriple preTrue ceGhostFails postTrue :=
  ⟨trivial, trivial, fun σ _ => ⟨σ, behaves_skip σ, trivial⟩,
    fun h => by
      obtain ⟨_, h1, _⟩ := h σ0 trivial
      exact not_diverges_of_term h1 (ceGhostDiverges_diverges σ0),
    trivial, trivial, fun σ _ => ⟨σ, behaves_skip σ, trivial⟩,
    fun h => by
      obtain ⟨_, h1, _⟩ := h σ0 trivial
      exact not_fails_of_term h1 (ceGhostFails_fails σ0)⟩

/-! ## Supporting lemmas `ghostNoFailFrom_of_not_fails`, `ghostNoDivergeFrom_of_not_diverges` -/

/-- Their hypotheses hold together for `demo` from every initial store. -/
theorem demo_not_fails_and_not_diverges (σ : Store) : ¬ Fails demo σ ∧ ¬ Diverges demo σ :=
  ⟨not_fails_of_term (demo_behaves σ), not_diverges_of_term (demo_behaves σ)⟩

/-! ## 3.D: non-vacuity and canonical counterexamples -/

/-- **Non-vacuity of 3.D.** -/
theorem weakPartialTriple_erase_hypotheses_satisfiable :
    GhostWritesGhost demo ∧ RealReadsReal demo ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom demo σ ∧ GhostNoFailFrom demo σ) ∧
      WeakPartialTriple preTrue demo postY6 :=
  ⟨ghostWritesGhost_demo, realReadsReal_demo,
    fun r _ => ⟨Store.ofReal r, realPart_ofReal r,
      ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_demo _, ghostNoFailFrom_demo _⟩,
    fun σ _ σ' h => by cases Behaves.unique h (demo_behaves σ); rfl⟩

theorem weakPartialTriple_erase_needs_ghostWritesGhost :
    RealReadsReal ceGhostWritesReal ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom ceGhostWritesReal σ ∧
        GhostNoFailFrom ceGhostWritesReal σ) ∧
      WeakPartialTriple preTrue ceGhostWritesReal postX1 ∧
      ¬ WeakPartialTriple preTrue (erase ceGhostWritesReal) postX1 :=
  ⟨trivial,
    fun r _ => ⟨Store.ofReal r, realPart_ofReal r,
      ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceGhostWritesReal _,
      ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceGhostWritesReal _⟩,
    fun σ _ σ' h => by cases Behaves.unique h (ceGhostWritesReal_behaves σ); rfl,
    fun h => by have := h σ0 trivial σ0 (behaves_skip σ0); cases this⟩

theorem weakPartialTriple_erase_needs_realReadsReal :
    GhostWritesGhost ceImplicitFlow ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom ceImplicitFlow σ ∧
        GhostNoFailFrom ceImplicitFlow σ) ∧
      WeakPartialTriple preTrue ceImplicitFlow postX1 ∧
      ¬ WeakPartialTriple preTrue (erase ceImplicitFlow) postX1 :=
  ⟨ghostWritesGhost_ceImplicitFlow,
    fun r _ => ⟨Store.ofReal r, realPart_ofReal r,
      ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceImplicitFlow _,
      ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceImplicitFlow _⟩,
    fun σ _ σ' h => by cases Behaves.unique h (ceImplicitFlow_behaves σ); rfl,
    fun h => by have := h σ0 trivial σ0 erase_ceImplicitFlow_behaves_σ0; cases this⟩

/-- R3b is needed in 3.D: `ghost { assert 0 }` satisfies R1, R2, the R3a half of the
hypothesis, and `{True} · {False}` weakly; its erasure refutes the triple. -/
theorem weakPartialTriple_erase_needs_ghostNoFailFrom :
    GhostWritesGhost ceGhostFails ∧ RealReadsReal ceGhostFails ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom ceGhostFails σ) ∧
      WeakPartialTriple preTrue ceGhostFails postFalse ∧
      ¬ WeakPartialTriple preTrue (erase ceGhostFails) postFalse :=
  ⟨trivial, trivial,
    exists_of_forall_pre fun σ _ =>
      ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceGhostFails σ,
    fun σ _ _ h => absurd (ceGhostFails_fails σ) (not_fails_of_term h),
    fun h => h σ0 trivial σ0 (behaves_skip σ0)⟩

/-- R3a is needed in 3.D: `ghost { while 1 do skip }` satisfies R1, R2, the R3b half
of the hypothesis, and `{True} · {False}` weakly; its erasure refutes the triple. -/
theorem weakPartialTriple_erase_needs_ghostNoDivergeFrom :
    GhostWritesGhost ceGhostDiverges ∧ RealReadsReal ceGhostDiverges ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoFailFrom ceGhostDiverges σ) ∧
      WeakPartialTriple preTrue ceGhostDiverges postFalse ∧
      ¬ WeakPartialTriple preTrue (erase ceGhostDiverges) postFalse :=
  ⟨trivial, trivial,
    exists_of_forall_pre fun σ _ =>
      ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ceGhostDiverges σ,
    fun σ _ _ h => absurd (ceGhostDiverges_diverges σ) (not_diverges_of_term h),
    fun h => h σ0 trivial σ0 (behaves_skip σ0)⟩

theorem weakPartialTriple_erase_needs_weakPartialTriple :
    GhostWritesGhost .skip ∧ RealReadsReal .skip ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom .skip σ ∧ GhostNoFailFrom .skip σ) ∧
      ¬ WeakPartialTriple preTrue (erase .skip) postFalse :=
  ⟨trivial, trivial,
    fun r _ => ⟨Store.ofReal r, realPart_ofReal r,
      ghostNoDivergeFrom_of_ghostBlocksNoDiverge (P := .skip) trivial _,
      ghostNoFailFrom_of_ghostBlocksNoFail (P := .skip) trivial _⟩,
    fun h => h σ0 trivial σ0 (behaves_skip σ0)⟩

/-- Safety matters for 3.A: with *weak* partial correctness and without R3b, the
transfer fails (`ghost { assert 0 }` satisfies all hypotheses of 3.A with the
triple weakened, and the conclusion fails). -/
theorem weakPartialTriple_erase_fails_without_ghostNoFailFrom :
    GhostWritesGhost ceGhostFails ∧ RealReadsReal ceGhostFails ∧
      (∀ σ, preTrue (realPart σ) → GhostNoDivergeFrom ceGhostFails σ) ∧
      WeakPartialTriple preTrue ceGhostFails postFalse ∧
      ¬ WeakPartialTriple preTrue (erase ceGhostFails) postFalse :=
  ⟨trivial, trivial,
    fun σ _ => ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceGhostFails σ,
    weakPartialTriple_erase_needs_ghostNoFailFrom.2.2.2.1,
    weakPartialTriple_erase_needs_ghostNoFailFrom.2.2.2.2⟩

/-- `ghost { if g then assert 0 else while 1 do skip }`: fails when `g ≠ 0`, diverges when
`g = 0`. -/
def ghostFailOrSpin : Stmt := .ghost (.ite (.var g) (.assert (.lit 0)) spin)

theorem ghostFailOrSpin_fails {σ : Store} (h : σ (.ghost 0) ≠ 0) : Fails ghostFailOrSpin σ :=
  ⟨3, by simp [ghostFailOrSpin, run, Expr.eval, g, h]⟩

theorem ghostFailOrSpin_inner_diverges {σ : Store} (h : σ (.ghost 0) = 0) :
    Diverges (.ite (.var g) (.assert (.lit 0)) spin) σ := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    have h' : Expr.eval (.var g) σ = 0 := h
    show (if Expr.eval (.var g) σ = 0 then run n spin σ else run n (.assert (.lit 0)) σ) = none
    simp only [h', ↓reduceIte]
    exact run_spin n σ

/-- In 3.D, R3a and R3b must hold at a *common* store: `ghostFailOrSpin` has, for every
real state, a store without ghost divergence and another without ghost failure, and
satisfies `{True} · {False}` weakly, yet its erasure refutes the triple. -/
theorem weakPartialTriple_erase_split_ghost_conditions_insufficient :
    GhostWritesGhost ghostFailOrSpin ∧ RealReadsReal ghostFailOrSpin ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoDivergeFrom ghostFailOrSpin σ) ∧
      (∀ r, preTrue r → ∃ σ, realPart σ = r ∧ GhostNoFailFrom ghostFailOrSpin σ) ∧
      WeakPartialTriple preTrue ghostFailOrSpin postFalse ∧
      ¬ WeakPartialTriple preTrue (erase ghostFailOrSpin) postFalse := by
  refine ⟨⟨trivial, trivial⟩, trivial, ?_, ?_, ?_, fun h => h σ0 trivial σ0 (behaves_skip σ0)⟩
  · intro r _
    refine ⟨(Store.ofReal r).update g 1, (realPart_update_ghost _ 0 1).trans (realPart_ofReal r), ?_⟩
    refine ghostReach_ghost (not_diverges_of_fails ⟨2, ?_⟩)
    simp [run, Expr.eval, Store.update, g]
  · intro r _
    exact ⟨Store.ofReal r, realPart_ofReal r,
      ghostReach_ghost (not_fails_of_diverges (ghostFailOrSpin_inner_diverges rfl))⟩
  · intro σ _ σ' hσ'
    by_cases h : σ (.ghost 0) = 0
    · refine absurd ?_ (not_diverges_of_term hσ')
      intro n
      cases n with
      | zero => rfl
      | succ n => exact ghostFailOrSpin_inner_diverges h n
    · exact absurd (ghostFailOrSpin_fails h) (not_fails_of_term hσ')

end Toy.Ghost
