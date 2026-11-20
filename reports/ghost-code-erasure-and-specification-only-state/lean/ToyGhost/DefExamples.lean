import ToyGhost.Noninterference
import ToyGhost.HoareExamples

/-!
# Positive and negative examples for every definition (all fully proved)
-/

namespace Toy.Ghost

/-! ## `realPart` -/

/-- Positive: updating a ghost variable is invisible in the real part. -/
theorem realPart_example_ghost_update_invisible : realPart (σ0.update g 1) = realPart σ0 :=
  realPart_σ0g

/-- Negative: updating a real variable is visible in the real part. -/
theorem realPart_example_real_update_visible : realPart (σ0.update x 1) ≠ realPart σ0 :=
  realPart_ceGhostWritesReal_ne

/-! ## `Expr.ReadsOnlyReal` -/

theorem readsOnlyReal_example_pos : (Expr.add (.var x) (.lit 1)).ReadsOnlyReal := ⟨trivial, trivial⟩
theorem readsOnlyReal_example_neg : ¬ (Expr.var g).ReadsOnlyReal := fun h => h
theorem readsOnlyReal_example_neg_nested : ¬ (Expr.lt (.var x) (.var g)).ReadsOnlyReal :=
  fun h => h.2

/-! ## `run`, `Behaves`, `Fails`, `Diverges` -/

theorem behaves_example_term : Behaves (.assign x (.lit 1)) σ0 (.term (σ0.update x 1)) := ⟨1, rfl⟩
theorem behaves_example_fail : Fails (.assert (.lit 0)) σ0 := ⟨1, rfl⟩
theorem behaves_example_diverge : Diverges spin σ0 := spin_diverges σ0
theorem behaves_example_spin_never_terminates : ¬ ∃ σ', Behaves spin σ0 (.term σ') :=
  fun ⟨_, h⟩ => not_diverges_of_term h (spin_diverges σ0)
theorem behaves_example_skip_never_fails : ¬ Fails .skip σ0 := not_fails_of_term (behaves_skip σ0)
/-- Running out of fuel is not divergence: `skip` with fuel `0` gives `none`, yet
`skip` terminates. -/
theorem behaves_example_fuel_zero : run 0 .skip σ0 = none ∧ ¬ Diverges .skip σ0 :=
  ⟨rfl, not_diverges_of_term (behaves_skip σ0)⟩

/-! ## `RBehaves` -/

theorem rbehaves_example_ghost_write_invisible :
    RBehaves pcGhostWritesGhost σ0 (.term (realPart σ0)) := by
  have := RBehaves.of_behaves (s := pcGhostWritesGhost) (σ := σ0) (b := .term σ0g) ⟨2, rfl⟩
  simpa [Behaviour.real, realPart_σ0g] using this

theorem rbehaves_example_real_write_visible :
    ¬ RBehaves ceGhostWritesReal σ0 (.term (realPart σ0)) := by
  intro h
  rw [RBehaves.iff_of_behaves (ceGhostWritesReal_behaves σ0)] at h
  exact realPart_ceGhostWritesReal_ne (RBehaviour.term.inj h).symm

/-! ## `erase` -/

theorem erase_example_ghost_block : erase ceGhostWritesReal = .skip := rfl
theorem erase_example_ghost_assign : erase (.assign g (.var x)) = .skip := rfl
theorem erase_example_demo :
    erase demo = .seq (.assign x (.lit 3)) (.seq .skip (.seq (.assign y (.add (.var x) (.var x))) .skip)) :=
  rfl
/-- Negative: erasure keeps real assignments. -/
theorem erase_example_keeps_real_assign : erase (.assign x (.lit 1)) ≠ .skip := by
  intro h; cases h
/-- Negative: erasure keeps real (run-time) assertions. -/
theorem erase_example_keeps_real_assert : erase (.assert (.var x)) ≠ .skip := by
  intro h; cases h

/-! ## `GhostWritesGhost` (R1) -/

theorem ghostWritesGhost_example_pos : GhostWritesGhost pcGhostWritesGhost := trivial
theorem ghostWritesGhost_example_pos_real_write_outside_ghost :
    GhostWritesGhost (.assign x (.lit 1)) := trivial
theorem ghostWritesGhost_example_neg : ¬ GhostWritesGhost ceGhostWritesReal := fun h => h
/-- Negative: a real write nested anywhere inside a ghost block is rejected. -/
theorem ghostWritesGhost_example_neg_nested :
    ¬ GhostWritesGhost (.ghost (.ite (.var g) (.ghost (.assign x (.lit 1))) .skip)) :=
  fun h => h.1

/-! ## `RealReadsReal` (R2) -/

theorem realReadsReal_example_pos : RealReadsReal pcRealBranch :=
  ⟨trivial, trivial, trivial, trivial⟩
/-- Positive: a ghost statement (here, an assignment to a ghost variable) may read
ghost and real variables. -/
theorem realReadsReal_example_pos_ghost_assign : RealReadsReal (.assign g (.add (.var g) (.var x))) :=
  trivial
theorem realReadsReal_example_neg_implicit_flow : ¬ RealReadsReal ceImplicitFlow := fun h => h.2.1
theorem realReadsReal_example_neg_data_flow : ¬ RealReadsReal ceDataFlow := fun h => h.2
theorem realReadsReal_example_neg_real_assert : ¬ RealReadsReal (.assert (.var g)) := fun h => h

/-! ## `GhostNoDivergeFrom` / `GhostNoFailFrom` (R3, per run) -/

/-- `x := 0; ghost { while x do skip }`: the ghost loop diverges from some states,
but not from the state in which this program reaches it. -/
def guardedGhostSpin : Stmt := .seq (.assign x (.lit 0)) (.ghost (.loop (.var x) .skip))

theorem ghostNoDivergeFrom_example_pos : GhostNoDivergeFrom demo σ0 :=
  demo_satisfies_erasure_hypotheses.2.2.2.1

theorem ghostNoDivergeFrom_example_pos_guarded (σ : Store) :
    GhostNoDivergeFrom guardedGhostSpin σ :=
  ghostReach_seq (ghostReach_assign _ _ _ σ) ⟨1, rfl⟩
    (ghostReach_ghost (not_diverges_of_term ⟨1, rfl⟩))

/-- Positive: `GhostNoDivergeFrom` says "does not diverge", not "terminates
normally": an always-failing ghost block satisfies it. -/
theorem ghostNoDivergeFrom_example_pos_failing :
    GhostNoDivergeFrom ceGhostFails σ0 ∧ Fails ceGhostFails σ0 :=
  ⟨ghostNoDivergeFrom_of_ghostBlocksNoDiverge ghostBlocksNoDiverge_ceGhostFails σ0,
    ceGhostFails_fails σ0⟩

theorem ghostNoDivergeFrom_example_neg : ¬ GhostNoDivergeFrom ceGhostDiverges σ0 :=
  fun h => h 1 (spin_diverges σ0)

theorem ghostNoFailFrom_example_pos : GhostNoFailFrom demo σ0 := ghostNoFailFrom_demo σ0
theorem ghostNoFailFrom_example_neg : ¬ GhostNoFailFrom ceGhostFails σ0 := fun h => h 1 ⟨1, rfl⟩

/-- Loop body `x := x + 1; ghost { assert 0 < x }`. -/
def loopBody : Stmt :=
  .seq (.assign x (.add (.var x) (.lit 1))) (.ghost (.assert (.lt (.lit 0) (.var x))))

/-- `x := 0; while x < 3 do { x := x + 1; ghost { assert 0 < x } }`: a ghost assertion
inside a real loop that holds on every run but fails from some states. -/
def loopDemo : Stmt := .seq (.assign x (.lit 0)) (.loop (.lt (.var x) (.lit 3)) loopBody)

theorem loopBody_assert_behaves {σ : Store} (hx : 0 ≤ σ x) :
    Behaves (.assert (.lt (.lit 0) (.var x))) (σ.update x ((Expr.add (.var x) (.lit 1)).eval σ))
      (.term (σ.update x ((Expr.add (.var x) (.lit 1)).eval σ))) := by
  have hx' : σ (.real 0) ≥ 0 := hx
  refine ⟨1, ?_⟩
  have : (0 : Int) < σ (.real 0) + 1 := by omega
  simp [run, Expr.eval, Store.update, x, this]

theorem loopBody_behaves {σ : Store} (hx : 0 ≤ σ x) :
    Behaves loopBody σ (.term (σ.update x ((Expr.add (.var x) (.lit 1)).eval σ))) := by
  obtain ⟨m, hm⟩ := loopBody_assert_behaves hx
  refine ⟨Nat.max 1 (m + 1) + 1, ?_⟩
  simp only [loopBody, run]
  rw [run_mono (show run 1 (.assign x (.add (.var x) (.lit 1))) σ =
      some (.ok (σ.update x ((Expr.add (.var x) (.lit 1)).eval σ))) from rfl) (Nat.le_max_left _ _)]
  simp only [Outcome.bind]
  exact run_mono (s := .ghost _) (n := m + 1) hm (Nat.le_max_right _ _)

theorem ghostNoFail_loop_part :
    ∀ n σ, 0 ≤ σ x →
      GhostReach (fun g τ => ¬ Fails g τ) n (.loop (.lt (.var x) (.lit 3)) loopBody) σ := by
  intro n
  induction n with
  | zero => intros; trivial
  | succ n ih =>
    intro σ hx
    simp only [GhostReach]
    split
    · trivial
    · refine ⟨ghostReach_seq (ghostReach_assign _ _ _ σ) ⟨1, rfl⟩
          (ghostReach_ghost (not_fails_of_term (loopBody_assert_behaves hx))) n, ?_⟩
      intro σ' hrun
      obtain ⟨m, hm⟩ := loopBody_behaves hx
      cases run_det hrun hm
      apply ih
      have hx' : σ (.real 0) ≥ 0 := hx
      simp [Store.update, Expr.eval, x]
      omega

/-- Positive: the per-run condition admits a ghost assertion inside a real loop. -/
theorem ghostNoFailFrom_example_pos_loop (σ : Store) : GhostNoFailFrom loopDemo σ :=
  ghostReach_seq (ghostReach_assign _ _ _ σ) ⟨1, rfl⟩
    (fun n => ghostNoFail_loop_part n _ (by simp [Store.update, Expr.eval]))

/-- `loopDemo` satisfies every hypothesis of 1.A–1.D and of their global form (a second
witness, with a loop). -/
theorem loopDemo_satisfies_global_erasure_hypotheses :
    GhostWritesGhost loopDemo ∧ RealReadsReal loopDemo ∧ (∀ σ, GhostNoDivergeFrom loopDemo σ) ∧
      (∀ σ, GhostNoFailFrom loopDemo σ) :=
  ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, trivial⟩,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge (P := loopDemo)
      ⟨trivial, trivial, fun σ => assert_not_diverges _ σ⟩,
    ghostNoFailFrom_example_pos_loop⟩

/-- ...whereas the static condition rejects it. -/
theorem loopDemo_not_ghostBlocksNoFail : ¬ GhostBlocksNoFail loopDemo :=
  fun h => h.2.2 σ0 ⟨1, rfl⟩

/-! ## `GhostBlocksNoDiverge` / `GhostBlocksNoFail` (R3, static all-states variants) -/

theorem ghostBlocksNoDiverge_example_pos : GhostBlocksNoDiverge pcGhostTerminatingLoop :=
  fun σ => not_diverges_of_term (σ' := σ) ⟨1, rfl⟩
theorem ghostBlocksNoDiverge_example_neg : ¬ GhostBlocksNoDiverge ceGhostDiverges :=
  fun h => h σ0 (spin_diverges σ0)
/-- The static variant is strictly stronger than the per-run one. -/
theorem ghostBlocksNoDiverge_example_neg_guarded : ¬ GhostBlocksNoDiverge guardedGhostSpin :=
  fun h => h.2 (σ0.update x 1) (run_loop_skip_none (by decide))
theorem ghostBlocksNoFail_example_pos : GhostBlocksNoFail pcGhostPassingAssert :=
  fun σ => not_fails_of_term (σ' := σ) ⟨1, rfl⟩
theorem ghostBlocksNoFail_example_neg : ¬ GhostBlocksNoFail demo := demo_not_ghostBlocksNoFail

/-! ## `NoGhostVars` / `NoGhostCode` -/

theorem noGhostVars_example_pos : NoGhostVars (erase demo) :=
  noGhostVars_erase_of_realReadsReal realReadsReal_demo
theorem noGhostVars_example_neg : ¬ NoGhostVars demo := fun h => h.2.1
/-- Positive: a ghost block that mentions no ghost variable mentions no ghost
variable (`NoGhostVars` is about variables, not about ghost blocks). -/
theorem noGhostVars_example_pos_ghost_skip : NoGhostVars (.ghost .skip) := trivial
/-- Negative: a real statement that reads a ghost variable. -/
theorem noGhostVars_example_neg_real_reads_ghost : ¬ NoGhostVars realReadsGhost := fun h => h
/-- Negative: `NoGhostCode` rejects a ghost block even if it mentions no ghost variable. -/
theorem noGhostCode_example_neg_ghost_skip : ¬ NoGhostCode (.ghost .skip) := fun h => h
theorem noGhostCode_example_pos : NoGhostCode (erase demo) := noGhostCode_erase demo
theorem noGhostCode_example_neg : ¬ NoGhostCode demo := fun h => h.2.1

/-! ## Bottom sets and `RefinesUpTo` -/

theorem abortBot_example_pos : abortBot .diverge := Or.inr rfl
theorem abortBot_example_neg : ¬ abortBot (.term (realPart σ0)) := by rintro (h | h) <;> cases h
theorem failBot_example_pos : failBot .fail := rfl
theorem failBot_example_neg : ¬ failBot .diverge := fun h => by cases h
theorem divBot_example_pos : divBot .diverge := rfl
theorem divBot_example_neg : ¬ divBot .fail := fun h => by cases h

theorem refinesUpTo_refl (B : RBehaviour → Prop) (P : Stmt) (σ : Store) : RefinesUpTo B P σ P σ :=
  Or.inr fun _ h => h
/-- Positive: anything refines divergence when divergence is bottom. -/
theorem refinesUpTo_example_pos : RefinesUpTo divBot spin σ0 .skip σ0 :=
  Or.inl ⟨.diverge, rfl, RBehaves.of_behaves (spin_diverges σ0)⟩
/-- Negative: termination does not refine divergence when only failure is bottom. -/
theorem refinesUpTo_example_neg : ¬ RefinesUpTo failBot spin σ0 .skip σ0 :=
  not_refinesUpTo_of_behaves (spin_diverges σ0) (behaves_skip σ0) (fun h => by cases h)
    (fun h => by cases h)
/-- Negative (direction): divergence never refines termination. -/
theorem refinesUpTo_example_neg_direction : ¬ RefinesUpTo abortBot .skip σ0 spin σ0 :=
  not_refinesUpTo_of_behaves (behaves_skip σ0) (spin_diverges σ0) (fun h => by cases h)
    (by rintro (h | h) <;> cases h)

/-! ## `SafePartialTriple` -/

theorem safePartialTriple_example_pos : SafePartialTriple preTrue (.assign x (.lit 1)) postX1 := by
  intro σ _
  have hb : Behaves (.assign x (.lit 1)) σ (.term (σ.update x 1)) := ⟨1, rfl⟩
  refine ⟨not_fails_of_term hb, fun σ' h => ?_⟩
  cases Behaves.unique h hb
  rfl
/-- Positive: partial correctness holds vacuously for a diverging program. -/
theorem safePartialTriple_example_pos_vacuous : SafePartialTriple preTrue spin postFalse :=
  fun σ _ => ⟨spin_not_fails σ, fun _ h => by cases Behaves.unique h (spin_diverges σ)⟩
/-- Negative: the triple includes safety (no assertion failure). -/
theorem safePartialTriple_example_neg_safety : ¬ SafePartialTriple preTrue (.assert (.lit 0)) postTrue :=
  fun h => (h σ0 trivial).1 ⟨1, rfl⟩
theorem safePartialTriple_example_neg_post : ¬ SafePartialTriple preTrue .skip postFalse :=
  fun h => (h σ0 trivial).2 σ0 (behaves_skip σ0)

/-! ## `WeakPartialTriple` -/

/-- Positive: weak partial correctness holds vacuously for a failing program (unlike
`SafePartialTriple`, see `safePartialTriple_example_neg_safety`). -/
theorem weakPartialTriple_example_pos_vacuous_fail :
    WeakPartialTriple preTrue (.assert (.lit 0)) postFalse :=
  fun _ _ _ h => not_fails_of_term h ⟨1, rfl⟩
theorem weakPartialTriple_example_pos : WeakPartialTriple preTrue (.assign x (.lit 1)) postX1 :=
  fun σ _ σ' h => by cases Behaves.unique h (show Behaves _ σ (.term (σ.update x 1)) from ⟨1, rfl⟩); rfl
theorem weakPartialTriple_example_neg_post : ¬ WeakPartialTriple preTrue .skip postFalse :=
  fun h => h σ0 trivial σ0 (behaves_skip σ0)

/-! ## `TotalTriple` -/

theorem totalTriple_example_pos : TotalTriple preTrue (.assign x (.lit 1)) postX1 :=
  fun σ _ => ⟨σ.update x 1, ⟨1, rfl⟩, rfl⟩
theorem totalTriple_example_neg_divergence : ¬ TotalTriple preTrue spin postTrue := fun h => by
  obtain ⟨_, h1, _⟩ := h σ0 trivial
  exact not_diverges_of_term h1 (spin_diverges σ0)

/-! ## Noninterference and erasure relations -/

theorem ghostToRealNI_example_pos : GhostToRealNI pcGhostWritesGhost :=
  ghostToRealNI_of_erasureExact pcGhostWritesGhost_erasureExact
theorem ghostToRealNI_example_neg : ¬ GhostToRealNI realReadsGhost := not_ghostToRealNI_realReadsGhost
theorem ghostToRealNI_example_neg_termination_channel : ¬ GhostToRealNI ghostSpinOnG :=
  ghostWritesGhost_realReadsReal_not_sufficient_for_ghostToRealNI.2.2.2.2.2.2

theorem ghostToRealNI_abortInsensitive_example_pos : GhostToRealNI_AbortInsensitive ghostSpinOnG := ghostToRealNI_abortInsensitive_ghostSpinOnG
/-- Positive: the failure channel is not observed (`ghost { assert g }`). -/
theorem ghostToRealNI_abortInsensitive_example_pos_failure_channel :
    GhostToRealNI_AbortInsensitive ghostAssertG :=
  ghostAssertG_abortInsensitive_not_ghostToRealNI.2.2.2.1
theorem ghostToRealNI_abortInsensitive_example_neg : ¬ GhostToRealNI_AbortInsensitive realReadsGhost := by
  intro h
  have := h σ0 σ0g (σ0.update x 0) (σ0g.update x 1) realPart_σ0g.symm ⟨1, rfl⟩ ⟨1, rfl⟩
  have := congrFun this 0
  simp [realPart, Store.update, x] at this

theorem erasureExact_example_pos : ErasureExact pcGhostWritesGhost := pcGhostWritesGhost_erasureExact
theorem erasureExact_example_neg : ¬ ErasureExact ceGhostWritesReal :=
  erasureExact_needs_ghostWritesGhost.2.2.2

theorem erasureAgrees_example_pos : ErasureAgrees realReadsGhost := erasureAgrees_realReadsGhost
theorem erasureAgrees_example_neg : ¬ ErasureAgrees ceGhostWritesReal :=
  fun h => erase_rbehaves_iff_needs_ghostWritesGhost.2.2.2.2 (h σ0)

end Toy.Ghost
