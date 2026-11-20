import ToyHoare.Logic
import ToyHoare.Linear
import ToyHoare.Incomplete
import ToyHoare.VC
import ToyHoare.Total
import ToyHoare.Examples

/-!
# Tightness counterexamples, positive controls and non-vacuity witnesses

Each tightness counterexample is stated in canonical form: a concrete instance satisfies all the
*other* hypotheses of the named result, and the result's conclusion fails (where useful, the
failure of the hypothesis under test is stated too). For the concrete impossibility results the
"hypotheses" are the fixed parameters of the statement (assertion language, precondition,
postcondition, program text); a positive control changes exactly one of them, keeps the others
(including linear definability of the pre- and postcondition), and shows the impossibility
disappears. Each non-vacuity theorem exhibits a concrete instance satisfying all hypotheses of
the named result.
-/

namespace Toy.Hoare

/-! ### `hoare_sound` -/

/-- Non-vacuity of `hoare_sound`: derivations exist, both with linear and with semantic
invented assertions. -/
theorem nonvacuity_hoare_sound :
    Deriv LinDef (fun _ => True) exLoop exPostWeak ∧ Deriv AnyAssn exPre exLoop exPost :=
  ⟨exLoop_deriv_linDef_weak_post, exLoop_deriv_anyAssn⟩

/-- Tightness of the derivability hypothesis of `hoare_sound` (it has no other hypotheses): the
conclusion fails for the triple `{true} x := 1 {x = 0}`, which is therefore not derivable for
any `L`. -/
theorem hoare_sound_deriv_tight :
    ¬ Valid (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0) ∧
    ∀ L : Assn → Prop, ¬ Deriv L (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0) :=
  ⟨invalid_assign_triple, fun _ h => invalid_assign_triple (hoare_sound h)⟩

/-! ### Relative completeness (`hoare_relatively_complete_of_wlpAdmissibleFor`,
`valid_iff_deriv_wlpInvented`, `deriv_anyAssn_iff_valid`) -/

/-- Non-vacuity of relative completeness: (1) with linear invariants and the non-trivial
postcondition `x = 0`, command-local admissibility holds for the countdown loop and
`{0 ≤ x} countdown {x = 0}` is valid; (2) with semantic assertions the hypotheses hold for the
example triple. -/
theorem nonvacuity_relcomp :
    (WlpAdmissibleFor LinDef countdown (fun s => s 0 = 0) ∧
      Valid (fun s => 0 ≤ s 0) countdown (fun s => s 0 = 0) ∧ ¬ ∀ s : Store, s 0 = 0) ∧
    (WlpAdmissibleFor AnyAssn exLoop exPost ∧ Valid exPre exLoop exPost) := by
  refine ⟨⟨wlpAdmissibleFor_example_pos, (total_sound_of_bounded_variant countdown_tderiv).valid,
    fun h => ?_⟩, ⟨fun _ _ => trivial, exLoop_valid⟩⟩
  have := h (fun _ => 1)
  omega

/-- Tightness of the validity hypothesis: command-local admissibility holds (`L := AnyAssn`), the
triple `{true} x := 1 {x = 0}` is invalid, and it is not derivable. -/
theorem relcomp_valid_tight :
    WlpAdmissibleFor AnyAssn (.assign 0 (.lit 1)) (fun s => s 0 = 0) ∧
    ¬ Valid (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0) ∧
    ¬ Deriv AnyAssn (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0) :=
  ⟨fun _ _ => trivial, invalid_assign_triple, deriv_example_neg⟩

/-- Tightness of the admissibility hypothesis: for `L := LinDef` and the example triple, the
validity hypothesis holds, command-local admissibility fails, and the triple is not
derivable. -/
theorem relcomp_wlp_admissible_tight :
    Valid exPre exLoop exPost ∧ ¬ WlpAdmissibleFor LinDef exLoop exPost ∧
    ¬ Deriv LinDef exPre exLoop exPost :=
  ⟨exLoop_valid, wlpAdmissibleFor_example_neg, linear_qf_hoare_incomplete.2.2.2⟩

/-- Tightness of the admissibility hypothesis of `deriv_wlp_of_wlpAdmissibleFor`: for
`L := LinDef`, admissibility fails and `{wlp exLoop exPost} exLoop {exPost}` is not
derivable. -/
theorem deriv_wlp_needs_admissible :
    ¬ WlpAdmissibleFor LinDef exLoop exPost ∧
    ¬ Deriv LinDef (wlp exLoop exPost) exLoop exPost := by
  refine ⟨wlpAdmissibleFor_example_neg, fun h => ?_⟩
  obtain ⟨I, hL, hP, hb, hx⟩ := Deriv.whileDo_inv h
  exact exLoop_no_linDef_invariant
    ⟨I, hL, fun s hs => hP s (valid_iff_imp_wlp.mp exLoop_valid s hs), hb, hx⟩

/-- With the precondition `x = 0` instead of `x = y + y`, the same loop and postcondition are
derivable in the linear logic (invariant `x = 0`): the witness variable `y` is what forces
infinitely many even values into every invariant. -/
theorem exLoop_deriv_linDef_pre_zero : Deriv LinDef (fun s => s 0 = 0) exLoop exPost := by
  have hL : LinDef (fun s => s 0 = 0) := ⟨.eq (.var 0) (.lit 0), fun s => by
    simp only [LAssn.eval, LTerm.eval]; exact decide_eq_true_iff.symm⟩
  have hbody : Deriv LinDef (fun s => s 0 = 0 ∧ exGuard.eval s = true) exBody
      (fun s => s 0 = 0) := by
    refine Deriv.conseq (fun s h => ?_) (Deriv.assign 0 _ _) (fun _ h => h)
    obtain ⟨h₁, h₂⟩ := h
    rw [exGuard_eval, decide_eq_true_iff] at h₂
    omega
  refine Deriv.conseq (fun _ h => h) (Deriv.whileDo hL hbody) (fun s h => ?_)
  obtain ⟨h₁, _⟩ := h
  simp only [exPost]
  omega

/-- Command-local admissibility is sufficient, not necessary, for a particular triple: it fails
for the example loop and `x ≠ 1` with linear invariants, yet `{x = 0} exLoop {x ≠ 1}` is
derivable with the linear invariant `x = 0`. -/
theorem wlpAdmissibleFor_not_necessary :
    ¬ WlpAdmissibleFor LinDef exLoop exPost ∧ LinDef (fun s => s 0 = 0) ∧
    Deriv LinDef (fun s => s 0 = 0) exLoop exPost := by
  refine ⟨wlpAdmissibleFor_example_neg, ⟨.eq (.var 0) (.lit 0), fun s => ?_⟩,
    exLoop_deriv_linDef_pre_zero⟩
  simp only [LAssn.eval, LTerm.eval]; exact decide_eq_true_iff.symm

/-- Non-vacuity of `valid_iff_deriv_wlpInvented` and `deriv_anyAssn_iff_valid`: both sides hold
for the example triple, and both fail for `{true} x := 1 {x = 0}`. -/
theorem nonvacuity_semantic_iff :
    (Deriv AnyAssn exPre exLoop exPost ∧ Deriv (WlpInvented exLoop exPost) exPre exLoop exPost ∧
      Valid exPre exLoop exPost) ∧
    (¬ Deriv AnyAssn (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0) ∧
      ¬ Valid (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0)) :=
  ⟨⟨exLoop_deriv_anyAssn, valid_iff_deriv_wlpInvented.mp exLoop_valid, exLoop_valid⟩,
    deriv_example_neg, invalid_assign_triple⟩

/-- Replacing `AnyAssn` by `LinDef` breaks the characterization: a valid triple that is not
derivable. -/
theorem semantic_iff_needs_anyAssn :
    Valid exPre exLoop exPost ∧ ¬ Deriv LinDef exPre exLoop exPost :=
  ⟨exLoop_valid, linear_qf_hoare_incomplete.2.2.2⟩

/-! ### `linear_qf_hoare_incomplete`: positive controls (one parameter changed at a time) -/

theorem exPostWeak_linDef : LinDef exPostWeak :=
  ⟨.le (.var 0) (.lit 1), fun s => by
    simp only [exPostWeak, LAssn.eval, LTerm.eval]; exact decide_eq_true_iff.symm⟩

/-- **Positive control (postcondition).** Keeping the precondition `x = y + y` and weakening the
postcondition to `x ≤ 1` (still linear), the triple is valid and derivable with the linear
invariant `true`. -/
theorem exLoop_linDef_control_weak_post :
    LinDef exPre ∧ LinDef exPostWeak ∧ Valid exPre exLoop exPostWeak ∧
    Deriv LinDef exPre exLoop exPostWeak := by
  have hd : Deriv LinDef exPre exLoop exPostWeak :=
    Deriv.conseq (fun _ _ => trivial) exLoop_deriv_linDef_weak_post (fun _ h => h)
  exact ⟨exPre_linDef, exPostWeak_linDef, hoare_sound hd, hd⟩

/-- **Positive control (precondition).** Keeping the postcondition `x ≠ 1` and replacing the
precondition by the linear `x = 0`, the triple is valid and derivable with the linear invariant
`x = 0`. -/
theorem exLoop_linDef_control_pre_zero :
    LinDef (fun s => s 0 = 0) ∧ LinDef exPost ∧ Valid (fun s => s 0 = 0) exLoop exPost ∧
    Deriv LinDef (fun s => s 0 = 0) exLoop exPost :=
  ⟨wlpAdmissibleFor_not_necessary.2.1, exPost_linDef, hoare_sound exLoop_deriv_linDef_pre_zero,
    exLoop_deriv_linDef_pre_zero⟩

/-- The example loop instrumented with an auxiliary variable `g` (variable 2):
`g := y; while 2 ≤ x do (x := x - 2; g := g - 1)`. -/
def exLoopGhost : Com :=
  .seq (.assign 2 (.var 1)) (.whileDo exGuard (.seq exBody (.assign 2 (.sub (.var 2) (.lit 1)))))

/-- The linear invariant `x = g + g` of the instrumented loop. -/
def exGhostInv : Assn := fun s => s 0 = s 2 + s 2

theorem exGhostInv_linDef : LinDef exGhostInv :=
  ⟨.eq (.var 0) (.add (.var 2) (.var 2)), fun s => by
    simp only [exGhostInv, LAssn.eval, LTerm.eval]; exact decide_eq_true_iff.symm⟩

/-- **Positive control (program text).** With the same linear pre- and postcondition, the loop
instrumented with an auxiliary counter `g` is valid and derivable with linear invented
assertions only: midpoint and invariant `x = g + g`, and body midpoint `x = g + g - 2`. -/
theorem exLoopGhost_linDef_control :
    LinDef exPre ∧ LinDef exPost ∧ Valid exPre exLoopGhost exPost ∧
    Deriv LinDef exPre exLoopGhost exPost := by
  have hmid : LinDef (fun s => s 0 = s 2 + s 2 - 2) :=
    ⟨.eq (.var 0) (.sub (.add (.var 2) (.var 2)) (.lit 2)), fun s => by
      simp only [LAssn.eval, LTerm.eval]; exact decide_eq_true_iff.symm⟩
  have hbody : Deriv LinDef (fun s => exGhostInv s ∧ exGuard.eval s = true)
      (.seq exBody (.assign 2 (.sub (.var 2) (.lit 1)))) exGhostInv := by
    refine Deriv.seq hmid ?_ ?_
    · refine Deriv.conseq (fun s h => ?_) (Deriv.assign 0 _ _) (fun _ h => h)
      obtain ⟨h₁, _⟩ := h
      simp only [exGhostInv] at h₁
      simp [upd, AExp.eval]
      omega
    · refine Deriv.conseq (fun s h => ?_) (Deriv.assign 2 _ _) (fun _ h => h)
      simp [exGhostInv, upd, AExp.eval]
      omega
  have hloop : Deriv LinDef exGhostInv
      (.whileDo exGuard (.seq exBody (.assign 2 (.sub (.var 2) (.lit 1))))) exPost := by
    refine Deriv.conseq (fun _ h => h) (Deriv.whileDo exGhostInv_linDef hbody) (fun s h => ?_)
    obtain ⟨h₁, _⟩ := h
    simp only [exGhostInv] at h₁
    simp only [exPost]
    omega
  have hinit : Deriv LinDef exPre (.assign 2 (.var 1)) exGhostInv := by
    refine Deriv.conseq (fun s h => ?_) (Deriv.assign 2 _ _) (fun _ h => h)
    simp only [exPre] at h
    simp [exGhostInv, upd, AExp.eval]
    omega
  have hd : Deriv LinDef exPre exLoopGhost exPost := Deriv.seq exGhostInv_linDef hinit hloop
  exact ⟨exPre_linDef, exPost_linDef, hoare_sound hd, hd⟩

/-! ### `linear_qf_not_expressive_wlp_exLoop` -/

/-- Non-vacuity: the `wlp` is a non-trivial assertion; it contains every state satisfying
`x = y + y` and no state with odd `x ≥ 1`. -/
theorem nonvacuity_wlp_exLoop_nontrivial :
    (∀ s, exPre s → wlp exLoop exPost s) ∧
    (∀ k : Nat, ¬ wlp exLoop exPost (st2 (2 * (k : Int) + 1) 0)) := by
  refine ⟨valid_iff_imp_wlp.mp exLoop_valid, fun k hw => ?_⟩
  have hpost := hw _ (exec_exLoop_odd k 0)
  simp [exPost, st2] at hpost

/-- If `c` runs from `s` to `f`, then `s` satisfies `wlp c Q` iff `f` satisfies `Q`
(by determinism). -/
theorem wlp_iff_of_exec {c : Com} {s f : Store} {Q : Assn} (hx : Exec c s f) :
    wlp c Q s ↔ Q f :=
  ⟨fun h => h f hx, fun h s' hx' => by rw [Exec.deterministic hx' hx]; exact h⟩

/-- Exact value of the `wlp` on the stores `st2 a b`: it holds iff `a ≤ 0` or `a` is even. -/
theorem wlp_exLoop_st2_iff (a b : Int) : wlp exLoop exPost (st2 a b) ↔ (a ≤ 0 ∨ a % 2 = 0) := by
  by_cases ha : a ≤ 1
  · have hg : exGuard.eval (st2 a b) = false := by
      rw [exGuard_eval]; simp [st2]; omega
    have hx : Exec exLoop (st2 a b) (st2 a b) := Exec.whileFalse hg
    rw [wlp_iff_of_exec hx]
    simp only [exPost, st2, ↓reduceIte]
    omega
  · obtain ⟨k, hk⟩ : ∃ k : Nat, a = 2 * (k : Int) ∨ a = 2 * (k : Int) + 1 :=
      ⟨(a / 2).toNat, by omega⟩
    rcases hk with hk | hk
    · subst hk
      rw [wlp_iff_of_exec (exec_exLoop_even k b)]
      simp only [exPost, st2, ↓reduceIte]
      omega
    · subst hk
      rw [wlp_iff_of_exec (exec_exLoop_odd k b)]
      simp only [exPost, st2, ↓reduceIte]
      omega

/-- **Positive control (language dropped).** With all semantic assertions admissible, the same
`wlp` is trivially admissible. -/
theorem wlp_exLoop_anyAssn : AnyAssn (wlp exLoop exPost) := trivial

/-! ### `vcgen_sound` -/

/-- Non-vacuity of `vcgen_sound`: the parity annotation of the example loop has valid side
conditions and the precondition implies the generated precondition. -/
theorem nonvacuity_vcgen_sound :
    VCsValid (vcgen exParityAnn exPost).2 ∧ ∀ s, exPre s → (vcgen exParityAnn exPost).1 s :=
  ⟨exParityAnn_verifies.2.2.1, exParityAnn_verifies.2.2.2⟩

/-- `while false do skip` annotated with the invariant `true`. -/
def falseLoopAnn : ACom := .whileDo (fun _ => True) .ff .skip

/-- Tightness of the side-condition hypothesis of `vcgen_sound`: for `falseLoopAnn` with
`P := true` and `Q := false`, the precondition implies the generated precondition, but
`{true} while false do skip {false}` is invalid (the exit side condition fails). -/
theorem vcgen_sound_vcs_tight :
    (∀ s, (fun _ => True) s → (vcgen falseLoopAnn (fun _ => False)).1 s) ∧
    ¬ Valid (fun _ => True) falseLoopAnn.erase (fun _ => False) := by
  refine ⟨fun _ _ => trivial, fun h => ?_⟩
  exact h (fun _ => 0) (fun _ => 0) trivial (Exec.whileFalse rfl)

/-- Tightness of the precondition hypothesis of `vcgen_sound`: for `x := 1` with `P := true` and
`Q := (x = 0)`, the (empty) list of side conditions is valid, but the triple is invalid. -/
theorem vcgen_sound_pre_tight :
    VCsValid (vcgen (.assign 0 (.lit 1)) (fun s => s 0 = 0)).2 ∧
    ¬ Valid (fun _ => True) (ACom.assign 0 (.lit 1)).erase (fun s => s 0 = 0) := by
  refine ⟨fun φ hφ => by simp [vcgen] at hφ, invalid_assign_triple⟩

/-! ### `vcgen_reachable_noninductive_annotation_fails` -/

/-- The same loop annotated with the linear inductive invariant `x = 0 ∨ x = 2`. -/
def ncAnnLin : ACom :=
  .whileDo (fun s => s 0 = 0 ∨ s 0 = 2) ncGuard (.assign 0 (.add (.var 0) (.lit 2)))

/-- **Positive control.** With the stronger linear annotation `x = 0 ∨ x = 2`, the same triple is
verified by VC generation: the failure is due to the weak annotation `x ≤ 2`, not to the
annotation language. -/
theorem ncAnnLin_verifies :
    ncAnnLin.erase = ncAnn.erase ∧ ncAnnLin.InvsIn LinDef ∧
    VCsValid (vcgen ncAnnLin ncPost).2 ∧ ∀ s, ncPre s → (vcgen ncAnnLin ncPost).1 s := by
  refine ⟨rfl, ⟨⟨.or (.eq (.var 0) (.lit 0)) (.eq (.var 0) (.lit 2)), fun s => ?_⟩, trivial⟩,
    ?_, fun s h => Or.inl h⟩
  · show _ ↔ ((decide (s 0 = 0) || decide (s 0 = 2)) = true)
    rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  · simp only [ncAnnLin, vcgen, VCsValid.cons]
    refine ⟨fun s h hb => ?_, fun s h hb => ?_, fun φ hφ => by simp at hφ⟩
    · rw [ncGuard_eval, decide_eq_true_iff] at hb
      simp [upd, AExp.eval]
      omega
    · rw [ncGuard_eval, decide_eq_false_iff_not] at hb
      simp only [ncPost]
      omega

/-- The annotation `x ≤ 2` is not `k`-inductive for any `k` either: for every `k` there is a run of
`k` loop iterations through stores satisfying the annotation and the guard (starting at the
unreachable `x = 3 - 2k`) whose next store violates the annotation. So `k`-induction does not
rescue this annotation. -/
theorem ncInv_not_k_inductive (k : Nat) :
    ∃ x₀ : Int,
      (∀ i : Nat, i < k →
        ncInv (st2 (x₀ + 2 * i) 0) ∧ ncGuard.eval (st2 (x₀ + 2 * i) 0) = true ∧
        Exec ncBody (st2 (x₀ + 2 * i) 0) (st2 (x₀ + 2 * ((i + 1 : Nat) : Int)) 0)) ∧
      ¬ ncInv (st2 (x₀ + 2 * k) 0) := by
  refine ⟨3 - 2 * k, fun i hi => ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [ncInv, st2, ↓reduceIte]; omega
  · rw [ncGuard_eval]; simp only [st2, ↓reduceIte, decide_eq_true_eq]; omega
  · have h := Exec.assign 0 (.add (.var 0) (.lit 2)) (st2 (3 - 2 * k + 2 * i) 0)
    have e : AExp.eval (.add (.var 0) (.lit 2)) (st2 (3 - 2 * k + 2 * i) 0) =
        3 - 2 * k + 2 * ((i + 1 : Nat) : Int) := by simp [AExp.eval, st2]; omega
    rw [e, upd_st2_zero] at h
    exact h
  · simp only [ncInv, st2, ↓reduceIte]; omega

/-! ### `valid_iff_vcs_annotWlp` -/

/-- Non-vacuity: for the example triple, the `wlp` annotation yields valid side conditions and a
generated precondition implied by `x = y + y`. -/
theorem nonvacuity_vcs_annotWlp :
    VCsValid (vcgen (annotWlp exLoop exPost) exPost).2 ∧
    ∀ s, exPre s → (vcgen (annotWlp exLoop exPost) exPost).1 s :=
  valid_iff_vcs_annotWlp.mp exLoop_valid

/-! ### `vcgen_linear_qf_annotations_incomplete` -/

/-- The example loop annotated with the linear invariant `true`. -/
def exTrueAnn : ACom := .whileDo (fun _ => True) exGuard (.assign 0 (.sub (.var 0) (.lit 2)))

/-- The example loop annotated with the linear invariant `x = 0`. -/
def exZeroAnn : ACom := .whileDo (fun s => s 0 = 0) exGuard (.assign 0 (.sub (.var 0) (.lit 2)))

/-- Non-vacuity: the setup holds and a linear annotation erasing to the loop exists. -/
theorem nonvacuity_vcgen_linear_qf_incomplete :
    LinDef exPre ∧ LinDef exPost ∧ Valid exPre exLoop exPost ∧
    exTrueAnn.erase = exLoop ∧ exTrueAnn.InvsIn LinDef :=
  ⟨exPre_linDef, exPost_linDef, exLoop_valid, rfl,
    ⟨⟨.tt, fun _ => by simp [LAssn.eval]⟩, trivial⟩⟩

/-- Tightness of `a.erase = exLoop`: the annotated program `skip` has linear annotations
(vacuously), and `exPre` implies its generated precondition `exPost` with no side conditions;
it does not erase to the loop. -/
theorem vcgen_erase_hyp_tight :
    ACom.skip.erase ≠ exLoop ∧ ACom.skip.InvsIn LinDef ∧
    VCsValid (vcgen .skip exPost).2 ∧ ∀ s, exPre s → (vcgen .skip exPost).1 s := by
  refine ⟨by decide, trivial, fun φ hφ => by simp [vcgen] at hφ, fun s h => ?_⟩
  simp only [vcgen, exPost]
  simp only [exPre] at h
  omega

/-- Tightness of `a.InvsIn LinDef`: the parity annotation erases to the loop and verifies it, and
its invariant is not linearly definable. -/
theorem vcgen_invsIn_hyp_tight :
    exParityAnn.erase = exLoop ∧ ¬ exParityAnn.InvsIn LinDef ∧
    VCsValid (vcgen exParityAnn exPost).2 ∧ ∀ s, exPre s → (vcgen exParityAnn exPost).1 s :=
  ⟨rfl, invsIn_example_neg, exParityAnn_verifies.2.2.1, exParityAnn_verifies.2.2.2⟩

/-- **Positive control (postcondition).** Keeping `x = y + y` and weakening the postcondition to
the linear `x ≤ 1`, the loop annotated with `true` is verified. -/
theorem vcgen_linDef_control_weak_post :
    LinDef exPre ∧ LinDef exPostWeak ∧ exTrueAnn.erase = exLoop ∧ exTrueAnn.InvsIn LinDef ∧
    VCsValid (vcgen exTrueAnn exPostWeak).2 ∧ ∀ s, exPre s → (vcgen exTrueAnn exPostWeak).1 s := by
  refine ⟨exPre_linDef, exPostWeak_linDef, rfl, nonvacuity_vcgen_linear_qf_incomplete.2.2.2.2,
    ?_, fun _ _ => trivial⟩
  simp only [exTrueAnn, vcgen, VCsValid.cons]
  refine ⟨fun _ _ _ => trivial, fun s _ hb => ?_, fun φ hφ => by simp at hφ⟩
  rw [exGuard_eval, decide_eq_false_iff_not] at hb
  simp only [exPostWeak]
  omega

/-- **Positive control (precondition).** Keeping `x ≠ 1` and replacing the precondition by the
linear `x = 0`, the loop annotated with `x = 0` is verified. -/
theorem vcgen_linDef_control_pre_zero :
    LinDef (fun s => s 0 = 0) ∧ LinDef exPost ∧ exZeroAnn.erase = exLoop ∧
    exZeroAnn.InvsIn LinDef ∧
    VCsValid (vcgen exZeroAnn exPost).2 ∧ ∀ s, s 0 = 0 → (vcgen exZeroAnn exPost).1 s := by
  refine ⟨wlpAdmissibleFor_not_necessary.2.1, exPost_linDef, rfl,
    ⟨wlpAdmissibleFor_not_necessary.2.1, trivial⟩, ?_, fun _ h => h⟩
  simp only [exZeroAnn, vcgen, VCsValid.cons]
  refine ⟨fun s h0 hb => ?_, fun s h0 _ => ?_, fun φ hφ => by simp at hφ⟩
  · rw [exGuard_eval, decide_eq_true_iff] at hb
    omega
  · simp only [exPost]
    omega

/-- The instrumented loop annotated with the linear invariant `x = g + g`. -/
def exGhostAnn : ACom :=
  .seq (.assign 2 (.var 1))
    (.whileDo exGhostInv exGuard
      (.seq (.assign 0 (.sub (.var 0) (.lit 2))) (.assign 2 (.sub (.var 2) (.lit 1)))))

/-- **Positive control (program text).** With the same linear pre- and postcondition, the loop
instrumented with an auxiliary counter `g` is verified by VC generation with the linear
invariant `x = g + g`. -/
theorem vcgen_ghost_linDef_control :
    LinDef exPre ∧ LinDef exPost ∧ exGhostAnn.erase = exLoopGhost ∧ exGhostAnn.InvsIn LinDef ∧
    VCsValid (vcgen exGhostAnn exPost).2 ∧ ∀ s, exPre s → (vcgen exGhostAnn exPost).1 s := by
  refine ⟨exPre_linDef, exPost_linDef, rfl, ⟨trivial, exGhostInv_linDef, trivial, trivial⟩,
    ?_, fun s h => ?_⟩
  · intro φ hφ
    simp only [exGhostAnn, vcgen, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hφ
    rcases hφ with rfl | rfl
    · intro s h _
      simp only [exGhostInv] at h
      simp [exGhostInv, upd, AExp.eval]
      omega
    · intro s h hb
      rw [exGuard_eval, decide_eq_false_iff_not] at hb
      simp only [exGhostInv] at h
      simp only [exPost]
      omega
  · simp only [exPre] at h
    simp [exGhostAnn, vcgen, exGhostInv, upd, AExp.eval]
    omega

/-! ### `total_sound_of_bounded_variant` -/

/-- Non-vacuity: a total-correctness derivation with a bounded variant. -/
theorem nonvacuity_total_sound :
    TDeriv true (fun s => 0 ≤ s 0) countdown (fun s => s 0 = 0) := countdown_tderiv

/-! ### `LAssn.eventually_const_on_affineLine`, `not_linDef_of_alternating_on_affineLine` -/

/-- Non-vacuity: the diagonal is an affine line, and along it the parity assertion is true and
false beyond every bound (the hypotheses of `not_linDef_of_alternating_on_affineLine` hold
together). -/
theorem nonvacuity_eventually_const_and_alternating :
    AffineLine (fun n => st2 n n) ∧
    ∀ N : Int, ∃ n n', N ≤ n ∧ N ≤ n' ∧ exParityInv (st2 n n) ∧ ¬ exParityInv (st2 n' n') := by
  refine ⟨affineLine_diag, fun N => ?_⟩
  refine ⟨2 * (N.toNat : Int), 2 * (N.toNat : Int) + 1, by omega, by omega, ?_, ?_⟩
  · simp [exParityInv, st2]
  · simp [exParityInv, st2]

/-- Tightness of the affine-line hypothesis: along the (non-affine) parity family
`n ↦ (fun _ => n % 2)`, the linear formula `x = 0` is not eventually constant. -/
theorem eventually_const_needs_affine :
    ¬ ∃ N : Int, ∃ bv : Bool, ∀ n, N ≤ n →
      (LAssn.eq (.var 0) (.lit 0)).eval ((fun n : Int => fun _ : Nat => n % 2) n) = bv := by
  rintro ⟨N, bv, h⟩
  have h₁ := h (2 * max N 0) (by omega)
  have h₂ := h (2 * max N 0 + 1) (by omega)
  have e₁ : (2 * max N 0) % 2 = 0 := by omega
  have e₂ : (2 * max N 0 + 1) % 2 = 1 := by omega
  simp only [LAssn.eval, LTerm.eval, e₁, e₂] at h₁ h₂
  rw [← h₁] at h₂
  exact absurd h₂ (by decide)

/-- Tightness of the alternation hypothesis: along the affine diagonal, the assertion
`x = y + y` does not alternate beyond every bound (it holds on the diagonal only at `0`), and it
is linearly definable. -/
theorem alternating_hyp_tight :
    AffineLine (fun n => st2 n n) ∧ LinDef exPre ∧
    ¬ (∀ N : Int, ∃ n n', N ≤ n ∧ N ≤ n' ∧ exPre (st2 n n) ∧ ¬ exPre (st2 n' n')) := by
  refine ⟨affineLine_diag, exPre_linDef, fun h => ?_⟩
  obtain ⟨n, _, hn, _, hP, _⟩ := h 1
  simp [exPre, st2] at hP
  omega

/-- Tightness of the affine-line hypothesis of `not_linDef_of_alternating_on_affineLine`: along
the non-affine parity family, the linearly definable assertion `x = 0` alternates beyond every
bound. -/
theorem alternating_needs_affine :
    (∀ N : Int, ∃ n n', N ≤ n ∧ N ≤ n' ∧
      (fun s : Store => s 0 = 0) ((fun n : Int => fun _ : Nat => n % 2) n) ∧
      ¬ (fun s : Store => s 0 = 0) ((fun n : Int => fun _ : Nat => n % 2) n')) ∧
    LinDef (fun s : Store => s 0 = 0) := by
  refine ⟨fun N => ⟨2 * max N 0, 2 * max N 0 + 1, by omega, by omega, ?_, ?_⟩, ?_⟩
  · show (2 * max N 0) % 2 = 0; omega
  · show ¬ (2 * max N 0 + 1) % 2 = 0; omega
  · exact ⟨.eq (.var 0) (.lit 0), fun s => by
      simp only [LAssn.eval, LTerm.eval]; exact decide_eq_true_iff.symm⟩

end Toy.Hoare
