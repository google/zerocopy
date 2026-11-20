import ToyHoare.Logic
import ToyHoare.Linear
import ToyHoare.Incomplete
import ToyHoare.VC
import ToyHoare.Total

/-!
# Definition examples

For each definition, at least one intended instance it admits (positive example) and one
instance it must reject (negative example), all fully proved.
-/

namespace Toy.Hoare

/-! ### `upd` -/

theorem upd_example_pos : upd (fun _ => 0) 0 5 0 = 5 := by decide

theorem upd_example_neg : upd (fun _ => 0) 0 5 1 ≠ 5 := by decide

/-! ### `AExp.eval` -/

/-- `x + 2 * y` at `x = 3`, `y = 4` is `11`. -/
theorem aexp_eval_example_pos :
    AExp.eval (.add (.var 0) (.mul (.lit 2) (.var 1))) (st2 3 4) = 11 := by decide

theorem aexp_eval_example_neg :
    AExp.eval (.add (.var 0) (.mul (.lit 2) (.var 1))) (st2 3 4) ≠ 14 := by decide

/-! ### `BExp.eval` -/

theorem bexp_eval_example_pos : (BExp.and (.lt (.var 0) (.lit 2)) (.not (.eq (.var 0) (.var 1)))).eval
    (st2 1 0) = true := by decide

theorem bexp_eval_example_neg : (BExp.lt (.var 0) (.lit 2)).eval (st2 2 0) = false := by decide

/-! ### `Exec` -/

/-- Countdown loop `while 0 < x do x := x - 1`. -/
def countdown : Com := .whileDo (.lt (.lit 0) (.var 0)) (.assign 0 (.sub (.var 0) (.lit 1)))

/-- Running the countdown from `x = 2` terminates with `x = 0`. -/
theorem exec_example_pos : Exec countdown (st2 2 0) (st2 0 0) := by
  have step : ∀ a : Int, Exec (.assign 0 (.sub (.var 0) (.lit 1))) (st2 a 0) (st2 (a - 1) 0) := by
    intro a
    have h := Exec.assign 0 (.sub (.var 0) (.lit 1)) (st2 a 0)
    have e : AExp.eval (.sub (.var 0) (.lit 1)) (st2 a 0) = a - 1 := by simp [AExp.eval, st2]
    rwa [e, upd_st2_zero] at h
  refine Exec.whileTrue (by decide) (step 2) ?_
  refine Exec.whileTrue (by decide) (step 1) ?_
  exact Exec.whileFalse (by decide)

/-- An assignment cannot leave the store unchanged when it changes the assigned variable. -/
theorem exec_example_neg : ¬ Exec (.assign 0 (.lit 1)) (fun _ => 0) (fun _ => 0) := by
  intro h
  have := congrFun (Exec.deterministic h (Exec.assign 0 (.lit 1) (fun _ => 0))) 0
  simp [upd, AExp.eval] at this

/-- A diverging loop has no final state. -/
theorem exec_example_neg_diverge (s s' : Store) : ¬ Exec (.whileDo .tt .skip) s s' :=
  exec_while_tt_diverges

/-! ### `Valid` -/

/-- Partial correctness admits divergence: a diverging loop satisfies any postcondition. -/
theorem valid_example_pos_diverge : Valid (fun _ => True) (.whileDo .tt .skip) (fun _ => False) :=
  fun _ _ _ hx => absurd hx exec_while_tt_diverges

theorem valid_example_pos : Valid (fun s => s 0 = 2) countdown (fun s => s 0 = 0) := by
  intro s s' hs hx
  have hd : Deriv AnyAssn (fun s => 0 ≤ s 0) countdown (fun s => s 0 = 0) := by
    refine Deriv.conseq (fun _ h => h) (Deriv.whileDo trivial ?_) (fun s h => ?_)
    · refine Deriv.conseq (fun s h => ?_) (Deriv.assign 0 _ _) (fun _ h => h)
      obtain ⟨h₁, h₂⟩ := h
      have h₂' : 0 < s 0 := of_decide_eq_true h₂
      simp only [upd_same, AExp.eval]
      omega
    · obtain ⟨h₁, h₂⟩ := h
      have h₂' : ¬ (0 < s 0) := of_decide_eq_false h₂
      omega
  have hs' : s 0 = 2 := hs
  exact hoare_sound hd s s' (show 0 ≤ s 0 by omega) hx

/-- The canonical invalid triple: `{true} x := 1 {x = 0}`. -/
theorem invalid_assign_triple :
    ¬ Valid (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0) := by
  intro h
  have := h (fun _ => 0) _ trivial (Exec.assign 0 (.lit 1) _)
  simp [AExp.eval] at this

/-! ### `wlp` -/

theorem wlp_example_pos (s : Store) : wlp (.assign 0 (.lit 1)) (fun s => s 0 = 1) s := by
  intro s' hx
  cases hx
  simp [AExp.eval]

theorem wlp_example_neg (s : Store) : ¬ wlp (.assign 0 (.lit 1)) (fun s => s 0 = 0) s := by
  intro h
  have := h _ (Exec.assign 0 (.lit 1) s)
  simp [AExp.eval] at this

/-! ### `Deriv` and `AnyAssn` -/

/-- `AnyAssn` admits every assertion (it has no negative example by design). -/
theorem anyAssn_example_pos : AnyAssn exParityInv := trivial

/-- A derivation in the linear logic. -/
theorem deriv_example_pos : Deriv LinDef (fun _ => True) exLoop exPostWeak :=
  exLoop_deriv_linDef_weak_post

/-- Even with no admissible assertions at all, loop- and sequence-free programs are derivable. -/
theorem deriv_example_pos_empty_L :
    Deriv (fun _ => False) (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 1) :=
  Deriv.conseq (fun s _ => by simp [AExp.eval]) (Deriv.assign 0 _ _) (fun _ h => h)

theorem deriv_example_neg :
    ¬ Deriv AnyAssn (fun _ => True) (.assign 0 (.lit 1)) (fun s => s 0 = 0) :=
  fun h => invalid_assign_triple (hoare_sound h)

/-- With no admissible assertions, no sequence is derivable, even a valid one: `L` really
constrains the intermediate assertion of `seq`. -/
theorem deriv_example_neg_empty_L :
    ¬ Deriv (fun _ => False) (fun _ => True) (.seq .skip .skip) (fun _ => True) := by
  suffices ∀ {P Q : Assn} {c₁ c₂ : Com}, ¬ Deriv (fun _ => False) P (.seq c₁ c₂) Q from this
  intro P Q c₁ c₂ h
  generalize hc : Com.seq c₁ c₂ = c at h
  induction h with
  | seq hR => exact hR
  | conseq _ _ _ ih => exact ih hc
  | skip => cases hc
  | assign => cases hc
  | cond => cases hc
  | whileDo => cases hc

/-! ### `LTerm.eval`, `LAssn.eval`, `LinDef`, `AffineLine` -/

theorem lterm_eval_example_pos : (LTerm.add (.var 0) (.smul 3 (.var 1))).eval (st2 1 2) = 7 := by
  decide

theorem lterm_eval_example_neg : (LTerm.add (.var 0) (.smul 3 (.var 1))).eval (st2 1 2) ≠ 9 := by
  decide

theorem lassn_eval_example_pos : exPreL.eval (st2 4 2) = true := by decide

theorem lassn_eval_example_neg : exPreL.eval (st2 3 2) = false := by decide

theorem linDef_example_pos : LinDef exPre := exPre_linDef

/-- Parity is rejected by `LinDef`. -/
theorem linDef_example_neg : ¬ LinDef (fun s => s 0 % 2 = 0) := parity_not_linDef

theorem affineLine_example_pos : AffineLine (fun n => st2 n n) := affineLine_diag

/-- The parity family `n ↦ (fun _ => n % 2)` is not an affine line. -/
theorem affineLine_example_neg : ¬ AffineLine (fun n : Int => fun _ : Nat => n % 2) := by
  intro h
  obtain ⟨a, b, hab⟩ := h 0
  have h0 := hab 0
  have h1 := hab 1
  have h2 := hab 2
  simp at h0 h1 h2
  omega

/-! ### `ACom.erase`, `vcgen`, `VCsValid`, `annotWlp`, `HeadReach`, `ACom.InvsIn` -/

theorem erase_example_pos : exParityAnn.erase = exLoop := rfl

theorem erase_example_neg : ncAnn.erase ≠ exLoop := by decide

theorem vcgen_example_pos :
    (vcgen (.assign 0 (.lit 1)) (fun s => s 0 = 1)).2 = [] ∧
    ∀ s, (vcgen (.assign 0 (.lit 1)) (fun s => s 0 = 1)).1 s := by
  refine ⟨rfl, fun s => ?_⟩
  simp [vcgen, AExp.eval]

theorem vcgen_example_neg (s : Store) : ¬ (vcgen (.assign 0 (.lit 1)) (fun s => s 0 = 0)).1 s := by
  simp [vcgen, AExp.eval]

theorem vcsValid_example_pos : VCsValid [fun s => s 0 = s 0] := by
  intro φ hφ s
  simp only [List.mem_singleton] at hφ
  subst hφ
  trivial

theorem vcsValid_example_neg : ¬ VCsValid [fun s => s 0 = 0] := by
  intro h
  have := h _ (List.mem_singleton.mpr rfl) (fun _ => 1)
  simp at this

theorem annotWlp_example_pos :
    annotWlp exLoop exPost =
      .whileDo (wlp exLoop exPost) exGuard (annotWlp exBody (wlp exLoop exPost)) := rfl

/-- The `wlp` annotation of the example loop is not a linear annotation. -/
theorem annotWlp_example_neg : ¬ (annotWlp exLoop exPost).InvsIn LinDef := by
  intro h
  exact linear_qf_not_expressive_wlp_exLoop h.1

theorem headReach_example_pos : HeadReach ncPre ncGuard ncBody (upd (fun _ => 0) 0 2) := by
  have h0 : HeadReach ncPre ncGuard ncBody (fun _ => 0) := HeadReach.init rfl
  have hx := Exec.assign 0 (.add (.var 0) (.lit 2)) (fun _ => 0)
  exact HeadReach.step h0 (by decide) hx

theorem headReach_example_neg : ¬ HeadReach ncPre ncGuard ncBody (fun _ => 1) := by
  intro h
  have := headReach_nc h
  simp at this

theorem invsIn_example_pos : exParityAnn.InvsIn AnyAssn := ⟨trivial, trivial⟩

theorem invsIn_example_neg : ¬ exParityAnn.InvsIn LinDef := fun h => parity_not_linDef h.1

/-! ### `TValid`, `TDeriv` -/

/-- Total-correctness derivation of `[0 ≤ x] countdown [x = 0]` with variant `x`. -/
theorem countdown_tderiv : TDeriv true (fun s => 0 ≤ s 0) countdown (fun s => s 0 = 0) := by
  refine TDeriv.conseq (fun _ h => h) (TDeriv.whileDo (fun s => s 0) (fun n => ?_) ?_) (fun s h => ?_)
  · refine TDeriv.conseq (fun s h => ?_) (TDeriv.assign 0 _ (fun s => 0 ≤ s 0 ∧ s 0 < n))
      (fun _ h => h)
    obtain ⟨h₁, h₂, h₃⟩ := h
    have h₂' : 0 < s 0 := of_decide_eq_true h₂
    simp only [upd_same, AExp.eval]
    omega
  · intro _ s h _; exact h
  · obtain ⟨h₁, h₂⟩ := h
    have h₂' : ¬ (0 < s 0) := of_decide_eq_false h₂
    omega

theorem tvalid_example_pos : TValid (fun s => 0 ≤ s 0) countdown (fun s => s 0 = 0) :=
  total_sound_of_bounded_variant countdown_tderiv

/-- Total correctness rejects divergence (contrast `valid_example_pos_diverge`). -/
theorem tvalid_example_neg : ¬ TValid (fun _ => True) (.whileDo .tt .skip) (fun _ => True) := by
  intro h
  obtain ⟨s', hx, _⟩ := h (fun _ => 0) trivial
  exact exec_while_tt_diverges hx

theorem tderiv_example_pos : TDeriv true (fun s => 0 ≤ s 0) countdown (fun s => s 0 = 0) :=
  countdown_tderiv

theorem tderiv_example_neg : ¬ TDeriv true (fun _ => True) (.whileDo .tt .skip) (fun _ => True) :=
  fun h => tvalid_example_neg (total_sound_of_bounded_variant h)

/-! ### `WlpInvented`, `WlpAdmissibleFor` -/

/-- The parity invariant `x % 2 = 0` and `wlp exLoop exPost` are different assertions: they
disagree at `x = -1` (no iteration runs, and `-1 ≠ 1`, but `-1` is odd). -/
theorem exParityInv_ne_wlp_exLoop : exParityInv ≠ wlp exLoop exPost := by
  intro heq
  have hw : wlp exLoop exPost (st2 (-1) 0) := by
    intro s' hx
    cases hx with
    | whileFalse _ => simp [exPost, st2]
    | whileTrue hb _ _ => rw [exGuard_eval] at hb; simp [st2] at hb
  have hp : ¬ exParityInv (st2 (-1) 0) := by simp [exParityInv, st2]
  rw [← heq] at hw
  exact hp hw

/-- The invariant invented for the example loop is its `wlp`. -/
theorem wlpInvented_example_pos : WlpInvented exLoop exPost (wlp exLoop exPost) := Or.inl rfl

/-- `WlpInvented` is a specific set of `wlp`s, not "any invariant": the (valid, inductive) parity
invariant of the example loop is not in it. -/
theorem wlpInvented_example_neg : ¬ WlpInvented exLoop exPost exParityInv := by
  rintro (h | h)
  · exact exParityInv_ne_wlp_exLoop h
  · exact h

/-- The `wlp` of the countdown loop for `x = 0` is `0 ≤ x`. -/
theorem wlp_countdown_iff (s : Store) : wlp countdown (fun s => s 0 = 0) s ↔ 0 ≤ s 0 := by
  constructor
  · intro hw
    by_cases h0 : 0 ≤ s 0
    · exact h0
    · have hb : (BExp.lt (.lit 0) (.var 0)).eval s = false := by
        rw [show (BExp.lt (.lit 0) (.var 0)).eval s = decide (0 < s 0) from rfl,
          decide_eq_false_iff_not]
        omega
      have hs0 := hw s (Exec.whileFalse hb)
      omega
  · intro h0 s' hx
    exact (total_sound_of_bounded_variant countdown_tderiv).valid s s' h0 hx

/-- Command-local admissibility holds for the countdown loop with the non-trivial postcondition
`x = 0` and linear invariants: its only invented assertion is `wlp countdown (x = 0)`, i.e.
`0 ≤ x`. -/
theorem wlpAdmissibleFor_example_pos : WlpAdmissibleFor LinDef countdown (fun s => s 0 = 0) := by
  rintro R (h | h)
  · subst h
    refine ⟨.le (.lit 0) (.var 0), fun s => (wlp_countdown_iff s).trans ?_⟩
    rw [show (LAssn.le (.lit 0) (.var 0)).eval s = decide (0 ≤ s 0) from rfl, decide_eq_true_iff]
  · exact h.elim

/-- Command-local admissibility fails for the example loop with linear invariants. -/
theorem wlpAdmissibleFor_example_neg : ¬ WlpAdmissibleFor LinDef exLoop exPost :=
  fun h => linear_qf_not_expressive_wlp_exLoop (h _ (Or.inl rfl))

end Toy.Hoare
