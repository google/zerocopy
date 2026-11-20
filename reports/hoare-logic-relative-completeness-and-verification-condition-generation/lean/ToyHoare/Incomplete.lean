import ToyHoare.Logic
import ToyHoare.Linear

/-!
# Expressiveness matters: a valid triple with no divisibility-free linear loop invariant

The triple `{x = y + y} while 2 ≤ x do x := x - 2 {x ≠ 1}` (with `x` = variable 0 and
`y` = variable 1) is valid, its pre- and postcondition are quantifier-free linear formulas, and it
is derivable with semantic assertions (invariant "x is even"). But every inductive invariant for it
must separate even from odd values of `x` along the line `x = y = n`, which no divisibility-free
quantifier-free linear formula can do (`LAssn.eventually_const_on_affineLine`). Hence it has no
derivation in which loop invariants and intermediate assertions are restricted to that language,
and the `wlp` of the loop for `x ≠ 1` is not definable in it. These statements concern this fixed
program text: an instrumented variant with an auxiliary variable is derivable with linear
invariants (`exLoopGhost_linDef_control` in `ToyHoare.Witnesses`).
-/

namespace Toy.Hoare

/-- Guard `2 ≤ x` (with `x` = variable 0). -/
def exGuard : BExp := .le (.lit 2) (.var 0)

/-- Loop body `x := x - 2`. -/
def exBody : Com := .assign 0 (.sub (.var 0) (.lit 2))

/-- The example loop `while 2 ≤ x do x := x - 2`. -/
def exLoop : Com := .whileDo exGuard exBody

/-- Precondition `x = y + y` (with `y` = variable 1): `x` is even, witnessed by `y`. -/
def exPre : Assn := fun s => s 0 = s 1 + s 1

/-- Postcondition `x ≠ 1`. -/
def exPost : Assn := fun s => s 0 ≠ 1

/-- The precondition as a quantifier-free linear formula. -/
def exPreL : LAssn := .eq (.var 0) (.add (.var 1) (.var 1))

/-- The postcondition as a quantifier-free linear formula. -/
def exPostL : LAssn := .not (.eq (.var 0) (.lit 1))

theorem exPre_linDef : LinDef exPre :=
  ⟨exPreL, fun s => by
    simp only [exPre, exPreL, LAssn.eval, LTerm.eval]; exact decide_eq_true_iff.symm⟩

theorem exPost_linDef : LinDef exPost :=
  ⟨exPostL, fun s => by
    simp only [exPost, exPostL, LAssn.eval, LTerm.eval, Bool.not_eq_true']
    exact decide_eq_false_iff_not.symm⟩

/-- Stores with `x = a`, `y = b`, all other variables `0`. -/
def st2 (a b : Int) : Store := fun i => if i = 0 then a else if i = 1 then b else 0

theorem upd_st2_zero (a b v : Int) : upd (st2 a b) 0 v = st2 v b := by
  funext i
  by_cases h : i = 0 <;> simp [upd, st2, h]

theorem exGuard_eval (s : Store) : exGuard.eval s = decide (2 ≤ s 0) := rfl

theorem exec_exBody_st2 (a b : Int) : Exec exBody (st2 a b) (st2 (a - 2) b) := by
  have h := Exec.assign 0 (.sub (.var 0) (.lit 2)) (st2 a b)
  have e : AExp.eval (.sub (.var 0) (.lit 2)) (st2 a b) = a - 2 := by simp [AExp.eval, st2]
  rw [e, upd_st2_zero] at h
  exact h

/-- Inversion of the while rule through any number of consequence steps. -/
theorem Deriv.whileDo_inv {L : Assn → Prop} {P Q : Assn} {b : BExp} {c : Com}
    (h : Deriv L P (.whileDo b c) Q) :
    ∃ I, L I ∧ (∀ s, P s → I s) ∧ Valid (fun s => I s ∧ b.eval s = true) c I ∧
      (∀ s, I s → b.eval s = false → Q s) := by
  generalize hw : Com.whileDo b c = w at h
  induction h with
  | whileDo hI hbody =>
    cases hw
    exact ⟨_, hI, fun _ h => h, hoare_sound hbody, fun _ h hb => ⟨h, hb⟩⟩
  | conseq hP _ hQ ih =>
    obtain ⟨I, hL, hPI, hv, hex⟩ := ih hw
    exact ⟨I, hL, fun s h => hPI s (hP s h), hv, fun s h hb => hQ s (hex s h hb)⟩
  | skip => cases hw
  | assign => cases hw
  | seq => cases hw
  | cond => cases hw

/-- Any inductive invariant of the example loop (containing the precondition, preserved by the
body when the guard holds, implying the postcondition on exit) separates parities on the diagonal
`x = y = n`: it holds at every even `n ≥ 0` and fails at every odd `n ≥ 1`. -/
theorem exLoop_invariant_parity {I : Assn} (hP : ∀ s, exPre s → I s)
    (hb : Valid (fun s => I s ∧ exGuard.eval s = true) exBody I)
    (hx : ∀ s, I s → exGuard.eval s = false → exPost s) :
    (∀ k : Nat, I (st2 (2 * k) (2 * k))) ∧ (∀ k : Nat, ¬ I (st2 (2 * k + 1) (2 * k + 1))) := by
  -- Downward closure along the loop: from `I (st2 a b)` and `2j ≤ a`, get `I (st2 (a - 2j) b)`.
  have down : ∀ (j : Nat) (a b : Int), I (st2 a b) → 2 * (j : Int) ≤ a → I (st2 (a - 2 * j) b) := by
    intro j
    induction j with
    | zero => intro a b h _; simpa using h
    | succ j ih =>
      intro a b h hj
      have hg : exGuard.eval (st2 a b) = true := by
        rw [exGuard_eval]; simp [st2]; omega
      have h' := hb _ _ ⟨h, hg⟩ (exec_exBody_st2 a b)
      have h'' := ih (a - 2) b h' (by omega)
      have e : a - 2 - 2 * (j : Int) = a - 2 * ((j + 1 : Nat) : Int) := by omega
      rwa [e] at h''
  -- No odd value of `x` is in `I`.
  have odd : ∀ (k : Nat) (b : Int), ¬ I (st2 (2 * k + 1) b) := by
    intro k
    induction k with
    | zero =>
      intro b h
      have hg : exGuard.eval (st2 (2 * ((0 : Nat) : Int) + 1) b) = false := by
        rw [exGuard_eval]; simp [st2]
      exact hx _ h hg (by simp [st2])
    | succ k ih =>
      intro b h
      have hg : exGuard.eval (st2 (2 * ((k + 1 : Nat) : Int) + 1) b) = true := by
        rw [exGuard_eval]; simp [st2]; omega
      have h' := hb _ _ ⟨h, hg⟩ (exec_exBody_st2 _ b)
      have e : 2 * ((k + 1 : Nat) : Int) + 1 - 2 = 2 * (k : Int) + 1 := by omega
      rw [e] at h'
      exact ih b h'
  refine ⟨fun k => ?_, fun k => odd k _⟩
  have hstart : I (st2 (4 * k) (2 * k)) := hP _ (by simp [exPre, st2]; omega)
  have h := down k (4 * k) (2 * k) hstart (by omega)
  have e : 4 * (k : Int) - 2 * k = 2 * k := by omega
  rwa [e] at h

/-- The diagonal `n ↦ st2 n n` is an affine line of stores. -/
theorem affineLine_diag : AffineLine (fun n => st2 n n) := by
  intro i
  by_cases h0 : i = 0
  · exact ⟨1, 0, fun n => by simp [st2, h0]⟩
  · by_cases h1 : i = 1
    · exact ⟨1, 0, fun n => by simp [st2, h1]⟩
    · exact ⟨0, 0, fun n => by simp [st2, h0, h1]⟩

/-- From an even `x = 2k ≥ 0` the example loop terminates with `x = 0`. -/
theorem exec_exLoop_even (k : Nat) (b : Int) :
    Exec exLoop (st2 (2 * (k : Int)) b) (st2 0 b) := by
  induction k with
  | zero =>
    have heq : 2 * ((0 : Nat) : Int) = 0 := by omega
    rw [heq]
    have hg : exGuard.eval (st2 0 b) = false := by
      rw [exGuard_eval]; simp [st2]
    exact Exec.whileFalse (c := exBody) hg
  | succ k ih =>
    have hg : exGuard.eval (st2 (2 * ((k + 1 : Nat) : Int)) b) = true := by
      rw [exGuard_eval]; simp [st2]; omega
    have hstep := exec_exBody_st2 (2 * ((k + 1 : Nat) : Int)) b
    have heq : 2 * ((k + 1 : Nat) : Int) - 2 = 2 * (k : Int) := by omega
    rw [heq] at hstep
    exact Exec.whileTrue hg hstep ih

/-- From an odd `x = 2k + 1 ≥ 1` the example loop terminates with `x = 1`. -/
theorem exec_exLoop_odd (k : Nat) (b : Int) :
    Exec exLoop (st2 (2 * (k : Int) + 1) b) (st2 1 b) := by
  induction k with
  | zero =>
    have heq : 2 * ((0 : Nat) : Int) + 1 = 1 := by omega
    rw [heq]
    have hg : exGuard.eval (st2 1 b) = false := by
      rw [exGuard_eval]; simp [st2]
    exact Exec.whileFalse (c := exBody) hg
  | succ k ih =>
    have hg : exGuard.eval (st2 (2 * ((k + 1 : Nat) : Int) + 1) b) = true := by
      rw [exGuard_eval]; simp [st2]; omega
    have hstep := exec_exBody_st2 (2 * ((k + 1 : Nat) : Int) + 1) b
    have heq : 2 * ((k + 1 : Nat) : Int) + 1 - 2 = 2 * (k : Int) + 1 := by omega
    rw [heq] at hstep
    exact Exec.whileTrue hg hstep ih

/-- No divisibility-free quantifier-free linear formula is an inductive invariant of the example
loop for the example pre- and postcondition. -/
theorem exLoop_no_linDef_invariant :
    ¬ ∃ I : Assn, LinDef I ∧ (∀ s, exPre s → I s) ∧
      Valid (fun s => I s ∧ exGuard.eval s = true) exBody I ∧
      (∀ s, I s → exGuard.eval s = false → exPost s) := by
  rintro ⟨I, hL, hP, hb, hx⟩
  obtain ⟨hev, hod⟩ := exLoop_invariant_parity hP hb hx
  refine not_linDef_of_alternating_on_affineLine (fun n => st2 n n) affineLine_diag (fun N => ?_) hL
  refine ⟨2 * (N.toNat : Int), 2 * (N.toNat : Int) + 1, by omega, by omega, hev _, hod _⟩

/-- The semantic invariant "x is even". -/
def exParityInv : Assn := fun s => s 0 % 2 = 0

/-- **Positive control.** With semantic assertions the example triple is derivable, using the
invariant "x is even". -/
theorem exLoop_deriv_anyAssn : Deriv AnyAssn exPre exLoop exPost := by
  refine Deriv.conseq (P' := exParityInv) (fun s h => ?_) (Deriv.whileDo trivial ?_) (fun s h => ?_)
  · simp only [exPre] at h; simp only [exParityInv]; omega
  · refine Deriv.conseq (fun s h => ?_) (Deriv.assign 0 _ exParityInv) (fun _ h => h)
    obtain ⟨h₁, _⟩ := h
    simp only [exParityInv] at h₁
    simp [exParityInv, upd, AExp.eval]
    omega
  · obtain ⟨h₁, h₂⟩ := h
    simp only [exParityInv] at h₁
    simp only [exPost]
    omega

theorem exLoop_valid : Valid exPre exLoop exPost := hoare_sound exLoop_deriv_anyAssn

/-- **Expressiveness matters (Hoare logic).** The triple `{x = y + y} while 2 ≤ x do x := x - 2
{x ≠ 1}`, whose pre- and postcondition are quantifier-free linear, is valid, but it has no
derivation in which every loop invariant and intermediate assertion is definable in
divisibility-free quantifier-free linear integer arithmetic (consequence premises remain
semantic). -/
theorem linear_qf_hoare_incomplete :
    LinDef exPre ∧ LinDef exPost ∧ Valid exPre exLoop exPost ∧ ¬ Deriv LinDef exPre exLoop exPost := by
  refine ⟨exPre_linDef, exPost_linDef, exLoop_valid, fun h => ?_⟩
  obtain ⟨I, hL, hP, hb, hx⟩ := Deriv.whileDo_inv h
  exact exLoop_no_linDef_invariant ⟨I, hL, hP, hb, hx⟩

/-- **Non-expressiveness.** The weakest liberal precondition of the example loop for the
postcondition `x ≠ 1` is not definable in divisibility-free quantifier-free linear integer
arithmetic. -/
theorem linear_qf_not_expressive_wlp_exLoop : ¬ LinDef (wlp exLoop exPost) := by
  intro hL
  refine exLoop_no_linDef_invariant ⟨wlp exLoop exPost, hL, ?_, ?_, ?_⟩
  · exact valid_iff_imp_wlp.mp exLoop_valid
  · intro s s₁ h hx s₂ hx₂
    exact h.1 s₂ (Exec.whileTrue h.2 hx hx₂)
  · intro s h hb
    exact h s (Exec.whileFalse hb)

/-- Postcondition `x ≤ 1`, a weakening of `exPost` on the loop's exit states. -/
def exPostWeak : Assn := fun s => s 0 ≤ 1

/-- With the invariant `true`, `{true} exLoop {x ≤ 1}` is derivable in the linear logic. -/
theorem exLoop_deriv_linDef_weak_post : Deriv LinDef (fun _ => True) exLoop exPostWeak := by
  refine Deriv.conseq (fun _ h => h) (Deriv.whileDo ⟨.tt, fun _ => by simp [LAssn.eval]⟩ ?_)
    (fun s h => ?_)
  · exact Deriv.conseq (fun _ _ => trivial) (Deriv.assign 0 _ (fun _ => True)) (fun _ h => h)
  · have h₂ := h.2
    rw [exGuard_eval] at h₂
    simp only [decide_eq_false_iff_not] at h₂
    simp only [exPostWeak]
    omega

/-- **Positive control for non-expressiveness.** For the weaker postcondition `x ≤ 1`, the weakest
liberal precondition of the same loop is linearly definable (it is `true`). -/
theorem wlp_exLoop_weak_post_linDef : LinDef (wlp exLoop exPostWeak) := by
  refine ⟨.tt, fun s => ?_⟩
  simp only [LAssn.eval, iff_true]
  exact fun s' hx => hoare_sound exLoop_deriv_linDef_weak_post s s' trivial hx

end Toy.Hoare
