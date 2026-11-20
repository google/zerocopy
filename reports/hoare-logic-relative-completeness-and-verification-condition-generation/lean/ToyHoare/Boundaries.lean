import ToyHoare.Logic
import ToyHoare.Linear
import ToyHoare.Incomplete
import ToyHoare.VC
import ToyHoare.Total
import ToyHoare.Examples

/-!
# Boundary results

Fully proved statements that delimit what the main results say:

* `linDef_forall_wlp_iff_tautology`: requiring `LinDef (wlp c' Q)` for *every* command `c'`
  holds only for valid postconditions `Q`, which is why relative completeness is stated with the
  command-local hypothesis `WlpAdmissibleFor`.
* `vcgen_linDef_verifies_quad_seq_but_not_deriv_linDef`: verification by `vcgen` with linear loop
  annotations and derivability in `Deriv LinDef` differ even on loop-free programs, because
  `Deriv LinDef` restricts every sequencing midpoint while `vcgen` does not, and programs may
  multiply variables.
* `vcgen_side_conditions_ignore_branch_guards`: `vcgen`'s side conditions must hold in every
  store, even for a loop inside a branch that is never taken.
* `lassn_eventually_const_one_sided`: eventual constancy is one-sided; the eventual truth values
  towards `+∞` and `-∞` can differ.
-/

namespace Toy.Hoare

/-! ### The global `wlp` admissibility hypothesis is nearly vacuous for linear assertions -/

/-- Highest variable index referenced in an `LTerm`. -/
def ltermMaxVar : LTerm → Nat
  | .lit _ => 0
  | .var x => x
  | .add t u => max (ltermMaxVar t) (ltermMaxVar u)
  | .sub t u => max (ltermMaxVar t) (ltermMaxVar u)
  | .smul _ t => ltermMaxVar t

/-- A linear term depends only on the variables up to `ltermMaxVar`. -/
theorem ltermEval_eq_of_eq_le (t : LTerm) {s₁ s₂ : Store} :
    (∀ i, i ≤ ltermMaxVar t → s₁ i = s₂ i) → t.eval s₁ = t.eval s₂ := by
  induction t with
  | lit _ => intro _; rfl
  | var x => intro h; exact h x (Nat.le_refl x)
  | add t u iht ihu =>
    intro h
    simp only [LTerm.eval]
    rw [iht (fun i hi => h i (by simp [ltermMaxVar]; omega)),
        ihu (fun i hi => h i (by simp [ltermMaxVar]; omega))]
  | sub t u iht ihu =>
    intro h
    simp only [LTerm.eval]
    rw [iht (fun i hi => h i (by simp [ltermMaxVar]; omega)),
        ihu (fun i hi => h i (by simp [ltermMaxVar]; omega))]
  | smul k t iht =>
    intro h
    simp only [LTerm.eval]
    rw [iht (fun i hi => h i (by simpa [ltermMaxVar] using hi))]

/-- Highest variable index referenced in an `LAssn`. -/
def lassnMaxVar : LAssn → Nat
  | .tt => 0
  | .le t u => max (ltermMaxVar t) (ltermMaxVar u)
  | .eq t u => max (ltermMaxVar t) (ltermMaxVar u)
  | .not φ => lassnMaxVar φ
  | .and φ ψ => max (lassnMaxVar φ) (lassnMaxVar ψ)
  | .or φ ψ => max (lassnMaxVar φ) (lassnMaxVar ψ)

/-- A formula depends only on the variables up to `lassnMaxVar`. -/
theorem lassnEval_eq_of_eq_le (φ : LAssn) {s₁ s₂ : Store} :
    (∀ i, i ≤ lassnMaxVar φ → s₁ i = s₂ i) → φ.eval s₁ = φ.eval s₂ := by
  induction φ with
  | tt => intro _; rfl
  | le t u =>
    intro h
    simp only [LAssn.eval]
    rw [ltermEval_eq_of_eq_le t (fun i hi => h i (by simp [lassnMaxVar]; omega)),
        ltermEval_eq_of_eq_le u (fun i hi => h i (by simp [lassnMaxVar]; omega))]
  | eq t u =>
    intro h
    simp only [LAssn.eval]
    rw [ltermEval_eq_of_eq_le t (fun i hi => h i (by simp [lassnMaxVar]; omega)),
        ltermEval_eq_of_eq_le u (fun i hi => h i (by simp [lassnMaxVar]; omega))]
  | not φ ih =>
    intro h
    simp only [LAssn.eval]
    rw [ih (fun i hi => h i (by simpa [lassnMaxVar] using hi))]
  | and φ ψ ih₁ ih₂ =>
    intro h
    simp only [LAssn.eval]
    rw [ih₁ (fun i hi => h i (by simp [lassnMaxVar]; omega)),
        ih₂ (fun i hi => h i (by simp [lassnMaxVar]; omega))]
  | or φ ψ ih₁ ih₂ =>
    intro h
    simp only [LAssn.eval]
    rw [ih₁ (fun i hi => h i (by simp [lassnMaxVar]; omega)),
        ih₂ (fun i hi => h i (by simp [lassnMaxVar]; omega))]

/-- `x₀ := target 0; …; x_k := target k`: overwrite variables `0 … k` with constants. -/
def assignUpTo (target : Store) : Nat → Com
  | 0 => .assign 0 (.lit (target 0))
  | k + 1 => .seq (assignUpTo target k) (.assign (k + 1) (.lit (target (k + 1))))

/-- The store reached by `assignUpTo target k` from `s`. -/
def overwriteUpTo (s target : Store) : Nat → Store
  | 0 => upd s 0 (target 0)
  | k + 1 => upd (overwriteUpTo s target k) (k + 1) (target (k + 1))

theorem exec_assignUpTo (target : Store) (k : Nat) (s : Store) :
    Exec (assignUpTo target k) s (overwriteUpTo s target k) := by
  induction k with
  | zero => exact Exec.assign 0 (.lit (target 0)) s
  | succ k ih =>
    exact Exec.seq ih (Exec.assign (k + 1) (.lit (target (k + 1))) (overwriteUpTo s target k))

theorem overwriteUpTo_apply (s target : Store) (k i : Nat) (hi : i ≤ k) :
    overwriteUpTo s target k i = target i := by
  induction k with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0
    simp [overwriteUpTo]
  | succ k ih =>
    by_cases hik : i = k + 1
    · subst hik
      simp [overwriteUpTo]
    · simp only [overwriteUpTo, upd_other _ _ hik]
      exact ih (by omega)

/-- `exLoop; if x = 0 then (while true do skip) else (x₀ := target 0; …; x_k := target k)`:
diverges from even `x ≥ 0` and ends in a store agreeing with `target` on variables `0 … k` from
odd `x ≥ 1`. -/
def parityTrap (target : Store) (k : Nat) : Com :=
  .seq exLoop (.cond (.eq (.var 0) (.lit 0)) (.whileDo .tt .skip) (assignUpTo target k))

/-- **The global `wlp` hypothesis collapses for linear assertions.** For every assertion `Q`,
`LinDef (wlp c' Q)` holds for *every* command `c'` if and only if `Q` holds in every store. So a
relative-completeness theorem whose hypothesis quantifies over all commands says nothing about
linear assertions beyond valid postconditions; `WlpAdmissibleFor` quantifies only over the `wlp`s
along the given command. -/
theorem linDef_forall_wlp_iff_tautology (Q : Assn) :
    (∀ c' : Com, LinDef (wlp c' Q)) ↔ (∀ s : Store, Q s) := by
  constructor
  · intro hwlp
    obtain ⟨φ, hφ⟩ := hwlp .skip
    have hQφ : ∀ s, Q s ↔ φ.eval s = true := by
      intro s
      have hskip : wlp .skip Q s ↔ Q s :=
        ⟨fun h => h s (Exec.skip s), fun h s' hx => by cases hx; exact h⟩
      exact hskip.symm.trans (hφ s)
    intro s₀
    by_cases hs₀ : Q s₀
    · exact hs₀
    · exfalso
      have hfalse : φ.eval s₀ = false := by
        cases hval : φ.eval s₀ with
        | false => rfl
        | true => exact absurd ((hQφ s₀).mpr hval) hs₀
      have hline : AffineLine (fun n => st2 n 0) := by
        intro i
        by_cases h0 : i = 0
        · exact ⟨1, 0, fun n => by simp [st2, h0]⟩
        · exact ⟨0, 0, fun n => by simp [st2, h0]⟩
      refine not_linDef_of_alternating_on_affineLine (fun n => st2 n 0) hline (fun N => ?_)
        (hwlp (parityTrap s₀ (lassnMaxVar φ)))
      refine ⟨2 * (N.toNat : Int), 2 * (N.toNat : Int) + 1, by omega, by omega, ?_, ?_⟩
      · intro s' hx
        unfold parityTrap at hx
        cases hx with
        | seq hx1 hx2 =>
          have hs1 := Exec.deterministic hx1 (exec_exLoop_even N.toNat 0)
          subst hs1
          cases hx2 with
          | condTrue _ hdiv => exact absurd hdiv exec_while_tt_diverges
          | condFalse hb _ => simp [BExp.eval, AExp.eval, st2] at hb
      · intro hw
        have hx1 := exec_exLoop_odd N.toNat 0
        have hb : (BExp.eq (.var 0) (.lit 0)).eval (st2 1 0) = false := by
          simp [BExp.eval, AExp.eval, st2]
        have hx2 := Exec.condFalse (c₁ := .whileDo .tt .skip) hb
          (exec_assignUpTo s₀ (lassnMaxVar φ) (st2 1 0))
        have hQs' := hw _ (Exec.seq hx1 hx2)
        have heval := (hQφ _).mp hQs'
        rw [lassnEval_eq_of_eq_le φ (s₂ := s₀) (fun i hi => overwriteUpTo_apply _ _ _ i hi)] at heval
        rw [hfalse] at heval
        cases heval
  · intro hTrue c'
    refine ⟨.tt, fun s => ?_⟩
    simp only [LAssn.eval, iff_true]
    exact fun s' _ => hTrue s'

/-! ### `vcgen` with linear loop annotations versus `Deriv LinDef` -/

/-- `x := y * y; x := x - y * y`. -/
def quadSeqCom : Com :=
  .seq (.assign 0 (.mul (.var 1) (.var 1)))
       (.assign 0 (.sub (.var 0) (.mul (.var 1) (.var 1))))

/-- `quadSeqCom` as an annotated command (it has no loops). -/
def quadSeqAnn : ACom :=
  .seq (.assign 0 (.mul (.var 1) (.var 1)))
       (.assign 0 (.sub (.var 0) (.mul (.var 1) (.var 1))))

/-- On stores `st2 a b`, a linear term is an affine function of `a` and `b`. -/
theorem ltermEvalSt2Linear (t : LTerm) :
    ∃ α β γ : Int, ∀ a b : Int, t.eval (st2 a b) = α * a + β * b + γ := by
  induction t with
  | lit c => exact ⟨0, 0, c, fun _ _ => by simp [LTerm.eval]⟩
  | var x =>
    by_cases h0 : x = 0
    · exact ⟨1, 0, 0, fun a b => by simp [LTerm.eval, st2, h0]⟩
    · by_cases h1 : x = 1
      · exact ⟨0, 1, 0, fun a b => by simp [LTerm.eval, st2, h1]⟩
      · exact ⟨0, 0, 0, fun a b => by simp [LTerm.eval, st2, h0, h1]⟩
  | add t u iht ihu =>
    obtain ⟨α₁, β₁, γ₁, h₁⟩ := iht
    obtain ⟨α₂, β₂, γ₂, h₂⟩ := ihu
    refine ⟨α₁ + α₂, β₁ + β₂, γ₁ + γ₂, fun a b => ?_⟩
    simp only [LTerm.eval, h₁, h₂, Int.add_mul]
    omega
  | sub t u iht ihu =>
    obtain ⟨α₁, β₁, γ₁, h₁⟩ := iht
    obtain ⟨α₂, β₂, γ₂, h₂⟩ := ihu
    refine ⟨α₁ - α₂, β₁ - β₂, γ₁ - γ₂, fun a b => ?_⟩
    simp only [LTerm.eval, h₁, h₂, Int.sub_mul]
    omega
  | smul k t iht =>
    obtain ⟨α, β, γ, h⟩ := iht
    refine ⟨k * α, k * β, k * γ, fun a b => ?_⟩
    simp only [LTerm.eval, h, Int.mul_add, Int.mul_assoc]

private theorem quad_le_same_sign (c d e : Int) :
    ∃ N : Int, ∀ n : Int, N ≤ n →
      decide (c * (n * n) + d * n ≤ e) = decide (c * (n * n + 1) + d * n ≤ e) := by
  refine ⟨(c.natAbs : Int) + (d.natAbs : Int) + (e.natAbs : Int) + 3, fun n hn => ?_⟩
  have hd_abs : -(d.natAbs : Int) ≤ d ∧ d ≤ (d.natAbs : Int) := by omega
  have he_abs : -(e.natAbs : Int) ≤ e ∧ e ≤ (e.natAbs : Int) := by omega
  have hn_pos : 0 ≤ n := by omega
  rcases Int.lt_trichotomy c 0 with hc | rfl | hc
  · have hc1 : c * (n * n) ≤ -(n * n) := by
      have hmul : 0 ≤ (-c - 1) * (n * n) := Int.mul_nonneg (by omega) (Int.mul_nonneg hn_pos hn_pos)
      rw [Int.sub_mul, Int.one_mul, Int.neg_mul] at hmul
      omega
    have hdn : d * n ≤ (d.natAbs : Int) * n := by
      have hmul : 0 ≤ ((d.natAbs : Int) - d) * n := Int.mul_nonneg (by omega) hn_pos
      rw [Int.sub_mul] at hmul
      omega
    have hgap : (e.natAbs : Int) + 3 ≤ (n - (d.natAbs : Int)) * n := by
      have h1 : (e.natAbs : Int) + 3 ≤ n - (d.natAbs : Int) := by omega
      have h2 : 1 ≤ n := by omega
      have hmul : (n - (d.natAbs : Int)) * 1 ≤ (n - (d.natAbs : Int)) * n :=
        Int.mul_le_mul_of_nonneg_left h2 (by omega)
      omega
    have hsum1 : c * (n * n) + d * n ≤ e := by
      rw [Int.sub_mul] at hgap
      omega
    have hsum2 : c * (n * n + 1) + d * n ≤ e := by
      rw [Int.mul_add, Int.mul_one]
      omega
    simp [hsum1, hsum2]
  · simp
  · have hc1 : n * n ≤ c * (n * n) := by
      have hmul : 0 ≤ (c - 1) * (n * n) := Int.mul_nonneg (by omega) (Int.mul_nonneg hn_pos hn_pos)
      rw [Int.sub_mul, Int.one_mul] at hmul
      omega
    have hdn : -((d.natAbs : Int) * n) ≤ d * n := by
      have hmul : 0 ≤ (d + (d.natAbs : Int)) * n := Int.mul_nonneg (by omega) hn_pos
      rw [Int.add_mul] at hmul
      omega
    have hgap : (e.natAbs : Int) + 3 ≤ (n - (d.natAbs : Int)) * n := by
      have h1 : (e.natAbs : Int) + 3 ≤ n - (d.natAbs : Int) := by omega
      have h2 : 1 ≤ n := by omega
      have hmul : (n - (d.natAbs : Int)) * 1 ≤ (n - (d.natAbs : Int)) * n :=
        Int.mul_le_mul_of_nonneg_left h2 (by omega)
      omega
    have hsum1 : ¬ (c * (n * n) + d * n ≤ e) := by
      rw [Int.sub_mul] at hgap
      omega
    have hsum2 : ¬ (c * (n * n + 1) + d * n ≤ e) := by
      rw [Int.mul_add, Int.mul_one]
      omega
    simp [hsum1, hsum2]

/-- Every formula takes the same value on `st2 (n * n) n` and `st2 (n * n + 1) n` for all large
`n`. -/
theorem lassnEvalParabolaNeighborEq (φ : LAssn) :
    ∃ N : Int, ∀ n : Int, N ≤ n → φ.eval (st2 (n * n) n) = φ.eval (st2 (n * n + 1) n) := by
  induction φ with
  | tt => exact ⟨0, fun _ _ => rfl⟩
  | le t u =>
    obtain ⟨α₁, β₁, γ₁, h₁⟩ := ltermEvalSt2Linear t
    obtain ⟨α₂, β₂, γ₂, h₂⟩ := ltermEvalSt2Linear u
    obtain ⟨N, hN⟩ := quad_le_same_sign (α₁ - α₂) (β₁ - β₂) (γ₂ - γ₁)
    refine ⟨N, fun n hn => ?_⟩
    have e₁ : decide (t.eval (st2 (n * n) n) ≤ u.eval (st2 (n * n) n)) =
        decide ((α₁ - α₂) * (n * n) + (β₁ - β₂) * n ≤ γ₂ - γ₁) := by
      simp only [h₁, h₂, Int.sub_mul, decide_eq_decide]; omega
    have e₂ : decide (t.eval (st2 (n * n + 1) n) ≤ u.eval (st2 (n * n + 1) n)) =
        decide ((α₁ - α₂) * (n * n + 1) + (β₁ - β₂) * n ≤ γ₂ - γ₁) := by
      simp only [h₁, h₂, Int.sub_mul, decide_eq_decide]; omega
    simp only [LAssn.eval, e₁, e₂, hN n hn]
  | eq t u =>
    have heqv : ∀ s, (LAssn.eq t u).eval s = ((LAssn.le t u).and (.le u t)).eval s := by
      intro s
      simp only [LAssn.eval]
      cases h1 : decide (t.eval s ≤ u.eval s) <;>
        cases h2 : decide (u.eval s ≤ t.eval s) <;>
        cases h3 : decide (t.eval s = u.eval s) <;>
        simp_all [decide_eq_true_eq, decide_eq_false_iff_not] <;>
        omega
    obtain ⟨α₁, β₁, γ₁, h₁⟩ := ltermEvalSt2Linear t
    obtain ⟨α₂, β₂, γ₂, h₂⟩ := ltermEvalSt2Linear u
    obtain ⟨N₁, hN₁⟩ := quad_le_same_sign (α₁ - α₂) (β₁ - β₂) (γ₂ - γ₁)
    obtain ⟨N₂, hN₂⟩ := quad_le_same_sign (α₂ - α₁) (β₂ - β₁) (γ₁ - γ₂)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    rw [heqv, heqv]
    have e₁ : decide (t.eval (st2 (n * n) n) ≤ u.eval (st2 (n * n) n)) =
        decide (t.eval (st2 (n * n + 1) n) ≤ u.eval (st2 (n * n + 1) n)) := by
      have a₁ : decide (t.eval (st2 (n * n) n) ≤ u.eval (st2 (n * n) n)) =
          decide ((α₁ - α₂) * (n * n) + (β₁ - β₂) * n ≤ γ₂ - γ₁) := by
        simp only [h₁, h₂, Int.sub_mul, decide_eq_decide]; omega
      have a₂ : decide (t.eval (st2 (n * n + 1) n) ≤ u.eval (st2 (n * n + 1) n)) =
          decide ((α₁ - α₂) * (n * n + 1) + (β₁ - β₂) * n ≤ γ₂ - γ₁) := by
        simp only [h₁, h₂, Int.sub_mul, decide_eq_decide]; omega
      rw [a₁, a₂, hN₁ n (by omega)]
    have e₂ : decide (u.eval (st2 (n * n) n) ≤ t.eval (st2 (n * n) n)) =
        decide (u.eval (st2 (n * n + 1) n) ≤ t.eval (st2 (n * n + 1) n)) := by
      have b₁ : decide (u.eval (st2 (n * n) n) ≤ t.eval (st2 (n * n) n)) =
          decide ((α₂ - α₁) * (n * n) + (β₂ - β₁) * n ≤ γ₁ - γ₂) := by
        simp only [h₁, h₂, Int.sub_mul, decide_eq_decide]; omega
      have b₂ : decide (u.eval (st2 (n * n + 1) n) ≤ t.eval (st2 (n * n + 1) n)) =
          decide ((α₂ - α₁) * (n * n + 1) + (β₂ - β₁) * n ≤ γ₁ - γ₂) := by
        simp only [h₁, h₂, Int.sub_mul, decide_eq_decide]; omega
      rw [b₁, b₂, hN₂ n (by omega)]
    simp only [LAssn.eval, e₁, e₂]
  | not φ ih =>
    obtain ⟨N, hN⟩ := ih
    exact ⟨N, fun n hn => by simp only [LAssn.eval, hN n hn]⟩
  | and φ ψ ih₁ ih₂ =>
    obtain ⟨N₁, hN₁⟩ := ih₁
    obtain ⟨N₂, hN₂⟩ := ih₂
    exact ⟨max N₁ N₂, fun n hn => by simp only [LAssn.eval, hN₁ n (by omega), hN₂ n (by omega)]⟩
  | or φ ψ ih₁ ih₂ =>
    obtain ⟨N₁, hN₁⟩ := ih₁
    obtain ⟨N₂, hN₂⟩ := ih₂
    exact ⟨max N₁ N₂, fun n hn => by simp only [LAssn.eval, hN₁ n (by omega), hN₂ n (by omega)]⟩

/-- Inversion of the sequencing rule through any number of consequence steps. -/
theorem Deriv.seq_inv {L : Assn → Prop} {P Q : Assn} {c₁ c₂ : Com}
    (h : Deriv L P (.seq c₁ c₂) Q) :
    ∃ R, L R ∧ Valid P c₁ R ∧ Valid R c₂ Q := by
  generalize hs : Com.seq c₁ c₂ = c at h
  induction h with
  | seq hR d₁ d₂ =>
    cases hs
    exact ⟨_, hR, hoare_sound d₁, hoare_sound d₂⟩
  | conseq hP _ hQ ih =>
    obtain ⟨R, hR, v₁, v₂⟩ := ih hs
    exact ⟨R, hR, fun s s' hp hx => v₁ s s' (hP s hp) hx,
           fun s s' hr hx => hQ s' (v₂ s s' hr hx)⟩
  | skip => cases hs
  | assign => cases hs
  | cond => cases hs
  | whileDo => cases hs

/-- **`vcgen` with linear loop annotations is not `Deriv LinDef`.** For the loop-free triple
`{true} x := y * y; x := x - y * y {x = 0}`: the pre- and postcondition are linearly definable, the
annotated program (no loops, so every annotation condition holds) is verified by `vcgen` with no
side conditions, yet the triple is not derivable in `Deriv LinDef`, because every valid
sequencing midpoint must separate `x = y * y` from `x = y * y + 1`, which no divisibility-free
quantifier-free linear formula does for large `y`. -/
theorem vcgen_linDef_verifies_quad_seq_but_not_deriv_linDef :
    LinDef (fun _ => True) ∧
    LinDef (fun s => s 0 = 0) ∧
    quadSeqAnn.erase = quadSeqCom ∧
    quadSeqAnn.InvsIn LinDef ∧
    VCsValid (vcgen quadSeqAnn (fun s => s 0 = 0)).2 ∧
    (∀ s, (fun _ : Store => True) s → (vcgen quadSeqAnn (fun s => s 0 = 0)).1 s) ∧
    ¬ Deriv LinDef (fun _ => True) quadSeqCom (fun s => s 0 = 0) := by
  refine ⟨⟨.tt, fun _ => by simp [LAssn.eval]⟩,
          ⟨.eq (.var 0) (.lit 0), fun s => by
            simp only [LAssn.eval, LTerm.eval]; exact decide_eq_true_iff.symm⟩,
          rfl, ⟨trivial, trivial⟩,
          fun φ hφ => by simp [quadSeqAnn, vcgen] at hφ,
          fun s _ => by simp [quadSeqAnn, vcgen, AExp.eval, upd],
          fun hd => ?_⟩
  obtain ⟨R, ⟨φ, hφ⟩, v₁, v₂⟩ := Deriv.seq_inv hd
  obtain ⟨N, hN⟩ := lassnEvalParabolaNeighborEq φ
  let n : Int := max N 0
  have h_on : R (st2 (n * n) n) := by
    have hx := Exec.assign 0 (.mul (.var 1) (.var 1)) (st2 0 n)
    have he : AExp.eval (.mul (.var 1) (.var 1)) (st2 0 n) = n * n := by simp [AExp.eval, st2]
    rw [he, upd_st2_zero] at hx
    exact v₁ (st2 0 n) (st2 (n * n) n) trivial hx
  have h_off : ¬ R (st2 (n * n + 1) n) := by
    intro hr
    have hx := Exec.assign 0 (.sub (.var 0) (.mul (.var 1) (.var 1))) (st2 (n * n + 1) n)
    have he : AExp.eval (.sub (.var 0) (.mul (.var 1) (.var 1))) (st2 (n * n + 1) n) = 1 := by
      simp [AExp.eval, st2]; omega
    rw [he, upd_st2_zero] at hx
    have h0 := v₂ _ _ hr hx
    simp [st2] at h0
  have htrue := (hφ (st2 (n * n) n)).mp h_on
  rw [hN n (by omega)] at htrue
  exact h_off ((hφ (st2 (n * n + 1) n)).mpr htrue)

/-! ### `vcgen` side conditions are global -/

/-- `if x = 1 then (while[true] false do skip) else skip`: a loop, annotated with `true`, inside a
branch that is never taken from `x = 0`. -/
def deadBranchAnn : ACom :=
  .cond (.eq (.var 0) (.lit 1)) (.whileDo (fun _ => True) .ff .skip) .skip

/-- For `{x = 0} if x = 1 then (while[true] false do skip) else skip {x = 0}`: the triple is
valid, the annotation is linear, the precondition implies the generated precondition, yet a side
condition (the loop's exit condition `true ∧ ¬false → x = 0`) is invalid, because side conditions
are checked in every store, not only in stores reaching the loop. -/
theorem vcgen_side_conditions_ignore_branch_guards :
    Valid (fun s => s 0 = 0) deadBranchAnn.erase (fun s => s 0 = 0) ∧
    deadBranchAnn.InvsIn LinDef ∧
    (∀ s, s 0 = 0 → (vcgen deadBranchAnn (fun s => s 0 = 0)).1 s) ∧
    ¬ VCsValid (vcgen deadBranchAnn (fun s => s 0 = 0)).2 := by
  refine ⟨fun s s' hs hx => ?_, ⟨⟨⟨.tt, fun _ => by simp [LAssn.eval]⟩, trivial⟩, trivial⟩,
    fun s hs => ?_, fun h => ?_⟩
  · simp only [deadBranchAnn, ACom.erase] at hx
    cases hx with
    | condTrue hb _ => simp [BExp.eval, AExp.eval, hs] at hb
    | condFalse _ hx => cases hx; exact hs
  · simp only [deadBranchAnn, vcgen]
    exact ⟨fun _ => trivial, fun _ => hs⟩
  · simp only [deadBranchAnn, vcgen, VCsValid.append, VCsValid.cons] at h
    have := h.1.2.1 (fun _ => 1) trivial rfl
    simp at this

/-! ### Eventual constancy is one-sided -/

/-- Along the diagonal `x = y = n`, the linear formula `0 ≤ x` is true for all `n ≥ 0` and false
for all `n ≤ -1`: the eventual values towards `+∞` and `-∞` differ. -/
theorem lassn_eventually_const_one_sided :
    (∀ n : Int, 0 ≤ n → (LAssn.le (.lit 0) (.var 0)).eval (st2 n n) = true) ∧
    (∀ n : Int, n ≤ -1 → (LAssn.le (.lit 0) (.var 0)).eval (st2 n n) = false) := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · simp [LAssn.eval, LTerm.eval, st2]; omega
  · simp [LAssn.eval, LTerm.eval, st2]; omega

end Toy.Hoare
