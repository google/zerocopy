import ToyHoare.Basic

/-!
# A non-expressive assertion language: divisibility-free quantifier-free linear arithmetic

`LAssn` is a syntactic assertion language: boolean combinations of `≤` and `=` between linear
terms (integer constants, variables, `+`, `-`, multiplication by an integer constant). There are no
quantifiers, no divisibility or modulo-by-constant predicates (so this is strictly weaker than the
SMT-LIB logic `QF_LIA`, whose formulas may use the predicates `(_ divisible n)` of the SMT-LIB
`Ints` theory), and no products of variables. `LinDef R` says that the semantic assertion `R` is
defined by some `LAssn` formula.

Key fact (`LAssn.eventually_const_on_affineLine`): along any affine line of stores, every `LAssn`
formula is eventually constant as the parameter tends to `+∞`. Consequently parity is not `LinDef`
(`parity_not_linDef`).
-/

namespace Toy.Hoare

/-- Linear integer terms: constants, variables, sums, differences and constant multiples. -/
inductive LTerm where
  | lit : Int → LTerm
  | var : Nat → LTerm
  | add : LTerm → LTerm → LTerm
  | sub : LTerm → LTerm → LTerm
  | smul : Int → LTerm → LTerm
  deriving Repr, DecidableEq

/-- Evaluation of a linear term in a store. -/
def LTerm.eval : LTerm → Store → Int
  | .lit n, _ => n
  | .var x, s => s x
  | .add t u, s => t.eval s + u.eval s
  | .sub t u, s => t.eval s - u.eval s
  | .smul k t, s => k * t.eval s

/-- Quantifier-free linear integer arithmetic formulas: `true`, `t ≤ u`, `t = u`, `¬`, `∧`, `∨`. -/
inductive LAssn where
  | tt : LAssn
  | le : LTerm → LTerm → LAssn
  | eq : LTerm → LTerm → LAssn
  | not : LAssn → LAssn
  | and : LAssn → LAssn → LAssn
  | or : LAssn → LAssn → LAssn
  deriving Repr, DecidableEq

/-- Truth value of a formula in a store (decidable, `Bool`-valued). -/
def LAssn.eval : LAssn → Store → Bool
  | .tt, _ => true
  | .le t u, s => decide (t.eval s ≤ u.eval s)
  | .eq t u, s => decide (t.eval s = u.eval s)
  | .not φ, s => !(φ.eval s)
  | .and φ ψ, s => φ.eval s && ψ.eval s
  | .or φ ψ, s => φ.eval s || ψ.eval s

/-- A semantic assertion is *linearly definable* if some quantifier-free linear formula holds in
exactly the stores satisfying it. -/
def LinDef (R : Assn) : Prop := ∃ φ : LAssn, ∀ s, R s ↔ φ.eval s = true

/-- A family of stores indexed by an integer parameter `n` along which the value of every variable
is an affine function of `n`. -/
def AffineLine (σ : Int → Store) : Prop := ∀ i : Nat, ∃ a b : Int, ∀ n, σ n i = a * n + b

theorem LTerm.eval_affine (t : LTerm) {σ : Int → Store} (hσ : AffineLine σ) :
    ∃ a b : Int, ∀ n, t.eval (σ n) = a * n + b := by
  induction t with
  | lit c => exact ⟨0, c, fun n => by simp [LTerm.eval]⟩
  | var x =>
    obtain ⟨a, b, h⟩ := hσ x
    exact ⟨a, b, fun n => by simp only [LTerm.eval]; exact h n⟩
  | add t u iht ihu =>
    obtain ⟨a₁, b₁, h₁⟩ := iht
    obtain ⟨a₂, b₂, h₂⟩ := ihu
    refine ⟨a₁ + a₂, b₁ + b₂, fun n => ?_⟩
    simp only [LTerm.eval, h₁, h₂, Int.add_mul]
    omega
  | sub t u iht ihu =>
    obtain ⟨a₁, b₁, h₁⟩ := iht
    obtain ⟨a₂, b₂, h₂⟩ := ihu
    refine ⟨a₁ - a₂, b₁ - b₂, fun n => ?_⟩
    simp only [LTerm.eval, h₁, h₂, Int.sub_mul]
    omega
  | smul k t ih =>
    obtain ⟨a, b, h⟩ := ih
    refine ⟨k * a, k * b, fun n => ?_⟩
    simp only [LTerm.eval, h, Int.mul_add, Int.mul_assoc]

private theorem mul_ge_self_of_pos {d n : Int} (hd : 0 < d) (hn : 0 ≤ n) : n ≤ d * n := by
  have h : 0 ≤ (d - 1) * n := Int.mul_nonneg (by omega) hn
  rw [Int.sub_mul, Int.one_mul] at h
  omega

private theorem mul_le_neg_self_of_neg {d n : Int} (hd : d < 0) (hn : 0 ≤ n) : d * n ≤ -n := by
  have h : 0 ≤ (-d - 1) * n := Int.mul_nonneg (by omega) hn
  rw [Int.sub_mul, Int.one_mul, Int.neg_mul] at h
  omega

/-- `d * n ≤ e` is eventually constant in `n`. -/
theorem affine_le_eventually_const (d e : Int) :
    ∃ N : Int, ∃ bv : Bool, ∀ n, N ≤ n → decide (d * n ≤ e) = bv := by
  rcases Int.lt_trichotomy d 0 with hd | hd | hd
  · refine ⟨max e (-e) + 1, true, fun n hn => ?_⟩
    have := mul_le_neg_self_of_neg hd (n := n) (by omega)
    simp only [decide_eq_true_eq]
    omega
  · exact ⟨0, decide (0 ≤ e), fun n _ => by simp [hd]⟩
  · refine ⟨max e (-e) + 1, false, fun n hn => ?_⟩
    have := mul_ge_self_of_pos hd (n := n) (by omega)
    simp only [decide_eq_false_iff_not]
    omega

/-- `d * n = e` is eventually constant in `n`. -/
theorem affine_eq_eventually_const (d e : Int) :
    ∃ N : Int, ∃ bv : Bool, ∀ n, N ≤ n → decide (d * n = e) = bv := by
  rcases Int.lt_trichotomy d 0 with hd | hd | hd
  · refine ⟨max e (-e) + 1, false, fun n hn => ?_⟩
    have := mul_le_neg_self_of_neg hd (n := n) (by omega)
    simp only [decide_eq_false_iff_not]
    omega
  · exact ⟨0, decide (0 = e), fun n _ => by simp [hd]⟩
  · refine ⟨max e (-e) + 1, false, fun n hn => ?_⟩
    have := mul_ge_self_of_pos hd (n := n) (by omega)
    simp only [decide_eq_false_iff_not]
    omega

/-- **Eventual constancy on affine lines.** Along an affine line of stores, every divisibility-free
quantifier-free linear formula has the same truth value at all sufficiently large parameters
(one-sided: `N ≤ n`). -/
theorem LAssn.eventually_const_on_affineLine (φ : LAssn) {σ : Int → Store} (hσ : AffineLine σ) :
    ∃ N : Int, ∃ bv : Bool, ∀ n, N ≤ n → φ.eval (σ n) = bv := by
  induction φ with
  | tt => exact ⟨0, true, fun _ _ => rfl⟩
  | le t u =>
    obtain ⟨a₁, b₁, h₁⟩ := t.eval_affine hσ
    obtain ⟨a₂, b₂, h₂⟩ := u.eval_affine hσ
    obtain ⟨N, bv, h⟩ := affine_le_eventually_const (a₁ - a₂) (b₂ - b₁)
    refine ⟨N, bv, fun n hn => ?_⟩
    rw [← h n hn]
    simp only [LAssn.eval, h₁, h₂, Int.sub_mul, decide_eq_decide]
    omega
  | eq t u =>
    obtain ⟨a₁, b₁, h₁⟩ := t.eval_affine hσ
    obtain ⟨a₂, b₂, h₂⟩ := u.eval_affine hσ
    obtain ⟨N, bv, h⟩ := affine_eq_eventually_const (a₁ - a₂) (b₂ - b₁)
    refine ⟨N, bv, fun n hn => ?_⟩
    rw [← h n hn]
    simp only [LAssn.eval, h₁, h₂, Int.sub_mul, decide_eq_decide]
    omega
  | not φ ih =>
    obtain ⟨N, bv, h⟩ := ih
    exact ⟨N, !bv, fun n hn => by simp only [LAssn.eval, h n hn]⟩
  | and φ ψ ih₁ ih₂ =>
    obtain ⟨N₁, bv₁, h₁⟩ := ih₁
    obtain ⟨N₂, bv₂, h₂⟩ := ih₂
    refine ⟨max N₁ N₂, bv₁ && bv₂, fun n hn => ?_⟩
    simp only [LAssn.eval, h₁ n (by omega), h₂ n (by omega)]
  | or φ ψ ih₁ ih₂ =>
    obtain ⟨N₁, bv₁, h₁⟩ := ih₁
    obtain ⟨N₂, bv₂, h₂⟩ := ih₂
    refine ⟨max N₁ N₂, bv₁ || bv₂, fun n hn => ?_⟩
    simp only [LAssn.eval, h₁ n (by omega), h₂ n (by omega)]

/-- If an assertion alternates (true somewhere and false somewhere) beyond every bound along some
affine line of stores, it is not definable in divisibility-free quantifier-free linear
arithmetic. -/
theorem not_linDef_of_alternating_on_affineLine {R : Assn} (σ : Int → Store) (hσ : AffineLine σ)
    (h : ∀ N : Int, ∃ n n', N ≤ n ∧ N ≤ n' ∧ R (σ n) ∧ ¬ R (σ n')) : ¬ LinDef R := by
  rintro ⟨φ, hφ⟩
  obtain ⟨N, bv, hN⟩ := φ.eventually_const_on_affineLine hσ
  obtain ⟨n, n', hn, hn', hR, hR'⟩ := h N
  have h₁ := (hφ _).mp hR
  rw [hN n hn] at h₁
  exact hR' ((hφ _).mpr (by rw [hN n' hn']; exact h₁))

/-- The constant line `n ↦ (fun _ => n)` is affine. -/
theorem affineLine_const : AffineLine (fun n : Int => fun _ : Nat => n) :=
  fun _ => ⟨1, 0, fun n => by simp⟩

/-- **Parity is not linearly definable**: no divisibility-free quantifier-free linear formula
defines "variable 0 is even". -/
theorem parity_not_linDef : ¬ LinDef (fun s => s 0 % 2 = 0) := by
  refine not_linDef_of_alternating_on_affineLine _ affineLine_const (fun N => ?_)
  refine ⟨2 * max N 0, 2 * max N 0 + 1, by omega, by omega, ?_, ?_⟩
  · show 2 * max N 0 % 2 = 0; omega
  · show ¬ (2 * max N 0 + 1) % 2 = 0; omega

end Toy.Hoare
