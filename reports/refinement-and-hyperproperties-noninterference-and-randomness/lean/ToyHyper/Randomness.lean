import ToyHyper.Core

/-!
# Randomness Collapse and Probabilistic Min-Entropy Invariance

This module models both possibilistic output-range diversity (full range over
`2^k` values) and finite discrete probability distributions using `Nat`-valued
unnormalized weights over `Fin n` (with positive total weight), avoiding real
numbers. Min-entropy lower bounds `H_∞(d) ≥ k` are expressed directly in `Nat`
arithmetic as `maxWeight d * 2 ^ k ≤ totalWeight d`.

Here "exact integer min-entropy `k`" means that `HasMinEntropyAtLeast d k`
holds and `HasMinEntropyAtLeast d (k + 1)` fails (for uniform distributions on
`2^k` points and point masses, the real-valued min-entropy is literally `k`).

This module proves:
- possibilistic full-range collapse under trace inclusion for `k > 0`,
- probabilistic min-entropy collapse from `k` to `0` under support inclusion
  for `k > 0`,
- that trace equivalence (equal supports) does not preserve min-entropy, so
  min-entropy is not a `Hyperprop` of the support,
- that `SameDist` (equality of probability distributions, an equivalence
  relation) is sufficient but not necessary to keep a min-entropy bound, and
- states well-definedness (invariance under weight rescaling) of min-entropy
  bounds under `ProportionalWeights` with a valid source and under `SameDist`.
-/

namespace Toy.Hyper

/-! ## Finite Sums and Maxima over `Fin n` -/

/-- Sum of a `Nat`-valued weight function over `Fin n`. -/
def sumFin : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _ + 1, w => w 0 + sumFin (fun i => w i.succ)

/-- Maximum of a `Nat`-valued weight function over `Fin n` (0 when `n = 0`). -/
def maxFin : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _ + 1, w => Nat.max (w 0) (maxFin (fun i => w i.succ))

theorem sumFin_congr {n : Nat} {w₁ w₂ : Fin n → Nat} (h : ∀ i, w₁ i = w₂ i) :
    sumFin w₁ = sumFin w₂ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumFin]
    rw [h 0, ih (fun i => h i.succ)]

theorem maxFin_congr {n : Nat} {w₁ w₂ : Fin n → Nat} (h : ∀ i, w₁ i = w₂ i) :
    maxFin w₁ = maxFin w₂ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [maxFin]
    rw [h 0, ih (fun i => h i.succ)]

theorem sumFin_const (n c : Nat) : sumFin (fun _ : Fin n => c) = n * c := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    simp only [sumFin, ih, Nat.succ_mul, Nat.add_comm]

theorem maxFin_zero (n : Nat) : maxFin (fun _ : Fin n => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [maxFin, ih]

theorem maxFin_const_pos (n c : Nat) (hn : 0 < n) :
    maxFin (fun _ : Fin n => c) = c := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [maxFin]
    | succ m =>
      change Nat.max c (maxFin (fun _ : Fin (m + 1) => c)) = c
      rw [ih (Nat.succ_pos m)]
      exact Nat.max_self c

theorem sumFin_point {n : Nat} (v : Fin n) :
    sumFin (fun x : Fin n => if x = v then 1 else 0) = 1 := by
  induction n with
  | zero => exact v.elim0
  | succ n ih =>
    refine Fin.cases ?_ ?_ v
    · simp only [sumFin, ↓reduceIte]
      have hRest :
          sumFin (fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then 1 else 0) =
          sumFin (fun _ : Fin n => 0) :=
        sumFin_congr fun i => by simp [Fin.succ_ne_zero]
      rw [hRest, sumFin_const, Nat.mul_zero, Nat.add_zero]
    · intro v'
      simp only [sumFin]
      have h0 : (0 : Fin (n + 1)) ≠ v'.succ := (Fin.succ_ne_zero v').symm
      simp only [h0, ↓reduceIte, Nat.zero_add]
      have hRest :
          sumFin (fun i : Fin n => if i.succ = v'.succ then 1 else 0) =
          sumFin (fun i : Fin n => if i = v' then 1 else 0) :=
        sumFin_congr fun i => by
          by_cases h : i = v'
          · subst h; simp
          · have hs : i.succ ≠ v'.succ := fun heq => h (Fin.succ_inj.mp heq)
            simp [h, hs]
      rw [hRest, ih v']

theorem maxFin_point {n : Nat} (v : Fin n) :
    maxFin (fun x : Fin n => if x = v then 1 else 0) = 1 := by
  induction n with
  | zero => exact v.elim0
  | succ n ih =>
    refine Fin.cases ?_ ?_ v
    · simp only [maxFin, ↓reduceIte]
      have hRest :
          maxFin (fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then 1 else 0) =
          maxFin (fun _ : Fin n => 0) :=
        maxFin_congr fun i => by simp [Fin.succ_ne_zero]
      rw [hRest, maxFin_zero]
      rfl
    · intro v'
      simp only [maxFin]
      have h0 : (0 : Fin (n + 1)) ≠ v'.succ := (Fin.succ_ne_zero v').symm
      simp only [h0, ↓reduceIte]
      have hRest :
          maxFin (fun i : Fin n => if i.succ = v'.succ then 1 else 0) =
          maxFin (fun i : Fin n => if i = v' then 1 else 0) :=
        maxFin_congr fun i => by
          by_cases h : i = v'
          · subst h; simp
          · have hs : i.succ ≠ v'.succ := fun heq => h (Fin.succ_inj.mp heq)
            simp [h, hs]
      rw [hRest, ih v']
      rfl

theorem maxFin_le_iff {n : Nat} (w : Fin n → Nat) (m : Nat) :
    maxFin w ≤ m ↔ ∀ i : Fin n, w i ≤ m := by
  induction n with
  | zero =>
    constructor
    · intro _ i; exact i.elim0
    · intro _; exact Nat.zero_le m
  | succ n ih =>
    simp only [maxFin, Nat.max_le, ih]
    constructor
    · intro ⟨h0, hS⟩ i
      exact Fin.cases h0 hS i
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩

theorem le_maxFin {n : Nat} (w : Fin n → Nat) (i : Fin n) :
    w i ≤ maxFin w :=
  (maxFin_le_iff w (maxFin w)).mp (Nat.le_refl _) i

theorem le_sumFin {n : Nat} (w : Fin n → Nat) (i : Fin n) :
    w i ≤ sumFin w := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ ?_ i
    · simp only [sumFin]; omega
    · intro j
      simp only [sumFin]
      have := ih (fun k => w k.succ) j
      omega

theorem two_pow_pos (k : Nat) : 0 < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

/-! ## Core Definitions for Possibilistic and Probabilistic Randomness -/

/-- A weight assignment over `Fin n` represents a valid finite probability
distribution iff its total weight is strictly positive (so `Pr[x] = w x / ∑ w`
is well-defined). -/
def ValidWeights {n : Nat} (w : Fin n → Nat) : Prop :=
  0 < sumFin w

/-- Raw weight proportionality between two `Nat`-valued weight functions over
`Fin n`. Without `ValidWeights`, the all-zero weight function relates to every
weight function (breaking transitivity, `proportionalWeights_without_valid_fails`,
and breaking min-entropy transfer when placed in the source slot,
`proportionalWeights_minEntropy_counterexample_source_not_valid`). -/
def ProportionalWeights {n : Nat} (w' w : Fin n → Nat) : Prop :=
  ∀ x : Fin n, w' x * sumFin w = w x * sumFin w'

/-- Raw-table min-entropy inequality over `Nat` weight functions:
`maxFin w * 2 ^ k ≤ sumFin w`. Used to state unbundled validity requirements
on weight tables. -/
def RawMinEnt {n : Nat} (w : Fin n → Nat) (k : Nat) : Prop :=
  maxFin w * 2 ^ k ≤ sumFin w

/-- A valid finite discrete probability distribution over `Fin n`, represented
by `Nat`-valued unnormalized weights with positive total weight. Note that
`FinDist 0` is uninhabited, matching the absence of probability distributions
over the empty set. -/
structure FinDist (n : Nat) where
  weight : Fin n → Nat
  valid : ValidWeights weight

/-- Total unnormalized weight of a finite distribution. -/
def totalWeight {n : Nat} (d : FinDist n) : Nat :=
  sumFin d.weight

/-- Maximum weight assigned to any single outcome in a finite distribution. -/
def maxWeight {n : Nat} (d : FinDist n) : Nat :=
  maxFin d.weight

/-- The possibilistic trace set (support) of a probabilistic system: the set of
outcomes assigned strictly positive probability mass. -/
def support {n : Nat} (d : FinDist n) : System (Fin n) :=
  fun x => 0 < d.weight x

/-- Possibilistic full-range specification over `2^k` output values: every
element of `Fin (2^k)` is an allowed trace. -/
def FullRangeSystem (k : Nat) : System (Fin (2 ^ k)) :=
  fun _ => True

/-- Possibilistic constant-output system emitting only `v : Fin (2^k)`. -/
def ConstSystem (k : Nat) (v : Fin (2 ^ k)) : System (Fin (2 ^ k)) :=
  fun x => x = v

/-- The possibilistic hyperproperty requiring a system over `Fin n` to be able
to exhibit every value in `Fin n` (surjectivity onto `Fin n`). -/
def RangesOverAll (n : Nat) : Hyperprop (Fin n) :=
  fun S => ∀ x : Fin n, S x

/-- Min-entropy lower bound in exact `Nat` arithmetic: `H_∞(d) ≥ k`, meaning
`max_x Pr[d = x] ≤ 2^{-k}`, stated without reals as
`maxWeight d * 2 ^ k ≤ totalWeight d`. -/
def HasMinEntropyAtLeast {n : Nat} (d : FinDist n) (k : Nat) : Prop :=
  maxWeight d * 2 ^ k ≤ totalWeight d

/-- Equality of probability distributions (an equivalence relation, not a
proper refinement order): `d'` and `d` assign identical probabilities
`w'(x) / W' = w(x) / W` to every outcome `x : Fin n`, stated via
cross-multiplication in `Nat`. -/
def SameDist {n : Nat} (d' d : FinDist n) : Prop :=
  ProportionalWeights d'.weight d.weight

/-! ## Canonical Distributions -/

/-- The uniform distribution over `Fin (2^k)` (weight `1` on every outcome). -/
def uniformDist (k : Nat) : FinDist (2 ^ k) where
  weight := fun _ => 1
  valid := by
    change 0 < sumFin (fun _ : Fin (2 ^ k) => 1)
    rw [sumFin_const, Nat.mul_one]
    exact two_pow_pos k

/-- A scaled representation of the uniform distribution over `Fin (2^k)`
(weight `2` on every outcome), witnessing distinct raw weight tables with
identical probability distributions. -/
def scaledUniformDist (k : Nat) : FinDist (2 ^ k) where
  weight := fun _ => 2
  valid := by
    change 0 < sumFin (fun _ : Fin (2 ^ k) => 2)
    rw [sumFin_const]
    have h := two_pow_pos k
    omega

/-- The point-mass distribution concentrated at outcome `v : Fin n`. -/
def pointDist {n : Nat} (v : Fin n) : FinDist n where
  weight := fun x => if x = v then 1 else 0
  valid := by
    change 0 < sumFin (fun x : Fin n => if x = v then 1 else 0)
    rw [sumFin_point]
    decide

/-- The constant-output distribution over `Fin (2^k)` concentrated at `0`. -/
def constDist (k : Nat) : FinDist (2 ^ k) :=
  pointDist ⟨0, two_pow_pos k⟩

/-- Skewed full-support distribution with weights `(3, 1)` on `Fin (2^1)`,
sharing the exact support of `uniformDist 1` while having strictly lower
min-entropy (`< 1`). -/
def skewedFullSupportDist : FinDist (2 ^ 1) where
  weight := fun i => if i.val = 0 then 3 else 1
  valid := by unfold ValidWeights; decide

/-- Distribution with weights `(2, 1, 1)` on `Fin 3` (integer min-entropy 1). -/
def dist211 : FinDist 3 where
  weight := fun i => if i.val = 0 then 2 else 1
  valid := by unfold ValidWeights; decide

/-- Distribution with weights `(1, 1, 0)` on `Fin 3`, supported inside
`dist211`, not equal to `dist211`, yet retaining min-entropy `1`. -/
def dist110 : FinDist 3 where
  weight := fun i => if i.val = 2 then 0 else 1
  valid := by unfold ValidWeights; decide

/-! ## Exact Totals, Maxima, and Equivalence Properties -/

theorem totalWeight_uniformDist (k : Nat) :
    totalWeight (uniformDist k) = 2 ^ k := by
  change sumFin (fun _ : Fin (2 ^ k) => 1) = 2 ^ k
  rw [sumFin_const, Nat.mul_one]

theorem maxWeight_uniformDist (k : Nat) :
    maxWeight (uniformDist k) = 1 := by
  change maxFin (fun _ : Fin (2 ^ k) => 1) = 1
  exact maxFin_const_pos (2 ^ k) 1 (two_pow_pos k)

theorem totalWeight_scaledUniformDist (k : Nat) :
    totalWeight (scaledUniformDist k) = 2 ^ k * 2 := by
  change sumFin (fun _ : Fin (2 ^ k) => 2) = 2 ^ k * 2
  exact sumFin_const (2 ^ k) 2

theorem maxWeight_scaledUniformDist (k : Nat) :
    maxWeight (scaledUniformDist k) = 2 := by
  change maxFin (fun _ : Fin (2 ^ k) => 2) = 2
  exact maxFin_const_pos (2 ^ k) 2 (two_pow_pos k)

theorem totalWeight_pointDist {n : Nat} (v : Fin n) :
    totalWeight (pointDist v) = 1 :=
  sumFin_point v

theorem maxWeight_pointDist {n : Nat} (v : Fin n) :
    maxWeight (pointDist v) = 1 :=
  maxFin_point v

theorem uniformDist_exact_minEntropy (k : Nat) :
    HasMinEntropyAtLeast (uniformDist k) k ∧
    ¬ HasMinEntropyAtLeast (uniformDist k) (k + 1) := by
  constructor
  · unfold HasMinEntropyAtLeast
    rw [maxWeight_uniformDist, totalWeight_uniformDist, Nat.one_mul]
    exact Nat.le_refl _
  · unfold HasMinEntropyAtLeast
    rw [maxWeight_uniformDist, totalWeight_uniformDist, Nat.one_mul, Nat.pow_succ]
    have h := two_pow_pos k
    omega

theorem constDist_exact_minEntropy (k : Nat) :
    HasMinEntropyAtLeast (constDist k) 0 ∧
    (∀ m, 0 < m → ¬ HasMinEntropyAtLeast (constDist k) m) := by
  constructor
  · unfold HasMinEntropyAtLeast constDist
    rw [maxWeight_pointDist, totalWeight_pointDist]
    decide
  · intro m hm hEnt
    unfold HasMinEntropyAtLeast constDist at hEnt
    rw [maxWeight_pointDist, totalWeight_pointDist, Nat.one_mul] at hEnt
    have hPow : 2 ≤ 2 ^ m := by
      cases m with
      | zero => omega
      | succ m' =>
        rw [Nat.pow_succ]
        have h := two_pow_pos m'
        omega
    omega

/-- `SameDist` implies trace inclusion on supports. -/
theorem sameDist_imp_support_refines {n : Nat} {d d' : FinDist n}
    (hSame : SameDist d' d) : Refines (support d') (support d) := by
  intro x hx
  have hEq : d'.weight x * totalWeight d = d.weight x * totalWeight d' := hSame x
  have hPos : 0 < d'.weight x * totalWeight d := Nat.mul_pos hx d.valid
  rw [hEq] at hPos
  exact Nat.pos_of_mul_pos_right hPos

theorem sameDist_refl {n : Nat} (d : FinDist n) : SameDist d d :=
  fun _ => rfl

theorem sameDist_symm {n : Nat} {d d' : FinDist n} (h : SameDist d' d) :
    SameDist d d' :=
  fun x => (h x).symm

theorem sameDist_trans {n : Nat} {d₁ d₂ d₃ : FinDist n}
    (h₁₂ : SameDist d₁ d₂) (h₂₃ : SameDist d₂ d₃) : SameDist d₁ d₃ := by
  intro x
  have hA : d₁.weight x * totalWeight d₂ = d₂.weight x * totalWeight d₁ := h₁₂ x
  have hB : d₂.weight x * totalWeight d₃ = d₃.weight x * totalWeight d₂ := h₂₃ x
  have hMul : (d₁.weight x * totalWeight d₃) * totalWeight d₂ =
      (d₃.weight x * totalWeight d₁) * totalWeight d₂ := by
    calc (d₁.weight x * totalWeight d₃) * totalWeight d₂
        = (d₁.weight x * totalWeight d₂) * totalWeight d₃ := by
          rw [Nat.mul_right_comm]
      _ = (d₂.weight x * totalWeight d₁) * totalWeight d₃ := by rw [hA]
      _ = (d₂.weight x * totalWeight d₃) * totalWeight d₁ := by
          rw [Nat.mul_right_comm]
      _ = (d₃.weight x * totalWeight d₂) * totalWeight d₁ := by rw [hB]
      _ = (d₃.weight x * totalWeight d₁) * totalWeight d₂ := by
          rw [Nat.mul_right_comm]
  exact Nat.eq_of_mul_eq_mul_right d₂.valid hMul

/-- Why `ValidWeights` is required for `SameDist` to be transitive: the
all-zero weight function satisfies `ProportionalWeights` against both
`uniformDist 1` and `constDist 1`, which are not proportional to each other. -/
theorem proportionalWeights_without_valid_fails :
    ¬ ValidWeights (fun _ : Fin 2 => 0) ∧
    ProportionalWeights (fun _ : Fin 2 => 0) (uniformDist 1).weight ∧
    ProportionalWeights (fun _ : Fin 2 => 0) (constDist 1).weight ∧
    ¬ ProportionalWeights (uniformDist 1).weight (constDist 1).weight := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold ValidWeights; simp [sumFin]
  · intro x
    simp [sumFin]
  · intro x
    simp [sumFin]
  · intro hProp
    have h1 := hProp ⟨1, by decide⟩
    simp [uniformDist, constDist, pointDist, sumFin] at h1

/-! ## Definition Positive and Negative Examples -/

/-- Positive example for `ValidWeights`: constant weight `1` on `Fin 2`. -/
theorem validWeights_pos_example : ValidWeights (fun _ : Fin 2 => 1) := by
  unfold ValidWeights; simp [sumFin]

/-- Negative example for `ValidWeights`: all-zero weights on `Fin 2`. -/
theorem validWeights_neg_example : ¬ ValidWeights (fun _ : Fin 2 => 0) := by
  unfold ValidWeights; simp [sumFin]

/-- Positive example for `ProportionalWeights`: `(2, 2)` is proportional to
`(1, 1)` on `Fin 2`. -/
theorem proportionalWeights_pos_example :
    ProportionalWeights (scaledUniformDist 1).weight (uniformDist 1).weight := by
  intro x
  change 2 * totalWeight (uniformDist 1) = 1 * totalWeight (scaledUniformDist 1)
  rw [totalWeight_uniformDist, totalWeight_scaledUniformDist]

/-- Negative example for `ProportionalWeights`: `(1, 0)` is not proportional to
`(1, 1)` on `Fin 2`. -/
theorem proportionalWeights_neg_example :
    ¬ ProportionalWeights (constDist 1).weight (uniformDist 1).weight := by
  intro h
  have h1 := h ⟨1, by decide⟩
  simp [constDist, pointDist, uniformDist, sumFin] at h1

/-- Positive example for `RawMinEnt`: uniform weights `(1, 1)` satisfy bound `1`. -/
theorem rawMinEnt_pos_example : RawMinEnt (uniformDist 1).weight 1 :=
  (uniformDist_exact_minEntropy 1).1

/-- Negative example for `RawMinEnt`: point weights `(1, 0)` fail bound `1`. -/
theorem rawMinEnt_neg_example : ¬ RawMinEnt (constDist 1).weight 1 :=
  (constDist_exact_minEntropy 1).2 1 (by decide)

/-- Positive example for `support`: `0` lies in the support of `uniformDist 1`. -/
theorem support_pos_example : support (uniformDist 1) ⟨0, by decide⟩ := by
  unfold support uniformDist; decide

/-- Negative example for `support`: `1` does not lie in the support of
`constDist 1`. -/
theorem support_neg_example : ¬ support (constDist 1) ⟨1, by decide⟩ := by
  unfold support constDist pointDist; decide

/-- Positive example for `RangesOverAll`: `FullRangeSystem 1` ranges over all
elements of `Fin 2`. -/
theorem rangesOverAll_pos_example : RangesOverAll (2 ^ 1) (FullRangeSystem 1) := by
  intro _
  trivial

/-- Negative example for `RangesOverAll`: `ConstSystem 1 0` misses `1`. -/
theorem rangesOverAll_neg_example :
    ¬ RangesOverAll (2 ^ 1) (ConstSystem 1 ⟨0, by decide⟩) := by
  intro h
  have h1 : (⟨1, by decide⟩ : Fin 2) = ⟨0, by decide⟩ := h ⟨1, by decide⟩
  cases h1

/-- Positive example for `HasMinEntropyAtLeast`: `uniformDist 2` has
min-entropy at least `2`. -/
theorem hasMinEntropyAtLeast_pos_example :
    HasMinEntropyAtLeast (uniformDist 2) 2 :=
  (uniformDist_exact_minEntropy 2).1

/-- Negative example for `HasMinEntropyAtLeast`: `constDist 2` does not have
min-entropy at least `1`. -/
theorem hasMinEntropyAtLeast_neg_example :
    ¬ HasMinEntropyAtLeast (constDist 2) 1 :=
  (constDist_exact_minEntropy 2).2 1 (by decide)

/-- Positive example for `SameDist`: `scaledUniformDist 1` has the same
probability distribution as `uniformDist 1` despite different raw weights. -/
theorem sameDist_pos_example : SameDist (scaledUniformDist 1) (uniformDist 1) :=
  proportionalWeights_pos_example

/-- Negative example for `SameDist`: `constDist 1` does not have the same
probability distribution as `uniformDist 1`. -/
theorem sameDist_neg_example : ¬ SameDist (constDist 1) (uniformDist 1) :=
  proportionalWeights_neg_example

/-! ## Possibilistic Full-Range Collapse Under Trace Inclusion -/

/-- For every `k > 0` and every chosen output `v : Fin (2^k)`, the full-range
system over `2^k` values has a nonempty constant-output trace-inclusion
refinement `ConstSystem k v` that fails `RangesOverAll (2^k)`. -/
theorem fullRange_const_refinement_not_rangesOverAll_of_pos
    (k : Nat) (hk : 0 < k) (v : Fin (2 ^ k)) :
    RangesOverAll (2 ^ k) (FullRangeSystem k) ∧
    Refines (ConstSystem k v) (FullRangeSystem k) ∧
    (∃ x, ConstSystem k v x) ∧
    ¬ RangesOverAll (2 ^ k) (ConstSystem k v) := by
  refine ⟨fun _ => trivial, fun _ _ => trivial, ⟨v, rfl⟩, ?_⟩
  intro hAll
  have hGe : 2 ≤ 2 ^ k := by
    cases k with
    | zero => omega
    | succ k' =>
      rw [Nat.pow_succ]
      have h := two_pow_pos k'
      omega
  by_cases hv : v.val = 0
  · have h1 : (⟨1, by omega⟩ : Fin (2 ^ k)) = v := hAll ⟨1, by omega⟩
    have hv1 : (1 : Nat) = v.val := congrArg Fin.val h1
    omega
  · have h0 : (⟨0, by omega⟩ : Fin (2 ^ k)) = v := hAll ⟨0, by omega⟩
    have hv0 : (0 : Nat) = v.val := congrArg Fin.val h0
    omega

/-- Non-vacuity witness for `fullRange_const_refinement_not_rangesOverAll_of_pos`
at `k = 1`, `v = 0` (exposing `0 < 1` together with the instantiated conclusion). -/
theorem fullRange_const_refinement_nonvacuity :
    0 < (1 : Nat) ∧
    RangesOverAll (2 ^ 1) (FullRangeSystem 1) ∧
    Refines (ConstSystem 1 ⟨0, by decide⟩) (FullRangeSystem 1) ∧
    (∃ x, ConstSystem 1 ⟨0, by decide⟩ x) ∧
    ¬ RangesOverAll (2 ^ 1) (ConstSystem 1 ⟨0, by decide⟩) :=
  ⟨by decide, fullRange_const_refinement_not_rangesOverAll_of_pos 1 (by decide) ⟨0, by decide⟩⟩

/-- Tightness counterexample for `hk : 0 < k` in
`fullRange_const_refinement_not_rangesOverAll_of_pos`: at `k = 0`, `Fin (2^0)`
is a singleton so `ConstSystem 0 0` still ranges over all values. -/
theorem fullRange_const_refinement_counterexample_k_zero :
    ¬ (0 < (0 : Nat)) ∧
    RangesOverAll (2 ^ 0) (ConstSystem 0 ⟨0, by decide⟩) := by
  refine ⟨by decide, ?_⟩
  intro ⟨x, hx⟩
  have hx0 : x = 0 := by omega
  subst hx0
  rfl

/-- Negated-full-conclusion form of `fullRange_const_refinement_counterexample_k_zero`
at `k = 0`, `v = 0`. -/
theorem fullRange_const_refinement_not_conclusion_at_zero :
    ¬ (0 < (0 : Nat)) ∧
    ¬ (RangesOverAll (2 ^ 0) (FullRangeSystem 0) ∧
      Refines (ConstSystem 0 ⟨0, by decide⟩) (FullRangeSystem 0) ∧
      (∃ x, ConstSystem 0 ⟨0, by decide⟩ x) ∧
      ¬ RangesOverAll (2 ^ 0) (ConstSystem 0 ⟨0, by decide⟩)) :=
  ⟨by decide, fun h => h.2.2.2 fullRange_const_refinement_counterexample_k_zero.2⟩

/-- Positive control for `fullRange_const_refinement_not_rangesOverAll_of_pos`:
trace equivalence (extensional equality of trace sets, admitting no proper
refinement) preserves `RangesOverAll n`. -/
theorem rangesOverAll_preserved_by_traceEquiv
    (n : Nat) {S S' : System (Fin n)}
    (hEq : TraceEquiv S' S) (hFull : RangesOverAll n S) :
    RangesOverAll n S' :=
  fun x => hEq.2 x (hFull x)

/-! ## Probabilistic Min-Entropy Collapse Under Support Inclusion -/

/-- Min-entropy bounds are downward monotone in `k`: if `H_∞(d) ≥ k₂` and
`k₁ ≤ k₂`, then `H_∞(d) ≥ k₁`. -/
theorem hasMinEntropyAtLeast_mono {n k₁ k₂ : Nat} {d : FinDist n}
    (hle : k₁ ≤ k₂) (hEnt : HasMinEntropyAtLeast d k₂) :
    HasMinEntropyAtLeast d k₁ := by
  unfold HasMinEntropyAtLeast at *
  have hPow : 2 ^ k₁ ≤ 2 ^ k₂ := Nat.pow_le_pow_right (by decide) hle
  exact Nat.le_trans (Nat.mul_le_mul_left (maxWeight d) hPow) hEnt

/-- For every `k > 0`, `uniformDist k` over `2^k` outputs has exact integer
min-entropy `k` (`≥ k` and `¬ ≥ k + 1`), while `constDist k` satisfies trace
inclusion on supports (`Refines (support (constDist k)) (support (uniformDist k))`),
has exact integer min-entropy `0` (`≥ 0` and `¬ ≥ 1`), and fails min-entropy `k`. -/
theorem uniform_support_refined_by_const_loses_minEntropy_of_pos
    (k : Nat) (hk : 0 < k) :
    HasMinEntropyAtLeast (uniformDist k) k ∧
    ¬ HasMinEntropyAtLeast (uniformDist k) (k + 1) ∧
    Refines (support (constDist k)) (support (uniformDist k)) ∧
    HasMinEntropyAtLeast (constDist k) 0 ∧
    ¬ HasMinEntropyAtLeast (constDist k) 1 ∧
    ¬ HasMinEntropyAtLeast (constDist k) k := by
  refine ⟨(uniformDist_exact_minEntropy k).1,
    (uniformDist_exact_minEntropy k).2, ?_,
    (constDist_exact_minEntropy k).1,
    (constDist_exact_minEntropy k).2 1 (by decide),
    (constDist_exact_minEntropy k).2 k hk⟩
  intro _ _
  change 0 < (1 : Nat)
  decide

/-- Non-vacuity witness for
`uniform_support_refined_by_const_loses_minEntropy_of_pos` at `k = 1`. -/
theorem uniform_support_const_refinement_nonvacuity :
    0 < (1 : Nat) ∧
    HasMinEntropyAtLeast (uniformDist 1) 1 ∧
    ¬ HasMinEntropyAtLeast (uniformDist 1) 2 ∧
    Refines (support (constDist 1)) (support (uniformDist 1)) ∧
    HasMinEntropyAtLeast (constDist 1) 0 ∧
    ¬ HasMinEntropyAtLeast (constDist 1) 1 := by
  have h := uniform_support_refined_by_const_loses_minEntropy_of_pos 1 (by decide)
  exact ⟨by decide, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Tightness counterexample for `hk : 0 < k` in
`uniform_support_refined_by_const_loses_minEntropy_of_pos`: at `k = 0`,
`constDist 0` still has min-entropy `0 = k`. -/
theorem uniform_support_const_refinement_counterexample_k_zero :
    ¬ (0 < (0 : Nat)) ∧ HasMinEntropyAtLeast (constDist 0) 0 :=
  ⟨by decide, (constDist_exact_minEntropy 0).1⟩

/-- Negated-full-conclusion form of
`uniform_support_const_refinement_counterexample_k_zero` at `k = 0`. -/
theorem uniform_support_const_refinement_not_conclusion_at_zero :
    ¬ (0 < (0 : Nat)) ∧
    ¬ (HasMinEntropyAtLeast (uniformDist 0) 0 ∧
      ¬ HasMinEntropyAtLeast (uniformDist 0) (0 + 1) ∧
      Refines (support (constDist 0)) (support (uniformDist 0)) ∧
      HasMinEntropyAtLeast (constDist 0) 0 ∧
      ¬ HasMinEntropyAtLeast (constDist 0) 1 ∧
      ¬ HasMinEntropyAtLeast (constDist 0) 0) :=
  ⟨by decide, fun h => h.2.2.2.2.2 uniform_support_const_refinement_counterexample_k_zero.2⟩

/-- Concrete positive control for
`uniform_support_refined_by_const_loses_minEntropy_of_pos`: for every `k`,
`scaledUniformDist k` equals `uniformDist k` as a probability distribution
(with distinct raw weights) and retains min-entropy `k`. Because `SameDist` is
an equivalence relation, this control admits no change in output probabilities. -/
theorem scaledUniform_preserves_minEntropy (k : Nat) :
    SameDist (scaledUniformDist k) (uniformDist k) ∧
    HasMinEntropyAtLeast (scaledUniformDist k) k := by
  constructor
  · intro x
    change 2 * totalWeight (uniformDist k) = 1 * totalWeight (scaledUniformDist k)
    rw [totalWeight_uniformDist, totalWeight_scaledUniformDist]
    rw [Nat.one_mul, Nat.mul_comm]
  · unfold HasMinEntropyAtLeast
    rw [maxWeight_scaledUniformDist, totalWeight_scaledUniformDist, Nat.mul_comm]
    exact Nat.le_refl _

/-- Boundary theorem: even trace equivalence (equal supports) does **not**
preserve min-entropy. `skewedFullSupportDist` (weights `(3, 1)`) and
`uniformDist 1` (weights `(1, 1)`) have identical supports, yet `uniformDist 1`
has min-entropy `1` while `skewedFullSupportDist` does not. -/
theorem same_support_different_minEntropy :
    TraceEquiv (support skewedFullSupportDist) (support (uniformDist 1)) ∧
    HasMinEntropyAtLeast (uniformDist 1) 1 ∧
    ¬ HasMinEntropyAtLeast skewedFullSupportDist 1 := by
  refine ⟨⟨fun _ _ => ?_, fun x _ => ?_⟩, (uniformDist_exact_minEntropy 1).1, ?_⟩
  · show 0 < (1 : Nat)
    decide
  · show 0 < (if x.val = 0 then 3 else 1)
    split <;> decide
  · unfold HasMinEntropyAtLeast maxWeight totalWeight; decide

/-- Boundary theorem: min-entropy is not a function of a distribution's support,
so no `Hyperprop` over `Fin (2^1)` captures `HasMinEntropyAtLeast d 1` on
`support d`. -/
theorem minEntropy_not_a_hyperprop_of_support :
    ¬ ∃ H : Hyperprop (Fin (2 ^ 1)),
        ∀ d : FinDist (2 ^ 1), H (support d) ↔ HasMinEntropyAtLeast d 1 := by
  rintro ⟨H, hH⟩
  have hEq : support skewedFullSupportDist = support (uniformDist 1) :=
    funext fun x => propext
      ⟨same_support_different_minEntropy.1.1 x, same_support_different_minEntropy.1.2 x⟩
  have h1 : H (support (uniformDist 1)) := (hH _).2 same_support_different_minEntropy.2.1
  exact same_support_different_minEntropy.2.2 ((hH skewedFullSupportDist).1 (hEq ▸ h1))

/-! ## Invariance of Min-Entropy Under Weight Rescaling (`SameDist`) -/

/-- Unbundled raw-table core of min-entropy invariance under proportional
weights: only positive total weight of the *source* table `w` (`ValidWeights w`)
is needed; nothing is assumed about `sumFin w'`. -/
theorem proportionalWeights_preserves_minEntropy_of_valid_source
    {n k : Nat} {w' w : Fin n → Nat}
    (hValid : ValidWeights w)
    (hProp : ProportionalWeights w' w)
    (hEnt : RawMinEnt w k) :
    RawMinEnt w' k := by
  unfold RawMinEnt at *
  unfold ValidWeights at hValid
  have hpow := two_pow_pos k
  have hx : ∀ x, w' x ≤ sumFin w' / 2 ^ k := by
    intro x
    rw [Nat.le_div_iff_mul_le hpow]
    apply Nat.le_of_mul_le_mul_right _ hValid
    have h1 : w' x * 2 ^ k * sumFin w = w x * sumFin w' * 2 ^ k := by
      rw [Nat.mul_right_comm, hProp x]
    rw [h1]
    calc w x * sumFin w' * 2 ^ k = (w x * 2 ^ k) * sumFin w' := by rw [Nat.mul_right_comm]
      _ ≤ (maxFin w * 2 ^ k) * sumFin w' :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_maxFin w x))
      _ ≤ sumFin w * sumFin w' := Nat.mul_le_mul_right _ hEnt
      _ = sumFin w' * sumFin w := Nat.mul_comm _ _
  have hm : maxFin w' ≤ sumFin w' / 2 ^ k := (maxFin_le_iff w' _).2 hx
  calc maxFin w' * 2 ^ k ≤ sumFin w' / 2 ^ k * 2 ^ k := Nat.mul_le_mul_right _ hm
    _ ≤ sumFin w' := Nat.div_mul_le_self _ _

/-- An all-zero target weight table trivially satisfies `RawMinEnt` for every
`k`, explaining why target validity (`d'.valid`) is unused in
`proportionalWeights_preserves_minEntropy_of_valid_source`. -/
theorem rawMinEnt_zero_target (n k : Nat) :
    RawMinEnt (fun _ : Fin n => 0) k := by
  unfold RawMinEnt
  rw [maxFin_zero]
  simp

/-- Canonical tightness counterexample for source validity `ValidWeights w` in
`proportionalWeights_preserves_minEntropy_of_valid_source` (and hence `d.valid`
in `sameDist_preserves_minEntropy`): with all-zero source `(0, 0)` and valid
target `(1, 0)`, proportionality and `RawMinEnt` on the source hold at `k = 1`,
yet `RawMinEnt` fails on the target. -/
theorem proportionalWeights_minEntropy_counterexample_source_not_valid :
    ¬ ValidWeights (fun _ : Fin 2 => 0) ∧
    ValidWeights (constDist 1).weight ∧
    ProportionalWeights (constDist 1).weight (fun _ : Fin 2 => 0) ∧
    RawMinEnt (fun _ : Fin 2 => 0) 1 ∧
    ¬ RawMinEnt (constDist 1).weight 1 := by
  refine ⟨validWeights_neg_example, (constDist 1).valid, ?_,
    by unfold RawMinEnt; decide, rawMinEnt_neg_example⟩
  intro x
  show (constDist 1).weight x * sumFin (fun _ : Fin 2 => 0) = 0 * sumFin (constDist 1).weight
  simp [sumFin]

/-- Invariance of min-entropy bounds under weight rescaling (`SameDist`): equal
probability distributions satisfy the same min-entropy lower bounds. Derived
from `proportionalWeights_preserves_minEntropy_of_valid_source` using only
`d.valid` (`d'.valid` is unused in this direction). -/
theorem sameDist_preserves_minEntropy {n k : Nat} {d d' : FinDist n}
    (hSame : SameDist d' d)
    (hEnt : HasMinEntropyAtLeast d k) :
    HasMinEntropyAtLeast d' k :=
  proportionalWeights_preserves_minEntropy_of_valid_source d.valid hSame hEnt

/-- Two-sided invariance corollary (following immediately from `sameDist_symm`):
because `SameDist` is an equivalence relation, min-entropy lower bounds
transfer in both directions (using `d.valid` forward and `d'.valid` backward). -/
theorem sameDist_minEntropy_iff {n k : Nat} {d d' : FinDist n}
    (hSame : SameDist d' d) :
    HasMinEntropyAtLeast d k ↔ HasMinEntropyAtLeast d' k :=
  ⟨sameDist_preserves_minEntropy hSame,
   sameDist_preserves_minEntropy (sameDist_symm hSame)⟩

/-- Non-vacuity witness for `sameDist_preserves_minEntropy`: distinct weight
representations `scaledUniformDist 1` and `uniformDist 1` satisfy both
hypotheses at `k = 1`. -/
theorem sameDist_preserves_minEntropy_nonvacuity :
    SameDist (scaledUniformDist 1) (uniformDist 1) ∧
    HasMinEntropyAtLeast (uniformDist 1) 1 :=
  ⟨sameDist_pos_example, (uniformDist_exact_minEntropy 1).1⟩

/-- Tightness counterexample for `hSame` in `sameDist_preserves_minEntropy`:
`constDist 1` refines the support of `uniformDist 1` (trace inclusion holds),
`uniformDist 1` has min-entropy `1`, yet `SameDist` fails and `constDist 1`
loses min-entropy `1`. -/
theorem sameDist_minEntropy_counterexample_no_sameDist :
    Refines (support (constDist 1)) (support (uniformDist 1)) ∧
    HasMinEntropyAtLeast (uniformDist 1) 1 ∧
    ¬ SameDist (constDist 1) (uniformDist 1) ∧
    ¬ HasMinEntropyAtLeast (constDist 1) 1 :=
  ⟨(uniform_support_refined_by_const_loses_minEntropy_of_pos 1 (by decide)).2.2.1,
   (uniformDist_exact_minEntropy 1).1,
   sameDist_neg_example,
   (constDist_exact_minEntropy 1).2 1 (by decide)⟩

/-- Tightness counterexample for `hEnt` in `sameDist_preserves_minEntropy`:
`constDist 1` satisfies `SameDist` with itself, fails min-entropy `1`, and the
conclusion fails. -/
theorem sameDist_minEntropy_counterexample_no_ent :
    SameDist (constDist 1) (constDist 1) ∧
    ¬ HasMinEntropyAtLeast (constDist 1) 1 :=
  ⟨sameDist_refl (constDist 1), (constDist_exact_minEntropy 1).2 1 (by decide)⟩

/-- Boundary theorem showing `SameDist` is sufficient, not necessary, to keep a
min-entropy bound: `dist110` (weights `(1, 1, 0)`) is supported inside `dist211`
(weights `(2, 1, 1)`), is not equal to `dist211` (`¬ SameDist`), yet keeps
min-entropy `1`. -/
theorem minEntropy_kept_without_sameDist :
    Refines (support dist110) (support dist211) ∧
    ¬ SameDist dist110 dist211 ∧
    HasMinEntropyAtLeast dist211 1 ∧
    ¬ HasMinEntropyAtLeast dist211 2 ∧
    HasMinEntropyAtLeast dist110 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x _
    show 0 < (if x.val = 0 then 2 else 1)
    split <;> decide
  · intro h
    have h2 := h ⟨2, by decide⟩
    revert h2
    decide
  · unfold HasMinEntropyAtLeast maxWeight totalWeight; decide
  · unfold HasMinEntropyAtLeast maxWeight totalWeight; decide
  · unfold HasMinEntropyAtLeast maxWeight totalWeight; decide

end Toy.Hyper
