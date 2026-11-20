/-!
# Sparse linear forms and their dense semantics

A linear form `a · x = Σᵢ aᵢ xᵢ` over integer-valued variables `x : Nat → Int` is
represented sparsely as a finite association list of `(index, coefficient)` pairs.
Duplicate indices are permitted and their coefficients add; this is what a checker
obtains when it concatenates scaled premises without normalizing.

The dense semantics is the coefficient function `SparseVec.coeff v : Nat → Int`
together with the dot product `denseDotOn ks a x = Σ_{i ∈ ks} a i * x i` over an
explicit index list `ks`.
-/

namespace Toy.Farkas

/-- A sparse linear form with integer coefficients: a finite association list of
`(variable index, coefficient)` pairs. Duplicate indices are allowed and add up. -/
abbrev SparseVec := List (Nat × Int)

namespace SparseVec

/-- Dense coefficient of variable `i`: the sum of every coefficient recorded for `i`
(so duplicates add, and an index that does not occur has coefficient `0`). -/
def coeff (v : SparseVec) (i : Nat) : Int :=
  (v.map (fun p => if p.1 = i then p.2 else 0)).sum

/-- Evaluation of the form at an integer point `x`: `Σ c * x i` over entries `(i, c)`. -/
def eval (v : SparseVec) (x : Nat → Int) : Int :=
  (v.map (fun p => p.2 * x p.1)).sum

/-- Scalar multiple `l • v`, entrywise on coefficients. -/
def smul (l : Int) (v : SparseVec) : SparseVec :=
  v.map (fun p => (p.1, l * p.2))

/-- Decidable zero test for the dense semantics: every mentioned index has total
coefficient `0`. Indices that are not mentioned have coefficient `0` by definition. -/
def isZero (v : SparseVec) : Bool :=
  v.all (fun p => v.coeff p.1 == 0)

/-- One more than the largest mentioned index (`0` for the empty form). -/
def bound (v : SparseVec) : Nat := v.foldr (fun p m => max (p.1 + 1) m) 0

theorem lt_bound (v : SparseVec) : ∀ p ∈ v, p.1 < v.bound := by
  induction v with
  | nil => simp
  | cons a v ih =>
    intro p hp
    simp only [bound, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hp with h | h
    · subst h; omega
    · have := ih p h; omega

end SparseVec

/-- Dense dot product `Σ_{i ∈ ks} a i * x i` over an explicit index list `ks`. -/
def denseDotOn (ks : List Nat) (a x : Nat → Int) : Int :=
  (ks.map (fun i => a i * x i)).sum

/-- Dense dot product over the index range `0, …, n-1`. -/
def denseDot (n : Nat) (a x : Nat → Int) : Int :=
  denseDotOn (List.range n) a x

/-! ## Definition examples -/

/-- Positive example: duplicate indices add in the dense semantics. -/
theorem ex_coeff_duplicates_add : SparseVec.coeff [(0, 1), (1, 5), (0, 2)] 0 = 3 := by decide

/-- Negative example: the dense coefficient is not a first-match lookup (which would give `1`). -/
theorem ex_coeff_not_first_match : SparseVec.coeff [(0, 1), (1, 5), (0, 2)] 0 ≠ 1 := by decide

/-- Positive example: `eval [(0,2),(1,-3)]` at `x = (5, 1, …)` is `2*5 - 3*1 = 7`. -/
theorem ex_eval_pos : SparseVec.eval [(0, 2), (1, -3)] (fun i => if i = 0 then 5 else 1) = 7 := by
  decide

/-- Negative example: evaluation uses every entry, not only the first one. -/
theorem ex_eval_neg : SparseVec.eval [(0, 2), (1, -3)] (fun i => if i = 0 then 5 else 1) ≠ 10 := by
  decide

/-- Positive example: `smul` scales every coefficient. -/
theorem ex_smul_pos : SparseVec.smul 3 [(0, 2), (1, -1)] = [(0, 6), (1, -3)] := by decide

/-- Negative example: `smul` does not scale indices. -/
theorem ex_smul_neg : SparseVec.smul 3 [(1, 2)] ≠ [(3, 6)] := by decide

/-- Positive example: a form whose duplicate entries cancel is recognised as zero
even though its list of entries is non-empty. -/
theorem ex_isZero_pos : SparseVec.isZero [(0, 1), (1, 4), (0, -1), (1, -4)] = true := by decide

/-- Negative example: a form with a surviving coefficient is not zero. -/
theorem ex_isZero_neg : SparseVec.isZero [(0, 1), (1, 4), (0, -1)] = false := by decide

/-- Positive example: dense dot product over an explicit index list. -/
theorem ex_denseDotOn_pos :
    denseDotOn [0, 2] (fun i => (i : Int) + 1) (fun _ => 2) = 8 := by decide

/-- Negative example: indices outside the list do not contribute. -/
theorem ex_denseDotOn_neg :
    denseDotOn [0, 2] (fun i => (i : Int) + 1) (fun _ => 2) ≠ 12 := by decide

/-- Positive example: `denseDot 3` sums over indices `0, 1, 2`. -/
theorem ex_denseDot_pos : denseDot 3 (fun i => (i : Int)) (fun _ => 1) = 3 := by decide

/-- Negative example: `denseDot 3` does not include index `3`. -/
theorem ex_denseDot_neg : denseDot 3 (fun i => (i : Int)) (fun _ => 1) ≠ 6 := by decide

/-! ## Algebra of the dense semantics -/

/-- Positive example: `bound` is one more than the largest mentioned index. -/
theorem ex_bound_pos : SparseVec.bound [(3, 1), (7, 0), (2, 5)] = 8 := by decide

/-- Negative example: `bound` is not the number of entries. -/
theorem ex_bound_neg : SparseVec.bound [(3, 1), (7, 0), (2, 5)] ≠ 3 := by decide

namespace SparseVec

@[simp] theorem coeff_nil (i : Nat) : coeff [] i = 0 := rfl

@[simp] theorem coeff_cons (a : Nat × Int) (v : SparseVec) (i : Nat) :
    coeff (a :: v) i = (if a.1 = i then a.2 else 0) + coeff v i := by
  simp [coeff]

@[simp] theorem eval_nil (x : Nat → Int) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (a : Nat × Int) (v : SparseVec) (x : Nat → Int) :
    eval (a :: v) x = a.2 * x a.1 + eval v x := by
  simp [eval]

theorem coeff_append (v w : SparseVec) (i : Nat) :
    coeff (v ++ w) i = coeff v i + coeff w i := by
  induction v with
  | nil => simp
  | cons a v ih => simp [ih, Int.add_assoc]

theorem eval_append (v w : SparseVec) (x : Nat → Int) :
    eval (v ++ w) x = eval v x + eval w x := by
  induction v with
  | nil => simp
  | cons a v ih => simp [ih, Int.add_assoc]

theorem coeff_smul (l : Int) (v : SparseVec) (i : Nat) :
    coeff (smul l v) i = l * coeff v i := by
  induction v with
  | nil => simp [smul]
  | cons a v ih =>
    simp only [smul, List.map_cons, coeff_cons] at ih ⊢
    rw [ih, Int.mul_add]
    split <;> simp

theorem eval_smul (l : Int) (v : SparseVec) (x : Nat → Int) :
    eval (smul l v) x = l * eval v x := by
  induction v with
  | nil => simp [smul]
  | cons a v ih =>
    simp only [smul, List.map_cons, eval_cons] at ih ⊢
    rw [ih, Int.mul_add, Int.mul_assoc]

theorem coeff_eq_zero_of_not_mem (v : SparseVec) (i : Nat) (h : ∀ p ∈ v, p.1 ≠ i) :
    coeff v i = 0 := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    rw [coeff_cons, ite_eq_right (h a (List.mem_cons_self ..)),
      ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    rfl

end SparseVec

theorem denseDotOn_nil (a x : Nat → Int) : denseDotOn [] a x = 0 := rfl

theorem denseDotOn_cons (k : Nat) (ks : List Nat) (a x : Nat → Int) :
    denseDotOn (k :: ks) a x = a k * x k + denseDotOn ks a x := by
  simp [denseDotOn]

theorem denseDotOn_add (ks : List Nat) (a b x : Nat → Int) :
    denseDotOn ks (fun i => a i + b i) x = denseDotOn ks a x + denseDotOn ks b x := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [denseDotOn_cons, denseDotOn_cons, denseDotOn_cons, ih, Int.add_mul]
    omega

theorem denseDotOn_zero (ks : List Nat) (x : Nat → Int) :
    denseDotOn ks (fun _ => 0) x = 0 := by
  induction ks with
  | nil => rfl
  | cons k ks ih => rw [denseDotOn_cons, ih, Int.zero_mul]; rfl

theorem denseDotOn_congr (ks : List Nat) (a b x : Nat → Int) (h : ∀ i ∈ ks, a i = b i) :
    denseDotOn ks a x = denseDotOn ks b x := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [denseDotOn_cons, denseDotOn_cons, h k (List.mem_cons_self ..),
      ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

theorem denseDotOn_single_of_not_mem (ks : List Nat) (j : Nat) (c : Int) (x : Nat → Int)
    (h : j ∉ ks) : denseDotOn ks (fun i => if j = i then c else 0) x = 0 := by
  rw [denseDotOn_congr ks _ (fun _ => 0) x, denseDotOn_zero]
  intro i hi
  have : j ≠ i := fun hji => h (hji ▸ hi)
  simp [this]

theorem denseDotOn_single (ks : List Nat) (j : Nat) (c : Int) (x : Nat → Int)
    (hnd : ks.Nodup) (hj : j ∈ ks) :
    denseDotOn ks (fun i => if j = i then c else 0) x = c * x j := by
  induction ks with
  | nil => simp at hj
  | cons k ks ih =>
    rw [List.nodup_cons] at hnd
    rw [denseDotOn_cons]
    by_cases hjk : j = k
    · subst hjk
      rw [denseDotOn_single_of_not_mem ks j c x hnd.1]
      simp
    · have hj' : j ∈ ks := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h hjk
        · exact h
      rw [ih hnd.2 hj', ite_eq_right hjk, Int.zero_mul, Int.zero_add]

/-! ## Sparse evaluation agrees with the dense semantics -/

/-- **Sparse = dense (general index list).** For any duplicate-free index list `ks`
that contains every index mentioned by `v`, sparse evaluation of `v` equals the dense
dot product of its coefficient function over `ks`. -/
theorem SparseVec.eval_eq_denseDotOn_coeff_of_nodup_of_keys_mem (v : SparseVec) (ks : List Nat)
    (hnd : ks.Nodup) (hmem : ∀ p ∈ v, p.1 ∈ ks) (x : Nat → Int) :
    v.eval x = denseDotOn ks v.coeff x := by
  induction v with
  | nil =>
    rw [SparseVec.eval_nil]
    exact (denseDotOn_zero ks x).symm
  | cons a v ih =>
    have hv : ∀ p ∈ v, p.1 ∈ ks := fun p hp => hmem p (List.mem_cons_of_mem _ hp)
    rw [SparseVec.eval_cons, ih hv]
    have : (SparseVec.coeff (a :: v)) =
        fun i => (if a.1 = i then a.2 else 0) + SparseVec.coeff v i := by
      funext i; exact SparseVec.coeff_cons a v i
    rw [this, denseDotOn_add, denseDotOn_single ks a.1 a.2 x hnd (hmem a (List.mem_cons_self ..))]

/-- **Sparse = dense (index range).** If every index mentioned by `v` is `< n`, then
sparse evaluation equals `Σ_{i < n} coeff v i * x i`. -/
theorem SparseVec.eval_eq_denseDot_coeff_of_keys_lt (v : SparseVec) (n : Nat)
    (h : ∀ p ∈ v, p.1 < n) (x : Nat → Int) :
    v.eval x = denseDot n v.coeff x :=
  SparseVec.eval_eq_denseDotOn_coeff_of_nodup_of_keys_mem v (List.range n) List.nodup_range
    (fun p hp => List.mem_range.mpr (h p hp)) x

/-- **Zero test characterization.** The decidable test `isZero` accepts exactly the
forms whose dense coefficient function is identically zero. -/
theorem SparseVec.isZero_iff_coeff_eq_zero (v : SparseVec) :
    v.isZero = true ↔ ∀ i, v.coeff i = 0 := by
  constructor
  · intro h i
    by_cases hi : ∃ p ∈ v, p.1 = i
    · obtain ⟨p, hp, rfl⟩ := hi
      have := List.all_eq_true.mp h p hp
      simpa using this
    · exact SparseVec.coeff_eq_zero_of_not_mem v i (fun p hp hpi => hi ⟨p, hp, hpi⟩)
  · intro h
    apply List.all_eq_true.mpr
    intro p _
    simp [h p.1]

/-- A form accepted by `isZero` evaluates to `0` at every integer point. -/
theorem SparseVec.eval_eq_zero_of_isZero (v : SparseVec) (h : v.isZero = true)
    (x : Nat → Int) : v.eval x = 0 := by
  have hc := (SparseVec.isZero_iff_coeff_eq_zero v).mp h
  rw [SparseVec.eval_eq_denseDot_coeff_of_keys_lt v v.bound (SparseVec.lt_bound v) x, denseDot,
    denseDotOn_congr _ _ (fun _ => 0) x (fun i _ => hc i), denseDotOn_zero]

/-! ## Sparse = dense: tightness and non-vacuity -/

/-- Non-vacuity of the general sparse=dense theorem: a form with a duplicate index, an index
list in a different order, both hypotheses hold and the values agree. -/
theorem nv_eval_eq_denseDotOn :
    ([1, 0] : List Nat).Nodup ∧ (∀ p ∈ ([(0, 2), (1, -3), (0, 1)] : SparseVec), p.1 ∈ [1, 0]) ∧
    SparseVec.eval [(0, 2), (1, -3), (0, 1)] (fun i => (i : Int) + 4) =
      denseDotOn [1, 0] (SparseVec.coeff [(0, 2), (1, -3), (0, 1)]) (fun i => (i : Int) + 4) := by
  decide

/-- Non-vacuity of the range form. -/
theorem nv_eval_eq_denseDot :
    (∀ p ∈ ([(0, 2), (2, -3), (0, 1)] : SparseVec), p.1 < 3) ∧
    SparseVec.eval [(0, 2), (2, -3), (0, 1)] (fun i => (i : Int) + 4) =
      denseDot 3 (SparseVec.coeff [(0, 2), (2, -3), (0, 1)]) (fun i => (i : Int) + 4) := by
  decide

/-- Tightness (`Nodup`): with the index list `[0, 0]` every index is covered but index `0`
is counted twice. -/
theorem ce_eval_eq_denseDotOn_duplicate_index_list :
    ¬ ([0, 0] : List Nat).Nodup ∧ (∀ p ∈ ([(0, 1)] : SparseVec), p.1 ∈ [0, 0]) ∧
    SparseVec.eval [(0, 1)] (fun _ => 1) ≠ denseDotOn [0, 0] (SparseVec.coeff [(0, 1)]) (fun _ => 1) := by
  decide

/-- Tightness (coverage): the index list `[0]` is duplicate-free but misses index `1`. -/
theorem ce_eval_eq_denseDotOn_missing_index :
    ([0] : List Nat).Nodup ∧ ¬ (∀ p ∈ ([(1, 1)] : SparseVec), p.1 ∈ [0]) ∧
    SparseVec.eval [(1, 1)] (fun _ => 1) ≠ denseDotOn [0] (SparseVec.coeff [(1, 1)]) (fun _ => 1) := by
  decide

/-- Tightness (range bound): index `1` is not `< 1`. -/
theorem ce_eval_eq_denseDot_index_out_of_range :
    ¬ (∀ p ∈ ([(1, 1)] : SparseVec), p.1 < 1) ∧
    SparseVec.eval [(1, 1)] (fun _ => 1) ≠ denseDot 1 (SparseVec.coeff [(1, 1)]) (fun _ => 1) := by
  decide

/-- Non-vacuity of the zero-test characterization: a non-empty form with cancelling duplicates. -/
theorem nv_isZero_iff : SparseVec.isZero [(3, 2), (3, -2)] = true ∧
    SparseVec.coeff [(3, 2), (3, -2)] 3 = 0 := by decide

end Toy.Farkas
