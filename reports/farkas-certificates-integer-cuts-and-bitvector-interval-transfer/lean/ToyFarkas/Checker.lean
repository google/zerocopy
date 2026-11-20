import ToyFarkas.Constraint

/-!
# The Farkas certificate checker

A certificate for a system `S = [c₀, …, c_{m-1}]` is a list of integer multipliers
`cert = [λ₀, …]`. The checker forms the combination `Σ λₖ · cₖ` (multiplier `k` paired
with constraint `k`; `List.zipWith` pairs them and ignores unpaired entries, so a short
certificate gives implicit multiplier `0` to the remaining constraints) and accepts iff

1. every multiplier is non-negative (`multipliersNonneg`);
2. the combined left-hand side is the zero form in the dense semantics (`lhsVanishes`);
3. the combined right-hand side makes `0 ⋈ rhs` false (`rhsContradicts`), where `⋈` is
   `<` when some *positively weighted* premise is strict, and `≤` otherwise.

So the derived conclusion is the trivially false `0 ≤ -c` with `c > 0`, or `0 < -c`
with `c ≥ 0`.
-/

namespace Toy.Farkas

/-- Every multiplier is non-negative. -/
def multipliersNonneg (cert : List Int) : Bool :=
  cert.all (fun l => decide (0 ≤ l))

/-- Sparse left-hand side of the combination `Σ λₖ · cₖ`: the scaled premises concatenated,
without normalization (duplicate indices may occur). -/
def combineLhs (S : List Constraint) (cert : List Int) : SparseVec :=
  (List.zipWith (fun l c => SparseVec.smul l c.lhs) cert S).flatten

/-- Right-hand side of the combination: `Σ λₖ * rhsₖ`. -/
def combineRhs (S : List Constraint) (cert : List Int) : Int :=
  (List.zipWith (fun l c => l * c.rhs) cert S).sum

/-- The combination is strict iff some premise with a *positive* multiplier is strict. -/
def combineStrict (S : List Constraint) (cert : List Int) : Bool :=
  (List.zipWith (fun l c => decide (0 < l) && c.isStrict) cert S).any id

/-- The combined left-hand side is the zero form. -/
def lhsVanishes (S : List Constraint) (cert : List Int) : Bool :=
  (combineLhs S cert).isZero

/-- The combined conclusion `0 ⋈ rhs` is false: `rhs ≤ 0` if the combination is strict,
`rhs < 0` otherwise. -/
def rhsContradicts (S : List Constraint) (cert : List Int) : Bool :=
  if combineStrict S cert then decide (combineRhs S cert ≤ 0) else decide (combineRhs S cert < 0)

/-- **The Farkas certificate checker** (a decidable Boolean function). -/
def checkFarkas (S : List Constraint) (cert : List Int) : Bool :=
  multipliersNonneg cert && lhsVanishes S cert && rhsContradicts S cert

/-! ## Definition examples -/

/-- The system `{x₀ ≤ 1, -x₀ ≤ -2}` (i.e. `x₀ ≤ 1 ∧ x₀ ≥ 2`). -/
def sysLeGe : List Constraint := [⟨[(0, 1)], .le, 1⟩, ⟨[(0, -1)], .le, -2⟩]

/-- The system `{x₀ ≤ 1, -x₀ ≤ -1}` (i.e. `x₀ = 1`), which is satisfiable. -/
def sysEq : List Constraint := [⟨[(0, 1)], .le, 1⟩, ⟨[(0, -1)], .le, -1⟩]

/-- The system `{x₀ < 1, -x₀ ≤ -1}` (i.e. `x₀ < 1 ∧ x₀ ≥ 1`), infeasible only because of strictness. -/
def sysStrict : List Constraint := [⟨[(0, 1)], .lt, 1⟩, ⟨[(0, -1)], .le, -1⟩]

theorem ex_multipliersNonneg_pos : multipliersNonneg [0, 3, 1] = true := by decide
theorem ex_multipliersNonneg_neg : multipliersNonneg [0, -3, 1] = false := by decide

/-- Positive example: combining `sysLeGe` with `(1, 1)` gives the (unnormalized) zero form
`x₀ - x₀`. -/
theorem ex_combineLhs_pos : combineLhs sysLeGe [1, 1] = [(0, 1), (0, -1)] := by decide
/-- Negative example: the combination is not normalized (it is not the empty list). -/
theorem ex_combineLhs_neg : combineLhs sysLeGe [1, 1] ≠ [] := by decide

theorem ex_combineRhs_pos : combineRhs sysLeGe [1, 1] = -1 := by decide
theorem ex_combineRhs_neg : combineRhs sysLeGe [2, 1] ≠ -1 := by decide

/-- Positive example: a positively weighted strict premise makes the combination strict. -/
theorem ex_combineStrict_pos : combineStrict sysStrict [1, 1] = true := by decide
/-- Negative example: a strict premise with multiplier `0` does not. -/
theorem ex_combineStrict_neg : combineStrict sysStrict [0, 1] = false := by decide

theorem ex_lhsVanishes_pos : lhsVanishes sysLeGe [1, 1] = true := by decide
theorem ex_lhsVanishes_neg : lhsVanishes sysLeGe [1, 2] = false := by decide

/-- Positive example: `0 ≤ -1` is contradictory. -/
theorem ex_rhsContradicts_pos : rhsContradicts sysLeGe [1, 1] = true := by decide
/-- Negative example: `0 ≤ 0` (non-strict) is not contradictory. -/
theorem ex_rhsContradicts_neg : rhsContradicts sysEq [1, 1] = false := by decide

/-- Positive example: `(1, 1)` certifies infeasibility of `sysLeGe`. -/
theorem ex_checkFarkas_pos : checkFarkas sysLeGe [1, 1] = true := by decide
/-- Positive example: `(1, 1)` certifies infeasibility of `sysStrict` through `0 < 0`. -/
theorem ex_checkFarkas_strict_pos : checkFarkas sysStrict [1, 1] = true := by decide
/-- Negative example: the satisfiable `sysEq` is rejected for every small certificate. -/
theorem ex_checkFarkas_neg :
    ∀ a b : Fin 5, checkFarkas sysEq [(a : Int) - 2, (b : Int) - 2] = false := by decide

/-- Pairing semantics: a short certificate gives the remaining constraints multiplier `0`. -/
theorem ex_checkFarkas_short_certificate :
    checkFarkas (sysLeGe ++ [⟨[(1, 1)], .le, 5⟩]) [1, 1] = true := by decide

/-- Pairing semantics: surplus multipliers are ignored by the combination but must still be
non-negative. -/
theorem ex_checkFarkas_surplus_multipliers :
    checkFarkas sysLeGe [1, 1, 7] = true ∧ checkFarkas sysLeGe [1, 1, -7] = false := by decide

/-! ## The sparse combination agrees with the dense combination -/

theorem coeff_flatten (L : List SparseVec) (i : Nat) :
    SparseVec.coeff L.flatten i = (L.map (fun v => SparseVec.coeff v i)).sum := by
  induction L with
  | nil => rfl
  | cons v L ih => simp [List.flatten_cons, SparseVec.coeff_append, ih]

theorem eval_flatten (L : List SparseVec) (x : Nat → Int) :
    SparseVec.eval L.flatten x = (L.map (fun v => SparseVec.eval v x)).sum := by
  induction L with
  | nil => rfl
  | cons v L ih => simp [List.flatten_cons, SparseVec.eval_append, ih]

/-- **Sparse combination = dense combination (coefficients).** The dense coefficient of the
sparse combination at index `i` is `Σₖ λₖ * coeff (lhsₖ) i`. -/
theorem combineLhs_coeff (S : List Constraint) (cert : List Int) (i : Nat) :
    SparseVec.coeff (combineLhs S cert) i =
      (List.zipWith (fun l c => l * SparseVec.coeff c.lhs i) cert S).sum := by
  induction cert generalizing S with
  | nil => simp [combineLhs]
  | cons l cert ih =>
    cases S with
    | nil => simp [combineLhs]
    | cons c S =>
      have := ih S
      simp only [combineLhs] at this ⊢
      simp [List.flatten_cons, SparseVec.coeff_append, SparseVec.coeff_smul, this]

/-- **Sparse combination = dense combination (values).** Evaluating the sparse combination
equals `Σₖ λₖ * (lhsₖ · x)`. -/
theorem combineLhs_eval (S : List Constraint) (cert : List Int) (x : Nat → Int) :
    SparseVec.eval (combineLhs S cert) x =
      (List.zipWith (fun l c => l * SparseVec.eval c.lhs x) cert S).sum := by
  induction cert generalizing S with
  | nil => simp [combineLhs]
  | cons l cert ih =>
    cases S with
    | nil => simp [combineLhs]
    | cons c S =>
      have := ih S
      simp only [combineLhs] at this ⊢
      simp [List.flatten_cons, SparseVec.eval_append, SparseVec.eval_smul, this]

/-! ## Soundness of the Farkas checker -/

/-- The combination of satisfied premises with non-negative multipliers is satisfied, with
strict inequality when some positively weighted premise is strict. -/
theorem combine_holdsScaled (S : List Constraint) (cert : List Int) (d : Int) (p : Nat → Int)
    (hnn : ∀ l ∈ cert, 0 ≤ l) (hS : SatScaled S d p) :
    SparseVec.eval (combineLhs S cert) p ≤ combineRhs S cert * d ∧
      (combineStrict S cert = true → SparseVec.eval (combineLhs S cert) p < combineRhs S cert * d) := by
  induction cert generalizing S with
  | nil => simp [combineLhs, combineRhs, combineStrict]
  | cons l cert ih =>
    cases S with
    | nil => simp [combineLhs, combineRhs, combineStrict]
    | cons c S =>
      have hl : 0 ≤ l := hnn l (List.mem_cons_self ..)
      have ih' := ih S (fun l' h => hnn l' (List.mem_cons_of_mem _ h))
        (fun c' h => hS c' (List.mem_cons_of_mem _ h))
      have hc : c.HoldsScaled d p := hS c (List.mem_cons_self ..)
      have e1 : SparseVec.eval (combineLhs (c :: S) (l :: cert)) p =
          l * SparseVec.eval c.lhs p + SparseVec.eval (combineLhs S cert) p := by
        simp [combineLhs, List.flatten_cons, SparseVec.eval_append, SparseVec.eval_smul]
      have e2 : combineRhs (c :: S) (l :: cert) * d = l * (c.rhs * d) + combineRhs S cert * d := by
        simp [combineRhs, Int.add_mul, Int.mul_assoc]
      have e3 : combineStrict (c :: S) (l :: cert) =
          ((decide (0 < l) && c.isStrict) || combineStrict S cert) := by
        simp [combineStrict]
      rw [e1, e2, e3]
      -- the head premise, scaled by `l ≥ 0`
      have hle : SparseVec.eval c.lhs p ≤ c.rhs * d := by
        unfold Constraint.HoldsScaled at hc
        cases hr : c.rel <;> rw [hr] at hc <;> simp [Rel.Sat] at hc <;> omega
      have hhead : l * SparseVec.eval c.lhs p ≤ l * (c.rhs * d) :=
        Int.mul_le_mul_of_nonneg_left hle hl
      refine ⟨Int.add_le_add hhead ih'.1, ?_⟩
      intro hs
      rcases Bool.or_eq_true_iff.mp hs with h | h
      · have hlpos : 0 < l := by simpa using (Bool.and_eq_true_iff.mp h).1
        have hstr : c.isStrict = true := (Bool.and_eq_true_iff.mp h).2
        have hlt : SparseVec.eval c.lhs p < c.rhs * d := by
          unfold Constraint.HoldsScaled at hc
          cases hr : c.rel <;> simp [Constraint.isStrict, hr] at hstr
          rw [hr] at hc; exact hc
        exact Int.add_lt_add_of_lt_of_le (Int.mul_lt_mul_of_pos_left hlt hlpos) ih'.1
      · exact Int.add_lt_add_of_le_of_lt hhead (ih'.2 h)

/-- **Farkas soundness, scaled points (structured form).** If the multipliers are
non-negative, the combined left-hand side vanishes, and the combined right-hand side is
contradictory, then no scaled point `(d, p)` with `d > 0` satisfies `S`. (Through the modeling
bridge in `ToyFarkas.Constraint`: the finite system `S` has no rational solution.) -/
theorem farkas_sound_scaled_of_nonneg_of_lhsVanishes_of_rhsContradicts
    (S : List Constraint) (cert : List Int)
    (hnn : multipliersNonneg cert = true)
    (hlhs : lhsVanishes S cert = true)
    (hrhs : rhsContradicts S cert = true)
    (d : Int) (hd : 0 < d) (p : Nat → Int) :
    ¬ SatScaled S d p := by
  intro hS
  have hnn' : ∀ l ∈ cert, 0 ≤ l := by
    intro l hl
    simpa using List.all_eq_true.mp hnn l hl
  have h0 : SparseVec.eval (combineLhs S cert) p = 0 :=
    SparseVec.eval_eq_zero_of_isZero _ hlhs p
  obtain ⟨hle, hlt⟩ := combine_holdsScaled S cert d p hnn' hS
  rw [h0] at hle hlt
  unfold rhsContradicts at hrhs
  split at hrhs
  · rename_i hs
    have hR : combineRhs S cert ≤ 0 := by simpa using hrhs
    have := hlt hs
    have : combineRhs S cert * d ≤ 0 * d := Int.mul_le_mul_of_nonneg_right hR (Int.le_of_lt hd)
    omega
  · have hR : combineRhs S cert < 0 := by simpa using hrhs
    have : combineRhs S cert * d < 0 * d := Int.mul_lt_mul_of_pos_right hR hd
    omega

/-- **Farkas soundness, scaled points.** If `checkFarkas S cert = true`, then no scaled
point `(d, p)` with `d > 0` satisfies `S`. (Through the modeling bridge in
`ToyFarkas.Constraint`: the finite system `S` has no rational solution.) -/
theorem checkFarkas_sound_scaled (S : List Constraint) (cert : List Int)
    (h : checkFarkas S cert = true) (d : Int) (hd : 0 < d) (p : Nat → Int) :
    ¬ SatScaled S d p := by
  simp only [checkFarkas, Bool.and_eq_true] at h
  exact farkas_sound_scaled_of_nonneg_of_lhsVanishes_of_rhsContradicts S cert h.1.1 h.1.2 h.2 d hd p

/-- **Farkas soundness, integer points.** If `checkFarkas S cert = true`, then no integer
point satisfies `S`. (The special case `d = 1` of `checkFarkas_sound_scaled`.) -/
theorem checkFarkas_sound_int (S : List Constraint) (cert : List Int)
    (h : checkFarkas S cert = true) (x : Nat → Int) :
    ¬ SatInt S x := by
  rw [satInt_iff_satScaled_one]
  exact checkFarkas_sound_scaled S cert h 1 (by decide) x

/-! ## Only positively weighted premises matter -/

/-- The premises of `S` that the certificate weights positively (multiplier `k` paired with
premise `k`, as in `List.zipWith`; unpaired premises and premises with multiplier `≤ 0` are
dropped). -/
def posSupport {α : Type} (cert : List Int) (S : List α) : List α :=
  ((cert.zip S).filter (fun q => decide (0 < q.1))).map Prod.snd

theorem posSupport_cons_cons {α : Type} (l : Int) (cert : List Int) (c : α) (S : List α) :
    posSupport (l :: cert) (c :: S) = if 0 < l then c :: posSupport cert S else posSupport cert S := by
  by_cases hl : 0 < l <;> simp [posSupport, hl]

theorem posSupport_map {α β : Type} (f : α → β) (cert : List Int) (S : List α) :
    posSupport cert (S.map f) = (posSupport cert S).map f := by
  induction cert generalizing S with
  | nil => simp [posSupport]
  | cons l cert ih =>
    cases S with
    | nil => simp [posSupport]
    | cons c S =>
      rw [List.map_cons, posSupport_cons_cons, posSupport_cons_cons, ih]
      split <;> simp

theorem mem_of_mem_posSupport {α : Type} {cert : List Int} {S : List α} {c : α}
    (h : c ∈ posSupport cert S) : c ∈ S := by
  simp only [posSupport, List.mem_map, List.mem_filter] at h
  obtain ⟨⟨l, c'⟩, ⟨hz, _⟩, rfl⟩ := h
  exact List.of_mem_zip hz |>.2

/-- The combination with non-negative multipliers holds as soon as the positively weighted
premises hold. -/
theorem combine_holdsScaled_of_posSupport (S : List Constraint) (cert : List Int) (d : Int)
    (p : Nat → Int) (hnn : ∀ l ∈ cert, 0 ≤ l) (hS : SatScaled (posSupport cert S) d p) :
    SparseVec.eval (combineLhs S cert) p ≤ combineRhs S cert * d ∧
      (combineStrict S cert = true → SparseVec.eval (combineLhs S cert) p < combineRhs S cert * d) := by
  induction cert generalizing S with
  | nil => simp [combineLhs, combineRhs, combineStrict]
  | cons l cert ih =>
    cases S with
    | nil => simp [combineLhs, combineRhs, combineStrict]
    | cons c S =>
      have hl : 0 ≤ l := hnn l (List.mem_cons_self ..)
      rw [posSupport_cons_cons] at hS
      have hrest : SatScaled (posSupport cert S) d p := by
        intro c' hc'
        split at hS
        · exact hS c' (List.mem_cons_of_mem _ hc')
        · exact hS c' hc'
      have ih' := ih S (fun l' h => hnn l' (List.mem_cons_of_mem _ h)) hrest
      have e1 : SparseVec.eval (combineLhs (c :: S) (l :: cert)) p =
          l * SparseVec.eval c.lhs p + SparseVec.eval (combineLhs S cert) p := by
        simp [combineLhs, List.flatten_cons, SparseVec.eval_append, SparseVec.eval_smul]
      have e2 : combineRhs (c :: S) (l :: cert) * d = l * (c.rhs * d) + combineRhs S cert * d := by
        simp [combineRhs, Int.add_mul, Int.mul_assoc]
      have e3 : combineStrict (c :: S) (l :: cert) =
          ((decide (0 < l) && c.isStrict) || combineStrict S cert) := by
        simp [combineStrict]
      rw [e1, e2, e3]
      by_cases hlpos : 0 < l
      · simp only [hlpos, ↓reduceIte] at hS
        have hc : c.HoldsScaled d p := hS c (List.mem_cons_self ..)
        have hle : SparseVec.eval c.lhs p ≤ c.rhs * d := by
          unfold Constraint.HoldsScaled at hc
          cases hr : c.rel <;> rw [hr] at hc <;> simp [Rel.Sat] at hc <;> omega
        have hhead : l * SparseVec.eval c.lhs p ≤ l * (c.rhs * d) :=
          Int.mul_le_mul_of_nonneg_left hle hl
        refine ⟨Int.add_le_add hhead ih'.1, ?_⟩
        intro hs
        rcases Bool.or_eq_true_iff.mp hs with h | h
        · have hstr : c.isStrict = true := (Bool.and_eq_true_iff.mp h).2
          have hlt : SparseVec.eval c.lhs p < c.rhs * d := by
            unfold Constraint.HoldsScaled at hc
            cases hr : c.rel <;> simp [Constraint.isStrict, hr] at hstr
            rw [hr] at hc; exact hc
          exact Int.add_lt_add_of_lt_of_le (Int.mul_lt_mul_of_pos_left hlt hlpos) ih'.1
        · exact Int.add_lt_add_of_le_of_lt hhead (ih'.2 h)
      · have hl0 : l = 0 := by omega
        subst hl0
        simp only [Int.zero_mul, Int.zero_add]
        refine ⟨ih'.1, ?_⟩
        intro hs
        simp only [Int.lt_irrefl, decide_false, Bool.false_and, Bool.false_or] at hs
        exact ih'.2 hs

/-- **Farkas soundness, positively weighted subsystem.** If `checkFarkas S cert = true`, then
already the subsystem of premises with a positive multiplier has no scaled point `(d, p)` with
`d > 0`. -/
theorem checkFarkas_sound_scaled_posSupport (S : List Constraint) (cert : List Int)
    (h : checkFarkas S cert = true) (d : Int) (hd : 0 < d) (p : Nat → Int) :
    ¬ SatScaled (posSupport cert S) d p := by
  intro hS
  simp only [checkFarkas, Bool.and_eq_true] at h
  obtain ⟨⟨hnn, hlhs⟩, hrhs⟩ := h
  have hnn' : ∀ l ∈ cert, 0 ≤ l := by
    intro l hl
    simpa using List.all_eq_true.mp hnn l hl
  have h0 : SparseVec.eval (combineLhs S cert) p = 0 :=
    SparseVec.eval_eq_zero_of_isZero _ hlhs p
  obtain ⟨hle, hlt⟩ := combine_holdsScaled_of_posSupport S cert d p hnn' hS
  rw [h0] at hle hlt
  unfold rhsContradicts at hrhs
  split at hrhs
  · rename_i hs
    have hR : combineRhs S cert ≤ 0 := by simpa using hrhs
    have := hlt hs
    have : combineRhs S cert * d ≤ 0 * d := Int.mul_le_mul_of_nonneg_right hR (Int.le_of_lt hd)
    omega
  · have hR : combineRhs S cert < 0 := by simpa using hrhs
    have : combineRhs S cert * d < 0 * d := Int.mul_lt_mul_of_pos_right hR hd
    omega

/-- Integer form of `checkFarkas_sound_scaled_posSupport` (`d = 1`). -/
theorem checkFarkas_sound_int_posSupport (S : List Constraint) (cert : List Int)
    (h : checkFarkas S cert = true) (x : Nat → Int) : ¬ SatInt (posSupport cert S) x := by
  rw [satInt_iff_satScaled_one]
  exact checkFarkas_sound_scaled_posSupport S cert h 1 (by decide) x

/-! ## Non-vacuity and tightness of the checker-level statements -/

/-- Non-vacuity of `checkFarkas_sound_scaled` (both hypotheses): the checker accepts `(1, 1)` for
`sysLeGe`, and `(1, 1)` for the strictness-dependent `sysStrict`, and `d = 1 > 0`. -/
theorem nv_checkFarkas_sound_scaled :
    checkFarkas sysLeGe [1, 1] = true ∧ checkFarkas sysStrict [1, 1] = true ∧ (0 : Int) < 1 := by
  decide

/-- Non-vacuity of the checker-level soundness statements without a denominator
(`checkFarkas_sound_int`, `checkFarkas_sound_int_posSupport`). -/
theorem nv_checkFarkas_sound :
    checkFarkas sysLeGe [1, 1] = true ∧ checkFarkas sysStrict [1, 1] = true := by decide

/-- Non-vacuity of the positive-support form with a premise the certificate does not use: the
third premise `x₁ ≤ -7` gets multiplier `0`, so it is not in the support, and the support is
`sysLeGe`. -/
theorem nv_checkFarkas_sound_posSupport :
    checkFarkas (sysLeGe ++ [⟨[(1, 1)], .le, -7⟩]) [1, 1, 0] = true ∧
    posSupport [1, 1, 0] (sysLeGe ++ [⟨[(1, 1)], .le, -7⟩]) = sysLeGe ∧ (0 : Int) < 1 := by
  decide

/-- **Tightness of `h : checkFarkas S cert = true`** (canonical form for
`checkFarkas_sound_scaled`, `checkFarkas_sound_int`, and the positive-support forms): the
certificate `(1, 1)` is rejected for the satisfiable `sysEq` (`x₀ = 1`); `d = 1 > 0` holds and the
conclusion fails, both at the scaled point `(1, pt1 1)` and at the integer point `pt1 1`, and for
the positively weighted subsystem (which is all of `sysEq`). -/
theorem ce_checkFarkas_rejected_satisfiable :
    checkFarkas sysEq [1, 1] = false ∧ (0 : Int) < 1 ∧
    SatScaled sysEq 1 (pt1 1) ∧ SatInt sysEq (pt1 1) ∧
    posSupport [1, 1] sysEq = sysEq := by decide

/-- Non-vacuity of the structured form: all three conditions hold for `sysLeGe` with `(1, 1)`,
and `d = 1 > 0`. -/
theorem nv_farkas_sound_structured :
    multipliersNonneg [1, 1] = true ∧ lhsVanishes sysLeGe [1, 1] = true ∧
      rhsContradicts sysLeGe [1, 1] = true ∧ (0 : Int) < 1 := by decide

/-- Non-vacuity of the sparse=dense coefficient statement with duplicates present. -/
theorem nv_combineLhs_coeff :
    SparseVec.coeff (combineLhs sysLeGe [2, 3]) 0 = 2 * 1 + 3 * (-1) := by decide

/-- Non-vacuity of the sparse=dense value statement with duplicates present. -/
theorem nv_combineLhs_eval :
    SparseVec.eval (combineLhs sysLeGe [2, 3]) (pt1 5) =
      2 * SparseVec.eval [(0, 1)] (pt1 5) + 3 * SparseVec.eval [(0, -1)] (pt1 5) := by decide

end Toy.Farkas
