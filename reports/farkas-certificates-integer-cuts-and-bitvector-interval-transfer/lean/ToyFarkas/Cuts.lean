import ToyFarkas.Completeness
import ToyFarkas.Counterexamples

/-!
# Chvátal–Gomory cuts and cut-plus-Farkas certificates

A Chvátal–Gomory (CG) step on a system `S` is given by integer multipliers `λ` and a divisor
`g`. Over the integers each strict premise `a · x < b` is first read as `a · x ≤ b - 1`
(`Constraint.tighten`). The step forms the combination `(Σ λₖ aₖ) · x ≤ Σ λₖ bₖ` and, when every
dense coefficient of the combined left-hand side is divisible by `g`, emits the cut

  `(Σ λₖ aₖ / g) · x ≤ ⌊(Σ λₖ bₖ) / g⌋`.

With rational multipliers `λ/g` this is the classical CG rounding: a non-negative combination
with integral coefficients, right-hand side rounded down. Lean's `Int` division `/` rounds
toward `-∞` for positive divisors, so `/ g` is the floor.

The cut's left-hand side is written in dense normal form over the indices `0, …, bound - 1`
of the combined form (`SparseVec.bound`); this keeps the definition simple and is not meant
to be efficient.

A cut-plus-Farkas certificate is a list of CG steps, each applied to the original system
extended by all previously derived cuts, followed by Farkas multipliers for the final system.
-/

namespace Toy.Farkas

/-- Integer-tightening keeps the left-hand side. -/
theorem Constraint.tighten_lhs (c : Constraint) : c.tighten.lhs = c.lhs := by
  obtain ⟨lhs, rel, rhs⟩ := c
  cases rel <;> rfl

/-- One Chvátal–Gomory step: a list of multipliers and a divisor. Multiplier `k` is paired with
constraint `k` of the current system by `List.zipWith` (as in `combineLhs`/`combineRhs`), so a short
list gives the remaining constraints multiplier `0` and surplus multipliers are ignored by the
combination (they are still checked to be non-negative by `cgValid`). -/
structure CGStep where
  mult : List Int
  div : Int
  deriving DecidableEq, Repr

/-- Combined left-hand side of a CG step. -/
def cgLhs (S : List Constraint) (k : CGStep) : SparseVec := combineLhs S k.mult

/-- Combined right-hand side of a CG step, after integer tightening of strict premises. -/
def cgRhs (S : List Constraint) (k : CGStep) : Int := combineRhs (S.map Constraint.tighten) k.mult

/-- Every dense coefficient of the combined left-hand side is divisible by the divisor. -/
def cgDivisible (S : List Constraint) (k : CGStep) : Bool :=
  (List.range (cgLhs S k).bound).all (fun i => SparseVec.coeff (cgLhs S k) i % k.div == 0)

/-- The cut produced by a CG step (no validity checks): left-hand side divided by `g`,
right-hand side divided by `g` and rounded down. -/
def cgCut (S : List Constraint) (k : CGStep) : Constraint :=
  ⟨(List.range (cgLhs S k).bound).map (fun i => (i, SparseVec.coeff (cgLhs S k) i / k.div)),
   .le, cgRhs S k / k.div⟩

/-- Validity of a CG step: non-negative multipliers, positive divisor, divisibility. -/
def cgValid (S : List Constraint) (k : CGStep) : Bool :=
  multipliersNonneg k.mult && decide (0 < k.div) && cgDivisible S k

/-- The checked CG step: the cut if the step is valid. -/
def cgDerive (S : List Constraint) (k : CGStep) : Option Constraint :=
  if cgValid S k then some (cgCut S k) else none

/-- Apply CG steps in order; step `j` sees the original system and the cuts of steps `< j`. -/
def applyCuts : List Constraint → List CGStep → Option (List Constraint)
  | S, [] => some S
  | S, k :: ks =>
    match cgDerive S k with
    | some c => applyCuts (S ++ [c]) ks
    | none => none

/-- A cut-plus-Farkas certificate. -/
structure CutCert where
  cuts : List CGStep
  farkas : List Int
  deriving DecidableEq, Repr

/-- **The cut-plus-Farkas checker** (a decidable Boolean function): all CG steps are valid and
the Farkas certificate is accepted for the extended system. -/
def checkCutCert (S : List Constraint) (cc : CutCert) : Bool :=
  match applyCuts S cc.cuts with
  | some S' => checkFarkas S' cc.farkas
  | none => false

/-! ## Definition examples -/

/-- `{2x₀ ≤ 3}`. -/
def sysTwoXLeThree : List Constraint := [⟨[(0, 2)], .le, 3⟩]

/-- Positive example: `cgLhs` is the (unnormalized) combined left-hand side. -/
theorem ex_cgLhs_pos :
    cgLhs [⟨[(0, 1), (1, 1)], .le, 1⟩, ⟨[(0, 1), (1, -1)], .le, 0⟩] ⟨[1, 1], 2⟩ =
      [(0, 1), (1, 1), (0, 1), (1, -1)] := by decide
/-- Negative example: `cgLhs` is not divided by the divisor and not normalized. -/
theorem ex_cgLhs_neg :
    cgLhs [⟨[(0, 1), (1, 1)], .le, 1⟩, ⟨[(0, 1), (1, -1)], .le, 0⟩] ⟨[1, 1], 2⟩ ≠ [(0, 1)] := by
  decide

theorem ex_cgCut_pos : cgCut sysTwoXLeThree ⟨[1], 2⟩ = ⟨[(0, 1)], .le, 1⟩ := by decide
/-- Negative example: the right-hand side is rounded down (`⌊3/2⌋ = 1`), not up. -/
theorem ex_cgCut_neg : cgCut sysTwoXLeThree ⟨[1], 2⟩ ≠ ⟨[(0, 1)], .le, 2⟩ := by decide
/-- Negative example: rounding is toward `-∞`, so `⌊-1/2⌋ = -1` (not `0`). -/
theorem ex_cgCut_floor_negative : cgCut sysHalf ⟨[0, 1], 2⟩ = ⟨[(0, -1)], .le, -1⟩ := by decide

/-- Positive example: strict premises are tightened before combining (`2x₀ < 3` gives `x₀ ≤ 1`). -/
theorem ex_cgRhs_strict_pos : cgRhs [⟨[(0, 2)], .lt, 3⟩] ⟨[1], 2⟩ = 2 := by decide
theorem ex_cgRhs_neg : cgRhs [⟨[(0, 2)], .lt, 3⟩] ⟨[1], 2⟩ ≠ 3 := by decide

theorem ex_cgDivisible_pos : cgDivisible sysTwoXLeThree ⟨[1], 2⟩ = true := by decide
theorem ex_cgDivisible_neg : cgDivisible sysTwoXLeThree ⟨[1], 3⟩ = false := by decide

/-- Positive example: divisibility is checked on dense coefficients, so a coefficient split
across duplicate entries (`x₀` from two premises) is handled. -/
theorem ex_cgDivisible_duplicates_pos :
    cgDivisible [⟨[(0, 1), (1, 1)], .le, 1⟩, ⟨[(0, 1), (1, -1)], .le, 0⟩] ⟨[1, 1], 2⟩ = true := by
  decide

theorem ex_cgValid_pos : cgValid sysTwoXLeThree ⟨[1], 2⟩ = true := by decide
theorem ex_cgValid_neg : cgValid sysTwoXLeThree ⟨[1], 0⟩ = false := by decide

theorem ex_cgDerive_pos : cgDerive sysTwoXLeThree ⟨[1], 2⟩ = some ⟨[(0, 1)], .le, 1⟩ := by decide
theorem ex_cgDerive_neg : cgDerive sysTwoXLeThree ⟨[-1], 2⟩ = none := by decide

/-- The certificate deriving `x₀ ≤ 0` and `-x₀ ≤ -1` from `{2x₀ ≤ 1, -2x₀ ≤ -1}` and combining. -/
def halfCutCert : CutCert := ⟨[⟨[1, 0], 2⟩, ⟨[0, 1], 2⟩], [0, 0, 1, 1]⟩

theorem ex_applyCuts_pos :
    applyCuts sysHalf halfCutCert.cuts =
      some (sysHalf ++ [⟨[(0, 1)], .le, 0⟩, ⟨[(0, -1)], .le, -1⟩]) := by decide
theorem ex_applyCuts_neg : applyCuts sysHalf [⟨[1, 0], 3⟩] = none := by decide

theorem ex_checkCutCert_pos : checkCutCert sysHalf halfCutCert = true := by decide
theorem ex_checkCutCert_neg : checkCutCert sysHalf ⟨[], [1, 1]⟩ = false := by decide

/-! ## Soundness over the integers -/

theorem denseDotOn_mul_right (ks : List Nat) (a x : Nat → Int) (g : Int) :
    denseDotOn ks a x * g = denseDotOn ks (fun i => a i * g) x := by
  induction ks with
  | nil => simp [denseDotOn]
  | cons k ks ih =>
    rw [denseDotOn_cons, denseDotOn_cons, Int.add_mul, ih, Int.mul_right_comm]

theorem eval_range_map (n : Nat) (f : Nat → Int) (x : Nat → Int) :
    SparseVec.eval ((List.range n).map (fun i => (i, f i))) x = denseDotOn (List.range n) f x := by
  simp [SparseVec.eval, denseDotOn, List.map_map, Function.comp_def]

theorem combineLhs_map_tighten (S : List Constraint) (cert : List Int) :
    combineLhs (S.map Constraint.tighten) cert = combineLhs S cert := by
  induction cert generalizing S with
  | nil => simp [combineLhs]
  | cons l cert ih =>
    cases S with
    | nil => simp [combineLhs]
    | cons c S =>
      have := ih S
      simp only [combineLhs, List.map_cons, List.zipWith_cons_cons, List.flatten_cons] at this ⊢
      rw [this, Constraint.tighten_lhs]

/-- The combination of tightened premises: `(Σ λₖ aₖ) · x ≤ Σ λₖ bₖ'` at every integer solution. -/
theorem cgLhs_eval_le_cgRhs (S : List Constraint) (k : CGStep)
    (hnn : multipliersNonneg k.mult = true) (x : Nat → Int) (hx : SatInt S x) :
    SparseVec.eval (cgLhs S k) x ≤ cgRhs S k := by
  have hnn' : ∀ l ∈ k.mult, 0 ≤ l := by
    intro l hl; simpa using List.all_eq_true.mp hnn l hl
  have hT : SatScaled (S.map Constraint.tighten) 1 x := by
    intro c hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    exact (Constraint.holdsInt_iff_holdsScaled_one _ x).mp
      ((Constraint.holdsInt_tighten_iff c' x).mpr (hx c' hc'))
  have h := (combine_holdsScaled (S.map Constraint.tighten) k.mult 1 x hnn' hT).1
  rw [combineLhs_map_tighten, Int.mul_one] at h
  exact h

/-- **CG cut soundness over the integers (structured form).** If the multipliers are
non-negative, the divisor is positive, and it divides every dense coefficient of the combined
left-hand side, then every integer solution of `S` satisfies the cut. -/
theorem cgCut_sound_int_of_nonneg_of_div_pos_of_divisible (S : List Constraint) (k : CGStep)
    (hnn : multipliersNonneg k.mult = true) (hg : 0 < k.div) (hdiv : cgDivisible S k = true)
    (x : Nat → Int) (hx : SatInt S x) : (cgCut S k).HoldsInt x := by
  have hcomb := cgLhs_eval_le_cgRhs S k hnn x hx
  have hev : SparseVec.eval (cgCut S k).lhs x * k.div = SparseVec.eval (cgLhs S k) x := by
    simp only [cgCut]
    rw [eval_range_map, denseDotOn_mul_right,
      SparseVec.eval_eq_denseDot_coeff_of_keys_lt (cgLhs S k) _ (SparseVec.lt_bound _) x, denseDot]
    apply denseDotOn_congr
    intro i hi
    have hmod := List.all_eq_true.mp hdiv i hi
    have hmod' : SparseVec.coeff (cgLhs S k) i % k.div = 0 := by simpa using hmod
    exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hmod')
  show Rel.Sat .le _ _
  simp only [Rel.Sat]
  exact (Int.le_ediv_iff_mul_le hg).mpr (hev ▸ hcomb)

/-- **CG cut soundness over the integers.** A cut returned by the checked step `cgDerive` is
satisfied by every integer solution of `S`. -/
theorem cgDerive_sound_int (S : List Constraint) (k : CGStep) (c : Constraint)
    (h : cgDerive S k = some c) (x : Nat → Int) (hx : SatInt S x) : c.HoldsInt x := by
  unfold cgDerive at h
  split at h
  · rename_i hv
    cases h
    simp only [cgValid, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact cgCut_sound_int_of_nonneg_of_div_pos_of_divisible S k hv.1.1 hv.1.2 hv.2 x hx
  · cases h

theorem applyCuts_satInt (ks : List CGStep) (S S' : List Constraint)
    (h : applyCuts S ks = some S') (x : Nat → Int) (hx : SatInt S x) : SatInt S' x := by
  induction ks generalizing S with
  | nil => simp [applyCuts] at h; subst h; exact hx
  | cons k ks ih =>
    simp only [applyCuts] at h
    split at h
    · rename_i c hc
      apply ih (S ++ [c]) h
      intro c' hc'
      rcases List.mem_append.mp hc' with h1 | h1
      · exact hx c' h1
      · simp at h1; subst h1; exact cgDerive_sound_int S k _ hc x hx
    · cases h

/-- **Cut-plus-Farkas soundness over the integers.** If `checkCutCert S cc = true`, then `S`
has no integer solution. -/
theorem checkCutCert_sound_int (S : List Constraint) (cc : CutCert)
    (h : checkCutCert S cc = true) (x : Nat → Int) : ¬ SatInt S x := by
  intro hx
  unfold checkCutCert at h
  split at h
  · rename_i S' hS'
    exact checkFarkas_sound_int S' cc.farkas h x (applyCuts_satInt cc.cuts S S' hS' x hx)
  · cases h

/-! ## Non-vacuity -/

/-- Non-vacuity of the CG soundness theorems: the step `(λ, g) = ((1), 2)` on `{2x₀ ≤ 3}` is
valid, `x₀ = 1` is an integer solution, `cgDerive` returns the cut `x₀ ≤ 1`, and the cut holds
at `x₀ = 1`. -/
theorem nv_cgCut_sound_int :
    multipliersNonneg [1] = true ∧ (0 : Int) < 2 ∧ cgDivisible sysTwoXLeThree ⟨[1], 2⟩ = true ∧
    SatInt sysTwoXLeThree (pt1 1) ∧ cgDerive sysTwoXLeThree ⟨[1], 2⟩ = some ⟨[(0, 1)], .le, 1⟩ ∧
    (cgCut sysTwoXLeThree ⟨[1], 2⟩).HoldsInt (pt1 1) := by
  decide

/-- Non-vacuity of cut-plus-Farkas soundness, on a system that plain Farkas certificates cannot
refute (`ce_farkas_incomplete_int`). -/
theorem nv_checkCutCert_sound_int : checkCutCert sysHalf halfCutCert = true := by decide

/-! ## Necessity of the side conditions -/

/-- **Integrality of the variables is necessary.** The valid step `((1, 0), 2)` on
`{2x₀ ≤ 1, -2x₀ ≤ -1}` yields the cut `x₀ ≤ 0`; the rational point `x₀ = 1/2`
(`(d, p) = (2, 1)`, `d > 0`) satisfies the premises but violates the cut. -/
theorem ce_cgCut_unsound_over_rat :
    multipliersNonneg [1, 0] = true ∧ (0 : Int) < 2 ∧ cgDivisible sysHalf ⟨[1, 0], 2⟩ = true ∧
    (0 : Int) < 2 ∧ SatScaled sysHalf 2 (pt1 1) ∧
    ¬ (cgCut sysHalf ⟨[1, 0], 2⟩).HoldsScaled 2 (pt1 1) := by decide

/-- **Cut-plus-Farkas certificates are not sound over the rationals.** The certificate
`halfCutCert` is accepted for `{2x₀ ≤ 1, -2x₀ ≤ -1}`, which the rational point `x₀ = 1/2`
satisfies. -/
theorem ce_checkCutCert_unsound_over_rat :
    checkCutCert sysHalf halfCutCert = true ∧ (0 : Int) < 2 ∧ SatScaled sysHalf 2 (pt1 1) := by
  decide

/-- **Non-negative multipliers are necessary.** The step `((-1), 1)` on `{x₀ ≤ 0}` has a positive
divisor that divides everything, but yields `-x₀ ≤ 0`, violated by the solution `x₀ = -1`. -/
theorem ce_cgCut_negative_multiplier :
    multipliersNonneg [-1] = false ∧ (0 : Int) < 1 ∧
    cgDivisible [⟨[(0, 1)], .le, 0⟩] ⟨[-1], 1⟩ = true ∧
    SatInt [⟨[(0, 1)], .le, 0⟩] (pt1 (-1)) ∧
    ¬ (cgCut [⟨[(0, 1)], .le, 0⟩] ⟨[-1], 1⟩).HoldsInt (pt1 (-1)) := by decide

/-- **A positive divisor is necessary.** The step `((1), -1)` on `{x₀ ≤ 0}` passes the other
checks but yields `-x₀ ≤ 0`, violated by the solution `x₀ = -1`. -/
theorem ce_cgCut_negative_divisor :
    multipliersNonneg [1] = true ∧ ¬ ((0 : Int) < -1) ∧
    cgDivisible [⟨[(0, 1)], .le, 0⟩] ⟨[1], -1⟩ = true ∧
    SatInt [⟨[(0, 1)], .le, 0⟩] (pt1 (-1)) ∧
    ¬ (cgCut [⟨[(0, 1)], .le, 0⟩] ⟨[1], -1⟩).HoldsInt (pt1 (-1)) := by decide

/-- **Divisibility (integral combined coefficients) is necessary.** The step `((1), 2)` on
`{x₀ - x₁ ≤ 0}` has non-negative multipliers and a positive divisor, but `2` does not divide
the coefficients; flooring them anyway gives `-x₁ ≤ 0`, violated by the solution
`(x₀, x₁) = (-1, -1)`. -/
theorem ce_cgCut_not_divisible :
    multipliersNonneg [1] = true ∧ (0 : Int) < 2 ∧
    cgDivisible [⟨[(0, 1), (1, -1)], .le, 0⟩] ⟨[1], 2⟩ = false ∧
    SatInt [⟨[(0, 1), (1, -1)], .le, 0⟩] (pt2 (-1) (-1)) ∧
    ¬ (cgCut [⟨[(0, 1), (1, -1)], .le, 0⟩] ⟨[1], 2⟩).HoldsInt (pt2 (-1) (-1)) := by decide

/-- **The point must satisfy the premises.** At `x₀ = 5`, which violates `2x₀ ≤ 3`, the valid
step `((1), 2)` yields the cut `x₀ ≤ 1`, which also fails. -/
theorem ce_cgCut_point_not_solution :
    multipliersNonneg [1] = true ∧ (0 : Int) < 2 ∧ cgDivisible sysTwoXLeThree ⟨[1], 2⟩ = true ∧
    ¬ SatInt sysTwoXLeThree (pt1 5) ∧ ¬ (cgCut sysTwoXLeThree ⟨[1], 2⟩).HoldsInt (pt1 5) := by decide

/-- **The acceptance hypothesis of `cgDerive_sound_int` is necessary** (canonical form): for the
step `((-1), 1)` on `{x₀ ≤ 0}`, `cgDerive` returns `none`; the unchecked cut `-x₀ ≤ 0` is violated by
the solution `x₀ = -1`. -/
theorem ce_cgDerive_rejected :
    cgDerive [⟨[(0, 1)], .le, 0⟩] ⟨[-1], 1⟩ = none ∧
    SatInt [⟨[(0, 1)], .le, 0⟩] (pt1 (-1)) ∧
    ¬ (cgCut [⟨[(0, 1)], .le, 0⟩] ⟨[-1], 1⟩).HoldsInt (pt1 (-1)) := by decide

/-- **Integrality is needed even without rounding.** The valid step `((1, 1), 1)` (divisor `1`, so
nothing is rounded) on `{x₀ < 1, -x₀ < 0}` tightens both strict premises (`x₀ ≤ 0`, `-x₀ ≤ -1`) and
derives `0 ≤ -1`; the rational point `x₀ = 1/2` (`(d, p) = (2, 1)`) satisfies the premises and
violates the cut. -/
theorem ce_cgCut_div_one_unsound_over_rat :
    cgValid sysOpenUnit ⟨[1, 1], 1⟩ = true ∧
    cgCut sysOpenUnit ⟨[1, 1], 1⟩ = ⟨[(0, 0)], .le, -1⟩ ∧
    (0 : Int) < 2 ∧ SatScaled sysOpenUnit 2 (pt1 1) ∧
    ¬ (cgCut sysOpenUnit ⟨[1, 1], 1⟩).HoldsScaled 2 (pt1 1) := by decide

/-- With no cut steps, `checkCutCert` is plain `checkFarkas` and does not tighten strict premises:
`(1, 1)` is rejected for `{x₀ < 1, -x₀ < 0}`, while one cut step with divisor `1` followed by a
Farkas certificate is accepted. -/
theorem ex_checkCutCert_no_cuts_no_tightening :
    checkCutCert sysOpenUnit ⟨[], [1, 1]⟩ = false ∧
    checkCutCert sysOpenUnit ⟨[⟨[1, 1], 1⟩], [0, 0, 1]⟩ = true := by decide

/-- **Integer tightening does not make Farkas certificates complete over `Int`.** `sysHalf` has
no strict premise, so tightening leaves it unchanged and the tightened checker rejects every
certificate, although `sysHalf` has no integer solution. -/
theorem ce_checkFarkasTightened_incomplete_int :
    sysHalf.map Constraint.tighten = sysHalf ∧
    (∀ x : Nat → Int, ¬ SatInt sysHalf x) ∧
    (∀ cert : List Int, checkFarkasTightened sysHalf cert = false) := by
  have hT : sysHalf.map Constraint.tighten = sysHalf := by decide
  refine ⟨hT, ce_farkas_incomplete_int.1, fun cert => ?_⟩
  unfold checkFarkasTightened
  rw [hT]
  exact ce_farkas_incomplete_int.2 cert

/-- The acceptance hypothesis of `checkCutCert_sound_int` cannot be dropped: a rejected
certificate for the satisfiable `{2x₀ ≤ 3}` (solution `x₀ = 1`). -/
theorem ce_checkCutCert_rejects_satisfiable :
    checkCutCert sysTwoXLeThree ⟨[⟨[1], 2⟩], [1]⟩ = false ∧ SatInt sysTwoXLeThree (pt1 1) := by
  decide

end Toy.Farkas
