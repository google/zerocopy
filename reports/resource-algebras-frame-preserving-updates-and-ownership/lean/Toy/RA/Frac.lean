import Toy.RA.Core
import Toy.RA.PosRat
import Toy.RA.Agree

/-!
# Fractional Permission and Fractional-Value Resource Algebras (`Frac`, `FracVal`)

Models Boyland-style fractional permissions (`fracRA`, Iris's `fracR` over
`ℚ_{>0}` with validity `q ≤ 1`) and fractional-value ownership
(`fracValRA α := prodRA fracRA (agreeRA α)`, matching `FRAC(α)` in Iris 2015
and the `DfracOwn` fragment of Iris's `dfrac_agreeR` via `to_frac_agree`),
where:
- a full fraction (`q = 1`) is exclusive and can update the carried value
  arbitrarily (to any fraction `q' ≤ 1` and singleton `ag y`),
- a partial fraction (`q < 1`) cannot change the carried value or increase its
  share, because a frame holding the complementary share `1 - q` at the
  original value observes any change.
-/

namespace Toy.RA

/-- Pure fractional permission resource algebra over `PosRat` (`ℚ_{>0}`):
composition is addition, and a fraction is valid iff `q ≤ 1`. Captures Iris's
`fracR`. -/
def fracRA : RawRA PosRat where
  op := PosRat.add
  valid q := PosRat.le q PosRat.one

theorem fracRA_opAssoc : OpAssoc fracRA := PosRat.add_assoc

theorem fracRA_opComm : OpComm fracRA := PosRat.add_comm

theorem fracRA_validOpL : ValidOpL fracRA :=
  fun _ _ h => PosRat.le_of_add_le h

theorem fracRA_isCoreFreeRA : IsCoreFreeRA fracRA :=
  ⟨fracRA_opAssoc, fracRA_opComm, fracRA_validOpL⟩

/-- Full permission `1` is exclusive in `fracRA`: adding any positive rational
exceeds `1`. Captures Iris's `frac_full_exclusive`. -/
theorem frac_full_isExclusive : IsExclusive fracRA PosRat.one :=
  fun f hf => PosRat.not_add_le_self PosRat.one f hf

/-! ## Positive and Negative Examples for `fracRA` -/

theorem fracRA_valid_pos_example :
    fracRA.valid PosRat.one ∧ fracRA.valid PosRat.half :=
  ⟨PosRat.le_refl PosRat.one, PosRat.le_of_lt PosRat.half_lt_one⟩

theorem fracRA_valid_neg_example :
    ¬ fracRA.valid PosRat.two ∧
    ¬ fracRA.valid (fracRA.op PosRat.one PosRat.half) :=
  ⟨PosRat.not_two_le_one, frac_full_isExclusive PosRat.half⟩

/-! ## Fractional-Value Ownership (`fracValRA`) -/

/-- Fractional-value resource algebra: a pair of a fractional permission and an
agreement value (`prodRA fracRA (agreeRA α)`). Captures `FRAC(α)` and the
`DfracOwn` fragment of Iris's `dfrac_agreeR` (`to_frac_agree`) used for
shared-read / exclusive-write points-to ownership. -/
def fracValRA (α : Type) : RawRA (PosRat × Agree α) :=
  prodRA fracRA (agreeRA α)

/-- Construct a fractional-value resource owning share `q` of value `x`.
Captures Iris's `to_frac_agree q x`. -/
def fracVal {α : Type} (q : PosRat) (x : α) : PosRat × Agree α :=
  (q, Agree.ag x)

/-- The exact complementary share `(1 - q, ag x)` for a partial fraction
`q < 1`, witnessing that another holder of the remaining share observes any
value change or share inflation. -/
def fracValComplement {α : Type} (q : PosRat) (hq : PosRat.lt q PosRat.one) (x : α) :
    PosRat × Agree α :=
  fracVal (PosRat.sub PosRat.one q hq) x

theorem fracValRA_opAssoc (α : Type) : OpAssoc (fracValRA α) :=
  prodRA_opAssoc fracRA (agreeRA α) fracRA_opAssoc (agreeRA_opAssoc α)

theorem fracValRA_opComm (α : Type) : OpComm (fracValRA α) :=
  prodRA_opComm fracRA (agreeRA α) fracRA_opComm (agreeRA_opComm α)

theorem fracValRA_validOpL (α : Type) : ValidOpL (fracValRA α) :=
  prodRA_validOpL fracRA (agreeRA α) fracRA_validOpL (agreeRA_validOpL α)

theorem fracValRA_isCoreFreeRA (α : Type) : IsCoreFreeRA (fracValRA α) :=
  prodRA_isCoreFreeRA fracRA (agreeRA α) fracRA_isCoreFreeRA (agreeRA_isCoreFreeRA α)

theorem fracVal_valid_iff {α : Type} (q : PosRat) (x : α) :
    (fracValRA α).valid (fracVal q x) ↔ PosRat.le q PosRat.one :=
  ⟨fun h => h.1, fun h => ⟨h, agree_ag_valid x⟩⟩

/-- Splitting / recombining shares of the same value. Captures Iris's
`frac_agree_op`. -/
theorem fracVal_split {α : Type} (q₁ q₂ : PosRat) (x : α) :
    (fracValRA α).op (fracVal q₁ x) (fracVal q₂ x) = fracVal (PosRat.add q₁ q₂) x := by
  exact Prod.ext rfl (agree_ag_idemp x)

/-- Full fractional ownership `(1, ag x)` is exclusive in `fracValRA α`.
Captures Iris's `to_dfrac_agree_exclusive`. -/
theorem fracVal_full_isExclusive {α : Type} (x : α) :
    IsExclusive (fracValRA α) (fracVal PosRat.one x) :=
  fun f hf => frac_full_isExclusive f.1 hf.1

/-! ## Positive and Negative Examples for `fracValRA` -/

theorem fracValRA_valid_pos_example :
    (fracValRA Bool).valid
      ((fracValRA Bool).op (fracVal PosRat.half false) (fracVal PosRat.half false)) := by
  rw [fracVal_split, PosRat.half_add_half]
  exact ⟨PosRat.le_refl PosRat.one, agree_ag_valid false⟩

theorem fracValRA_valid_neg_example :
    ¬ (fracValRA Bool).valid
      ((fracValRA Bool).op (fracVal PosRat.half false) (fracVal PosRat.half true)) ∧
    ¬ (fracValRA Bool).valid
      ((fracValRA Bool).op (fracVal PosRat.one false) (fracVal PosRat.half false)) := by
  refine ⟨?_, ?_⟩
  · intro ⟨_, hagree⟩
    have heq := (agree_ag_op_valid_iff false true).mp hagree
    cases heq
  · intro ⟨hfrac, _⟩
    exact frac_full_isExclusive PosRat.half hfrac

/-! ## Main Results for Fractional Ownership -/

/-- Full-fraction update characterization over all carrier targets `(q', s)`:
`(1, ag x)` updates frame-preservingly to `(q', s)` iff `q' ≤ 1` and `s` is a
valid singleton `Agree.ag y` for some `y : α`. -/
theorem fracVal_full_fpUpdate_iff {α : Type} (x : α) (q' : PosRat) (s : Agree α) :
    fpUpdate (fracValRA α) (fracVal PosRat.one x) (q', s) ↔
      PosRat.le q' PosRat.one ∧ ∃ y : α, s = .ag y := by
  constructor
  · intro hupd
    have hv : (fracValRA α).valid (fracVal PosRat.one x) :=
      ⟨PosRat.le_refl PosRat.one, agree_ag_valid x⟩
    have hv' := hupd none hv
    exact ⟨hv'.1, agree_valid_eq_ag hv'.2⟩
  · rintro ⟨hq', y, rfl⟩
    exact exclusive_fpUpdate (fracValRA α) (fracVal PosRat.one x) (q', .ag y)
      (fracVal_full_isExclusive x) ⟨hq', agree_ag_valid y⟩

/-- Singleton specialization: `(1, ag x)` updates frame-preservingly to
`(q', ag y)` for arbitrary `y` if and only if `q' ≤ 1`. -/
theorem fracVal_full_ag_fpUpdate_iff {α : Type} (x y : α) (q' : PosRat) :
    fpUpdate (fracValRA α) (fracVal PosRat.one x) (fracVal q' y) ↔
      PosRat.le q' PosRat.one := by
  rw [fracVal_full_fpUpdate_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, y, rfl⟩⟩

/-- Corollary: a full fraction `(1, ag x)` can update its carried value
arbitrarily to `(1, ag y)`. -/
theorem fracVal_full_fpUpdate {α : Type} (x y : α) :
    fpUpdate (fracValRA α) (fracVal PosRat.one x) (fracVal PosRat.one y) :=
  (fracVal_full_ag_fpUpdate_iff x y PosRat.one).mpr (PosRat.le_refl PosRat.one)

/-- Corollary: two complementary shares whose sum is `1` recombine to allow an
arbitrary value update. Captures Iris's `frac_agree_update_2`. -/
theorem fracVal_recombine_fpUpdate {α : Type} {q₁ q₂ : PosRat}
    (hq : PosRat.add q₁ q₂ = PosRat.one) (x y : α) :
    fpUpdate (fracValRA α)
      ((fracValRA α).op (fracVal q₁ x) (fracVal q₂ x))
      ((fracValRA α).op (fracVal q₁ y) (fracVal q₂ y)) := by
  rw [fracVal_split, fracVal_split, hq]
  exact fracVal_full_fpUpdate x y

theorem fracVal_full_fpUpdate_iff_nonvacuity :
    IsCoreFreeRA (fracValRA Bool) ∧ (fracValRA Bool).valid (fracVal PosRat.one false) ∧
    (fracValRA Bool).valid (fracVal PosRat.one true) :=
  ⟨fracValRA_isCoreFreeRA Bool,
   ⟨PosRat.le_refl PosRat.one, agree_ag_valid false⟩,
   ⟨PosRat.le_refl PosRat.one, agree_ag_valid true⟩⟩

/-- Exposed witness frame for partial-fraction immutability: when `q < 1` and
`x ≠ y`, the complementary frame `fracValComplement q hq x = (1 - q, ag x)`
composes validly with `(q, ag x)` and invalidly with `(q', ag y)`. -/
theorem fracVal_partial_complement_observes_change {α : Type}
    {q q' : PosRat} (hq : PosRat.lt q PosRat.one) {x y : α} (hxy : x ≠ y) :
    (fracValRA α).valid ((fracValRA α).op (fracVal q x) (fracValComplement q hq x)) ∧
    ¬ (fracValRA α).valid ((fracValRA α).op (fracVal q' y) (fracValComplement q hq x)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, (agree_ag_op_valid_iff x x).mpr rfl⟩
    change PosRat.le (PosRat.add q (PosRat.sub PosRat.one q hq)) PosRat.one
    rw [PosRat.add_sub_cancel]
    exact PosRat.le_refl PosRat.one
  · intro ⟨_, hagree⟩
    exact hxy ((agree_ag_op_valid_iff y x).mp hagree).symm

/-- Exact characterization of frame-preserving updates out of a partial fraction
`q < 1` over all carrier targets `(q', s)`: `(q, ag x) ⤳ (q', s)` holds iff
the share does not increase (`q' ≤ q`) and `s = ag x`. -/
theorem fracVal_partial_fpUpdate_iff {α : Type}
    {q q' : PosRat} (hq : PosRat.lt q PosRat.one) (x : α) (s : Agree α) :
    fpUpdate (fracValRA α) (fracVal q x) (q', s) ↔
      PosRat.le q' q ∧ s = .ag x := by
  constructor
  · intro hupd
    have hcompValid :
        (fracValRA α).valid (opOpt (fracValRA α) (fracVal q x) (some (fracValComplement q hq x))) := by
      refine ⟨?_, (agree_ag_op_valid_iff x x).mpr rfl⟩
      change PosRat.le (PosRat.add q (PosRat.sub PosRat.one q hq)) PosRat.one
      rw [PosRat.add_sub_cancel]
      exact PosRat.le_refl PosRat.one
    have hcompValid' := hupd (some (fracValComplement q hq x)) hcompValid
    have hfrac' : PosRat.le (PosRat.add q' (PosRat.sub PosRat.one q hq)) PosRat.one := hcompValid'.1
    have hle : PosRat.le q' q := by
      have h1 : PosRat.le (PosRat.add q' (PosRat.sub PosRat.one q hq))
                          (PosRat.add q (PosRat.sub PosRat.one q hq)) := by
        rw [PosRat.add_sub_cancel]
        exact hfrac'
      exact PosRat.le_of_add_le_add_right h1
    have hs : (agreeRA α).valid s := agreeRA_validOpL α s (.ag x) hcompValid'.2
    rcases agree_valid_eq_ag hs with ⟨y, rfl⟩
    have heq : x = y := ((agree_ag_op_valid_iff y x).mp hcompValid'.2).symm
    subst heq
    exact ⟨hle, rfl⟩
  · rintro ⟨hqle, rfl⟩ mf hmf
    cases mf with
    | none =>
      exact ⟨PosRat.le_trans hqle hmf.1, agree_ag_valid x⟩
    | some f =>
      exact ⟨PosRat.le_trans (PosRat.add_le_add_right f.1 hqle) hmf.1, hmf.2⟩

/-- Singleton specialization: when `q < 1`, `(q, ag x) ⤳ (q', ag y)` holds iff
`q' ≤ q ∧ x = y`. -/
theorem fracVal_partial_ag_fpUpdate_iff {α : Type}
    {q q' : PosRat} (hq : PosRat.lt q PosRat.one) (x y : α) :
    fpUpdate (fracValRA α) (fracVal q x) (fracVal q' y) ↔
      PosRat.le q' q ∧ x = y := by
  rw [fracVal_partial_fpUpdate_iff hq]
  constructor
  · intro ⟨hle, h⟩
    have hm := congrArg (fun s : Agree α => s.mem y) h
    exact ⟨hle, (Eq.mp hm rfl).symm⟩
  · rintro ⟨hle, rfl⟩
    exact ⟨hle, rfl⟩

theorem fracVal_partial_fpUpdate_iff_nonvacuity :
    IsCoreFreeRA (fracValRA Bool) ∧ PosRat.lt PosRat.half PosRat.one :=
  ⟨fracValRA_isCoreFreeRA Bool, PosRat.half_lt_one⟩

/-- Canonical tightness counterexample for `hq : PosRat.lt q PosRat.one` in
`fracVal_partial_fpUpdate_iff`: at the full fraction `q = 1`, changing `false`
to `true` IS frame-preserving even though `ag true ≠ ag false`. -/
theorem fracVal_partial_iff_full_counterexample :
    IsCoreFreeRA (fracValRA Bool) ∧
    ¬ PosRat.lt PosRat.one PosRat.one ∧
    ¬ (fpUpdate (fracValRA Bool) (fracVal PosRat.one false) (PosRat.one, .ag true) ↔
        PosRat.le PosRat.one PosRat.one ∧ (.ag true : Agree Bool) = .ag false) := by
  refine ⟨fracValRA_isCoreFreeRA Bool, PosRat.posRat_lt_neg_example, ?_⟩
  intro hiff
  have ⟨_, hft⟩ := hiff.mp (fracVal_full_fpUpdate false true)
  have hm := congrArg (fun a : Agree Bool => a.mem true) hft
  cases (Eq.mp hm rfl)

/-- Secondary counterexample showing over-full (invalid) fractions `q = 2` also
break `fracVal_partial_fpUpdate_iff` (vacuously updating to any value). -/
theorem fracVal_partial_iff_overfull_counterexample :
    IsCoreFreeRA (fracValRA Bool) ∧
    ¬ PosRat.lt PosRat.two PosRat.one ∧
    fpUpdate (fracValRA Bool) (fracVal PosRat.two false) (PosRat.two, .ag true) ∧
    ¬ (PosRat.le PosRat.two PosRat.two ∧ (.ag true : Agree Bool) = .ag false) := by
  refine ⟨fracValRA_isCoreFreeRA Bool, ?_, ?_, ?_⟩
  · intro hlt
    exact PosRat.not_two_le_one (PosRat.le_of_lt hlt)
  · intro mf hmf
    cases mf with
    | none => exact False.elim (PosRat.not_two_le_one hmf.1)
    | some f => exact False.elim (PosRat.not_two_le_one (PosRat.le_of_add_le hmf.1))
  · intro ⟨_, hft⟩
    have hm := congrArg (fun a : Agree Bool => a.mem true) hft
    cases (Eq.mp hm rfl)

/-- Impossibility of changing the value under a partial fraction: whenever
`q < 1` and `x ≠ y`, `(q, ag x) ⤳ (q', ag y)` fails for every `q' : PosRat`,
with an explicit witness frame given by `fracVal_partial_complement_observes_change`. -/
theorem fracVal_partial_value_change_impossible {α : Type}
    {q q' : PosRat} (hq : PosRat.lt q PosRat.one) {x y : α} (hxy : x ≠ y) :
    ¬ fpUpdate (fracValRA α) (fracVal q x) (fracVal q' y) := by
  intro hupd
  have ⟨hv, hnv⟩ := fracVal_partial_complement_observes_change (q' := q') hq hxy
  exact hnv (hupd (some (fracValComplement q hq x)) hv)

theorem fracVal_partial_value_change_impossible_nonvacuity :
    IsCoreFreeRA (fracValRA Bool) ∧ PosRat.lt PosRat.half PosRat.one ∧ (false ≠ true) :=
  ⟨fracValRA_isCoreFreeRA Bool, PosRat.half_lt_one, Bool.false_ne_true⟩

/-- Canonical tightness counterexample for `hq` and positive control for
`fracVal_partial_value_change_impossible`: upgrading from a partial share to
the full share `q = 1` permits changing `false` to `true`. -/
theorem fracVal_full_value_change_control :
    IsCoreFreeRA (fracValRA Bool) ∧
    ¬ PosRat.lt PosRat.one PosRat.one ∧
    (false ≠ true) ∧
    fpUpdate (fracValRA Bool) (fracVal PosRat.one false) (fracVal PosRat.one true) :=
  ⟨fracValRA_isCoreFreeRA Bool, PosRat.posRat_lt_neg_example, Bool.false_ne_true,
   fracVal_full_fpUpdate false true⟩

/-- Canonical tightness counterexample for `hxy : x ≠ y` in
`fracVal_partial_value_change_impossible`: keeping the value unchanged under a
partial share `q = 1/2` is frame-preserving. -/
theorem fracVal_partial_same_value_counterexample :
    IsCoreFreeRA (fracValRA Bool) ∧
    PosRat.lt PosRat.half PosRat.one ∧
    ¬ (false ≠ false) ∧
    fpUpdate (fracValRA Bool) (fracVal PosRat.half false) (fracVal PosRat.half false) :=
  ⟨fracValRA_isCoreFreeRA Bool, PosRat.half_lt_one, fun h => h rfl,
   fpUpdate_refl (fracValRA Bool) (fracVal PosRat.half false)⟩

end Toy.RA
