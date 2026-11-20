import Toy.MachInt.Defs
import Toy.MachInt.Examples
import Toy.MachInt.Lemmas

/-!
# Main theorem statements (`Toy.MachInt`)

This module states the core refinement theorems and exact overflow obligations for
fixed-width machine-integer arithmetic:
1. Wrapping evaluation of ring expressions (`+`, `-`, `*`, unary `-`, constants) equals
   integer evaluation reduced modulo `2^n`, transferring all unconditional integer ring
   identities with no overflow side conditions.
2. Checked evaluation (`evalCheckedU`, `evalCheckedS`) is sound with respect to
   mathematical integer evaluation whenever it returns `some v`, and succeeds (`isSome = true`)
   if and only if every subexpression evaluates within range.
3. Order does not transfer unconditionally through wrapping (`MAX + 1` fails strict ordering
   at `BitVec.allOnes n` / `BitVec.intMax n`), whereas monotonicity of `+` under `<` holds
   under sufficient no-overflow hypotheses and is characterized exactly by identical overflow
   flags on both summands.
4. Checked division and remainder: unsigned `/` and `%` match `Nat.div`/`Nat.mod`;
   signed `/` and `%` match truncating `Int.tdiv`/`Int.tmod` (not Lean's default `Int`
   `/`/`%`, which are Euclidean `Int.ediv`/`Int.emod`); `MIN / -1` is the unique
   overflowing signed division; `checked_rem(MIN, -1)` is `none` despite `0` being
   in range; and `div_euclid`/`rem_euclid` match `Int.ediv`/`Int.emod`.
5. Masked left/right shifts (`wrapping_shl`/`wrapping_shr`) agree with mathematical
   shift/power-of-two arithmetic when `ShiftInBounds n k` holds.
6. Numeric `as` casts capture unsigned truncation/zero-extension, signed sign-extension,
   same-width bit-pattern reinterpretation, and widen-then-narrow round trips.
-/

namespace Toy.MachInt

/-! ## Result 1: Wrapping transfers integer ring identities -/

/-- Wrapping evaluation of any `RingExpr` in unsigned reading equals mathematical `Int`
    evaluation of the lifted environment reduced modulo `2^n` (Euclidean `Int.emod`). -/
theorem evalWrap_toNat_eq_emod (n : Nat) (env : Nat → BitVec n) (e : RingExpr) :
    ((evalWrap n env e).toNat : Int) = (evalInt (fun i => (env i).toNat) e) % ((2 ^ n : Nat) : Int) := by
  exact evalWrap_toNat_cast n env e

/-- Wrapping evaluation of any `RingExpr` in two's-complement signed reading equals
    mathematical `Int` evaluation of the lifted signed environment reduced via balanced
    modulo `Int.bmod · (2^n)`. -/
theorem evalWrap_toInt_eq_bmod (n : Nat) (env : Nat → BitVec n) (e : RingExpr) :
    (evalWrap n env e).toInt = (evalInt (fun i => (env i).toInt) e).bmod (2 ^ n) := by
  exact evalWrap_toInt_bmod n env e

/-- Any ring identity proved over unbounded mathematical integers `Int` transfers
    unconditionally to fixed-width wrapping evaluation for every bitwidth `n` and every
    environment `env : Nat → BitVec n`. -/
theorem evalWrap_eq_of_intRingIdentity (n : Nat) (env : Nat → BitVec n)
    {e₁ e₂ : RingExpr} (hid : IntRingIdentity e₁ e₂) :
    evalWrap n env e₁ = evalWrap n env e₂ := by
  have h := fun e => evalWrap_eq_ofInt_evalInt n env (fun i => (env i).toInt)
    (fun i => ofInt_toInt_self (env i)) e
  rw [h e₁, h e₂, hid]

/-! ## Result 2: Checked arithmetic refinement -/

/-- Soundness of checked unsigned evaluation: if `evalCheckedU n env e = some v`
    (definitionally `evalPlainU n env e = Outcome.ok v`), then `v.toNat` equals the exact
    mathematical integer evaluation `evalInt (fun i => (env i).toNat) e`. -/
theorem evalCheckedU_sound (n : Nat) (env : Nat → BitVec n) (e : RingExpr) (v : BitVec n)
    (hsome : evalCheckedU n env e = some v) :
    (v.toNat : Int) = evalInt (fun i => (env i).toNat) e := by
  obtain ⟨hv, hs⟩ := evalCheckedU_eq_some_imp n env e v hsome
  rw [evalInt_eq_evalWrap_toNat_of_inRange n env e (subexprsInRange_root hs), hv]

/-- Sufficiency of per-subexpression range bounds for checked unsigned evaluation: if every
    subexpression (variables, constants, and compound nodes) evaluates inside
    `InUnsignedRange n`, then `evalCheckedU n env e = some (evalWrap n env e)`. -/
theorem evalCheckedU_complete (n : Nat) (env : Nat → BitVec n) (e : RingExpr)
    (hrange : SubexprsInRange (InUnsignedRange n) (fun i => (env i).toNat) e) :
    evalCheckedU n env e = some (evalWrap n env e) := by
  exact evalCheckedU_eq_some_of_subexprsInRange n env e hrange

/-- Exact side-condition characterization for checked unsigned evaluation on `RingExpr`:
    `evalCheckedU n env e` succeeds (`isSome = true`) if and only if every subexpression
    evaluates inside `InUnsignedRange n`. -/
theorem evalCheckedU_isSome_iff_subexprsInRange (n : Nat) (env : Nat → BitVec n) (e : RingExpr) :
    (evalCheckedU n env e).isSome = true ↔
      SubexprsInRange (InUnsignedRange n) (fun i => (env i).toNat) e := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    exact (evalCheckedU_eq_some_imp n env e v hv).2
  · intro h
    rw [evalCheckedU_eq_some_of_subexprsInRange n env e h]
    rfl

/-- Soundness of checked signed two's-complement evaluation: if `evalCheckedS n env e = some v`
    (definitionally `evalPlainS n env e = Outcome.ok v`), then `v.toInt` equals the exact
    mathematical integer evaluation `evalInt (fun i => (env i).toInt) e`. -/
theorem evalCheckedS_sound (n : Nat) (env : Nat → BitVec n) (e : RingExpr) (v : BitVec n)
    (hsome : evalCheckedS n env e = some v) :
    v.toInt = evalInt (fun i => (env i).toInt) e := by
  obtain ⟨hv, hs⟩ := evalCheckedS_eq_some_imp n env e v hsome
  rw [evalInt_eq_evalWrap_toInt_of_inRange n env e (subexprsInRange_root hs), hv]

/-- Sufficiency of per-subexpression range bounds for checked signed evaluation: if every
    subexpression evaluates inside `InSignedRange n`, then
    `evalCheckedS n env e = some (evalWrap n env e)`. -/
theorem evalCheckedS_complete (n : Nat) (env : Nat → BitVec n) (e : RingExpr)
    (hrange : SubexprsInRange (InSignedRange n) (fun i => (env i).toInt) e) :
    evalCheckedS n env e = some (evalWrap n env e) := by
  exact evalCheckedS_eq_some_of_subexprsInRange n env e hrange

/-- Exact side-condition characterization for checked signed evaluation on `RingExpr`:
    `evalCheckedS n env e` succeeds (`isSome = true`) if and only if every subexpression
    evaluates inside `InSignedRange n`. -/
theorem evalCheckedS_isSome_iff_subexprsInRange (n : Nat) (env : Nat → BitVec n) (e : RingExpr) :
    (evalCheckedS n env e).isSome = true ↔
      SubexprsInRange (InSignedRange n) (fun i => (env i).toInt) e := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    exact (evalCheckedS_eq_some_imp n env e v hv).2
  · intro h
    rw [evalCheckedS_eq_some_of_subexprsInRange n env e h]
    rfl

/-! ## Result 3: Order and addition monotonicity under wrapping -/

/-- Impossibility (unsigned): at every bitwidth `n`, `BitVec.allOnes n + 1#n = 0#n`, so
    strict successor ordering `Ult x (x + 1#n)` fails at `x = BitVec.allOnes n`
    (`u<n>::MAX`), refuting `∀ x : BitVec n, Ult x (x + 1#n)`. -/
theorem not_ult_allOnes_add_one (n : Nat) :
    BitVec.allOnes n + 1#n = 0#n ∧
    ¬ Ult (BitVec.allOnes n) (BitVec.allOnes n + 1#n) ∧
    ¬ (∀ x : BitVec n, Ult x (x + 1#n)) := by
  have hwrap : BitVec.allOnes n + 1#n = 0#n := by
    apply BitVec.eq_of_toNat_eq
    have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rw [BitVec.toNat_add, BitVec.toNat_allOnes, BitVec.toNat_ofNat, BitVec.toNat_zero,
      Nat.add_mod_mod, Nat.sub_add_cancel hp, Nat.mod_self]
  have hnot : ¬ Ult (BitVec.allOnes n) (BitVec.allOnes n + 1#n) := by
    rw [hwrap]
    simp [Ult, BitVec.ult]
  exact ⟨hwrap, hnot, fun hall => hnot (hall (BitVec.allOnes n))⟩

/-- Corollary: `∀ x : BitVec n, Ult x (x + 1#n)` fails for every bitwidth `n`. -/
theorem not_ult_add_one_uMax (n : Nat) :
    ¬ (∀ x : BitVec n, Ult x (x + 1#n)) :=
  (not_ult_allOnes_add_one n).2.2

/-- Under `PosWidth n`, adding `1#n` to `BitVec.allOnes n` wraps strictly below `BitVec.allOnes n`. -/
theorem ult_allOnes_add_one_allOnes_of_posWidth {n : Nat} (hn : PosWidth n) :
    Ult (BitVec.allOnes n + 1#n) (BitVec.allOnes n) := by
  rw [(not_ult_allOnes_add_one n).1]
  have : 1 < 2 ^ n := Nat.one_lt_two_pow (Nat.ne_of_gt hn)
  simp [Ult, BitVec.ult]
  omega

/-- Impossibility (signed): at every bitwidth `n`, `BitVec.intMax n + 1#n = BitVec.intMin n`,
    so signed strict successor ordering `Slt x (x + 1#n)` fails at `x = BitVec.intMax n`
    (`i<n>::MAX`), refuting `∀ x : BitVec n, Slt x (x + 1#n)`. -/
theorem not_slt_intMax_add_one (n : Nat) :
    BitVec.intMax n + 1#n = BitVec.intMin n ∧
    ¬ Slt (BitVec.intMax n) (BitVec.intMax n + 1#n) ∧
    ¬ (∀ x : BitVec n, Slt x (x + 1#n)) := by
  have hwrap : BitVec.intMax n + 1#n = BitVec.intMin n := BitVec.intMax_add_one
  have hnot : ¬ Slt (BitVec.intMax n) (BitVec.intMax n + 1#n) := by
    rw [hwrap]
    intro h
    have hmin := BitVec.toInt_intMin_le (BitVec.intMax n)
    simp only [Slt, BitVec.slt, decide_eq_true_eq] at h
    omega
  exact ⟨hwrap, hnot, fun hall => hnot (hall (BitVec.intMax n))⟩

/-- Corollary: `∀ x : BitVec n, Slt x (x + 1#n)` fails for every bitwidth `n`. -/
theorem not_slt_add_one_sMax (n : Nat) :
    ¬ (∀ x : BitVec n, Slt x (x + 1#n)) :=
  (not_slt_intMax_add_one n).2.2

/-- Under `PosWidth n`, adding `1#n` to `BitVec.intMax n` wraps strictly below `BitVec.intMax n`. -/
theorem slt_intMax_add_one_intMax_of_posWidth {n : Nat} (hn : PosWidth n) :
    Slt (BitVec.intMax n + 1#n) (BitVec.intMax n) := by
  rw [(not_slt_intMax_add_one n).1]
  have hpos : 0 < n := hn
  have h1 : (1 : Int) ≤ (2 : Int) ^ (n - 1) := by
    exact_mod_cast (Nat.one_le_two_pow (n := n - 1))
  simp only [Slt, BitVec.slt, decide_eq_true_eq]
  rw [BitVec.toInt_intMin_of_pos hpos, BitVec.toInt_intMax]
  omega

/-- Unsigned addition preserves `<` (`Ult (a + c) (b + c)`) when `Ult a b` and `NoUAddOverflow b c`
    (which entails `NoUAddOverflow a c` via `noUAddOverflow_of_ult_of_noUAddOverflow`).
    The hypothesis `NoUAddOverflow b c` is sufficient and cannot be dropped alone, though not
    necessary when both sums wrap. -/
theorem ult_add_right_of_noUAddOverflow {n : Nat} (a b c : BitVec n)
    (hlt : Ult a b) (hnoB : NoUAddOverflow b c) :
    Ult (a + c) (b + c) := by
  have hnoA : NoUAddOverflow a c := noUAddOverflow_of_ult_of_noUAddOverflow hlt hnoB
  unfold Ult BitVec.ult at hlt ⊢
  unfold NoUAddOverflow BitVec.uaddOverflow at hnoA hnoB
  simp only [decide_eq_true_eq] at hlt ⊢
  simp only [decide_eq_false_iff_not, Nat.not_le, ge_iff_le] at hnoA hnoB
  rw [BitVec.toNat_add_of_lt hnoA, BitVec.toNat_add_of_lt hnoB]
  omega

/-- Signed addition preserves `<` (`Slt (a + c) (b + c)`) when `Slt a b` and neither sum
    overflows (`NoSAddOverflow a c` and `NoSAddOverflow b c`). Each guard is sufficient and
    cannot be dropped alone, though not necessary when both sums wrap in the same direction. -/
theorem slt_add_right_of_noSAddOverflow {n : Nat} (a b c : BitVec n)
    (hlt : Slt a b) (hnoA : NoSAddOverflow a c) (hnoB : NoSAddOverflow b c) :
    Slt (a + c) (b + c) := by
  unfold Slt BitVec.slt at hlt ⊢
  unfold NoSAddOverflow BitVec.saddOverflow at hnoA hnoB
  simp only [decide_eq_true_eq] at hlt ⊢
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Int.not_le, Int.not_lt,
    ge_iff_le] at hnoA hnoB
  have hn : 0 < n := by
    by_cases h0 : n = 0
    · subst h0
      have ha : a = 0#0 := BitVec.eq_nil a
      have hb : b = 0#0 := BitVec.eq_nil b
      subst ha hb
      simp at hlt
    · exact Nat.pos_of_ne_zero h0
  have hnat : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have hs : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
    calc 2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) hs
      _ = 2 ^ (n - 1) * 2 := Nat.pow_succ 2 (n - 1)
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  have h2pow : (2 : Int) ^ n = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
    have hcast : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by exact_mod_cast hnat
    simpa [Int.natCast_pow] using hcast
  have h2pow_pos : (2 : Int) ^ (n - 1) = ((2 ^ (n - 1) : Nat) : Int) := by
    simp [Int.natCast_pow]
  have ha_eq : (a + c).toInt = a.toInt + c.toInt := by
    rw [BitVec.toInt_add, Int.bmod_eq_of_le_mul_two]
    · simp only [Int.natCast_pow, Int.cast_ofNat_Int]; omega
    · simp only [Int.natCast_pow, Int.cast_ofNat_Int]; omega
  have hb_eq : (b + c).toInt = b.toInt + c.toInt := by
    rw [BitVec.toInt_add, Int.bmod_eq_of_le_mul_two]
    · simp only [Int.natCast_pow, Int.cast_ofNat_Int]; omega
    · simp only [Int.natCast_pow, Int.cast_ofNat_Int]; omega
  rw [ha_eq, hb_eq]
  omega

/-- Exact unsigned order-preservation criterion: given `Ult a b`, adding `c` preserves
    unsigned strict inequality if and only if `a + c` and `b + c` have identical unsigned
    overflow status (either neither wraps, or both wrap modulo `2^n`). -/
theorem ult_add_right_iff_uaddOverflow_eq {n : Nat} (a b c : BitVec n) (hlt : Ult a b) :
    Ult (a + c) (b + c) ↔ BitVec.uaddOverflow a c = BitVec.uaddOverflow b c := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  unfold Ult BitVec.ult at hlt ⊢
  simp only [decide_eq_true_eq] at hlt ⊢
  rw [BitVec.toNat_add, BitVec.toNat_add]
  unfold BitVec.uaddOverflow
  have hm : ∀ x : Nat, x < 2 * 2 ^ n →
      x % 2 ^ n = if x < 2 ^ n then x else x - 2 ^ n := by
    intro x hx
    split
    · exact Nat.mod_eq_of_lt (by assumption)
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hm _ (by omega), hm _ (by omega)]
  by_cases h1 : a.toNat + c.toNat < 2 ^ n <;> by_cases h2 : b.toNat + c.toNat < 2 ^ n <;>
    simp [h1, h2] <;> omega

private theorem bmod_eq_three_cases {n : Nat} (hn : 0 < n) (z : Int)
    (hlo : -(2 * ((2 ^ (n - 1) : Nat) : Int)) ≤ z)
    (hhi : z < 2 * ((2 ^ (n - 1) : Nat) : Int)) :
    z.bmod (2 ^ n) =
      if z < -((2 ^ (n - 1) : Nat) : Int) then z + ((2 ^ n : Nat) : Int)
      else if z < ((2 ^ (n - 1) : Nat) : Int) then z
      else z - ((2 ^ n : Nat) : Int) := by
  have hnat : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have hs : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
    calc 2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) hs
      _ = 2 ^ (n - 1) * 2 := Nat.pow_succ 2 (n - 1)
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  have h2pow : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
    exact_mod_cast hnat
  have heq : (2 : Int) ^ n = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
    simpa [Int.natCast_pow] using h2pow
  split
  · have hstep : z.bmod (2 ^ n) = (z + ((2 ^ n : Nat) : Int)).bmod (2 ^ n) := by
      simpa using (Int.add_bmod_right z (2 ^ n)).symm
    rw [hstep, Int.bmod_eq_of_le_mul_two]
    · simp only [Int.natCast_pow, Int.cast_ofNat_Int]; rw [heq]; rw [← h2pow]; omega
    · simp only [Int.natCast_pow, Int.cast_ofNat_Int]; rw [heq]; rw [← h2pow]; omega
  · split
    · rw [Int.bmod_eq_of_le_mul_two]
      · simp only [Int.natCast_pow, Int.cast_ofNat_Int]; rw [heq]; omega
      · simp only [Int.natCast_pow, Int.cast_ofNat_Int]; rw [heq]; omega
    · have hstep : z.bmod (2 ^ n) = (z - ((2 ^ n : Nat) : Int)).bmod (2 ^ n) := by
        simpa using (Int.sub_bmod_right z (2 ^ n)).symm
      rw [hstep, Int.bmod_eq_of_le_mul_two]
      · simp only [Int.natCast_pow, Int.cast_ofNat_Int]; rw [heq]; rw [← h2pow]; omega
      · simp only [Int.natCast_pow, Int.cast_ofNat_Int]; rw [heq]; rw [← h2pow]; omega

/-- Exact signed order-preservation criterion: given `Slt a b`, adding `c` preserves
    signed strict inequality if and only if `a + c` and `b + c` have identical signed
    overflow status (either neither wraps, or both wrap in the same direction). -/
theorem slt_add_right_iff_saddOverflow_eq {n : Nat} (a b c : BitVec n) (hlt : Slt a b) :
    Slt (a + c) (b + c) ↔ BitVec.saddOverflow a c = BitVec.saddOverflow b c := by
  have hn : 0 < n := by
    by_cases h0 : n = 0
    · subst h0
      have ha : a = 0#0 := BitVec.eq_nil a
      have hb : b = 0#0 := BitVec.eq_nil b
      subst ha hb
      simp [Slt] at hlt
    · exact Nat.pos_of_ne_zero h0
  unfold Slt BitVec.slt at hlt ⊢
  simp only [decide_eq_true_eq] at hlt ⊢
  have hal : -((2 ^ (n - 1) : Nat) : Int) ≤ a.toInt := by
    simpa [Int.natCast_pow] using @BitVec.le_toInt n a
  have hau : a.toInt < ((2 ^ (n - 1) : Nat) : Int) := by
    simpa [Int.natCast_pow] using @BitVec.toInt_lt n a
  have hbl : -((2 ^ (n - 1) : Nat) : Int) ≤ b.toInt := by
    simpa [Int.natCast_pow] using @BitVec.le_toInt n b
  have hbu : b.toInt < ((2 ^ (n - 1) : Nat) : Int) := by
    simpa [Int.natCast_pow] using @BitVec.toInt_lt n b
  have hcl : -((2 ^ (n - 1) : Nat) : Int) ≤ c.toInt := by
    simpa [Int.natCast_pow] using @BitVec.le_toInt n c
  have hcu : c.toInt < ((2 ^ (n - 1) : Nat) : Int) := by
    simpa [Int.natCast_pow] using @BitVec.toInt_lt n c
  have ha_eq : (a + c).toInt = (a.toInt + c.toInt).bmod (2 ^ n) := BitVec.toInt_add a c
  have hb_eq : (b + c).toInt = (b.toInt + c.toInt).bmod (2 ^ n) := BitVec.toInt_add b c
  rw [ha_eq, hb_eq, bmod_eq_three_cases hn _ (by omega) (by omega),
    bmod_eq_three_cases hn _ (by omega) (by omega)]
  have hnat : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have hs : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
    calc 2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) hs
      _ = 2 ^ (n - 1) * 2 := Nat.pow_succ 2 (n - 1)
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  have h2pow : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
    exact_mod_cast hnat
  unfold BitVec.saddOverflow
  have h2p : (2 : Int) ^ (n - 1) = ((2 ^ (n - 1) : Nat) : Int) := by
    simp [Int.natCast_pow]
  have hov_eq : ∀ z : Int,
      (decide (z ≥ (2 : Int) ^ (n - 1)) || decide (z < -(2 : Int) ^ (n - 1))) = true ↔
      (z ≥ ((2 ^ (n - 1) : Nat) : Int) ∨ z < -((2 ^ (n - 1) : Nat) : Int)) := by
    intro z
    rw [h2p]
    simp
  have hov_f : ∀ z : Int,
      (decide (z ≥ (2 : Int) ^ (n - 1)) || decide (z < -(2 : Int) ^ (n - 1))) = false ↔
      (¬ (z ≥ ((2 ^ (n - 1) : Nat) : Int)) ∧ ¬ (z < -((2 ^ (n - 1) : Nat) : Int))) := by
    intro z
    rw [h2p]
    simp
  have ha_cases :
      (a.toInt + c.toInt < -((2 ^ (n - 1) : Nat) : Int)) ∨
      (-((2 ^ (n - 1) : Nat) : Int) ≤ a.toInt + c.toInt ∧ a.toInt + c.toInt < ((2 ^ (n - 1) : Nat) : Int)) ∨
      (((2 ^ (n - 1) : Nat) : Int) ≤ a.toInt + c.toInt) := by omega
  have hb_cases :
      (b.toInt + c.toInt < -((2 ^ (n - 1) : Nat) : Int)) ∨
      (-((2 ^ (n - 1) : Nat) : Int) ≤ b.toInt + c.toInt ∧ b.toInt + c.toInt < ((2 ^ (n - 1) : Nat) : Int)) ∨
      (((2 ^ (n - 1) : Nat) : Int) ≤ b.toInt + c.toInt) := by omega
  rcases ha_cases with haL | ⟨haM1, haM2⟩ | haH <;>
    rcases hb_cases with hbL | ⟨hbM1, hbM2⟩ | hbH
  · have ha_ov := (hov_eq (a.toInt + c.toInt)).2 (Or.inr haL)
    have hb_ov := (hov_eq (b.toInt + c.toInt)).2 (Or.inr hbL)
    rw [ha_ov, hb_ov]
    simp only [haL, hbL, ↓reduceIte, iff_true]
    omega
  · have hb1 : ¬ (b.toInt + c.toInt < -((2 ^ (n - 1) : Nat) : Int)) := by omega
    have hnb : ¬ (b.toInt + c.toInt ≥ ((2 ^ (n - 1) : Nat) : Int)) := by omega
    have ha_ov := (hov_eq (a.toInt + c.toInt)).2 (Or.inr haL)
    have hb_ov := (hov_f (b.toInt + c.toInt)).2 ⟨hnb, hb1⟩
    rw [ha_ov, hb_ov]
    simp only [haL, hb1, hbM2, ↓reduceIte]
    constructor <;> intro h
    · exfalso; omega
    · simp at h
  · exfalso; omega
  · exfalso; omega
  · have ha1 : ¬ (a.toInt + c.toInt < -((2 ^ (n - 1) : Nat) : Int)) := by omega
    have hna : ¬ (a.toInt + c.toInt ≥ ((2 ^ (n - 1) : Nat) : Int)) := by omega
    have hb1 : ¬ (b.toInt + c.toInt < -((2 ^ (n - 1) : Nat) : Int)) := by omega
    have hnb : ¬ (b.toInt + c.toInt ≥ ((2 ^ (n - 1) : Nat) : Int)) := by omega
    have ha_ov := (hov_f (a.toInt + c.toInt)).2 ⟨hna, ha1⟩
    have hb_ov := (hov_f (b.toInt + c.toInt)).2 ⟨hnb, hb1⟩
    rw [ha_ov, hb_ov]
    simp only [ha1, haM2, hb1, hbM2, ↓reduceIte, iff_true]
    omega
  · have ha1 : ¬ (a.toInt + c.toInt < -((2 ^ (n - 1) : Nat) : Int)) := by omega
    have hna : ¬ (a.toInt + c.toInt ≥ ((2 ^ (n - 1) : Nat) : Int)) := by omega
    have hb1 : ¬ (b.toInt + c.toInt < -((2 ^ (n - 1) : Nat) : Int)) := by omega
    have hb2 : ¬ (b.toInt + c.toInt < ((2 ^ (n - 1) : Nat) : Int)) := by omega
    have ha_ov := (hov_f (a.toInt + c.toInt)).2 ⟨hna, ha1⟩
    have hb_ov := (hov_eq (b.toInt + c.toInt)).2 (Or.inl hbH)
    rw [ha_ov, hb_ov]
    simp only [ha1, haM2, hb1, hb2, ↓reduceIte]
    constructor <;> intro h
    · exfalso; omega
    · simp at h
  · exfalso; omega
  · exfalso; omega
  · have ha1 : ¬ (a.toInt + c.toInt < -((2 ^ (n - 1) : Nat) : Int)) := by omega
    have ha2 : ¬ (a.toInt + c.toInt < ((2 ^ (n - 1) : Nat) : Int)) := by omega
    have hb1 : ¬ (b.toInt + c.toInt < -((2 ^ (n - 1) : Nat) : Int)) := by omega
    have hb2 : ¬ (b.toInt + c.toInt < ((2 ^ (n - 1) : Nat) : Int)) := by omega
    have ha_ov := (hov_eq (a.toInt + c.toInt)).2 (Or.inl haH)
    have hb_ov := (hov_eq (b.toInt + c.toInt)).2 (Or.inl hbH)
    rw [ha_ov, hb_ov]
    simp only [ha1, ha2, hb1, hb2, ↓reduceIte, iff_true]
    omega

/-! ## Result 4: Division, remainder, and Euclidean division -/

/-- Checked unsigned division and remainder (`u<n>::checked_div`, `u<n>::checked_rem`):
    whenever `NonZeroDiv b`, both return `some` and agree with `Nat.div` and `Nat.mod`. -/
theorem checkedUDiv_and_checkedURem_eq_nat_div_mod {n : Nat} (a b : BitVec n)
    (hb : NonZeroDiv b) :
    ∃ q r : BitVec n,
      checkedUDiv a b = some q ∧ checkedURem a b = some r ∧
      q.toNat = a.toNat / b.toNat ∧ r.toNat = a.toNat % b.toNat := by
  have hb' : (b == 0#n) = false := by
    unfold NonZeroDiv at hb
    simp [hb]
  refine ⟨a / b, a % b, ?_, ?_, BitVec.toNat_udiv, BitVec.toNat_umod⟩
  · simp only [checkedUDiv, hb', Bool.false_eq_true, ↓reduceIte]
  · simp only [checkedURem, hb', Bool.false_eq_true, ↓reduceIte]

/-- Checked signed division (`i<n>::checked_div`) corresponds to truncating integer division
    `Int.tdiv` (not Lean's default `Int.ediv` `/`) under `NonZeroDiv b` and `NoSDivOverflow a b`. -/
theorem checkedSDiv_eq_some_and_toInt_eq_tdiv {n : Nat} (a b : BitVec n)
    (hb : NonZeroDiv b) (hno : NoSDivOverflow a b) :
    ∃ q : BitVec n,
      checkedSDiv a b = some q ∧ q.toInt = a.toInt.tdiv b.toInt := by
  refine ⟨a.sdiv b, ?_, BitVec.toInt_sdiv_of_ne_or_ne a b (ne_or_ne_of_noSDivOverflow hno)⟩
  simp only [checkedSDiv, sdivGuard_eq_false hb hno, Bool.false_eq_true, ↓reduceIte]

/-- Checked signed remainder (`i<n>::checked_rem`) corresponds to truncating integer remainder
    `Int.tmod` (not Lean's default `Int.emod` `%`) under `NonZeroDiv b` and `NoSDivOverflow a b`. -/
theorem checkedSRem_eq_some_and_toInt_eq_tmod {n : Nat} (a b : BitVec n)
    (hb : NonZeroDiv b) (hno : NoSDivOverflow a b) :
    ∃ r : BitVec n,
      checkedSRem a b = some r ∧ r.toInt = a.toInt.tmod b.toInt := by
  refine ⟨a.srem b, ?_, BitVec.toInt_srem a b⟩
  simp only [checkedSRem, sdivGuard_eq_false hb hno, Bool.false_eq_true, ↓reduceIte]

/-- For every positive bitwidth `PosWidth n`, `MIN / -1` is the unique signed division pair
    whose mathematical truncating quotient falls outside `InSignedRange n`. -/
theorem tdiv_not_inSignedRange_iff_intMin_negOne {n : Nat} (hn : PosWidth n)
    (a b : BitVec n) :
    ¬ InSignedRange n (a.toInt.tdiv b.toInt) ↔ (a = BitVec.intMin n ∧ b = -1#n) := by
  constructor
  · intro hout
    refine Classical.byContradiction fun hne => hout ?_
    rw [← BitVec.toInt_sdiv_of_ne_or_ne a b (ne_or_ne_of_noSDivOverflow hne)]
    exact inSignedRange_toInt _
  · rintro ⟨rfl, rfl⟩
    have hpos : 0 < n := hn
    rw [inSignedRange_iff_of_pos hpos, BitVec.toInt_intMin_of_pos hpos, BitVec.neg_one_eq_allOnes,
      BitVec.toInt_allOnes]
    simp only [hpos, ↓reduceIte, Int.tdiv_neg, Int.tdiv_one]
    omega

/-- Trap-on-remainder edge case: for every `PosWidth n`, `-1#n ≠ 0#n` and the mathematical
    remainder `(BitVec.intMin n).toInt.tmod (-1#n).toInt = 0` is in `InSignedRange n`, yet
    both `checkedSRem (intMin n) (-1#n)` and `checkedSRemEuclid (intMin n) (-1#n)` equal
    `none` (by unfolding; the `= none` results hold at every width `n` via
    `checkedSRem_intMin_negOne_eq_none_unconditional`, while `PosWidth n` is required only
    for `NonZeroDiv (-1#n)`). -/
theorem checkedSRem_intMin_negOne_eq_none {n : Nat} (hn : PosWidth n) :
    NonZeroDiv (-1#n) ∧
    InSignedRange n ((BitVec.intMin n).toInt.tmod (-1#n).toInt) ∧
    checkedSRem (BitVec.intMin n) (-1#n) = none ∧
    checkedSRemEuclid (BitVec.intMin n) (-1#n) = none := by
  have hpow : 1 < 2 ^ n := Nat.one_lt_two_pow (Nat.ne_of_gt hn)
  have hneg1 : (-1#n) ≠ 0#n := by
    intro h
    have htn : (-1#n).toNat = (0#n).toNat := congrArg BitVec.toNat h
    rw [BitVec.toNat_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpow,
      BitVec.toNat_zero] at htn
    have hmod : (2 ^ n - 1) % 2 ^ n = 2 ^ n - 1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod] at htn
    omega
  have hmin_in : InSignedRange n 0 := by
    unfold InSignedRange sMinVal sMaxVal
    rw [BitVec.toInt_intMin_of_pos hn, BitVec.toInt_intMax]
    have hpow1 : (1 : Int) ≤ (2 : Int) ^ (n - 1) := by
      exact_mod_cast (Nat.one_le_two_pow (n := n - 1))
    omega
  have htmod : (BitVec.intMin n).toInt.tmod (-1#n).toInt = 0 := by
    rw [BitVec.toInt_intMin_of_pos hn, BitVec.neg_one_eq_allOnes, BitVec.toInt_allOnes]
    have hpos : 0 < n := hn
    simp [hpos]
  refine ⟨hneg1, ?_, ?_, ?_⟩
  · rw [htmod]
    exact hmin_in
  · simp [checkedSRem]
  · simp [checkedSRemEuclid]

/-- Checked Euclidean signed division (`i<n>::checked_div_euclid`) returns `some q` with
    `q.toInt = a.toInt.ediv b.toInt` under `NonZeroDiv b` and `NoSDivOverflow a b`. -/
theorem checkedSDivEuclid_eq_some_and_toInt_eq_ediv {n : Nat} (a b : BitVec n)
    (hb : NonZeroDiv b) (hno : NoSDivOverflow a b) :
    ∃ q : BitVec n,
      checkedSDivEuclid a b = some q ∧ q.toInt = a.toInt.ediv b.toInt := by
  refine ⟨sdivEuclid a b, ?_, toInt_sdivEuclid a b hb hno⟩
  simp only [checkedSDivEuclid, sdivGuard_eq_false hb hno, Bool.false_eq_true, ↓reduceIte]

/-- Checked Euclidean signed remainder (`i<n>::checked_rem_euclid`) returns `some r` with
    `r.toInt = a.toInt.emod b.toInt` under `NonZeroDiv b` and `NoSDivOverflow a b`. -/
theorem checkedSRemEuclid_eq_some_and_toInt_eq_emod {n : Nat} (a b : BitVec n)
    (hb : NonZeroDiv b) (hno : NoSDivOverflow a b) :
    ∃ r : BitVec n,
      checkedSRemEuclid a b = some r ∧ r.toInt = a.toInt.emod b.toInt := by
  refine ⟨sremEuclid a b, ?_, toInt_sremEuclid a b hb⟩
  simp only [checkedSRemEuclid, sdivGuard_eq_false hb hno, Bool.false_eq_true, ↓reduceIte]

/-! ## Result 5: Shifts and shift-count masking -/

/-- When `ShiftInBounds n k` holds (`k < n`), `wrappingShl x k` agrees with `checkedShl x k`
    and computes `(x.toNat * 2^k) % 2^n` (and `Int.bmod (x.toInt * 2^k) (2^n)`). -/
theorem wrappingShl_eq_mul_twoPow_of_shiftInBounds {n k : Nat} (x : BitVec n)
    (hk : ShiftInBounds n k) :
    checkedShl x k = some (wrappingShl x k) ∧
    (wrappingShl x k).toNat = (x.toNat * 2 ^ k) % 2 ^ n ∧
    (wrappingShl x k).toInt = (x.toInt * ((2 ^ k : Nat) : Int)).bmod (2 ^ n) := by
  unfold ShiftInBounds at hk
  have hmod : k % n = k := Nat.mod_eq_of_lt hk
  have hwrap : wrappingShl x k = x <<< k := by
    unfold wrappingShl
    rw [hmod]
  refine ⟨?_, ?_, ?_⟩
  · simp [checkedShl, hk, hwrap]
  · rw [hwrap, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  · rw [hwrap, BitVec.toInt_shiftLeft]
    have hnat : ((x.toNat <<< k : Nat) : Int) = (x.toNat : Int) * ((2 ^ k : Nat) : Int) := by
      rw [Nat.shiftLeft_eq]
      exact_mod_cast rfl
    rw [hnat, BitVec.toInt_eq_toNat_bmod, Int.bmod_mul_bmod]

/-- When `ShiftInBounds n k` holds (`k < n`), `wrappingUShr x k` agrees with `checkedUShr x k`
    and computes `x.toNat / 2^k`, while `wrappingSShr x k` agrees with `checkedSShr x k`
    and computes `x.toInt.fdiv (2^k)` (arithmetic floor shift, not truncating `tdiv`). -/
theorem wrappingUShr_and_wrappingSShr_of_shiftInBounds {n k : Nat} (x : BitVec n)
    (hk : ShiftInBounds n k) :
    checkedUShr x k = some (wrappingUShr x k) ∧
    (wrappingUShr x k).toNat = x.toNat / 2 ^ k ∧
    checkedSShr x k = some (wrappingSShr x k) ∧
    (wrappingSShr x k).toInt = x.toInt.fdiv ((2 ^ k : Nat) : Int) := by
  unfold ShiftInBounds at hk
  have hmod : k % n = k := Nat.mod_eq_of_lt hk
  have hwu : wrappingUShr x k = x >>> k := by
    unfold wrappingUShr
    rw [hmod]
  have hws : wrappingSShr x k = x.sshiftRight k := by
    unfold wrappingSShr
    rw [hmod]
  have hpow_pos : (0 : Int) < ((2 ^ k : Nat) : Int) := by
    exact_mod_cast (Nat.two_pow_pos k)
  have h_sr_eq_fdiv : x.toInt >>> k = x.toInt.fdiv ((2 ^ k : Nat) : Int) := by
    rw [Int.shiftRight_eq_div_pow, Int.fdiv_eq_ediv_of_nonneg _ (Int.le_of_lt hpow_pos)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [checkedUShr, hk, hwu]
  · rw [hwu, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · simp [checkedSShr, hk, hws]
  · rw [hws, BitVec.sshiftRight_eq, BitVec.toInt_ofInt]
    have hlow : -((2 ^ (n - 1) : Nat) : Int) ≤ x.toInt >>> k := by
      simpa [Int.natCast_pow] using (BitVec.le_toInt_shiftRight (x := x) (n := k))
    have hhigh : x.toInt >>> k < ((2 ^ (n - 1) : Nat) : Int) := by
      simpa [Int.natCast_pow] using (BitVec.toInt_shiftRight_lt (x := x) (n := k))
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
    have hnat : 2 ^ n = 2 * 2 ^ (n - 1) := by
      have hs : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
      calc 2 ^ n = 2 ^ ((n - 1) + 1) := congrArg (2 ^ ·) hs
        _ = 2 ^ (n - 1) * 2 := Nat.pow_succ 2 (n - 1)
        _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
    have hpow : ((2 ^ n : Nat) : Int) = 2 * ((2 ^ (n - 1) : Nat) : Int) := by
      exact_mod_cast hnat
    have hbmod : (x.toInt >>> k).bmod (2 ^ n) = x.toInt >>> k := by
      rw [Int.bmod_eq_of_le_mul_two]
      · rw [hpow]; omega
      · rw [hpow]; omega
    rw [hbmod, h_sr_eq_fdiv]

/-! ## Result 6: Numeric `as` casts and round trips -/

/-- Casting an unsigned `n`-bit value to `m` bits computes `x.toNat % 2^m` unconditionally. -/
theorem castFromUnsigned_toNat_eq_mod {n m : Nat} (x : BitVec n) :
    (castFromUnsigned m x).toNat = x.toNat % 2 ^ m := by
  unfold castFromUnsigned
  exact BitVec.toNat_setWidth m x

/-- Casting an unsigned `n`-bit value first to `m` bits and then widening/keeping to `k` bits
    (`WidthLe m k`) preserves the modulo-`2^m` truncated value `x.toNat % 2^m`, modeling
    `(x as u8) as u32 = x % 256`. -/
theorem castFromUnsigned_widened_toNat_eq_mod {n m k : Nat} (x : BitVec n) (hle : WidthLe m k) :
    (castFromUnsigned k (castFromUnsigned m x)).toNat = x.toNat % 2 ^ m := by
  unfold castFromUnsigned WidthLe at *
  rw [BitVec.toNat_setWidth_of_le hle, BitVec.toNat_setWidth]

/-- Concrete specialization `(x as u8) as u32 = x % 256` on 32-bit unsigned integers. -/
theorem cast_u32_to_u8_to_u32_eq_mod_256 (x : BitVec 32) :
    (castFromUnsigned 32 (castFromUnsigned 8 x)).toNat = x.toNat % 256 := by
  simpa using castFromUnsigned_widened_toNat_eq_mod (n := 32) (m := 8) (k := 32) x (by decide)

/-- Sign-extending a signed `n`-bit integer to width `m` (`WidthLe n m`) preserves its
    two's-complement mathematical integer value `toInt`. -/
theorem castFromSigned_toInt_eq_of_widthLe {n m : Nat} (x : BitVec n) (hle : WidthLe n m) :
    (castFromSigned m x).toInt = x.toInt := by
  unfold castFromSigned WidthLe at *
  exact BitVec.toInt_signExtend_of_le hle

/-- Same-width `as` cast (`i<n> as u<n>` / `u<n> as i<n>`) is pure bit-pattern
    reinterpretation: `(reinterpretCast x).toNat` equals `x.toInt` shifted by `2^n` when
    negative (`x.toInt < 0`), and `(reinterpretCast x).toInt = Int.bmod x.toNat (2^n)`. -/
theorem reinterpretCast_characterization {n : Nat} (x : BitVec n) :
    (reinterpretCast x).toNat = (if x.toInt < 0 then x.toInt + ((2 ^ n : Nat) : Int) else x.toInt) ∧
    (reinterpretCast x).toInt = Int.bmod x.toNat (2 ^ n) := by
  unfold reinterpretCast
  constructor
  · rw [BitVec.toInt_eq_msb_cond]
    cases h : x.msb
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hnonneg : ¬ ((x.toNat : Int) < 0) := by omega
      simp [hnonneg]
    · simp only [↓reduceIte]
      have hneg : (x.toNat : Int) - ((2 ^ n : Nat) : Int) < 0 := by
        have hx : x.toNat < 2 ^ n := x.isLt
        omega
      simp only [hneg, ↓reduceIte]
      omega
  · exact @BitVec.toInt_eq_toNat_bmod n x

/-- Widening then narrowing back (`u<n> -> u<m> -> u<n>` and `i<n> -> i<m> -> i<n>`) is an
    exact identity whenever `WidthLe n m` (`n ≤ m`). -/
theorem cast_roundTrip_widen_then_narrow_of_widthLe {n m : Nat} (x : BitVec n)
    (hle : WidthLe n m) :
    castFromUnsigned n (castFromUnsigned m x) = x ∧
    castFromSigned n (castFromSigned m x) = x := by
  unfold castFromUnsigned castFromSigned WidthLe at *
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth_of_le hle, Nat.mod_eq_of_lt x.isLt]
  · apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend, BitVec.toInt_signExtend_of_le hle, Nat.min_eq_left hle,
      BitVec.toInt_bmod_cancel]

end Toy.MachInt
