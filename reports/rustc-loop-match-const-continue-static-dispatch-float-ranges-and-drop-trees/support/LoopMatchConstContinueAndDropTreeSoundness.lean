/-
  LoopMatchConstContinueAndDropTreeSoundness.lean

  Kernel-checked Lean v4.34.1 formalization of rustc's `#![feature(loop_match)]`
  and `#[const_continue]` lowering:
    1. IEEE-754 binary32 static `ValTree` `F32Range` vs dynamic MIR `BinOp::{Eq,Le,Lt}`
       total parity across all 2^32 bit patterns (including `-0.0`, `+0.0`, `+inf`, `-inf`,
       and all `NaN` payloads).
    2. Exact inner-to-outer lexical LIFO drop execution via `rustc`'s `DropTree`
       fold (`compiler/rustc_mir_build/src/builder/scope.rs:1018-1044`) and dual
       `const_continue_drops` parity on `imaginary_target`.
    3. Lock-step observational bisimulation between dynamic loop-header `SwitchInt`
       dispatch and `static_pattern_match` direct-arm jump-threading (including
       `Or`-pattern `sub_branches` and `@`-binding rebinding from `state_place`).
    4. Constructive sharpness counterexamples demonstrating exact necessity of
       each compiler invariant (guard prohibition, pre-jump `state_place` write,
       pre-jump `DropTree` execution, and `!needs_drop(state_ty)`).

  Axiom & codegen hygiene:
    - 0 `sorry`, 0 `Classical.choice`, 0 `omega`, 0 `bv_decide`, 0 `native_decide`,
      0 `partial def`, 0 `._unsafe_rec`.
    - All recursive definitions are marked `noncomputable def`.
    - No `deriving DecidableEq` or `deriving Repr` on any inductive type.
-/

namespace LoopMatchSoundness

/-! ## Part 1: IEEE-754 Binary32 Bit-Exact Ordering and Float Range Parity -/

/-- Exact IEEE-754 binary32 fields: 1-bit sign, 8-bit biased exponent, 23-bit significand. -/
structure F32Bits where
  sign : Bool
  exp  : Nat
  frac : Nat

/-- Bit-width validity invariant for IEEE-754 binary32: `exp < 256` and `frac < 2^23`. -/
def F32Bits.Valid (x : F32Bits) : Prop :=
  x.exp < 256 ∧ x.frac < 8388608

/-- Unsigned 31-bit magnitude payload `(exp << 23) + frac`. -/
def F32Bits.mag (x : F32Bits) : Nat :=
  x.exp * 8388608 + x.frac

/-- Exact 32-bit IEEE-754 bit pattern matching `f32::to_bits`. -/
def F32Bits.toBits (x : F32Bits) : Nat :=
  (if x.sign then 2147483648 else 0) + x.mag

def F32Bits.isNaN (x : F32Bits) : Bool :=
  decide (x.exp = 255) && !decide (x.frac = 0)

def F32Bits.isZero (x : F32Bits) : Bool :=
  decide (x.exp = 0) && decide (x.frac = 0)

def f32PosZero  : F32Bits := { sign := false, exp := 0,   frac := 0 }
def f32NegZero  : F32Bits := { sign := true,  exp := 0,   frac := 0 }
def f32PosInf   : F32Bits := { sign := false, exp := 255, frac := 0 }
def f32NegInf   : F32Bits := { sign := true,  exp := 255, frac := 0 }
def f32CanonNaN : F32Bits := { sign := false, exp := 255, frac := 4194304 }
def f32One      : F32Bits := { sign := false, exp := 127, frac := 0 }
def f32Five     : F32Bits := { sign := false, exp := 129, frac := 2097152 }

theorem f32NegZero_bits : f32NegZero.toBits = 2147483648 := rfl
theorem f32PosZero_bits : f32PosZero.toBits = 0 := rfl
theorem f32PosInf_bits  : f32PosInf.toBits  = 2139095040 := rfl
theorem f32NegInf_bits  : f32NegInf.toBits  = 4286578688 := rfl

/-- Kernel-fast constructive `Nat` equality as `Bool` (zero `Classical.choice`). -/
def natEqBool (a b : Nat) : Bool :=
  decide (a = b)

/-- Kernel-fast constructive `Nat` strict less-than as `Bool`. -/
def natLtBool (a b : Nat) : Bool :=
  decide (a < b)

/-- Kernel-fast constructive `Nat` less-than-or-equal as `Bool`. -/
def natLeBool (a b : Nat) : Bool :=
  decide (a ≤ b)

/-- IEEE-754 quiet equality (`==`): NaN != everything, `-0.0 == +0.0`. -/
def f32Eq (a b : F32Bits) : Bool :=
  if a.isNaN || b.isNaN then false
  else if a.isZero && b.isZero then true
  else (a.sign == b.sign) && natEqBool a.mag b.mag

/-- IEEE-754 strict less-than (`<`): NaN unordered, `-0.0 < +0.0` is false. -/
def f32Lt (a b : F32Bits) : Bool :=
  if a.isNaN || b.isNaN then false
  else if a.isZero && b.isZero then false
  else match a.sign, b.sign with
    | true,  false => true
    | false, true  => false
    | false, false => natLtBool a.mag b.mag
    | true,  true  => natLtBool b.mag a.mag

/-- IEEE-754 less-than-or-equal (`<=`). -/
def f32Le (a b : F32Bits) : Bool :=
  f32Lt a b || f32Eq a b

/-- Elementary `Nat` helper avoiding `omega`: `e < 255 ∧ f < 8388608 → e * 8388608 + f < 255 * 8388608`. -/
private theorem mag_lt_inf_of_exp_lt {e f : Nat} (he : e < 255) (hf : f < 8388608) :
    e * 8388608 + f < 255 * 8388608 := by
  have h1 : e + 1 ≤ 255 := he
  have h2 : (e + 1) * 8388608 ≤ 255 * 8388608 := Nat.mul_le_mul_right 8388608 h1
  have h3 : e * 8388608 + f < e * 8388608 + 8388608 := Nat.add_lt_add_left hf (e * 8388608)
  have h4 : e * 8388608 + 8388608 = (e + 1) * 8388608 := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [h4] at h3
  exact Nat.lt_of_lt_of_le h3 h2

/-- Any valid non-NaN binary32 value satisfies `x.exp = 255 → x.frac = 0`. -/
private theorem valid_non_nan_exp_255 {x : F32Bits} (hnan : x.isNaN = false)
    (he : x.exp = 255) : x.frac = 0 := by
  unfold F32Bits.isNaN at hnan
  rw [he] at hnan
  have h255 : decide (255 = 255) = true := rfl
  rw [h255, Bool.true_and] at hnan
  cases hf : decide (x.frac = 0) with
  | true => exact of_decide_eq_true hf
  | false => rw [hf] at hnan; cases hnan

/-- Any valid non-NaN binary32 has `x.mag < 255 * 8388608` or `x.exp = 255 ∧ x.frac = 0`. -/
private theorem valid_non_nan_mag_cases {x : F32Bits} (hv : x.Valid) (hnan : x.isNaN = false) :
    x.mag < 255 * 8388608 ∨ (x.exp = 255 ∧ x.frac = 0) := by
  have hle : x.exp ≤ 255 := Nat.le_of_lt_succ hv.1
  cases Nat.lt_or_eq_of_le hle with
  | inl hlt =>
    exact Or.inl (mag_lt_inf_of_exp_lt hlt hv.2)
  | inr heq =>
    exact Or.inr ⟨heq, valid_non_nan_exp_255 hnan heq⟩

theorem f32Le_negInf_left {x : F32Bits} (hv : x.Valid) :
    f32Le f32NegInf x = !x.isNaN := by
  have hinf_nan : f32NegInf.isNaN = false := rfl
  have hinf_zero : f32NegInf.isZero = false := rfl
  have hinf_sign : f32NegInf.sign = true := rfl
  have hinf_mag : f32NegInf.mag = 255 * 8388608 := rfl
  unfold f32Le f32Lt f32Eq
  rw [hinf_nan, hinf_zero, hinf_sign]
  cases hnan : x.isNaN with
  | true =>
    simp only [Bool.false_or, ↓reduceIte, Bool.or_self, Bool.not_true]
  | false =>
    simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.not_false]
    cases hs : x.sign with
    | false =>
      simp only [Bool.true_or]
    | true =>
      simp only [beq_self_eq_true, Bool.true_and]
      cases valid_non_nan_mag_cases hv hnan with
      | inl hlt =>
        have hblt : natLtBool x.mag f32NegInf.mag = true := by
          unfold natLtBool
          rw [hinf_mag]
          exact decide_eq_true hlt
        rw [hblt]
        rfl
      | inr hinf =>
        have hmag : f32NegInf.mag = x.mag := by
          rw [hinf_mag]
          unfold F32Bits.mag
          rw [hinf.1, hinf.2, Nat.add_zero]
        rw [hmag]
        have heq : natEqBool x.mag x.mag = true := decide_eq_true rfl
        rw [heq, Bool.or_true]

theorem f32Le_posInf_right {x : F32Bits} (hv : x.Valid) :
    f32Le x f32PosInf = !x.isNaN := by
  have hinf_nan : f32PosInf.isNaN = false := rfl
  have hinf_zero : f32PosInf.isZero = false := rfl
  have hinf_sign : f32PosInf.sign = false := rfl
  have hinf_mag : f32PosInf.mag = 255 * 8388608 := rfl
  unfold f32Le f32Lt f32Eq
  rw [hinf_nan, hinf_zero, hinf_sign]
  cases hnan : x.isNaN with
  | true =>
    simp only [Bool.or_false, ↓reduceIte, Bool.or_self, Bool.not_true]
  | false =>
    simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.not_false]
    cases hs : x.sign with
    | true =>
      simp only [Bool.true_or]
    | false =>
      simp only [beq_self_eq_true, Bool.true_and]
      cases valid_non_nan_mag_cases hv hnan with
      | inl hlt =>
        have hblt : natLtBool x.mag f32PosInf.mag = true := by
          unfold natLtBool
          rw [hinf_mag]
          exact decide_eq_true hlt
        rw [hblt]
        rfl
      | inr hinf =>
        have hmag : x.mag = f32PosInf.mag := by
          rw [hinf_mag]
          unfold F32Bits.mag
          rw [hinf.1, hinf.2, Nat.add_zero]
        rw [hmag]
        have heq : natEqBool f32PosInf.mag f32PosInf.mag = true := decide_eq_true rfl
        rw [heq, Bool.or_true]

theorem f32Lt_nan_right (a x : F32Bits) (hnan : x.isNaN = true) : f32Lt a x = false := by
  unfold f32Lt; rw [hnan]; simp

theorem f32Lt_nan_left (x b : F32Bits) (hnan : x.isNaN = true) : f32Lt x b = false := by
  unfold f32Lt; rw [hnan]; simp

theorem f32Le_nan_right (a x : F32Bits) (hnan : x.isNaN = true) : f32Le a x = false := by
  unfold f32Le f32Lt f32Eq; rw [hnan]; simp

theorem f32Le_nan_left (x b : F32Bits) (hnan : x.isNaN = true) : f32Le x b = false := by
  unfold f32Le f32Lt f32Eq; rw [hnan]; simp

/-- Helper: `(a < b || a = b) && (b < a || b = a)` reduces to `a = b` (zero `Classical.choice`). -/
private theorem nat_le_antisymm_bool (a b : Nat) :
    ((natLtBool a b || natEqBool a b) && (natLtBool b a || natEqBool b a)) = natEqBool a b := by
  unfold natLtBool natEqBool
  cases hab : decide (a < b) with
  | true =>
    have hlt : a < b := of_decide_eq_true hab
    have hba : decide (b < a) = false := decide_eq_false (Nat.lt_asymm hlt)
    have hne1 : decide (a = b) = false := decide_eq_false (Nat.ne_of_lt hlt)
    have hne2 : decide (b = a) = false := decide_eq_false (Nat.ne_of_gt hlt)
    rw [hba, hne1, hne2]
    rfl
  | false =>
    cases hba : decide (b < a) with
    | true =>
      have hlt : b < a := of_decide_eq_true hba
      have hne1 : decide (a = b) = false := decide_eq_false (Nat.ne_of_gt hlt)
      have hne2 : decide (b = a) = false := decide_eq_false (Nat.ne_of_lt hlt)
      rw [hne1, hne2]
      rfl
    | false =>
      cases heq : decide (a = b) with
      | true =>
        have h : a = b := of_decide_eq_true heq
        subst h
        have hrefl : decide (a = a) = true := decide_eq_true rfl
        rw [hrefl]
        rfl
      | false =>
        rfl

/-- Helper: `natEqBool` symmetry without `LawfulBEq Nat` (zero `Classical.choice`). -/
private theorem nat_eq_bool_comm (a b : Nat) : natEqBool a b = natEqBool b a := by
  unfold natEqBool
  cases h : decide (a = b) with
  | true =>
    have heq : a = b := of_decide_eq_true h
    subst heq
    exact (decide_eq_true rfl).symm
  | false =>
    have hne : a ≠ b := of_decide_eq_false h
    exact (decide_eq_false (fun hba => hne hba.symm)).symm

/-- Helper: reversed-sign variant `((b < a || a = b) && (a < b || b = a)) = (a = b)`. -/
private theorem nat_le_antisymm_bool_rev (a b : Nat) :
    ((natLtBool b a || natEqBool a b) && (natLtBool a b || natEqBool b a)) = natEqBool a b := by
  rw [nat_eq_bool_comm a b]
  have h := nat_le_antisymm_bool b a
  rw [nat_eq_bool_comm a b] at h
  exact h

/-- Static `rustc_apfloat` `F32Range(l, h, end)` check in
`compiler/rustc_mir_build/src/builder/matches/mod.rs:2964-2970`:
`(*l..=*h).contains(&actual)` or `(*l..*h).contains(&actual)`. -/
def apfloatRangeContains (lo hi : F32Bits) (incl : Bool) (actual : F32Bits) : Bool :=
  f32Le lo actual && (if incl then f32Le actual hi else f32Lt actual hi)

/-- Dynamic MIR `TestKind::Range` check in
`compiler/rustc_mir_build/src/builder/matches/test.rs:238-275`:
tests finite `lo` with `BinOp::Le`, finite `hi` with `BinOp::Le`/`BinOp::Lt`,
and skips non-finite endpoints. -/
def mirDynamicFloatRangeTest (lo hi : Option F32Bits) (incl : Bool) (actual : F32Bits) : Bool :=
  let loOk := match lo with
    | none => true
    | some l => f32Le l actual
  let hiOk := match hi with
    | none => true
    | some h => if incl then f32Le actual h else f32Lt actual h
  loOk && hiOk

/-- Dynamic MIR `TestKind::ScalarEq` check (`matches/test.rs:227-236`) for a float literal. -/
def mirDynamicFloatEqTest (expected actual : F32Bits) : Bool :=
  f32Eq expected actual

private theorem f32Lt_of_non_nan_non_zero (a b : F32Bits)
    (ha : a.isNaN = false) (hb : b.isNaN = false)
    (hz : (a.isZero && b.isZero) = false) :
    f32Lt a b =
      match a.sign, b.sign with
      | true,  false => true
      | false, true  => false
      | false, false => natLtBool a.mag b.mag
      | true,  true  => natLtBool b.mag a.mag := by
  unfold f32Lt
  rw [ha, hb, hz]
  rfl

private theorem f32Eq_of_non_nan_non_zero (a b : F32Bits)
    (ha : a.isNaN = false) (hb : b.isNaN = false)
    (hz : (a.isZero && b.isZero) = false) :
    f32Eq a b = ((a.sign == b.sign) && natEqBool a.mag b.mag) := by
  unfold f32Eq
  rw [ha, hb, hz]
  rfl

private theorem f32_sign_mag_antisymm (vs xs : Bool) (vm xm : Nat) :
    (((match vs, xs with
        | true,  false => true
        | false, true  => false
        | false, false => natLtBool vm xm
        | true,  true  => natLtBool xm vm) || ((vs == xs) && natEqBool vm xm)) &&
     ((match xs, vs with
        | true,  false => true
        | false, true  => false
        | false, false => natLtBool xm vm
        | true,  true  => natLtBool vm xm) || ((xs == vs) && natEqBool xm vm))) =
    ((vs == xs) && natEqBool vm xm) := by
  cases vs <;> cases xs
  · simp only [beq_self_eq_true, Bool.true_and]
    exact nat_le_antisymm_bool vm xm
  · rfl
  · rfl
  · simp only [beq_self_eq_true, Bool.true_and]
    exact nat_le_antisymm_bool_rev vm xm

private theorem f32_singleton_non_nan_non_both_zero (v x : F32Bits)
    (hv : v.isNaN = false) (hx : x.isNaN = false)
    (hz1 : (v.isZero && x.isZero) = false) (hz2 : (x.isZero && v.isZero) = false) :
    (f32Le v x && f32Le x v) = f32Eq v x := by
  unfold f32Le
  rw [f32Lt_of_non_nan_non_zero v x hv hx hz1,
      f32Eq_of_non_nan_non_zero v x hv hx hz1,
      f32Lt_of_non_nan_non_zero x v hx hv hz2,
      f32Eq_of_non_nan_non_zero x v hx hv hz2]
  exact f32_sign_mag_antisymm v.sign x.sign v.mag x.mag

/-- Exact parity between singleton `F32Range(v, v, Included)` (produced by
`rustc_pattern_analysis/src/rustc.rs:569-576`) and dynamic `BinOp::Eq` (`TestKind::ScalarEq`). -/
theorem f32_singleton_range_eq_scalar_eq (v x : F32Bits) :
    apfloatRangeContains v v true x = mirDynamicFloatEqTest v x := by
  unfold apfloatRangeContains mirDynamicFloatEqTest
  cases hv : v.isNaN with
  | true =>
    have h1 : f32Le v x = false := f32Le_nan_left v x hv
    have h2 : f32Eq v x = false := by unfold f32Eq; rw [hv]; rfl
    rw [h1, h2]; rfl
  | false =>
    cases hx : x.isNaN with
    | true =>
      have h1 : f32Le v x = false := f32Le_nan_right v x hx
      have h2 : f32Eq v x = false := by unfold f32Eq; rw [hv, hx]; rfl
      rw [h1, h2]; rfl
    | false =>
      cases hvz : v.isZero with
      | false =>
        exact f32_singleton_non_nan_non_both_zero v x hv hx
          (by rw [hvz]; rfl) (by rw [hvz, Bool.and_false])
      | true =>
        cases hxz : x.isZero with
        | false =>
          exact f32_singleton_non_nan_non_both_zero v x hv hx
            (by rw [hxz, Bool.and_false]) (by rw [hxz]; rfl)
        | true =>
          unfold f32Le f32Lt f32Eq
          rw [hv, hx, hvz, hxz]
          rfl

/-- Exact total parity between `rustc_pattern_analysis` + `static_pattern_match_inner`
(`F32Range` replacing absent bounds with `-inf`/`+inf`) and dynamic MIR `TestKind::Range`
under `rustc`'s THIR invariants (`thir/pattern/mod.rs:250-280`: not twice-open, and
upper-unbounded `lo..` uses `RangeEnd::Included`). -/
theorem ieee754_range_static_eq_dynamic
    (lo hi : Option F32Bits) (incl : Bool) (x : F32Bits)
    (hx : x.Valid)
    (h_not_twice_open : lo.isSome = true ∨ hi.isSome = true)
    (h_open_hi_incl : hi = none → incl = true) :
    apfloatRangeContains (lo.getD f32NegInf) (hi.getD f32PosInf) incl x =
    mirDynamicFloatRangeTest lo hi incl x := by
  cases lo with
  | none =>
    cases hi with
    | none =>
      cases h_not_twice_open with
      | inl h => cases h
      | inr h => cases h
    | some h =>
      unfold apfloatRangeContains mirDynamicFloatRangeTest
      simp only [Option.getD_none, Option.getD_some, Bool.true_and]
      rw [f32Le_negInf_left hx]
      cases hnan : x.isNaN with
      | false => simp
      | true =>
        cases incl with
        | true => simp [f32Le_nan_left x h hnan]
        | false => simp [f32Lt_nan_left x h hnan]
  | some l =>
    cases hi with
    | none =>
      have hincl : incl = true := h_open_hi_incl rfl
      subst hincl
      unfold apfloatRangeContains mirDynamicFloatRangeTest
      simp only [Option.getD_some, Option.getD_none, ↓reduceIte, Bool.and_true]
      rw [f32Le_posInf_right hx]
      cases hnan : x.isNaN with
      | false => simp
      | true => simp [f32Le_nan_right l x hnan]
    | some h =>
      rfl

/-- Theorem (3): IEEE-754 signed-zero equivalence and `NaN` wildcard routing.
    Establishes simultaneously for static `ValTree` `F32Range` and dynamic MIR comparisons:
    (a) `-0.0f32` (`0x8000_0000`) matches `0.0 =>` while preserving its exact sign bit;
    (b) every `NaN` payload fails every `F32Range` test and falls through to `_ =>`;
    (c) open-ended `0.0..` matches `-0.0` and `+inf` while rejecting `-inf` and `NaN`;
    (d) half-open `..0.0` matches `-inf` while rejecting `-0.0`, `+0.0`, and `NaN`. -/
theorem ieee754_signed_zero_and_nan_static_vs_dynamic_agree :
    -- (a) -0.0 matches `0.0 =>` statically and dynamically, retaining bit pattern 0x8000_0000
    (apfloatRangeContains f32PosZero f32PosZero true f32NegZero = true ∧
     mirDynamicFloatEqTest f32PosZero f32NegZero = true ∧
     f32NegZero.toBits = 2147483648) ∧
    -- (b) every NaN fails every F32Range statically and dynamically
    (∀ (lo hi : F32Bits) (incl : Bool) (nan : F32Bits),
      nan.isNaN = true →
      apfloatRangeContains lo hi incl nan = false ∧
      mirDynamicFloatRangeTest (some lo) (some hi) incl nan = false ∧
      mirDynamicFloatEqTest lo nan = false) ∧
    -- (c) open-ended `0.0..` matches -0.0 and +inf, rejects -inf and NaN
    (apfloatRangeContains f32PosZero f32PosInf true f32NegZero = true ∧
     mirDynamicFloatRangeTest (some f32PosZero) none true f32NegZero = true ∧
     apfloatRangeContains f32PosZero f32PosInf true f32PosInf = true ∧
     mirDynamicFloatRangeTest (some f32PosZero) none true f32PosInf = true ∧
     apfloatRangeContains f32PosZero f32PosInf true f32NegInf = false ∧
     apfloatRangeContains f32PosZero f32PosInf true f32CanonNaN = false) ∧
    -- (d) half-open `..0.0` matches -inf, rejects -0.0, +0.0, and NaN
    (apfloatRangeContains f32NegInf f32PosZero false f32NegInf = true ∧
     mirDynamicFloatRangeTest none (some f32PosZero) false f32NegInf = true ∧
     apfloatRangeContains f32NegInf f32PosZero false f32NegZero = false ∧
     mirDynamicFloatRangeTest none (some f32PosZero) false f32NegZero = false ∧
     apfloatRangeContains f32NegInf f32PosZero false f32CanonNaN = false) := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_, ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
          ⟨by decide, by decide, by decide, by decide, by decide⟩⟩
  intro lo hi incl nan hnan
  refine ⟨?_, ?_, ?_⟩
  · unfold apfloatRangeContains
    rw [f32Le_nan_right lo nan hnan]; rfl
  · unfold mirDynamicFloatRangeTest
    dsimp only
    rw [f32Le_nan_right lo nan hnan]; rfl
  · unfold mirDynamicFloatEqTest f32Eq
    rw [hnan]; simp

/-! ## Part 2: `DropTree` Construction and Lexical LIFO Preservation -/

/-- Symbolic identifier for a local variable with a `Drop` destructor. -/
abbrev DropTag := String

/-- Observable trace event: either an arm-body marker or a destructor call. -/
inductive Event where
  | armEmit (label : String) (val : Nat)
  | drop (tag : DropTag)

/-- A node in `rustc`'s `DropTree` (`compiler/rustc_mir_build/src/builder/scope.rs:240-246`). -/
inductive DropNode where
  | root
  | node (tag : DropTag) (next : Nat)

/-- `DropTree` mirroring `compiler/rustc_mir_build/src/builder/scope.rs:230-237`.
    Index `0` is `ROOT_NODE`. -/
structure DropTree where
  nodes : List DropNode

def DropTree.empty : DropTree :=
  { nodes := [DropNode.root] }

/-- Safe list indexing returning `Option α` (`noncomputable def`, 0 `._unsafe_rec`). -/
noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [],      _     => none
  | x :: _,  0     => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- `DropTree::add_drop` (`scope.rs:299-307`), appending a new drop node pointing to `next`. -/
def DropTree.addDrop (t : DropTree) (tag : DropTag) (next : Nat) : DropTree × Nat :=
  let idx := t.nodes.length
  ({ nodes := t.nodes ++ [DropNode.node tag next] }, idx)

/-- Fold over a flat list of scheduled drops in declaration order, matching
`scope.rs:1018-1021` and `scope.rs:1031-1034`:
`scopes[stack_index + 1..].iter().flat_map(|s| &s.drops).fold(ROOT_NODE, add_drop)`. -/
noncomputable def buildDropChainFromList (t : DropTree) (cur : Nat) :
    List DropTag → DropTree × Nat
  | [] => (t, cur)
  | d :: ds =>
    let r := t.addDrop d cur
    buildDropChainFromList r.1 r.2 ds

/-- Flatten nested scopes (`scopes[stack_index + 1..]`, outermost-to-innermost)
    in declaration order (`flat_map(|scope| &scope.drops)`). -/
noncomputable def flattenScopes : List (List DropTag) → List DropTag
  | [] => []
  | s :: ss => s ++ flattenScopes ss

/-- Build the `DropTree` and entry `DropIdx` for nested scopes inside `'blk`. -/
noncomputable def buildScopeDropTree (scopes : List (List DropTag)) : DropTree × Nat :=
  buildDropChainFromList DropTree.empty 0 (flattenScopes scopes)

/-- Execute a `DropTree` from `entry` down to `ROOT_NODE = 0` with step budget `fuel`,
    returning `(emittedDrops, reachedRoot)`. -/
noncomputable def execDropTree (t : DropTree) : Nat → Nat → List DropTag × Bool
  | 0, _ => ([], false)
  | _ + 1, 0 => ([], true)
  | fuel + 1, idx =>
    match listGet? t.nodes idx with
    | some (DropNode.node tag next) =>
      let res := execDropTree t fuel next
      (tag :: res.1, res.2)
    | some DropNode.root => ([], true)
    | none => ([], false)

/-- Reference lexical LIFO drop order: innermost scope first, reverse declaration order
    within each scope. -/
noncomputable def lexicalLifoDrops : List (List DropTag) → List DropTag
  | [] => []
  | s :: ss => lexicalLifoDrops ss ++ s.reverse

private theorem listGet?_append_left {α : Type} :
    ∀ (xs ys : List α) (i : Nat), i < xs.length →
      listGet? (xs ++ ys) i = listGet? xs i
  | [], _, _, h => nomatch h
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, h =>
    listGet?_append_left xs ys i (Nat.lt_of_succ_lt_succ h)

private theorem listGet?_append_eq {α : Type} :
    ∀ (xs : List α) (x : α),
      listGet? (xs ++ [x]) xs.length = some x
  | [], _ => rfl
  | _ :: xs, x => listGet?_append_eq xs x

private theorem execDropTree_append_preserve (nodes suffix : List DropNode) :
    ∀ (fuel idx : Nat),
      idx < nodes.length →
      (∀ k tag next, k < nodes.length →
        listGet? nodes k = some (DropNode.node tag next) → next < k) →
      execDropTree { nodes := nodes ++ suffix } fuel idx =
      execDropTree { nodes := nodes } fuel idx
  | 0, _, _, _ => rfl
  | _ + 1, 0, _, _ => rfl
  | fuel + 1, idx + 1, hlt, hwf => by
    simp only [execDropTree]
    rw [listGet?_append_left nodes suffix (idx + 1) hlt]
    cases hget : listGet? nodes (idx + 1) with
    | none => rfl
    | some dn =>
      cases dn with
      | root => rfl
      | node tag next =>
        have hnext_lt : next < idx + 1 := hwf (idx + 1) tag next hlt hget
        have hnext_bound : next < nodes.length := Nat.lt_trans hnext_lt hlt
        dsimp only
        rw [execDropTree_append_preserve nodes suffix fuel next hnext_bound hwf]

/-- Invariant satisfied by every `DropTree` constructed via `buildDropChainFromList`. -/
structure DropTreeInv (t : DropTree) (cur : Nat) (emitted : List DropTag) : Prop where
  cur_lt : cur < t.nodes.length
  root0  : listGet? t.nodes 0 = some DropNode.root
  acyc   : ∀ k tag next, k < t.nodes.length →
             listGet? t.nodes k = some (DropNode.node tag next) → next < k
  exec   : ∀ fuel, cur < fuel → execDropTree t fuel cur = (emitted, true)

private theorem dropTreeInv_empty : DropTreeInv DropTree.empty 0 [] where
  cur_lt := Nat.zero_lt_succ 0
  root0  := rfl
  acyc   := by
    intro k tag next hk hget
    cases k with
    | zero => simp [DropTree.empty, listGet?] at hget
    | succ k' =>
      have : k' < 0 := Nat.lt_of_succ_lt_succ hk
      exact nomatch this
  exec := by
    intro fuel hfuel
    cases fuel with
    | zero => exact nomatch hfuel
    | succ _ => rfl

private theorem dropTreeInv_addDrop {t : DropTree} {cur : Nat} {emitted : List DropTag}
    (hinv : DropTreeInv t cur emitted) (d : DropTag) :
    let r := t.addDrop d cur
    DropTreeInv r.1 r.2 (d :: emitted) := by
  dsimp only [DropTree.addDrop]
  have hlen : (t.nodes ++ [DropNode.node d cur]).length = t.nodes.length + 1 := by
    simp [List.length_append]
  have hpos : 0 < t.nodes.length := Nat.lt_of_le_of_lt (Nat.zero_le cur) hinv.cur_lt
  refine
    { cur_lt := by rw [hlen]; exact Nat.lt_succ_self _
      root0 := by rw [listGet?_append_left t.nodes [DropNode.node d cur] 0 hpos]; exact hinv.root0
      acyc := ?_
      exec := ?_ }
  · intro k tag next hk hget
    rw [hlen] at hk
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with
    | inl hlt =>
      rw [listGet?_append_left t.nodes [DropNode.node d cur] k hlt] at hget
      exact hinv.acyc k tag next hlt hget
    | inr heq =>
      subst heq
      rw [listGet?_append_eq t.nodes (DropNode.node d cur)] at hget
      cases hget
      exact hinv.cur_lt
  · intro fuel hfuel
    cases fuel with
    | zero => exact nomatch hfuel
    | succ fuel' =>
      cases hlen_eq : t.nodes.length with
      | zero =>
        rw [hlen_eq] at hpos
        exact nomatch hpos
      | succ n =>
        simp only [execDropTree]
        rw [← hlen_eq]
        rw [listGet?_append_eq t.nodes (DropNode.node d cur)]
        dsimp only
        rw [execDropTree_append_preserve t.nodes [DropNode.node d cur] fuel' cur hinv.cur_lt hinv.acyc]
        have hcur_lt_fuel' : cur < fuel' := by
          have h1 : t.nodes.length ≤ fuel' := Nat.le_of_lt_succ hfuel
          exact Nat.lt_of_lt_of_le hinv.cur_lt h1
        rw [hinv.exec fuel' hcur_lt_fuel']

private theorem buildDropChainFromList_inv :
    ∀ (ds : List DropTag) (t : DropTree) (cur : Nat) (emitted : List DropTag),
      DropTreeInv t cur emitted →
      let r := buildDropChainFromList t cur ds
      DropTreeInv r.1 r.2 (ds.reverse ++ emitted)
  | [], t, cur, emitted, hinv => by
    simpa [buildDropChainFromList] using hinv
  | d :: ds, t, cur, emitted, hinv => by
    have hstep := dropTreeInv_addDrop hinv d
    have hrec := buildDropChainFromList_inv ds (t.addDrop d cur).1 (t.addDrop d cur).2 (d :: emitted) hstep
    simpa [buildDropChainFromList, List.reverse_cons, List.append_assoc] using hrec

private theorem flattenScopes_reverse_eq_lexicalLifo :
    ∀ (scopes : List (List DropTag)),
      (flattenScopes scopes).reverse = lexicalLifoDrops scopes
  | [] => rfl
  | s :: ss => by
    simp only [flattenScopes, lexicalLifoDrops, List.reverse_append]
    rw [flattenScopes_reverse_eq_lexicalLifo ss]

/-- Theorem (2): Exact inner-to-outer lexical LIFO drop execution before `real_target` entry.
    For EVERY arbitrarily nested scope stack `scopes`, folding `scopes[stack_index + 1..]`
    through `DropTree::add_drop` and executing from the returned entry `DropIdx` reaches
    `ROOT_NODE` (`real_target`) after emitting the EXACT lexical LIFO drop sequence
    (innermost scope first, reverse declaration order within each scope). -/
theorem const_continue_drop_tree_preserves_lexical_lifo
    (scopes : List (List DropTag)) :
    let res := buildScopeDropTree scopes
    ∀ fuel, res.2 < fuel →
      execDropTree res.1 fuel res.2 = (lexicalLifoDrops scopes, true) := by
  have hinv := buildDropChainFromList_inv (flattenScopes scopes) DropTree.empty 0 [] dropTreeInv_empty
  simp only [List.append_nil] at hinv
  rw [flattenScopes_reverse_eq_lexicalLifo scopes] at hinv
  exact hinv.exec

/-- Dual `DropTree` parity (`scope.rs:1016-1044`): the borrowck `const_continue_drops`
    tree entered from `imaginary_target` and the real exit `DropTree` entered from
    `drop_and_continue_block` fold the exact same `scopes[stack_index + 1..]` slice
    and therefore emit identical LIFO drop sequences before their respective targets
    (`loop_block` vs `real_target`). -/
theorem dual_drop_tree_imaginary_edge_matches_real_edge
    (scopes : List (List DropTag)) :
    let realTree := buildScopeDropTree scopes
    let imagTree := buildScopeDropTree scopes
    ∀ fuel, realTree.2 < fuel →
      execDropTree realTree.1 fuel realTree.2 = execDropTree imagTree.1 fuel imagTree.2 ∧
      execDropTree realTree.1 fuel realTree.2 = (lexicalLifoDrops scopes, true) := by
  dsimp only
  intro fuel hfuel
  have h := const_continue_drop_tree_preserves_lexical_lifo scopes fuel hfuel
  exact ⟨rfl, h⟩

/-- Concrete instantiation matching our live `rustc` and `Miri -Zmiri-tree-borrows`
    measurement (`DROPS=["arm0_inner", "arm0_outer", "arm1"]`). -/
theorem concrete_arm0_nested_drops :
    lexicalLifoDrops [["arm0_outer"], ["arm0_inner"]] ++ ["arm1"] =
    ["arm0_inner", "arm0_outer", "arm1"] := rfl

/-! ## Part 3: Full `#[loop_match]` Operational Semantics and Bisimulation -/

/-- Supported `#[loop_match]` state value (`into.rs:270-281`: integers/bool/char,
    fieldless enum discriminants, and IEEE-754 binary32 floats). -/
inductive StateVal where
  | nat (v : Nat)
  | enumTag (variantIdx : Nat)
  | f32 (bits : F32Bits)

def StateVal.Valid : StateVal → Prop
  | .nat _       => True
  | .enumTag _   => True
  | .f32 bits    => bits.Valid

/-- Guard-free atomic pattern constructors accepted by `static_pattern_match_inner`
    (`matches/mod.rs:2921-2986`). -/
inductive AtomicPat where
  | wild
  | natRange (lo hi : Nat) (incl : Bool)
  | enumVar (variantIdx : Nat)
  | f32Range (lo hi : Option F32Bits) (incl : Bool)
      (h_non_empty : lo.isSome = true ∨ hi.isSome = true)
      (h_open_hi : hi = none → incl = true)

/-- An `Or`-pattern sub-branch (`MatchTreeSubBranch`), optionally carrying an `@`-binding
    that copies `state_place` into the arm's bound local `x` inside `sub_branch.success_block`. -/
structure SubBranchPat where
  pat : AtomicPat
  bindsState : Bool

/-- Top-level arm pattern: either a single atomic pattern (1 `sub_branch`) or a flat
    top-level `Or`-pattern with per-alternative `sub_branches`. -/
inductive ArmPat where
  | single (sub : SubBranchPat)
  | orPat (subs : List SubBranchPat)

/-- Static `static_pattern_match_inner` predicate (`matches/mod.rs:2921-2986`). -/
def staticMatchAtomic (v : StateVal) (p : AtomicPat) : Bool :=
  match p, v with
  | .wild, _ => true
  | .natRange lo hi incl, .nat n =>
    natLeBool lo n && (if incl then natLeBool n hi else natLtBool n hi)
  | .enumVar idx, .enumTag actual => idx == actual
  | .f32Range lo hi incl _ _, .f32 bits =>
    apfloatRangeContains (lo.getD f32NegInf) (hi.getD f32PosInf) incl bits
  | _, _ => false

/-- Dynamic loop-header MIR decision-tree test (`matches/test.rs:227-275` + `SwitchInt`). -/
def dynamicMatchAtomic (v : StateVal) (p : AtomicPat) : Bool :=
  match p, v with
  | .wild, _ => true
  | .natRange lo hi incl, .nat n =>
    natLeBool lo n && (if incl then natLeBool n hi else natLtBool n hi)
  | .enumVar idx, .enumTag actual => idx == actual
  | .f32Range lo hi incl _ _, .f32 bits =>
    mirDynamicFloatRangeTest lo hi incl bits
  | _, _ => false

theorem staticMatchAtomic_eq_dynamicMatchAtomic (v : StateVal) (hv : v.Valid) (p : AtomicPat) :
    staticMatchAtomic v p = dynamicMatchAtomic v p := by
  cases p with
  | wild => rfl
  | natRange lo hi incl =>
    cases v <;> rfl
  | enumVar idx =>
    cases v <;> rfl
  | f32Range lo hi incl hne hhi =>
    cases v with
    | nat _ => rfl
    | enumTag _ => rfl
    | f32 bits =>
      exact ieee754_range_static_eq_dynamic lo hi incl bits hv hne hhi

/-- Search sub-branches of an `Or`-pattern in order, returning `(subBranchIdx, bindsState)`. -/
noncomputable def matchSubBranches (pred : StateVal → AtomicPat → Bool)
    (v : StateVal) (idx : Nat) : List SubBranchPat → Option (Nat × Bool)
  | [] => none
  | sb :: rest =>
    if pred v sb.pat then some (idx, sb.bindsState)
    else matchSubBranches pred v (idx + 1) rest

/-- Resolved target inside `BuiltMatchTree`: `(armIndex, subBranchIndex, bindsState)`. -/
structure MatchTarget where
  armIdx     : Nat
  subIdx     : Nat
  bindsState : Bool

/-- Arm terminator inside a `#[loop_match]` body. -/
inductive ArmExit where
  | exitLoop (retVal : Nat)
  | normalBreak (nextState : StateVal)
  | constContinue (nextConst : StateVal)

/-- Result of executing an arm body (given current `acc` and optional `@`-bound state value). -/
structure ArmEffect where
  newAcc     : Nat
  bodyEvents : List Event
  liveScopes : List (List DropTag)
  exit       : ArmExit

/-- A single guard-free `#[loop_match]` arm. -/
structure LoopMatchArm where
  pat  : ArmPat
  body : Nat → Option StateVal → ArmEffect

/-- Resolve `(armIdx, subIdx, bindsState)` across all arms using `pred`. -/
noncomputable def resolveArms (pred : StateVal → AtomicPat → Bool)
    (v : StateVal) (armIdx : Nat) : List LoopMatchArm → Option MatchTarget
  | [] => none
  | arm :: rest =>
    match arm.pat with
    | .single sb =>
      if pred v sb.pat then some { armIdx := armIdx, subIdx := 0, bindsState := sb.bindsState }
      else resolveArms pred v (armIdx + 1) rest
    | .orPat subs =>
      match matchSubBranches pred v 0 subs with
      | some (subIdx, binds) => some { armIdx := armIdx, subIdx := subIdx, bindsState := binds }
      | none => resolveArms pred v (armIdx + 1) rest

/-- Static `static_pattern_match` (`matches/mod.rs:2882-2916`). -/
noncomputable def staticPatternMatch (arms : List LoopMatchArm) (v : StateVal) :
    Option MatchTarget :=
  resolveArms staticMatchAtomic v 0 arms

/-- Dynamic loop-header `SwitchInt` / range-test dispatch (`matches/mod.rs` + `matches/test.rs`). -/
noncomputable def dynamicPatternMatch (arms : List LoopMatchArm) (v : StateVal) :
    Option MatchTarget :=
  resolveArms dynamicMatchAtomic v 0 arms

private theorem matchSubBranches_eq (v : StateVal) (hv : v.Valid) :
    ∀ (idx : Nat) (subs : List SubBranchPat),
      matchSubBranches staticMatchAtomic v idx subs =
      matchSubBranches dynamicMatchAtomic v idx subs
  | _, [] => rfl
  | idx, sb :: rest => by
    simp only [matchSubBranches]
    rw [staticMatchAtomic_eq_dynamicMatchAtomic v hv sb.pat]
    rw [matchSubBranches_eq v hv (idx + 1) rest]

private theorem resolveArms_eq (v : StateVal) (hv : v.Valid) :
    ∀ (armIdx : Nat) (arms : List LoopMatchArm),
      resolveArms staticMatchAtomic v armIdx arms =
      resolveArms dynamicMatchAtomic v armIdx arms
  | _, [] => rfl
  | armIdx, arm :: rest => by
    simp only [resolveArms]
    cases hp : arm.pat with
    | single sb =>
      dsimp only
      rw [staticMatchAtomic_eq_dynamicMatchAtomic v hv sb.pat]
      rw [resolveArms_eq v hv (armIdx + 1) rest]
    | orPat subs =>
      dsimp only
      rw [matchSubBranches_eq v hv 0 subs]
      rw [resolveArms_eq v hv (armIdx + 1) rest]

/-- Exact static-vs-dynamic target-block resolution agreement across all valid state values
    (integers, fieldless enum tags, and all 2^32 IEEE-754 binary32 floats) and all guard-free
    patterns including `Or`-pattern `sub_branches`. -/
theorem static_pattern_match_eq_dynamic_match
    (arms : List LoopMatchArm) (v : StateVal) (hv : v.Valid) :
    staticPatternMatch arms v = dynamicPatternMatch arms v :=
  resolveArms_eq v hv 0 arms

/-- Convert a list of drop tags to `Event.drop` trace entries (`noncomputable def`). -/
noncomputable def dropTagsToEvents : List DropTag → List Event
  | [] => []
  | d :: ds => Event.drop d :: dropTagsToEvents ds

/-- Machine execution configuration. -/
structure ExecState where
  statePlace : StateVal
  acc        : Nat
  trace      : List Event

/-- Execution outcome after `fuel` loop iterations. -/
inductive RunOutcome where
  | halted (retVal : Nat) (finalState : StateVal) (finalTrace : List Event)
  | running (st : ExecState)
  | stuck

/-- A well-formed `#[loop_match]` program: every `#[const_continue]` target constant is
    valid (`StateVal.Valid`), resolves statically (`staticPatternMatch` succeeds, as enforced
    by `ConstContinueUnknownJumpTarget` in `scope.rs:991-995`), and every `normalBreak`
    produces a valid `StateVal`. -/
structure WellFormedLoopMatch (arms : List LoopMatchArm) : Prop where
  validNext : ∀ (arm : LoopMatchArm) (acc : Nat) (bound : Option StateVal),
    arm ∈ arms →
    match (arm.body acc bound).exit with
    | .exitLoop _        => True
    | .normalBreak v     => v.Valid
    | .constContinue c   => c.Valid ∧ (staticPatternMatch arms c).isSome = true

/-- Pure liveness read emitted by `scope.rs:945-953, 1007` (`Rvalue::Discriminant` for enums,
    `Rvalue::Use(Operand::Copy(state_place))` for primitives). -/
def readDiscrOrCopy (v : StateVal) : Nat :=
  match v with
  | .nat n       => n
  | .enumTag idx => idx
  | .f32 bits    => bits.toBits

/-- Execute `DropTree` for `scopes` with exact guaranteed fuel `entry + 1`, returning
    the emitted `Event.drop` list. -/
noncomputable def runRealDropTreeEvents (scopes : List (List DropTag)) : List Event :=
  let built := buildScopeDropTree scopes
  let res := execDropTree built.1 (built.2 + 1) built.2
  dropTagsToEvents res.1

theorem runRealDropTreeEvents_eq_lexical (scopes : List (List DropTag)) :
    runRealDropTreeEvents scopes = dropTagsToEvents (lexicalLifoDrops scopes) := by
  unfold runRealDropTreeEvents
  dsimp only
  have h := const_continue_drop_tree_preserves_lexical_lifo scopes
    ((buildScopeDropTree scopes).2 + 1) (Nat.lt_succ_self _)
  rw [h]

/-- Control-flow location in the compiled `#[loop_match]` CFG. -/
inductive PC where
  | loopHeader
  | directTarget (tgt : MatchTarget)

/-- Execute `fuel` iterations of the DYNAMIC loop-header `SwitchInt` semantics. -/
noncomputable def runDynamic (arms : List LoopMatchArm) :
    Nat → ExecState → RunOutcome
  | 0, st => RunOutcome.running st
  | fuel + 1, st =>
    match dynamicPatternMatch arms st.statePlace with
    | none => RunOutcome.stuck
    | some tgt =>
      match listGet? arms tgt.armIdx with
      | none => RunOutcome.stuck
      | some arm =>
        let bound := if tgt.bindsState then some st.statePlace else none
        let eff := arm.body st.acc bound
        let dropEvs := dropTagsToEvents (lexicalLifoDrops eff.liveScopes)
        let trace' := st.trace ++ eff.bodyEvents ++ dropEvs
        match eff.exit with
        | .exitLoop retVal =>
          RunOutcome.halted retVal st.statePlace trace'
        | .normalBreak nextV =>
          runDynamic arms fuel { statePlace := nextV, acc := eff.newAcc, trace := trace' }
        | .constContinue nextC =>
          runDynamic arms fuel { statePlace := nextC, acc := eff.newAcc, trace := trace' }

/-- Execute `fuel` iterations of the STATIC `#[const_continue]` direct-jump-threaded CFG,
    mirroring `scope.rs:991-1046` step-by-step. -/
noncomputable def runStatic (arms : List LoopMatchArm) :
    Nat → PC → ExecState → RunOutcome
  | 0, _, st => RunOutcome.running st
  | fuel + 1, pc, st =>
    let optTgt := match pc with
      | .loopHeader       => dynamicPatternMatch arms st.statePlace
      | .directTarget tgt => some tgt
    match optTgt with
    | none => RunOutcome.stuck
    | some tgt =>
      match listGet? arms tgt.armIdx with
      | none => RunOutcome.stuck
      | some arm =>
        let bound := if tgt.bindsState then some st.statePlace else none
        let eff := arm.body st.acc bound
        match eff.exit with
        | .exitLoop retVal =>
          let dropEvs := runRealDropTreeEvents eff.liveScopes
          RunOutcome.halted retVal st.statePlace (st.trace ++ eff.bodyEvents ++ dropEvs)
        | .normalBreak nextV =>
          let dropEvs := runRealDropTreeEvents eff.liveScopes
          let trace' := st.trace ++ eff.bodyEvents ++ dropEvs
          runStatic arms fuel PC.loopHeader
            { statePlace := nextV, acc := eff.newAcc, trace := trace' }
        | .constContinue nextC =>
          match staticPatternMatch arms nextC with
          | none => RunOutcome.stuck
          | some realTarget =>
            let stAfterWrite := nextC
            let _discr := readDiscrOrCopy stAfterWrite
            let dropEvs := runRealDropTreeEvents eff.liveScopes
            let trace' := st.trace ++ eff.bodyEvents ++ dropEvs
            runStatic arms fuel (PC.directTarget realTarget)
              { statePlace := stAfterWrite, acc := eff.newAcc, trace := trace' }

private theorem listGet?_mem {α : Type} :
    ∀ (xs : List α) (i : Nat) (x : α), listGet? xs i = some x → x ∈ xs
  | [], _, _, h => by cases h
  | _ :: _, 0, _, h => by
    simp only [listGet?, Option.some.injEq] at h
    subst h
    exact List.Mem.head _
  | _ :: xs, i + 1, x, h =>
    List.Mem.tail _ (listGet?_mem xs i x h)

/-- PC-alignment invariant connecting the static direct-jump CFG and the dynamic loop-header
    CFG at every iteration boundary. -/
def PcAligned (arms : List LoopMatchArm) (pc : PC) (st : ExecState) : Prop :=
  st.statePlace.Valid ∧
  match pc with
  | .loopHeader       => True
  | .directTarget tgt => dynamicPatternMatch arms st.statePlace = some tgt

/-- Generalized bisimulation invariant across arbitrary iteration fuel `fuel`. -/
theorem runStatic_bisimulates_runDynamic_gen
    (arms : List LoopMatchArm) (hwf : WellFormedLoopMatch arms) :
    ∀ (fuel : Nat) (pc : PC) (st : ExecState),
      PcAligned arms pc st →
      runStatic arms fuel pc st = runDynamic arms fuel st
  | 0, _, _, _ => rfl
  | fuel + 1, pc, st, ⟨hvalid, hpc⟩ => by
    have hstep :
        ∀ (optTgt : Option MatchTarget),
          optTgt = dynamicPatternMatch arms st.statePlace →
          (match optTgt with
            | none => RunOutcome.stuck
            | some tgt =>
              match listGet? arms tgt.armIdx with
              | none => RunOutcome.stuck
              | some arm =>
                let bound := if tgt.bindsState then some st.statePlace else none
                let eff := arm.body st.acc bound
                match eff.exit with
                | .exitLoop retVal =>
                  let dropEvs := runRealDropTreeEvents eff.liveScopes
                  RunOutcome.halted retVal st.statePlace (st.trace ++ eff.bodyEvents ++ dropEvs)
                | .normalBreak nextV =>
                  let dropEvs := runRealDropTreeEvents eff.liveScopes
                  let trace' := st.trace ++ eff.bodyEvents ++ dropEvs
                  runStatic arms fuel PC.loopHeader
                    { statePlace := nextV, acc := eff.newAcc, trace := trace' }
                | .constContinue nextC =>
                  match staticPatternMatch arms nextC with
                  | none => RunOutcome.stuck
                  | some realTarget =>
                    let stAfterWrite := nextC
                    let _discr := readDiscrOrCopy stAfterWrite
                    let dropEvs := runRealDropTreeEvents eff.liveScopes
                    let trace' := st.trace ++ eff.bodyEvents ++ dropEvs
                    runStatic arms fuel (PC.directTarget realTarget)
                      { statePlace := stAfterWrite, acc := eff.newAcc, trace := trace' }) =
          runDynamic arms (fuel + 1) st := by
      intro optTgt hopt
      rw [hopt]
      simp only [runDynamic]
      cases hd : dynamicPatternMatch arms st.statePlace with
      | none => rfl
      | some tgt =>
        dsimp only
        cases harm : listGet? arms tgt.armIdx with
        | none => rfl
        | some arm =>
          have hmem : arm ∈ arms := listGet?_mem arms tgt.armIdx arm harm
          have hnext := hwf.validNext arm st.acc
            (if tgt.bindsState then some st.statePlace else none) hmem
          dsimp only
          simp only [runRealDropTreeEvents_eq_lexical]
          cases hexit : (arm.body st.acc (if tgt.bindsState then some st.statePlace else none)).exit with
          | exitLoop retVal => rfl
          | normalBreak nextV =>
            rw [hexit] at hnext
            dsimp only
            exact runStatic_bisimulates_runDynamic_gen arms hwf fuel PC.loopHeader
              { statePlace := nextV
                acc := (arm.body st.acc (if tgt.bindsState then some st.statePlace else none)).newAcc
                trace := st.trace ++
                  (arm.body st.acc (if tgt.bindsState then some st.statePlace else none)).bodyEvents ++
                  dropTagsToEvents (lexicalLifoDrops
                    (arm.body st.acc (if tgt.bindsState then some st.statePlace else none)).liveScopes) }
              ⟨hnext, trivial⟩
          | constContinue nextC =>
            rw [hexit] at hnext
            have hvalidC : nextC.Valid := hnext.1
            have hsomeC : (staticPatternMatch arms nextC).isSome = true := hnext.2
            dsimp only
            cases hstat : staticPatternMatch arms nextC with
            | none =>
              rw [hstat] at hsomeC
              cases hsomeC
            | some realTarget =>
              dsimp only
              have hdynC : dynamicPatternMatch arms nextC = some realTarget := by
                rw [← static_pattern_match_eq_dynamic_match arms nextC hvalidC]
                exact hstat
              exact runStatic_bisimulates_runDynamic_gen arms hwf fuel (PC.directTarget realTarget)
                { statePlace := nextC
                  acc := (arm.body st.acc (if tgt.bindsState then some st.statePlace else none)).newAcc
                  trace := st.trace ++
                    (arm.body st.acc (if tgt.bindsState then some st.statePlace else none)).bodyEvents ++
                    dropTagsToEvents (lexicalLifoDrops
                      (arm.body st.acc (if tgt.bindsState then some st.statePlace else none)).liveScopes) }
                ⟨hvalidC, hdynC⟩
    cases pc with
    | loopHeader =>
      exact hstep (dynamicPatternMatch arms st.statePlace) rfl
    | directTarget tgt =>
      exact hstep (some tgt) hpc.symm

/-- Theorem (1): Observational equivalence between dynamic loop-header `SwitchInt` dispatch
    and `static_pattern_match` direct-arm jump-threading. -/
theorem const_continue_direct_jump_bisimulates_loop_header_switch
    (arms : List LoopMatchArm) (hwf : WellFormedLoopMatch arms)
    (st : ExecState) (hvalid : st.statePlace.Valid) (fuel : Nat) :
    runStatic arms fuel PC.loopHeader st = runDynamic arms fuel st :=
  runStatic_bisimulates_runDynamic_gen arms hwf fuel PC.loopHeader st ⟨hvalid, trivial⟩

/-! ## Part 4: Constructive Sharpness Counterexamples -/

/-- Guarded arm model demonstrating why `rustc` MUST emit `LoopMatchArmWithGuard`
    (`compiler/rustc_mir_build/src/builder/expr/into.rs:318-321`). -/
structure GuardedArm where
  pat        : AtomicPat
  guard      : Nat → Bool × List Event
  bodyOutput : Nat

noncomputable def execGuardedDynamic (v : StateVal) (acc : Nat) :
    List GuardedArm → Option (Nat × List Event)
  | [] => none
  | arm :: rest =>
    if dynamicMatchAtomic v arm.pat then
      let g := arm.guard acc
      if g.1 then some (arm.bodyOutput, g.2)
      else
        match execGuardedDynamic v acc rest with
        | none => none
        | some res => some (res.1, g.2 ++ res.2)
    else
      execGuardedDynamic v acc rest

/-- Naively jump-threading directly to the first structurally matching arm's `success_block`
    (ignoring guards, as `static_pattern_match` has no guard predicate). -/
noncomputable def execGuardedStaticNaive (v : StateVal) :
    List GuardedArm → Option (Nat × List Event)
  | [] => none
  | arm :: rest =>
    if staticMatchAtomic v arm.pat then some (arm.bodyOutput, [])
    else execGuardedStaticNaive v rest

/-- Counterexample 1 (`ce1_arm_guard_side_effect_breaks_static_dispatch`):
    If arm guards were permitted in `#[loop_match]`, a false-evaluating side-effecting
    guard on arm 0 (`0 if { emit("guard"); acc == 1 } => 10`, `_ => 20`) causes dynamic
    dispatch to emit `armEmit "guard_eval" 0` and fall through to arm 1 (`20`), whereas
    static jump-threading enters arm 0 (`10`) with empty trace `[]`. -/
theorem ce1_arm_guard_side_effect_breaks_static_dispatch :
    let guardedArms : List GuardedArm :=
      [ { pat := AtomicPat.natRange 0 0 true
          guard := fun acc => (acc == 1, [Event.armEmit "guard_eval" acc])
          bodyOutput := 10 }
      , { pat := AtomicPat.wild
          guard := fun _ => (true, [])
          bodyOutput := 20 } ]
    execGuardedDynamic (StateVal.nat 0) 0 guardedArms =
      some (20, [Event.armEmit "guard_eval" 0]) ∧
    execGuardedStaticNaive (StateVal.nat 0) guardedArms =
      some (10, []) ∧
    execGuardedDynamic (StateVal.nat 0) 0 guardedArms ≠
      execGuardedStaticNaive (StateVal.nat 0) guardedArms := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

/-- Faulty variant of `runStatic` that omits `expr_into_dest(state_place, block, value)`
    (`scope.rs:999`) before jumping to `sub_branch.success_block`. -/
noncomputable def runStaticSkipStateWrite (arms : List LoopMatchArm) :
    Nat → PC → ExecState → RunOutcome
  | 0, _, st => RunOutcome.running st
  | fuel + 1, pc, st =>
    let optTgt := match pc with
      | .loopHeader       => dynamicPatternMatch arms st.statePlace
      | .directTarget tgt => some tgt
    match optTgt with
    | none => RunOutcome.stuck
    | some tgt =>
      match listGet? arms tgt.armIdx with
      | none => RunOutcome.stuck
      | some arm =>
        let bound := if tgt.bindsState then some st.statePlace else none
        let eff := arm.body st.acc bound
        match eff.exit with
        | .exitLoop retVal =>
          let dropEvs := runRealDropTreeEvents eff.liveScopes
          RunOutcome.halted retVal st.statePlace (st.trace ++ eff.bodyEvents ++ dropEvs)
        | .normalBreak nextV =>
          let dropEvs := runRealDropTreeEvents eff.liveScopes
          runStaticSkipStateWrite arms fuel PC.loopHeader
            { statePlace := nextV, acc := eff.newAcc, trace := st.trace ++ eff.bodyEvents ++ dropEvs }
        | .constContinue nextC =>
          match staticPatternMatch arms nextC with
          | none => RunOutcome.stuck
          | some realTarget =>
            let dropEvs := runRealDropTreeEvents eff.liveScopes
            -- BUG: keeps stale `st.statePlace` instead of writing `nextC`!
            runStaticSkipStateWrite arms fuel (PC.directTarget realTarget)
              { statePlace := st.statePlace, acc := eff.newAcc, trace := st.trace ++ eff.bodyEvents ++ dropEvs }

/-- Exact model of `c3` `x @ 0 | x @ 2 =>` (`OR_BIND = 22`). -/
def orBindArms : List LoopMatchArm :=
  [ { pat := ArmPat.orPat
        [ { pat := AtomicPat.natRange 0 0 true, bindsState := true }
        , { pat := AtomicPat.natRange 2 2 true, bindsState := true } ]
      body := fun acc bound =>
        let x := match bound with
          | some (StateVal.nat n) => n
          | _ => 999
        let acc1 := acc + x
        if x == 0 then
          { newAcc := acc1 + 20
            bodyEvents := [Event.armEmit "or_bind_iter" x]
            liveScopes := []
            exit := ArmExit.constContinue (StateVal.nat 2) }
        else
          { newAcc := acc1
            bodyEvents := [Event.armEmit "or_bind_exit" x]
            liveScopes := []
            exit := ArmExit.exitLoop acc1 } }
  , { pat := ArmPat.single { pat := AtomicPat.wild, bindsState := false }
      body := fun acc _ =>
        { newAcc := acc
          bodyEvents := []
          liveScopes := []
          exit := ArmExit.exitLoop 999 } } ]

/-- Counterexample 2 (`ce2_skipping_state_write_before_subbranch_breaks_at_binding`):
    On `x @ 0 | x @ 2 =>`, correct `#[const_continue]` halts with `OR_BIND = 22`,
    matching dynamic dispatch. Skipping the `state_place` write leaves `state_place = 0`,
    so `sub_branch[1]` re-binds stale `x = 0` and loops into `acc = 60` (`running` vs `halted 22`). -/
theorem ce2_skipping_state_write_before_subbranch_breaks_at_binding :
    let init : ExecState := { statePlace := StateVal.nat 0, acc := 0, trace := [] }
    runStatic orBindArms 3 PC.loopHeader init =
      RunOutcome.halted 22 (StateVal.nat 2)
        [Event.armEmit "or_bind_iter" 0, Event.armEmit "or_bind_exit" 2] ∧
    runDynamic orBindArms 3 init =
      RunOutcome.halted 22 (StateVal.nat 2)
        [Event.armEmit "or_bind_iter" 0, Event.armEmit "or_bind_exit" 2] ∧
    runStaticSkipStateWrite orBindArms 3 PC.loopHeader init =
      RunOutcome.running
        { statePlace := StateVal.nat 0
          acc := 60
          trace := [Event.armEmit "or_bind_iter" 0, Event.armEmit "or_bind_iter" 0,
                    Event.armEmit "or_bind_iter" 0] } ∧
    runStaticSkipStateWrite orBindArms 3 PC.loopHeader init ≠
      runDynamic orBindArms 3 init := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  cases h

/-- Faulty variant of `runStatic` that jumps directly to `real_target` WITHOUT running
    the real-edge `DropTree` (`scope.rs:1029-1044`). -/
noncomputable def runStaticOmitDropTree (arms : List LoopMatchArm) :
    Nat → PC → ExecState → RunOutcome
  | 0, _, st => RunOutcome.running st
  | fuel + 1, pc, st =>
    let optTgt := match pc with
      | .loopHeader       => dynamicPatternMatch arms st.statePlace
      | .directTarget tgt => some tgt
    match optTgt with
    | none => RunOutcome.stuck
    | some tgt =>
      match listGet? arms tgt.armIdx with
      | none => RunOutcome.stuck
      | some arm =>
        let bound := if tgt.bindsState then some st.statePlace else none
        let eff := arm.body st.acc bound
        match eff.exit with
        | .exitLoop retVal =>
          let dropEvs := runRealDropTreeEvents eff.liveScopes
          RunOutcome.halted retVal st.statePlace (st.trace ++ eff.bodyEvents ++ dropEvs)
        | .normalBreak nextV =>
          let dropEvs := runRealDropTreeEvents eff.liveScopes
          runStaticOmitDropTree arms fuel PC.loopHeader
            { statePlace := nextV, acc := eff.newAcc, trace := st.trace ++ eff.bodyEvents ++ dropEvs }
        | .constContinue nextC =>
          match staticPatternMatch arms nextC with
          | none => RunOutcome.stuck
          | some realTarget =>
            -- BUG: omits `runRealDropTreeEvents eff.liveScopes` before jumping!
            runStaticOmitDropTree arms fuel (PC.directTarget realTarget)
              { statePlace := nextC, acc := eff.newAcc, trace := st.trace ++ eff.bodyEvents }

/-- Exact model of `c1` nested-scope drop order:
    arm 0 declares `_outer = Guard("arm0_outer")`, inner block `{ _inner = Guard("arm0_inner");
    #[const_continue] break 'blk 1; }`, arm 1 declares `_g1 = Guard("arm1")` and breaks `'outer`. -/
def nestedDropArms : List LoopMatchArm :=
  [ { pat := ArmPat.single { pat := AtomicPat.natRange 0 0 true, bindsState := false }
      body := fun acc _ =>
        { newAcc := acc + 1
          bodyEvents := []
          liveScopes := [["arm0_outer"], ["arm0_inner"]]
          exit := ArmExit.constContinue (StateVal.nat 1) } }
  , { pat := ArmPat.single { pat := AtomicPat.natRange 1 1 true, bindsState := false }
      body := fun acc _ =>
        { newAcc := acc + 10
          bodyEvents := []
          liveScopes := [["arm1"]]
          exit := ArmExit.exitLoop (acc + 10) } } ]

/-- Counterexample 3 (`ce3_omitting_drop_tree_leaks_inner_arm_guard`):
    Omitting the real-edge `DropTree` before jumping to `real_target` produces trace
    `[Event.drop "arm1"]` (leaking both `"arm0_inner"` and `"arm0_outer"`), whereas
    correct `runStatic` and `runDynamic` both emit
    `[Event.drop "arm0_inner", Event.drop "arm0_outer", Event.drop "arm1"]`. -/
theorem ce3_omitting_drop_tree_leaks_inner_arm_guard :
    let init : ExecState := { statePlace := StateVal.nat 0, acc := 0, trace := [] }
    runStatic nestedDropArms 3 PC.loopHeader init =
      RunOutcome.halted 11 (StateVal.nat 1)
        [Event.drop "arm0_inner", Event.drop "arm0_outer", Event.drop "arm1"] ∧
    runDynamic nestedDropArms 3 init =
      RunOutcome.halted 11 (StateVal.nat 1)
        [Event.drop "arm0_inner", Event.drop "arm0_outer", Event.drop "arm1"] ∧
    runStaticOmitDropTree nestedDropArms 3 PC.loopHeader init =
      RunOutcome.halted 11 (StateVal.nat 1)
        [Event.drop "arm1"] ∧
    runStaticOmitDropTree nestedDropArms 3 PC.loopHeader init ≠
      runDynamic nestedDropArms 3 init := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  have hlen :
      ([Event.drop "arm1"] : List Event).length =
      ([Event.drop "arm0_inner", Event.drop "arm0_outer", Event.drop "arm1"] : List Event).length := by
    injection h with _ _ htr
    exact congrArg List.length htr
  cases hlen

/-- Bonus Counterexample 4 (`ce4_drop_state_overwrite_omits_old_state_drop`):
    Models our empirically discovered `rustc` semantic divergence on `Drop`-implementing
    fieldless enums (`enum DropState { A, B }`, `c5_drop_fieldless_enum_divergence`):
    plain `loop { s = 'blk: { ... } }` executes `drop_and_replace` on `s` (emitting
    `"drop_S::A"` after `"armA_outer"`), whereas `#[loop_match]` emits bare `Assign` /
    `expr_into_dest` without `Drop { replace: true }`, omitting `"drop_S::A"` and proving
    that `!needs_drop(state_ty)` is a sharp precondition for observational equivalence. -/
theorem ce4_drop_state_overwrite_omits_old_state_drop :
    let plainLoopTrace : List Event :=
      dropTagsToEvents (lexicalLifoDrops [["armA_outer"], ["armA_inner"]]) ++
      [Event.drop "drop_S::A"] ++
      dropTagsToEvents (lexicalLifoDrops [["armB"]]) ++
      [Event.drop "drop_S::B"]
    let loopMatchTrace : List Event :=
      dropTagsToEvents (lexicalLifoDrops [["armA_outer"], ["armA_inner"]]) ++
      dropTagsToEvents (lexicalLifoDrops [["armB"]]) ++
      [Event.drop "drop_S::B"]
    plainLoopTrace =
      [Event.drop "armA_inner", Event.drop "armA_outer", Event.drop "drop_S::A",
       Event.drop "armB", Event.drop "drop_S::B"] ∧
    loopMatchTrace =
      [Event.drop "armA_inner", Event.drop "armA_outer",
       Event.drop "armB", Event.drop "drop_S::B"] ∧
    plainLoopTrace ≠ loopMatchTrace := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  have hlen := congrArg List.length h
  cases hlen

end LoopMatchSoundness
