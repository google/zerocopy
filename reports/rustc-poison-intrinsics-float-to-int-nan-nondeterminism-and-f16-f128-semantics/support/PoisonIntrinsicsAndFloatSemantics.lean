/-!
# Poison-Bearing Intrinsics, `FloatToInt` Open-Interval Truncation, RFC 3514 NaN Nondeterminism, and Fast/Algebraic Float Semantics

Standalone constructive `Lean v4.34.1` mechanization of:
1. Poison-producing integer intrinsics (`disjoint_bitor`, `exact_div`, `unchecked_add`,
   `unchecked_shl`) vs. `#[miri::intrinsic_fallback_is_spec]` `assume` / Miri UB
   equivalence, the bit-level disjoint-OR-equals-addition invariant, and
   `select_unpredictable` drop-count & backend representation (`Immediate` / `Pair` /
   `Ref`) equivalence.
2. Exact rational (`num / (denPred + 1)`) open-interval characterization of
   `float_to_int_unchecked` (`Round::TowardZero`) vs. total saturating `CastKind::FloatToInt`,
   including unsigned `(-1, 0)` acceptance and `i32::MAX as f32` round-to-`2^31` UB.
3. RFC 3514 set-valued `generateNaN` (`{preferredQNaN, quiet(in), rawSNaN(in)} × {+, -}`)
   and `±4 ULP` `fadd_fast` vs. total `fadd_algebraic` (`nnan`/`ninf` omitted).
4. Four constructive counterexample theorems demonstrating unsound specification shortcuts.

Axiom hygiene: pure core Lean 4 (`propext` / `Quot.sound` only — zero `sorry`, zero
`Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial def`).
-/

namespace PoisonIntrinsicsAndFloatSemantics

-- ============================================================================
-- Part I: Poison Lattice, `noundef` Observation, and Integer Intrinsics
-- ============================================================================

/-- Simplified LLVM scalar value model distinguishing concrete values from `poison`. -/
inductive LLVMVal (α : Type) where
  | val (v : α)
  | poison
  deriving DecidableEq, Repr

/-- Operational interpreter outcome distinguishing normal return from immediate UB. -/
inductive UBOutcome (α : Type) where
  | ok (v : α)
  | ub
  deriving DecidableEq, Repr

/-- Evaluating a `noundef`-annotated result turns `poison` into immediate UB. -/
def observeNoundef {α : Type} : LLVMVal α → UBOutcome α
  | .val v => .ok v
  | .poison => .ub

/-- Semantics of `core::intrinsics::assume(cond)` followed by continuation `k`. -/
def evalAssume {α : Type} (cond : Bool) (k : Unit → UBOutcome α) : UBOutcome α :=
  if cond then k () else .ub

-- ----------------------------------------------------------------------------
-- I.A: `disjoint_bitor` vs. LLVM `or disjoint` and bit-level sum equivalence
-- ----------------------------------------------------------------------------

/-- LLVM `or disjoint iN %a, %b`: returns `poison` whenever `(a &&& b) != 0`. -/
def evalDisjointBitOr (w : Nat) (a b : BitVec w) : LLVMVal (BitVec w) :=
  if (a &&& b) == 0#w then .val (a ||| b) else .poison

/-- Rust `core::intrinsics::fallback::DisjointBitOr::disjoint_bitor`:
    `unsafe { super::assume((self & other) == 0) }; self | other`. -/
def evalDisjointBitOrFallback (w : Nat) (a b : BitVec w) : UBOutcome (BitVec w) :=
  evalAssume ((a &&& b) == 0#w) (fun () => .ok (a ||| b))

/-- Exact equivalence between `#[miri::intrinsic_fallback_is_spec]` and `noundef(or disjoint)`. -/
theorem disjointBitOr_fallback_eq_observeNoundef (w : Nat) (a b : BitVec w) :
    observeNoundef (evalDisjointBitOr w a b) = evalDisjointBitOrFallback w a b := by
  unfold evalDisjointBitOr evalDisjointBitOrFallback evalAssume
  cases h : ((a &&& b) == 0#w) <;> rfl

theorem disjointBitOr_fallback_iff_no_poison (w : Nat) (a b : BitVec w) :
    (evalDisjointBitOr w a b ≠ .poison) ↔ (evalDisjointBitOrFallback w a b ≠ .ub) := by
  rw [← disjointBitOr_fallback_eq_observeNoundef]
  cases evalDisjointBitOr w a b <;> simp [observeNoundef]

/-- Little-endian bit-list model to prove `(a & b) == 0 → a + b = a | b` with zero carry. -/
noncomputable def bitAndList : List Bool → List Bool → List Bool
  | x :: xs, y :: ys => (x && y) :: bitAndList xs ys
  | _, _ => []

noncomputable def bitOrList : List Bool → List Bool → List Bool
  | x :: xs, y :: ys => (x || y) :: bitOrList xs ys
  | [], ys => ys
  | xs, [] => xs

noncomputable def allFalse : List Bool → Bool
  | [] => true
  | b :: bs => (!b) && allFalse bs

def fullAdder (x y cin : Bool) : Bool × Bool :=
  let sum := xor (xor x y) cin
  let cout := (x && y) || (cin && (x || y))
  (sum, cout)

noncomputable def addBitsCarry : List Bool → List Bool → Bool → List Bool × Bool
  | [], ys, false => (ys, false)
  | x :: xs, [], false => (x :: xs, false)
  | [], [], true => ([], true)
  | [], y :: ys, true =>
      let (s, c) := fullAdder false y true
      let (rest, cout) := addBitsCarry [] ys c
      (s :: rest, cout)
  | x :: xs, [], true =>
      let (s, c) := fullAdder x false true
      let (rest, cout) := addBitsCarry xs [] c
      (s :: rest, cout)
  | x :: xs, y :: ys, cin =>
      let (s, c) := fullAdder x y cin
      let (rest, cout) := addBitsCarry xs ys c
      (s :: rest, cout)

/-- Constructive structural proof of `(a & b) == 0 → (a | b) == (a + b)` (no carry out). -/
theorem bitList_disjoint_implies_add_eq_or_no_carry :
    ∀ (xs ys : List Bool),
      allFalse (bitAndList xs ys) = true →
      addBitsCarry xs ys false = (bitOrList xs ys, false)
  | [], [], _ => by simp [addBitsCarry, bitOrList]
  | [], _ :: _, _ => by simp [addBitsCarry, bitOrList]
  | _ :: _, [], _ => by simp [addBitsCarry, bitOrList]
  | x :: xs, y :: ys, h => by
      have hand : (!(x && y) && allFalse (bitAndList xs ys)) = true := h
      have hrest : allFalse (bitAndList xs ys) = true := (Bool.and_eq_true_iff.mp hand).2
      have ih := bitList_disjoint_implies_add_eq_or_no_carry xs ys hrest
      cases x <;> cases y
      · simp [addBitsCarry, fullAdder, bitOrList, ih]
      · simp [addBitsCarry, fullAdder, bitOrList, ih]
      · simp [addBitsCarry, fullAdder, bitOrList, ih]
      · cases hand

-- ----------------------------------------------------------------------------
-- I.B: Integer Bounds, `exact_div`, `unchecked_add`, and `unchecked_shl`
-- ----------------------------------------------------------------------------

/-- Signed `w`-bit range `[-(2^(w-1)), 2^(w-1) - 1]` and unsigned `[0, 2^w - 1]`. -/
def intMin (w : Nat) (signed : Bool) : Int :=
  if signed then
    match w with
    | 0 => 0
    | k + 1 => -(Int.ofNat (Nat.pow 2 k))
  else
    0

def intMax (w : Nat) (signed : Bool) : Int :=
  if signed then
    match w with
    | 0 => 0
    | k + 1 => Int.ofNat (Nat.pow 2 k) - 1
  else
    Int.ofNat (Nat.pow 2 w) - 1

def inIntRange (w : Nat) (signed : Bool) (v : Int) : Bool :=
  decide (intMin w signed ≤ v) && decide (v ≤ intMax w signed)

/-- `rustc_const_eval` `BinOp::Rem` semantics (faults on `b = 0` or signed `MIN % -1`). -/
def evalMiriRem (w : Nat) (signed : Bool) (a b : Int) : UBOutcome Int :=
  if b == 0 then .ub
  else if signed && (a == intMin w true) && (b == -1) then .ub
  else .ok (Int.tmod a b)

/-- `rustc_const_eval` `BinOp::Div` semantics (faults on `b = 0` or signed `MIN / -1`). -/
def evalMiriDiv (w : Nat) (signed : Bool) (a b : Int) : UBOutcome Int :=
  if b == 0 then .ub
  else if signed && (a == intMin w true) && (b == -1) then .ub
  else .ok (Int.tdiv a b)

/-- Miri/CTFE `exact_div` (`interpret/intrinsics.rs:928-935`): runs `Rem` first, then checks
    `rem == 0`, then runs `Div`. -/
def evalExactDivMiri (w : Nat) (signed : Bool) (a b : Int) : UBOutcome Int :=
  match evalMiriRem w signed a b with
  | .ub => .ub
  | .ok rem =>
      if rem != 0 then .ub
      else evalMiriDiv w signed a b

/-- LLVM `sdiv exact` / `udiv exact` result under well-typed `iW` inputs. -/
def evalExactDivLLVM (w : Nat) (signed : Bool) (a b : Int) : LLVMVal Int :=
  if b == 0 then .poison
  else if signed && (a == intMin w true) && (b == -1) then .poison
  else if Int.tmod a b != 0 then .poison
  else .val (Int.tdiv a b)

theorem exactDiv_miri_eq_observeNoundef (w : Nat) (signed : Bool) (a b : Int) :
    observeNoundef (evalExactDivLLVM w signed a b) = evalExactDivMiri w signed a b := by
  unfold evalExactDivLLVM evalExactDivMiri evalMiriRem evalMiriDiv
  by_cases hb : (b == 0) = true
  · simp [hb, observeNoundef]
  · have hb' : (b == 0) = false := Bool.eq_false_iff.mpr hb
    by_cases ho : (signed && (a == intMin w true) && (b == -1)) = true
    · simp [hb', ho, observeNoundef]
    · have ho' : (signed && (a == intMin w true) && (b == -1)) = false :=
        Bool.eq_false_iff.mpr ho
      by_cases hr : (Int.tmod a b != 0) = true
      · simp [hb', ho', hr, observeNoundef]
      · have hr' : (Int.tmod a b != 0) = false := Bool.eq_false_iff.mpr hr
        simp [hb', ho', hr', observeNoundef]

theorem exactDiv_miri_iff_no_poison (w : Nat) (signed : Bool) (a b : Int) :
    (evalExactDivLLVM w signed a b ≠ .poison) ↔ (evalExactDivMiri w signed a b ≠ .ub) := by
  rw [← exactDiv_miri_eq_observeNoundef]
  cases evalExactDivLLVM w signed a b <;>
    simp [observeNoundef]

theorem exactSDiv_signedMin_neg1_ub :
    evalExactDivMiri 8 true (-128) (-1) = .ub := by
  decide

/-- LLVM `add nsw` (`signed = true`) / `add nuw` (`signed = false`). -/
def evalUncheckedAddLLVM (w : Nat) (signed : Bool) (a b : Int) : LLVMVal Int :=
  if inIntRange w signed (a + b) then .val (a + b) else .poison

/-- Miri `BinOp::AddUnchecked`. -/
def evalUncheckedAddMiri (w : Nat) (signed : Bool) (a b : Int) : UBOutcome Int :=
  if inIntRange w signed (a + b) then .ok (a + b) else .ub

theorem uncheckedAdd_miri_iff_no_poison (w : Nat) (signed : Bool) (a b : Int) :
    (evalUncheckedAddLLVM w signed a b ≠ .poison) ↔ (evalUncheckedAddMiri w signed a b ≠ .ub) := by
  unfold evalUncheckedAddLLVM evalUncheckedAddMiri
  cases inIntRange w signed (a + b) <;> simp

/-- LLVM `shl` (unmasked `build_shift_expr_rhs(..., is_unchecked = true)`):
    produces `poison` when `shift < 0` or `shift >= w`. -/
def evalUncheckedShlLLVM (w : Nat) (a shift : Int) : LLVMVal Int :=
  if decide (0 ≤ shift) && decide (shift < Int.ofNat w) then
    .val ((a * Int.ofNat (Nat.pow 2 shift.toNat)) % Int.ofNat (Nat.pow 2 w))
  else
    .poison

/-- Miri `BinOp::ShlUnchecked`: checks `rem_euclid(w) == shift`, i.e. `0 ≤ shift < w`. -/
def evalUncheckedShlMiri (w : Nat) (a shift : Int) : UBOutcome Int :=
  if decide (0 ≤ shift) && decide (shift < Int.ofNat w) then
    .ok ((a * Int.ofNat (Nat.pow 2 shift.toNat)) % Int.ofNat (Nat.pow 2 w))
  else
    .ub

/-- Checked wrapping MIR `BinOp::Shl` masks `shift mod w` (total for `w > 0`). -/
def evalCheckedShl (w : Nat) (a shift : Int) : Int :=
  let masked := Int.emod shift (Int.ofNat w)
  (a * Int.ofNat (Nat.pow 2 masked.toNat)) % Int.ofNat (Nat.pow 2 w)

theorem uncheckedShl_miri_iff_no_poison (w : Nat) (a shift : Int) :
    (evalUncheckedShlLLVM w a shift ≠ .poison) ↔ (evalUncheckedShlMiri w a shift ≠ .ub) := by
  unfold evalUncheckedShlLLVM evalUncheckedShlMiri
  cases (decide (0 ≤ shift) && decide (shift < Int.ofNat w)) <;> simp

theorem checkedShl_total_while_uncheckedShl_poisons_at_width :
    evalUncheckedShlLLVM 32 1 32 = .poison ∧ evalCheckedShl 32 1 32 = 1 := by
  decide

-- ----------------------------------------------------------------------------
-- I.C: `select_unpredictable` Drop Semantics & Backend Representation Equivalence
-- ----------------------------------------------------------------------------

/-- Abstract representation of `core::intrinsics::select_unpredictable`:
    calls `forget` on the unselected value, leaving only 1 drop for the returned value. -/
def selectIntrinsicDrops {α : Type} (cond : Bool) (t f : α) : α × Nat :=
  let selected := if cond then t else f
  (selected, 1)

/-- Abstract representation of `core::hint::select_unpredictable`:
    drops the unselected value via `drop_in_place` before returning, yielding 2 drops total. -/
def selectHintDrops {α : Type} (cond : Bool) (t f : α) : α × Nat :=
  let selected := if cond then t else f
  (selected, 2)

/-- Three backend lowering strategies in `compiler/rustc_codegen_llvm/src/intrinsic.rs`:
    `OperandValue::Immediate`, `OperandValue::Pair`, and `OperandValue::Ref` (`memcpy`). -/
def selectImmediate {α : Type} (c : Bool) (a b : α) : α :=
  if c then a else b

def selectPackedPair {α β : Type} (c : Bool) (a b : α × β) : α × β :=
  let p1 : α × β := (a.1, a.2)
  let p2 : α × β := (b.1, b.2)
  let sel := if c then p1 else p2
  (sel.1, sel.2)

def selectRefMemcpy {α : Type} (c : Bool) (memA memB : α) : α :=
  let ptrIsA := c
  if ptrIsA then memA else memB

theorem selectUnpredictable_repr_equiv {α β : Type} (c : Bool) (a b : α × β) :
    selectImmediate c a b = selectPackedPair c a b ∧
      selectPackedPair c a b = selectRefMemcpy c a b := by
  cases c <;> simp [selectImmediate, selectPackedPair, selectRefMemcpy]

-- ============================================================================
-- Part II: Exact Rational `FloatToInt` Open-Interval & Saturating Semantics
-- ============================================================================

/-- Extended floating-point model with exact rationals `num / (denPred + 1)`,
    infinities, and NaNs carrying sign, quiet bit, and payload. -/
inductive ExtFloat where
  | finite (num : Int) (denPred : Nat)
  | inf (pos : Bool)
  | nan (sign : Bool) (quiet : Bool) (payload : Nat)
  deriving DecidableEq, Repr

/-- Target integer interval `[minVal, maxVal]`. -/
structure IntBounds where
  minVal : Int
  maxVal : Int
  deriving DecidableEq, Repr

def u8Bounds : IntBounds := { minVal := 0, maxVal := 255 }
def i32Bounds : IntBounds := { minVal := -2147483648, maxVal := 2147483647 }

/-- Toward-zero truncation of rational `num / (denPred + 1)`. -/
def truncTowardZero (num : Int) (denPred : Nat) : Int :=
  Int.tdiv num (Int.ofNat (denPred + 1))

/-- Operational semantics of `core::intrinsics::float_to_int_unchecked`:
    truncates toward zero first, then checks target integer bounds. -/
def floatToIntUnchecked (b : IntBounds) : ExtFloat → UBOutcome Int
  | .finite num denPred =>
      let q := truncTowardZero num denPred
      if decide (b.minVal ≤ q) && decide (q ≤ b.maxVal) then .ok q else .ub
  | .inf _ => .ub
  | .nan _ _ _ => .ub

/-- Safe `as` cast (`CastKind::FloatToInt` -> `@llvm.fptoui.sat` / `@llvm.fptosi.sat`). -/
def floatToIntSat (b : IntBounds) : ExtFloat → Int
  | .nan _ _ _ => 0
  | .inf true => b.maxVal
  | .inf false => b.minVal
  | .finite num denPred =>
      let q := truncTowardZero num denPred
      if q < b.minVal then b.minVal
      else if b.maxVal < q then b.maxVal
      else q

-- Constructive Nat-div / Int-tdiv helper lemmas (zero `omega`!)
private theorem tdiv_nonneg_of_nonneg (num : Int) (d : Nat) (h : 0 ≤ num) :
    Int.tdiv num (Int.ofNat d) = Int.ofNat (num.natAbs / d) := by
  cases num with
  | ofNat m => rfl
  | negSucc m => exact False.elim (by cases h)

private theorem tdiv_neg_of_neg (num : Int) (d : Nat) (h : num < 0) :
    Int.tdiv num (Int.ofNat d) = - Int.ofNat (num.natAbs / d) := by
  cases num with
  | ofNat m => exact False.elim (Int.lt_irrefl 0 (Int.lt_of_le_of_lt (Int.natCast_nonneg m) h))
  | negSucc m => rfl

private theorem nat_div_le_iff_lt_succ_mul (a b d : Nat) (hd : 0 < d) :
    a / d ≤ b ↔ a < (b + 1) * d := by
  constructor
  · intro h
    have hlt : a / d < b + 1 := Nat.lt_succ_of_le h
    exact (Nat.div_lt_iff_lt_mul hd).mp hlt
  · intro h
    have hlt : a / d < b + 1 := (Nat.div_lt_iff_lt_mul hd).mpr h
    exact Nat.le_of_lt_succ hlt

private theorem ofNat_succ_mul (n d : Nat) :
    Int.ofNat ((n + 1) * d) = (Int.ofNat n + 1) * Int.ofNat d := rfl

private theorem tdiv_upper_iff (num : Int) (denPred : Nat) (maxVal : Int) (hmax : 0 ≤ maxVal) :
    truncTowardZero num denPred ≤ maxVal ↔ num < (maxVal + 1) * Int.ofNat (denPred + 1) := by
  unfold truncTowardZero
  have hd : 0 < denPred + 1 := Nat.succ_pos denPred
  have hmaxN : Int.ofNat maxVal.natAbs = maxVal := Int.ofNat_natAbs_of_nonneg hmax
  have hdPos : (0 : Int) < Int.ofNat (denPred + 1) := Int.ofNat_lt.mpr hd
  by_cases hnum : 0 ≤ num
  · have hq := tdiv_nonneg_of_nonneg num (denPred + 1) hnum
    have hnumN : Int.ofNat num.natAbs = num := Int.ofNat_natAbs_of_nonneg hnum
    rw [hq, ← hmaxN]
    constructor
    · intro hle
      have hleN : num.natAbs / (denPred + 1) ≤ maxVal.natAbs := Int.ofNat_le.mp hle
      have hltN : num.natAbs < (maxVal.natAbs + 1) * (denPred + 1) :=
        (nat_div_le_iff_lt_succ_mul num.natAbs maxVal.natAbs (denPred + 1) hd).mp hleN
      have hltI : Int.ofNat num.natAbs < Int.ofNat ((maxVal.natAbs + 1) * (denPred + 1)) :=
        Int.ofNat_lt.mpr hltN
      rw [hnumN, ofNat_succ_mul] at hltI
      simpa [hmaxN] using hltI
    · intro hlt
      have hltI : Int.ofNat num.natAbs < Int.ofNat ((maxVal.natAbs + 1) * (denPred + 1)) := by
        rw [hnumN, ofNat_succ_mul]
        simpa [hmaxN] using hlt
      have hltN : num.natAbs < (maxVal.natAbs + 1) * (denPred + 1) := Int.ofNat_lt.mp hltI
      have hleN : num.natAbs / (denPred + 1) ≤ maxVal.natAbs :=
        (nat_div_le_iff_lt_succ_mul num.natAbs maxVal.natAbs (denPred + 1) hd).mpr hltN
      exact Int.ofNat_le.mpr hleN
  · have hlt0 : num < 0 := Int.lt_of_not_ge hnum
    have hq := tdiv_neg_of_neg num (denPred + 1) hlt0
    constructor
    · intro _
      have h1 : (0 : Int) < maxVal + 1 :=
        Int.lt_of_lt_of_le (by decide) (Int.add_le_add_right hmax 1)
      have hprod : (0 : Int) < (maxVal + 1) * Int.ofNat (denPred + 1) := Int.mul_pos h1 hdPos
      exact Int.lt_trans hlt0 hprod
    · intro _
      rw [hq]
      have hneg : - Int.ofNat (num.natAbs / (denPred + 1)) ≤ 0 :=
        Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)
      exact Int.le_trans hneg hmax

private theorem tdiv_lower_iff (num : Int) (denPred : Nat) (minVal : Int) (hmin : minVal ≤ 0) :
    minVal ≤ truncTowardZero num denPred ↔ (minVal - 1) * Int.ofNat (denPred + 1) < num := by
  unfold truncTowardZero
  have hd : 0 < denPred + 1 := Nat.succ_pos denPred
  have hdPos : (0 : Int) < Int.ofNat (denPred + 1) := Int.ofNat_lt.mpr hd
  have hnegMin : 0 ≤ -minVal := Int.neg_nonneg_of_nonpos hmin
  have hminN : Int.ofNat (-minVal).natAbs = -minVal := Int.ofNat_natAbs_of_nonneg hnegMin
  have heq : ((-minVal) + 1) * Int.ofNat (denPred + 1) = -((minVal - 1) * Int.ofNat (denPred + 1)) := by
    rw [← Int.neg_mul]
    congr 1
    rw [Int.neg_sub, Int.sub_eq_add_neg, Int.add_comm 1 (-minVal)]
  by_cases hnum : 0 ≤ num
  · have hq := tdiv_nonneg_of_nonneg num (denPred + 1) hnum
    constructor
    · intro _
      have hlt0 : minVal - 1 < 0 := by
        have hstep : minVal - 1 ≤ 0 - 1 := Int.sub_le_sub_right hmin 1
        exact Int.lt_of_le_of_lt hstep (by decide)
      have hprod : (minVal - 1) * Int.ofNat (denPred + 1) < 0 := Int.mul_neg_of_neg_of_pos hlt0 hdPos
      exact Int.lt_of_lt_of_le hprod hnum
    · intro _
      rw [hq]
      exact Int.le_trans hmin (Int.natCast_nonneg _)
  · have hlt0 : num < 0 := Int.lt_of_not_ge hnum
    have hq := tdiv_neg_of_neg num (denPred + 1) hlt0
    have hnegNum : 0 ≤ -num := Int.le_of_lt (Int.neg_pos_of_neg hlt0)
    have hnumN : Int.ofNat (-num).natAbs = -num := Int.ofNat_natAbs_of_nonneg hnegNum
    have habs : (-num).natAbs = num.natAbs := Int.natAbs_neg num
    rw [hq]
    constructor
    · intro hle
      have hle2 : Int.ofNat (num.natAbs / (denPred + 1)) ≤ -minVal :=
        Int.le_of_neg_le_neg (by simpa [Int.neg_neg] using hle)
      rw [← hminN] at hle2
      have hleN : num.natAbs / (denPred + 1) ≤ (-minVal).natAbs := Int.ofNat_le.mp hle2
      have hltN : num.natAbs < ((-minVal).natAbs + 1) * (denPred + 1) :=
        (nat_div_le_iff_lt_succ_mul num.natAbs (-minVal).natAbs (denPred + 1) hd).mp hleN
      have hltI : Int.ofNat num.natAbs < Int.ofNat (((-minVal).natAbs + 1) * (denPred + 1)) :=
        Int.ofNat_lt.mpr hltN
      rw [← habs, hnumN, ofNat_succ_mul, hminN, heq] at hltI
      exact Int.lt_of_neg_lt_neg hltI
    · intro hlt
      have hmul2 : -num < -((minVal - 1) * Int.ofNat (denPred + 1)) := Int.neg_lt_neg hlt
      have hltI : Int.ofNat num.natAbs < Int.ofNat (((-minVal).natAbs + 1) * (denPred + 1)) := by
        rw [← habs, hnumN, ofNat_succ_mul, hminN, heq]
        exact hmul2
      have hltN : num.natAbs < ((-minVal).natAbs + 1) * (denPred + 1) := Int.ofNat_lt.mp hltI
      have hleN : num.natAbs / (denPred + 1) ≤ (-minVal).natAbs :=
        (nat_div_le_iff_lt_succ_mul num.natAbs (-minVal).natAbs (denPred + 1) hd).mpr hltN
      have hle2 : Int.ofNat (num.natAbs / (denPred + 1)) ≤ -minVal := by
        rw [← hminN]
        exact Int.ofNat_le.mpr hleN
      exact Int.le_of_neg_le_neg (by simpa [Int.neg_neg] using hle2)

/-- Theorem 2a: Exact Open-Interval Characterization of `floatToIntUnchecked`.
    For any signed or unsigned integer bounds `[minVal, maxVal]` containing `0`,
    `float_to_int_unchecked(num / d)` is defined iff `(minVal - 1) * d < num < (maxVal + 1) * d`. -/
theorem floatToIntUnchecked_defined_iff_open_interval
    (b : IntBounds) (hmin : b.minVal ≤ 0) (hmax : 0 ≤ b.maxVal)
    (num : Int) (denPred : Nat) :
    floatToIntUnchecked b (.finite num denPred) = .ok (truncTowardZero num denPred) ↔
      (b.minVal - 1) * Int.ofNat (denPred + 1) < num ∧
        num < (b.maxVal + 1) * Int.ofNat (denPred + 1) := by
  unfold floatToIntUnchecked
  by_cases hc : (decide (b.minVal ≤ truncTowardZero num denPred) &&
      decide (truncTowardZero num denPred ≤ b.maxVal)) = true
  · simp only [hc, ↓reduceIte, true_iff]
    have h1 : b.minVal ≤ truncTowardZero num denPred :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
    have h2 : truncTowardZero num denPred ≤ b.maxVal :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hc).2
    exact ⟨(tdiv_lower_iff num denPred b.minVal hmin).mp h1,
           (tdiv_upper_iff num denPred b.maxVal hmax).mp h2⟩
  · have hcf : (decide (b.minVal ≤ truncTowardZero num denPred) &&
        decide (truncTowardZero num denPred ≤ b.maxVal)) = false := Bool.eq_false_iff.mpr hc
    simp only [hcf, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro hbad; cases hbad
    · intro ⟨hl, hu⟩
      have h1 : b.minVal ≤ truncTowardZero num denPred :=
        (tdiv_lower_iff num denPred b.minVal hmin).mpr hl
      have h2 : truncTowardZero num denPred ≤ b.maxVal :=
        (tdiv_upper_iff num denPred b.maxVal hmax).mpr hu
      have htrue : (decide (b.minVal ≤ truncTowardZero num denPred) &&
          decide (truncTowardZero num denPred ≤ b.maxVal)) = true :=
        Bool.and_eq_true_iff.mpr ⟨decide_eq_true h1, decide_eq_true h2⟩
      rw [htrue] at hcf
      cases hcf

/-- Theorem 2b: Every open unit negative rational `-1 < num / d < 0` is DEFINED for unsigned targets
    and evaluates to `0` under `float_to_int_unchecked`. -/
theorem floatToIntUnchecked_unsigned_admits_neg_open_unit_interval
    (b : IntBounds) (hmin : b.minVal = 0) (hmax : 0 ≤ b.maxVal)
    (num : Int) (denPred : Nat)
    (hgt : -(Int.ofNat (denPred + 1)) < num) (hlt : num < 0) :
    floatToIntUnchecked b (.finite num denPred) = .ok 0 := by
  have hle : b.minVal ≤ 0 := by rw [hmin]; exact Int.le_refl 0
  have hd : 0 < denPred + 1 := Nat.succ_pos denPred
  have hltq : truncTowardZero num denPred = 0 := by
    unfold truncTowardZero
    rw [tdiv_neg_of_neg num (denPred + 1) hlt]
    have hneg : 0 ≤ -num := Int.le_of_lt (Int.neg_pos_of_neg hlt)
    have hnumN : Int.ofNat (-num).natAbs = -num := Int.ofNat_natAbs_of_nonneg hneg
    have hltI : Int.ofNat (-num).natAbs < Int.ofNat (denPred + 1) := by
      rw [hnumN]
      exact Int.neg_lt_of_neg_lt hgt
    have hltN : num.natAbs < denPred + 1 := by
      rw [← Int.natAbs_neg num]
      exact Int.ofNat_lt.mp hltI
    have hdiv0 : num.natAbs / (denPred + 1) = 0 := Nat.div_eq_of_lt hltN
    rw [hdiv0]
    rfl
  have hl : (b.minVal - 1) * Int.ofNat (denPred + 1) < num := by
    rw [hmin]
    simpa using hgt
  have hu : num < (b.maxVal + 1) * Int.ofNat (denPred + 1) := by
    have h1 : (0 : Int) < b.maxVal + 1 := Int.lt_of_lt_of_le (by decide) (Int.add_le_add_right hmax 1)
    have h2 : (0 : Int) < Int.ofNat (denPred + 1) := Int.ofNat_lt.mpr hd
    exact Int.lt_trans hlt (Int.mul_pos h1 h2)
  have hdef := (floatToIntUnchecked_defined_iff_open_interval b hle hmax num denPred).mpr ⟨hl, hu⟩
  rw [hltq] at hdef
  exact hdef

private theorem if_neg_local {α : Type} {c : Prop} [Decidable c] (h : ¬c) (a b : α) :
    (if c then a else b) = b := by
  simp [h]

/-- Theorem 2c: Saturating `as` refines `float_to_int_unchecked` whenever the latter is defined,
    while remaining total on `NaN` and `±Inf`. -/
theorem floatToIntSat_refines_floatToIntUnchecked (b : IntBounds) (x : ExtFloat) (v : Int) :
    floatToIntUnchecked b x = .ok v → floatToIntSat b x = v := by
  intro h
  cases x with
  | inf _ => simp [floatToIntUnchecked] at h
  | nan _ _ _ => simp [floatToIntUnchecked] at h
  | finite num denPred =>
      unfold floatToIntUnchecked at h
      by_cases hc : (decide (b.minVal ≤ truncTowardZero num denPred) &&
          decide (truncTowardZero num denPred ≤ b.maxVal)) = true
      · simp only [hc, ↓reduceIte, UBOutcome.ok.injEq] at h
        have h1 : b.minVal ≤ truncTowardZero num denPred :=
          of_decide_eq_true (Bool.and_eq_true_iff.mp hc).1
        have h2 : truncTowardZero num denPred ≤ b.maxVal :=
          of_decide_eq_true (Bool.and_eq_true_iff.mp hc).2
        change (if truncTowardZero num denPred < b.minVal then b.minVal
          else if b.maxVal < truncTowardZero num denPred then b.maxVal
          else truncTowardZero num denPred) = v
        have hn1 : ¬(truncTowardZero num denPred < b.minVal) := Int.not_lt.mpr h1
        have hn2 : ¬(b.maxVal < truncTowardZero num denPred) := Int.not_lt.mpr h2
        rw [if_neg_local hn1, if_neg_local hn2, h]
      · have hcf : (decide (b.minVal ≤ truncTowardZero num denPred) &&
            decide (truncTowardZero num denPred ≤ b.maxVal)) = false := Bool.eq_false_iff.mpr hc
        simp [hcf] at h

/-- Round-to-nearest-even from `[2^30, 2^31]` to IEEE binary32 (ULP = `128 = 2^7`).
    `i32::MAX = 2^31 - 1 = 2147483647` has remainder `127 > 64`, so RNE rounds UP to `2^31`. -/
def roundF32HighRangeRNE (n : Nat) : Nat :=
  let ulp := 128
  let base := (n / ulp) * ulp
  let rem := n % ulp
  if rem > 64 || (rem == 64 && (n / ulp) % 2 == 1) then base + ulp else base

theorem i32_max_as_f32_rounds_to_two_pow_31 :
    roundF32HighRangeRNE 2147483647 = 2147483648 ∧
      roundF32HighRangeRNE 2147483520 = 2147483520 := by
  decide

-- ============================================================================
-- Part III: RFC 3514 `generateNaN` & `fadd_fast` vs. `fadd_algebraic` Refinement
-- ============================================================================

/-- IEEE NaN bit-level model separating sign, quiet bit, and low payload bits. -/
structure NaNVal where
  sign : Bool
  quiet : Bool
  payload : Nat
  deriving DecidableEq, Repr

/-- Valid IEEE NaN must have nonzero mantissa (`quiet = true` or `payload > 0`). -/
def isValidNaN (n : NaNVal) : Bool :=
  n.quiet || decide (n.payload > 0)

def preferredQNaN : NaNVal :=
  { sign := false, quiet := true, payload := 0 }

def quietenNaN (n : NaNVal) : NaNVal :=
  { n with quiet := true }

/-- Mirrors `src/tools/miri/src/operator.rs` `make_signaling`: clears quiet bit only if
    remaining payload keeps the value a NaN (`payload > 0`). -/
def makeSignalingNaN? (n : NaNVal) : Option NaNVal :=
  if decide (n.payload > 0) then some { n with quiet := false } else none

def withBothSigns (n : NaNVal) : List NaNVal :=
  [{ n with sign := false }, { n with sign := true }]

/-- CTFE `Machine::generate_nan`: always returns positive canonical quiet `F2::NAN`. -/
def generateNaN_CTFE (_inputs : List NaNVal) : List NaNVal :=
  [preferredQNaN]

/-- Miri `-Zmiri-deterministic-floats` (`!float_nondet`): identical to CTFE. -/
def generateNaN_MiriDet (_inputs : List NaNVal) : List NaNVal :=
  [preferredQNaN]

/-- Miri default (`float_nondet = true`, RFC 3514): uniform choice over
    `{preferredQNaN} ∪ {quiet(in)} ∪ {rawSNaN(in) | !in.quiet}` with random sign flip. -/
def generateNaN_MiriDefault (inputs : List NaNVal) : List NaNVal :=
  let quieted := inputs.flatMap (fun f => withBothSigns (quietenNaN f))
  let signaling := inputs.flatMap (fun f =>
    if !f.quiet then
      match makeSignalingNaN? f with
      | some s => withBothSigns s
      | none => []
    else [])
  withBothSigns preferredQNaN ++ quieted ++ signaling

theorem generateNaN_ctfe_eq_miriDet (inputs : List NaNVal) :
    generateNaN_CTFE inputs = generateNaN_MiriDet inputs := rfl

theorem generateNaN_miriDet_subset_miriDefault (inputs : List NaNVal) (x : NaNVal) :
    x ∈ generateNaN_MiriDet inputs → x ∈ generateNaN_MiriDefault inputs := by
  intro hx
  simp only [generateNaN_MiriDet, List.mem_singleton] at hx
  subst hx
  simp [generateNaN_MiriDefault, withBothSigns, preferredQNaN]

theorem generateNaN_strict_refinement_zero_div_zero :
    { sign := true, quiet := true, payload := 0 } ∈ generateNaN_MiriDefault [] ∧
      { sign := true, quiet := true, payload := 0 } ∉ generateNaN_MiriDet [] := by
  decide

/-- Representative `f32::from_bits(0x7f80_0001)` (`sNaN` with payload 1). -/
def sNaN1 : NaNVal := { sign := false, quiet := false, payload := 1 }

theorem generateNaN_strict_refinement_snan_six_outputs :
    (generateNaN_MiriDefault [sNaN1]).length = 6 ∧
      ({ sign := false, quiet := false, payload := 1 } : NaNVal) ∈ generateNaN_MiriDefault [sNaN1] ∧
      ({ sign := true, quiet := false, payload := 1 } : NaNVal) ∈ generateNaN_MiriDefault [sNaN1] ∧
      ({ sign := false, quiet := false, payload := 1 } : NaNVal) ∉ generateNaN_MiriDet [sNaN1] := by
  decide

private theorem isValidNaN_withBothSigns (n : NaNVal) (h : isValidNaN n = true) :
    ∀ x ∈ withBothSigns n, isValidNaN x = true := by
  intro x hx
  simp only [withBothSigns, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> exact h

private theorem isValidNaN_flatMap {α : Type} (f : α → List NaNVal) (xs : List α)
    (hf : ∀ a, ∀ x ∈ f a, isValidNaN x = true) :
    ∀ x ∈ xs.flatMap f, isValidNaN x = true := by
  induction xs with
  | nil => intro x hx; cases hx
  | cons a rest ih =>
      intro x hx
      simp only [List.flatMap_cons, List.mem_append] at hx
      rcases hx with hx1 | hx2
      · exact hf a x hx1
      · exact ih x hx2

/-- Every NaN generated by Miri (`generateNaN_MiriDefault`) is a valid NaN (never `±Inf`),
    even if a malformed input had `payload = 0`. -/
theorem generateNaN_miriDefault_all_valid_nan (inputs : List NaNVal) :
    ∀ x ∈ generateNaN_MiriDefault inputs, isValidNaN x = true := by
  intro x hx
  unfold generateNaN_MiriDefault at hx
  simp only [List.mem_append] at hx
  rcases hx with (hx1 | hx2) | hx3
  · exact isValidNaN_withBothSigns preferredQNaN rfl x hx1
  · refine isValidNaN_flatMap _ inputs (fun f y hy => ?_) x hx2
    exact isValidNaN_withBothSigns (quietenNaN f) rfl y hy
  · refine isValidNaN_flatMap _ inputs (fun f y hy => ?_) x hx3
    cases hq : !f.quiet
    · simp [hq] at hy
    · simp only [hq, ↓reduceIte] at hy
      unfold makeSignalingNaN? at hy
      cases hp : decide (f.payload > 0)
      · simp [hp] at hy
      · simp only [hp, ↓reduceIte] at hy
        apply isValidNaN_withBothSigns { f with quiet := false } _ y hy
        simp [isValidNaN, hp]

-- ----------------------------------------------------------------------------
-- III.B: `fadd_fast` (`±4 ULP` + Finite Guard) vs. `fadd_algebraic` (Total)
-- ----------------------------------------------------------------------------

/-- Abstract IEEE-like scalar grid index for finite non-zero / zero / non-finite outcomes. -/
inductive FloatDomain where
  | zero (neg : Bool)
  | finiteNonZero (gridIdx : Int)
  | inf (pos : Bool)
  | nan (val : NaNVal)
  deriving DecidableEq, Repr

def FloatDomain.isFinite : FloatDomain → Bool
  | .zero _ | .finiteNonZero _ => true
  | .inf _ | .nan _ => false

/-- Abstract IEEE binary addition producing either a finite result or overflow/NaN. -/
def abstractFloatAdd (a b : FloatDomain) (overflowPos overflowNeg : Bool) : FloatDomain :=
  match a, b with
  | .nan n, _ => .nan n
  | _, .nan n => .nan n
  | .inf true, .inf false | .inf false, .inf true => .nan preferredQNaN
  | .inf p, _ | _, .inf p => .inf p
  | .zero s1, .zero s2 => .zero (s1 && s2)
  | .zero _, y => y
  | x, .zero _ => x
  | .finiteNonZero i, .finiteNonZero j =>
      if overflowPos then .inf true
      else if overflowNeg then .inf false
      else .finiteNonZero (i + j)

/-- Exact discrete `[-4, +4]` ULP envelope modeling `apply_random_float_error_ulp(..., 4)`. -/
def ulpOffsets4 : List Int := [-4, -3, -2, -1, 0, 1, 2, 3, 4]

def applyMiriUlp4 (deterministic : Bool) : FloatDomain → List FloatDomain
  | .finiteNonZero idx =>
      if deterministic then [.finiteNonZero idx]
      else ulpOffsets4.map (fun d => .finiteNonZero (idx + d))
  | other => [other]

inductive FloatEvalMode where
  | ctfe
  | miriDeterministic
  | miriDefault
  deriving DecidableEq, Repr

/-- Operational model of `core::intrinsics::fadd_fast`:
    immediate UB if either input is non-finite OR the computed result is non-finite. -/
def evalFloatFast (mode : FloatEvalMode) (a b : FloatDomain)
    (overflowPos overflowNeg : Bool) : UBOutcome (List FloatDomain) :=
  if !a.isFinite || !b.isFinite then .ub
  else
    let res := abstractFloatAdd a b overflowPos overflowNeg
    if !res.isFinite then .ub
    else
      let det := match mode with | .miriDefault => false | _ => true
      .ok (applyMiriUlp4 det res)

/-- Operational model of `core::intrinsics::fadd_algebraic` (`reassoc nsz arcp contract`,
    strictly omitting `nnan` and `ninf`): never UB, defined on `NaN`, `±Inf`, and overflow. -/
def evalFloatAlgebraic (mode : FloatEvalMode) (a b : FloatDomain)
    (overflowPos overflowNeg : Bool) : UBOutcome (List FloatDomain) :=
  let res := abstractFloatAdd a b overflowPos overflowNeg
  match res with
  | .nan _ =>
      let nanIns := match a, b with
        | .nan n1, .nan n2 => [n1, n2]
        | .nan n1, _ => [n1]
        | _, .nan n2 => [n2]
        | _, _ => []
      match mode with
      | .miriDefault => .ok ((generateNaN_MiriDefault nanIns).map FloatDomain.nan)
      | _ => .ok [FloatDomain.nan preferredQNaN]
  | _ =>
      let det := match mode with | .miriDefault => false | _ => true
      .ok (applyMiriUlp4 det res)

/-- Hypothetical unsound `fadd_algebraic` if `ninf` were added: finite overflow turns to poison/UB! -/
def evalFloatAlgebraicWithNinf (mode : FloatEvalMode) (a b : FloatDomain)
    (overflowPos overflowNeg : Bool) : UBOutcome (List FloatDomain) :=
  match evalFloatAlgebraic mode a b overflowPos overflowNeg with
  | .ub => .ub
  | .ok xs =>
      if xs.any (fun v => match v with | .inf _ => true | _ => false) then .ub else .ok xs

theorem evalFloatFast_refinement_chain (a b : FloatDomain) (op on : Bool) :
    (∀ v, evalFloatFast .ctfe a b op on = .ok [v] →
      evalFloatFast .miriDeterministic a b op on = .ok [v]) ∧
    (∀ xs, evalFloatFast .miriDeterministic a b op on = .ok xs →
      ∃ ys, evalFloatFast .miriDefault a b op on = .ok ys ∧ ∀ x ∈ xs, x ∈ ys) := by
  constructor
  · intro v h
    unfold evalFloatFast at h ⊢
    exact h
  · intro xs h
    unfold evalFloatFast at h ⊢
    by_cases hfin : (!a.isFinite || !b.isFinite) = true
    · simp [hfin] at h
    · have hfin' : (!a.isFinite || !b.isFinite) = false := Bool.eq_false_iff.mpr hfin
      simp only [hfin', Bool.false_eq_true, ↓reduceIte] at h ⊢
      let res := abstractFloatAdd a b op on
      by_cases hres : (!res.isFinite) = true
      · simp [res, hres] at h
      · have hres' : (!res.isFinite) = false := Bool.eq_false_iff.mpr hres
        simp only [res, hres', Bool.false_eq_true, ↓reduceIte, UBOutcome.ok.injEq] at h ⊢
        subst h
        refine ⟨applyMiriUlp4 false (abstractFloatAdd a b op on), rfl, ?_⟩
        intro x hx
        revert hx
        cases abstractFloatAdd a b op on <;> intro hx
        · simpa [applyMiriUlp4] using hx
        · simp only [applyMiriUlp4, ↓reduceIte, List.mem_singleton] at hx
          subst hx
          simp [applyMiriUlp4, ulpOffsets4]
        · simpa [applyMiriUlp4] using hx
        · simpa [applyMiriUlp4] using hx

theorem evalFloatFast_nondet_has_nine_ulps (idx1 idx2 : Int) :
    ∃ ys, evalFloatFast .miriDefault (.finiteNonZero idx1) (.finiteNonZero idx2) false false = .ok ys ∧
      ys.length = 9 := by
  refine ⟨ulpOffsets4.map (fun d => .finiteNonZero ((idx1 + idx2) + d)), rfl, rfl⟩

theorem evalFloatAlgebraic_total_and_safe_on_nonfinite (mode : FloatEvalMode)
    (a b : FloatDomain) (op on : Bool) :
    evalFloatAlgebraic mode a b op on ≠ .ub := by
  unfold evalFloatAlgebraic
  cases abstractFloatAdd a b op on <;> cases mode <;> simp

-- ============================================================================
-- Part IV: Four Constructive Counterexample Theorems
-- ============================================================================

/-- Counterexample 1: Requiring a closed `[0, 255]` float precondition for `u8` falsely
    rejects `-0.9999` (`-9999 / 10000`), which truncates toward zero to `0_u8` and is UB-free. -/
theorem ce1_closed_interval_precondition_falsely_rejects_defined_neg_fraction_u8 :
    let x := ExtFloat.finite (-9999) 9999
    let closedIntervalAdmits := decide ((0 : Int) * 10000 ≤ (-9999 : Int))
    closedIntervalAdmits = false ∧ floatToIntUnchecked u8Bounds x = .ok 0 := by
  decide

/-- Counterexample 2: `i32::MAX` (`2147483647`) cast to `f32` rounds to `2^31 = 2147483648`,
    causing immediate UB in `float_to_int_unchecked::<f32, i32>`, whereas `0x4eff_ffff` (`2147483520`) succeeds. -/
theorem ce2_i32_max_round_to_f32_overflows_float_to_int_unchecked :
    let rounded := roundF32HighRangeRNE 2147483647
    floatToIntUnchecked i32Bounds (.finite (Int.ofNat rounded) 0) = .ub ∧
      floatToIntUnchecked i32Bounds (.finite (Int.ofNat (roundF32HighRangeRNE 2147483520)) 0) =
        .ok 2147483520 := by
  decide

/-- Counterexample 3: Adding LLVM `ninf` to `fadd_algebraic` turns valid finite overflow
    `fadd_algebraic(f32::MAX, f32::MAX) -> +inf` from defined to unsound UB. -/
theorem ce3_adding_ninf_to_fadd_algebraic_introduces_unsound_overflow_poison :
    let f32Max := FloatDomain.finiteNonZero 2139095039
    evalFloatAlgebraic .miriDefault f32Max f32Max true false = .ok [.inf true] ∧
      evalFloatAlgebraicWithNinf .miriDefault f32Max f32Max true false = .ub := by
  decide

/-- Counterexample 4: `core::intrinsics::select_unpredictable` calls `forget` (`1` drop) whereas
    `core::hint::select_unpredictable` drops the unselected argument (`2` drops), refuting
    drop-count equivalence. -/
theorem ce4_intrinsic_vs_hint_select_unpredictable_drop_count_divergence :
    (selectIntrinsicDrops true 10 20).1 = (selectHintDrops true 10 20).1 ∧
      (selectIntrinsicDrops true 10 20).2 ≠ (selectHintDrops true 10 20).2 := by
  decide

-- Axiom footprints of core theorems
#print axioms disjointBitOr_fallback_eq_observeNoundef
#print axioms disjointBitOr_fallback_iff_no_poison
#print axioms bitList_disjoint_implies_add_eq_or_no_carry
#print axioms exactDiv_miri_eq_observeNoundef
#print axioms exactDiv_miri_iff_no_poison
#print axioms exactSDiv_signedMin_neg1_ub
#print axioms uncheckedAdd_miri_iff_no_poison
#print axioms uncheckedShl_miri_iff_no_poison
#print axioms checkedShl_total_while_uncheckedShl_poisons_at_width
#print axioms selectUnpredictable_repr_equiv
#print axioms floatToIntUnchecked_defined_iff_open_interval
#print axioms floatToIntUnchecked_unsigned_admits_neg_open_unit_interval
#print axioms floatToIntSat_refines_floatToIntUnchecked
#print axioms i32_max_as_f32_rounds_to_two_pow_31
#print axioms generateNaN_ctfe_eq_miriDet
#print axioms generateNaN_miriDet_subset_miriDefault
#print axioms generateNaN_strict_refinement_zero_div_zero
#print axioms generateNaN_strict_refinement_snan_six_outputs
#print axioms generateNaN_miriDefault_all_valid_nan
#print axioms evalFloatFast_refinement_chain
#print axioms evalFloatFast_nondet_has_nine_ulps
#print axioms evalFloatAlgebraic_total_and_safe_on_nonfinite
#print axioms ce1_closed_interval_precondition_falsely_rejects_defined_neg_fraction_u8
#print axioms ce2_i32_max_round_to_f32_overflows_float_to_int_unchecked
#print axioms ce3_adding_ninf_to_fadd_algebraic_introduces_unsound_overflow_poison
#print axioms ce4_intrinsic_vs_hint_select_unpredictable_drop_count_divergence

end PoisonIntrinsicsAndFloatSemantics
