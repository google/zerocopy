import Toy.WrapNiche.Imported.Results

/-!
# Wrapping intervals of a niche field

A niche field is modelled as `Fin M`: its `M` possible values (for a `w`-bit integer field,
`M = 2 ^ w`; no result below needs `M` to be a power of two). All arithmetic on field values
is wrapping arithmetic modulo `M`, written out explicitly with `Nat` floor modulo (`%`) and
truncated subtraction; every truncated subtraction below has its arguments ordered so that it
does not truncate (each is of the form `M - j` with `j ≤ M`, or is guarded where noted).

* `WrapInterval M` is a pair `[s, e]`. Its membership `WrapInterval.Mem` is defined
  semantically, by cases: if `s ≤ e` it is `s..=e`; if `s > e` it is `s..=M-1` followed by
  `0..=e`. Every wrapping interval is non-empty (it contains `s`), and the full field is
  represented by every `[s, s - 1]` (for example `[0, M - 1]`).
* `offset s x` is the wrapping distance `(x - s) mod M`.
* A validity set is `V : Fin M → Bool` (`true` = valid). Its interval hull is described by the
  predicate `IsHull V H`: `H` is a wrapping interval containing every valid value, of the least
  size among such intervals.
-/

namespace Toy.WrapNiche

/-- A value of `Fin M` exists only when `0 < M`. -/
theorem pos_of_fin {M : Nat} (x : Fin M) : 0 < M :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) x.isLt

/-- Wrapping addition of a natural number: `(x + j) mod M` (floor modulo). -/
def wrapAdd {M : Nat} (x : Fin M) (j : Nat) : Fin M :=
  ⟨(x.val + j) % M, Nat.mod_lt _ (pos_of_fin x)⟩

/-- Wrapping subtraction of a natural number: `(x - j) mod M`, computed as
`(x + (M - j % M)) % M` (the inner truncated subtraction never truncates since `j % M < M`). -/
def wrapSub {M : Nat} (x : Fin M) (j : Nat) : Fin M :=
  ⟨(x.val + (M - j % M)) % M, Nat.mod_lt _ (pos_of_fin x)⟩

/-- The wrapping offset of `x` from `s`: `(x - s) mod M`, computed as `(x + (M - s)) % M`
(the truncated subtraction `M - s` never truncates since `s < M`). Always `< M`. This is the
single modular subtraction a niche decoder performs. -/
def offset {M : Nat} (s x : Fin M) : Nat := (x.val + (M - s.val)) % M

/-- A wrapping interval `[s, e]` of field values. -/
structure WrapInterval (M : Nat) where
  /-- First value. -/
  s : Fin M
  /-- Last value. -/
  e : Fin M
deriving DecidableEq, Repr

namespace WrapInterval

variable {M : Nat}

/-- Semantic membership: `s..=e` if `s ≤ e`, otherwise `s..=M-1` followed by `0..=e`. This
is the reading of a wrapping range documented for rustc's `WrappingRange`. -/
def Mem (I : WrapInterval M) (x : Fin M) : Prop :=
  if I.s ≤ I.e then I.s ≤ x ∧ x ≤ I.e else I.s ≤ x ∨ x ≤ I.e

instance (I : WrapInterval M) (x : Fin M) : Decidable (I.Mem x) := by
  unfold Mem; infer_instance

/-- The number of values in the interval, `((e - s) mod M) + 1`, a number in `[1, M]`. -/
def size (I : WrapInterval M) : Nat := offset I.s I.e + 1

/-- The interval `[e + 1, s - 1]` (wrapping). For a non-full interval it is the complement. -/
def compl (I : WrapInterval M) : WrapInterval M := ⟨wrapAdd I.e 1, wrapSub I.s 1⟩

end WrapInterval

/-! ## Range tests -/

/-- The single-subtraction range test: `(x - s) mod M ≤ (e - s) mod M`. -/
def subTest {M : Nat} (I : WrapInterval M) (x : Fin M) : Prop :=
  offset I.s x ≤ offset I.s I.e

/-- A comparison range test with a fixed origin `o`: compare the offsets of `s`, `x`, `e`
from `o` as plain numbers. Origin `0` is the unsigned test `s ≤ x ≤ e`
(`unsignedTest_iff_originTest_zero`); for `M = 256`, origin `128` is the signed test on the
`i8` readings (`signedTestI8_iff_originTest_128`). -/
def originTest {M : Nat} (o : Fin M) (I : WrapInterval M) (x : Fin M) : Prop :=
  offset o I.s ≤ offset o x ∧ offset o x ≤ offset o I.e

/-- A two-branch comparison test with a fixed origin `o`: if `I` does not wrap past `o`
(`offset o s ≤ offset o e`) it is `originTest o`; otherwise it is the disjunction
`offset o s ≤ offset o x ∨ offset o x ≤ offset o e`. At origin `0` the two branches are the two
cases of the definition of `WrapInterval.Mem`. -/
def twoBranchTest {M : Nat} (o : Fin M) (I : WrapInterval M) (x : Fin M) : Prop :=
  if offset o I.s ≤ offset o I.e then originTest o I x
  else offset o I.s ≤ offset o x ∨ offset o x ≤ offset o I.e

/-- The unsigned comparison test `s ≤ x ≤ e`. -/
def unsignedTest {M : Nat} (I : WrapInterval M) (x : Fin M) : Prop :=
  I.s ≤ x ∧ x ≤ I.e

/-- Two's-complement reading of an 8-bit field value. -/
def toI8 (x : Fin 256) : Int := if x.val < 128 then (x.val : Int) else (x.val : Int) - 256

/-- The signed comparison test on `i8` readings: `toI8 s ≤ toI8 x ≤ toI8 e`. -/
def signedTestI8 (I : WrapInterval 256) (x : Fin 256) : Prop :=
  toI8 I.s ≤ toI8 x ∧ toI8 x ≤ toI8 I.e

instance {M : Nat} (I : WrapInterval M) (x : Fin M) : Decidable (subTest I x) := by
  unfold subTest; infer_instance
instance {M : Nat} (o : Fin M) (I : WrapInterval M) (x : Fin M) :
    Decidable (originTest o I x) := by
  unfold originTest; infer_instance
instance {M : Nat} (o : Fin M) (I : WrapInterval M) (x : Fin M) :
    Decidable (twoBranchTest o I x) := by
  unfold twoBranchTest; infer_instance
instance {M : Nat} (I : WrapInterval M) (x : Fin M) : Decidable (unsignedTest I x) := by
  unfold unsignedTest; infer_instance
instance (I : WrapInterval 256) (x : Fin 256) : Decidable (signedTestI8 I x) := by
  unfold signedTestI8; infer_instance

/-- A test `T` is *exact* for the interval `I` if it agrees with membership on every value. -/
def ExactFor {M : Nat} (T : WrapInterval M → Fin M → Prop) (I : WrapInterval M) : Prop :=
  ∀ x, I.Mem x ↔ T I x

/-! ## Validity sets and interval hulls -/

/-- The interval `I` contains every valid value of `V`. -/
def Covers {M : Nat} (I : WrapInterval M) (V : Fin M → Bool) : Prop :=
  ∀ x, V x = true → I.Mem x

/-- `H` is an interval hull of `V`: it covers `V` and no covering interval is smaller.
(Several intervals of the least size may exist; all statements quantify over any of them. For
the empty validity set every singleton `[s, s]` is a hull.) -/
def IsHull {M : Nat} (V : Fin M → Bool) (H : WrapInterval M) : Prop :=
  Covers H V ∧ ∀ J : WrapInterval M, Covers J V → H.size ≤ J.size

/-- `V` is exactly the set of members of some wrapping interval. (Every wrapping interval is
non-empty, so the empty validity set is not an interval set.) -/
def IsWrapIntervalSet {M : Nat} (V : Fin M → Bool) : Prop :=
  ∃ I : WrapInterval M, ∀ x, I.Mem x ↔ V x = true

/-- The validity set whose valid values are exactly the members of `I`. -/
def intervalV {M : Nat} (I : WrapInterval M) : Fin M → Bool := fun x => decide (I.Mem x)

/-- The number of invalid values (niches) of `V`. For `M = 256 ^ n` this is the imported
`numInvalid` (`nichesCount_eq_numInvalid`). -/
def nichesCount {M : Nat} (V : Fin M → Bool) : Nat :=
  ((List.finRange M).filter (fun p => !V p)).length

instance decForallWrapInterval {M : Nat} (P : WrapInterval M → Prop) [DecidablePred P] :
    Decidable (∀ J : WrapInterval M, P J) :=
  decidable_of_iff (∀ s e : Fin M, P ⟨s, e⟩)
    ⟨fun h J => h J.s J.e, fun h s e => h ⟨s, e⟩⟩

instance decExistsWrapInterval {M : Nat} (P : WrapInterval M → Prop) [DecidablePred P] :
    Decidable (∃ J : WrapInterval M, P J) :=
  decidable_of_iff (∃ s e : Fin M, P ⟨s, e⟩)
    ⟨fun ⟨s, e, h⟩ => ⟨⟨s, e⟩, h⟩, fun ⟨J, h⟩ => ⟨J.s, J.e, h⟩⟩

instance {M : Nat} (I : WrapInterval M) (V : Fin M → Bool) : Decidable (Covers I V) := by
  unfold Covers; infer_instance
instance {M : Nat} (V : Fin M → Bool) (H : WrapInterval M) : Decidable (IsHull V H) := by
  unfold IsHull; infer_instance
instance {M : Nat} (V : Fin M → Bool) : Decidable (IsWrapIntervalSet V) := by
  unfold IsWrapIntervalSet; infer_instance
instance {M : Nat} (T : WrapInterval M → Fin M → Prop) [∀ I x, Decidable (T I x)]
    (I : WrapInterval M) : Decidable (ExactFor T I) := by
  unfold ExactFor; infer_instance

/-! ## Fully proved bridge lemmas -/

/-- The package's niche count is the imported `numInvalid` at `M = 256 ^ n`. -/
theorem nichesCount_eq_numInvalid {n : Nat} (V : Imported.Validity n) :
    nichesCount (M := 256 ^ n) V = Imported.numInvalid V := rfl

/-- The offset of a value from itself is `0`. -/
theorem offset_self {M : Nat} (s : Fin M) : offset s s = 0 := by
  unfold offset
  have h := s.isLt
  rw [show s.val + (M - s.val) = M by omega, Nat.mod_self]

/-- The single-subtraction test is the fixed-origin test whose origin is the interval's own
start `s`. -/
theorem subTest_iff_originTest_start {M : Nat} (I : WrapInterval M) (x : Fin M) :
    subTest I x ↔ originTest I.s I x := by
  unfold subTest originTest
  rw [offset_self]
  exact ⟨fun h => ⟨Nat.zero_le _, h⟩, fun h => h.2⟩

/-- `offset 0 x` is `x` itself. -/
theorem offset_zero {M : Nat} (x : Fin M) :
    offset ⟨0, pos_of_fin x⟩ x = x.val := by
  unfold offset
  simp only [Nat.sub_zero, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt x.isLt

/-- The unsigned test is the fixed-origin test at origin `0`. -/
theorem unsignedTest_iff_originTest_zero {M : Nat} (I : WrapInterval M) (x : Fin M) :
    unsignedTest I x ↔ originTest ⟨0, pos_of_fin x⟩ I x := by
  unfold unsignedTest originTest
  have h1 : offset ⟨0, pos_of_fin x⟩ I.s = I.s.val := offset_zero I.s
  have h2 : offset ⟨0, pos_of_fin x⟩ I.e = I.e.val := offset_zero I.e
  rw [h1, h2, offset_zero x]
  exact Iff.rfl

/-- The `i8` signed test is the fixed-origin test at origin `128` (for `M = 256`). -/
theorem signedTestI8_iff_originTest_128 (I : WrapInterval 256) (x : Fin 256) :
    signedTestI8 I x ↔ originTest 128 I x := by
  have key : ∀ y : Fin 256, toI8 y + 128 = ((offset 128 y : Nat) : Int) := by
    intro y
    have hy := y.isLt
    unfold toI8 offset
    show _ = (((y.val + (256 - 128)) % 256 : Nat) : Int)
    by_cases h : y.val < 128
    · simp only [h, ↓reduceIte]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [h, ↓reduceIte]
      have : (y.val + (256 - 128)) % 256 = y.val - 128 := by omega
      rw [this]; omega
  unfold signedTestI8 originTest
  have hs := key I.s
  have hx := key x
  have he := key I.e
  omega

end Toy.WrapNiche
