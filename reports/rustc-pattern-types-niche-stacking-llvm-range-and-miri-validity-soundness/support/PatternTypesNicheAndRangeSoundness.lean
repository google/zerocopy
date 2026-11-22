/-!
# Soundness of `rustc` Pattern Types, Iterative `Option` Niche Stacking,
  LLVM `range` Dead-Branch Elimination, and `CheckEnums` vs. Miri Validity

Kernel-checked constructive Lean 4 formalization (`Lean v4.34.1`, zero external
dependencies, zero `sorry`, zero `Classical.choice`, zero `omega`, zero
`bv_decide`, zero `native_decide`, zero `partial def`, zero `._unsafe_rec`).

## Scope & Modeling Boundary
This module formalizes an abstract specification of:
1. `rustc_abi::WrappingRange` over `w`-bit unsigned bit patterns (`BitVec w`),
   matching `compiler/rustc_abi/src/wrapping_range.rs` (`contains`) and
   `compiler/rustc_abi/src/lib.rs` (`Niche::available`, `Niche::reserve`).
2. Iterative `Option` niche-allocation algebra (`nestOption`, `nestOptionIter`)
   showing `k`-nested `Option` fits inside a single `w`-bit scalar slot
   whenever `k ≤ 2^w - |valid(r)|`, with pairwise-disjoint tags and injective
   encoding/decoding, plus a constructive pigeonhole proof that `k > 2^w - |valid(r)|`
   forces tag expansion beyond `w` bits.
3. Equivalence between Rust's inclusive modular `WrappingRange` and LLVM's
   half-open `range(iW lo, hi)` attribute (for non-full ranges), soundness of
   dead-branch elimination under the `TyKind::Pat` validity invariant, and the
   asymmetry between widening (`Pat(B, r) → B`, unconditionally valid) and
   narrowing (`B → Pat(B, r)`, requiring a range check).
4. The validity-enforcement cliff between MIR's `CheckEnums` pass
   (`compiler/rustc_mir_transform/src/check_enums.rs`) and Miri's
   `ValidityVisitor` (`compiler/rustc_const_eval/src/interpret/validity.rs`),
   with three constructive counterexamples.
-/

namespace PatternTypesSoundness

/-! ## Section 1: Elementary Constructive `Nat` Arithmetic Helpers (No `omega`) -/

/-- Modulus `2^w` for bit-width `w`. -/
def modulus (w : Nat) : Nat := 2 ^ w

theorem modulus_pos (w : Nat) : 0 < modulus w := by
  unfold modulus
  induction w with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    rw [Nat.pow_succ]
    exact Nat.mul_pos ih (Nat.succ_pos 1)

theorem modulus_ge_two {w : Nat} (hw : 1 ≤ w) : 2 ≤ modulus w := by
  cases w with
  | zero => cases hw
  | succ k =>
    unfold modulus
    rw [Nat.pow_succ]
    have h1 : 1 ≤ 2 ^ k := modulus_pos k
    have h2 : 1 * 2 ≤ 2 ^ k * 2 := Nat.mul_le_mul_right 2 h1
    simpa [Nat.one_mul] using h2

private theorem sub_add_one_lt_of_lt {a b m : Nat} (hb : b < m) :
    b - a + 1 ≤ m :=
  Nat.le_trans (Nat.add_le_add_right (Nat.sub_le b a) 1) hb

private theorem eq_of_sub_eq_sub {a b c : Nat} (ha : c ≤ a) (hb : c ≤ b)
    (heq : a - c = b - c) : a = b := by
  have h1 := congrArg (· + c) heq
  simpa [Nat.sub_add_cancel ha, Nat.sub_add_cancel hb] using h1

private theorem sub_lt_sub_right_of_lt {a b c : Nat} (hab : a < b) (hcb : c ≤ a) :
    a - c < b - c := by
  have h1 : a - c + c = a := Nat.sub_add_cancel hcb
  have h2 : b - c + c = b := Nat.sub_add_cancel (Nat.le_trans hcb (Nat.le_of_lt hab))
  rw [← h1, ← h2] at hab
  exact Nat.lt_of_add_lt_add_right hab

/-! ## Section 2: `WrappingRange` Validity Algebra over `BitVec w` -/

/-- Inclusive modular validity range `[start, end]` over `0 .. 2^w - 1`.
Matches `rustc_abi::WrappingRange` (`compiler/rustc_abi/src/wrapping_range.rs:19-22`).
When `start ≤ end`, valid values are `start ≤ v ≤ end`.
When `end < start`, valid values wrap around `2^w`: `start ≤ v < 2^w` or `v ≤ end`. -/
structure WrappingRange where
  start : Nat
  «end» : Nat
  deriving DecidableEq, Repr

namespace WrappingRange

/-- Well-formedness of a `WrappingRange` for bit-width `w ≥ 1`. -/
def wf (w : Nat) (r : WrappingRange) : Prop :=
  1 ≤ w ∧ r.start < modulus w ∧ r.end < modulus w

/-- Inclusive modular membership predicate, matching
`compiler/rustc_abi/src/wrapping_range.rs:57-63`. -/
def contains (r : WrappingRange) (v : Nat) : Bool :=
  if r.start ≤ r.end then
    decide (r.start ≤ v) && decide (v ≤ r.end)
  else
    decide (r.start ≤ v) || decide (v ≤ r.end)

/-- Bit-vector validity predicate over `BitVec w`. -/
def containsBV {w : Nat} (r : WrappingRange) (v : BitVec w) : Bool :=
  r.contains v.toNat

/-- Full validity range `0 ..= (2^w - 1)` of an unconstrained `w`-bit scalar. -/
def full (w : Nat) : WrappingRange :=
  { start := 0, «end» := modulus w - 1 }

/-- Number of valid bit patterns contained in `r` modulo `2^w`. -/
def validCount (w : Nat) (r : WrappingRange) : Nat :=
  if r.start ≤ r.end then
    r.end - r.start + 1
  else
    (modulus w - r.start) + (r.end + 1)

/-- Number of invalid (niche) bit patterns outside `r` modulo `2^w`, matching
`Niche::available` (`compiler/rustc_abi/src/lib.rs:2128-2137`). -/
def availableNiches (w : Nat) (r : WrappingRange) : Nat :=
  if r.start ≤ r.end then
    modulus w - (r.end - r.start + 1)
  else
    r.start - r.end - 1

theorem full_wf {w : Nat} (hw : 1 ≤ w) : (full w).wf w :=
  ⟨hw, modulus_pos w, Nat.sub_lt (modulus_pos w) Nat.zero_lt_one⟩

theorem contains_full {w : Nat} (_hw : 1 ≤ w) (v : BitVec w) :
    (full w).containsBV v = true := by
  unfold containsBV contains full
  have hle : 0 ≤ modulus w - 1 := Nat.zero_le _
  have hv : v.toNat ≤ modulus w - 1 := Nat.le_pred_of_lt v.isLt
  simp [hle, hv]

theorem availableNiches_full {w : Nat} (_hw : 1 ≤ w) :
    (full w).availableNiches w = 0 := by
  unfold availableNiches full
  have hm : 1 ≤ modulus w := modulus_pos w
  simp [Nat.sub_add_cancel hm]

theorem validCount_pos {w : Nat} {r : WrappingRange} (_hwf : r.wf w) :
    1 ≤ r.validCount w := by
  unfold validCount
  split
  · exact Nat.succ_le_succ (Nat.zero_le _)
  · exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_add_left _ _)

theorem validCount_add_availableNiches {w : Nat} {r : WrappingRange} (hwf : r.wf w) :
    r.validCount w + r.availableNiches w = modulus w := by
  rcases hwf with ⟨_, hs, he⟩
  unfold validCount availableNiches
  by_cases h : r.start ≤ r.end
  · simp only [h, ↓reduceIte]
    exact Nat.add_sub_cancel' (sub_add_one_lt_of_lt he)
  · simp only [h, ↓reduceIte]
    have hlt : r.end < r.start := Nat.lt_of_not_le h
    have h1 : 1 ≤ r.start - r.end := Nat.sub_pos_of_lt hlt
    have hstep1 : r.end + 1 + (r.start - r.end - 1) = r.start := by
      rw [Nat.add_comm r.end 1, Nat.add_assoc, Nat.add_comm r.end,
          ← Nat.add_assoc 1, Nat.add_comm 1 (r.start - r.end - 1),
          Nat.sub_add_cancel h1, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
    rw [Nat.add_assoc, hstep1, Nat.sub_add_cancel (Nat.le_of_lt hs)]

theorem validCount_le_modulus {w : Nat} {r : WrappingRange} (hwf : r.wf w) :
    r.validCount w ≤ modulus w := by
  rw [← validCount_add_availableNiches hwf]
  exact Nat.le_add_right _ _

theorem contains_iff {r : WrappingRange} {v : Nat} :
    r.contains v = true ↔
      (if r.start ≤ r.end then r.start ≤ v ∧ v ≤ r.end else r.start ≤ v ∨ v ≤ r.end) := by
  unfold contains
  by_cases h : r.start ≤ r.end
  · simp [h]
  · simp [h]

theorem contains_eq_false_iff {r : WrappingRange} {v : Nat} :
    r.contains v = false ↔
      (if r.start ≤ r.end then v < r.start ∨ r.end < v else r.end < v ∧ v < r.start) := by
  unfold contains
  by_cases h : r.start ≤ r.end
  · simp only [h, ↓reduceIte, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]
  · simp only [h, ↓reduceIte, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le, and_comm]

/-- Next modular value `(x + 1) mod 2^w` for `x < 2^w`. -/
def nextMod (w x : Nat) : Nat :=
  if x + 1 = modulus w then 0 else x + 1

/-- Previous modular value `(x - 1) mod 2^w` for `x < 2^w`. -/
def prevMod (w x : Nat) : Nat :=
  if x = 0 then modulus w - 1 else x - 1

theorem nextMod_lt {w x : Nat} (hx : x < modulus w) : nextMod w x < modulus w := by
  unfold nextMod
  by_cases h : x + 1 = modulus w
  · simp [h, modulus_pos w]
  · simp only [h, ↓reduceIte]
    exact Nat.lt_of_le_of_ne hx h

theorem nextMod_eq_mod {w x : Nat} (hx : x < modulus w) :
    nextMod w x = (x + 1) % modulus w := by
  unfold nextMod
  by_cases h : x + 1 = modulus w
  · simp [h, Nat.mod_self]
  · simp only [h, ↓reduceIte]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_ne hx h)).symm

theorem prevMod_lt {w x : Nat} (hx : x < modulus w) : prevMod w x < modulus w := by
  unfold prevMod
  by_cases h : x = 0
  · simp only [h, ↓reduceIte]
    exact Nat.sub_lt (modulus_pos w) Nat.zero_lt_one
  · simp only [h, ↓reduceIte]
    exact Nat.lt_of_le_of_lt (Nat.sub_le x 1) hx

/-- Exact equivalence between `availableNiches = 0` and `(end + 1) mod 2^w = start`. -/
theorem availableNiches_eq_zero_iff_nextMod_eq_start {w : Nat} {r : WrappingRange}
    (hwf : r.wf w) :
    r.availableNiches w = 0 ↔ nextMod w r.end = r.start := by
  rcases hwf with ⟨_, hs, he⟩
  unfold availableNiches nextMod
  by_cases h : r.start ≤ r.end
  · simp only [h, ↓reduceIte]
    by_cases hend : r.end + 1 = modulus w
    · simp only [hend, ↓reduceIte]
      constructor
      · intro hzero
        have hge : modulus w ≤ r.end - r.start + 1 := Nat.le_of_sub_eq_zero hzero
        rw [← hend] at hge
        have hle2 : r.end ≤ r.end - r.start := Nat.le_of_succ_le_succ hge
        cases hsz : r.start with
        | zero => rfl
        | succ k =>
          rw [hsz] at h hle2
          have hlt : r.end - Nat.succ k < r.end :=
            Nat.sub_lt (Nat.lt_of_lt_of_le (Nat.zero_lt_succ k) h) (Nat.zero_lt_succ k)
          exact absurd (Nat.lt_of_lt_of_le hlt hle2) (Nat.lt_irrefl _)
      · intro hs0
        rw [← hs0, Nat.sub_zero, hend, Nat.sub_self]
    · simp only [hend, ↓reduceIte]
      have hlt_m : r.end + 1 < modulus w := Nat.lt_of_le_of_ne he hend
      have h1 : r.end - r.start + 1 < modulus w :=
        Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.sub_le r.end r.start) 1) hlt_m
      have hpos : 0 < modulus w - (r.end - r.start + 1) := Nat.sub_pos_of_lt h1
      have hne_end : r.end + 1 ≠ r.start := by
        intro heq
        have hlt : r.start < r.end + 1 := Nat.lt_succ_of_le h
        rw [heq] at hlt
        exact Nat.lt_irrefl _ hlt
      constructor
      · intro hzero; exact absurd hzero (Nat.ne_of_gt hpos)
      · intro heq; exact absurd heq hne_end
  · simp only [h, ↓reduceIte]
    have hlt : r.end < r.start := Nat.lt_of_not_le h
    have hend_lt : r.end + 1 < modulus w := Nat.lt_of_le_of_lt hlt hs
    have hneq : r.end + 1 ≠ modulus w := Nat.ne_of_lt hend_lt
    simp only [hneq, ↓reduceIte]
    constructor
    · intro hzero
      have hle : r.start - r.end ≤ 1 := Nat.le_of_sub_eq_zero hzero
      have hge : 1 ≤ r.start - r.end := Nat.sub_pos_of_lt hlt
      have heq1 : r.start - r.end = 1 := Nat.le_antisymm hle hge
      have hadd := congrArg (· + r.end) heq1
      rw [Nat.sub_add_cancel (Nat.le_of_lt hlt), Nat.add_comm 1 r.end] at hadd
      exact hadd.symm
    · intro heq
      rw [← heq, Nat.add_sub_cancel_left, Nat.sub_self]

/-- LLVM half-open modular `range(iW lo, hi)` predicate (well-formed when `lo ≠ hi`,
`lo < 2^w`, `hi < 2^w`). When `lo < hi`, matches `lo ≤ v < hi`; when `hi < lo`,
wraps around `2^w`: `lo ≤ v` or `v < hi`. -/
def llvmHalfOpenContains (lo hi v : Nat) : Bool :=
  if lo < hi then
    decide (lo ≤ v) && decide (v < hi)
  else
    decide (lo ≤ v) || decide (v < hi)

/-- Exact equivalence between Rust's inclusive `WrappingRange` and LLVM's half-open
`range(iW r.start, (r.end + 1) mod 2^w)` attribute for every non-full scalar range. -/
theorem llvmHalfOpenContains_eq_contains {w : Nat} {r : WrappingRange}
    (hwf : r.wf w) (hnonfull : 0 < r.availableNiches w) (v : BitVec w) :
    llvmHalfOpenContains r.start ((r.end + 1) % modulus w) v.toNat = r.containsBV v := by
  rcases hwf with ⟨hw, hs, he⟩
  have hnext : nextMod w r.end = (r.end + 1) % modulus w := nextMod_eq_mod he
  have hne : nextMod w r.end ≠ r.start := by
    intro heq
    have hzero := (availableNiches_eq_zero_iff_nextMod_eq_start ⟨hw, hs, he⟩).mpr heq
    rw [hzero] at hnonfull
    exact Nat.lt_irrefl 0 hnonfull
  rw [← hnext]
  unfold llvmHalfOpenContains containsBV contains nextMod
  by_cases hend : r.end + 1 = modulus w
  · simp only [hend, ↓reduceIte]
    have hnotlt : ¬ (r.start < 0) := Nat.not_lt_zero r.start
    have hle_end : r.start ≤ r.end := by
      have h1 : r.start ≤ modulus w - 1 := Nat.le_pred_of_lt hs
      have hend_eq : r.end = modulus w - 1 := by
        rw [← hend]; exact (Nat.add_sub_cancel r.end 1).symm
      rwa [hend_eq]
    have hv_le_end : v.toNat ≤ r.end := by
      have h1 : v.toNat < r.end + 1 := by rw [hend]; exact v.isLt
      exact Nat.le_of_lt_succ h1
    simp [hnotlt, hle_end, hv_le_end]
  · simp only [hend, ↓reduceIte]
    by_cases h : r.start ≤ r.end
    · have hlt_hi : r.start < r.end + 1 := Nat.lt_succ_of_le h
      simp only [hlt_hi, h, ↓reduceIte]
      by_cases hvs : r.start ≤ v.toNat
      · by_cases hve : v.toNat ≤ r.end
        · have hvlt : v.toNat < r.end + 1 := Nat.lt_succ_of_le hve
          simp [hvs, hve, hvlt]
        · have hvnlt : ¬ (v.toNat < r.end + 1) := fun hlt => hve (Nat.le_of_lt_succ hlt)
          simp [hvs, hve, hvnlt]
      · simp [hvs]
    · have hlt : r.end < r.start := Nat.lt_of_not_le h
      have hnotlt : ¬ (r.start < r.end + 1) := Nat.not_lt_of_le hlt
      simp only [hnotlt, h, ↓reduceIte]
      by_cases hvs : r.start ≤ v.toNat
      · simp [hvs]
      · by_cases hve : v.toNat ≤ r.end
        · have hvlt : v.toNat < r.end + 1 := Nat.lt_succ_of_le hve
          simp [hvs, hve, hvlt]
        · have hvnlt : ¬ (v.toNat < r.end + 1) := fun hlt => hve (Nat.le_of_lt_succ hlt)
          simp [hvs, hve, hvnlt]

/-! ## Section 3: Iterative `Option` Niche-Allocation Algebra (`nestOption`) -/

/-- Unsigned distance of `sign_extend(w, x)` to `0` for `x < 2^w`, matching
`size.sign_extend(x).unsigned_abs()` in `compiler/rustc_abi/src/lib.rs:2182-2183`. -/
def signedAbsDist (w x : Nat) : Nat :=
  let half := modulus (w - 1)
  if x < half then x else modulus w - x

/-- `rustc`'s `Niche::reserve` (`count = 1`) bound-selection heuristic: picks the
adjacent niche (`start - 1` vs `end + 1`) closest to `0` in signed two's-complement
order, preserving the PR #155473 `bool` exception (`w = 8`, `0..=1`). -/
def chooseMoveStart (w : Nat) (r : WrappingRange) : Bool :=
  if w = 8 ∧ r.start = 0 ∧ r.end = 1 then
    false
  else
    decide (signedAbsDist w (prevMod w r.start) ≤ signedAbsDist w (nextMod w r.end))

/-- Reserve a single niche either at `start - 1` (`moveStart = true`) or
`end + 1` (`moveStart = false`), returning `(extendedRange, nicheTag)`. -/
def reserveOneDir (w : Nat) (r : WrappingRange) (moveStart : Bool) :
    Option (WrappingRange × Nat) :=
  if r.availableNiches w = 0 then
    none
  else if moveStart then
    let tag := prevMod w r.start
    some ({ start := tag, «end» := r.end }, tag)
  else
    let tag := nextMod w r.end
    some ({ start := r.start, «end» := tag }, tag)

/-- Single-step `Option` niche reservation matching `rustc_abi::Niche::reserve(_, 1)`. -/
def nestOption (w : Nat) (r : WrappingRange) : Option (WrappingRange × Nat) :=
  reserveOneDir w r (chooseMoveStart w r)

private theorem availableNiches_moveStart {w : Nat} {r : WrappingRange}
    (hwf : r.wf w) (hpos : 0 < r.availableNiches w) :
    ({ start := prevMod w r.start, «end» := r.end } : WrappingRange).availableNiches w =
      r.availableNiches w - 1 := by
  rcases hwf with ⟨hw, hs, he⟩
  have hne_wrap : nextMod w r.end ≠ r.start := by
    intro heq
    have hz := (availableNiches_eq_zero_iff_nextMod_eq_start ⟨hw, hs, he⟩).mpr heq
    rw [hz] at hpos
    exact Nat.lt_irrefl 0 hpos
  unfold availableNiches prevMod
  by_cases hs0 : r.start = 0
  · simp only [hs0, ↓reduceIte]
    have hm1_gt : r.end < modulus w - 1 := by
      refine Nat.lt_of_le_of_ne (Nat.le_pred_of_lt he) ?_
      intro heq
      apply hne_wrap
      unfold nextMod
      have hadd : r.end + 1 = modulus w := by
        rw [heq]; exact Nat.sub_add_cancel (modulus_pos w)
      simp [hadd, hs0]
    have hnotle : ¬ (modulus w - 1 ≤ r.end) := Nat.not_le_of_gt hm1_gt
    simp only [hnotle, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
    rw [Nat.sub_sub, Nat.sub_sub, Nat.sub_sub, Nat.add_comm 1 (r.end + 1)]
  · simp only [hs0, ↓reduceIte]
    have hs_pos : 0 < r.start := Nat.pos_of_ne_zero hs0
    by_cases hle : r.start ≤ r.end
    · have hle' : r.start - 1 ≤ r.end := Nat.le_trans (Nat.sub_le r.start 1) hle
      simp only [hle', hle, ↓reduceIte]
      have hsub_eq : r.end - (r.start - 1) = r.end - r.start + 1 := by
        have h1 : r.end - (r.start - 1) + (r.start - 1) = r.end := Nat.sub_add_cancel hle'
        have h2 : (r.end - r.start + 1) + (r.start - 1) = r.end := by
          rw [Nat.add_assoc, Nat.add_comm 1, Nat.sub_add_cancel hs_pos, Nat.sub_add_cancel hle]
        exact Nat.add_right_cancel (h1.trans h2.symm)
      rw [hsub_eq, ← Nat.sub_sub]
    · have hlt : r.end < r.start := Nat.lt_of_not_le hle
      have hne_adj : r.end + 1 ≠ r.start := by
        intro heq
        apply hne_wrap
        unfold nextMod
        have hend_lt_m : r.end + 1 < modulus w := by rw [heq]; exact hs
        have hneq_m : r.end + 1 ≠ modulus w := Nat.ne_of_lt hend_lt_m
        simp only [hneq_m, ↓reduceIte]
        exact heq
      have hlt' : r.end < r.start - 1 := by
        refine Nat.lt_of_le_of_ne (Nat.le_pred_of_lt hlt) ?_
        intro heq
        apply hne_adj
        rw [heq, Nat.sub_add_cancel hs_pos]
      have hnotle' : ¬ (r.start - 1 ≤ r.end) := Nat.not_le_of_gt hlt'
      simp only [hnotle', hle, ↓reduceIte]
      rw [Nat.sub_sub, Nat.sub_sub, Nat.sub_sub, Nat.sub_sub, Nat.add_comm 1 (r.end + 1), Nat.add_assoc]

private theorem availableNiches_moveEnd {w : Nat} {r : WrappingRange}
    (hwf : r.wf w) (hpos : 0 < r.availableNiches w) :
    ({ start := r.start, «end» := nextMod w r.end } : WrappingRange).availableNiches w =
      r.availableNiches w - 1 := by
  rcases hwf with ⟨hw, hs, he⟩
  have hne_wrap : nextMod w r.end ≠ r.start := by
    intro heq
    have hz := (availableNiches_eq_zero_iff_nextMod_eq_start ⟨hw, hs, he⟩).mpr heq
    rw [hz] at hpos
    exact Nat.lt_irrefl 0 hpos
  unfold availableNiches nextMod
  by_cases hend : r.end + 1 = modulus w
  · simp only [hend, ↓reduceIte]
    have hs_pos : 0 < r.start := by
      cases hz : r.start with
      | zero =>
        exfalso
        apply hne_wrap
        unfold nextMod
        simp [hend, hz]
      | succ k => exact Nat.zero_lt_succ k
    have hle : r.start ≤ r.end := by
      have h1 : r.start ≤ modulus w - 1 := Nat.le_pred_of_lt hs
      have hend_eq : r.end = modulus w - 1 := by
        rw [← hend]; exact (Nat.add_sub_cancel r.end 1).symm
      rwa [hend_eq]
    have hnotle : ¬ (r.start ≤ 0) := Nat.not_le_of_gt hs_pos
    simp only [hnotle, hle, ↓reduceIte, Nat.sub_zero]
    have hsub : modulus w - (r.end - r.start + 1) = r.start := by
      have heq_rhs : r.end - r.start + 1 + r.start = modulus w := by
        rw [Nat.add_assoc, Nat.add_comm 1 r.start, ← Nat.add_assoc,
            Nat.sub_add_cancel hle, hend]
      have h1 := congrArg (· - (r.end - r.start + 1)) heq_rhs
      simpa [Nat.add_sub_cancel_left] using h1.symm
    rw [hsub]
  · simp only [hend, ↓reduceIte]
    by_cases hle : r.start ≤ r.end
    · have hle' : r.start ≤ r.end + 1 := Nat.le_succ_of_le hle
      simp only [hle', hle, ↓reduceIte]
      have hsub_eq : r.end + 1 - r.start = r.end - r.start + 1 := Nat.sub_add_comm hle
      rw [hsub_eq, ← Nat.sub_sub]
    · have hlt : r.end < r.start := Nat.lt_of_not_le hle
      have hne_adj : r.end + 1 ≠ r.start := by
        intro heq
        apply hne_wrap
        unfold nextMod
        simp only [hend, ↓reduceIte]
        exact heq
      have hlt' : r.end + 1 < r.start := Nat.lt_of_le_of_ne hlt hne_adj
      have hnotle' : ¬ (r.start ≤ r.end + 1) := Nat.not_le_of_gt hlt'
      simp only [hnotle', hle, ↓reduceIte]
      rw [Nat.sub_sub, Nat.sub_sub, Nat.sub_sub]

/-- Key single-step soundness lemma for `reserveOneDir` (direction-independent):
reserving one niche from a well-formed non-full `WrappingRange` yields a well-formed
extended range whose valid set is the exact disjoint union `{tag} ∪ valid(r)`,
decrementing `availableNiches` by `1` and incrementing `validCount` by `1`. -/
theorem reserveOneDir_spec {w : Nat} {r : WrappingRange} (moveStart : Bool)
    (hwf : r.wf w) (hpos : 0 < r.availableNiches w) :
    ∃ r' tag,
      reserveOneDir w r moveStart = some (r', tag) ∧
      r'.wf w ∧
      tag < modulus w ∧
      r.contains tag = false ∧
      (∀ v : Nat, v < modulus w → r'.contains v = (decide (v = tag) || r.contains v)) ∧
      r'.availableNiches w = r.availableNiches w - 1 ∧
      r'.validCount w = r.validCount w + 1 := by
  rcases hwf with ⟨hw, hs, he⟩
  have hne0 : r.availableNiches w ≠ 0 := Nat.ne_of_gt hpos
  unfold reserveOneDir
  simp only [hne0, ↓reduceIte]
  have hne_wrap : nextMod w r.end ≠ r.start := by
    intro heq
    have hz := (availableNiches_eq_zero_iff_nextMod_eq_start ⟨hw, hs, he⟩).mpr heq
    rw [hz] at hpos
    exact Nat.lt_irrefl 0 hpos
  cases moveStart with
  | true =>
    have hwf' : ({ start := prevMod w r.start, «end» := r.end } : WrappingRange).wf w :=
      ⟨hw, prevMod_lt hs, he⟩
    have hav : ({ start := prevMod w r.start, «end» := r.end } : WrappingRange).availableNiches w =
        r.availableNiches w - 1 := availableNiches_moveStart ⟨hw, hs, he⟩ hpos
    refine ⟨{ start := prevMod w r.start, «end» := r.end }, prevMod w r.start, rfl,
      hwf', prevMod_lt hs, ?_, ?_, hav, ?_⟩
    · rw [contains_eq_false_iff]
      unfold prevMod
      by_cases hs0 : r.start = 0
      · simp only [hs0, Nat.zero_le, ↓reduceIte]
        right
        refine Nat.lt_of_le_of_ne (Nat.le_pred_of_lt he) ?_
        intro heq
        apply hne_wrap
        unfold nextMod
        have hadd : r.end + 1 = modulus w := by
          rw [heq]; exact Nat.sub_add_cancel (modulus_pos w)
        simp [hadd, hs0]
      · simp only [hs0, ↓reduceIte]
        have hs_pos : 0 < r.start := Nat.pos_of_ne_zero hs0
        have hprev_lt : r.start - 1 < r.start := Nat.sub_lt hs_pos Nat.zero_lt_one
        by_cases hle : r.start ≤ r.end
        · simp only [hle, ↓reduceIte]; exact Or.inl hprev_lt
        · simp only [hle, ↓reduceIte]
          have hlt : r.end < r.start := Nat.lt_of_not_le hle
          have hne_adj : r.end + 1 ≠ r.start := by
            intro heq
            apply hne_wrap
            unfold nextMod
            have hend_lt_m : r.end + 1 < modulus w := by rw [heq]; exact hs
            have hneq_m : r.end + 1 ≠ modulus w := Nat.ne_of_lt hend_lt_m
            simp only [hneq_m, ↓reduceIte]
            exact heq
          have hlt_prev : r.end < r.start - 1 := by
            refine Nat.lt_of_le_of_ne (Nat.le_pred_of_lt hlt) ?_
            intro heq
            apply hne_adj
            rw [heq, Nat.sub_add_cancel hs_pos]
          exact ⟨hlt_prev, hprev_lt⟩
    · intro v hv
      unfold contains prevMod
      by_cases hs0 : r.start = 0
      · simp only [hs0, Nat.zero_le, ↓reduceIte]
        have hm1_gt : r.end < modulus w - 1 := by
          refine Nat.lt_of_le_of_ne (Nat.le_pred_of_lt he) ?_
          intro heq
          apply hne_wrap
          unfold nextMod
          have hadd : r.end + 1 = modulus w := by
            rw [heq]; exact Nat.sub_add_cancel (modulus_pos w)
          simp [hadd, hs0]
        have hnotle : ¬ (modulus w - 1 ≤ r.end) := Nat.not_le_of_gt hm1_gt
        simp only [hnotle, ↓reduceIte]
        have hv_le_m1 : v ≤ modulus w - 1 := Nat.le_pred_of_lt hv
        by_cases hveq : v = modulus w - 1
        · subst hveq; simp
        · have hv_not_ge : ¬ (modulus w - 1 ≤ v) := fun hge => hveq (Nat.le_antisymm hv_le_m1 hge)
          simp [hveq, hv_not_ge]
      · simp only [hs0, ↓reduceIte]
        have hs_pos : 0 < r.start := Nat.pos_of_ne_zero hs0
        by_cases hle : r.start ≤ r.end
        · have hle' : r.start - 1 ≤ r.end := Nat.le_trans (Nat.sub_le r.start 1) hle
          simp only [hle', hle, ↓reduceIte]
          by_cases hveq : v = r.start - 1
          · subst hveq; simp [hle']
          · simp only [hveq, decide_false, Bool.false_or]
            by_cases hvs : r.start ≤ v
            · have hvs' : r.start - 1 ≤ v := Nat.le_trans (Nat.sub_le r.start 1) hvs
              simp [hvs, hvs']
            · have hnot : ¬ (r.start - 1 ≤ v) := by
                intro hge
                have hvle : v ≤ r.start - 1 := Nat.le_pred_of_lt (Nat.lt_of_not_le hvs)
                exact hveq (Nat.le_antisymm hvle hge)
              simp [hvs, hnot]
        · have hlt : r.end < r.start := Nat.lt_of_not_le hle
          have hne_adj : r.end + 1 ≠ r.start := by
            intro heq
            apply hne_wrap
            unfold nextMod
            have hend_lt_m : r.end + 1 < modulus w := by rw [heq]; exact hs
            have hneq_m : r.end + 1 ≠ modulus w := Nat.ne_of_lt hend_lt_m
            simp only [hneq_m, ↓reduceIte]
            exact heq
          have hlt' : r.end < r.start - 1 := by
            refine Nat.lt_of_le_of_ne (Nat.le_pred_of_lt hlt) ?_
            intro heq
            apply hne_adj
            rw [heq, Nat.sub_add_cancel hs_pos]
          have hnotle' : ¬ (r.start - 1 ≤ r.end) := Nat.not_le_of_gt hlt'
          simp only [hnotle', hle, ↓reduceIte]
          by_cases hveq : v = r.start - 1
          · subst hveq; simp
          · simp only [hveq, decide_false, Bool.false_or]
            by_cases hvs : r.start ≤ v
            · have hvs' : r.start - 1 ≤ v := Nat.le_trans (Nat.sub_le r.start 1) hvs
              simp [hvs, hvs']
            · have hnot : ¬ (r.start - 1 ≤ v) := by
                intro hge
                have hvle : v ≤ r.start - 1 := Nat.le_pred_of_lt (Nat.lt_of_not_le hvs)
                exact hveq (Nat.le_antisymm hvle hge)
              simp [hvs, hnot]
    · have hsum := validCount_add_availableNiches ⟨hw, hs, he⟩
      have hsum' := validCount_add_availableNiches hwf'
      rw [hav] at hsum'
      have hsum_eq :
          ({ start := prevMod w r.start, «end» := r.end } : WrappingRange).validCount w +
            (r.availableNiches w - 1) =
          (r.validCount w + 1) + (r.availableNiches w - 1) := by
        rw [hsum', Nat.add_assoc, Nat.add_comm 1, Nat.sub_add_cancel hpos, hsum]
      exact Nat.add_right_cancel hsum_eq
  | false =>
    have hwf' : ({ start := r.start, «end» := nextMod w r.end } : WrappingRange).wf w :=
      ⟨hw, hs, nextMod_lt he⟩
    have hav : ({ start := r.start, «end» := nextMod w r.end } : WrappingRange).availableNiches w =
        r.availableNiches w - 1 := availableNiches_moveEnd ⟨hw, hs, he⟩ hpos
    refine ⟨{ start := r.start, «end» := nextMod w r.end }, nextMod w r.end, rfl,
      hwf', nextMod_lt he, ?_, ?_, hav, ?_⟩
    · rw [contains_eq_false_iff]
      unfold nextMod
      by_cases hend : r.end + 1 = modulus w
      · simp only [hend, ↓reduceIte]
        have hs_pos : 0 < r.start := by
          cases hz : r.start with
          | zero =>
            exfalso; apply hne_wrap; unfold nextMod; simp [hend, hz]
          | succ k => exact Nat.zero_lt_succ k
        have hle : r.start ≤ r.end := by
          have h1 : r.start ≤ modulus w - 1 := Nat.le_pred_of_lt hs
          have hend_eq : r.end = modulus w - 1 := by
            rw [← hend]; exact (Nat.add_sub_cancel r.end 1).symm
          rwa [hend_eq]
        simp only [hle, ↓reduceIte]
        exact Or.inl hs_pos
      · simp only [hend, ↓reduceIte]
        by_cases hle : r.start ≤ r.end
        · simp only [hle, ↓reduceIte]; exact Or.inr (Nat.lt_succ_self r.end)
        · simp only [hle, ↓reduceIte]
          have hlt : r.end < r.start := Nat.lt_of_not_le hle
          have hne_adj : r.end + 1 ≠ r.start := by
            intro heq
            apply hne_wrap
            unfold nextMod
            simp only [hend, ↓reduceIte]
            exact heq
          exact ⟨Nat.lt_succ_self r.end, Nat.lt_of_le_of_ne hlt hne_adj⟩
    · intro v hv
      unfold contains nextMod
      by_cases hend : r.end + 1 = modulus w
      · simp only [hend, ↓reduceIte]
        have hs_pos : 0 < r.start := by
          cases hz : r.start with
          | zero =>
            exfalso; apply hne_wrap; unfold nextMod; simp [hend, hz]
          | succ k => exact Nat.zero_lt_succ k
        have hle : r.start ≤ r.end := by
          have h1 : r.start ≤ modulus w - 1 := Nat.le_pred_of_lt hs
          have hend_eq : r.end = modulus w - 1 := by
            rw [← hend]; exact (Nat.add_sub_cancel r.end 1).symm
          rwa [hend_eq]
        have hnotle : ¬ (r.start ≤ 0) := Nat.not_le_of_gt hs_pos
        simp only [hnotle, hle, ↓reduceIte]
        have hv_le_end : v ≤ r.end := by
          have h1 : v < r.end + 1 := by rw [hend]; exact hv
          exact Nat.le_of_lt_succ h1
        by_cases hv0 : v = 0
        · subst hv0; simp
        · have hnot0 : ¬ (v ≤ 0) := fun h => hv0 (Nat.eq_zero_of_le_zero h)
          simp [hv0, hnot0, hv_le_end]
      · simp only [hend, ↓reduceIte]
        by_cases hle : r.start ≤ r.end
        · have hle' : r.start ≤ r.end + 1 := Nat.le_succ_of_le hle
          simp only [hle', hle, ↓reduceIte]
          by_cases hveq : v = r.end + 1
          · subst hveq; simp [hle']
          · simp only [hveq, decide_false, Bool.false_or]
            by_cases hvs : r.start ≤ v
            · by_cases hve : v ≤ r.end
              · simp [hvs, hve, Nat.le_succ_of_le hve]
              · have hnot : ¬ (v ≤ r.end + 1) := by
                  intro hle1
                  cases Nat.eq_or_lt_of_le hle1 with
                  | inl heq => exact hveq heq
                  | inr hlt => exact hve (Nat.le_of_lt_succ hlt)
                simp [hvs, hve, hnot]
            · simp [hvs]
        · have hlt : r.end < r.start := Nat.lt_of_not_le hle
          have hne_adj : r.end + 1 ≠ r.start := by
            intro heq
            apply hne_wrap
            unfold nextMod
            simp only [hend, ↓reduceIte]
            exact heq
          have hlt' : r.end + 1 < r.start := Nat.lt_of_le_of_ne hlt hne_adj
          have hnotle' : ¬ (r.start ≤ r.end + 1) := Nat.not_le_of_gt hlt'
          simp only [hnotle', hle, ↓reduceIte]
          by_cases hveq : v = r.end + 1
          · subst hveq; simp
          · simp only [hveq, decide_false, Bool.false_or]
            by_cases hvs : r.start ≤ v
            · simp [hvs]
            · by_cases hve : v ≤ r.end
              · simp [hvs, hve, Nat.le_succ_of_le hve]
              · have hnot : ¬ (v ≤ r.end + 1) := by
                  intro hle1
                  cases Nat.eq_or_lt_of_le hle1 with
                  | inl heq => exact hveq heq
                  | inr hlt2 => exact hve (Nat.le_of_lt_succ hlt2)
                simp [hvs, hve, hnot]
    · have hsum := validCount_add_availableNiches ⟨hw, hs, he⟩
      have hsum' := validCount_add_availableNiches hwf'
      rw [hav] at hsum'
      have hsum_eq :
          ({ start := r.start, «end» := nextMod w r.end } : WrappingRange).validCount w +
            (r.availableNiches w - 1) =
          (r.validCount w + 1) + (r.availableNiches w - 1) := by
        rw [hsum', Nat.add_assoc, Nat.add_comm 1, Nat.sub_add_cancel hpos, hsum]
      exact Nat.add_right_cancel hsum_eq

theorem nestOption_spec {w : Nat} {r : WrappingRange}
    (hwf : r.wf w) (hpos : 0 < r.availableNiches w) :
    ∃ r' tag,
      nestOption w r = some (r', tag) ∧
      r'.wf w ∧
      tag < modulus w ∧
      r.contains tag = false ∧
      (∀ v : Nat, v < modulus w → r'.contains v = (decide (v = tag) || r.contains v)) ∧
      r'.availableNiches w = r.availableNiches w - 1 ∧
      r'.validCount w = r.validCount w + 1 :=
  reserveOneDir_spec (chooseMoveStart w r) hwf hpos

theorem nestOption_none_of_zero {w : Nat} {r : WrappingRange}
    (hzero : r.availableNiches w = 0) :
    nestOption w r = none := by
  unfold nestOption reserveOneDir
  simp [hzero]

/-- Iterate `nestOption` `k` times using `Nat.rec` (no `._unsafe_rec` generated).
Returns `(finalRange, tags)` where `tags[0]` is the outermost `Option^k::None` tag
and `tags[k-1]` is the innermost `Option^1::None` tag. -/
noncomputable def nestOptionIter (w : Nat) (r : WrappingRange) (k : Nat) :
    Option (WrappingRange × List Nat) :=
  Nat.rec
    (some (r, []))
    (fun _ acc =>
      match acc with
      | none => none
      | some (cur, tags) =>
        match nestOption w cur with
        | none => none
        | some (nxt, tag) => some (nxt, tag :: tags))
    k

/-- Lookup element `i` in `xs : List Nat` with default `0` using `List.rec`
(no `._unsafe_rec` generated). -/
noncomputable def listGetNat (xs : List Nat) (i : Nat) : Nat :=
  List.rec
    (fun _ => 0)
    (fun hd _ ih idx => match idx with | 0 => hd | j + 1 => ih j)
    xs i

/-- Find the first index `i < xs.length` where `xs[i] = target`, using `List.rec`
(no `._unsafe_rec` generated). -/
noncomputable def listFindIdxNat (xs : List Nat) (target : Nat) : Option Nat :=
  List.rec
    none
    (fun hd _ ih =>
      if hd = target then
        some 0
      else
        match ih with
        | none => none
        | some j => some (j + 1))
    xs

/-- Pairwise distinctness of a `List Nat` expressed via `List.rec` (no `._unsafe_rec`). -/
def PairwiseDistinct (xs : List Nat) : Prop :=
  List.rec True (fun hd tl ih => (∀ y, y ∈ tl → hd ≠ y) ∧ ih) xs

theorem listGetNat_mem {xs : List Nat} {i : Nat} (hi : i < xs.length) :
    listGetNat xs i ∈ xs := by
  induction xs generalizing i with
  | nil => cases hi
  | cons hd tl ih =>
    cases i with
    | zero => exact List.Mem.head tl
    | succ j =>
      have hj : j < tl.length := Nat.lt_of_succ_lt_succ hi
      exact List.Mem.tail hd (ih hj)

theorem listFindIdxNat_lt {xs : List Nat} {target idx : Nat}
    (h : listFindIdxNat xs target = some idx) : idx < xs.length := by
  induction xs generalizing idx with
  | nil => cases h
  | cons hd tl ih =>
    change (if hd = target then some 0 else
      match listFindIdxNat tl target with | none => none | some j => some (j + 1)) = some idx at h
    by_cases heq : hd = target
    · simp only [heq, ↓reduceIte] at h
      injection h with h0
      rw [← h0]
      exact Nat.zero_lt_succ _
    · simp only [heq, ↓reduceIte] at h
      cases hf : listFindIdxNat tl target with
      | none => rw [hf] at h; cases h
      | some j =>
        rw [hf] at h
        injection h with hj
        rw [← hj]
        exact Nat.succ_lt_succ (ih hf)

theorem listFindIdxNat_get_of_distinct {xs : List Nat} (hdist : PairwiseDistinct xs)
    {i : Nat} (hi : i < xs.length) :
    listFindIdxNat xs (listGetNat xs i) = some i := by
  induction xs generalizing i with
  | nil => cases hi
  | cons hd tl ih =>
    rcases hdist with ⟨hhead, htl⟩
    cases i with
    | zero =>
      change (if hd = hd then some 0 else _) = some 0
      simp
    | succ j =>
      have hj : j < tl.length := Nat.lt_of_succ_lt_succ hi
      have hmem : listGetNat tl j ∈ tl := listGetNat_mem hj
      have hne : hd ≠ listGetNat tl j := hhead _ hmem
      change (if hd = listGetNat tl j then some 0 else
        match listFindIdxNat tl (listGetNat tl j) with
        | none => none
        | some m => some (m + 1)) = some (j + 1)
      simp only [hne, ↓reduceIte]
      rw [ih htl hj]

theorem listFindIdxNat_none_of_not_mem {xs : List Nat} {target : Nat}
    (hnot : target ∉ xs) :
    listFindIdxNat xs target = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    have hne : hd ≠ target := fun heq => hnot (heq ▸ List.Mem.head tl)
    have htl : target ∉ tl := fun hmem => hnot (List.Mem.tail hd hmem)
    change (if hd = target then some 0 else
      match listFindIdxNat tl target with
      | none => none
      | some j => some (j + 1)) = none
    simp only [hne, ↓reduceIte]
    rw [ih htl]

/-- Canonical value space of `k`-nested `Option` over a `w`-bit pattern payload `r`:
`noneAt level` encodes `Some^(level)(None)` (for `level < k`), and `payload v hv`
encodes `Some^k(v)` where `v : BitVec w` satisfies `r.containsBV v = true`. -/
inductive NestedOptionVal (w : Nat) (r : WrappingRange) (k : Nat) where
  | noneAt (level : Fin k)
  | payload (v : BitVec w) (hv : r.containsBV v = true)

/-- Encode a `k`-nested `Option` value into a single `BitVec w` (`1` byte when `w = 8`),
keeping `Some^k(v)` transparent and mapping `noneAt level` to `tags[level]`. -/
noncomputable def encodeNestedOption (w : Nat) (r : WrappingRange) (k : Nat) (tags : List Nat) :
    NestedOptionVal w r k → BitVec w
  | .noneAt lvl => BitVec.ofNat w (listGetNat tags lvl.val)
  | .payload v _ => v

/-- Decode a single `BitVec w` into `NestedOptionVal w r k` given the allocated
tag table `tags` (with `tags.length = k`). -/
noncomputable def decodeNestedOption (w : Nat) (r : WrappingRange) (k : Nat)
    (tags : List Nat) (hlen : tags.length = k) (raw : BitVec w) :
    Option (NestedOptionVal w r k) :=
  match hfind : listFindIdxNat tags raw.toNat with
  | some idx =>
    let hlt : idx < k := hlen ▸ listFindIdxNat_lt hfind
    some (.noneAt ⟨idx, hlt⟩)
  | none =>
    if hvalid : r.containsBV raw = true then
      some (.payload raw hvalid)
    else
      none

/-- **Theorem 1: Iterative `Option` Niche-Stacking Injectivity & Size Preservation.**
For any bit-width `w ≥ 1`, well-formed `WrappingRange` `r`, and nesting depth
`k ≤ r.availableNiches w`:
1. `nestOptionIter w r k` succeeds with `(rK, tags)` where `rK.wf w`,
   `rK.availableNiches w = r.availableNiches w - k`, and
   `rK.validCount w = r.validCount w + k`.
2. `tags.length = k`, every tag is `< 2^w` and disjoint from `r`, and all `k`
   tags are pairwise distinct.
3. The extended range `rK` covers exactly `valid(r) ∪ tags`.
4. `encodeNestedOption` maps `NestedOptionVal w r k` into a single `BitVec w`
   (`1` byte when `w = 8`) with exact left-inverse `decodeNestedOption` and
   strict injectivity (`encode x = encode y → x = y`). -/
theorem nestedOption_niche_disjoint_and_injective
    {w : Nat} {r : WrappingRange} {k : Nat}
    (hwf : r.wf w) (hk : k ≤ r.availableNiches w) :
    ∃ rK, ∃ tags, ∃ hlen : tags.length = k,
      nestOptionIter w r k = some (rK, tags) ∧
      rK.wf w ∧
      rK.availableNiches w = r.availableNiches w - k ∧
      rK.validCount w = r.validCount w + k ∧
      PairwiseDistinct tags ∧
      (∀ t, t ∈ tags → t < modulus w ∧ r.contains t = false) ∧
      (∀ v : BitVec w, rK.containsBV v = true ↔ r.containsBV v = true ∨ v.toNat ∈ tags) ∧
      (∀ x : NestedOptionVal w r k,
        decodeNestedOption w r k tags hlen (encodeNestedOption w r k tags x) = some x) ∧
      (∀ x y : NestedOptionVal w r k,
        encodeNestedOption w r k tags x = encodeNestedOption w r k tags y → x = y) := by
  have hcore :
      ∀ m : Nat, m ≤ r.availableNiches w →
        ∃ rM tags,
          nestOptionIter w r m = some (rM, tags) ∧
          tags.length = m ∧
          rM.wf w ∧
          rM.availableNiches w = r.availableNiches w - m ∧
          rM.validCount w = r.validCount w + m ∧
          PairwiseDistinct tags ∧
          (∀ t, t ∈ tags → t < modulus w ∧ r.contains t = false) ∧
          (∀ v : Nat, v < modulus w →
            (rM.contains v = true ↔ r.contains v = true ∨ v ∈ tags)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨r, [], rfl, rfl, hwf, (Nat.sub_zero _).symm, (Nat.add_zero _).symm, trivial, ?_, ?_⟩
      · intro t ht; cases ht
      · intro v _; simp
    | succ j ih =>
      intro hle_succ
      have hj_le : j ≤ r.availableNiches w := Nat.le_trans (Nat.le_succ j) hle_succ
      rcases ih hj_le with ⟨rJ, tagsJ, hiterJ, hlenJ, hwfJ, havJ, hvcJ, hdistJ, htagsJ, hcovJ⟩
      have hposJ : 0 < rJ.availableNiches w := by
        rw [havJ]
        exact Nat.sub_pos_of_lt hle_succ
      rcases nestOption_spec hwfJ hposJ with
        ⟨rNext, tag, hstep, hwfNext, htagLt, hnotInRJ, hcovStep, havStep, hvcStep⟩
      refine ⟨rNext, tag :: tagsJ, ?_, ?_, hwfNext, ?_, ?_, ?_, ?_, ?_⟩
      · change (match nestOptionIter w r j with
          | none => none
          | some (cur, tags) =>
            match nestOption w cur with
            | none => none
            | some (nxt, t) => some (nxt, t :: tags)) = some (rNext, tag :: tagsJ)
        rw [hiterJ]
        dsimp only
        rw [hstep]
      · simp [hlenJ]
      · rw [havStep, havJ, Nat.sub_sub]
      · rw [hvcStep, hvcJ, Nat.add_assoc]
      · refine ⟨?_, hdistJ⟩
        intro y hy heq
        subst heq
        have htrue : rJ.contains tag = true := (hcovJ tag htagLt).mpr (Or.inr hy)
        rw [hnotInRJ] at htrue
        cases htrue
      · intro t ht
        cases ht with
        | head =>
          refine ⟨htagLt, ?_⟩
          cases hc : r.contains tag with
          | false => rfl
          | true =>
            have htrue : rJ.contains tag = true := (hcovJ tag htagLt).mpr (Or.inl hc)
            rw [hnotInRJ] at htrue
            cases htrue
        | tail _ hmem => exact htagsJ t hmem
      · intro v hv
        rw [hcovStep v hv, Bool.or_eq_true, decide_eq_true_iff, hcovJ v hv]
        constructor
        · intro h
          rcases h with heq | hr | hmem
          · exact Or.inr (heq ▸ List.Mem.head tagsJ)
          · exact Or.inl hr
          · exact Or.inr (List.Mem.tail tag hmem)
        · intro h
          rcases h with hr | hmem
          · exact Or.inr (Or.inl hr)
          · cases hmem with
            | head => exact Or.inl rfl
            | tail _ htl => exact Or.inr (Or.inr htl)
  rcases hcore k hk with ⟨rK, tags, hiter, hlen, hwfK, havK, hvcK, hdist, htags, hcov⟩
  have hround : ∀ x : NestedOptionVal w r k,
      decodeNestedOption w r k tags hlen (encodeNestedOption w r k tags x) = some x := by
    intro x
    cases x with
    | noneAt lvl =>
      unfold encodeNestedOption decodeNestedOption
      have hidx : lvl.val < tags.length := hlen.symm ▸ lvl.isLt
      have hmem : listGetNat tags lvl.val ∈ tags := listGetNat_mem hidx
      have hlt_mod : listGetNat tags lvl.val < modulus w := (htags _ hmem).1
      have htoNat : (BitVec.ofNat w (listGetNat tags lvl.val)).toNat = listGetNat tags lvl.val := by
        simp [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt hlt_mod
      have hfind : listFindIdxNat tags (BitVec.ofNat w (listGetNat tags lvl.val)).toNat = some lvl.val := by
        rw [htoNat]
        exact listFindIdxNat_get_of_distinct hdist hidx
      split
      · rename_i idx hmatch
        rw [hfind] at hmatch
        injection hmatch with hidx_eq
        subst hidx_eq
        rfl
      · rename_i hmatch
        rw [hfind] at hmatch
        cases hmatch
    | payload v hv =>
      unfold encodeNestedOption decodeNestedOption
      have hnotMem : v.toNat ∉ tags := by
        intro hmem
        have hfalse : r.contains v.toNat = false := (htags _ hmem).2
        unfold containsBV at hv
        rw [hfalse] at hv
        cases hv
      have hfind : listFindIdxNat tags v.toNat = none := listFindIdxNat_none_of_not_mem hnotMem
      split
      · rename_i idx hmatch
        rw [hfind] at hmatch
        cases hmatch
      · simp [hv]
  have hinj : ∀ x y : NestedOptionVal w r k,
      encodeNestedOption w r k tags x = encodeNestedOption w r k tags y → x = y := by
    intro x y heq
    have h1 := hround x
    have h2 := hround y
    rw [heq] at h1
    rw [h1] at h2
    injection h2
  refine ⟨rK, tags, hlen, hiter, hwfK, havK, hvcK, hdist, htags, ?_, hround, hinj⟩
  intro v
  exact hcov v.toNat v.isLt

/-! ## Section 4: LLVM `range(lo, hi)` / `nonnull` Elimination Soundness & Widening Safety -/

/-- Denotational outcome of a scalar-returning function that may either return a
`BitVec w` value or trap/panic on a failed guard. -/
inductive ExecResult (w : Nat) where
  | ret (v : BitVec w)
  | trap
  deriving DecidableEq, Repr

/-- Source semantics with an explicit range-validity guard (e.g. `if v == 0 || v > 10 { panic!() }`). -/
def evalRangeGuarded {w : Nat} (r : WrappingRange) (body : BitVec w → BitVec w)
    (x : BitVec w) : ExecResult w :=
  if r.containsBV x then .ret (body x) else .trap

/-- Source semantics written directly against LLVM's half-open modular interval `[lo, hi)`. -/
def evalLlvmHalfOpenGuarded {w : Nat} (lo hi : Nat) (body : BitVec w → BitVec w)
    (x : BitVec w) : ExecResult w :=
  if llvmHalfOpenContains lo hi x.toNat then .ret (body x) else .trap

/-- Optimized LLVM semantics after `range(iW lo, hi)` / `nonnull` erases the impossible trap branch. -/
def evalLlvmRangeFolded {w : Nat} (body : BitVec w → BitVec w) (x : BitVec w) : ExecResult w :=
  .ret (body x)

/-- **Theorem 2: LLVM `range` Dead-Branch Elimination Soundness.**
Whenever an input `x : BitVec w` satisfies the `TyKind::Pat` validity invariant
`r.containsBV x = true`, LLVM's half-open `range(iW r.start, (r.end + 1) mod 2^w)`
assumption holds and erasing the out-of-range trap branch preserves exact
operational semantics. -/
theorem llvm_range_elim_sound_under_pat_validity
    {w : Nat} {r : WrappingRange} (hwf : r.wf w) (hnonfull : 0 < r.availableNiches w)
    (body : BitVec w → BitVec w) (x : BitVec w) (hvalid : r.containsBV x = true) :
    llvmHalfOpenContains r.start ((r.end + 1) % modulus w) x.toNat = true ∧
    evalRangeGuarded r body x = evalLlvmRangeFolded body x ∧
    evalLlvmHalfOpenGuarded r.start ((r.end + 1) % modulus w) body x = evalLlvmRangeFolded body x := by
  have hllvm : llvmHalfOpenContains r.start ((r.end + 1) % modulus w) x.toNat = true := by
    rw [llvmHalfOpenContains_eq_contains hwf hnonfull x]
    exact hvalid
  refine ⟨hllvm, ?_, ?_⟩
  · unfold evalRangeGuarded evalLlvmRangeFolded
    rw [hvalid]
    rfl
  · unfold evalLlvmHalfOpenGuarded evalLlvmRangeFolded
    rw [hllvm]
    rfl

/-- **Theorem 3: `NonNull` / `NonZero` / `TyKind::Pat` Subtype-Widening Safety.**
1. Widening `Pat(B, r) → B` (`as_inner` / `NonZero::get` / `NonNull::as_ptr` via
   `transmute`) is unconditionally valid for every valid `Pat` bit pattern.
2. Narrowing `B → Pat(B, r)` is valid iff `r.containsBV x = true`.
3. For every proper pattern range (`0 < r.availableNiches w`), there constructively
   exists a valid base-type value `bad : BitVec w` (`(r.end + 1) mod 2^w`) that
   violates `Pat(B, r)`, proving a range check or proof obligation is necessary. -/
theorem pat_to_base_always_valid_and_base_to_pat_requires_range_check
    {w : Nat} {r : WrappingRange} (hwf : r.wf w) :
    (∀ x : BitVec w, r.containsBV x = true → (WrappingRange.full w).containsBV x = true) ∧
    (∀ x : BitVec w, (r.containsBV x = true ↔ r.contains x.toNat = true)) ∧
    (0 < r.availableNiches w →
      ∃ bad : BitVec w,
        (WrappingRange.full w).containsBV bad = true ∧
        r.containsBV bad = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x _
    exact contains_full hwf.1 x
  · intro x
    rfl
  · intro hpos
    rcases reserveOneDir_spec false hwf hpos with
      ⟨_, tag, _, _, htagLt, htagInvalid, _, _, _⟩
    refine ⟨BitVec.ofNat w tag, contains_full hwf.1 _, ?_⟩
    unfold containsBV
    have htoNat : (BitVec.ofNat w tag).toNat = tag := by
      simp [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt htagLt
    rw [htoNat]
    exact htagInvalid

/-! ## Section 5: Constructive Pigeonhole & Niche-Exhaustion Impossibility -/

/-- Constructive finite pigeonhole principle (`Fin (n + 1) → Fin n` cannot be
injective), proved by elementary induction with zero `Classical.choice`. -/
theorem no_injective_fin_succ_to_fin :
    ∀ (n : Nat) (f : Fin (n + 1) → Fin n), ¬ (∀ a b, f a = f b → a = b) := by
  intro n
  induction n with
  | zero =>
    intro f _
    exact Fin.elim0 (f ⟨0, Nat.zero_lt_one⟩)
  | succ m ih =>
    intro f hinj
    let last : Fin (m + 2) := ⟨m + 1, Nat.lt_succ_self (m + 1)⟩
    let pivot : Fin (m + 1) := f last
    let g : Fin (m + 1) → Fin m := fun i =>
      let i' : Fin (m + 2) := ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self (m + 1))⟩
      let y : Fin (m + 1) := f i'
      if hlt : y.val < pivot.val then
        ⟨y.val, Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ pivot.isLt)⟩
      else
        have hne_i : i' ≠ last := fun heq =>
          Nat.ne_of_lt i.isLt (congrArg Fin.val heq)
        have hne_y : y ≠ pivot := fun heq => hne_i (hinj i' last heq)
        have hgt : pivot.val < y.val :=
          Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun heq => hne_y (Fin.ext heq.symm))
        have hy_pos : 1 ≤ y.val := Nat.lt_of_le_of_lt (Nat.zero_le _) hgt
        have hy_sub_lt : y.val - 1 < m := by
          have := sub_lt_sub_right_of_lt y.isLt hy_pos
          rwa [Nat.add_sub_cancel] at this
        ⟨y.val - 1, hy_sub_lt⟩
    apply ih g
    intro a b hgab
    let a' : Fin (m + 2) := ⟨a.val, Nat.lt_trans a.isLt (Nat.lt_succ_self (m + 1))⟩
    let b' : Fin (m + 2) := ⟨b.val, Nat.lt_trans b.isLt (Nat.lt_succ_self (m + 1))⟩
    have ha_ne : f a' ≠ pivot := fun heq =>
      Nat.ne_of_lt a.isLt (congrArg Fin.val (hinj a' last heq))
    have hb_ne : f b' ≠ pivot := fun heq =>
      Nat.ne_of_lt b.isLt (congrArg Fin.val (hinj b' last heq))
    have hval : (g a).val = (g b).val := congrArg Fin.val hgab
    have hfa_fb : f a' = f b' := by
      dsimp only [g] at hval
      change (if hlt : (f a').val < pivot.val then (⟨(f a').val, _⟩ : Fin m)
              else ⟨(f a').val - 1, _⟩).val =
             (if hlt : (f b').val < pivot.val then (⟨(f b').val, _⟩ : Fin m)
              else ⟨(f b').val - 1, _⟩).val at hval
      by_cases ha : (f a').val < pivot.val
      · by_cases hb : (f b').val < pivot.val
        · simp only [ha, hb, ↓reduceDIte] at hval
          exact Fin.ext hval
        · simp only [ha, hb, ↓reduceDIte] at hval
          have hgt : pivot.val < (f b').val :=
            Nat.lt_of_le_of_ne (Nat.le_of_not_gt hb) (fun heq => hb_ne (Fin.ext heq.symm))
          have hle : pivot.val ≤ (f b').val - 1 := Nat.le_pred_of_lt hgt
          have hlt2 : (f a').val < (f b').val - 1 := Nat.lt_of_lt_of_le ha hle
          exact absurd hval (Nat.ne_of_lt hlt2)
      · by_cases hb : (f b').val < pivot.val
        · simp only [ha, hb, ↓reduceDIte] at hval
          have hgt : pivot.val < (f a').val :=
            Nat.lt_of_le_of_ne (Nat.le_of_not_gt ha) (fun heq => ha_ne (Fin.ext heq.symm))
          have hle : pivot.val ≤ (f a').val - 1 := Nat.le_pred_of_lt hgt
          have hlt2 : (f b').val < (f a').val - 1 := Nat.lt_of_lt_of_le hb hle
          exact absurd hval.symm (Nat.ne_of_lt hlt2)
        · simp only [ha, hb, ↓reduceDIte] at hval
          have hgt_a : pivot.val < (f a').val :=
            Nat.lt_of_le_of_ne (Nat.le_of_not_gt ha) (fun heq => ha_ne (Fin.ext heq.symm))
          have hgt_b : pivot.val < (f b').val :=
            Nat.lt_of_le_of_ne (Nat.le_of_not_gt hb) (fun heq => hb_ne (Fin.ext heq.symm))
          have hpos_a : 1 ≤ (f a').val := Nat.lt_of_le_of_lt (Nat.zero_le _) hgt_a
          have hpos_b : 1 ≤ (f b').val := Nat.lt_of_le_of_lt (Nat.zero_le _) hgt_b
          exact Fin.ext (eq_of_sub_eq_sub hpos_a hpos_b hval)
    exact Fin.ext (congrArg (Fin.val (n := m + 2)) (hinj a' b' hfa_fb))

/-- Enumerate the `i`-th valid bit pattern in `r` (starting at `r.start` and
stepping modularly modulo `2^w`) for `i < r.validCount w`. -/
def nthValidVal (w : Nat) (r : WrappingRange) (i : Nat) : Nat :=
  if r.start + i < modulus w then r.start + i else r.start + i - modulus w

theorem nthValidVal_lt {w : Nat} {r : WrappingRange} (hwf : r.wf w) {i : Nat}
    (hi : i < r.validCount w) :
    nthValidVal w r i < modulus w := by
  have hi_m : i < modulus w := Nat.lt_of_lt_of_le hi (validCount_le_modulus hwf)
  unfold nthValidVal
  by_cases h : r.start + i < modulus w
  · simp [h]
  · simp only [h, ↓reduceIte]
    have hge : modulus w ≤ r.start + i := Nat.le_of_not_gt h
    have hsum : r.start + i < modulus w + modulus w := Nat.add_lt_add hwf.2.1 hi_m
    have hsub := sub_lt_sub_right_of_lt hsum hge
    simpa [Nat.add_sub_cancel] using hsub

theorem nthValidVal_contains {w : Nat} {r : WrappingRange} (hwf : r.wf w) {i : Nat}
    (hi : i < r.validCount w) :
    r.contains (nthValidVal w r i) = true := by
  rcases hwf with ⟨_, hs, he⟩
  rw [contains_iff]
  unfold validCount at hi
  unfold nthValidVal
  by_cases hle : r.start ≤ r.end
  · simp only [hle, ↓reduceIte] at hi ⊢
    have h1 : r.start + i ≤ r.end := by
      have hlt : i ≤ r.end - r.start := Nat.le_of_lt_succ hi
      have hadd := Nat.add_le_add_left hlt r.start
      rwa [Nat.add_comm r.start (r.end - r.start), Nat.sub_add_cancel hle] at hadd
    have hlt_m : r.start + i < modulus w := Nat.lt_of_le_of_lt h1 he
    simp only [hlt_m, ↓reduceIte]
    exact ⟨Nat.le_add_right r.start i, h1⟩
  · simp only [hle, ↓reduceIte] at hi ⊢
    by_cases hlt_m : r.start + i < modulus w
    · simp only [hlt_m, ↓reduceIte]
      exact Or.inl (Nat.le_add_right r.start i)
    · simp only [hlt_m, ↓reduceIte]
      right
      have hge_m : modulus w ≤ r.start + i := Nat.le_of_not_gt hlt_m
      have hhi : r.start + i < modulus w + (r.end + 1) := by
        have hadd := Nat.add_lt_add_left hi r.start
        rw [← Nat.add_assoc, Nat.add_comm r.start (modulus w - r.start),
            Nat.sub_add_cancel (Nat.le_of_lt hs)] at hadd
        exact hadd
      have hsub_lt : r.start + i - modulus w < r.end + 1 := by
        have := sub_lt_sub_right_of_lt hhi hge_m
        rwa [Nat.add_sub_cancel_left] at this
      exact Nat.le_of_lt_succ hsub_lt

theorem nthValidVal_inj {w : Nat} {r : WrappingRange} (hwf : r.wf w) {i j : Nat}
    (hi : i < r.validCount w) (hj : j < r.validCount w)
    (heq : nthValidVal w r i = nthValidVal w r j) : i = j := by
  have hi_m : i < modulus w := Nat.lt_of_lt_of_le hi (validCount_le_modulus hwf)
  have hj_m : j < modulus w := Nat.lt_of_lt_of_le hj (validCount_le_modulus hwf)
  unfold nthValidVal at heq
  by_cases hi_s : r.start + i < modulus w
  · by_cases hj_s : r.start + j < modulus w
    · simp only [hi_s, hj_s, ↓reduceIte] at heq
      exact Nat.add_left_cancel heq
    · simp only [hi_s, hj_s, ↓reduceIte] at heq
      have hge_j : modulus w ≤ r.start + j := Nat.le_of_not_gt hj_s
      have hlt_j : r.start + j - modulus w < r.start := by
        have hsum : r.start + j < r.start + modulus w := Nat.add_lt_add_left hj_m r.start
        have := sub_lt_sub_right_of_lt hsum hge_j
        rwa [Nat.add_sub_cancel] at this
      have hge_i : r.start ≤ r.start + i := Nat.le_add_right r.start i
      rw [heq] at hge_i
      exact absurd (Nat.lt_of_le_of_lt hge_i hlt_j) (Nat.lt_irrefl _)
  · by_cases hj_s : r.start + j < modulus w
    · simp only [hi_s, hj_s, ↓reduceIte] at heq
      have hge_i : modulus w ≤ r.start + i := Nat.le_of_not_gt hi_s
      have hlt_i : r.start + i - modulus w < r.start := by
        have hsum : r.start + i < r.start + modulus w := Nat.add_lt_add_left hi_m r.start
        have := sub_lt_sub_right_of_lt hsum hge_i
        rwa [Nat.add_sub_cancel] at this
      have hge_j : r.start ≤ r.start + j := Nat.le_add_right r.start j
      rw [← heq] at hge_j
      exact absurd (Nat.lt_of_le_of_lt hge_j hlt_i) (Nat.lt_irrefl _)
    · simp only [hi_s, hj_s, ↓reduceIte] at heq
      have hge_i : modulus w ≤ r.start + i := Nat.le_of_not_gt hi_s
      have hge_j : modulus w ≤ r.start + j := Nat.le_of_not_gt hj_s
      exact Nat.add_left_cancel (eq_of_sub_eq_sub hge_i hge_j heq)

/-- **Niche-Exhaustion Impossibility Theorem (General Pigeonhole):**
Whenever `k > r.availableNiches w`, `NestedOptionVal w r k` has at least `2^w + 1`
distinct values, so NO injective encoding into `BitVec w` exists — forcing external
tag expansion beyond `w` bits. -/
theorem no_injective_encoding_when_niches_exhausted
    {w : Nat} {r : WrappingRange} {k : Nat}
    (hwf : r.wf w) (hexh : r.availableNiches w < k) :
    ∀ enc : NestedOptionVal w r k → BitVec w,
      ¬ (∀ x y, enc x = enc y → x = y) := by
  intro enc hinj
  have hsum : modulus w + 1 ≤ k + r.validCount w := by
    have h1 : r.availableNiches w + 1 ≤ k := hexh
    have h2 := Nat.add_le_add_right h1 (r.validCount w)
    rw [Nat.add_right_comm, Nat.add_comm (r.availableNiches w) (r.validCount w),
        validCount_add_availableNiches hwf] at h2
    exact h2
  let embed : Fin (modulus w + 1) → NestedOptionVal w r k := fun idx =>
    if hlt : idx.val < k then
      .noneAt ⟨idx.val, hlt⟩
    else
      let j := idx.val - k
      have hj : j < r.validCount w := by
        have hlt_tot : idx.val < k + r.validCount w := Nat.lt_of_lt_of_le idx.isLt hsum
        have hk_le : k ≤ idx.val := Nat.le_of_not_gt hlt
        have := sub_lt_sub_right_of_lt hlt_tot hk_le
        rwa [Nat.add_sub_cancel_left] at this
      let raw := nthValidVal w r j
      have hraw_lt : raw < modulus w := nthValidVal_lt hwf hj
      have hraw_bv : r.containsBV (BitVec.ofNat w raw) = true := by
        unfold containsBV
        have htoNat : (BitVec.ofNat w raw).toNat = raw := by
          simp [BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt hraw_lt
        rw [htoNat]
        exact nthValidVal_contains hwf hj
      .payload (BitVec.ofNat w raw) hraw_bv
  have hembed_inj : ∀ a b : Fin (modulus w + 1), embed a = embed b → a = b := by
    intro a b heq
    dsimp only [embed] at heq
    by_cases ha : a.val < k
    · by_cases hb : b.val < k
      · simp only [ha, hb, ↓reduceDIte] at heq
        injection heq with hfin
        exact Fin.ext (congrArg (Fin.val (n := k)) hfin)
      · simp only [ha, hb, ↓reduceDIte] at heq
        cases heq
    · by_cases hb : b.val < k
      · simp only [ha, hb, ↓reduceDIte] at heq
        cases heq
      · simp only [ha, hb, ↓reduceDIte] at heq
        injection heq with hbv
        have hka : k ≤ a.val := Nat.le_of_not_gt ha
        have hkb : k ≤ b.val := Nat.le_of_not_gt hb
        have hja : a.val - k < r.validCount w := by
          have := sub_lt_sub_right_of_lt (Nat.lt_of_lt_of_le a.isLt hsum) hka
          rwa [Nat.add_sub_cancel_left] at this
        have hjb : b.val - k < r.validCount w := by
          have := sub_lt_sub_right_of_lt (Nat.lt_of_lt_of_le b.isLt hsum) hkb
          rwa [Nat.add_sub_cancel_left] at this
        have hnat : nthValidVal w r (a.val - k) = nthValidVal w r (b.val - k) := by
          have h1 := congrArg BitVec.toNat hbv
          simp only [BitVec.toNat_ofNat] at h1
          change nthValidVal w r (a.val - k) % modulus w = nthValidVal w r (b.val - k) % modulus w at h1
          rw [Nat.mod_eq_of_lt (nthValidVal_lt hwf hja),
              Nat.mod_eq_of_lt (nthValidVal_lt hwf hjb)] at h1
          exact h1
        have hsub_eq : a.val - k = b.val - k := nthValidVal_inj hwf hja hjb hnat
        exact Fin.ext (eq_of_sub_eq_sub hka hkb hsub_eq)
  let f : Fin (modulus w + 1) → Fin (modulus w) := fun idx =>
    let bv := enc (embed idx)
    ⟨bv.toNat, bv.isLt⟩
  apply no_injective_fin_succ_to_fin (modulus w) f
  intro a b hfab
  have hbv : enc (embed a) = enc (embed b) := BitVec.eq_of_toNat_eq (congrArg Fin.val hfab)
  exact hembed_inj a b (hinj _ _ hbv)

/-! ## Section 6: `CheckEnums` (`-Z ub-checks=yes`) vs. Miri Validity Model -/

/-- Destination type shapes for raw `Rvalue::Cast(CastKind::Transmute, op, ty)`,
distinguishing enum ADTs (inspected by `CheckEnums`) from `TyKind::Pat` and
transparent struct wrappers (`NonZero<T>`, `NonNull<T>`, `BoxRaw<T>`).
Intentionally omits `deriving DecidableEq, Repr` to prevent Lean from emitting
recursive `._unsafe_rec` compiler helpers on the recursive inductive type. -/
inductive MirDstTy where
  | baseInt (w : Nat)
  | patRange (w : Nat) (r : WrappingRange)
  | patNotNull (w : Nat)
  | transparentStruct (inner : MirDstTy)
  | enumNiche (w : Nat) (r : WrappingRange)

/-- Miri `ValidityVisitor` check (`compiler/rustc_const_eval/src/interpret/validity.rs:1015-1070, 1497-1535`),
recursing through transparent struct fields (e.g., `NonZero<u8>` `.0.0`) via
`MirDstTy.rec` (no `._unsafe_rec` generated). -/
noncomputable def miriValid (ty : MirDstTy) (bits : Nat) : Bool :=
  MirDstTy.rec
    (fun w => decide (bits < modulus w))
    (fun w r => decide (bits < modulus w) && r.contains bits)
    (fun w => decide (bits < modulus w) && decide (1 ≤ bits))
    (fun _ ih => ih)
    (fun w r => decide (bits < modulus w) && r.contains bits)
    ty

/-- `rustc`'s `-Z ub-checks=yes` `CheckEnums` pass
(`compiler/rustc_mir_transform/src/check_enums.rs:167-237`): checks ONLY
`ty::Adt(adt_def, _)` where `adt_def.is_enum()`; returns early (accepts without
inserting a runtime check) on `TyKind::Pat` and `#[repr(transparent)]` structs. -/
def checkEnumsAccepts (ty : MirDstTy) (bits : Nat) : Bool :=
  match ty with
  | .enumNiche w r => decide (bits < modulus w) && r.contains bits
  | .baseInt _ | .patRange _ _ | .patNotNull _ | .transparentStruct _ => true

/-- General incompleteness theorem: `CheckEnums` accepts EVERY invalid raw
transmute whose destination is a `TyKind::Pat` or transparent wrapper struct. -/
theorem checkEnums_incomplete_on_pat_and_transparent {ty : MirDstTy} {bits : Nat}
    (hnonEnum : ∀ w r, ty ≠ .enumNiche w r)
    (hbad : miriValid ty bits = false) :
    checkEnumsAccepts ty bits = true ∧ miriValid ty bits = false := by
  refine ⟨?_, hbad⟩
  cases ty with
  | enumNiche w r => exact absurd rfl (hnonEnum w r)
  | baseInt _ => rfl
  | patRange _ _ => rfl
  | patNotNull _ => rfl
  | transparentStruct _ => rfl

/-! ## Section 7: Concrete Ranges, `rustc` Niche-Byte Verification, & 3 Counterexamples -/

/-- `pattern_type!(u8 is 1..=10)`. -/
def pat1To10Range : WrappingRange := { start := 1, «end» := 10 }

/-- `pattern_type!(u8 is 1..=254)` (2 available niches: `0` and `255`). -/
def pat254Range : WrappingRange := { start := 1, «end» := 254 }

/-- `NonZero<u8>` inner `pattern_type!(u8 is 1..)` (`1..=255`, 1 niche: `0`). -/
def nonZeroU8Range : WrappingRange := { start := 1, «end» := 255 }

/-- `pattern_type!(i8 is ..=-1 | 1..)` represented as wrapping `1..=255` on `u8`. -/
def signedNonZeroI8Range : WrappingRange := { start := 1, «end» := 255 }

/-- `NonZero<u8>` = `transparentStruct (transparentStruct (patRange 8 {1, 255}))`
(`.0` = `NonZeroU8Inner`, `.0.0` = `pattern_type!(u8 is 1..)`). -/
def nonZeroU8Ty : MirDstTy :=
  .transparentStruct (.transparentStruct (.patRange 8 nonZeroU8Range))

/-- `Option<Pat1To10>` enum layout (`valid_range = 0..=10`, `None = 0`). -/
def optPat1To10Ty : MirDstTy :=
  .enumNiche 8 { start := 0, «end» := 10 }

/-- Exact match with `rustc` empirical `NICHE_BYTES` for 3 nested `Option`s over `Pat1To10`:
`Option::None = 0`, `Option<Option>::None = 255`, `Option<Option<Option>>::None = 254`. -/
theorem pat1To10_three_nested_options_exact_tags :
    nestOptionIter 8 pat1To10Range 3 = some ({ start := 254, «end» := 10 }, [254, 255, 0]) := rfl

/-- Exact match with `rustc` empirical `NICHE_BYTES` for `Pat254` (`0`, then `255`, then exhausted). -/
theorem pat254_niche_stacking_and_exhaustion :
    nestOptionIter 8 pat254Range 2 = some ({ start := 255, «end» := 254 }, [255, 0]) ∧
    nestOptionIter 8 pat254Range 3 = none := ⟨rfl, rfl⟩

/-- **Counterexample 1 (`ce1_invalid_pat_transmute_miscompiles_under_llvm_range_attr`):**
Constructively exhibits `v = 11#8` for `Pat1To10` (`1..=10`): valid as `u8`,
invalid for `Pat1To10`, trapped by the guarded source (`take_pat_u8`), yet
silently returned as `11#8` after LLVM `range(i8 1, 11)` dead-branch folding. -/
theorem ce1_invalid_pat_transmute_miscompiles_under_llvm_range_attr :
    let bad : BitVec 8 := BitVec.ofNat 8 11
    (WrappingRange.full 8).containsBV bad = true ∧
    pat1To10Range.containsBV bad = false ∧
    llvmHalfOpenContains 1 11 bad.toNat = false ∧
    evalRangeGuarded pat1To10Range id bad = .trap ∧
    evalLlvmRangeFolded id bad = .ret bad ∧
    evalRangeGuarded pat1To10Range id bad ≠ evalLlvmRangeFolded id bad := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  cases h

/-- **Counterexample 2 (`ce2_niche_exhaustion_forces_tag_expansion`):**
Constructively proves niche exhaustion for BOTH `Option<Option<NonZero<u8>>>`
(`availableNiches = 1`, exhausted at `k = 2`) and `Option<Option<Option<Pat254>>>`
(`availableNiches = 2`, exhausted at `k = 3`): `nestOptionIter` returns `none`,
and NO injective encoding into `BitVec 8` (`1` byte) exists, forcing external tag
expansion (`size_of > 1`). -/
theorem ce2_niche_exhaustion_forces_tag_expansion :
    nestOptionIter 8 nonZeroU8Range 1 = some ({ start := 0, «end» := 255 }, [0]) ∧
    nestOptionIter 8 nonZeroU8Range 2 = none ∧
    (∀ enc : NestedOptionVal 8 nonZeroU8Range 2 → BitVec 8,
      ¬ (∀ x y, enc x = enc y → x = y)) ∧
    nestOptionIter 8 pat254Range 2 = some ({ start := 255, «end» := 254 }, [255, 0]) ∧
    nestOptionIter 8 pat254Range 3 = none ∧
    (∀ enc : NestedOptionVal 8 pat254Range 3 → BitVec 8,
      ¬ (∀ x y, enc x = enc y → x = y)) := by
  have hwfNZ : nonZeroU8Range.wf 8 := ⟨Nat.succ_le_succ (Nat.zero_le _), by decide, by decide⟩
  have hwfP254 : pat254Range.wf 8 := ⟨Nat.succ_le_succ (Nat.zero_le _), by decide, by decide⟩
  have hexhNZ : nonZeroU8Range.availableNiches 8 < 2 := by decide
  have hexhP254 : pat254Range.availableNiches 8 < 3 := by decide
  exact ⟨rfl, rfl, no_injective_encoding_when_niches_exhausted hwfNZ hexhNZ,
         rfl, rfl, no_injective_encoding_when_niches_exhausted hwfP254 hexhP254⟩

/-- **Counterexample 3 (`ce3_ub_checks_bypass_misses_raw_transmute_to_nonzero`):**
Constructively proves that `-Z ub-checks=yes` (`CheckEnums`) misses raw
`transmute` into `Pat1To10` (`11`), `PatNonNull` (`0`), and `NonZero<u8>` (`0`)
while Miri flags all three as UB, contrasting with `Option<Pat1To10>` (`99`)
where `CheckEnums` DOES catch the invalid enum tag. -/
theorem ce3_ub_checks_bypass_misses_raw_transmute_to_nonzero :
    (checkEnumsAccepts (.patRange 8 pat1To10Range) 11 = true ∧
      miriValid (.patRange 8 pat1To10Range) 11 = false) ∧
    (checkEnumsAccepts (.patNotNull 64) 0 = true ∧
      miriValid (.patNotNull 64) 0 = false) ∧
    (checkEnumsAccepts nonZeroU8Ty 0 = true ∧
      miriValid nonZeroU8Ty 0 = false) ∧
    (checkEnumsAccepts optPat1To10Ty 99 = false ∧
      miriValid optPat1To10Ty 99 = false) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end WrappingRange

end PatternTypesSoundness
