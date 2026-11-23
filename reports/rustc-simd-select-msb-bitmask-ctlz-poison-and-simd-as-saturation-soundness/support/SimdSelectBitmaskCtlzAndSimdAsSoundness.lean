prelude
import Init.Core
import Init.Notation
import Init.NotationExtra
import Init.Tactics
import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Int.Basic
import Init.Data.List.Basic
import Init.Data.List.Notation
import Init.Data.Option.Basic
import Init.WF
import Init.WFTactics

/-!
# Soundness of Rust SIMD Mask Selection, Bitmask Packing, Bit-Count Poison Refinement, and Saturating Float-to-Int Lowering

This module formalizes in constructive, kernel-checked Lean `v4.34.1` (using only locked
`Init.*` foundation imports, zero `sorry`, zero `Classical.choice`, zero `omega`,
zero `bv_decide`, zero `native_decide`, zero `partial def`, and zero `._unsafe_rec`
auxiliaries) the four semantic contracts connecting `rustc_codegen_llvm` / `rustc_codegen_ssa`
lowerings and CTFE / Miri abstract-machine semantics:

1. **Module 1 (`simd_select` MSB Extraction vs. All-0/All-1 Mask Validity):**
   `rustc_const_eval` / Miri requires every SIMD mask lane to be `0` (`false`) or
   all-ones (`2^w - 1 = -1` signed), rejecting any other bit pattern (such as `1` or
   `-2`) as immediate UB. `rustc_codegen_llvm`'s `vector_mask_to_bitmask` lowers masks via
   logical right shift (`lshr (w - 1)`) and truncation (`trunc to <N x i1>`), whereas
   scalar boolean array extraction inspects LSB (`& 1`) and hardware bitwise blends mix
   all `w` bits. We prove `{0, 2^w - 1}` is the unique fixed-point domain on which all
   three agree, prove `Outcome.refines` from Miri to LLVM MSB lowering (both `simd_select`
   and `simd_reduce_{all,any}`), and exhibit exact counterexamples on `1` and `-2`.

2. **Module 2 (`simd_select_bitmask` <-> `vector_mask_to_bitmask` Little-Endian Bijection):**
   Models multi-byte `[u8; K]` little-endian bitmasks and proves bit `8 * k + b` indexes
   lane `8 * k + b` (`b < 8`), establishing exact `bools <-> [u8; K]` round-trip Galois
   bijections across arbitrary non-power-of-two lane counts `N <= 8 * K`, upper padding-bit
   invariance (`i >= N`), `simd_select_bitmask` / `simd_bitmask` round-trip equivalence with
   `simd_select`, and a formal counterexample capturing the x86-64 SSE2/AVX2 `<10 x i8>`
   byte-0 replication miscompilation observed in LLVM 22.1.6.

3. **Module 3 (`ctlz`/`cttz` vs. `ctlz_nonzero`/`cttz_nonzero` Poison & Range Refinement):**
   Models `ctlzStep` and `cttzStep` with full bit-level leading/trailing-zero correctness
   lemmas, proving total `[0, W]` bounds when `is_zero_poison = false` (including
   `simd_ctlz` / `simd_cttz`), strict `[0, W)` bounds when `is_zero_poison = true` and
   execution does not hit UB (`x != 0`), downstream `< W` branch elimination soundness,
   top-bit zeroing (`bitAt n (p + j) = false` at `W = pow2 p`, e.g., bit 5 at `W = 32`),
   and `x = 0` divergence witnesses.

4. **Module 4 (`simd_as` Total Saturation vs. `simd_cast` / `float_to_int_unchecked`):**
   Models extended IEEE floating-point numbers (`nan`, `posInf`, `negInf`, `finite`)
   against two's-complement signed and unsigned integer targets, proving exact equivalence
   between truncated-toward-zero range bounds `[MIN, MAX]` and Rust's open-interval
   preconditions `(-2^(w-1) - 1, 2^(w-1))` and `(-1, 2^w)`, total clamped saturation of
   `simd_as`, UB refinement `simd_cast -> simd_as`, and open-boundary differential witnesses
   (`-128.9` ok vs. `-129.0` UB for `i8`; `-0.999` ok vs. `-1.0` UB for `u8`; `NaN -> 0`).

5. **Module 5 (Unified End-to-End Verification Contract):**
   Bundles all four intrinsic-family theorems into a single top-level theorem.
-/

namespace SimdSelectBitmaskCtlzAndSimdAsSoundness

/-! ## Module 0: Pure Foundation Arithmetic, Bit Extraction, and Outcome Refinement -/

/-- Outcome of an abstract-machine or LLVM IR semantics evaluation (`ok` or `ub`). -/
inductive Outcome (α : Type) where
  | ok (val : α)
  | ub

/-- Refinement relation for UB-bearing semantics: whenever the specification succeeds with
`a`, the lowering/implementation must also succeed with `a`; when the specification is
`Outcome.ub`, any implementation behavior refines it. -/
noncomputable def Outcome.refines {α : Type} (spec impl : Outcome α) : Prop :=
  ∀ a : α, spec = Outcome.ok a → impl = Outcome.ok a

theorem Outcome.refines_refl {α : Type} (x : Outcome α) : Outcome.refines x x := by
  intro a h
  exact h

theorem Outcome.refines_trans {α : Type} {x y z : Outcome α}
    (hxy : Outcome.refines x y) (hyz : Outcome.refines y z) : Outcome.refines x z := by
  intro a hx
  exact hyz a (hxy a hx)

theorem Outcome.refines_ub {α : Type} (impl : Outcome α) : Outcome.refines Outcome.ub impl := by
  intro a h
  cases h

theorem Outcome.refines_ok_iff {α : Type} {a : α} {impl : Outcome α} :
    Outcome.refines (Outcome.ok a) impl ↔ impl = Outcome.ok a := by
  constructor
  · intro h
    exact h a rfl
  · intro h b hb
    injection hb with hba
    subst hba
    exact h

/-- Locked `Init` prefix arithmetic bridge lemmas for `Nat`, `Bool`, and `List`. -/
theorem nat_eq_zero_of_lt_succ {n : Nat} (h : n < 1) : n = 0 := by
  cases n with
  | zero => rfl
  | succ k => cases Nat.not_lt_zero k (Nat.lt_of_succ_lt_succ h)

theorem nat_lt_of_mul_lt_mul_left {a b c : Nat} (h : c * a < c * b) : a < b := by
  cases Nat.decLt a b with
  | isTrue hab => exact hab
  | isFalse hnot =>
    have hle : b ≤ a := Nat.le_of_not_lt hnot
    have hcm : c * b ≤ c * a := Nat.mul_le_mul_left c hle
    exact False.elim (Nat.not_lt_of_le hcm h)

theorem nat_div_add_mod (m n : Nat) : n * Nat.div m n + Nat.mod m n = m :=
  Nat.div_add_mod m n

theorem nat_mod_lt (x : Nat) {y : Nat} (hy : 0 < y) : Nat.mod x y < y :=
  Nat.mod_lt x hy

theorem nat_div_eq_of_lt {a b : Nat} (h : a < b) : Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

theorem nat_add_mul_div_left (x z : Nat) {y : Nat} (hy : 0 < y) :
    Nat.div (x + y * z) y = Nat.div x y + z :=
  Nat.add_mul_div_left x z hy

theorem nat_add_mul_mod_self_left (x y z : Nat) :
    Nat.mod (x + y * z) y = Nat.mod x y :=
  Nat.add_mul_mod_self_left x y z

theorem nat_zero_div (b : Nat) : Nat.div 0 b = 0 :=
  Nat.zero_div b

theorem nat_zero_mod (b : Nat) : Nat.mod 0 b = 0 :=
  Nat.zero_mod b

theorem nat_div_one (x : Nat) : Nat.div x 1 = x :=
  Nat.div_one x

theorem nat_mod_one (x : Nat) : Nat.mod x 1 = 0 :=
  Nat.mod_one x

theorem nat_mul_mod_right (m n : Nat) : Nat.mod (m * n) m = 0 :=
  Nat.mul_mod_right m n

theorem nat_mul_div_right (n : Nat) {m : Nat} (hm : 0 < m) : Nat.div (m * n) m = n :=
  Nat.mul_div_right n hm

theorem bool_and_eq_true_elim {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> cases h <;> exact ⟨rfl, rfl⟩

theorem list_length_map {α β : Type} (f : α → β) :
    ∀ l : List α, (l.map f).length = l.length
  | [] => rfl
  | _ :: tl => congrArg Nat.succ (list_length_map f tl)

theorem list_mem_map_elim {α β : Type} (f : α → β) :
    ∀ (y : β) (l : List α), y ∈ l.map f → ∃ x, x ∈ l ∧ f x = y
  | _, [], hy => nomatch hy
  | y, x :: tl, hy => by
    cases hy with
    | head => exact ⟨x, List.Mem.head tl, rfl⟩
    | tail _ htl =>
      have ih := list_mem_map_elim f y tl htl
      cases ih with
      | intro x' hx' => exact ⟨x', List.Mem.tail x hx'.1, hx'.2⟩

theorem list_all_eq_true_of {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ x, x ∈ l → p x = true) → l.all p = true
  | [], _ => rfl
  | x :: tl, hall => by
    have hx : p x = true := hall x (List.Mem.head tl)
    have htl : tl.all p = true :=
      list_all_eq_true_of p tl (fun y hy => hall y (List.Mem.tail x hy))
    unfold List.all
    rw [hx, htl]
    rfl

/-- Total list indexing helper avoiding partial `get!` notation. -/
noncomputable def listGetD {α : Type} (d : α) : List α → Nat → α
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, i + 1 => listGetD d xs i

/-- Safe optional list lookup. -/
noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, i + 1 => listGet? xs i

theorem listGetD_cons_zero {α : Type} (d x : α) (xs : List α) :
    listGetD d (x :: xs) 0 = x := rfl

theorem listGetD_cons_succ {α : Type} (d x : α) (xs : List α) (i : Nat) :
    listGetD d (x :: xs) (i + 1) = listGetD d xs i := rfl

theorem listGet?_lt_some {α : Type} :
    ∀ (xs : List α) (i : Nat), i < xs.length → ∃ v, listGet? xs i = some v
  | [], _, hi => nomatch hi
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, i + 1, hi =>
    have hlt : i < xs.length := Nat.lt_of_succ_lt_succ hi
    listGet?_lt_some xs i hlt

theorem listGetD_eq_of_listGet? {α : Type} (d : α) :
    ∀ (xs : List α) (i : Nat) (v : α), listGet? xs i = some v → listGetD d xs i = v
  | [], _, _, h => nomatch h
  | _ :: _, 0, _, h => by
    cases h
    rfl
  | _ :: xs, i + 1, v, h => listGetD_eq_of_listGet? d xs i v h

/-- Recursive `2^n` using only basic `Nat` arithmetic. -/
noncomputable def pow2 : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * pow2 n

theorem pow2_zero : pow2 0 = 1 := rfl

theorem pow2_succ (n : Nat) : pow2 (n + 1) = 2 * pow2 n := rfl

theorem pow2_pos : ∀ n : Nat, 0 < pow2 n
  | 0 => Nat.zero_lt_one
  | n + 1 => by
    unfold pow2
    exact Nat.mul_pos (by decide) (pow2_pos n)

theorem pow2_ge_one (n : Nat) : 1 ≤ pow2 n :=
  pow2_pos n

theorem pow2_ge_two {n : Nat} (hn : 1 ≤ n) : 2 ≤ pow2 n := by
  cases n with
  | zero => cases hn
  | succ k =>
    unfold pow2
    exact Nat.mul_le_mul_left 2 (pow2_ge_one k)

theorem pow2_add : ∀ a b : Nat, pow2 (a + b) = pow2 a * pow2 b
  | a, 0 => by
    rw [Nat.add_zero]
    change pow2 a = pow2 a * 1
    rw [Nat.mul_one]
  | a, b + 1 => by
    have ih := pow2_add a b
    have hp : pow2 ((a + b) + 1) = 2 * pow2 (a + b) := rfl
    have hp2 : pow2 (b + 1) = 2 * pow2 b := rfl
    rw [← Nat.add_assoc, hp, hp2, ih, Nat.mul_left_comm]

theorem pow2_add_comm_mul (a b : Nat) : pow2 (a + b) = pow2 b * pow2 a := by
  rw [pow2_add, Nat.mul_comm]

theorem pow2_le_succ (k : Nat) : pow2 k ≤ pow2 (k + 1) := by
  have h1 : 1 ≤ 2 := by decide
  have hm := Nat.mul_le_mul_right (pow2 k) h1
  rw [Nat.one_mul] at hm
  exact hm

theorem pow2_mono : ∀ {a b : Nat}, a ≤ b → pow2 a ≤ pow2 b := by
  intro a b h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (pow2_le_succ _)

theorem pow2_strict_mono {a b : Nat} (h : a < b) : pow2 a < pow2 b := by
  cases b with
  | zero => cases h
  | succ k =>
    have hak : a ≤ k := Nat.le_of_lt_succ h
    have hle : pow2 a ≤ pow2 k := pow2_mono hak
    have hpos : 0 < pow2 k := pow2_pos k
    have hlt : pow2 k < 2 * pow2 k := by
      rw [Nat.two_mul]
      exact Nat.lt_add_of_pos_left hpos
    exact Nat.lt_of_le_of_lt hle hlt

theorem pow2_le_mul {i m : Nat} (h : i ≤ m) : ∃ t, pow2 m = pow2 i * t := by
  induction h with
  | refl => exact ⟨1, (Nat.mul_one _).symm⟩
  | step _ ih =>
    cases ih with
    | intro t ht =>
      have hp : ∀ k, pow2 (k + 1) = 2 * pow2 k := fun _ => rfl
      rw [hp, ht, Nat.mul_left_comm]
      exact ⟨2 * t, rfl⟩

theorem pow2_succ_decomp (i m : Nat) (h : i < m) : ∃ d, pow2 (m + 1) = pow2 i * (2 * d) := by
  cases pow2_le_mul (Nat.le_of_lt h) with
  | intro t ht =>
    have hp : pow2 (m + 1) = 2 * pow2 m := rfl
    have hres : pow2 (m + 1) = pow2 i * (2 * t) := by
      rw [hp, ht, Nat.mul_left_comm]
    exact ⟨t, hres⟩

/-- Maximum unsigned value of a `w`-bit lane (`2^w - 1`). -/
noncomputable def allOnes (w : Nat) : Nat := pow2 w - 1

theorem allOnes_zero : allOnes 0 = 0 := rfl

theorem allOnes_add_one_eq_pow2 (w : Nat) : allOnes w + 1 = pow2 w :=
  Nat.sub_add_cancel (pow2_ge_one w)

theorem allOnes_lt_pow2 (w : Nat) : allOnes w < pow2 w := by
  exact Nat.sub_lt (pow2_pos w) Nat.zero_lt_one

theorem allOnes_pos_of_pos {w : Nat} (hw : 1 ≤ w) : 0 < allOnes w := by
  have h2 : 2 ≤ pow2 w := pow2_ge_two hw
  unfold allOnes
  exact Nat.sub_pos_of_lt h2

theorem lt_pow2_of_le_allOnes {w x : Nat} (h : x ≤ allOnes w) : x < pow2 w :=
  Nat.lt_of_le_of_lt h (allOnes_lt_pow2 w)

theorem le_allOnes_of_lt_pow2 {w x : Nat} (h : x < pow2 w) : x ≤ allOnes w :=
  Nat.le_sub_one_of_lt h

theorem mul_add_lt_mul {a b r1 r2 : Nat} (hr1 : r1 < a) (hr2 : r2 < b) :
    a * r2 + r1 < a * b := by
  have hr2p : r2 + 1 ≤ b := hr2
  have h1 : a * r2 + r1 < a * r2 + a := Nat.add_lt_add_left hr1 (a * r2)
  have h2 : a * r2 + a = a * (r2 + 1) := by rw [Nat.mul_succ]
  have h3 : a * (r2 + 1) ≤ a * b := Nat.mul_le_mul_left a hr2p
  rw [h2] at h1
  exact Nat.lt_of_lt_of_le h1 h3

theorem nat_add_div_pow_of_lt {x y m : Nat} (hx : x < m) (hm : 0 < m) :
    Nat.div (x + m * y) m = y := by
  rw [nat_add_mul_div_left x y hm]
  rw [nat_div_eq_of_lt hx, Nat.zero_add]

theorem nat_add_mod_pow_of_lt {x y m : Nat} (hx : x < m) :
    Nat.mod (x + m * y) m = x := by
  rw [nat_add_mul_mod_self_left]
  exact nat_mod_eq_of_lt hx

theorem nat_div_add_mul_two (b y : Nat) (hb : b < 2) :
    Nat.div (b + 2 * y) 2 = y :=
  nat_add_div_pow_of_lt hb (by decide)

theorem nat_mod_add_mul_two (b y : Nat) (hb : b < 2) :
    Nat.mod (b + 2 * y) 2 = b :=
  nat_add_mod_pow_of_lt hb

theorem nat_div_div_eq_div_mul (x a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    Nat.div (Nat.div x a) b = Nat.div x (a * b) := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  let r1 := Nat.mod x a
  let q1 := Nat.div x a
  let r2 := Nat.mod q1 b
  let q2 := Nat.div q1 b
  have hx1 : a * q1 + r1 = x := nat_div_add_mod x a
  have hq1 : b * q2 + r2 = q1 := nat_div_add_mod q1 b
  have hr1 : r1 < a := nat_mod_lt x ha
  have hr2 : r2 < b := nat_mod_lt q1 hb
  have hrem : a * r2 + r1 < a * b := mul_add_lt_mul hr1 hr2
  have hx : (a * r2 + r1) + (a * b) * q2 = x := by
    rw [Nat.add_comm (a * r2 + r1) _]
    rw [← Nat.add_assoc, Nat.mul_assoc a b q2]
    rw [← Nat.left_distrib a (b * q2) r2]
    rw [hq1]
    exact hx1
  have hl1 : Nat.div ((a * r2 + r1) + (a * b) * q2) a = r2 + b * q2 := by
    rw [Nat.mul_assoc a b q2, Nat.add_comm (a * r2) r1, Nat.add_assoc r1 (a * r2) (a * (b * q2))]
    rw [← Nat.left_distrib a r2 (b * q2)]
    exact nat_add_div_pow_of_lt hr1 ha
  have hl : Nat.div (Nat.div ((a * r2 + r1) + (a * b) * q2) a) b = q2 := by
    rw [hl1]
    exact nat_add_div_pow_of_lt hr2 hb
  have hr : Nat.div ((a * r2 + r1) + (a * b) * q2) (a * b) = q2 :=
    nat_add_div_pow_of_lt hrem hab
  rw [hx] at hl hr
  exact hl.trans hr.symm

theorem nat_mod_mul_eq (x a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    Nat.mod x (a * b) = a * Nat.mod (Nat.div x a) b + Nat.mod x a := by
  let r1 := Nat.mod x a
  let q1 := Nat.div x a
  let r2 := Nat.mod q1 b
  let q2 := Nat.div q1 b
  have hx1 : a * q1 + r1 = x := nat_div_add_mod x a
  have hq1 : b * q2 + r2 = q1 := nat_div_add_mod q1 b
  have hr1 : r1 < a := nat_mod_lt x ha
  have hr2 : r2 < b := nat_mod_lt q1 hb
  have hrem : a * r2 + r1 < a * b := mul_add_lt_mul hr1 hr2
  have hx : (a * r2 + r1) + (a * b) * q2 = x := by
    rw [Nat.add_comm (a * r2 + r1) _]
    rw [← Nat.add_assoc, Nat.mul_assoc a b q2]
    rw [← Nat.left_distrib a (b * q2) r2]
    rw [hq1]
    exact hx1
  have hmod : Nat.mod ((a * r2 + r1) + (a * b) * q2) (a * b) = a * r2 + r1 :=
    nat_add_mod_pow_of_lt hrem
  rw [hx] at hmod
  exact hmod

/-- Extract bit `i` (0 = LSB) of a natural number `x` using prefix `Nat.div`/`Nat.mod`. -/
noncomputable def bitAt (x i : Nat) : Bool :=
  decide (Nat.mod (Nat.div x (pow2 i)) 2 == 1)

theorem bitAt_zero_nat (i : Nat) : bitAt 0 i = false := by
  unfold bitAt
  rw [nat_zero_div, nat_zero_mod]
  decide

theorem bitAt_div_pow2 (x a b : Nat) :
    bitAt (Nat.div x (pow2 a)) b = bitAt x (a + b) := by
  unfold bitAt
  rw [nat_div_div_eq_div_mul x (pow2 a) (pow2 b) (pow2_pos a) (pow2_pos b)]
  rw [← pow2_add a b]

theorem bitAt_div_two (x b : Nat) :
    bitAt (Nat.div x 2) b = bitAt x (b + 1) := by
  have h := bitAt_div_pow2 x 1 b
  have hp1 : pow2 1 = 2 := rfl
  rw [hp1] at h
  rw [Nat.add_comm 1 b] at h
  exact h

theorem bitAt_add_pow2_mul_low (x y : Nat) :
    ∀ {n i : Nat}, i < n → bitAt (x + pow2 n * y) i = bitAt x i := by
  intro n i hi
  cases hi with
  | refl =>
    unfold bitAt
    have hp1 : pow2 1 = 2 := rfl
    have hp : pow2 (i + 1) = pow2 i * 2 := by
      rw [pow2_add_comm_mul, hp1, Nat.mul_comm 2 (pow2 i)]
    rw [hp, Nat.mul_assoc]
    rw [nat_add_mul_div_left x (2 * y) (pow2_pos i)]
    rw [nat_add_mul_mod_self_left]
  | step hm =>
    rename_i m
    have hstep := pow2_succ_decomp i m hm
    cases hstep with
    | intro d hd =>
      unfold bitAt
      rw [hd, Nat.mul_assoc]
      rw [nat_add_mul_div_left x (2 * d * y) (pow2_pos i)]
      rw [Nat.mul_assoc 2 d y]
      rw [nat_add_mul_mod_self_left]

theorem bitAt_add_pow2_mul_high {x y n : Nat} (hx : x < pow2 n) (k : Nat) :
    bitAt (x + pow2 n * y) (n + k) = bitAt y k := by
  rw [← bitAt_div_pow2]
  rw [nat_add_div_pow_of_lt hx (pow2_pos n)]

theorem bitAt_mod_pow2_low (x n : Nat) {i : Nat} (hi : i < n) :
    bitAt (Nat.mod x (pow2 n)) i = bitAt x i := by
  let m := Nat.mod x (pow2 n)
  let q := Nat.div x (pow2 n)
  have hx : m + pow2 n * q = x := by
    rw [Nat.add_comm]
    exact nat_div_add_mod x (pow2 n)
  have hr := bitAt_add_pow2_mul_low m q hi
  rw [hx] at hr
  exact hr.symm

theorem bitAt_mod_pow2_high (x n k : Nat) :
    bitAt (Nat.mod x (pow2 n)) (n + k) = false := by
  unfold bitAt
  have hlt : Nat.mod x (pow2 n) < pow2 (n + k) :=
    Nat.lt_of_lt_of_le (nat_mod_lt x (pow2_pos n)) (pow2_mono (Nat.le_add_right n k))
  rw [nat_div_eq_of_lt hlt, nat_zero_mod]
  decide

theorem bitAt_lt_pow2_zero {x n : Nat} (hx : x < pow2 n) (k : Nat) :
    bitAt x (n + k) = false := by
  rw [← nat_mod_eq_of_lt hx]
  exact bitAt_mod_pow2_high x n k

theorem allOnes_decomp (k : Nat) : allOnes (k + 1) = allOnes k + pow2 k := by
  unfold allOnes
  have h2 : 2 * pow2 k = pow2 k + pow2 k := Nat.two_mul (pow2 k)
  have h1 : pow2 (k + 1) = pow2 k + pow2 k := (pow2_succ k).trans h2
  rw [h1]
  have hk : 1 ≤ pow2 k := pow2_ge_one k
  rw [Nat.add_sub_assoc hk (pow2 k)]
  rw [Nat.add_comm (pow2 k) (pow2 k - 1)]

theorem bitAt_allOnes_lt : ∀ {w i : Nat}, i < w → bitAt (allOnes w) i = true
  | 0, i, hi => nomatch hi
  | w + 1, i, hi => by
    rw [allOnes_decomp w]
    have hc : i < w ∨ i = w := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
    cases hc with
    | inl hlt =>
      rw [← Nat.mul_one (pow2 w)]
      rw [bitAt_add_pow2_mul_low (allOnes w) 1 hlt]
      exact bitAt_allOnes_lt hlt
    | inr heq =>
      subst heq
      have h1 : allOnes i + pow2 i = allOnes i + pow2 i * 1 := by rw [Nat.mul_one]
      rw [h1]
      have hsub : i = i + 0 := (Nat.add_zero i).symm
      have hr := bitAt_add_pow2_mul_high (y := 1) (allOnes_lt_pow2 i) 0
      rw [← hsub] at hr
      rw [hr]
      decide

theorem bitAt_allOnes_ge {w k : Nat} : bitAt (allOnes w) (w + k) = false :=
  bitAt_lt_pow2_zero (allOnes_lt_pow2 w) k

theorem mod_two_lt_two (x : Nat) : Nat.mod x 2 < 2 :=
  nat_mod_lt x (by decide)

theorem eq_zero_of_lt_pow2_succ_div_eq_zero_mod_eq_zero {w x : Nat}
    (hx : x < pow2 (w + 1)) (hbit : bitAt x w = false) (hmod : Nat.mod x (pow2 w) = 0) :
    x = 0 := by
  let q := Nat.div x (pow2 w)
  let r := Nat.mod x (pow2 w)
  have hdm0 : pow2 w * q + r = x := nat_div_add_mod x (pow2 w)
  have hq2 : q < 2 := by
    have hle : pow2 w * q ≤ pow2 w * q + r := Nat.le_add_right _ _
    rw [hdm0] at hle
    have hlt2 : pow2 w * q < 2 * pow2 w := by
      rw [← pow2_succ w]
      exact Nat.lt_of_le_of_lt hle hx
    rw [Nat.mul_comm 2 (pow2 w)] at hlt2
    exact nat_lt_of_mul_lt_mul_left hlt2
  have hqm : Nat.mod q 2 = q := nat_mod_eq_of_lt hq2
  have hne1 : q ≠ 1 := by
    intro heq
    unfold bitAt at hbit
    change decide (Nat.mod q 2 == 1) = false at hbit
    rw [hqm, heq] at hbit
    cases hbit
  have hq0 : q = 0 := by
    cases hq : q with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => exact False.elim (hne1 hq)
      | succ k2 =>
        rw [hq] at hq2
        exact False.elim (Nat.not_lt_zero k2 (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hq2)))
  have hr0 : r = 0 := hmod
  rw [hq0, hr0, Nat.mul_zero, Nat.zero_add] at hdm0
  exact hdm0.symm

/-! ## Module 1: `simd_select` MSB Lowering vs. Miri `{0, -1}` Validity & `simd_reduce_{all,any}` -/

/-- `vector_mask_to_bitmask` MSB extraction (`lshr (w - 1)` followed by `trunc to i1`). -/
noncomputable def msbLane (w x : Nat) : Bool :=
  if w == 0 then false else bitAt x (w - 1)

/-- Scalar array extraction (`Mask::to_array` LSB check `(x & 1) == 1`). -/
noncomputable def lsbLane (x : Nat) : Bool :=
  bitAt x 0

/-- Bitwise vector mask blend at bit `j` (models ARM NEON `vbsl` bit-by-bit selection). -/
noncomputable def bitwiseSelectBit (w maskLane aLane bLane j : Nat) : Bool :=
  if j < w then
    if bitAt maskLane j then bitAt aLane j else bitAt bLane j
  else false

/-- `rustc_const_eval` / Miri `simd_element_to_bool`: accepts ONLY `0` (all-0-bits) or
`allOnes w` (all-1-bits / `-1` signed), rejecting any other bit pattern as UB (`none`). -/
noncomputable def decodeSimdMaskLane? (w lane : Nat) : Option Bool :=
  if w == 0 then none
  else if lane == 0 then some false
  else if lane == allOnes w then some true
  else none

/-- Validate and decode all mask lanes via `decodeSimdMaskLane?`. -/
noncomputable def decodeMaskVec? (w : Nat) : List Nat → Option (List Bool)
  | [] => some []
  | m :: ms =>
    match decodeSimdMaskLane? w m, decodeMaskVec? w ms with
    | some b, some bs => some (b :: bs)
    | _, _ => none

/-- Propositional validity predicate for a `w`-bit SIMD mask vector. -/
noncomputable def validMaskVec (w : Nat) (mask : List Nat) : Prop :=
  1 ≤ w ∧ ∀ m, m ∈ mask → m = 0 ∨ m = allOnes w

/-- LLVM lowering helper `vector_mask_to_bitmask`: extracts MSB of every lane without UB. -/
noncomputable def vectorMaskToBitmask (w : Nat) (mask : List Nat) : List Bool :=
  mask.map (msbLane w)

/-- Select lanes from two vectors according to a decoded boolean mask. -/
noncomputable def selectByBools {α : Type} : List Bool → List α → List α → Outcome (List α)
  | [], [], [] => Outcome.ok []
  | b :: bs, a :: as, c :: cs =>
    match selectByBools bs as cs with
    | Outcome.ok rest => Outcome.ok ((if b then a else c) :: rest)
    | Outcome.ub => Outcome.ub
  | _, _, _ => Outcome.ub

/-- Miri abstract-machine semantics for `simd_select`: requires `{0, allOnes w}` lanes. -/
noncomputable def simdSelectMiri {α : Type} (w : Nat) (mask : List Nat) (a b : List α) :
    Outcome (List α) :=
  if mask.length == a.length && a.length == b.length then
    match decodeMaskVec? w mask with
    | some bs => selectByBools bs a b
    | none => Outcome.ub
  else Outcome.ub

/-- `rustc_codegen_llvm` semantics for `simd_select`: lowers mask via `vectorMaskToBitmask`
(MSB extraction) and selects unconditionally whenever lane counts match. -/
noncomputable def simdSelectLlvmMsb {α : Type} (w : Nat) (mask : List Nat) (a b : List α) :
    Outcome (List α) :=
  if mask.length == a.length && a.length == b.length then
    selectByBools (vectorMaskToBitmask w mask) a b
  else Outcome.ub

/-- `rustc_const_eval` / Miri `simd_reduce_all`: validates `{0, allOnes w}`, reduces `and`. -/
noncomputable def simdReduceAllMiri (w : Nat) (mask : List Nat) : Outcome Bool :=
  match decodeMaskVec? w mask with
  | some bs => Outcome.ok (bs.all id)
  | none => Outcome.ub

/-- `rustc_codegen_llvm` `simd_reduce_all`: `vector_reduce_and (vectorMaskToBitmask w mask)`. -/
noncomputable def simdReduceAllLlvm (w : Nat) (mask : List Nat) : Outcome Bool :=
  if w == 0 then Outcome.ub else Outcome.ok ((vectorMaskToBitmask w mask).all id)

/-- `rustc_const_eval` / Miri `simd_reduce_any`: validates `{0, allOnes w}`, reduces `or`. -/
noncomputable def simdReduceAnyMiri (w : Nat) (mask : List Nat) : Outcome Bool :=
  match decodeMaskVec? w mask with
  | some bs => Outcome.ok (bs.any id)
  | none => Outcome.ub

/-- `rustc_codegen_llvm` `simd_reduce_any`: `vector_reduce_or (vectorMaskToBitmask w mask)`. -/
noncomputable def simdReduceAnyLlvm (w : Nat) (mask : List Nat) : Outcome Bool :=
  if w == 0 then Outcome.ub else Outcome.ok ((vectorMaskToBitmask w mask).any id)

theorem msbLane_zero (w : Nat) : msbLane w 0 = false := by
  unfold msbLane
  cases (w == 0)
  · simp [bitAt_zero_nat]
  · rfl

theorem msbLane_allOnes {w : Nat} (hw : 1 ≤ w) : msbLane w (allOnes w) = true := by
  cases w with
  | zero => cases hw
  | succ k =>
    unfold msbLane
    have h0 : (k + 1 == 0) = false := rfl
    have h1 : k + 1 - 1 = k := rfl
    rw [h0, h1]
    dsimp
    exact bitAt_allOnes_lt (Nat.lt_succ_self k)

theorem lsbLane_zero : lsbLane 0 = false := bitAt_zero_nat 0

theorem lsbLane_allOnes {w : Nat} (hw : 1 ≤ w) : lsbLane (allOnes w) = true :=
  bitAt_allOnes_lt hw

theorem decodeSimdMaskLane_zero {w : Nat} (hw : 1 ≤ w) :
    decodeSimdMaskLane? w 0 = some false := by
  cases w with
  | zero => cases hw
  | succ _ => rfl

theorem decodeSimdMaskLane_allOnes {w : Nat} (hw : 1 ≤ w) :
    decodeSimdMaskLane? w (allOnes w) = some true := by
  cases w with
  | zero => cases hw
  | succ k =>
    have hpos : 0 < allOnes (k + 1) := allOnes_pos_of_pos hw
    have hne : (allOnes (k + 1) == 0) = false := decide_eq_false (Nat.ne_of_gt hpos)
    unfold decodeSimdMaskLane?
    have hw0 : (k + 1 == 0) = false := rfl
    rw [hw0, hne]
    dsimp
    cases hself : (allOnes (k + 1) == allOnes (k + 1))
    · exact False.elim (ne_of_beq_false hself rfl)
    · rfl

theorem decodeSimdMaskLane_some_iff {w lane : Nat} {b : Bool} :
    decodeSimdMaskLane? w lane = some b →
    1 ≤ w ∧ ((lane = 0 ∧ b = false) ∨ (lane = allOnes w ∧ b = true)) := by
  intro h
  unfold decodeSimdMaskLane? at h
  cases hw : (w == 0)
  · have hw1 : 1 ≤ w := by
      cases w with
      | zero => cases hw
      | succ k => exact Nat.succ_le_succ (Nat.zero_le k)
    rw [hw] at h
    dsimp at h
    cases hl0 : (lane == 0)
    · rw [hl0] at h
      dsimp at h
      cases hla : (lane == allOnes w)
      · rw [hla] at h
        cases h
      · rw [hla] at h
        dsimp at h
        injection h with hb
        exact ⟨hw1, Or.inr ⟨eq_of_beq hla, hb.symm⟩⟩
    · rw [hl0] at h
      dsimp at h
      injection h with hb
      exact ⟨hw1, Or.inl ⟨eq_of_beq hl0, hb.symm⟩⟩
  · rw [hw] at h
    cases h

theorem msb_eq_lsb_and_all_bits_of_valid {w lane : Nat} (hw : 1 ≤ w)
    (hv : lane = 0 ∨ lane = allOnes w) :
    msbLane w lane = lsbLane lane ∧
    ∀ j, j < w → bitAt lane j = lsbLane lane := by
  cases hv with
  | inl h0 =>
    subst h0
    constructor
    · rw [msbLane_zero, lsbLane_zero]
    · intro j _
      rw [bitAt_zero_nat, lsbLane_zero]
  | inr ha =>
    subst ha
    constructor
    · rw [msbLane_allOnes hw, lsbLane_allOnes hw]
    · intro j hj
      rw [bitAt_allOnes_lt hj, lsbLane_allOnes hw]

theorem unique_fixed_point_of_bit_confluence {w lane : Nat} (_hw : 1 ≤ w)
    (hbound : lane < pow2 w)
    (hconfl : ∀ j, j < w → bitAt lane j = lsbLane lane) :
    lane = 0 ∨ lane = allOnes w := by
  have helper : ∀ k, k ≤ w → ∀ x, x < pow2 k → (∀ j, j < k → bitAt x j = lsbLane lane) →
      x = 0 ∨ x = allOnes k := by
    intro k hk
    induction k with
    | zero =>
      intro x hx _
      have hp0 : pow2 0 = 1 := rfl
      rw [hp0] at hx
      left
      exact nat_eq_zero_of_lt_succ hx
    | succ m ih =>
      intro x hx hb
      have hmw : m ≤ w := Nat.le_of_succ_le hk
      have hbitm := hb m (Nat.lt_succ_self m)
      let q := Nat.div x (pow2 m)
      let r := Nat.mod x (pow2 m)
      have hdm0 : pow2 m * q + r = x := nat_div_add_mod x (pow2 m)
      have hdiv_lt : q < 2 := by
        have hle : pow2 m * q ≤ pow2 m * q + r := Nat.le_add_right _ _
        rw [hdm0] at hle
        have hlt2 : pow2 m * q < 2 * pow2 m := by
          rw [← pow2_succ m]
          exact Nat.lt_of_le_of_lt hle hx
        rw [Nat.mul_comm 2 (pow2 m)] at hlt2
        exact nat_lt_of_mul_lt_mul_left hlt2
      have hlow : ∀ j, j < m → bitAt r j = lsbLane lane := by
        intro j hj
        rw [bitAt_mod_pow2_low x m hj]
        exact hb j (Nat.lt_succ_of_lt hj)
      have hih := ih hmw r (nat_mod_lt x (pow2_pos m)) hlow
      cases hih with
      | inl hm0 =>
        cases hlsb : lsbLane lane
        · have hqm : bitAt x m = false := by rw [hbitm, hlsb]
          left
          exact eq_zero_of_lt_pow2_succ_div_eq_zero_mod_eq_zero hx hqm hm0
        · rw [hlsb] at hbitm
          cases m with
          | zero =>
            have hq2' : x < 2 := hx
            unfold bitAt pow2 at hbitm
            rw [nat_div_one, nat_mod_eq_of_lt hq2'] at hbitm
            have hx1 : x = 1 := eq_of_beq (decide_eq_true_eq.mp hbitm)
            right
            rw [hx1]
            rfl
          | succ m' =>
            have hbit0 := hb 0 (Nat.zero_lt_succ (m' + 1))
            rw [hlsb] at hbit0
            have hmod_low : bitAt r 0 = bitAt x 0 := bitAt_mod_pow2_low x (m' + 1) (Nat.zero_lt_succ m')
            rw [hm0, bitAt_zero_nat] at hmod_low
            rw [← hmod_low] at hbit0
            cases hbit0
      | inr hma =>
        cases hlsb : lsbLane lane
        · cases m with
          | zero =>
            have hbit0f : bitAt x 0 = false := by rw [hbitm, hlsb]
            have h0x : Nat.mod x (pow2 0) = 0 := by
              rw [pow2_zero]
              exact nat_mod_one x
            left
            exact eq_zero_of_lt_pow2_succ_div_eq_zero_mod_eq_zero hx hbit0f h0x
          | succ m' =>
            have hbit0 := hb 0 (Nat.zero_lt_succ (m' + 1))
            rw [hlsb] at hbit0
            have hmod_low : bitAt r 0 = bitAt x 0 := bitAt_mod_pow2_low x (m' + 1) (Nat.zero_lt_succ m')
            rw [hma, bitAt_allOnes_lt (Nat.zero_lt_succ m')] at hmod_low
            rw [← hmod_low] at hbit0
            cases hbit0
        · rw [hlsb] at hbitm
          have hq1 : q = 1 := by
            unfold bitAt at hbitm
            change decide (Nat.mod q 2 == 1) = true at hbitm
            rw [nat_mod_eq_of_lt hdiv_lt] at hbitm
            exact eq_of_beq (decide_eq_true_eq.mp hbitm)
          right
          have hr_eq : r = allOnes m := hma
          rw [hq1, hr_eq, Nat.mul_one, Nat.add_comm (pow2 m) (allOnes m), ← allOnes_decomp m] at hdm0
          exact hdm0.symm
  exact helper w (Nat.le_refl w) lane hbound hconfl

theorem decodeMaskVec_eq_vectorMaskToBitmask {w : Nat} :
    ∀ (mask : List Nat) (bs : List Bool),
      decodeMaskVec? w mask = some bs → vectorMaskToBitmask w mask = bs
  | [], [], _ => rfl
  | [], _ :: _, h => by
    unfold decodeMaskVec? at h
    cases h
  | m :: ms, [], h => by
    unfold decodeMaskVec? at h
    cases hm : decodeSimdMaskLane? w m with
    | none =>
      rw [hm] at h
      cases h
    | some _ =>
      rw [hm] at h
      cases hrest : decodeMaskVec? w ms with
      | none =>
        rw [hrest] at h
        cases h
      | some _ =>
        rw [hrest] at h
        cases h
  | m :: ms, b :: bs, h => by
    unfold decodeMaskVec? at h
    cases hm : decodeSimdMaskLane? w m with
    | none =>
      rw [hm] at h
      cases h
    | some bm =>
      rw [hm] at h
      cases hrest : decodeMaskVec? w ms with
      | none =>
        rw [hrest] at h
        cases h
      | some brest =>
        rw [hrest] at h
        dsimp at h
        injection h with hcons
        injection hcons with hb hbs
        subst hb
        subst hbs
        have hdec := decodeSimdMaskLane_some_iff hm
        have hw1 : 1 ≤ w := hdec.1
        have hmsb : msbLane w m = bm := by
          cases hdec.2 with
          | inl h0 =>
            rw [h0.1, h0.2]
            exact msbLane_zero w
          | inr ha =>
            rw [ha.1, ha.2]
            exact msbLane_allOnes hw1
        unfold vectorMaskToBitmask
        dsimp [List.map]
        rw [hmsb]
        have htail := decodeMaskVec_eq_vectorMaskToBitmask ms brest hrest
        unfold vectorMaskToBitmask at htail
        rw [htail]

theorem validMaskVec_decodeMaskVec_some {w : Nat} (hv1 : 1 ≤ w) :
    ∀ (mask : List Nat), (∀ m, m ∈ mask → m = 0 ∨ m = allOnes w) →
      decodeMaskVec? w mask = some (vectorMaskToBitmask w mask)
  | [], _ => rfl
  | m :: ms, hm => by
    have hmhd : m = 0 ∨ m = allOnes w := hm m (List.Mem.head ms)
    have hmst : ∀ x, x ∈ ms → x = 0 ∨ x = allOnes w :=
      fun x hx => hm x (List.Mem.tail m hx)
    have hdec : decodeSimdMaskLane? w m = some (msbLane w m) := by
      cases hmhd with
      | inl h0 =>
        subst h0
        rw [decodeSimdMaskLane_zero hv1, msbLane_zero]
      | inr ha =>
        subst ha
        rw [decodeSimdMaskLane_allOnes hv1, msbLane_allOnes hv1]
    have htail := validMaskVec_decodeMaskVec_some hv1 ms hmst
    unfold decodeMaskVec?
    rw [hdec, htail]
    rfl

theorem selectByBools_total_of_eq_len {α : Type} :
    ∀ (bs : List Bool) (a b : List α),
      bs.length = a.length → a.length = b.length →
      ∃ res, selectByBools bs a b = Outcome.ok res ∧ res.length = bs.length
  | [], [], [], _, _ => ⟨[], rfl, rfl⟩
  | b :: bs, x :: xs, y :: ys, ha, hb => by
    have ha' : bs.length = xs.length := Nat.succ.inj ha
    have hb' : xs.length = ys.length := Nat.succ.inj hb
    cases selectByBools_total_of_eq_len bs xs ys ha' hb' with
    | intro res hres =>
      unfold selectByBools
      rw [hres.1]
      exact ⟨(if b then x else y) :: res, rfl, congrArg Nat.succ hres.2⟩
  | [], _ :: _, _, ha, _ => nomatch ha
  | [], _, _ :: _, ha, hb => by
    rw [← ha] at hb
    cases hb
  | _ :: _, [], _, ha, _ => nomatch ha
  | _ :: _, _ :: _, [], _, hb => nomatch hb

/-- **Main Theorem 1A:** Miri-valid `simd_select` is refined by LLVM's MSB lowering `vector_mask_to_bitmask`. -/
theorem simdSelectMsb_refines_miri {α : Type} (w : Nat) (mask : List Nat) (a b : List α) :
    Outcome.refines (simdSelectMiri w mask a b) (simdSelectLlvmMsb w mask a b) := by
  intro out h
  unfold simdSelectMiri at h
  unfold simdSelectLlvmMsb
  cases hlen : (mask.length == a.length && a.length == b.length)
  · rw [hlen] at h
    cases h
  · rw [hlen] at h
    dsimp at h
    dsimp
    cases hdec : decodeMaskVec? w mask
    · rw [hdec] at h
      cases h
    · rename_i bs
      rw [hdec] at h
      dsimp at h
      have hvm := decodeMaskVec_eq_vectorMaskToBitmask mask bs hdec
      rw [hvm]
      exact h

/-- **Main Theorem 1B:** Under Miri `{0, allOnes w}` validity (`validMaskVec`), LLVM MSB
lowering equals Miri semantics identically on matching lengths. -/
theorem simdSelectMsb_eq_miri_of_valid {α : Type} {w : Nat} {mask : List Nat} {a b : List α}
    (hv : validMaskVec w mask) :
    simdSelectLlvmMsb w mask a b = simdSelectMiri w mask a b := by
  unfold simdSelectLlvmMsb simdSelectMiri
  cases (mask.length == a.length && a.length == b.length)
  · rfl
  · dsimp
    rw [validMaskVec_decodeMaskVec_some hv.1 mask hv.2]

theorem simdReduceAll_refines_miri (w : Nat) (mask : List Nat) (hw : 1 ≤ w) :
    Outcome.refines (simdReduceAllMiri w mask) (simdReduceAllLlvm w mask) := by
  intro res h
  unfold simdReduceAllMiri at h
  unfold simdReduceAllLlvm
  have hw0 : (w == 0) = false := by
    cases w with
    | zero => cases hw
    | succ _ => rfl
  rw [hw0]
  dsimp
  cases hdec : decodeMaskVec? w mask
  · rw [hdec] at h
    cases h
  · rename_i bs
    rw [hdec] at h
    dsimp at h
    rw [decodeMaskVec_eq_vectorMaskToBitmask mask bs hdec]
    exact h

theorem simdReduceAny_refines_miri (w : Nat) (mask : List Nat) (hw : 1 ≤ w) :
    Outcome.refines (simdReduceAnyMiri w mask) (simdReduceAnyLlvm w mask) := by
  intro res h
  unfold simdReduceAnyMiri at h
  unfold simdReduceAnyLlvm
  have hw0 : (w == 0) = false := by
    cases w with
    | zero => cases hw
    | succ _ => rfl
  rw [hw0]
  dsimp
  cases hdec : decodeMaskVec? w mask
  · rw [hdec] at h
    cases h
  · rename_i bs
    rw [hdec] at h
    dsimp at h
    rw [decodeMaskVec_eq_vectorMaskToBitmask mask bs hdec]
    exact h

/-- Concrete divergence counterexamples at width `w = 8` (and `w = 32` MSB vs LSB):
passing `1` or `254` (`-2` in 8-bit two's complement) triggers Miri UB while LLVM MSB lowering
returns `b` (for `1`) and `a` (for `-2`). -/
theorem simdSelect_counterexample_mask_one :
    simdSelectMiri 8 [1, 0, 1, 0] [10, 20, 30, 40] [100, 200, 300, 400] = Outcome.ub ∧
    simdSelectLlvmMsb 8 [1, 0, 1, 0] [10, 20, 30, 40] [100, 200, 300, 400] =
      Outcome.ok [100, 200, 300, 400] := by
  constructor <;> rfl

theorem simdSelect_counterexample_mask_neg2 :
    simdSelectMiri 8 [254, 254, 1, 0] [10, 20, 30, 40] [100, 200, 300, 400] = Outcome.ub ∧
    simdSelectLlvmMsb 8 [254, 254, 1, 0] [10, 20, 30, 40] [100, 200, 300, 400] =
      Outcome.ok [10, 20, 300, 400] := by
  constructor <;> rfl

theorem simdReduceAny_counterexample_mask_one :
    simdReduceAnyMiri 8 [1, 0, 0, 0] = Outcome.ub ∧
    simdReduceAnyLlvm 8 [1, 0, 0, 0] = Outcome.ok false := by
  constructor <;> rfl

theorem msbLane_1_vs_lsbLane_1_w32 :
    msbLane 32 1 = false ∧ lsbLane 1 = true := by
  constructor
  · unfold msbLane bitAt pow2
    rfl
  · rfl

theorem msbLane_neg2_w8_eq_true :
    msbLane 8 254 = true ∧ decodeSimdMaskLane? 8 254 = none := by
  constructor <;> rfl

/-! ## Module 2: Little-Endian `simd_select_bitmask` <-> `vector_mask_to_bitmask` Galois Bijection -/

/-- Pack a list of booleans into a little-endian integer (index 0 = bit 0 = weight 1). -/
noncomputable def bitsToNatLE : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNatLE bs

/-- Unpack `len` bits in little-endian order (`[bitAt x 0, ..., bitAt x (len - 1)]`). -/
noncomputable def natToBitsLEFrom (x : Nat) : Nat → Nat → List Bool
  | _, 0 => []
  | start, len + 1 => bitAt x start :: natToBitsLEFrom x (start + 1) len

noncomputable def natToBitsLE (len x : Nat) : List Bool :=
  natToBitsLEFrom x 0 len

/-- Pack a list of bytes (`< 256`) into a little-endian integer (byte 0 = lowest 8 bits). -/
noncomputable def bytesToNatLE : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * bytesToNatLE bs

/-- Unpack `k` little-endian bytes from integer `x`. -/
noncomputable def natToBytesLE : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, x => Nat.mod x 256 :: natToBytesLE k (Nat.div x 256)

theorem natToBytesLE_succ (k x : Nat) :
    natToBytesLE (k + 1) x = Nat.mod x 256 :: natToBytesLE k (Nat.div x 256) := rfl

/-- Valid `k`-byte array (`bytes.length = k` and every byte `< 256`). -/
noncomputable def validBytesLE (k : Nat) (bytes : List Nat) : Prop :=
  bytes.length = k ∧ ∀ b, b ∈ bytes → b < 256

/-- Convert `[u8; K]` little-endian bitmask into `len` lane selection booleans
matching `trunc i{8*K} to i{len}` + `bitcast i{len} to <len x i1>`. -/
noncomputable def bitmaskBytesToBools (len : Nat) (bytes : List Nat) : List Bool :=
  natToBitsLE len (bytesToNatLE bytes)

/-- Convert `len` booleans into `K` little-endian `u8` bytes (zero-padding unused upper bits). -/
noncomputable def boolsToBitmaskBytes (numBytes : Nat) (bs : List Bool) : List Nat :=
  natToBytesLE numBytes (bitsToNatLE bs)

/-- Spec semantics for `simd_select_bitmask` on `[u8; K]` masks (`len <= 8 * K`). -/
noncomputable def simdSelectBitmaskSpec {α : Type} (bytes : List Nat) (a b : List α) :
    Outcome (List α) :=
  if a.length == b.length && a.length ≤ 8 * bytes.length && bytes.all (fun x => decide (x < 256)) then
    selectByBools (bitmaskBytesToBools a.length bytes) a b
  else Outcome.ub

/-- Spec semantics for `simd_bitmask` returning `[u8; numBytes]`. -/
noncomputable def simdBitmaskBytesSpec (w numBytes : Nat) (mask : List Nat) : Outcome (List Nat) :=
  if mask.length ≤ 8 * numBytes then
    match decodeMaskVec? w mask with
    | some bs => Outcome.ok (boolsToBitmaskBytes numBytes bs)
    | none => Outcome.ub
  else Outcome.ub

theorem natToBitsLEFrom_div_two (x start len : Nat) :
    natToBitsLEFrom (Nat.div x 2) start len = natToBitsLEFrom x (start + 1) len := by
  induction len generalizing start with
  | zero => rfl
  | succ k ih =>
    unfold natToBitsLEFrom
    rw [bitAt_div_two]
    rw [ih (start + 1)]

theorem natToBitsLE_succ (len x : Nat) :
    natToBitsLE (len + 1) x = bitAt x 0 :: natToBitsLE len (Nat.div x 2) := by
  unfold natToBitsLE
  change bitAt x 0 :: natToBitsLEFrom x (0 + 1) len = bitAt x 0 :: natToBitsLEFrom (Nat.div x 2) 0 len
  rw [natToBitsLEFrom_div_two x 0 len]

theorem natToBitsLE_length (len x : Nat) : (natToBitsLE len x).length = len := by
  unfold natToBitsLE
  have hgen : ∀ s x', (natToBitsLEFrom x' s len).length = len := by
    induction len with
    | zero =>
      intro _ _
      rfl
    | succ _ ih =>
      intro s x'
      unfold natToBitsLEFrom
      rw [List.length_cons, ih (s + 1) x']
  exact hgen 0 x

theorem listGetD_natToBitsLEFrom (x : Nat) :
    ∀ (len start i : Nat), i < len →
      listGetD false (natToBitsLEFrom x start len) i = bitAt x (start + i)
  | 0, _, i, hi => nomatch hi
  | _ + 1, start, 0, _ => by
    unfold natToBitsLEFrom listGetD
    rw [Nat.add_zero]
  | k + 1, start, i + 1, hi => by
    unfold natToBitsLEFrom listGetD
    have hlt : i < k := Nat.lt_of_succ_lt_succ hi
    rw [listGetD_natToBitsLEFrom x k (start + 1) i hlt]
    rw [Nat.add_assoc start 1 i, Nat.add_comm 1 i]

theorem listGetD_natToBitsLE (len x i : Nat) (hi : i < len) :
    listGetD false (natToBitsLE len x) i = bitAt x i := by
  unfold natToBitsLE
  rw [listGetD_natToBitsLEFrom x len 0 i hi, Nat.zero_add]

theorem bitAt_bitsToNatLE_lt :
    ∀ (bs : List Bool) (i : Nat), i < bs.length →
      bitAt (bitsToNatLE bs) i = listGetD false bs i
  | [], _, hi => nomatch hi
  | b :: bs, 0, _ => by
    unfold bitsToNatLE bitAt pow2 listGetD
    rw [nat_div_one]
    cases b
    · have hm : Nat.mod ((if false = true then 1 else 0) + 2 * bitsToNatLE bs) 2 = 0 := by
        dsimp
        rw [Nat.zero_add]
        exact nat_mul_mod_right 2 _
      exact congrArg (fun t => decide (t == 1)) hm
    · have hm : Nat.mod ((if true = true then 1 else 0) + 2 * bitsToNatLE bs) 2 = 1 := by
        dsimp
        rw [nat_add_mul_mod_self_left]
      exact congrArg (fun t => decide (t == 1)) hm
  | b :: bs, i + 1, hi => by
    unfold bitsToNatLE listGetD
    have hb2 : (if b then 1 else 0) < 2 := by cases b <;> decide
    rw [← bitAt_div_two]
    rw [nat_div_add_mul_two _ (bitsToNatLE bs) hb2]
    have hlt : i < bs.length := Nat.lt_of_succ_lt_succ hi
    exact bitAt_bitsToNatLE_lt bs i hlt

theorem bitsToNatLE_lt_pow2 : ∀ (bs : List Bool), bitsToNatLE bs < pow2 bs.length
  | [] => by
    unfold bitsToNatLE List.length pow2
    decide
  | b :: bs => by
    have ih := bitsToNatLE_lt_pow2 bs
    unfold bitsToNatLE List.length pow2
    have h2 : 2 * bitsToNatLE bs + 2 ≤ 2 * pow2 bs.length := by
      have hsucc : bitsToNatLE bs + 1 ≤ pow2 bs.length := ih
      have hm := Nat.mul_le_mul_left 2 hsucc
      rw [Nat.left_distrib, Nat.mul_one] at hm
      exact hm
    cases b
    · dsimp
      rw [Nat.zero_add]
      have hpos : 0 < 2 := by decide
      exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hpos) h2
    · dsimp
      have h12 : 1 < 2 := by decide
      have hlt : 1 + 2 * bitsToNatLE bs < 2 * bitsToNatLE bs + 2 := by
        rw [Nat.add_comm 1 _]
        exact Nat.add_lt_add_left h12 _
      exact Nat.lt_of_lt_of_le hlt h2

theorem bitAt_bitsToNatLE_ge (bs : List Bool) (k : Nat) :
    bitAt (bitsToNatLE bs) (bs.length + k) = false :=
  bitAt_lt_pow2_zero (bitsToNatLE_lt_pow2 bs) k

/-- Left inverse: unpacking `bs.length` bits from `bitsToNatLE bs` recovers `bs` identically. -/
theorem natToBitsLE_bitsToNatLE : ∀ bs : List Bool, natToBitsLE bs.length (bitsToNatLE bs) = bs
  | [] => rfl
  | b :: bs => by
    rw [List.length_cons, natToBitsLE_succ]
    have h0 : bitAt (bitsToNatLE (b :: bs)) 0 = b := by
      have hl := bitAt_bitsToNatLE_lt (b :: bs) 0 (Nat.zero_lt_succ bs.length)
      exact hl
    have hb2 : (if b then 1 else 0) < 2 := by cases b <;> decide
    have hdiv : Nat.div (bitsToNatLE (b :: bs)) 2 = bitsToNatLE bs := by
      change Nat.div ((if b then 1 else 0) + 2 * bitsToNatLE bs) 2 = bitsToNatLE bs
      exact nat_div_add_mul_two _ (bitsToNatLE bs) hb2
    rw [h0, hdiv, natToBitsLE_bitsToNatLE bs]

/-- Truncation theorem: packing the first `n` unpacked bits equals `x mod 2^n`
(modeling LLVM's `trunc i{8*K} to i{n}`). -/
theorem bitsToNatLE_natToBitsLE : ∀ (n x : Nat),
    bitsToNatLE (natToBitsLE n x) = Nat.mod x (pow2 n)
  | 0, x => by
    unfold natToBitsLE natToBitsLEFrom bitsToNatLE pow2
    rw [nat_mod_one]
  | n + 1, x => by
    rw [natToBitsLE_succ]
    unfold bitsToNatLE
    rw [bitsToNatLE_natToBitsLE n (Nat.div x 2)]
    have hpow : pow2 (n + 1) = 2 * pow2 n := pow2_succ n
    rw [hpow, nat_mod_mul_eq x 2 (pow2 n) (by decide) (pow2_pos n)]
    have hbit0 : (if bitAt x 0 then 1 else 0) = Nat.mod x 2 := by
      unfold bitAt pow2
      rw [nat_div_one]
      have hm2 : Nat.mod x 2 < 2 := mod_two_lt_two x
      cases hmx : Nat.mod x 2 with
      | zero => decide
      | succ k =>
        cases k with
        | zero => decide
        | succ k2 =>
          rw [hmx] at hm2
          have hn := Nat.not_lt_zero k2 (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hm2))
          cases hn
    rw [hbit0]
    exact Nat.add_comm _ _

theorem natToBitsLE_mod_eq (n x : Nat) :
    natToBitsLE n (Nat.mod x (pow2 n)) = natToBitsLE n x := by
  have h1 := natToBitsLE_bitsToNatLE (natToBitsLE n x)
  rw [natToBitsLE_length n x] at h1
  rw [bitsToNatLE_natToBitsLE n x] at h1
  exact h1

theorem natToBytesLE_pow2 : ∀ (k x : Nat),
    x < pow2 (8 * k) → bytesToNatLE (natToBytesLE k x) = x
  | 0, x, hx => by
    have hp0 : pow2 (8 * 0) = 1 := rfl
    rw [hp0] at hx
    unfold natToBytesLE bytesToNatLE
    exact (nat_eq_zero_of_lt_succ hx).symm
  | k + 1, x, hx => by
    have h256 : 256 = pow2 8 := by decide
    let q := Nat.div x 256
    let r := Nat.mod x 256
    have hdm0 : 256 * q + r = x := nat_div_add_mod x 256
    have hxlt : q < pow2 (8 * k) := by
      have hle : 256 * q ≤ 256 * q + r := Nat.le_add_right _ _
      rw [hdm0] at hle
      have hm : 8 * (k + 1) = 8 + 8 * k := by
        rw [Nat.mul_succ, Nat.add_comm]
      rw [hm, pow2_add, ← h256] at hx
      have hlt2 : 256 * q < 256 * pow2 (8 * k) := Nat.lt_of_le_of_lt hle hx
      exact nat_lt_of_mul_lt_mul_left hlt2
    unfold natToBytesLE bytesToNatLE
    rw [natToBytesLE_pow2 k q hxlt]
    rw [Nat.add_comm r _]
    exact hdm0

theorem natToBytesLE_mod (k x : Nat) :
    bytesToNatLE (natToBytesLE k x) = Nat.mod x (pow2 (8 * k)) := by
  induction k generalizing x with
  | zero =>
    unfold natToBytesLE bytesToNatLE
    have hp0 : pow2 (8 * 0) = 1 := rfl
    rw [hp0, nat_mod_one]
  | succ m ih =>
    unfold natToBytesLE bytesToNatLE
    rw [ih (Nat.div x 256)]
    have h256 : 256 = pow2 8 := by decide
    have hm : 8 * (m + 1) = 8 + 8 * m := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [hm, pow2_add, ← h256]
    rw [nat_mod_mul_eq x 256 (pow2 (8 * m)) (by decide) (pow2_pos (8 * m))]
    exact Nat.add_comm (Nat.mod x 256) _

theorem natToBytesLE_length : ∀ (k x : Nat), (natToBytesLE k x).length = k
  | 0, _ => rfl
  | k + 1, x => by
    rw [natToBytesLE_succ]
    rw [List.length_cons, natToBytesLE_length k (Nat.div x 256)]

theorem natToBytesLE_all_lt : ∀ (k x b : Nat), b ∈ natToBytesLE k x → b < 256
  | 0, _, _, hb => nomatch hb
  | k + 1, x, b, hb => by
    rw [natToBytesLE_succ] at hb
    cases hb with
    | head => exact nat_mod_lt x (by decide)
    | tail _ htl => exact natToBytesLE_all_lt k (Nat.div x 256) b htl

theorem bytesToNatLE_lt_pow2 :
    ∀ (bytes : List Nat), (∀ b, b ∈ bytes → b < 256) → bytesToNatLE bytes < pow2 (8 * bytes.length)
  | [], _ => by
    unfold bytesToNatLE List.length pow2
    decide
  | hd :: tl, hall => by
    have hhd : hd < 256 := hall hd (List.Mem.head tl)
    have htl : ∀ b, b ∈ tl → b < 256 := fun b hb => hall b (List.Mem.tail hd hb)
    have ih := bytesToNatLE_lt_pow2 tl htl
    have hsucc : bytesToNatLE tl + 1 ≤ pow2 (8 * tl.length) := ih
    have hm := Nat.mul_le_mul_left 256 hsucc
    rw [Nat.left_distrib, Nat.mul_one] at hm
    have hsum : hd + 256 * bytesToNatLE tl < 256 * bytesToNatLE tl + 256 := by
      rw [Nat.add_comm hd _]
      exact Nat.add_lt_add_left hhd _
    have hres := Nat.lt_of_lt_of_le hsum hm
    have hpow : 256 * pow2 (8 * tl.length) = pow2 (8 * (hd :: tl).length) := by
      have h256 : 256 = pow2 8 := by decide
      rw [List.length_cons, Nat.mul_succ, Nat.add_comm (8 * tl.length) 8, pow2_add, ← h256]
    rw [hpow] at hres
    exact hres

theorem bytesToNatLE_natToBytesLE_self :
    ∀ (bytes : List Nat), (∀ b, b ∈ bytes → b < 256) →
      natToBytesLE bytes.length (bytesToNatLE bytes) = bytes
  | [], _ => rfl
  | hd :: tl, hall => by
    have hhd : hd < 256 := hall hd (List.Mem.head tl)
    have htl : ∀ b, b ∈ tl → b < 256 := fun b hb => hall b (List.Mem.tail hd hb)
    unfold bytesToNatLE
    rw [List.length_cons, natToBytesLE_succ]
    have hmod : Nat.mod (hd + 256 * bytesToNatLE tl) 256 = hd :=
      nat_add_mod_pow_of_lt hhd
    have hdiv : Nat.div (hd + 256 * bytesToNatLE tl) 256 = bytesToNatLE tl :=
      nat_add_div_pow_of_lt hhd (by decide)
    rw [hmod, hdiv]
    rw [bytesToNatLE_natToBytesLE_self tl htl]

/-- **Main Theorem 2A (Little-Endian Multi-Byte Bit Indexing):**
For any `[u8; K]` byte array, bit `8 * k + b` (`b < 8`) of `bytesToNatLE bytes` equals
bit `b` of byte `k`! Directly formalizes LE `trunc i{8*K} -> bitcast <N x i1>`. -/
theorem bitAt_bytesToNatLE :
    ∀ (bytes : List Nat) (k b : Nat),
      (∀ x, x ∈ bytes → x < 256) → b < 8 →
      bitAt (bytesToNatLE bytes) (8 * k + b) = bitAt (listGetD 0 bytes k) b
  | [], k, b, _, _ => by
    unfold bytesToNatLE listGetD
    rw [bitAt_zero_nat, bitAt_zero_nat]
  | hd :: tl, 0, b, hall, hb => by
    have h256 : (256 : Nat) = pow2 8 := by decide
    unfold bytesToNatLE listGetD
    rw [Nat.mul_zero, Nat.zero_add, h256]
    exact bitAt_add_pow2_mul_low hd (bytesToNatLE tl) hb
  | hd :: tl, k + 1, b, hall, hb => by
    have hhd : hd < 256 := hall hd (List.Mem.head tl)
    have htl : ∀ x, x ∈ tl → x < 256 := fun x hx => hall x (List.Mem.tail hd hx)
    have h256 : (256 : Nat) = pow2 8 := by decide
    have hhd' : hd < pow2 8 := by rw [← h256]; exact hhd
    have hidx : 8 * (k + 1) + b = 8 + (8 * k + b) := by
      rw [Nat.mul_succ, Nat.add_comm (8 * k) 8, Nat.add_assoc]
    unfold bytesToNatLE listGetD
    rw [hidx, h256]
    rw [bitAt_add_pow2_mul_high hhd' (8 * k + b)]
    exact bitAt_bytesToNatLE tl k b htl hb

/-- **Main Theorem 2B (Galois Round-Trip Across Arbitrary `[u8; K]` and Non-Power-of-2 `N <= 8 * K`):**
Packing `bs` into `numBytes` LE bytes via `boolsToBitmaskBytes` and unpacking `bs.length` bits via
`bitmaskBytesToBools` yields `bs` identically (including non-power-of-2 widths such as `N = 10`). -/
theorem bitmaskBytesToBools_boolsToBitmaskBytes (numBytes : Nat) (bs : List Bool)
    (hlen : bs.length ≤ 8 * numBytes) :
    bitmaskBytesToBools bs.length (boolsToBitmaskBytes numBytes bs) = bs := by
  unfold bitmaskBytesToBools boolsToBitmaskBytes
  have hlt : bitsToNatLE bs < pow2 (8 * numBytes) :=
    Nat.lt_of_lt_of_le (bitsToNatLE_lt_pow2 bs) (pow2_mono hlen)
  rw [natToBytesLE_pow2 numBytes (bitsToNatLE bs) hlt]
  exact natToBitsLE_bitsToNatLE bs

/-- **Main Theorem 2C (Right-Inverse Modulo Padding Bits `>= N`):**
Packing `bitmaskBytesToBools n bytes` back into `bytes.length` bytes preserves all bits `< n` and
zeros any padding bits `>= n`. -/
theorem boolsToBitmaskBytes_bitmaskBytesToBools (n : Nat) (bytes : List Nat)
    (hlen : n ≤ 8 * bytes.length) :
    bytesToNatLE (boolsToBitmaskBytes bytes.length (bitmaskBytesToBools n bytes)) =
      Nat.mod (bytesToNatLE bytes) (pow2 n) := by
  unfold boolsToBitmaskBytes bitmaskBytesToBools
  rw [bitsToNatLE_natToBitsLE n (bytesToNatLE bytes)]
  have hlt : Nat.mod (bytesToNatLE bytes) (pow2 n) < pow2 (8 * bytes.length) :=
    Nat.lt_of_lt_of_le (nat_mod_lt _ (pow2_pos n)) (pow2_mono hlen)
  exact natToBytesLE_pow2 bytes.length _ hlt

/-- Padding bits at positions `i >= N` do not affect `bitmaskBytesToBools N`. -/
theorem bitmaskBytesToBools_upper_bit_invariant (n hi : Nat) (bytes bytes' : List Nat)
    (heq : bytesToNatLE bytes' = bytesToNatLE bytes + pow2 n * hi) :
    bitmaskBytesToBools n bytes' = bitmaskBytesToBools n bytes := by
  unfold bitmaskBytesToBools
  rw [← natToBitsLE_mod_eq n (bytesToNatLE bytes')]
  rw [← natToBitsLE_mod_eq n (bytesToNatLE bytes)]
  rw [heq, nat_add_mul_mod_self_left]

/-- **Main Theorem 2D (`simd_bitmask` <-> `simd_select_bitmask` End-to-End Bijection):**
Composing `simdBitmaskBytesSpec` with `simdSelectBitmaskSpec` reproduces `simdSelectMiri`
identically whenever lane count `a.length = mask.length <= 8 * numBytes`. -/
theorem simdSelectBitmask_after_simdBitmask {α : Type} {w numBytes : Nat}
    {mask : List Nat} {a b : List α} {bytes : List Nat}
    (hmal : a.length = mask.length)
    (hlen : mask.length ≤ 8 * numBytes)
    (hbm : simdBitmaskBytesSpec w numBytes mask = Outcome.ok bytes) :
    simdSelectBitmaskSpec bytes a b = simdSelectMiri w mask a b := by
  unfold simdBitmaskBytesSpec at hbm
  rw [ite_eq_left hlen] at hbm
  cases hdec : decodeMaskVec? w mask
  · rw [hdec] at hbm
    cases hbm
  · rename_i bs
    rw [hdec] at hbm
    dsimp at hbm
    injection hbm with hbytes
    subst hbytes
    have hvm : vectorMaskToBitmask w mask = bs := decodeMaskVec_eq_vectorMaskToBitmask mask bs hdec
    have hblen : bs.length = mask.length := by
      unfold vectorMaskToBitmask at hvm
      rw [← hvm, list_length_map]
    unfold simdSelectBitmaskSpec simdSelectMiri
    rw [hdec]
    have hlen_bytes : (boolsToBitmaskBytes numBytes bs).length = numBytes :=
      natToBytesLE_length numBytes (bitsToNatLE bs)
    have hall : (boolsToBitmaskBytes numBytes bs).all (fun x => decide (x < 256)) = true := by
      unfold boolsToBitmaskBytes
      exact list_all_eq_true_of (fun x => decide (x < 256)) _
        (fun x hx => decide_eq_true (natToBytesLE_all_lt numBytes (bitsToNatLE bs) x hx))
    have ha_le : (a.length ≤ 8 * (boolsToBitmaskBytes numBytes bs).length) := by
      rw [hlen_bytes, hmal]
      exact hlen
    have hle_b : decide (a.length ≤ 8 * (boolsToBitmaskBytes numBytes bs).length) = true :=
      decide_eq_true ha_le
    rw [hall, hle_b, Bool.and_true, Bool.and_true]
    have hmeq : (mask.length == a.length) = true := by
      cases hcmp : (mask.length == a.length)
      · exact False.elim (ne_of_beq_false hcmp hmal.symm)
      · rfl
    rw [hmeq, Bool.true_and]
    cases (a.length == b.length)
    · rfl
    · dsimp
      have hrt : bitmaskBytesToBools a.length (boolsToBitmaskBytes numBytes bs) = bs := by
        rw [hmal, ← hblen]
        exact bitmaskBytesToBools_boolsToBitmaskBytes numBytes bs (by rw [hblen]; exact hlen)
      rw [hrt]

/-- Byte-0-replicating miscompilation model matching LLVM 22.1.6 x86-64 SSE2/AVX2
`U8x10` lowering (`punpcklbw; pshuflw $0; pshufd $68` / `vpbroadcastb`). -/
noncomputable def buggySse2ReplicateByte0 : List Nat → List Nat
  | [] => []
  | b0 :: _ => [b0, b0]

/-- Concrete witnesses for `N = 16` (`[3, 1]`), `N = 10` (`[0xCB, 0xFE]`, `[0x00, 0x01]`),
and the formal x86-64 SSE2/AVX2 `U8x10` divergence where lane 8 receives `19` in Miri /
canonical LE semantics (`[0, 1]` yields `9`), vs. `9` / `19` under byte-0 replication. -/
theorem bitmask_len16_witness :
    bitmaskBytesToBools 16 [3, 1] =
      [true, true, false, false, false, false, false, false,
       true, false, false, false, false, false, false, false] ∧
    listGetD false (bitmaskBytesToBools 10 [0, 1]) 8 = true := by
  constructor <;> rfl

theorem llvm_x86_u8x10_bitmask_bug_witness :
    let a10 : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
    let b10 : List Nat := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20]
    simdSelectBitmaskSpec [203, 254] a10 b10 = Outcome.ok [1, 2, 13, 4, 15, 16, 7, 8, 19, 10] ∧
    simdSelectBitmaskSpec (buggySse2ReplicateByte0 [203, 254]) a10 b10 =
      Outcome.ok [1, 2, 13, 4, 15, 16, 7, 8, 9, 10] ∧
    simdSelectBitmaskSpec [0, 1] a10 b10 = Outcome.ok [11, 12, 13, 14, 15, 16, 17, 18, 9, 20] ∧
    simdSelectBitmaskSpec (buggySse2ReplicateByte0 [0, 1]) a10 b10 =
      Outcome.ok [11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by
  dsimp
  constructor
  · rfl
  · constructor
    · rfl
    · constructor <;> rfl

/-! ## Module 3: `ctlz`/`cttz` vs. `ctlz_nonzero`/`cttz_nonzero` Poison & Range Refinement -/

/-- Structural leading-zero count over a `w`-bit unsigned word `x`. -/
noncomputable def ctlzStep : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, x => if bitAt x w then 0 else 1 + ctlzStep w (Nat.mod x (pow2 w))

/-- Structural trailing-zero count over a `w`-bit unsigned word `x`. -/
noncomputable def cttzStep : Nat → Nat → Nat
  | 0, _ => 0
  | w + 1, x => if bitAt x 0 then 0 else 1 + cttzStep w (Nat.div x 2)

/-- Abstract-machine & LLVM semantics for `@llvm.ctlz(x, i1 isZeroPoison)`. -/
noncomputable def evalCtlz (isZeroPoison : Bool) (w x : Nat) : Outcome Nat :=
  if isZeroPoison && (x == 0) then Outcome.ub else Outcome.ok (ctlzStep w x)

/-- Abstract-machine & LLVM semantics for `@llvm.cttz(x, i1 isZeroPoison)`. -/
noncomputable def evalCttz (isZeroPoison : Bool) (w x : Nat) : Outcome Nat :=
  if isZeroPoison && (x == 0) then Outcome.ub else Outcome.ok (cttzStep w x)

/-- SIMD intrinsics `simd_ctlz` / `simd_cttz` always pass `dont_poison_on_zero = false`. -/
noncomputable def evalSimdCtlz (w : Nat) (lanes : List Nat) : Outcome (List Nat) :=
  Outcome.ok (lanes.map (ctlzStep w))

noncomputable def evalSimdCttz (w : Nat) (lanes : List Nat) : Outcome (List Nat) :=
  Outcome.ok (lanes.map (cttzStep w))

theorem ctlzStep_zero : ∀ w : Nat, ctlzStep w 0 = w
  | 0 => rfl
  | w + 1 => by
    unfold ctlzStep
    rw [bitAt_zero_nat, nat_zero_mod, ctlzStep_zero w, Nat.add_comm 1 w]
    rfl

theorem cttzStep_zero : ∀ w : Nat, cttzStep w 0 = w
  | 0 => rfl
  | w + 1 => by
    unfold cttzStep
    rw [bitAt_zero_nat, nat_zero_div, cttzStep_zero w, Nat.add_comm 1 w]
    rfl

theorem ctlzStep_le_width : ∀ (w x : Nat), ctlzStep w x ≤ w
  | 0, _ => Nat.le_refl 0
  | w + 1, x => by
    unfold ctlzStep
    cases bitAt x w
    · dsimp
      rw [Nat.add_comm 1 _]
      exact Nat.succ_le_succ (ctlzStep_le_width w (Nat.mod x (pow2 w)))
    · exact Nat.zero_le _

theorem cttzStep_le_width : ∀ (w x : Nat), cttzStep w x ≤ w
  | 0, _ => Nat.le_refl 0
  | w + 1, x => by
    unfold cttzStep
    cases bitAt x 0
    · dsimp
      rw [Nat.add_comm 1 _]
      exact Nat.succ_le_succ (cttzStep_le_width w (Nat.div x 2))
    · exact Nat.zero_le _

/-- Strict `[0, W)` bound whenever `x != 0` and `x < 2^W` (`ctlz_nonzero`). -/
theorem ctlzStep_lt_width_of_nonzero :
    ∀ {w x : Nat}, 1 ≤ w → x < pow2 w → x ≠ 0 → ctlzStep w x < w
  | 0, _, hw, _, _ => nomatch hw
  | w + 1, x, _, hx, hne => by
    unfold ctlzStep
    cases hb : bitAt x w
    · dsimp
      cases w with
      | zero =>
        have hmod : Nat.mod x (pow2 0) = 0 := by
          rw [pow2_zero]
          exact nat_mod_one x
        have hx0 := eq_zero_of_lt_pow2_succ_div_eq_zero_mod_eq_zero hx hb hmod
        exact False.elim (hne hx0)
      | succ k =>
        have hkw : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have hrm : Nat.mod x (pow2 (k + 1)) < pow2 (k + 1) := nat_mod_lt x (pow2_pos (k + 1))
        have hne_mod : Nat.mod x (pow2 (k + 1)) ≠ 0 := by
          intro h0
          exact hne (eq_zero_of_lt_pow2_succ_div_eq_zero_mod_eq_zero hx hb h0)
        have ih := ctlzStep_lt_width_of_nonzero hkw hrm hne_mod
        rw [Nat.add_comm 1 _]
        exact Nat.succ_lt_succ ih
    · exact Nat.zero_lt_succ w

/-- Strict `[0, W)` bound whenever `x != 0` and `x < 2^W` (`cttz_nonzero`). -/
theorem cttzStep_lt_width_of_nonzero :
    ∀ {w x : Nat}, 1 ≤ w → x < pow2 w → x ≠ 0 → cttzStep w x < w
  | 0, _, hw, _, _ => nomatch hw
  | w + 1, x, _, hx, hne => by
    unfold cttzStep
    cases hb : bitAt x 0
    · dsimp
      have hm2 : Nat.mod x 2 = 0 := by
        have hlt2 := mod_two_lt_two x
        cases hmx : Nat.mod x 2 with
        | zero => rfl
        | succ k =>
          cases k with
          | zero =>
            unfold bitAt pow2 at hb
            rw [nat_div_one, hmx] at hb
            cases hb
          | succ k2 =>
            rw [hmx] at hlt2
            have hn := Nat.not_lt_zero k2 (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hlt2))
            cases hn
      have hx2 : 2 * Nat.div x 2 = x := by
        have hdm := nat_div_add_mod x 2
        rw [hm2, Nat.add_zero] at hdm
        exact hdm
      have hdiv_ne : Nat.div x 2 ≠ 0 := by
        intro h0
        rw [h0, Nat.mul_zero] at hx2
        exact hne hx2.symm
      have hdiv_lt : Nat.div x 2 < pow2 w := by
        rw [← hx2, pow2_succ] at hx
        exact nat_lt_of_mul_lt_mul_left hx
      cases w with
      | zero =>
        rw [pow2_zero] at hdiv_lt
        exact False.elim (hdiv_ne (nat_eq_zero_of_lt_succ hdiv_lt))
      | succ k =>
        have hkw : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        have ih := cttzStep_lt_width_of_nonzero hkw hdiv_lt hdiv_ne
        rw [Nat.add_comm 1 _]
        exact Nat.succ_lt_succ ih
    · exact Nat.zero_lt_succ w

/-- Leading-zero semantic verification: all bits above `w - 1 - ctlzStep w x` are zero,
and bit `w - 1 - ctlzStep w x` is 1 whenever `ctlzStep w x < w`. -/
theorem ctlzStep_prefix_zero :
    ∀ (w x j : Nat), j < ctlzStep w x → bitAt x (w - 1 - j) = false
  | 0, _, j, hj => nomatch hj
  | w + 1, x, j, hj => by
    unfold ctlzStep at hj
    cases hb : bitAt x w
    · rw [hb] at hj
      dsimp at hj
      cases w with
      | zero =>
        unfold ctlzStep at hj
        rw [Nat.add_zero] at hj
        have hj0 : j = 0 := nat_eq_zero_of_lt_succ hj
        subst hj0
        exact hb
      | succ k =>
        cases j with
        | zero => exact hb
        | succ j' =>
          rw [Nat.add_comm 1 _] at hj
          have hj' : j' < ctlzStep (k + 1) (Nat.mod x (pow2 (k + 1))) := Nat.lt_of_succ_lt_succ hj
          have ih := ctlzStep_prefix_zero (k + 1) (Nat.mod x (pow2 (k + 1))) j' hj'
          have hsub_lt : k + 1 - 1 - j' < k + 1 := by
            have h1 : k + 1 - 1 = k := rfl
            rw [h1]
            exact Nat.lt_succ_of_le (Nat.sub_le k j')
          rw [bitAt_mod_pow2_low x (k + 1) hsub_lt] at ih
          have hidx : (k + 1 + 1) - 1 - (j' + 1) = (k + 1) - 1 - j' := by
            change (k + 1) - (j' + 1) = k - j'
            exact Nat.succ_sub_succ k j'
          rw [hidx]
          exact ih
    · rw [hb] at hj
      cases hj

theorem ctlzStep_first_one :
    ∀ (w x : Nat), ctlzStep w x < w → bitAt x (w - 1 - ctlzStep w x) = true
  | 0, _, hj => nomatch hj
  | w + 1, x, hj => by
    unfold ctlzStep
    unfold ctlzStep at hj
    cases hb : bitAt x w
    · rw [hb] at hj
      dsimp at hj
      dsimp
      cases w with
      | zero =>
        unfold ctlzStep at hj
        rw [Nat.add_zero] at hj
        cases Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ hj)
      | succ k =>
        rw [Nat.add_comm 1 _] at hj
        have hlt : ctlzStep (k + 1) (Nat.mod x (pow2 (k + 1))) < k + 1 := Nat.lt_of_succ_lt_succ hj
        have ih := ctlzStep_first_one (k + 1) (Nat.mod x (pow2 (k + 1))) hlt
        have hsub_lt : (k + 1 - 1) - ctlzStep (k + 1) (Nat.mod x (pow2 (k + 1))) < k + 1 := by
          have h1 : k + 1 - 1 = k := rfl
          rw [h1]
          exact Nat.lt_succ_of_le (Nat.sub_le k _)
        rw [bitAt_mod_pow2_low x (k + 1) hsub_lt] at ih
        have hidx : (k + 1) - (1 + ctlzStep (k + 1) (Nat.mod x (pow2 (k + 1)))) =
            k - ctlzStep (k + 1) (Nat.mod x (pow2 (k + 1))) := by
          rw [Nat.add_comm 1 (ctlzStep _ _)]
          exact Nat.succ_sub_succ k _
        change bitAt x ((k + 1) - (1 + ctlzStep (k + 1) (Nat.mod x (pow2 (k + 1))))) = true
        rw [hidx]
        exact ih
    · exact hb

/-- Trailing-zero semantic verification: all bits `< cttzStep w x` are zero, and bit `cttzStep w x` is 1. -/
theorem cttzStep_prefix_zero :
    ∀ (w x j : Nat), j < cttzStep w x → bitAt x j = false
  | 0, _, j, hj => nomatch hj
  | w + 1, x, j, hj => by
    unfold cttzStep at hj
    cases hb : bitAt x 0
    · rw [hb] at hj
      dsimp at hj
      cases j with
      | zero => exact hb
      | succ j' =>
        rw [Nat.add_comm 1 _] at hj
        have hj' : j' < cttzStep w (Nat.div x 2) := Nat.lt_of_succ_lt_succ hj
        have ih := cttzStep_prefix_zero w (Nat.div x 2) j' hj'
        rw [bitAt_div_two] at ih
        exact ih
    · rw [hb] at hj
      cases hj

theorem cttzStep_first_one :
    ∀ (w x : Nat), cttzStep w x < w → bitAt x (cttzStep w x) = true
  | 0, _, hj => nomatch hj
  | w + 1, x, hj => by
    unfold cttzStep
    unfold cttzStep at hj
    cases hb : bitAt x 0
    · rw [hb] at hj
      dsimp at hj
      dsimp
      rw [Nat.add_comm 1 _] at hj
      have hlt : cttzStep w (Nat.div x 2) < w := Nat.lt_of_succ_lt_succ hj
      have ih := cttzStep_first_one w (Nat.div x 2) hlt
      rw [Nat.add_comm 1 _]
      exact (bitAt_div_two x (cttzStep w (Nat.div x 2))).symm.trans ih
    · exact hb

/-- **Main Theorem 3A (Range Bounds):** `evalCtlz false` (`is_zero_poison = false`) ranges over
`[0, W]`, whereas `evalCtlz true` (`ctlz_nonzero`) guarantees strict `[0, W)` on any non-UB outcome. -/
theorem ctlz_safe_total_range (w x : Nat) :
    ∃ n, evalCtlz false w x = Outcome.ok n ∧ n ≤ w :=
  ⟨ctlzStep w x, rfl, ctlzStep_le_width w x⟩

theorem ctlz_nonzero_strict_range {w x n : Nat} (hw : 1 ≤ w) (hx : x < pow2 w)
    (h : evalCtlz true w x = Outcome.ok n) :
    x ≠ 0 ∧ n < w := by
  unfold evalCtlz at h
  cases hx0 : (x == 0)
  · rw [hx0] at h
    dsimp at h
    injection h with hn
    subst hn
    have hne : x ≠ 0 := fun heq => by
      subst heq
      cases hx0
    exact ⟨hne, ctlzStep_lt_width_of_nonzero hw hx hne⟩
  · rw [hx0] at h
    cases h

theorem cttz_nonzero_strict_range {w x n : Nat} (hw : 1 ≤ w) (hx : x < pow2 w)
    (h : evalCttz true w x = Outcome.ok n) :
    x ≠ 0 ∧ n < w := by
  unfold evalCttz at h
  cases hx0 : (x == 0)
  · rw [hx0] at h
    dsimp at h
    injection h with hn
    subst hn
    have hne : x ≠ 0 := fun heq => by
      subst heq
      cases hx0
    exact ⟨hne, cttzStep_lt_width_of_nonzero hw hx hne⟩
  · rw [hx0] at h
    cases h

/-- **Main Theorem 3B (Poison Refinement):** Safe `ctlz`/`cttz` refines `ctlz_nonzero`/`cttz_nonzero`. -/
theorem ctlz_safe_refines_nonzero (w x : Nat) :
    Outcome.refines (evalCtlz true w x) (evalCtlz false w x) := by
  intro n h
  unfold evalCtlz at h
  unfold evalCtlz
  cases hx0 : (x == 0)
  · rw [hx0] at h
    exact h
  · rw [hx0] at h
    cases h

theorem cttz_safe_refines_nonzero (w x : Nat) :
    Outcome.refines (evalCttz true w x) (evalCttz false w x) := by
  intro n h
  unfold evalCttz at h
  unfold evalCttz
  cases hx0 : (x == 0)
  · rw [hx0] at h
    exact h
  · rw [hx0] at h
    cases h

/-- **Main Theorem 3C (KnownBits Power-of-2 Top-Bit Clearing, e.g., Bit 5 for `W = 32 = pow2 5`):**
Because `n < pow2 p`, all bits `p + j` are zero (`KnownBits::ctlz` clamping `MaxLZ` to `W - 1`). -/
theorem ctlz_nonzero_clears_high_bits {p x n : Nat} (hx : x < pow2 (pow2 p))
    (h : evalCtlz true (pow2 p) x = Outcome.ok n) (j : Nat) :
    bitAt n (p + j) = false := by
  have hw : 1 ≤ pow2 p := pow2_ge_one p
  have hr := ctlz_nonzero_strict_range hw hx h
  exact bitAt_lt_pow2_zero hr.2 j

/-- **Main Theorem 3D (Soundness of Eliding `< W` Branch After `ctlz_nonzero`):**
Removing `if n < w then f n else g n` to `f n` preserves abstract-machine outcomes identically
under `is_zero_poison = true` for `1 <= w` and `x < 2^w`. -/
noncomputable def ctlzGuardChecked (isZeroPoison : Bool) (w x : Nat) (f g : Nat → Nat) : Outcome Nat :=
  match evalCtlz isZeroPoison w x with
  | Outcome.ub => Outcome.ub
  | Outcome.ok n => Outcome.ok (if n < w then f n else g n)

noncomputable def ctlzGuardElided (isZeroPoison : Bool) (w x : Nat) (f : Nat → Nat) : Outcome Nat :=
  match evalCtlz isZeroPoison w x with
  | Outcome.ub => Outcome.ub
  | Outcome.ok n => Outcome.ok (f n)

theorem ctlz_nonzero_lt_guard_elision_sound {w x : Nat} (hw : 1 ≤ w) (hx : x < pow2 w)
    (f g : Nat → Nat) :
    ctlzGuardChecked true w x f g = ctlzGuardElided true w x f := by
  unfold ctlzGuardChecked ctlzGuardElided
  cases hev : evalCtlz true w x with
  | ub => rfl
  | ok n =>
    dsimp
    have hr := ctlz_nonzero_strict_range hw hx hev
    rw [ite_eq_left hr.2]

theorem ctlz_zero_divergence_witness :
    evalCtlz false 32 0 = Outcome.ok 32 ∧
    evalCtlz true 32 0 = Outcome.ub ∧
    ctlzGuardChecked false 32 0 (fun n => n + 1000) (fun _ => 9999) = Outcome.ok 9999 ∧
    Outcome.refines (ctlzGuardElided true 32 0 (fun n => n + 1000)) (Outcome.ok 1031) := by
  constructor
  · unfold evalCtlz
    dsimp
    rw [ctlzStep_zero 32]
  · constructor
    · rfl
    · constructor
      · unfold ctlzGuardChecked evalCtlz
        dsimp
        rw [ctlzStep_zero 32]
        rfl
      · unfold ctlzGuardElided evalCtlz
        exact Outcome.refines_ub _

/-! ## Module 4: `simd_as` Total Saturation vs. `simd_cast` / `float_to_int_unchecked` -/

/-- Extended floating-point semantic representation capturing all cases observed by
truncating/saturating float-to-int conversions (`NaN`, `+Inf`, `-Inf`, and `(-1)^isNeg * (intMag + frac)`
with `frac in [0, 1)` signaled by `hasFrac`). -/
inductive ExtFloat where
  | nan
  | posInf
  | negInf
  | finite (isNeg : Bool) (intMag : Nat) (hasFrac : Bool)

/-- Signed vs. unsigned target integer family. -/
inductive IntSignedness where
  | unsigned
  | signed

/-- Canonical map `n -> -(n : Int)` directly over `Int.ofNat`/`Int.negSucc` constructors. -/
noncomputable def negNatToInt : Nat → Int
  | 0 => Int.ofNat 0
  | n + 1 => Int.negSucc n

/-- Exact `Round::TowardZero` truncation of `(-1)^isNeg * (intMag + frac)` (`frac in [0, 1)`). -/
noncomputable def truncTowardZero : Bool → Nat → Int
  | false, m => Int.ofNat m
  | true, m => negNatToInt m

/-- Total constructor-level integer ordering matching mathematical `<=` on `Int`. -/
noncomputable def sIntLe : Int → Int → Bool
  | Int.ofNat m, Int.ofNat n => decide (m ≤ n)
  | Int.negSucc _, Int.ofNat _ => true
  | Int.ofNat _, Int.negSucc _ => false
  | Int.negSucc m, Int.negSucc n => decide (n ≤ m)

/-- Minimum representable value for integer target `(signedness, w)` (`w >= 1`). -/
noncomputable def sIntMinBound : IntSignedness → Nat → Int
  | IntSignedness.unsigned, _ => Int.ofNat 0
  | IntSignedness.signed, w => if w == 0 then Int.ofNat 0 else negNatToInt (pow2 (w - 1))

/-- Maximum representable value for integer target `(signedness, w)` (`w >= 1`). -/
noncomputable def sIntMaxBound : IntSignedness → Nat → Int
  | IntSignedness.unsigned, w => Int.ofNat (pow2 w - 1)
  | IntSignedness.signed, w => if w == 0 then Int.ofNat 0 else Int.ofNat (pow2 (w - 1) - 1)

/-- Total clamping onto `[lo, hi]`. -/
noncomputable def sIntClamp (lo hi x : Int) : Int :=
  if !(sIntLe lo x) then lo
  else if !(sIntLe x hi) then hi
  else x

/-- Rust Reference / `core::intrinsics` open-interval domain check:
`(-2^(w-1) - 1, 2^(w-1))` for signed `iW`, `(-1, 2^w)` for unsigned `uW`. -/
noncomputable def inOpenFloatDomain (s : IntSignedness) (w : Nat) : ExtFloat → Bool
  | ExtFloat.nan => false
  | ExtFloat.posInf => false
  | ExtFloat.negInf => false
  | ExtFloat.finite isNeg intMag _ =>
    match s with
    | IntSignedness.unsigned =>
      if isNeg then intMag == 0 else decide (intMag < pow2 w)
    | IntSignedness.signed =>
      if w == 0 then false
      else if isNeg then decide (intMag ≤ pow2 (w - 1))
      else decide (intMag < pow2 (w - 1))

/-- Lane-level `@llvm.fptosi.sat` / `@llvm.fptoui.sat` semantics (`simd_as`). -/
noncomputable def evalFloatToIntSat (s : IntSignedness) (w : Nat) : ExtFloat → Int
  | ExtFloat.nan => Int.ofNat 0
  | ExtFloat.negInf => sIntMinBound s w
  | ExtFloat.posInf => sIntMaxBound s w
  | ExtFloat.finite isNeg intMag _ =>
    sIntClamp (sIntMinBound s w) (sIntMaxBound s w) (truncTowardZero isNeg intMag)

/-- Lane-level unchecked `fptosi` / `fptoui` semantics (`float_to_int_unchecked` and `simd_cast`). -/
noncomputable def evalFloatToIntUnchecked (s : IntSignedness) (w : Nat) : ExtFloat → Outcome Int
  | ExtFloat.nan => Outcome.ub
  | ExtFloat.negInf => Outcome.ub
  | ExtFloat.posInf => Outcome.ub
  | ExtFloat.finite isNeg intMag _ =>
    if w == 0 then Outcome.ub
    else
      let t := truncTowardZero isNeg intMag
      if sIntLe (sIntMinBound s w) t && sIntLe t (sIntMaxBound s w) then Outcome.ok t
      else Outcome.ub

/-- Vector-level `simd_as` semantics (total for `w >= 1`). -/
noncomputable def evalSimdAs (s : IntSignedness) (w : Nat) (xs : List ExtFloat) : Outcome (List Int) :=
  if w == 0 then Outcome.ub else Outcome.ok (xs.map (evalFloatToIntSat s w))

/-- Vector-level `simd_cast` float-to-int semantics (UB if ANY lane violates open interval). -/
noncomputable def evalSimdCast (s : IntSignedness) (w : Nat) : List ExtFloat → Outcome (List Int)
  | [] => if w == 0 then Outcome.ub else Outcome.ok []
  | x :: xs =>
    match evalFloatToIntUnchecked s w x, evalSimdCast s w xs with
    | Outcome.ok y, Outcome.ok ys => Outcome.ok (y :: ys)
    | _, _ => Outcome.ub

theorem sIntLe_refl : ∀ x : Int, sIntLe x x = true
  | Int.ofNat m => decide_eq_true (Nat.le_refl m)
  | Int.negSucc m => decide_eq_true (Nat.le_refl m)

theorem sIntLe_ofNat_ofNat (m n : Nat) : sIntLe (Int.ofNat m) (Int.ofNat n) = decide (m ≤ n) :=
  rfl

theorem sIntLe_negNat_ofNat (m n : Nat) : sIntLe (negNatToInt m) (Int.ofNat n) = true := by
  cases m with
  | zero => exact decide_eq_true (Nat.zero_le n)
  | succ _ => rfl

theorem sIntLe_negNatToInt (a b : Nat) :
    sIntLe (negNatToInt b) (negNatToInt a) = decide (a ≤ b) := by
  cases a with
  | zero =>
    cases b with
    | zero => decide
    | succ _ => rfl
  | succ a' =>
    cases b with
    | zero => rfl
    | succ b' =>
      change decide (a' ≤ b') = decide (a' + 1 ≤ b' + 1)
      cases hle : decide (a' ≤ b')
      · have hnot : ¬ (a' ≤ b') := decide_eq_false_iff_not.mp hle
        have hnot2 : ¬ (a' + 1 ≤ b' + 1) := fun h => hnot (Nat.le_of_succ_le_succ h)
        exact (decide_eq_false hnot2).symm
      · have hle' : a' ≤ b' := decide_eq_true_eq.mp hle
        exact (decide_eq_true (Nat.succ_le_succ hle')).symm

theorem sIntLe_zero_negNat_right (n : Nat) :
    sIntLe (Int.ofNat 0) (negNatToInt n) = (n == 0) := by
  cases n <;> rfl

theorem sIntLe_bounds_valid (s : IntSignedness) {w : Nat} (hw : 1 ≤ w) :
    sIntLe (sIntMinBound s w) (sIntMaxBound s w) = true := by
  cases s with
  | unsigned =>
    unfold sIntMinBound sIntMaxBound sIntLe
    exact decide_eq_true (Nat.zero_le _)
  | signed =>
    cases w with
    | zero => cases hw
    | succ k =>
      unfold sIntMinBound sIntMaxBound
      dsimp
      exact sIntLe_negNat_ofNat _ _

theorem sIntLe_min_zero (s : IntSignedness) {w : Nat} (hw : 1 ≤ w) :
    sIntLe (sIntMinBound s w) (Int.ofNat 0) = true := by
  cases s with
  | unsigned =>
    unfold sIntMinBound
    rfl
  | signed =>
    cases w with
    | zero => cases hw
    | succ k =>
      unfold sIntMinBound
      dsimp
      exact sIntLe_negNat_ofNat _ 0

theorem sIntLe_zero_max (s : IntSignedness) {w : Nat} (hw : 1 ≤ w) :
    sIntLe (Int.ofNat 0) (sIntMaxBound s w) = true := by
  cases s with
  | unsigned =>
    unfold sIntMaxBound sIntLe
    exact decide_eq_true (Nat.zero_le _)
  | signed =>
    cases w with
    | zero => cases hw
    | succ k =>
      unfold sIntMaxBound
      dsimp
      unfold sIntLe
      exact decide_eq_true (Nat.zero_le _)

theorem sIntClamp_in_bounds (lo hi x : Int) (hlo_hi : sIntLe lo hi = true) :
    sIntLe lo (sIntClamp lo hi x) = true ∧ sIntLe (sIntClamp lo hi x) hi = true := by
  unfold sIntClamp
  cases h1 : sIntLe lo x
  · dsimp
    exact ⟨sIntLe_refl lo, hlo_hi⟩
  · dsimp
    cases h2 : sIntLe x hi
    · dsimp
      exact ⟨hlo_hi, sIntLe_refl hi⟩
    · dsimp
      exact ⟨h1, h2⟩

theorem sIntClamp_eq_self_of_in_bounds {lo hi x : Int}
    (h1 : sIntLe lo x = true) (h2 : sIntLe x hi = true) :
    sIntClamp lo hi x = x := by
  unfold sIntClamp
  rw [h1, h2]
  rfl

/-- **Main Theorem 4A (Truncation Bounds <-> Open-Interval Precondition Equivalence):**
For any integer width `w >= 1` and signedness `s`, checking `[MIN, MAX]` on the truncated
value `truncTowardZero isNeg intMag` is equivalent to Rust's open-interval domain check
`(-2^(w-1) - 1, 2^(w-1))` (signed) or `(-1, 2^w)` (unsigned). -/
theorem truncInBounds_iff_inOpenFloatDomain (s : IntSignedness) {w : Nat} (hw : 1 ≤ w)
    (isNeg : Bool) (intMag : Nat) (hasFrac : Bool) :
    (sIntLe (sIntMinBound s w) (truncTowardZero isNeg intMag) &&
      sIntLe (truncTowardZero isNeg intMag) (sIntMaxBound s w)) =
      inOpenFloatDomain s w (ExtFloat.finite isNeg intMag hasFrac) := by
  have hw0 : (w == 0) = false := by
    cases w with
    | zero => cases hw
    | succ _ => rfl
  cases s with
  | unsigned =>
    unfold sIntMinBound sIntMaxBound truncTowardZero inOpenFloatDomain
    cases isNeg
    · dsimp
      change (sIntLe (Int.ofNat 0) (Int.ofNat intMag) &&
        sIntLe (Int.ofNat intMag) (Int.ofNat (pow2 w - 1))) = decide (intMag < pow2 w)
      have h0 : sIntLe (Int.ofNat 0) (Int.ofNat intMag) = true :=
        decide_eq_true (Nat.zero_le intMag)
      rw [h0, Bool.true_and, sIntLe_ofNat_ofNat]
      have hpos : 0 < pow2 w := pow2_pos w
      cases hle : decide (intMag ≤ pow2 w - 1)
      · have hnot : ¬ (intMag ≤ pow2 w - 1) := decide_eq_false_iff_not.mp hle
        have hnot2 : ¬ (intMag < pow2 w) := fun h => hnot (Nat.le_sub_one_of_lt h)
        exact (decide_eq_false hnot2).symm
      · have hle' : intMag ≤ pow2 w - 1 := decide_eq_true_eq.mp hle
        exact (decide_eq_true (Nat.lt_of_le_of_lt hle' (Nat.sub_lt hpos Nat.zero_lt_one))).symm
    · dsimp
      change (sIntLe (Int.ofNat 0) (negNatToInt intMag) &&
        sIntLe (negNatToInt intMag) (Int.ofNat (pow2 w - 1))) = (intMag == 0)
      rw [sIntLe_zero_negNat_right, sIntLe_negNat_ofNat, Bool.and_true]
  | signed =>
    unfold sIntMinBound sIntMaxBound truncTowardZero inOpenFloatDomain
    dsimp
    rw [hw0]
    dsimp
    cases isNeg
    · dsimp
      have hmin : sIntLe (negNatToInt (pow2 (w - 1))) (Int.ofNat intMag) = true :=
        sIntLe_negNat_ofNat _ _
      change (sIntLe (negNatToInt (pow2 (w - 1))) (Int.ofNat intMag) &&
        sIntLe (Int.ofNat intMag) (Int.ofNat (pow2 (w - 1) - 1))) = decide (intMag < pow2 (w - 1))
      rw [hmin, Bool.true_and, sIntLe_ofNat_ofNat]
      have hpos : 0 < pow2 (w - 1) := pow2_pos (w - 1)
      cases hle : decide (intMag ≤ pow2 (w - 1) - 1)
      · have hnot : ¬ (intMag ≤ pow2 (w - 1) - 1) := decide_eq_false_iff_not.mp hle
        have hnot2 : ¬ (intMag < pow2 (w - 1)) := fun h => hnot (Nat.le_sub_one_of_lt h)
        exact (decide_eq_false hnot2).symm
      · have hle' : intMag ≤ pow2 (w - 1) - 1 := decide_eq_true_eq.mp hle
        exact (decide_eq_true (Nat.lt_of_le_of_lt hle' (Nat.sub_lt hpos Nat.zero_lt_one))).symm
    · dsimp
      change (sIntLe (negNatToInt (pow2 (w - 1))) (negNatToInt intMag) &&
        sIntLe (negNatToInt intMag) (Int.ofNat (pow2 (w - 1) - 1))) = decide (intMag ≤ pow2 (w - 1))
      have hmax : sIntLe (negNatToInt intMag) (Int.ofNat (pow2 (w - 1) - 1)) = true :=
        sIntLe_negNat_ofNat _ _
      rw [hmax, Bool.and_true]
      exact sIntLe_negNatToInt intMag (pow2 (w - 1))

theorem evalFloatToIntSat_in_bounds (s : IntSignedness) {w : Nat} (hw : 1 ≤ w) (f : ExtFloat) :
    sIntLe (sIntMinBound s w) (evalFloatToIntSat s w f) = true ∧
    sIntLe (evalFloatToIntSat s w f) (sIntMaxBound s w) = true := by
  cases f with
  | nan => exact ⟨sIntLe_min_zero s hw, sIntLe_zero_max s hw⟩
  | negInf => exact ⟨sIntLe_refl _, sIntLe_bounds_valid s hw⟩
  | posInf => exact ⟨sIntLe_bounds_valid s hw, sIntLe_refl _⟩
  | finite isNeg intMag _ =>
    exact sIntClamp_in_bounds (sIntMinBound s w) (sIntMaxBound s w) _ (sIntLe_bounds_valid s hw)

theorem evalFloatToIntSat_refines_unchecked (s : IntSignedness) (w : Nat) (f : ExtFloat) :
    Outcome.refines (evalFloatToIntUnchecked s w f) (Outcome.ok (evalFloatToIntSat s w f)) := by
  intro r h
  cases f with
  | nan =>
    unfold evalFloatToIntUnchecked at h
    cases h
  | negInf =>
    unfold evalFloatToIntUnchecked at h
    cases h
  | posInf =>
    unfold evalFloatToIntUnchecked at h
    cases h
  | finite isNeg intMag hasFrac =>
    unfold evalFloatToIntUnchecked at h
    cases hw0 : (w == 0)
    · rw [hw0] at h
      dsimp at h
      cases hbounds : (sIntLe (sIntMinBound s w) (truncTowardZero isNeg intMag) &&
          sIntLe (truncTowardZero isNeg intMag) (sIntMaxBound s w))
      · rw [hbounds] at h
        cases h
      · rw [hbounds] at h
        dsimp at h
        injection h with hr
        subst hr
        unfold evalFloatToIntSat
        dsimp
        have hpair := bool_and_eq_true_elim hbounds
        rw [sIntClamp_eq_self_of_in_bounds hpair.1 hpair.2]
    · rw [hw0] at h
      cases h

/-- **Main Theorem 4B (`simd_as` Total Safety & Bounds):**
For `w >= 1`, `evalSimdAs s w xs` never exhibits UB (`Outcome.ok ys`), preserves lane count,
and every output lane lies inside `[MIN, MAX]`. -/
theorem simdAs_total_and_in_bounds (s : IntSignedness) {w : Nat} (hw : 1 ≤ w)
    (xs : List ExtFloat) :
    ∃ ys, evalSimdAs s w xs = Outcome.ok ys ∧
      ys.length = xs.length ∧
      ∀ y, y ∈ ys → sIntLe (sIntMinBound s w) y = true ∧ sIntLe y (sIntMaxBound s w) = true := by
  have hw0 : (w == 0) = false := by
    cases w with
    | zero => cases hw
    | succ _ => rfl
  unfold evalSimdAs
  rw [hw0]
  dsimp
  refine ⟨xs.map (evalFloatToIntSat s w), rfl, list_length_map _ xs, ?_⟩
  intro y hy
  have hm := list_mem_map_elim (evalFloatToIntSat s w) y xs hy
  cases hm with
  | intro x hx =>
    rw [← hx.2]
    exact evalFloatToIntSat_in_bounds s hw x

/-- **Main Theorem 4C (`simd_as` Refines `simd_cast`):**
Whenever `simd_cast` (`evalSimdCast`) does not trigger UB, `simd_as` produces the exact same
integer lane vector; whenever any lane of `simd_cast` hits UB, `simd_as` saturates totals. -/
theorem simdAs_refines_simdCast (s : IntSignedness) (w : Nat) :
    ∀ xs : List ExtFloat, Outcome.refines (evalSimdCast s w xs) (evalSimdAs s w xs)
  | [] => by
    intro ys h
    unfold evalSimdCast at h
    unfold evalSimdAs
    cases hw0 : (w == 0)
    · rw [hw0] at h
      exact h
    · rw [hw0] at h
      cases h
  | x :: xs => by
    intro ys h
    unfold evalSimdCast at h
    cases hx : evalFloatToIntUnchecked s w x with
    | ub =>
      rw [hx] at h
      cases h
    | ok y =>
      rw [hx] at h
      cases hrest : evalSimdCast s w xs with
      | ub =>
        rw [hrest] at h
        cases h
      | ok rest =>
        rw [hrest] at h
        dsimp at h
        injection h with hcons
        subst hcons
        have hxs := simdAs_refines_simdCast s w xs rest hrest
        unfold evalSimdAs at hxs
        unfold evalSimdAs
        cases hw0 : (w == 0)
        · rw [hw0] at hxs
          dsimp at hxs
          injection hxs with hmap
          have hxy := evalFloatToIntSat_refines_unchecked s w x y hx
          injection hxy with hsat
          rw [← hsat]
          change Outcome.ok (evalFloatToIntSat s w x :: List.map (evalFloatToIntSat s w) xs) =
            Outcome.ok (evalFloatToIntSat s w x :: rest)
          rw [hmap]
        · rw [hw0] at hxs
          cases hxs

theorem simdCast_eq_unchecked_singleton (s : IntSignedness) {w : Nat} (hw : 1 ≤ w) (x : ExtFloat) :
    (∃ y, evalFloatToIntUnchecked s w x = Outcome.ok y ∧
          evalSimdCast s w [x] = Outcome.ok [y]) ∨
    (evalFloatToIntUnchecked s w x = Outcome.ub ∧ evalSimdCast s w [x] = Outcome.ub) := by
  have hw0 : (w == 0) = false := by
    cases w with
    | zero => cases hw
    | succ _ => rfl
  unfold evalSimdCast
  cases hx : evalFloatToIntUnchecked s w x with
  | ub =>
    right
    exact ⟨rfl, rfl⟩
  | ok y =>
    left
    refine ⟨y, rfl, ?_⟩
    have hnil : evalSimdCast s w [] = Outcome.ok [] := by
      unfold evalSimdCast
      rw [hw0]
      rfl
    rw [hnil]

/-- Differential boundary witnesses matching `Probe C` (`-128.9` ok vs `-129.0` UB on `i8`;
`-0.999` ok vs `-1.0` UB on `u8`; `NaN -> 0`, `+Inf -> MAX`, `-Inf -> MIN` under `simd_as`). -/
theorem float_to_int_open_boundary_witnesses :
    evalFloatToIntUnchecked IntSignedness.signed 8 (ExtFloat.finite true 128 true) =
      Outcome.ok (Int.negSucc 127) ∧
    evalFloatToIntUnchecked IntSignedness.signed 8 (ExtFloat.finite false 127 true) =
      Outcome.ok (Int.ofNat 127) ∧
    evalFloatToIntUnchecked IntSignedness.signed 8 (ExtFloat.finite true 129 false) = Outcome.ub ∧
    evalFloatToIntSat IntSignedness.signed 8 (ExtFloat.finite true 129 false) =
      Int.negSucc 127 ∧
    evalFloatToIntUnchecked IntSignedness.unsigned 8 (ExtFloat.finite true 0 true) =
      Outcome.ok (Int.ofNat 0) ∧
    evalFloatToIntUnchecked IntSignedness.unsigned 8 (ExtFloat.finite false 255 true) =
      Outcome.ok (Int.ofNat 255) ∧
    evalFloatToIntUnchecked IntSignedness.unsigned 8 (ExtFloat.finite true 1 false) = Outcome.ub ∧
    evalFloatToIntSat IntSignedness.unsigned 8 (ExtFloat.finite true 1 false) = Int.ofNat 0 ∧
    evalFloatToIntSat IntSignedness.signed 32 ExtFloat.nan = Int.ofNat 0 ∧
    evalFloatToIntUnchecked IntSignedness.signed 32 ExtFloat.nan = Outcome.ub := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor
          · rfl
          · constructor
            · rfl
            · constructor
              · rfl
              · constructor
                · rfl
                · constructor <;> rfl

/-! ## Module 5: Unified End-to-End Verification Contract Theorem -/

/-- Unified soundness theorem combining all four intrinsic-family contracts:
1. `simd_select` LLVM MSB lowering refines Miri `{0, allOnes w}` semantics (`simdSelectMsb_refines_miri`)
   and matches it identically on valid masks (`simdSelectMsb_eq_miri_of_valid`).
2. `simd_select_bitmask` and `simd_bitmask` form an exact LE round-trip bijection across arbitrary
   non-power-of-two lane counts `N <= 8 * K` (`simdSelectBitmask_after_simdBitmask`), indexing bit
   `8 * k + b` of byte `k` (`bitAt_bytesToNatLE`).
3. `ctlz_nonzero` guarantees strict `< w` (`ctlz_nonzero_strict_range`), justifies eliding `< w`
   downstream checks (`ctlz_nonzero_lt_guard_elision_sound`), and is safely refined by `ctlz`/`simd_ctlz`
   (`ctlz_safe_refines_nonzero`).
4. `simd_as` is total within `[MIN, MAX]` (`simdAs_total_and_in_bounds`) and refines `simd_cast` /
   `float_to_int_unchecked` (`simdAs_refines_simdCast`), whose UB guard matches the Rust open interval
   (`truncInBounds_iff_inOpenFloatDomain`). -/
theorem all_four_intrinsic_contracts_sound
    {α : Type} {w numBytes : Nat} (hw : 1 ≤ w)
    (mask : List Nat) (a b : List α)
    (xCtlz : Nat) (hxCtlz : xCtlz < pow2 w)
    (s : IntSignedness) (floats : List ExtFloat) :
    Outcome.refines (simdSelectMiri w mask a b) (simdSelectLlvmMsb w mask a b) ∧
    (validMaskVec w mask → simdSelectLlvmMsb w mask a b = simdSelectMiri w mask a b) ∧
    (∀ bytes, a.length = mask.length → mask.length ≤ 8 * numBytes →
      simdBitmaskBytesSpec w numBytes mask = Outcome.ok bytes →
      simdSelectBitmaskSpec bytes a b = simdSelectMiri w mask a b) ∧
    Outcome.refines (evalCtlz true w xCtlz) (evalCtlz false w xCtlz) ∧
    (∀ f g : Nat → Nat, ctlzGuardChecked true w xCtlz f g = ctlzGuardElided true w xCtlz f) ∧
    Outcome.refines (evalSimdCast s w floats) (evalSimdAs s w floats) ∧
    (∃ ys, evalSimdAs s w floats = Outcome.ok ys ∧
      ∀ y, y ∈ ys → sIntLe (sIntMinBound s w) y = true ∧ sIntLe y (sIntMaxBound s w) = true) := by
  constructor
  · exact simdSelectMsb_refines_miri w mask a b
  · constructor
    · intro hv
      exact simdSelectMsb_eq_miri_of_valid hv
    · constructor
      · intro bytes hmal hlen hbm
        exact simdSelectBitmask_after_simdBitmask hmal hlen hbm
      · constructor
        · exact ctlz_safe_refines_nonzero w xCtlz
        · constructor
          · intro f g
            exact ctlz_nonzero_lt_guard_elision_sound hw hxCtlz f g
          · constructor
            · exact simdAs_refines_simdCast s w floats
            · have hs := simdAs_total_and_in_bounds s hw floats
              cases hs with
              | intro ys hys => exact ⟨ys, hys.1, hys.2.2⟩

end SimdSelectBitmaskCtlzAndSimdAsSoundness
