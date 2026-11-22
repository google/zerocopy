prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Option.Basic

/-!
# Soundness and Sharpness of Rust Core SIMD Intrinsics and MCP#838 MIR Validation

Self-contained, kernel-checked Lean 4 (`v4.34.1`) formalization of:
1. Per-active-lane `simd_masked_load` memory safety with unconditional base-pointer
   `SimdAlign` checking and refinement onto `@llvm.masked.load`
   (`simd_masked_load_refines_llvm_masked_load`), plus inactive-lane memory framing
   (`simd_masked_load_inactive_lane_frame`) and the `x86_64` vs. `s390x`
   `SimdAlign::Vector` alignment split (`s390x_align8_vector_safe_x86_ub`).
2. The `{-1, 0}` (`{0, 2^w - 1}`) canonical SIMD mask precondition unifying MSB
   (`lshr (w - 1)` + `trunc` / `icmp slt 0`), LSB (`trunc i1` / `& 1`), nonzero
   (`brif` / `!= 0`), and per-bit bitwise selection (`canonical_mask_unifies_msb_and_lsb`),
   plus uniqueness of `{0, 2^w - 1}` (`bit_uniform_implies_canonical`).
3. Little-endian (`x86_64`) vs. big-endian (`s390x`) `bitcast <N x i1> to iN`
   bijection and `simd_select_bitmask(simd_bitmask(m), yes, no)` round-trip soundness
   across both endiannesses (`simd_bitmask_select_roundtrip_both_endians`).
4. Constructive sharpness counterexamples (`ce1_plus1_mask_diverges_msb_vs_lsb`,
   `ce2_all_zero_mask_misaligned_violates_llvm_align_attr`,
   `ce3_unchecked_simd_cast_oob_poison`).
5. MCP#838 MIR place-validation prohibition on projecting fields of `#[repr(simd)]`
   ADTs regardless of function safety (`mcp838_forbids_simd_field_projection`).

Audit discipline:
- Explicit `prelude`, imports strictly within `joshlf/anneal`'s locked `Init.*` set.
- Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
  zero `native_decide`, zero `partial def`, zero `._unsafe_rec`.
- All recursive definitions on inductive types are marked `noncomputable def`, and
  structural `DecidableEq` instances are implemented manually (no `deriving`).
-/

namespace Anneal.Simd.MaskedLoadBitmaskMcp838

/-! ## Section 1: Core Data Types & Manual Structural `DecidableEq` -/

/-- Alignment mode parameter `const ALIGN: SimdAlign` of `simd_masked_load` /
`simd_masked_store` (`library/core/src/intrinsics/simd/mod.rs:408-417`). -/
inductive SimdAlign where
  | unaligned
  | element
  | vector

noncomputable def SimdAlign.decEq (a b : SimdAlign) : Decidable (a = b) :=
  match a, b with
  | .unaligned, .unaligned => isTrue rfl
  | .element, .element => isTrue rfl
  | .vector, .vector => isTrue rfl
  | .unaligned, .element => isFalse (fun h => by cases h)
  | .unaligned, .vector => isFalse (fun h => by cases h)
  | .element, .unaligned => isFalse (fun h => by cases h)
  | .element, .vector => isFalse (fun h => by cases h)
  | .vector, .unaligned => isFalse (fun h => by cases h)
  | .vector, .element => isFalse (fun h => by cases h)

noncomputable instance : DecidableEq SimdAlign := SimdAlign.decEq

/-- Target byte/bit endianness (`rustc_abi::Endian`). -/
inductive Endian where
  | little
  | big

noncomputable def Endian.decEq (a b : Endian) : Decidable (a = b) :=
  match a, b with
  | .little, .little => isTrue rfl
  | .big, .big => isTrue rfl
  | .little, .big => isFalse (fun h => by cases h)
  | .big, .little => isFalse (fun h => by cases h)

noncomputable instance : DecidableEq Endian := Endian.decEq

/-- Execution outcome for `simd_masked_load` and `@llvm.masked.load`. -/
inductive LoadOutcome (α : Type) where
  | ok (lanes : List α)
  | ubLength
  | ubAlign
  | ubMask
  | ubMemory

/-- Structural `DecidableEq` on `List α` implemented manually (no `deriving`). -/
noncomputable def listDecEq {α : Type} (dec : ∀ x y : α, Decidable (x = y)) :
    ∀ xs ys : List α, Decidable (xs = ys)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | x :: xs, y :: ys =>
    match dec x y with
    | isFalse hne =>
      isFalse (fun h => by injection h with h1 _; exact hne h1)
    | isTrue heq =>
      match listDecEq dec xs ys with
      | isFalse hne =>
        isFalse (fun h => by injection h with _ h2; exact hne h2)
      | isTrue heq2 =>
        isTrue (by rw [heq, heq2])

noncomputable def LoadOutcome.decEq {α : Type} (dec : ∀ x y : α, Decidable (x = y)) :
    ∀ a b : LoadOutcome α, Decidable (a = b)
  | .ok xs, .ok ys =>
    match listDecEq dec xs ys with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun hEq => by injection hEq with h1; exact h h1)
  | .ubLength, .ubLength => isTrue rfl
  | .ubAlign, .ubAlign => isTrue rfl
  | .ubMask, .ubMask => isTrue rfl
  | .ubMemory, .ubMemory => isTrue rfl
  | .ok _, .ubLength => isFalse (fun h => by cases h)
  | .ok _, .ubAlign => isFalse (fun h => by cases h)
  | .ok _, .ubMask => isFalse (fun h => by cases h)
  | .ok _, .ubMemory => isFalse (fun h => by cases h)
  | .ubLength, .ok _ => isFalse (fun h => by cases h)
  | .ubLength, .ubAlign => isFalse (fun h => by cases h)
  | .ubLength, .ubMask => isFalse (fun h => by cases h)
  | .ubLength, .ubMemory => isFalse (fun h => by cases h)
  | .ubAlign, .ok _ => isFalse (fun h => by cases h)
  | .ubAlign, .ubLength => isFalse (fun h => by cases h)
  | .ubAlign, .ubMask => isFalse (fun h => by cases h)
  | .ubAlign, .ubMemory => isFalse (fun h => by cases h)
  | .ubMask, .ok _ => isFalse (fun h => by cases h)
  | .ubMask, .ubLength => isFalse (fun h => by cases h)
  | .ubMask, .ubAlign => isFalse (fun h => by cases h)
  | .ubMask, .ubMemory => isFalse (fun h => by cases h)
  | .ubMemory, .ok _ => isFalse (fun h => by cases h)
  | .ubMemory, .ubLength => isFalse (fun h => by cases h)
  | .ubMemory, .ubAlign => isFalse (fun h => by cases h)
  | .ubMemory, .ubMask => isFalse (fun h => by cases h)

noncomputable instance {α : Type} [DecidableEq α] : DecidableEq (LoadOutcome α) :=
  LoadOutcome.decEq inferInstance

/-- Total indexed boolean lookup on `List Bool` (avoids `List.getD` outside minimal `Init`). -/
noncomputable def getBoolD : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, i + 1 => getBoolD bs i

private theorem list_length_map {α β : Type} (f : α → β) :
    ∀ xs : List α, (xs.map f).length = xs.length
  | [] => rfl
  | _ :: xs => by
    change (xs.map f).length + 1 = xs.length + 1
    rw [list_length_map f xs]

/-! ## Section 2: Elementary Constructive Arithmetic Lemmas (No `omega`) -/

private theorem two_pow_pos : ∀ n : Nat, 0 < Nat.pow 2 n
  | 0 => Nat.zero_lt_one
  | n + 1 => by
    have ih := two_pow_pos n
    change 0 < Nat.pow 2 n * 2
    exact Nat.mul_pos ih (Nat.succ_pos 1)

private theorem two_pow_succ_eq (n : Nat) : Nat.pow 2 (n + 1) = Nat.pow 2 n + Nat.pow 2 n := by
  change Nat.pow 2 n * 2 = Nat.pow 2 n + Nat.pow 2 n
  rw [Nat.mul_succ, Nat.mul_one]

private theorem two_pow_add (a : Nat) : ∀ b : Nat,
    Nat.pow 2 (a + b) = Nat.pow 2 a * Nat.pow 2 b
  | 0 => (Nat.mul_one _).symm
  | b + 1 => by
    rw [Nat.add_succ]
    change Nat.pow 2 (a + b) * 2 = Nat.pow 2 a * (Nat.pow 2 b * 2)
    rw [two_pow_add a b, Nat.mul_assoc]

private theorem two_pow_ge_two {w : Nat} (hw : 2 ≤ w) : 2 ≤ Nat.pow 2 w := by
  cases w with
  | zero => cases hw
  | succ k =>
    cases k with
    | zero => cases hw with | step h => cases h
    | succ m =>
      have hp : 1 ≤ Nat.pow 2 (m + 1) := two_pow_pos (m + 1)
      rw [two_pow_succ_eq (m + 1)]
      exact Nat.add_le_add hp hp

private theorem two_pow_sub_one_mul_two {w : Nat} (hw : 1 ≤ w) :
    Nat.pow 2 w = Nat.pow 2 (Nat.sub w 1) + Nat.pow 2 (Nat.sub w 1) := by
  cases w with
  | zero => cases hw
  | succ k =>
    change Nat.pow 2 (k + 1) = Nat.pow 2 k + Nat.pow 2 k
    exact two_pow_succ_eq k

private theorem nat_sub_one_lt_self {n : Nat} (hn : 0 < n) : Nat.sub n 1 < n := by
  cases n with
  | zero => cases hn
  | succ k => exact Nat.lt_succ_self k

private theorem nat_add_sub_cancel_right_ge {a b : Nat} (h : 1 ≤ b) :
    a + Nat.sub b 1 = Nat.sub (a + b) 1 := by
  cases b with
  | zero => cases h
  | succ k =>
    change a + k = Nat.sub (a + (k + 1)) 1
    rw [Nat.add_succ]
    rfl

private theorem nat_lt_of_add_lt_add_right {a b c : Nat} (h : a + c < b + c) : a < b := by
  induction c with
  | zero => exact h
  | succ k ih => exact ih (Nat.lt_of_succ_lt_succ h)

private theorem nat_pow_pred_le_allOnes {w : Nat} (hw : 2 ≤ w) :
    Nat.pow 2 (Nat.sub w 1) ≤ Nat.sub (Nat.pow 2 w) 1 := by
  have hw1 : 1 ≤ w := Nat.le_trans (Nat.le_succ 1) hw
  have hsplit := two_pow_sub_one_mul_two hw1
  have hp : 1 ≤ Nat.pow 2 (Nat.sub w 1) := two_pow_pos (Nat.sub w 1)
  rw [hsplit, ← nat_add_sub_cancel_right_ge hp]
  exact Nat.le_add_right _ _

private theorem nat_div_zero_left (b : Nat) : Nat.div 0 b = 0 :=
  Nat.zero_div b

private theorem nat_div_one (a : Nat) : Nat.div a 1 = a :=
  Nat.div_one a

private theorem nat_sub_sub (a b c : Nat) : Nat.sub (Nat.sub a b) c = Nat.sub a (b + c) :=
  Nat.sub_sub a b c

private theorem nat_add_sub_cancel_of_le {a b : Nat} (h : a ≤ b) :
    a + Nat.sub b a = b := by
  rw [Nat.add_comm]
  exact Nat.sub_add_cancel h

private theorem nat_sub_sub_self {a b : Nat} (h : b ≤ a) :
    Nat.sub a (Nat.sub a b) = b := by
  have h1 : Nat.sub a (Nat.sub a b) + Nat.sub a b = a := Nat.sub_add_cancel (Nat.sub_le a b)
  have h2 : b + Nat.sub a b = a := nat_add_sub_cancel_of_le h
  exact Nat.add_right_cancel (h1.trans h2.symm)

private theorem nat_lt_of_mul_lt_mul_left {a b c : Nat} (h : c * a < c * b) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl hlt => exact hlt
  | inr hge =>
    have hle : c * b ≤ c * a := Nat.mul_le_mul_left c hge
    exact absurd (Nat.lt_of_lt_of_le h hle) (Nat.lt_irrefl _)

private theorem nat_div_eq_of_lt {a b : Nat} (h : a < b) : Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

private theorem nat_add_div_right (a : Nat) {b : Nat} (hb : 0 < b) :
    Nat.div (a + b) b = Nat.div a b + 1 :=
  Nat.add_div_right a hb

private theorem nat_add_mul_div_right (a c : Nat) {b : Nat} (hb : 0 < b) :
    Nat.div (a + c * b) b = Nat.div a b + c :=
  Nat.add_mul_div_right a c hb

private theorem nat_add_mul_mod_self_left (x y z : Nat) :
    Nat.mod (x + y * z) y = Nat.mod x y :=
  Nat.add_mul_mod_self_left x y z

private theorem nat_add_mul_mod_self_right (x y z : Nat) :
    Nat.mod (x + y * z) z = Nat.mod x z :=
  Nat.add_mul_mod_self_right x y z

private theorem nat_div_div_eq_div_mul (a b c : Nat) :
    Nat.div (Nat.div a b) c = Nat.div a (b * c) :=
  Nat.div_div_eq_div_mul a b c

private theorem nat_div_add_mod (m n : Nat) :
    n * Nat.div m n + Nat.mod m n = m :=
  Nat.div_add_mod m n

private theorem nat_mod_lt (x : Nat) {y : Nat} (hy : 0 < y) :
    Nat.mod x y < y :=
  Nat.mod_lt x hy

private theorem mod_two_of_two_mul_sub_one {k : Nat} (hk : 1 ≤ k) :
    Nat.mod (Nat.sub (k + k) 1) 2 = 1 := by
  cases k with
  | zero => cases hk
  | succ m =>
    have hEq : Nat.sub ((m + 1) + (m + 1)) 1 = 1 + 2 * m := by
      rw [Nat.add_succ, Nat.succ_add]
      change (m + m) + 1 = 1 + 2 * m
      rw [Nat.add_comm (m + m) 1, Nat.two_mul]
    rw [hEq, nat_add_mul_mod_self_left]

private theorem div_two_pow_pred_of_allOnes {w : Nat} (hw : 1 ≤ w) :
    Nat.div (Nat.sub (Nat.pow 2 w) 1) (Nat.pow 2 (Nat.sub w 1)) = 1 := by
  have hsplit := two_pow_sub_one_mul_two hw
  have hp : 0 < Nat.pow 2 (Nat.sub w 1) := two_pow_pos (Nat.sub w 1)
  rw [hsplit, ← nat_add_sub_cancel_right_ge hp]
  rw [Nat.add_comm (Nat.pow 2 (Nat.sub w 1)) (Nat.sub (Nat.pow 2 (Nat.sub w 1)) 1)]
  rw [nat_add_div_right _ hp]
  have hlt : Nat.sub (Nat.pow 2 (Nat.sub w 1)) 1 < Nat.pow 2 (Nat.sub w 1) :=
    nat_sub_one_lt_self hp
  rw [nat_div_eq_of_lt hlt]

private theorem div_eq_one_of_bounds {m k : Nat} (hk : 0 < k) (hlo : k ≤ m) (hhi : m < k + k) :
    Nat.div m k = 1 := by
  have hsub : m = Nat.sub m k + k := (Nat.sub_add_cancel hlo).symm
  have hlt : Nat.sub m k < k := by
    have h1 : Nat.sub m k + k < k + k := by rw [← hsub]; exact hhi
    exact nat_lt_of_add_lt_add_right h1
  rw [hsub, nat_add_div_right _ hk, nat_div_eq_of_lt hlt]

private theorem mod_two_cases (n : Nat) : Nat.mod n 2 = 0 ∨ Nat.mod n 2 = 1 := by
  have hlt : Nat.mod n 2 < 2 := nat_mod_lt n (Nat.succ_pos 1)
  cases hm : Nat.mod n 2 with
  | zero => exact Or.inl rfl
  | succ k =>
    rw [hm] at hlt
    cases k with
    | zero => exact Or.inr rfl
    | succ m =>
      have h1 : m + 1 < 1 := Nat.lt_of_succ_lt_succ hlt
      have h2 : m < 0 := Nat.lt_of_succ_lt_succ h1
      cases h2

/-! ## Section 3: Canonical `{-1, 0}` SIMD Masks & MSB/LSB/Nonzero Unification -/

/-- Bit `k` of natural number `n`: `((n / 2^k) % 2) == 1`. -/
noncomputable def bitAt (n k : Nat) : Bool :=
  Nat.beq (Nat.mod (Nat.div n (Nat.pow 2 k)) 2) 1

/-- All-ones `w`-bit unsigned pattern `2^w - 1` (two's-complement `-1` at width `w`). -/
noncomputable def allOnes (w : Nat) : Nat :=
  Nat.sub (Nat.pow 2 w) 1

/-- Rust/Miri mask-lane validity invariant (`rustc_const_eval/src/interpret/intrinsics/simd.rs:873-885`):
every lane must be all-0-bits (`0`) or all-1-bits (`2^w - 1`, signed `-1`). -/
noncomputable def IsCanonicalMaskLane (w m : Nat) : Prop :=
  m = 0 ∨ m = allOnes w

/-- Vector-level canonical mask invariant: every lane satisfies `IsCanonicalMaskLane`. -/
noncomputable def IsCanonicalMask (w : Nat) (ms : List Nat) : Prop :=
  ∀ m, m ∈ ms → IsCanonicalMaskLane w m

/-- MSB extraction matching `rustc_codegen_llvm`'s `vector_mask_to_bitmask`
(`lshr(x, w - 1)` followed by `trunc ... to i1`, folded by InstCombine to `icmp slt 0`). -/
noncomputable def maskMsbLshrTrunc (w m : Nat) : Bool :=
  bitAt m (Nat.sub w 1)

/-- Sign-bit comparison `m >= 2^(w - 1)` (equivalent to signed `icmp slt <w> m, 0`
for `w`-bit unsigned representation `m < 2^w`). -/
noncomputable def maskMsbSignCmp (w m : Nat) : Bool :=
  Nat.ble (Nat.pow 2 (Nat.sub w 1)) m

/-- LSB extraction matching bare `trunc ... to i1` and `core::simd::Mask::to_array` (`& 1`). -/
noncomputable def maskLsb (m : Nat) : Bool :=
  Nat.beq (Nat.mod m 2) 1

/-- Nonzero check matching `rustc_codegen_cranelift`'s `brif(mask_lane, ...)` and
`rustc_codegen_gcc`'s `ComparisonOp::NotEquals(mask, 0)`. -/
noncomputable def maskNonZero (m : Nat) : Bool :=
  !Nat.beq m 0

/-- Per-bit bitwise multiplex `(bit_j(m) && bit_j(yes)) || (!bit_j(m) && bit_j(no))`
matching ARM NEON `vbsl` / bitwise blend. -/
noncomputable def bitwiseSelectAtBit (m yes no j : Nat) : Bool :=
  (bitAt m j && bitAt yes j) || (!bitAt m j && bitAt no j)

/-- For every `w`-bit word `m < 2^w` (`w >= 1`), `lshr(m, w - 1) & 1 == 1` equals
signed `< 0` (`2^(w - 1) <= m`), proving LLVM InstCombine's rewrite of
`vector_mask_to_bitmask` (`trunc (lshr x, w - 1) to i1` -> `icmp slt x, 0`). -/
theorem maskMsbLshrTrunc_eq_signCmp {w m : Nat} (hw : 1 ≤ w) (hm : m < Nat.pow 2 w) :
    maskMsbLshrTrunc w m = maskMsbSignCmp w m := by
  unfold maskMsbLshrTrunc bitAt maskMsbSignCmp
  have hsplit := two_pow_sub_one_mul_two hw
  have hp : 0 < Nat.pow 2 (Nat.sub w 1) := two_pow_pos (Nat.sub w 1)
  cases hcmp : Nat.ble (Nat.pow 2 (Nat.sub w 1)) m with
  | false =>
    have hlt : m < Nat.pow 2 (Nat.sub w 1) := by
      cases Nat.lt_or_ge m (Nat.pow 2 (Nat.sub w 1)) with
      | inl h => exact h
      | inr hge =>
        have hble : Nat.ble (Nat.pow 2 (Nat.sub w 1)) m = true := Nat.ble_eq.mpr hge
        rw [hble] at hcmp
        cases hcmp
    rw [nat_div_eq_of_lt hlt]
    rfl
  | true =>
    have hge : Nat.pow 2 (Nat.sub w 1) ≤ m := Nat.ble_eq.mp hcmp
    have hhi : m < Nat.pow 2 (Nat.sub w 1) + Nat.pow 2 (Nat.sub w 1) := by
      rw [← hsplit]; exact hm
    rw [div_eq_one_of_bounds hp hge hhi]
    rfl

private theorem bitAt_zero (k : Nat) : bitAt 0 k = false := by
  unfold bitAt
  rw [nat_div_zero_left]
  rfl

private theorem bitAt_allOnes_of_lt : ∀ (w k : Nat), k < w → bitAt (allOnes w) k = true
  | 0, _, hk => by cases hk
  | w + 1, k, hk => by
    unfold bitAt allOnes
    have hpow : Nat.pow 2 (w + 1) = Nat.pow 2 k * Nat.pow 2 (Nat.sub (w + 1) k) := by
      have hsum : k + Nat.sub (w + 1) k = w + 1 := nat_add_sub_cancel_of_le (Nat.le_of_lt hk)
      rw [← two_pow_add k (Nat.sub (w + 1) k), hsum]
    have hremPos : 1 ≤ Nat.sub (w + 1) k := Nat.sub_pos_of_lt hk
    have hpowKPos : 0 < Nat.pow 2 k := two_pow_pos k
    have hpowRPos : 1 ≤ Nat.pow 2 (Nat.sub (w + 1) k) := two_pow_pos (Nat.sub (w + 1) k)
    have hEq : Nat.sub (Nat.pow 2 (w + 1)) 1 =
        Nat.sub (Nat.pow 2 k) 1 + Nat.sub (Nat.pow 2 (Nat.sub (w + 1) k)) 1 * Nat.pow 2 k := by
      let r := Nat.sub (Nat.pow 2 (Nat.sub (w + 1) k)) 1
      have hdecomp : Nat.pow 2 (Nat.sub (w + 1) k) = r + 1 := (Nat.sub_add_cancel hpowRPos).symm
      change Nat.sub (Nat.pow 2 (w + 1)) 1 = Nat.sub (Nat.pow 2 k) 1 + r * Nat.pow 2 k
      rw [hpow, hdecomp, Nat.mul_comm (Nat.pow 2 k) (r + 1), Nat.add_mul, Nat.one_mul]
      rw [← nat_add_sub_cancel_right_ge hpowKPos, Nat.add_comm]
    rw [hEq, nat_add_mul_div_right _ _ hpowKPos,
        nat_div_eq_of_lt (nat_sub_one_lt_self hpowKPos), Nat.zero_add]
    rw [two_pow_sub_one_mul_two hremPos]
    rw [mod_two_of_two_mul_sub_one (two_pow_pos (Nat.sub (Nat.sub (w + 1) k) 1))]
    rfl

/-- **Theorem 2 (All-Ones `{-1, 0}` Mask Precondition Unifying MSB, LSB, Nonzero, and Bitwise Lowerings):**
Under `IsCanonicalMaskLane w m` (`w >= 2`), `rustc_codegen_llvm`'s `vector_mask_to_bitmask`
(`lshr + trunc` / `icmp slt 0`), LSB truncation (`trunc i1` / `Mask::to_array` `& 1`),
and nonzero branching (`cranelift` `brif` / `gcc` `!= 0`) evaluate to the exact same Boolean
truth value, and per-bit bitwise selection (`vbsl` / `pand`/`pandn`/`por`) selects every bit
`j < w` uniformly from `yes` or `no`. -/
theorem canonical_mask_unifies_msb_and_lsb {w m : Nat} (hw : 2 ≤ w)
    (hcanon : IsCanonicalMaskLane w m) :
    maskMsbLshrTrunc w m = maskLsb m ∧
    maskMsbSignCmp w m = maskLsb m ∧
    maskLsb m = maskNonZero m ∧
    (∀ yes no j, j < w →
      bitwiseSelectAtBit m yes no j = if maskLsb m then bitAt yes j else bitAt no j) := by
  have hw1 : 1 ≤ w := Nat.le_trans (Nat.le_succ 1) hw
  cases hcanon with
  | inl h0 =>
    subst h0
    have hp : 0 < Nat.pow 2 (Nat.sub w 1) := two_pow_pos (Nat.sub w 1)
    have hble0 : Nat.ble (Nat.pow 2 (Nat.sub w 1)) 0 = false := by
      cases h : Nat.ble (Nat.pow 2 (Nat.sub w 1)) 0 with
      | false => rfl
      | true =>
        have hle := Nat.ble_eq.mp h
        exact absurd (Nat.lt_of_lt_of_le hp hle) (Nat.lt_irrefl 0)
    have hmsb0 : maskMsbLshrTrunc w 0 = false := bitAt_zero (Nat.sub w 1)
    refine ⟨hmsb0, hble0, rfl, ?_⟩
    intro yes no j _
    unfold bitwiseSelectAtBit maskLsb
    rw [bitAt_zero j]
    rfl
  | inr h1 =>
    subst h1
    have hdiv : Nat.div (allOnes w) (Nat.pow 2 (Nat.sub w 1)) = 1 :=
      div_two_pow_pred_of_allOnes hw1
    have hble : Nat.ble (Nat.pow 2 (Nat.sub w 1)) (allOnes w) = true :=
      Nat.ble_eq.mpr (nat_pow_pred_le_allOnes hw)
    have hmod : Nat.mod (allOnes w) 2 = 1 := by
      unfold allOnes
      rw [two_pow_sub_one_mul_two hw1]
      exact mod_two_of_two_mul_sub_one (two_pow_pos (Nat.sub w 1))
    have hne0 : Nat.beq (allOnes w) 0 = false := by
      have hge2 : 2 ≤ Nat.pow 2 w := two_pow_ge_two hw
      have hpos : 0 < allOnes w := by
        unfold allOnes
        exact Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hge2)
      cases h : Nat.beq (allOnes w) 0 with
      | false => rfl
      | true =>
        have heq : allOnes w = 0 := Nat.eq_of_beq_eq_true h
        rw [heq] at hpos
        cases hpos
    have hmsb1 : maskMsbLshrTrunc w (allOnes w) = true := by
      unfold maskMsbLshrTrunc bitAt
      rw [hdiv]
      rfl
    have hlsb1 : maskLsb (allOnes w) = true := by
      unfold maskLsb
      rw [hmod]
      rfl
    have hnz1 : maskNonZero (allOnes w) = true := by
      unfold maskNonZero
      rw [hne0]
      rfl
    refine ⟨hmsb1.trans hlsb1.symm, hble.trans hlsb1.symm, hlsb1.trans hnz1.symm, ?_⟩
    intro yes no j hj
    unfold bitwiseSelectAtBit
    rw [bitAt_allOnes_of_lt w j hj, hlsb1]
    cases bitAt yes j <;> rfl

/-- Converse uniqueness: among all `w`-bit words `m < 2^w`, `{0, 2^w - 1}` is the UNIQUE
set on which every bit position `j < w` agrees with a single uniform boolean `b`. -/
theorem bit_uniform_implies_canonical :
    ∀ (w m : Nat) (b : Bool),
      m < Nat.pow 2 w →
      (∀ j, j < w → bitAt m j = b) →
      m = if b then allOnes w else 0
  | 0, m, b, hm, _ => by
    have hlt1 : m < 1 := hm
    cases m with
    | zero => cases b <;> rfl
    | succ k => cases Nat.lt_of_succ_lt_succ hlt1
  | w + 1, m, b, hm, hunif => by
    have hdivLt : Nat.div m 2 < Nat.pow 2 w := by
      have hmul : 2 * Nat.div m 2 ≤ m := by
        have hdm := nat_div_add_mod m 2
        have hle : 2 * Nat.div m 2 ≤ 2 * Nat.div m 2 + Nat.mod m 2 := Nat.le_add_right _ _
        rw [hdm] at hle
        exact hle
      have hlt2 : 2 * Nat.div m 2 < 2 * Nat.pow 2 w := by
        have hpow : Nat.pow 2 (w + 1) = 2 * Nat.pow 2 w := by
          change Nat.pow 2 w * 2 = 2 * Nat.pow 2 w
          exact Nat.mul_comm _ _
        rw [← hpow]
        exact Nat.lt_of_le_of_lt hmul hm
      exact nat_lt_of_mul_lt_mul_left hlt2
    have hdivUnif : ∀ j, j < w → bitAt (Nat.div m 2) j = b := by
      intro j hj
      have hsucc : bitAt m (j + 1) = b := hunif (j + 1) (Nat.succ_lt_succ hj)
      unfold bitAt at hsucc
      unfold bitAt
      rw [nat_div_div_eq_div_mul]
      have hmul : 2 * Nat.pow 2 j = Nat.pow 2 (j + 1) := by
        change 2 * Nat.pow 2 j = Nat.pow 2 j * 2
        exact Nat.mul_comm _ _
      rw [hmul]
      exact hsucc
    have ih := bit_uniform_implies_canonical w (Nat.div m 2) b hdivLt hdivUnif
    have hbit0 : bitAt m 0 = b := hunif 0 (Nat.zero_lt_succ w)
    have hdm := nat_div_add_mod m 2
    have hbit0' : Nat.beq (Nat.mod m 2) 1 = b := by
      unfold bitAt at hbit0
      change Nat.beq (Nat.mod (Nat.div m 1) 2) 1 = b at hbit0
      rw [nat_div_one] at hbit0
      exact hbit0
    cases b with
    | false =>
      rw [ih] at hdm
      cases mod_two_cases m with
      | inl hm0 =>
        rw [hm0] at hdm
        exact hdm.symm
      | inr hm1 =>
        rw [hm1] at hbit0'
        cases hbit0'
    | true =>
      rw [ih] at hdm
      cases mod_two_cases m with
      | inl hm0 =>
        rw [hm0] at hbit0'
        cases hbit0'
      | inr hm1 =>
        rw [hm1] at hdm
        have hres : 2 * allOnes w + 1 = allOnes (w + 1) := by
          unfold allOnes
          have hp : 1 ≤ Nat.pow 2 w := two_pow_pos w
          rw [two_pow_succ_eq w, Nat.two_mul]
          have h1 : Nat.sub (Nat.pow 2 w) 1 + 1 = Nat.pow 2 w := Nat.sub_add_cancel hp
          rw [Nat.add_assoc, h1, Nat.add_comm (Nat.sub (Nat.pow 2 w) 1) (Nat.pow 2 w)]
          exact nat_add_sub_cancel_right_ge hp
        exact hdm.symm.trans hres

/-! ## Section 4: `simd_masked_load` Operational Semantics & LLVM Refinement -/

/-- Required base-pointer alignment bytes for `SimdAlign` (`rustc_const_eval/simd.rs:839-850`,
`rustc_codegen_llvm/src/intrinsic.rs:2619-2630`).
Note: `vecAlign` is target-datalayout dependent (`16` on `x86_64`, `8` on `s390x` `v128:64`). -/
noncomputable def requiredAlign (elemAlign vecAlign : Nat) : SimdAlign → Nat
  | .unaligned => 1
  | .element => elemAlign
  | .vector => vecAlign

/-- Unconditional pointer alignment predicate (`ptr % align == 0`). -/
noncomputable def isAligned (baseAddr align : Nat) : Bool :=
  Nat.beq (Nat.mod baseAddr align) 0

/-- Wrapping pointer byte offset `ptr.wrapping_offset(i * elemSize)` modulo `2^ptrBits`. -/
noncomputable def wrappingLaneAddr (ptrBits baseAddr elemSize idx : Nat) : Nat :=
  Nat.mod (baseAddr + idx * elemSize) (Nat.pow 2 ptrBits)

/-- Partial element-granularity memory map: `some v` if the `elemSize` bytes at `addr`
are allocated and readable, `none` if out-of-bounds or unmapped. -/
abbrev MemMap (α : Type) := Nat → Option α

/-- Phase 3–4 lane loop of MIR / Miri `simd_masked_load`:
validates every mask lane against `{0, 2^w - 1}` and dereferences `mem` ONLY on active
(`allOnes w`) lanes (`rustc_const_eval/src/interpret/intrinsics/simd.rs:680-695`). -/
noncomputable def evalMaskedLoadMirLanes {α : Type} (w ptrBits elemSize baseAddr : Nat)
    (mem : MemMap α) : Nat → List Nat → List α → LoadOutcome α
  | _, [], [] => .ok []
  | idx, m :: ms, d :: ds =>
    if Nat.beq m 0 then
      match evalMaskedLoadMirLanes w ptrBits elemSize baseAddr mem (idx + 1) ms ds with
      | .ok rest => .ok (d :: rest)
      | err => err
    else if Nat.beq m (allOnes w) then
      match mem (wrappingLaneAddr ptrBits baseAddr elemSize idx) with
      | none => .ubMemory
      | some v =>
        match evalMaskedLoadMirLanes w ptrBits elemSize baseAddr mem (idx + 1) ms ds with
        | .ok rest => .ok (v :: rest)
        | err => err
    else
      .ubMask
  | _, _, _ => .ubLength

/-- Full 4-phase MIR / Miri operational semantics of `simd_masked_load`.
Unconditionally checks `isAligned baseAddr (requiredAlign elemAlign vecAlign align)` BEFORE
inspecting any mask lane (even when all mask lanes are `0`). -/
noncomputable def evalSimdMaskedLoadMir {α : Type}
    (w ptrBits elemSize elemAlign vecAlign : Nat)
    (align : SimdAlign) (baseAddr : Nat) (mem : MemMap α)
    (mask : List Nat) (passthrough : List α) : LoadOutcome α :=
  if !Nat.beq mask.length passthrough.length then
    .ubLength
  else if !isAligned baseAddr (requiredAlign elemAlign vecAlign align) then
    .ubAlign
  else
    evalMaskedLoadMirLanes w ptrBits elemSize baseAddr mem 0 mask passthrough

/-- LLVM `@llvm.masked.load` lane loop after `vector_mask_to_bitmask` (`maskMsbLshrTrunc`). -/
noncomputable def evalLlvmMaskedLoadLanes {α : Type} (w ptrBits elemSize baseAddr : Nat)
    (mem : MemMap α) : Nat → List Nat → List α → LoadOutcome α
  | _, [], [] => .ok []
  | idx, m :: ms, d :: ds =>
    if maskMsbLshrTrunc w m then
      match mem (wrappingLaneAddr ptrBits baseAddr elemSize idx) with
      | none => .ubMemory
      | some v =>
        match evalLlvmMaskedLoadLanes w ptrBits elemSize baseAddr mem (idx + 1) ms ds with
        | .ok rest => .ok (v :: rest)
        | err => err
    else
      match evalLlvmMaskedLoadLanes w ptrBits elemSize baseAddr mem (idx + 1) ms ds with
      | .ok rest => .ok (d :: rest)
      | err => err
  | _, _, _ => .ubLength

/-- Full LLVM lowering of `simd_masked_load`: attaches `align N` on `Argument(0)` (`ptr`)
unconditionally (`intrinsic.rs:2711-2715`), converts mask lanes via `vector_mask_to_bitmask`
(`lshr (w - 1)` + `trunc`), and executes `@llvm.masked.load`. -/
noncomputable def evalLlvmMaskedLoad {α : Type}
    (w ptrBits elemSize elemAlign vecAlign : Nat)
    (align : SimdAlign) (baseAddr : Nat) (mem : MemMap α)
    (mask : List Nat) (passthrough : List α) : LoadOutcome α :=
  if !Nat.beq mask.length passthrough.length then
    .ubLength
  else if !isAligned baseAddr (requiredAlign elemAlign vecAlign align) then
    .ubAlign
  else
    evalLlvmMaskedLoadLanes w ptrBits elemSize baseAddr mem 0 mask passthrough

private theorem evalMaskedLoadLanes_refines_llvm {α : Type}
    (w ptrBits elemSize baseAddr : Nat) (hw : 2 ≤ w) (mem : MemMap α) :
    ∀ (idx : Nat) (mask : List Nat) (passthrough out : List α),
      evalMaskedLoadMirLanes w ptrBits elemSize baseAddr mem idx mask passthrough = .ok out →
      evalLlvmMaskedLoadLanes w ptrBits elemSize baseAddr mem idx mask passthrough = .ok out := by
  intro idx mask
  revert idx
  induction mask with
  | nil =>
    intro idx passthrough out h
    cases passthrough with
    | nil =>
      unfold evalMaskedLoadMirLanes at h
      unfold evalLlvmMaskedLoadLanes
      exact h
    | cons _ _ =>
      unfold evalMaskedLoadMirLanes at h
      cases h
  | cons m ms ih =>
    intro idx passthrough out h
    cases passthrough with
    | nil =>
      unfold evalMaskedLoadMirLanes at h
      cases h
    | cons d ds =>
      unfold evalMaskedLoadMirLanes at h
      unfold evalLlvmMaskedLoadLanes
      cases hm0 : Nat.beq m 0 with
      | true =>
        rw [hm0] at h
        have hmeq : m = 0 := Nat.eq_of_beq_eq_true hm0
        subst hmeq
        have hmsb : maskMsbLshrTrunc w 0 = false := bitAt_zero (Nat.sub w 1)
        rw [hmsb]
        cases hrec : evalMaskedLoadMirLanes w ptrBits elemSize baseAddr mem (idx + 1) ms ds with
        | ok rest =>
          rw [hrec] at h
          have hll := ih (idx + 1) ds rest hrec
          rw [hll]
          exact h
        | ubLength => rw [hrec] at h; cases h
        | ubAlign => rw [hrec] at h; cases h
        | ubMask => rw [hrec] at h; cases h
        | ubMemory => rw [hrec] at h; cases h
      | false =>
        rw [hm0] at h
        cases hm1 : Nat.beq m (allOnes w) with
        | false =>
          rw [hm1] at h
          cases h
        | true =>
          rw [hm1] at h
          have hmeq : m = allOnes w := Nat.eq_of_beq_eq_true hm1
          subst hmeq
          have hw1 : 1 ≤ w := Nat.le_trans (Nat.le_succ 1) hw
          have hmsb : maskMsbLshrTrunc w (allOnes w) = true := by
            unfold maskMsbLshrTrunc bitAt allOnes
            rw [div_two_pow_pred_of_allOnes hw1]
            rfl
          rw [hmsb]
          cases hmem : mem (wrappingLaneAddr ptrBits baseAddr elemSize idx) with
          | none =>
            rw [hmem] at h
            cases h
          | some v =>
            rw [hmem] at h
            cases hrec : evalMaskedLoadMirLanes w ptrBits elemSize baseAddr mem (idx + 1) ms ds with
            | ok rest =>
              rw [hrec] at h
              have hll := ih (idx + 1) ds rest hrec
              rw [hll]
              exact h
            | ubLength => rw [hrec] at h; cases h
            | ubAlign => rw [hrec] at h; cases h
            | ubMask => rw [hrec] at h; cases h
            | ubMemory => rw [hrec] at h; cases h

/-- **Theorem 1 (Per-Active-Lane `simd_masked_load` Memory Safety With Unconditional
Base-Pointer `SimdAlign`):** Whenever MIR/Miri `simd_masked_load` executes without UB
and returns `.ok out` (`w >= 2`), LLVM's `@llvm.masked.load` lowering (with unconditional
`Argument(0)` `align` attribute and `vector_mask_to_bitmask` MSB lowering) refines it
exactly with the identical `.ok out` vector. -/
theorem simd_masked_load_refines_llvm_masked_load {α : Type}
    {w ptrBits elemSize elemAlign vecAlign : Nat} (hw : 2 ≤ w)
    {align : SimdAlign} {baseAddr : Nat} {mem : MemMap α}
    {mask : List Nat} {passthrough out : List α}
    (hMir : evalSimdMaskedLoadMir w ptrBits elemSize elemAlign vecAlign align baseAddr mem mask passthrough = .ok out) :
    evalLlvmMaskedLoad w ptrBits elemSize elemAlign vecAlign align baseAddr mem mask passthrough = .ok out := by
  unfold evalSimdMaskedLoadMir at hMir
  unfold evalLlvmMaskedLoad
  cases hlen : Nat.beq mask.length passthrough.length with
  | false =>
    rw [hlen] at hMir
    cases hMir
  | true =>
    rw [hlen] at hMir
    cases halign : isAligned baseAddr (requiredAlign elemAlign vecAlign align) with
    | false =>
      rw [halign] at hMir
      cases hMir
    | true =>
      rw [halign] at hMir
      exact evalMaskedLoadLanes_refines_llvm w ptrBits elemSize baseAddr hw mem 0 mask passthrough out hMir

/-- **Inactive-Lane Memory Framing (Partial-Allocation Tail Load Soundness):**
If two memories `mem₁` and `mem₂` agree on every address corresponding to an active
(`allOnes w`) lane, then `evalSimdMaskedLoadMir` produces the exact same result on both
— even if `mem₂` leaves all inactive (`0`) lane addresses completely unmapped (`none`). -/
theorem simd_masked_load_inactive_lane_frame {α : Type}
    {w ptrBits elemSize elemAlign vecAlign : Nat}
    {align : SimdAlign} {baseAddr : Nat} {mem₁ mem₂ : MemMap α}
    {mask : List Nat} {passthrough : List α}
    (hAgree : ∀ i m,
      mask[i]? = some m →
      Nat.beq m (allOnes w) = true →
      Nat.beq m 0 = false →
      mem₁ (wrappingLaneAddr ptrBits baseAddr elemSize i) =
        mem₂ (wrappingLaneAddr ptrBits baseAddr elemSize i)) :
    evalSimdMaskedLoadMir w ptrBits elemSize elemAlign vecAlign align baseAddr mem₁ mask passthrough =
      evalSimdMaskedLoadMir w ptrBits elemSize elemAlign vecAlign align baseAddr mem₂ mask passthrough := by
  have hLanes :
      ∀ (idx : Nat) (ms : List Nat) (ds : List α),
        (∀ j m, ms[j]? = some m → Nat.beq m (allOnes w) = true → Nat.beq m 0 = false →
          mem₁ (wrappingLaneAddr ptrBits baseAddr elemSize (idx + j)) =
            mem₂ (wrappingLaneAddr ptrBits baseAddr elemSize (idx + j))) →
        evalMaskedLoadMirLanes w ptrBits elemSize baseAddr mem₁ idx ms ds =
          evalMaskedLoadMirLanes w ptrBits elemSize baseAddr mem₂ idx ms ds := by
    intro idx ms
    revert idx
    induction ms with
    | nil =>
      intro idx ds _
      cases ds <;> rfl
    | cons m ms ih =>
      intro idx ds hSub
      cases ds with
      | nil => rfl
      | cons d ds =>
        unfold evalMaskedLoadMirLanes
        have hTail :
            evalMaskedLoadMirLanes w ptrBits elemSize baseAddr mem₁ (idx + 1) ms ds =
              evalMaskedLoadMirLanes w ptrBits elemSize baseAddr mem₂ (idx + 1) ms ds := by
          apply ih (idx + 1) ds
          intro j m' hm' h1 h0
          have hIdx : idx + 1 + j = idx + (j + 1) := by
            rw [Nat.add_assoc, Nat.add_comm 1 j]
          rw [hIdx]
          exact hSub (j + 1) m' hm' h1 h0
        cases hm0 : Nat.beq m 0 with
        | true => dsimp; rw [hTail]
        | false =>
          dsimp
          cases hm1 : Nat.beq m (allOnes w) with
          | false => rfl
          | true =>
            dsimp
            have hHead : mem₁ (wrappingLaneAddr ptrBits baseAddr elemSize idx) =
                mem₂ (wrappingLaneAddr ptrBits baseAddr elemSize idx) := by
              have h0 := hSub 0 m rfl hm1 hm0
              rw [Nat.add_zero] at h0
              exact h0
            rw [hHead, hTail]
  unfold evalSimdMaskedLoadMir
  cases hlen : Nat.beq mask.length passthrough.length with
  | false => rfl
  | true =>
    cases halign : isAligned baseAddr (requiredAlign elemAlign vecAlign align) with
    | false => rfl
    | true =>
      apply hLanes 0 mask passthrough
      intro j m hm h1 h0
      rw [Nat.zero_add]
      exact hAgree j m hm h1 h0

/-- Concrete target-datalayout split for `SimdAlign::Vector` on `U32x4` at `baseAddr = 8`
with an all-zero mask: UB on `x86_64` (`vecAlign = 16`), valid on `s390x` (`v128:64`, `vecAlign = 8`). -/
theorem s390x_align8_vector_safe_x86_ub :
    evalSimdMaskedLoadMir 32 64 4 4 16 .vector 8 (fun _ => none) [0, 0, 0, 0] [33, 33, 33, 33] = .ubAlign ∧
    evalSimdMaskedLoadMir 32 64 4 4 8 .vector 8 (fun _ => none) [0, 0, 0, 0] [33, 33, 33, 33] = .ok [33, 33, 33, 33] := by
  exact ⟨rfl, rfl⟩

/-! ## Section 5: LE vs. BE `bitcast <N x i1> to iN` Bijection & Round-Trip -/

/-- Endian-dependent bit position of lane `idx` inside a `len`-lane `simd_bitmask` /
`simd_select_bitmask` (`rustc_const_eval/src/interpret/intrinsics/simd.rs:856-863`). -/
noncomputable def bitmaskIndex (e : Endian) (len idx : Nat) : Nat :=
  match e with
  | .little => idx
  | .big => Nat.sub (Nat.sub len 1) idx

theorem bitmaskIndex_lt (e : Endian) {len idx : Nat} (h : idx < len) :
    bitmaskIndex e len idx < len := by
  cases e with
  | little => exact h
  | big =>
    unfold bitmaskIndex
    have hpos : 0 < len := Nat.lt_of_le_of_lt (Nat.zero_le idx) h
    exact Nat.lt_of_le_of_lt (Nat.sub_le (Nat.sub len 1) idx) (nat_sub_one_lt_self hpos)

theorem bitmaskIndex_inj (e : Endian) {len i j : Nat}
    (hi : i < len) (hj : j < len)
    (heq : bitmaskIndex e len i = bitmaskIndex e len j) : i = j := by
  cases e with
  | little => exact heq
  | big =>
    have heq' : Nat.sub (Nat.sub len 1) i = Nat.sub (Nat.sub len 1) j := heq
    have hi1 : i ≤ Nat.sub len 1 := Nat.le_sub_one_of_lt hi
    have hj1 : j ≤ Nat.sub len 1 := Nat.le_sub_one_of_lt hj
    have hsum1 : Nat.sub (Nat.sub len 1) i + i = Nat.sub len 1 := Nat.sub_add_cancel hi1
    have hsum2 : Nat.sub (Nat.sub len 1) j + j = Nat.sub len 1 := Nat.sub_add_cancel hj1
    rw [heq'] at hsum1
    exact Nat.add_left_cancel (hsum1.trans hsum2.symm)

theorem bitmaskIndex_involution_big {len idx : Nat} (h : idx < len) :
    bitmaskIndex .big len (bitmaskIndex .big len idx) = idx := by
  unfold bitmaskIndex
  have hle : idx ≤ Nat.sub len 1 := Nat.le_sub_one_of_lt h
  exact nat_sub_sub_self hle

/-- Helper loop packing a list of booleans from lane index `idx` onward into a `Nat` bitmask,
matching `lean-miri/Miri/Interpreter/IntrinsicSimd.lean:372` (`bits + 2^(bitIndex e len idx)`). -/
noncomputable def packBitmaskAux (e : Endian) (totalLen : Nat) : Nat → List Bool → Nat
  | _, [] => 0
  | idx, b :: bs =>
    let rest := packBitmaskAux e totalLen (idx + 1) bs
    if b then rest + Nat.pow 2 (bitmaskIndex e totalLen idx) else rest

/-- `simd_bitmask` packing for an arbitrary lane list `bs` under endianness `e`. -/
noncomputable def packBitmask (e : Endian) (bs : List Bool) : Nat :=
  packBitmaskAux e bs.length 0 bs

/-- Lane selection directly from a bitmask integer (`simd_select_bitmask`). -/
noncomputable def selectByBitmaskAux {α : Type} (e : Endian) (totalLen maskBits : Nat) :
    Nat → List α → List α → List α
  | _, [], _ => []
  | _, _, [] => []
  | idx, y :: ys, n :: ns =>
    let chosen := if bitAt maskBits (bitmaskIndex e totalLen idx) then y else n
    chosen :: selectByBitmaskAux e totalLen maskBits (idx + 1) ys ns

noncomputable def selectByBitmask {α : Type} (e : Endian) (maskBits : Nat)
    (yes no : List α) : List α :=
  selectByBitmaskAux e yes.length maskBits 0 yes no

/-- Reference lanewise `simd_select` using a boolean mask list. -/
noncomputable def selectByBoolList {α : Type} : List Bool → List α → List α → List α
  | [], _, _ => []
  | _, [], _ => []
  | _, _, [] => []
  | b :: bs, y :: ys, n :: ns =>
    (if b then y else n) :: selectByBoolList bs ys ns

/-- Little-endian invariant: every bit set in `packBitmaskAux .little totalLen idx bs` is at
position `>= idx`, so the packed integer is a multiple of `2^idx`. -/
private theorem packBitmaskAux_le_mul (totalLen : Nat) :
    ∀ (idx : Nat) (bs : List Bool),
      ∃ q, packBitmaskAux .little totalLen idx bs = q * Nat.pow 2 idx
  | idx, [] => ⟨0, by unfold packBitmaskAux; rw [Nat.zero_mul]⟩
  | idx, b :: bs => by
    let ⟨q, hq⟩ := packBitmaskAux_le_mul totalLen (idx + 1) bs
    unfold packBitmaskAux
    have hpow : Nat.pow 2 (idx + 1) = 2 * Nat.pow 2 idx := by
      change Nat.pow 2 idx * 2 = 2 * Nat.pow 2 idx
      exact Nat.mul_comm _ _
    rw [hq, hpow]
    cases b with
    | false =>
      exact ⟨q * 2, by dsimp; rw [Nat.mul_assoc]⟩
    | true =>
      exact ⟨q * 2 + 1, by
        unfold bitmaskIndex
        dsimp
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]⟩

/-- Big-endian invariant: every bit set in `packBitmaskAux .big totalLen idx bs` lies strictly
below `totalLen - idx` when `idx + bs.length <= totalLen`, so the packed integer is `< 2^(totalLen - idx)`. -/
private theorem packBitmaskAux_be_lt (totalLen : Nat) :
    ∀ (idx : Nat) (bs : List Bool),
      idx + bs.length ≤ totalLen →
      packBitmaskAux .big totalLen idx bs < Nat.pow 2 (Nat.sub totalLen idx)
  | idx, [], _ => by
    unfold packBitmaskAux
    exact two_pow_pos (Nat.sub totalLen idx)
  | idx, b :: bs, hbound => by
    have hbound' : (idx + 1) + bs.length ≤ totalLen := by
      have hEq : (idx + 1) + bs.length = idx + (bs.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 bs.length]
      rw [hEq]
      exact hbound
    have ih := packBitmaskAux_be_lt totalLen (idx + 1) bs hbound'
    have hltIdx : idx < totalLen :=
      Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.zero_lt_succ bs.length)) hbound
    have hsubComm : Nat.sub totalLen (idx + 1) = Nat.sub (Nat.sub totalLen 1) idx := by
      rw [nat_sub_sub, Nat.add_comm 1 idx]
    have hsubEq : Nat.sub totalLen idx = Nat.sub (Nat.sub totalLen 1) idx + 1 := by
      rw [← hsubComm]
      have hpos : 1 ≤ Nat.sub totalLen idx := Nat.sub_pos_of_lt hltIdx
      have hstep : Nat.sub totalLen (idx + 1) = Nat.sub (Nat.sub totalLen idx) 1 :=
        (nat_sub_sub totalLen idx 1).symm
      rw [hstep]
      exact (Nat.sub_add_cancel hpos).symm
    rw [hsubComm] at ih
    rw [hsubEq, two_pow_succ_eq]
    unfold packBitmaskAux
    cases b with
    | false =>
      exact Nat.lt_of_lt_of_le ih (Nat.le_add_right _ _)
    | true =>
      unfold bitmaskIndex
      exact Nat.add_lt_add_right ih _

private theorem bitAt_add_pow2_of_mul_succ {q k : Nat} :
    bitAt (q * Nat.pow 2 (k + 1) + Nat.pow 2 k) k = true := by
  unfold bitAt
  have hp : 0 < Nat.pow 2 k := two_pow_pos k
  have hEq : q * Nat.pow 2 (k + 1) + Nat.pow 2 k =
      0 + (q * 2 + 1) * Nat.pow 2 k := by
    change q * (Nat.pow 2 k * 2) + Nat.pow 2 k = 0 + (q * 2 + 1) * Nat.pow 2 k
    rw [Nat.zero_add, Nat.add_mul, Nat.one_mul, Nat.mul_comm (Nat.pow 2 k) 2, Nat.mul_assoc]
  rw [hEq, nat_add_mul_div_right _ _ hp, nat_div_zero_left, Nat.zero_add]
  rw [Nat.add_comm (q * 2) 1, Nat.mul_comm q 2, nat_add_mul_mod_self_left]
  rfl

private theorem bitAt_add_pow2_of_mul_gt {q k d : Nat} :
    bitAt (q * Nat.pow 2 (k + 1) + Nat.pow 2 k) (k + 1 + d) =
      bitAt (q * Nat.pow 2 (k + 1)) (k + 1 + d) := by
  unfold bitAt
  have hp1 : 0 < Nat.pow 2 (k + 1) := two_pow_pos (k + 1)
  have hpD : 0 < Nat.pow 2 d := two_pow_pos d
  have hpow : Nat.pow 2 (k + 1 + d) = Nat.pow 2 (k + 1) * Nat.pow 2 d := two_pow_add (k + 1) d
  rw [hpow]
  have hdiv1 : Nat.div (q * Nat.pow 2 (k + 1) + Nat.pow 2 k) (Nat.pow 2 (k + 1) * Nat.pow 2 d) =
      Nat.div (Nat.div (q * Nat.pow 2 (k + 1) + Nat.pow 2 k) (Nat.pow 2 (k + 1))) (Nat.pow 2 d) :=
    (nat_div_div_eq_div_mul _ _ _).symm
  have hdiv2 : Nat.div (q * Nat.pow 2 (k + 1)) (Nat.pow 2 (k + 1) * Nat.pow 2 d) =
      Nat.div (Nat.div (q * Nat.pow 2 (k + 1)) (Nat.pow 2 (k + 1))) (Nat.pow 2 d) :=
    (nat_div_div_eq_div_mul _ _ _).symm
  rw [hdiv1, hdiv2]
  have hlt : Nat.pow 2 k < Nat.pow 2 (k + 1) := by
    rw [two_pow_succ_eq k]
    exact Nat.lt_add_of_pos_right (two_pow_pos k)
  have hA : Nat.div (q * Nat.pow 2 (k + 1) + Nat.pow 2 k) (Nat.pow 2 (k + 1)) = q := by
    rw [Nat.add_comm, nat_add_mul_div_right _ _ hp1, nat_div_eq_of_lt hlt, Nat.zero_add]
  have hB : Nat.div (q * Nat.pow 2 (k + 1)) (Nat.pow 2 (k + 1)) = q := by
    have h0 := nat_add_mul_div_right 0 q hp1
    rw [Nat.zero_add, nat_div_zero_left, Nat.zero_add] at h0
    exact h0
  rw [hA, hB]

private theorem bitAt_mul_two_pow_succ_self (q k : Nat) :
    bitAt (q * Nat.pow 2 (k + 1)) k = false := by
  unfold bitAt
  have hp : 0 < Nat.pow 2 k := two_pow_pos k
  have hEq : q * Nat.pow 2 (k + 1) = 0 + (q * 2) * Nat.pow 2 k := by
    change q * (Nat.pow 2 k * 2) = 0 + (q * 2) * Nat.pow 2 k
    rw [Nat.zero_add, Nat.mul_comm (Nat.pow 2 k) 2, Nat.mul_assoc]
  rw [hEq, nat_add_mul_div_right _ _ hp, nat_div_zero_left, Nat.zero_add]
  have h0 : Nat.mod (0 + 2 * q) 2 = 0 := by rw [nat_add_mul_mod_self_left]
  rw [Nat.mul_comm q 2, ← Nat.zero_add (2 * q), h0]
  rfl

private theorem bitAt_add_pow2_of_lt_self {r k : Nat} (hr : r < Nat.pow 2 k) :
    bitAt (r + Nat.pow 2 k) k = true := by
  unfold bitAt
  have hp : 0 < Nat.pow 2 k := two_pow_pos k
  rw [nat_add_div_right r hp, nat_div_eq_of_lt hr]
  rfl

private theorem bitAt_lt_pow2_self {r k : Nat} (hr : r < Nat.pow 2 k) :
    bitAt r k = false := by
  unfold bitAt
  rw [nat_div_eq_of_lt hr]
  rfl

private theorem bitAt_add_pow2_of_lt_pos {r j d : Nat} :
    bitAt (r + Nat.pow 2 (j + 1 + d)) j = bitAt r j := by
  unfold bitAt
  have hp : 0 < Nat.pow 2 j := two_pow_pos j
  have hpow : Nat.pow 2 (j + 1 + d) = (2 * Nat.pow 2 d) * Nat.pow 2 j := by
    rw [Nat.add_assoc, two_pow_add j (1 + d)]
    have h1 : Nat.pow 2 (1 + d) = 2 * Nat.pow 2 d := by
      rw [Nat.add_comm 1 d]
      change Nat.pow 2 d * 2 = 2 * Nat.pow 2 d
      exact Nat.mul_comm _ _
    rw [h1, Nat.mul_comm]
  rw [hpow, nat_add_mul_div_right _ _ hp, nat_add_mul_mod_self_left]

private theorem bitAt_packBitmaskAux_le (totalLen : Nat) :
    ∀ (idx : Nat) (bs : List Bool) (j : Nat),
      j < bs.length →
      bitAt (packBitmaskAux .little totalLen idx bs) (idx + j) = getBoolD bs j
  | idx, [], j, hj => by cases hj
  | idx, b :: bs, 0, _ => by
    rw [Nat.add_zero]
    unfold packBitmaskAux getBoolD
    let ⟨q, hq⟩ := packBitmaskAux_le_mul totalLen (idx + 1) bs
    rw [hq]
    cases b with
    | false => exact bitAt_mul_two_pow_succ_self q idx
    | true =>
      unfold bitmaskIndex
      exact bitAt_add_pow2_of_mul_succ
  | idx, b :: bs, j + 1, hj => by
    have hj' : j < bs.length := Nat.lt_of_succ_lt_succ hj
    have ih := bitAt_packBitmaskAux_le totalLen (idx + 1) bs j hj'
    have hIdx : idx + (j + 1) = idx + 1 + j := by
      rw [Nat.add_assoc, Nat.add_comm 1 j]
    rw [hIdx]
    unfold packBitmaskAux getBoolD
    cases b with
    | false => exact ih
    | true =>
      unfold bitmaskIndex
      let ⟨q, hq⟩ := packBitmaskAux_le_mul totalLen (idx + 1) bs
      rw [hq] at ih
      rw [hq]
      exact bitAt_add_pow2_of_mul_gt.trans ih

private theorem bitAt_packBitmaskAux_be (totalLen : Nat) :
    ∀ (idx : Nat) (bs : List Bool) (j : Nat),
      idx + bs.length ≤ totalLen →
      j < bs.length →
      bitAt (packBitmaskAux .big totalLen idx bs) (bitmaskIndex .big totalLen (idx + j)) =
        getBoolD bs j
  | idx, [], j, _, hj => by cases hj
  | idx, b :: bs, 0, hbound, _ => by
    rw [Nat.add_zero]
    have hbound' : (idx + 1) + bs.length ≤ totalLen := by
      have hEq : (idx + 1) + bs.length = idx + (bs.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 bs.length]
      rw [hEq]
      exact hbound
    have hlt := packBitmaskAux_be_lt totalLen (idx + 1) bs hbound'
    have hsubEq : Nat.sub totalLen (idx + 1) = Nat.sub (Nat.sub totalLen 1) idx := by
      rw [nat_sub_sub, Nat.add_comm 1 idx]
    rw [hsubEq] at hlt
    unfold packBitmaskAux getBoolD bitmaskIndex
    cases b with
    | false => exact bitAt_lt_pow2_self hlt
    | true => exact bitAt_add_pow2_of_lt_self hlt
  | idx, b :: bs, j + 1, hbound, hj => by
    have hbound' : (idx + 1) + bs.length ≤ totalLen := by
      have hEq : (idx + 1) + bs.length = idx + (bs.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 bs.length]
      rw [hEq]
      exact hbound
    have hj' : j < bs.length := Nat.lt_of_succ_lt_succ hj
    have ih := bitAt_packBitmaskAux_be totalLen (idx + 1) bs j hbound' hj'
    have hIdx : idx + (j + 1) = (idx + 1) + j := by
      rw [Nat.add_assoc, Nat.add_comm 1 j]
    rw [hIdx]
    unfold packBitmaskAux getBoolD
    cases b with
    | false => exact ih
    | true =>
      have hltPos : bitmaskIndex .big totalLen ((idx + 1) + j) < bitmaskIndex .big totalLen idx := by
        unfold bitmaskIndex
        have hltLen : (idx + 1) + j < totalLen :=
          Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj' (idx + 1)) hbound'
        have hle1 : (idx + 1) + j ≤ Nat.sub totalLen 1 := Nat.le_sub_one_of_lt hltLen
        have hle2 : idx ≤ Nat.sub totalLen 1 :=
          Nat.le_trans (Nat.le_trans (Nat.le_succ idx) (Nat.le_add_right (idx + 1) j)) hle1
        have hsum1 : Nat.sub (Nat.sub totalLen 1) ((idx + 1) + j) + ((idx + 1) + j) =
            Nat.sub totalLen 1 := Nat.sub_add_cancel hle1
        have hsum2 : Nat.sub (Nat.sub totalLen 1) idx + idx = Nat.sub totalLen 1 :=
          Nat.sub_add_cancel hle2
        have hltIdx : idx < (idx + 1) + j :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self idx) (Nat.le_add_right (idx + 1) j)
        have hStrict :
            Nat.sub (Nat.sub totalLen 1) ((idx + 1) + j) + idx <
              Nat.sub (Nat.sub totalLen 1) idx + idx := by
          have hStep :
              Nat.sub (Nat.sub totalLen 1) ((idx + 1) + j) + idx <
                Nat.sub (Nat.sub totalLen 1) ((idx + 1) + j) + ((idx + 1) + j) :=
            Nat.add_lt_add_left hltIdx _
          exact Nat.lt_of_lt_of_eq hStep (hsum1.trans hsum2.symm)
        exact nat_lt_of_add_lt_add_right hStrict
      have hDiff : bitmaskIndex .big totalLen idx =
          bitmaskIndex .big totalLen ((idx + 1) + j) + 1 +
            Nat.sub (bitmaskIndex .big totalLen idx)
              (bitmaskIndex .big totalLen ((idx + 1) + j) + 1) :=
        (nat_add_sub_cancel_of_le hltPos).symm
      rw [hDiff]
      exact bitAt_add_pow2_of_lt_pos.trans ih

/-- Exact bit-extraction theorem for `packBitmask` under BOTH little-endian and big-endian. -/
theorem bitAt_packBitmask (e : Endian) (bs : List Bool) {i : Nat} (hi : i < bs.length) :
    bitAt (packBitmask e bs) (bitmaskIndex e bs.length i) = getBoolD bs i := by
  unfold packBitmask
  cases e with
  | little =>
    have h := bitAt_packBitmaskAux_le bs.length 0 bs i hi
    rw [Nat.zero_add] at h
    exact h
  | big =>
    have h := bitAt_packBitmaskAux_be bs.length 0 bs i (by rw [Nat.zero_add]; exact Nat.le_refl _) hi
    rw [Nat.zero_add] at h
    exact h

/-- Endian bit-reversal bijection: lane `i` sits at bit `i` in the LE bitmask and at
bit `N - 1 - i` in the BE bitmask. -/
theorem bitmask_le_be_reversal (bs : List Bool) {i : Nat} (hi : i < bs.length) :
    bitAt (packBitmask .little bs) i =
      bitAt (packBitmask .big bs) (Nat.sub (Nat.sub bs.length 1) i) := by
  have hle := bitAt_packBitmask .little bs hi
  have hbe := bitAt_packBitmask .big bs hi
  exact hle.trans hbe.symm

private theorem selectByBitmaskAux_eq_selectByBoolList {α : Type} (e : Endian)
    (totalLen maskBits : Nat) :
    ∀ (idx : Nat) (bs : List Bool) (yes no : List α),
      bs.length = yes.length →
      yes.length = no.length →
      (∀ j, j < bs.length →
        bitAt maskBits (bitmaskIndex e totalLen (idx + j)) = getBoolD bs j) →
      selectByBitmaskAux e totalLen maskBits idx yes no = selectByBoolList bs yes no := by
  intro idx bs
  revert idx
  induction bs with
  | nil =>
    intro idx yes no hlen1 _ _
    cases yes with
    | nil => rfl
    | cons _ _ => cases hlen1
  | cons b bs ih =>
    intro idx yes no hlen1 hlen2 hbits
    cases yes with
    | nil => cases hlen1
    | cons y ys =>
      cases no with
      | nil => cases hlen2
      | cons n ns =>
        unfold selectByBitmaskAux selectByBoolList
        have hhead : bitAt maskBits (bitmaskIndex e totalLen idx) = b := by
          have h0 := hbits 0 (Nat.zero_lt_succ bs.length)
          rw [Nat.add_zero] at h0
          exact h0
        rw [hhead]
        have hlen1' : bs.length = ys.length := Nat.succ.inj hlen1
        have hlen2' : ys.length = ns.length := Nat.succ.inj hlen2
        have htail : selectByBitmaskAux e totalLen maskBits (idx + 1) ys ns =
            selectByBoolList bs ys ns := by
          apply ih (idx + 1) ys ns hlen1' hlen2'
          intro j hj
          have hIdxEq : (idx + 1) + j = idx + (j + 1) := by
            rw [Nat.add_assoc, Nat.add_comm 1 j]
          rw [hIdxEq]
          exact hbits (j + 1) (Nat.succ_lt_succ hj)
        rw [htail]

private theorem map_maskMsb_eq_map_maskLsb {w : Nat} (hw : 2 ≤ w) :
    ∀ (ms : List Nat), IsCanonicalMask w ms →
      ms.map (maskMsbLshrTrunc w) = ms.map maskLsb
  | [], _ => rfl
  | m :: tl, hcanon => by
    have hm : IsCanonicalMaskLane w m := hcanon m (List.Mem.head tl)
    have htl : IsCanonicalMask w tl := fun x hx => hcanon x (List.Mem.tail m hx)
    have hbit := (canonical_mask_unifies_msb_and_lsb hw hm).1
    change maskMsbLshrTrunc w m :: tl.map (maskMsbLshrTrunc w) = maskLsb m :: tl.map maskLsb
    rw [hbit, map_maskMsb_eq_map_maskLsb hw tl htl]

/-- **Theorem 3 (LE vs. BE `bitcast <N x i1> to iN` Bijection & Round-Trip):**
For BOTH `.little` (`x86_64`) and `.big` (`s390x`) endiannesses, packing a canonical mask
`ms` via `simd_bitmask` (`packBitmask e (ms.map (maskMsbLshrTrunc w))`) and feeding the
resulting integer into `simd_select_bitmask` (`selectByBitmask e`) reproduces lanewise
selection identically, independent of endianness—and equals selection using LSB extraction. -/
theorem simd_bitmask_select_roundtrip_both_endians {α : Type}
    (e : Endian) {w : Nat} (hw : 2 ≤ w)
    (ms : List Nat) (yes no : List α)
    (hcanon : IsCanonicalMask w ms)
    (hlen1 : ms.length = yes.length) (hlen2 : yes.length = no.length) :
    selectByBitmask e (packBitmask e (ms.map (maskMsbLshrTrunc w))) yes no =
      selectByBoolList (ms.map maskLsb) yes no := by
  rw [map_maskMsb_eq_map_maskLsb hw ms hcanon]
  unfold selectByBitmask
  have hlenBs : (ms.map maskLsb).length = yes.length := by
    rw [list_length_map]
    exact hlen1
  rw [← hlenBs]
  apply selectByBitmaskAux_eq_selectByBoolList e (ms.map maskLsb).length
    (packBitmask e (ms.map maskLsb)) 0 (ms.map maskLsb) yes no hlenBs hlen2
  intro j hj
  rw [Nat.zero_add]
  exact bitAt_packBitmask e (ms.map maskLsb) hj

/-- Concrete 8-lane bitmask endianness witness matching live Miri execution:
lanes `{0, 2}` active yield `0x05` (`5`) on LE (`x86_64`) and `0xA0` (`160`) on BE (`s390x`). -/
theorem bitmask_8lane_le_0x05_be_0xa0 :
    packBitmask .little [true, false, true, false, false, false, false, false] = 5 ∧
    packBitmask .big [true, false, true, false, false, false, false, false] = 160 := by
  exact ⟨rfl, rfl⟩

/-! ## Section 6: Float-to-Unsigned Cast (`simd_as` vs. `simd_cast`) & Sharpness Counterexamples -/

/-- Classification of an IEEE-754 floating-point lane relative to an unsigned target integer
range `[0, maxVal]` (e.g., `maxVal = 255` for `u8`). -/
inductive FloatLaneClass (maxVal : Nat) where
  | nan
  | negInf
  | posInf
  | negFinite
  | inRange (truncVal : Nat) (hLe : truncVal ≤ maxVal)
  | tooLarge (truncVal : Nat) (hGt : maxVal < truncVal)

/-- Result of unchecked `simd_cast` (`fptoui` in LLVM, `float_to_int_checked` in `rustc_const_eval`). -/
inductive CastOutcome where
  | ok (val : Nat)
  | poisonOrUb

/-- Saturating `simd_as` (`@llvm.fptoui.sat.v4i8.v4f32`): total over all IEEE-754 inputs,
mapping `NaN` and negative values to `0` and out-of-range positive values to `maxVal`. -/
noncomputable def evalSimdAsUnsigned {maxVal : Nat} : FloatLaneClass maxVal → Nat
  | .nan => 0
  | .negInf => 0
  | .negFinite => 0
  | .inRange n _ => n
  | .tooLarge _ _ => maxVal
  | .posInf => maxVal

/-- Unchecked `simd_cast` (`fptoui` in LLVM / `float_to_int_checked` in Miri):
yields `.ok n` strictly inside `[0, maxVal]` and `.poisonOrUb` otherwise. -/
noncomputable def evalSimdCastUnsigned {maxVal : Nat} : FloatLaneClass maxVal → CastOutcome
  | .inRange n _ => .ok n
  | _ => .poisonOrUb

theorem simd_as_agrees_with_simd_cast_in_range {maxVal : Nat} (n : Nat) (h : n ≤ maxVal) :
    evalSimdCastUnsigned (.inRange n h) = .ok (evalSimdAsUnsigned (.inRange n h)) :=
  rfl

/-- **Sharpness Counterexample 1 (`+1` Non-`{0, -1}` Mask Lane):**
At lane width `w = 32`, `m = 1` violates `IsCanonicalMaskLane 32 1`, and diverges between
MSB lowerings (`rustc_codegen_llvm` `vector_mask_to_bitmask` / `icmp slt 0` -> `false`)
and LSB/nonzero lowerings (`trunc i1`, `core::simd::Mask::to_array` `& 1`, `cranelift` `brif`,
`gcc` `!= 0` -> `true`). -/
theorem ce1_plus1_mask_diverges_msb_vs_lsb :
    ¬ IsCanonicalMaskLane 32 1 ∧
    maskMsbLshrTrunc 32 1 = false ∧
    maskMsbSignCmp 32 1 = false ∧
    maskLsb 1 = true ∧
    maskNonZero 1 = true ∧
    maskMsbLshrTrunc 32 1 ≠ maskLsb 1 := by
  refine ⟨?_, rfl, rfl, rfl, rfl, (fun h => by cases h)⟩
  intro h
  cases h with
  | inl h0 => cases h0
  | inr h1 =>
    have hneq : Nat.beq 1 (allOnes 32) = false := rfl
    rw [h1] at hneq
    rw [Nat.beq_refl] at hneq
    cases hneq

/-- **Sharpness Counterexample 2 (Unconditional Alignment Under All-Zero Mask):**
At `baseAddr = 1` with all-zero mask `[0, 0, 0, 0]` and `SimdAlign::Element` (`elemAlign = 4`),
BOTH MIR/Miri `simd_masked_load` and LLVM `@llvm.masked.load` (`Argument(0) align 4`) fault
with `.ubAlign` even though zero lanes read memory; switching to `SimdAlign::Unaligned`
succeeds with `[55, 55, 55, 55]`, and `baseAddr = 0` (`null()`) succeeds under `SimdAlign::Vector`. -/
theorem ce2_all_zero_mask_misaligned_violates_llvm_align_attr :
    evalSimdMaskedLoadMir 32 64 4 4 16 .element 1 (fun _ => none) [0, 0, 0, 0] [0, 0, 0, 0] = .ubAlign ∧
    evalLlvmMaskedLoad 32 64 4 4 16 .element 1 (fun _ => none) [0, 0, 0, 0] [0, 0, 0, 0] = .ubAlign ∧
    evalSimdMaskedLoadMir 32 64 4 4 16 .unaligned 1 (fun _ => none) [0, 0, 0, 0] [55, 55, 55, 55] = .ok [55, 55, 55, 55] ∧
    evalSimdMaskedLoadMir 32 64 4 4 16 .vector 0 (fun _ => none) [0, 0, 0, 0] [77, 77, 77, 77] = .ok [77, 77, 77, 77] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Sharpness Counterexample 3 (Unchecked `simd_cast` OOB/NaN Poison vs. `simd_as` Saturation):**
Converting `300.0_f32` or `NaN` to `u8` (`maxVal = 255`) triggers `.poisonOrUb` under
`simd_cast` (`fptoui` / Miri `float_to_int_checked`), whereas `simd_as` (`@llvm.fptoui.sat`)
deterministically saturates `300.0 -> 255` and `NaN -> 0`. -/
theorem ce3_unchecked_simd_cast_oob_poison :
    (let c300 : FloatLaneClass 255 := .tooLarge 300 (by decide)
     evalSimdCastUnsigned c300 = .poisonOrUb ∧ evalSimdAsUnsigned c300 = 255) ∧
    (let cNan : FloatLaneClass 255 := .nan
     evalSimdCastUnsigned cNan = .poisonOrUb ∧ evalSimdAsUnsigned cNan = 0) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ## Section 7: MCP#838 MIR Validator Prohibition on `#[repr(simd)]` Field Projection -/

/-- ADT representation class relevant to `AdtDef::can_project_fields`
(`compiler/rustc_middle/src/ty/adt.rs:222-226`, `rustc_mir_transform/src/validate.rs:718-732`). -/
inductive AdtKind where
  | ordinary
  | reprSimd
  | reprScalable
  | dynMetadata

noncomputable def AdtKind.decEq (a b : AdtKind) : Decidable (a = b) :=
  match a, b with
  | .ordinary, .ordinary => isTrue rfl
  | .reprSimd, .reprSimd => isTrue rfl
  | .reprScalable, .reprScalable => isTrue rfl
  | .dynMetadata, .dynMetadata => isTrue rfl
  | .ordinary, .reprSimd => isFalse (fun h => by cases h)
  | .ordinary, .reprScalable => isFalse (fun h => by cases h)
  | .ordinary, .dynMetadata => isFalse (fun h => by cases h)
  | .reprSimd, .ordinary => isFalse (fun h => by cases h)
  | .reprSimd, .reprScalable => isFalse (fun h => by cases h)
  | .reprSimd, .dynMetadata => isFalse (fun h => by cases h)
  | .reprScalable, .ordinary => isFalse (fun h => by cases h)
  | .reprScalable, .reprSimd => isFalse (fun h => by cases h)
  | .reprScalable, .dynMetadata => isFalse (fun h => by cases h)
  | .dynMetadata, .ordinary => isFalse (fun h => by cases h)
  | .dynMetadata, .reprSimd => isFalse (fun h => by cases h)
  | .dynMetadata, .reprScalable => isFalse (fun h => by cases h)

noncomputable instance : DecidableEq AdtKind := AdtKind.decEq

/-- Recursive simplified MIR type tree (with manual `DecidableEq`, no `deriving`). -/
inductive MirValTy where
  | scalar
  | array (elem : MirValTy) (len : Nat)
  | adt (kind : AdtKind) (field0 : MirValTy)

noncomputable def MirValTy.decEq : ∀ a b : MirValTy, Decidable (a = b)
  | .scalar, .scalar => isTrue rfl
  | .array e1 n1, .array e2 n2 =>
    match MirValTy.decEq e1 e2 with
    | isFalse h => isFalse (fun hEq => by injection hEq with h1 _; exact h h1)
    | isTrue h1 =>
      match Nat.decEq n1 n2 with
      | isFalse h => isFalse (fun hEq => by injection hEq with _ h2; exact h h2)
      | isTrue h2 => isTrue (by rw [h1, h2])
  | .adt k1 f1, .adt k2 f2 =>
    match AdtKind.decEq k1 k2 with
    | isFalse h => isFalse (fun hEq => by injection hEq with h1 _; exact h h1)
    | isTrue h1 =>
      match MirValTy.decEq f1 f2 with
      | isFalse h => isFalse (fun hEq => by injection hEq with _ h2; exact h h2)
      | isTrue h2 => isTrue (by rw [h1, h2])
  | .scalar, .array _ _ => isFalse (fun h => by cases h)
  | .scalar, .adt _ _ => isFalse (fun h => by cases h)
  | .array _ _, .scalar => isFalse (fun h => by cases h)
  | .array _ _, .adt _ _ => isFalse (fun h => by cases h)
  | .adt _ _, .scalar => isFalse (fun h => by cases h)
  | .adt _ _, .array _ _ => isFalse (fun h => by cases h)

noncomputable instance : DecidableEq MirValTy := MirValTy.decEq

/-- Recursive MIR projection chain (single-field projection `.field0` or identity `.here`). -/
inductive MirProjChain where
  | here
  | field0 (rest : MirProjChain)

noncomputable def MirProjChain.decEq : ∀ a b : MirProjChain, Decidable (a = b)
  | .here, .here => isTrue rfl
  | .field0 r1, .field0 r2 =>
    match MirProjChain.decEq r1 r2 with
    | isTrue h => isTrue (by rw [h])
    | isFalse h => isFalse (fun hEq => by injection hEq with h1; exact h h1)
  | .here, .field0 _ => isFalse (fun h => by cases h)
  | .field0 _, .here => isFalse (fun h => by cases h)

noncomputable instance : DecidableEq MirProjChain := MirProjChain.decEq

/-- Mirror of `AdtDef::can_project_fields` (`compiler/rustc_middle/src/ty/adt.rs:222-226`). -/
noncomputable def canProjectFields : AdtKind → Bool
  | .ordinary => true
  | .reprSimd => false
  | .reprScalable => false
  | .dynMetadata => false

/-- MIR validator outcome for place projection checking (`validate.rs:718-732`). -/
inductive MirValidateOutcome where
  | valid (ty : MirValTy)
  | iceBannedSimdProjection
  | iceOtherInvalidProjection

/-- Recursive MIR `TypeChecker` place-projection validator mirroring
`rustc_mir_transform/src/validate.rs:718-732`. Note that `isUnsafeFn : Bool` is ignored:
MCP#838 rejects SIMD field projections identically in `#![forbid(unsafe_code)]` safe code
and `unsafe` code alike. -/
noncomputable def validateMirPlace (_isUnsafeFn : Bool) :
    MirValTy → MirProjChain → MirValidateOutcome
  | ty, .here => .valid ty
  | .adt kind field0Ty, .field0 rest =>
    if canProjectFields kind then
      validateMirPlace _isUnsafeFn field0Ty rest
    else
      match kind with
      | .reprSimd => .iceBannedSimdProjection
      | _ => .iceOtherInvalidProjection
  | _, .field0 _ => .iceOtherInvalidProjection

/-- **Theorem 5 (MCP#838 Safe-Code ICE Invariant):** Projecting `.0` into any
`#[repr(simd)]` struct (such as `#[repr(simd)] pub struct U32x4(pub [u32; 4])`) fails
MIR `Validator` with `.iceBannedSimdProjection` for EVERY safety level `isUnsafeFn`
(including `isUnsafeFn = false`, i.e., `#![forbid(unsafe_code)]`), whereas ordinary
structs project cleanly. -/
theorem mcp838_forbids_simd_field_projection (isUnsafeFn : Bool)
    (innerTy : MirValTy) (rest : MirProjChain) :
    validateMirPlace isUnsafeFn (.adt .reprSimd innerTy) (.field0 rest) =
      .iceBannedSimdProjection ∧
    validateMirPlace false (.adt .ordinary (.array .scalar 4)) (.field0 .here) =
      .valid (.array .scalar 4) := by
  exact ⟨rfl, rfl⟩

end Anneal.Simd.MaskedLoadBitmaskMcp838
