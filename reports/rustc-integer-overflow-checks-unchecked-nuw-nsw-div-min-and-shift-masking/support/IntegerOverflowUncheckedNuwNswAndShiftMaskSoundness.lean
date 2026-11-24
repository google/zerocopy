/-!
# Soundness and Refinement of `rustc` Integer Overflow Checks, Mandatory `Div`/`Rem` Guards,
# `unchecked_*` `nuw`/`nsw` Poison Semantics, and Safe Shift Bit-Width Masking

This self-contained Lean 4 (`v4.34.1`) mechanization formalizes the three-tier integer arithmetic
architecture of `rustc` (`compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs`,
`compiler/rustc_codegen_ssa/src/mir/{block.rs, rvalue.rs}`,
`compiler/rustc_codegen_ssa/src/base.rs`, `compiler/rustc_codegen_llvm/src/builder.rs`,
`compiler/rustc_const_eval/src/interpret/operator.rs`, and `library/core/src/num/int_macros.rs`)
paired with the LLVM Language Reference (`llvm/docs/LangRef.md`) and Anneal's MIR semantics
(`Trusted.MirSemantics`):

1. **Profile-dependent `-C overflow-checks` semantics (`on` vs. `off`)** for `+`, `-`, `*`,
   unary `-`, and safe shifts (`<<`, `>>`): checked-panic vs. deterministic two's-complement
   wrapping / bit-width-masked shifts.
2. **Profile-independent mandatory `Div`/`Rem` guards** (`b == 0` and signed
   `a == INT_MIN && b == -1`): proving that guarding these exact two inputs eliminates every
   undefined LLVM `udiv`/`sdiv`/`urem`/`srem` input across all widths `w >= 2` (and clarifying
   why `srem` is guarded on `(INT_MIN, -1)` despite `INT_MIN.tmod (-1) = 0` fitting in range).
3. **`unsafe` `unchecked_*` intrinsics (`nuw`/`nsw` poison vs. Miri immediate UB)** and exact
   three-way bit-level agreement on non-overflowing inputs, alongside explicit separation
   witnesses (`nuw` vs. `nsw`, `nsw` `sgt` folding soundness vs. wrapping failure, and
   `-C overflow-checks=off` wrapping determinism vs. `unchecked_add` poison).
4. **Safe shift bit-width masking (`b &&& (2^k - 1)`)**: proving total poison- and UB-freedom
   for arbitrary power-of-two widths `w = 2^k`, mixed signed-RHS `zext` preservation for
   `k <= r` (matching `build_shift_expr_rhs` in `base.rs`), and the `512`-bit counterexample
   for `i8` RHS (`k = 9, r = 8`).

All definitions carry explicit `noncomputable def` modifiers (with no `noncomputable section`,
no `partial def`, no `deriving` clauses on inductives/structures, and zero `._unsafe_rec`
compiler helpers), and all proofs are constructive (`0 Classical.choice`, `0 sorry`, `0 omega`,
`0 bv_decide`, `0 native_decide`).
-/

namespace RustcIntOverflow

/-! ## Part I: Semantic Outcome Domains and Refinement Preorders -/

/-- Integer signedness mode (`TyKind::Uint` vs. `TyKind::Int`). -/
inductive Signedness where
  | unsigned
  | signed

namespace Signedness

/-- Structural boolean equality on `Signedness`. -/
noncomputable def beq : Signedness → Signedness → Bool
  | .unsigned, .unsigned => true
  | .signed, .signed => true
  | _, _ => false

theorem beq_refl (s : Signedness) : beq s s = true := by
  cases s <;> rfl

theorem eq_of_beq_true {s₁ s₂ : Signedness} (h : beq s₁ s₂ = true) : s₁ = s₂ := by
  cases s₁ <;> cases s₂ <;> first | rfl | exact Bool.noConfusion h

theorem beq_eq_true_iff (s₁ s₂ : Signedness) : beq s₁ s₂ = true ↔ s₁ = s₂ :=
  ⟨eq_of_beq_true, fun h => h ▸ beq_refl s₁⟩

end Signedness

/-- Compilation profile flag `-C overflow-checks={on, off}`. -/
inductive OverflowProfile where
  | checksOn
  | checksOff

namespace OverflowProfile

/-- Convert `OverflowProfile` to `Bool` (`true` iff `-C overflow-checks=on`). -/
noncomputable def toBool : OverflowProfile → Bool
  | .checksOn => true
  | .checksOff => false

/-- Structural boolean equality on `OverflowProfile`. -/
noncomputable def beq : OverflowProfile → OverflowProfile → Bool
  | .checksOn, .checksOn => true
  | .checksOff, .checksOff => true
  | _, _ => false

theorem toBool_checksOn : toBool .checksOn = true := rfl
theorem toBool_checksOff : toBool .checksOff = false := rfl

end OverflowProfile

/-- LLVM IR SSA value domain for width-`w` integers (`BitVec w` or `poison`). -/
inductive PoisonVal (w : Nat) where
  | val (bits : BitVec w)
  | poison

namespace PoisonVal

/-- Structural boolean equality on `PoisonVal w`. -/
noncomputable def beq {w : Nat} : PoisonVal w → PoisonVal w → Bool
  | .val a, .val b => a == b
  | .poison, .poison => true
  | _, _ => false

/-- Alive2-style pointwise value refinement: `tgt` refines `src` (`tgt ⊑ src`) iff either
`src` is `poison` (which any concrete value or `poison` refines) or `tgt = src`. -/
noncomputable def Refines {w : Nat} (tgt src : PoisonVal w) : Prop :=
  src = .poison ∨ tgt = src

theorem refines_refl {w : Nat} (x : PoisonVal w) : Refines x x :=
  Or.inr rfl

theorem refines_trans {w : Nat} {a b c : PoisonVal w}
    (hab : Refines a b) (hbc : Refines b c) : Refines a c := by
  cases hbc with
  | inl hc => exact Or.inl hc
  | inr hbe =>
    subst hbe
    exact hab

theorem refines_poison_top {w : Nat} (tgt : PoisonVal w) : Refines tgt .poison :=
  Or.inl rfl

theorem eq_of_refines_val {w : Nat} {tgt : PoisonVal w} {v : BitVec w}
    (h : Refines tgt (.val v)) : tgt = .val v := by
  cases h with
  | inl hp => cases hp
  | inr heq => exact heq

end PoisonVal

/-- Unified execution outcome across MIR panics, LLVM deferred `poison`, and immediate UB
(Rust Abstract Machine / Miri / LLVM `sdiv` zero-or-overflow / `ret noundef poison`). -/
inductive ExecOutcome (w : Nat) where
  | ok (bits : BitVec w)
  | panic
  | poison
  | immediateUB

namespace ExecOutcome

/-- Structural boolean equality on `ExecOutcome w`. -/
noncomputable def beq {w : Nat} : ExecOutcome w → ExecOutcome w → Bool
  | .ok a, .ok b => a == b
  | .panic, .panic => true
  | .poison, .poison => true
  | .immediateUB, .immediateUB => true
  | _, _ => false

/-- Lift a `PoisonVal w` directly into `ExecOutcome w` (keeping deferred `poison`). -/
noncomputable def ofPoisonVal {w : Nat} : PoisonVal w → ExecOutcome w
  | .val bv => .ok bv
  | .poison => .poison

/-- Lower a `PoisonVal w` across an LLVM `noundef` ABI boundary (`ret noundef`, parameter
passing, or branch condition), where `poison` becomes immediate UB (`LangRef.md`
"Poison Values"). -/
noncomputable def lowerNoundef {w : Nat} : PoisonVal w → ExecOutcome w
  | .val bv => .ok bv
  | .poison => .immediateUB

/-- Program refinement order on `ExecOutcome w` (`tgt ⊑ src`):
- `src = .immediateUB` allows any target behavior (`ok`, `panic`, `poison`, `immediateUB`);
- `src = .poison` is refined by any `.ok bv` or `.poison` (poison may be refined into any
  concrete bit-vector or kept as poison, though not turned into an observable `panic`);
- `src = .panic` is refined only by `.panic` (safe Rust panic determinism);
- `src = .ok bv` is refined only by `.ok bv`. -/
noncomputable def Refines {w : Nat} (tgt src : ExecOutcome w) : Prop :=
  match src with
  | .immediateUB => True
  | .poison => tgt = .poison ∨ (∃ bv : BitVec w, tgt = .ok bv)
  | .panic => tgt = .panic
  | .ok bv => tgt = .ok bv

theorem refines_refl {w : Nat} (x : ExecOutcome w) : Refines x x := by
  cases x with
  | ok bv => rfl
  | panic => rfl
  | poison => exact Or.inl rfl
  | immediateUB => trivial

theorem refines_trans {w : Nat} {a b c : ExecOutcome w}
    (hab : Refines a b) (hbc : Refines b c) : Refines a c := by
  cases c with
  | immediateUB => trivial
  | panic =>
    dsimp [Refines] at hbc
    subst hbc
    exact hab
  | ok bv =>
    dsimp [Refines] at hbc
    subst hbc
    exact hab
  | poison =>
    dsimp [Refines] at hbc
    cases hbc with
    | inl hbp =>
      subst hbp
      exact hab
    | inr hbv =>
      rcases hbv with ⟨bv, hbv⟩
      subst hbv
      dsimp [Refines] at hab
      subst hab
      exact Or.inr ⟨bv, rfl⟩

theorem refines_immediateUB_top {w : Nat} (tgt : ExecOutcome w) :
    Refines tgt .immediateUB :=
  trivial

theorem refines_of_poisonRefines {w : Nat} {t s : PoisonVal w}
    (h : PoisonVal.Refines t s) : Refines (ofPoisonVal t) (ofPoisonVal s) := by
  cases s with
  | poison =>
    cases t with
    | poison => exact Or.inl rfl
    | val bv => exact Or.inr ⟨bv, rfl⟩
  | val bv =>
    have ht := PoisonVal.eq_of_refines_val h
    subst ht
    rfl

theorem refines_lowerNoundef_of_poisonRefines {w : Nat} {t s : PoisonVal w}
    (h : PoisonVal.Refines t s) : Refines (lowerNoundef t) (lowerNoundef s) := by
  cases s with
  | poison => trivial
  | val bv =>
    have ht := PoisonVal.eq_of_refines_val h
    subst ht
    rfl

theorem not_ok_refines_panic {w : Nat} (bv : BitVec w) : ¬ Refines (.ok bv) .panic := by
  intro h
  dsimp [Refines] at h
  cases h

theorem not_panic_refines_ok {w : Nat} (bv : BitVec w) : ¬ Refines .panic (.ok bv) := by
  intro h
  dsimp [Refines] at h
  cases h

theorem not_immediateUB_refines_ok {w : Nat} (bv : BitVec w) :
    ¬ Refines .immediateUB (.ok bv) := by
  intro h
  dsimp [Refines] at h
  cases h

theorem not_poison_refines_ok {w : Nat} (bv : BitVec w) :
    ¬ Refines .poison (.ok bv) := by
  intro h
  dsimp [Refines] at h
  cases h

end ExecOutcome

/-! ## Part II: Constructive `BitVec w` Two's-Complement Bounds and Overflow Predicates -/

/-- Unsigned maximum mathematical value at width `w`: `2^w - 1`. -/
noncomputable def uMaxNat (w : Nat) : Nat :=
  2 ^ w - 1

/-- Minimum signed mathematical value at width `w >= 1`: `-2^(w - 1)`. -/
noncomputable def sMinInt (w : Nat) : Int :=
  -(Int.ofNat (2 ^ (w - 1)))

/-- Maximum signed mathematical value at width `w >= 1`: `2^(w - 1) - 1`. -/
noncomputable def sMaxInt (w : Nat) : Int :=
  Int.ofNat (2 ^ (w - 1)) - 1

/-- Membership in the `w`-bit unsigned integer range `[0, 2^w)`. -/
noncomputable def inUnsignedRange (w : Nat) (z : Int) : Prop :=
  0 ≤ z ∧ z < Int.ofNat (2 ^ w)

/-- Membership in the `w`-bit two's-complement signed integer range `[-2^(w-1), 2^(w-1))`. -/
noncomputable def inSignedRange (w : Nat) (z : Int) : Prop :=
  sMinInt w ≤ z ∧ z ≤ sMaxInt w

/-- Boolean unsigned range test on `Int`. -/
noncomputable def inUnsignedRangeBool (w : Nat) (z : Int) : Bool :=
  decide (0 ≤ z) && decide (z < Int.ofNat (2 ^ w))

/-- Boolean signed range test on `Int`. -/
noncomputable def inSignedRangeBool (w : Nat) (z : Int) : Bool :=
  decide (sMinInt w ≤ z) && decide (z ≤ sMaxInt w)

theorem pow2_pos (n : Nat) : 0 < 2 ^ n :=
  Nat.pow_pos (by decide : 0 < 2)

theorem pow2_ge_one (n : Nat) : 1 ≤ 2 ^ n :=
  pow2_pos n

theorem pow2_ge_two_of_pos {n : Nat} (hn : 1 ≤ n) : 2 ≤ 2 ^ n := by
  have h1 : 2 ^ 1 ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hn
  exact h1

theorem pow2_pred_lt_pow2 {w : Nat} (hw : 1 ≤ w) :
    2 ^ (w - 1) < 2 ^ w := by
  have hlt : 2 ^ (w - 1) < 2 ^ (w - 1) + 2 ^ (w - 1) :=
    Nat.lt_add_of_pos_right (pow2_pos (w - 1))
  have heq : 2 ^ (w - 1) + 2 ^ (w - 1) = 2 ^ w := by
    have hsucc : w - 1 + 1 = w := Nat.sub_add_cancel hw
    calc
      2 ^ (w - 1) + 2 ^ (w - 1) = 2 * 2 ^ (w - 1) := (Nat.two_mul _).symm
      _ = 2 ^ (w - 1) * 2 := Nat.mul_comm 2 _
      _ = 2 ^ (w - 1 + 1) := (Nat.pow_succ 2 (w - 1)).symm
      _ = 2 ^ w := by rw [hsucc]
  rw [heq] at hlt
  exact hlt

theorem pow2_twice_pred_eq {w : Nat} (hw : 1 ≤ w) :
    2 * 2 ^ (w - 1) = 2 ^ w := by
  have hsucc : w - 1 + 1 = w := Nat.sub_add_cancel hw
  calc
    2 * 2 ^ (w - 1) = 2 ^ (w - 1) * 2 := Nat.mul_comm 2 (2 ^ (w - 1))
    _ = 2 ^ (w - 1 + 1) := (Nat.pow_succ 2 (w - 1)).symm
    _ = 2 ^ w := by rw [hsucc]

theorem pow2_pred_eq_half {w : Nat} (hw : 1 ≤ w) :
    2 ^ (w - 1) = 2 ^ w / 2 := by
  have heq : 2 * 2 ^ (w - 1) = 2 ^ w := pow2_twice_pred_eq hw
  calc
    2 ^ (w - 1) = (2 ^ (w - 1) * 2) / 2 :=
      (Nat.mul_div_cancel (2 ^ (w - 1)) (by decide : 0 < 2)).symm
    _ = (2 * 2 ^ (w - 1)) / 2 := by rw [Nat.mul_comm]
    _ = 2 ^ w / 2 := by rw [heq]

theorem pow2_pred_ge_two_of_ge_two {w : Nat} (hw : 2 ≤ w) :
    2 ≤ 2 ^ (w - 1) := by
  have hw1 : 1 ≤ w - 1 := Nat.le_sub_of_add_le hw
  exact pow2_ge_two_of_pos hw1

theorem pow2_succ_eq_twice (k : Nat) : 2 ^ (k + 1) = 2 * 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem sMinInt_neg_eq (w : Nat) : -(sMinInt w) = Int.ofNat (2 ^ (w - 1)) := by
  dsimp [sMinInt]
  exact Int.neg_neg _

theorem inSignedRange_iff_lt {w : Nat} (z : Int) :
    inSignedRange w z ↔ -(Int.ofNat (2 ^ (w - 1))) ≤ z ∧ z < Int.ofNat (2 ^ (w - 1)) := by
  dsimp [inSignedRange, sMinInt, sMaxInt]
  constructor
  · intro ⟨hlo, hhi⟩
    refine ⟨hlo, ?_⟩
    have h1 : z ≤ Int.ofNat (2 ^ (w - 1)) - 1 := hhi
    exact Int.lt_of_le_sub_one h1
  · intro ⟨hlo, hhi⟩
    exact ⟨hlo, Int.le_sub_one_of_lt hhi⟩

theorem toNat_lt_pow2_pred_of_msb_false {w : Nat} {x : BitVec w} (h : x.msb = false) :
    x.toNat < 2 ^ (w - 1) := by
  rw [BitVec.msb_eq_toNat] at h
  exact Nat.lt_of_not_le (of_decide_eq_false h)

theorem pow2_pred_le_toNat_of_msb_true {w : Nat} {x : BitVec w} (h : x.msb = true) :
    2 ^ (w - 1) ≤ x.toNat := by
  rw [BitVec.msb_eq_toNat] at h
  exact of_decide_eq_true h

theorem toInt_of_msb_false {w : Nat} (hw : 1 ≤ w) {x : BitVec w} (h : x.msb = false) :
    x.toInt = Int.ofNat x.toNat ∧ x.toNat < 2 ^ (w - 1) := by
  have hlt : x.toNat < 2 ^ (w - 1) := toNat_lt_pow2_pred_of_msb_false h
  have h2lt : 2 * x.toNat < 2 ^ w := by
    rw [← pow2_twice_pred_eq hw]
    exact Nat.mul_lt_mul_of_pos_left hlt (by decide : 0 < 2)
  refine ⟨?_, hlt⟩
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [h2lt, ↓reduceIte]
  rfl

theorem toInt_of_msb_true {w : Nat} (hw : 1 ≤ w) {x : BitVec w} (h : x.msb = true) :
    x.toInt = -Int.ofNat (-x).toNat ∧ 1 ≤ (-x).toNat ∧ (-x).toNat ≤ 2 ^ (w - 1) := by
  have hge : 2 ^ (w - 1) ≤ x.toNat := pow2_pred_le_toNat_of_msb_true h
  have hpos : 0 < x.toNat := Nat.lt_of_lt_of_le (pow2_pos (w - 1)) hge
  have hsub_lt : 2 ^ w - x.toNat < 2 ^ w := Nat.sub_lt (pow2_pos w) hpos
  have hneg_toNat : (-x).toNat = 2 ^ w - x.toNat := by
    rw [BitVec.toNat_neg]
    exact Nat.mod_eq_of_lt hsub_lt
  have h2ge : ¬ (2 * x.toNat < 2 ^ w) := by
    rw [← pow2_twice_pred_eq hw]
    exact Nat.not_lt_of_ge (Nat.mul_le_mul_left 2 hge)
  have hint : x.toInt = -Int.ofNat (2 ^ w - x.toNat) := by
    rw [BitVec.toInt_eq_toNat_cond]
    simp only [h2ge, ↓reduceIte]
    have hle : x.toNat ≤ 2 ^ w := Nat.le_of_lt x.isLt
    have hsub : Int.ofNat (2 ^ w - x.toNat) = Int.ofNat (2 ^ w) - Int.ofNat x.toNat :=
      Int.ofNat_sub hle
    change Int.ofNat x.toNat - Int.ofNat (2 ^ w) = -Int.ofNat (2 ^ w - x.toNat)
    rw [hsub, Int.neg_sub]
  have hpos_neg : 1 ≤ 2 ^ w - x.toNat := Nat.sub_pos_of_lt x.isLt
  have hle_neg : 2 ^ w - x.toNat ≤ 2 ^ (w - 1) := by
    have hsub2 : 2 ^ w - 2 ^ (w - 1) = 2 ^ (w - 1) := by
      have heq := pow2_twice_pred_eq hw
      rw [Nat.two_mul] at heq
      rw [← heq]
      exact Nat.add_sub_self_left _ _
    rw [← hsub2]
    exact Nat.sub_le_sub_left hge (2 ^ w)
  rw [hneg_toNat]
  exact ⟨hint, hpos_neg, hle_neg⟩

theorem bitvec_toInt_inSignedRange {w : Nat} (a : BitVec w) :
    inSignedRange w a.toInt := by
  rw [inSignedRange_iff_lt]
  cases w with
  | zero =>
    have ha0 : a.toNat = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ a.isLt)
    have ha_bv : a = 0#0 := BitVec.eq_of_toNat_eq ha0
    rw [ha_bv, BitVec.toInt_zero]
    decide
  | succ k =>
    have hw1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    cases hmsb : a.msb with
    | false =>
      have ⟨heq, hlt⟩ := toInt_of_msb_false hw1 hmsb
      rw [heq]
      exact ⟨Int.le_trans (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) (Int.natCast_nonneg _),
             Int.ofNat_lt.mpr hlt⟩
    | true =>
      have ⟨heq, _, hle⟩ := toInt_of_msb_true hw1 hmsb
      rw [heq]
      refine ⟨Int.neg_le_neg (Int.ofNat_le.mpr hle), ?_⟩
      exact Int.lt_of_le_of_lt (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _))
        (Int.ofNat_lt.mpr (pow2_pos _))

theorem bitvec_toNat_inUnsignedRange {w : Nat} (a : BitVec w) :
    inUnsignedRange w (Int.ofNat a.toNat) := by
  refine ⟨Int.natCast_nonneg a.toNat, ?_⟩
  exact Int.ofNat_lt.mpr a.isLt

theorem intMinBv_toInt {w : Nat} (hw : 1 ≤ w) :
    (BitVec.intMin w).toInt = sMinInt w := by
  have hlt : 2 ^ (w - 1) < 2 ^ w := pow2_pred_lt_pow2 hw
  have hmod : 2 ^ (w - 1) % 2 ^ w = 2 ^ (w - 1) := Nat.mod_eq_of_lt hlt
  rw [BitVec.toInt_intMin, hmod]
  rfl

theorem intMaxBv_toInt {w : Nat} (_hw : 1 ≤ w) :
    (BitVec.intMax w).toInt = sMaxInt w := by
  rw [BitVec.toInt_intMax]
  rfl

theorem allOnesBv_toInt {w : Nat} (hw : 1 ≤ w) :
    (BitVec.allOnes w).toInt = -1 := by
  have hpos : 0 < w := hw
  rw [BitVec.toInt_allOnes]
  simp [hpos]

theorem negOneLit_eq_allOnes (w : Nat) : (-1#w : BitVec w) = BitVec.allOnes w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_neg, BitVec.toNat_allOnes]
  simp only [BitVec.toNat_ofNat]
  cases w with
  | zero => simp
  | succ k =>
    have hgt : 1 < 2 ^ (k + 1) := pow2_ge_two_of_pos (Nat.succ_le_succ (Nat.zero_le k))
    have hmod1 : 1 % 2 ^ (k + 1) = 1 := Nat.mod_eq_of_lt hgt
    rw [hmod1]
    have hlt : 2 ^ (k + 1) - 1 < 2 ^ (k + 1) :=
      Nat.sub_lt (pow2_pos (k + 1)) (by decide : 0 < 1)
    exact Nat.mod_eq_of_lt hlt

theorem negOneLit_toInt {w : Nat} (hw : 1 ≤ w) :
    (-1#w : BitVec w).toInt = -1 := by
  rw [negOneLit_eq_allOnes]
  exact allOnesBv_toInt hw

theorem toInt_eq_sMinInt_iff {w : Nat} (hw : 1 ≤ w) (a : BitVec w) :
    a.toInt = sMinInt w ↔ a = BitVec.intMin w := by
  constructor
  · intro h
    apply BitVec.toInt_inj.mp
    rw [h, intMinBv_toInt hw]
  · intro h
    subst h
    exact intMinBv_toInt hw

theorem toInt_eq_neg_one_iff {w : Nat} (hw : 1 ≤ w) (b : BitVec w) :
    b.toInt = -1 ↔ b = BitVec.allOnes w := by
  constructor
  · intro h
    apply BitVec.toInt_inj.mp
    rw [h, allOnesBv_toInt hw]
  · intro h
    subst h
    exact allOnesBv_toInt hw

theorem toInt_eq_zero_iff {w : Nat} (b : BitVec w) :
    b.toInt = 0 ↔ b = 0#w := by
  constructor
  · intro h
    apply BitVec.toInt_inj.mp
    rw [h, BitVec.toInt_zero]
  · intro h
    subst h
    exact BitVec.toInt_zero

theorem intMin_ne_zero {w : Nat} (hw : 1 ≤ w) : BitVec.intMin w ≠ 0#w := by
  intro h
  have h1 : (BitVec.intMin w).toInt = (0#w).toInt := congrArg BitVec.toInt h
  rw [intMinBv_toInt hw, BitVec.toInt_zero] at h1
  change -(Int.ofNat (2 ^ (w - 1))) = 0 at h1
  have hpos : 0 < Int.ofNat (2 ^ (w - 1)) := Int.ofNat_lt.mpr (pow2_pos (w - 1))
  have hneg : -(Int.ofNat (2 ^ (w - 1))) < -0 := Int.neg_lt_neg hpos
  change -(Int.ofNat (2 ^ (w - 1))) < 0 at hneg
  rw [h1] at hneg
  exact Int.lt_irrefl 0 hneg

theorem allOnes_ne_zero {w : Nat} (hw : 1 ≤ w) : BitVec.allOnes w ≠ 0#w := by
  intro h
  have h1 : (BitVec.allOnes w).toInt = (0#w).toInt := congrArg BitVec.toInt h
  rw [allOnesBv_toInt hw, BitVec.toInt_zero] at h1
  exact Int.noConfusion h1

theorem intMin_ne_allOnes {w : Nat} (hw : 2 ≤ w) : BitVec.intMin w ≠ BitVec.allOnes w := by
  intro h
  have hw1 : 1 ≤ w := Nat.le_trans (by decide : 1 ≤ 2) hw
  have h1 : (BitVec.intMin w).toInt = (BitVec.allOnes w).toInt := congrArg BitVec.toInt h
  rw [intMinBv_toInt hw1, allOnesBv_toInt hw1] at h1
  change -(Int.ofNat (2 ^ (w - 1))) = -1 at h1
  have hp2 : 2 ≤ 2 ^ (w - 1) := pow2_pred_ge_two_of_ge_two hw
  have hle : Int.ofNat 2 ≤ Int.ofNat (2 ^ (w - 1)) := Int.ofNat_le.mpr hp2
  have hneg : -(Int.ofNat (2 ^ (w - 1))) ≤ -(2 : Int) := Int.neg_le_neg hle
  rw [h1] at hneg
  exact (by decide : ¬ ((-1 : Int) ≤ (-2 : Int))) hneg

theorem bmod_eq_self_of_inSignedRange {w : Nat} (hw : 1 ≤ w) {z : Int}
    (hz : inSignedRange w z) : z.bmod (2 ^ w) = z := by
  have hlo : -(Int.ofNat (2 ^ w) / 2) ≤ z := by
    have hhalf : 2 ^ w / 2 = 2 ^ (w - 1) := (pow2_pred_eq_half hw).symm
    have hdiv : Int.ofNat (2 ^ w) / 2 = Int.ofNat (2 ^ (w - 1)) := by
      calc
        Int.ofNat (2 ^ w) / 2 = Int.ofNat (2 ^ w / 2) := rfl
        _ = Int.ofNat (2 ^ (w - 1)) := by rw [← hhalf]
    rw [hdiv]
    exact hz.1
  have hhi : z < (Int.ofNat (2 ^ w) + 1) / 2 := by
    have hlt : z < Int.ofNat (2 ^ (w - 1)) := (inSignedRange_iff_lt z).mp hz |>.2
    have hhalf : 2 ^ (w - 1) = 2 ^ w / 2 := pow2_pred_eq_half hw
    have hle : Int.ofNat (2 ^ (w - 1)) ≤ (Int.ofNat (2 ^ w) + 1) / 2 := by
      have hdiv2 : Int.ofNat (2 ^ w) / 2 ≤ (Int.ofNat (2 ^ w) + 1) / 2 := by
        exact Int.ediv_le_ediv (by decide : 0 < (2 : Int)) (Int.le_add_of_nonneg_right (by decide : 0 ≤ (1 : Int)))
      calc
        Int.ofNat (2 ^ (w - 1)) = Int.ofNat (2 ^ w / 2) := by rw [hhalf]
        _ = Int.ofNat (2 ^ w) / 2 := rfl
        _ ≤ (Int.ofNat (2 ^ w) + 1) / 2 := hdiv2
    exact Int.lt_of_lt_of_le hlt hle
  exact Int.bmod_eq_of_le hlo hhi

/-- Constructive boolean overflow check for unsigned addition (`a.toNat + b.toNat >= 2^w`). -/
noncomputable def uAddOv {w : Nat} (a b : BitVec w) : Bool :=
  decide (2 ^ w ≤ a.toNat + b.toNat)

/-- Constructive boolean overflow check for signed addition (`a.toInt + b.toInt ∉ [-2^(w-1), 2^(w-1))`). -/
noncomputable def sAddOv {w : Nat} (a b : BitVec w) : Bool :=
  !inSignedRangeBool w (a.toInt + b.toInt)

/-- Constructive boolean overflow check for unsigned subtraction (`a.toNat < b.toNat`). -/
noncomputable def uSubOv {w : Nat} (a b : BitVec w) : Bool :=
  decide (a.toNat < b.toNat)

/-- Constructive boolean overflow check for signed subtraction (`a.toInt - b.toInt ∉ [-2^(w-1), 2^(w-1))`). -/
noncomputable def sSubOv {w : Nat} (a b : BitVec w) : Bool :=
  !inSignedRangeBool w (a.toInt - b.toInt)

/-- Constructive boolean overflow check for unsigned multiplication (`a.toNat * b.toNat >= 2^w`). -/
noncomputable def uMulOv {w : Nat} (a b : BitVec w) : Bool :=
  decide (2 ^ w ≤ a.toNat * b.toNat)

/-- Constructive boolean overflow check for signed multiplication (`a.toInt * b.toInt ∉ [-2^(w-1), 2^(w-1))`). -/
noncomputable def sMulOv {w : Nat} (a b : BitVec w) : Bool :=
  !inSignedRangeBool w (a.toInt * b.toInt)

/-- Constructive boolean overflow check for signed unary negation (`w >= 1 ∧ a == BitVec.intMin w`). -/
noncomputable def sNegOv {w : Nat} (a : BitVec w) : Bool :=
  decide (1 ≤ w) && (a == BitVec.intMin w)

theorem inSignedRangeBool_true_iff (w : Nat) (z : Int) :
    inSignedRangeBool w z = true ↔ inSignedRange w z := by
  dsimp [inSignedRangeBool, inSignedRange]
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

theorem uAddOv_false_iff {w : Nat} (a b : BitVec w) :
    uAddOv a b = false ↔ a.toNat + b.toNat < 2 ^ w := by
  dsimp [uAddOv]
  rw [decide_eq_false_iff_not]
  exact Nat.not_le

theorem sAddOv_false_iff {w : Nat} (a b : BitVec w) :
    sAddOv a b = false ↔ inSignedRange w (a.toInt + b.toInt) := by
  dsimp [sAddOv]
  rw [Bool.not_eq_false']
  exact inSignedRangeBool_true_iff w (a.toInt + b.toInt)

theorem uSubOv_false_iff {w : Nat} (a b : BitVec w) :
    uSubOv a b = false ↔ b.toNat ≤ a.toNat := by
  dsimp [uSubOv]
  rw [decide_eq_false_iff_not]
  exact Nat.not_lt

theorem sSubOv_false_iff {w : Nat} (a b : BitVec w) :
    sSubOv a b = false ↔ inSignedRange w (a.toInt - b.toInt) := by
  dsimp [sSubOv]
  rw [Bool.not_eq_false']
  exact inSignedRangeBool_true_iff w (a.toInt - b.toInt)

theorem uMulOv_false_iff {w : Nat} (a b : BitVec w) :
    uMulOv a b = false ↔ a.toNat * b.toNat < 2 ^ w := by
  dsimp [uMulOv]
  rw [decide_eq_false_iff_not]
  exact Nat.not_le

theorem sMulOv_false_iff {w : Nat} (a b : BitVec w) :
    sMulOv a b = false ↔ inSignedRange w (a.toInt * b.toInt) := by
  dsimp [sMulOv]
  rw [Bool.not_eq_false']
  exact inSignedRangeBool_true_iff w (a.toInt * b.toInt)

theorem sNegOv_false_iff {w : Nat} (hw : 1 ≤ w) (a : BitVec w) :
    sNegOv a = false ↔ a ≠ BitVec.intMin w := by
  dsimp [sNegOv]
  have hdec : decide (1 ≤ w) = true := decide_eq_true hw
  rw [hdec, Bool.true_and, beq_eq_false_iff_ne]

theorem toNat_add_eq_of_noOv {w : Nat} {a b : BitVec w} (h : uAddOv a b = false) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt ((uAddOv_false_iff a b).mp h)

theorem toInt_add_eq_of_noOv {w : Nat} (hw : 1 ≤ w) {a b : BitVec w} (h : sAddOv a b = false) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [BitVec.toInt_add]
  exact bmod_eq_self_of_inSignedRange hw ((sAddOv_false_iff a b).mp h)

theorem toNat_sub_eq_of_noOv {w : Nat} {a b : BitVec w} (h : uSubOv a b = false) :
    (a - b).toNat = a.toNat - b.toNat := by
  have hle : b.toNat ≤ a.toNat := (uSubOv_false_iff a b).mp h
  have hsub : 2 ^ w - b.toNat + a.toNat = 2 ^ w + (a.toNat - b.toNat) := by
    have hb : b.toNat ≤ 2 ^ w := Nat.le_of_lt b.isLt
    calc
      2 ^ w - b.toNat + a.toNat = (2 ^ w - b.toNat) + (b.toNat + (a.toNat - b.toNat)) := by
        rw [Nat.add_sub_of_le hle]
      _ = ((2 ^ w - b.toNat) + b.toNat) + (a.toNat - b.toNat) := by
        rw [Nat.add_assoc]
      _ = 2 ^ w + (a.toNat - b.toNat) := by
        rw [Nat.sub_add_cancel hb]
  rw [BitVec.toNat_sub, hsub, Nat.add_mod_left]
  have hlt : a.toNat - b.toNat < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.sub_le a.toNat b.toNat) a.isLt
  exact Nat.mod_eq_of_lt hlt

theorem toInt_sub_eq_of_noOv {w : Nat} (hw : 1 ≤ w) {a b : BitVec w} (h : sSubOv a b = false) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [BitVec.toInt_sub]
  exact bmod_eq_self_of_inSignedRange hw ((sSubOv_false_iff a b).mp h)

theorem toNat_mul_eq_of_noOv {w : Nat} {a b : BitVec w} (h : uMulOv a b = false) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt ((uMulOv_false_iff a b).mp h)

theorem toInt_mul_eq_of_noOv {w : Nat} (hw : 1 ≤ w) {a b : BitVec w} (h : sMulOv a b = false) :
    (a * b).toInt = a.toInt * b.toInt := by
  rw [BitVec.toInt_mul]
  exact bmod_eq_self_of_inSignedRange hw ((sMulOv_false_iff a b).mp h)

theorem toInt_neg_eq_of_noOv {w : Nat} (hw : 1 ≤ w) {a : BitVec w} (h : sNegOv a = false) :
    (-a).toInt = -a.toInt :=
  BitVec.toInt_neg_of_ne_intMin ((sNegOv_false_iff hw a).mp h)

/-! ## Part III: Safe & Unchecked Division/Remainder (`as_rvalue.rs` + LLVM `sdiv`/`srem`) -/

/-- Guard 1 in `Builder::build_binary_op` (`as_rvalue.rs:531-541`): divisor equals zero. -/
noncomputable def divZeroGuard {w : Nat} (b : BitVec w) : Bool :=
  b == 0#w

/-- Guard 2 in `Builder::build_binary_op` (`as_rvalue.rs:545-578`): signed `INT_MIN` divided
or modulo by `-1`. -/
noncomputable def sdivOverflowGuard {w : Nat} (a b : BitVec w) : Bool :=
  (a == BitVec.intMin w) && (b == BitVec.allOnes w)

/-- LLVM `udiv`/`sdiv`/`urem`/`srem` definedness side-condition (`LangRef.md`
`11503-11504`, `11546-11549`, `11623-11625`, `11671-11678`).
Undefined (`false`) on division/remainder by zero (all types) or `(INT_MIN, -1)` (signed). -/
noncomputable def llvmDivRemDefined {w : Nat} (s : Signedness) (a b : BitVec w) : Bool :=
  match s with
  | .unsigned => !divZeroGuard b
  | .signed => !divZeroGuard b && !sdivOverflowGuard a b

/-- LLVM `udiv` / `sdiv` operational semantics (`immediateUB` when `!llvmDivRemDefined`). -/
noncomputable def evalLlvmDiv {w : Nat} (s : Signedness) (a b : BitVec w) : ExecOutcome w :=
  match llvmDivRemDefined s a b with
  | false => .immediateUB
  | true =>
    match s with
    | .unsigned => .ok (a / b)
    | .signed => .ok (a.sdiv b)

/-- LLVM `urem` / `srem` operational semantics (`immediateUB` when `!llvmDivRemDefined`). -/
noncomputable def evalLlvmRem {w : Nat} (s : Signedness) (a b : BitVec w) : ExecOutcome w :=
  match llvmDivRemDefined s a b with
  | false => .immediateUB
  | true =>
    match s with
    | .unsigned => .ok (a % b)
    | .signed => .ok (a.srem b)

/-- Safe Rust `/` lowering (`as_rvalue.rs:520-580`, `block.rs:773`, `terminator.rs:172-176`):
ignores `OverflowProfile` and emits mandatory `DivisionByZero` and signed `Overflow(Div)`
panic guards before `udiv`/`sdiv`. -/
noncomputable def evalRustSafeDiv {w : Nat} (_prof : OverflowProfile)
    (s : Signedness) (a b : BitVec w) : ExecOutcome w :=
  match divZeroGuard b with
  | true => .panic
  | false =>
    match s with
    | .unsigned => evalLlvmDiv .unsigned a b
    | .signed =>
      match sdivOverflowGuard a b with
      | true => .panic
      | false => evalLlvmDiv .signed a b

/-- Safe Rust `%` lowering (`as_rvalue.rs:520-580`, `block.rs:773`, `terminator.rs:172-176`):
ignores `OverflowProfile` and emits mandatory `RemainderByZero` and signed `Overflow(Rem)`
panic guards before `urem`/`srem`. -/
noncomputable def evalRustSafeRem {w : Nat} (_prof : OverflowProfile)
    (s : Signedness) (a b : BitVec w) : ExecOutcome w :=
  match divZeroGuard b with
  | true => .panic
  | false =>
    match s with
    | .unsigned => evalLlvmRem .unsigned a b
    | .signed =>
      match sdivOverflowGuard a b with
      | true => .panic
      | false => evalLlvmRem .signed a b

/-- Unchecked Rust `intrinsics::unchecked_div` / `unchecked_rem` (Miri `operator.rs:201-224`,
`270-273`; LLVM bare `udiv`/`sdiv`/`urem`/`srem`). -/
noncomputable def evalUncheckedDiv {w : Nat} (s : Signedness) (a b : BitVec w) : ExecOutcome w :=
  evalLlvmDiv s a b

/-- Unchecked Rust `intrinsics::unchecked_rem`. -/
noncomputable def evalUncheckedRem {w : Nat} (s : Signedness) (a b : BitVec w) : ExecOutcome w :=
  evalLlvmRem s a b

/-- Helper lemma: `b.toInt.natAbs ≤ 2^(w-1)` for all `b : BitVec w`. -/
theorem toInt_natAbs_le_pow2_pred {w : Nat} (_hw : 1 ≤ w) (b : BitVec w) :
    b.toInt.natAbs ≤ 2 ^ (w - 1) := by
  have hr : inSignedRange w b.toInt := bitvec_toInt_inSignedRange b
  have hlo : -(Int.ofNat (2 ^ (w - 1))) ≤ b.toInt := hr.1
  have hlt : b.toInt < Int.ofNat (2 ^ (w - 1)) := (inSignedRange_iff_lt b.toInt).mp hr |>.2
  have habs : (b.toInt.natAbs : Int) ≤ Int.ofNat (2 ^ (w - 1)) := by
    cases hb : b.toInt with
    | ofNat m =>
      have hm : Int.ofNat m < Int.ofNat (2 ^ (w - 1)) := hb ▸ hlt
      exact Int.le_of_lt hm
    | negSucc m =>
      have hm : -(Int.ofNat (2 ^ (w - 1))) ≤ Int.negSucc m := hb ▸ hlo
      have hm2 : Int.ofNat (m + 1) ≤ Int.ofNat (2 ^ (w - 1)) := by
        have hneg := Int.neg_le_neg hm
        rw [Int.neg_neg] at hneg
        exact hneg
      exact hm2
  exact Int.ofNat_le.mp habs

/-- Helper lemma: `a.toInt.natAbs = 2^(w-1)` iff `a = BitVec.intMin w`. -/
theorem toInt_natAbs_eq_pow2_pred_iff {w : Nat} (hw : 1 ≤ w) (a : BitVec w) :
    a.toInt.natAbs = 2 ^ (w - 1) ↔ a = BitVec.intMin w := by
  have hr : inSignedRange w a.toInt := bitvec_toInt_inSignedRange a
  have hlt : a.toInt < Int.ofNat (2 ^ (w - 1)) := (inSignedRange_iff_lt a.toInt).mp hr |>.2
  constructor
  · intro heq
    cases ha : a.toInt with
    | ofNat m =>
      have hm : m = 2 ^ (w - 1) := by
        have h1 : (Int.ofNat m).natAbs = 2 ^ (w - 1) := ha ▸ heq
        exact h1
      have hlt2 : Int.ofNat m < Int.ofNat (2 ^ (w - 1)) := ha ▸ hlt
      rw [hm] at hlt2
      exact False.elim ((Int.lt_irrefl _) hlt2)
    | negSucc m =>
      have hm : m + 1 = 2 ^ (w - 1) := by
        have h1 : (Int.negSucc m).natAbs = 2 ^ (w - 1) := ha ▸ heq
        exact h1
      have hai : a.toInt = sMinInt w := by
        rw [ha]
        change Int.negSucc m = -(Int.ofNat (2 ^ (w - 1)))
        rw [← hm]
        rfl
      exact (toInt_eq_sMinInt_iff hw a).mp hai
  · intro ha
    subst ha
    rw [intMinBv_toInt hw]
    dsimp [sMinInt]
    exact Int.natAbs_neg (Int.ofNat (2 ^ (w - 1)))

/-- Constructive signedness-range bound on `(z : Int)` from `z.natAbs < 2^(w-1)`. -/
theorem inSignedRange_of_natAbs_lt {w : Nat} {z : Int}
    (hlt : z.natAbs < 2 ^ (w - 1)) : inSignedRange w z := by
  rw [inSignedRange_iff_lt]
  cases hz : z with
  | ofNat m =>
    have hm : m < 2 ^ (w - 1) := by
      have h1 : (Int.ofNat m).natAbs < 2 ^ (w - 1) := hz ▸ hlt
      exact h1
    refine ⟨?_, Int.ofNat_lt.mpr hm⟩
    exact Int.le_trans (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) (Int.natCast_nonneg m)
  | negSucc m =>
    have hm : m + 1 < 2 ^ (w - 1) := by
      have h1 : (Int.negSucc m).natAbs < 2 ^ (w - 1) := hz ▸ hlt
      exact h1
    have hlt2 : Int.ofNat (m + 1) < Int.ofNat (2 ^ (w - 1)) := Int.ofNat_lt.mpr hm
    have hneg : -(Int.ofNat (2 ^ (w - 1))) < -(Int.ofNat (m + 1)) := Int.neg_lt_neg hlt2
    have hneg_eq : -(Int.ofNat (m + 1)) = Int.negSucc m := rfl
    rw [hneg_eq] at hneg
    refine ⟨Int.le_of_lt hneg, ?_⟩
    exact Int.lt_of_lt_of_le (Int.negSucc_lt_zero m) (Int.natCast_nonneg _)

/-- When `b.toInt.natAbs ≥ 2`, `(a.toInt.tdiv b.toInt).natAbs < 2^(w-1)` for all `w ≥ 2`. -/
theorem tdiv_natAbs_lt_of_abs_ge_two {w : Nat} (hw : 2 ≤ w) (a b : BitVec w)
    (hb2 : 2 ≤ b.toInt.natAbs) :
    (a.toInt.tdiv b.toInt).natAbs < 2 ^ (w - 1) := by
  have hw1 : 1 ≤ w := Nat.le_trans (by decide : 1 ≤ 2) hw
  have ha_le : a.toInt.natAbs ≤ 2 ^ (w - 1) := toInt_natAbs_le_pow2_pred hw1 a
  have hd1 : a.toInt.natAbs / b.toInt.natAbs ≤ 2 ^ (w - 1) / b.toInt.natAbs :=
    Nat.div_le_div_right ha_le
  have hd2 : 2 ^ (w - 1) / b.toInt.natAbs ≤ 2 ^ (w - 1) / 2 :=
    Nat.div_le_div_left hb2 (by decide : 0 < 2)
  have hpos : 0 < 2 ^ (w - 1) := pow2_pos (w - 1)
  have hd3 : 2 ^ (w - 1) / 2 < 2 ^ (w - 1) :=
    Nat.div_lt_self hpos (by decide : 1 < 2)
  rw [Int.natAbs_tdiv]
  exact Nat.lt_of_le_of_lt (Nat.le_trans hd1 hd2) hd3

/-- When `b ≠ 0#w` and `b ≠ BitVec.allOnes w`, `a.toInt.tdiv b.toInt` always lies in
`inSignedRange w` (`[-2^(w-1), 2^(w-1) - 1]`). -/
theorem tdiv_inSignedRange_of_ne_neg_one {w : Nat} (hw : 2 ≤ w) (a b : BitVec w)
    (hb0 : b ≠ 0#w) (hb1 : b ≠ BitVec.allOnes w) :
    inSignedRange w (a.toInt.tdiv b.toInt) := by
  have hw1 : 1 ≤ w := Nat.le_trans (by decide : 1 ≤ 2) hw
  have hbz : b.toInt ≠ 0 := fun h => hb0 ((toInt_eq_zero_iff b).mp h)
  have hb_abs_pos : 1 ≤ b.toInt.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hbz)
  cases Nat.eq_or_lt_of_le hb_abs_pos with
  | inr hb2 =>
    exact inSignedRange_of_natAbs_lt (tdiv_natAbs_lt_of_abs_ge_two hw a b hb2)
  | inl hb_eq1 =>
    have h1 : b.toInt.natAbs = 1 := hb_eq1.symm
    cases hbi : b.toInt with
    | ofNat m =>
      have hm : m = 1 := by
        have h0 : (Int.ofNat m).natAbs = 1 := hbi ▸ h1
        exact h0
      rw [hm]
      change inSignedRange w (a.toInt.tdiv 1)
      rw [Int.tdiv_one]
      exact bitvec_toInt_inSignedRange a
    | negSucc m =>
      have hm : m + 1 = 1 := by
        have h0 : (Int.negSucc m).natAbs = 1 := hbi ▸ h1
        exact h0
      have hm0 : m = 0 := Nat.succ.inj hm
      have hb_m1 : b.toInt = -1 := by rw [hbi, hm0]; rfl
      exact False.elim (hb1 ((toInt_eq_neg_one_iff hw1 b).mp hb_m1))

/-- Core Signed Division Soundness Theorem: Across ALL `w >= 2`, guarding `b == 0#w` and
`a == BitVec.intMin w && b == BitVec.allOnes w` guarantees BOTH mathematical range containment
`inSignedRange w (a.toInt.tdiv b.toInt)` AND exact LLVM `sdiv` equality `(a.sdiv b).toInt = a.toInt.tdiv b.toInt`. -/
theorem sdiv_inSignedRange_of_guarded {w : Nat} (hw : 2 ≤ w) (a b : BitVec w)
    (hb0 : b ≠ 0#w) (hno : ¬ (a = BitVec.intMin w ∧ b = BitVec.allOnes w)) :
    inSignedRange w (a.toInt.tdiv b.toInt) ∧
    (a.sdiv b).toInt = a.toInt.tdiv b.toInt := by
  have hw1 : 1 ≤ w := Nat.le_trans (by decide : 1 ≤ 2) hw
  have hrange : inSignedRange w (a.toInt.tdiv b.toInt) := by
    cases hbeq : (b == BitVec.allOnes w) with
    | false =>
      exact tdiv_inSignedRange_of_ne_neg_one hw a b hb0 (beq_eq_false_iff_ne.mp hbeq)
    | true =>
      have hb_all : b = BitVec.allOnes w := beq_iff_eq.mp hbeq
      have ha_ne : a ≠ BitVec.intMin w := fun ha => hno ⟨ha, hb_all⟩
      have hb_int : b.toInt = -1 := by rw [hb_all]; exact allOnesBv_toInt hw1
      rw [hb_int, Int.tdiv_neg, Int.tdiv_one]
      have ha_abs_le : a.toInt.natAbs ≤ 2 ^ (w - 1) := toInt_natAbs_le_pow2_pred hw1 a
      have ha_abs_ne : a.toInt.natAbs ≠ 2 ^ (w - 1) := fun heq =>
        ha_ne ((toInt_natAbs_eq_pow2_pred_iff hw1 a).mp heq)
      have hneg_lt : (-a.toInt).natAbs < 2 ^ (w - 1) := by
        rw [Int.natAbs_neg]
        exact Nat.lt_of_le_of_ne ha_abs_le ha_abs_ne
      exact inSignedRange_of_natAbs_lt hneg_lt
  refine ⟨hrange, ?_⟩
  have toInt_ofNat_lt : ∀ {q : Nat}, q < 2 ^ (w - 1) → (BitVec.ofNat w q).toInt = Int.ofNat q := by
    intro q hq
    have hqlt : q < 2 ^ w := Nat.lt_trans hq (pow2_pred_lt_pow2 hw1)
    have hnat : (BitVec.ofNat w q).toNat = q := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hqlt
    have h2 : 2 * q < 2 ^ w := by
      rw [← pow2_twice_pred_eq hw1]
      exact Nat.mul_lt_mul_of_pos_left hq (by decide : 0 < 2)
    rw [BitVec.toInt_eq_toNat_cond, hnat]
    simp only [h2, ↓reduceIte]
    rfl
  have toInt_neg_ofNat_le : ∀ {q : Nat}, q ≤ 2 ^ (w - 1) → (-(BitVec.ofNat w q)).toInt = -Int.ofNat q := by
    intro q hq
    cases Nat.eq_zero_or_pos q with
    | inl hq0 =>
      subst hq0
      have hz : -(BitVec.ofNat w 0) = 0#w := BitVec.neg_zero w
      rw [hz, BitVec.toInt_zero]
      rfl
    | inr hqpos =>
      have hqlt : q < 2 ^ w := Nat.lt_of_le_of_lt hq (pow2_pred_lt_pow2 hw1)
      have hnat : (BitVec.ofNat w q).toNat = q := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt hqlt
      have hneg_lt : 2 ^ w - q < 2 ^ w := Nat.sub_lt (pow2_pos w) hqpos
      have hneg_nat : (-(BitVec.ofNat w q)).toNat = 2 ^ w - q := by
        rw [BitVec.toNat_neg, hnat]
        exact Nat.mod_eq_of_lt hneg_lt
      have hge : 2 ^ (w - 1) ≤ 2 ^ w - q := by
        have heq := pow2_twice_pred_eq hw1
        rw [Nat.two_mul] at heq
        have hsum : 2 ^ (w - 1) + q ≤ 2 ^ w := by
          rw [← heq]
          exact Nat.add_le_add_left hq _
        exact Nat.le_sub_of_add_le hsum
      have hmsb : (-(BitVec.ofNat w q)).msb = true := by
        rw [BitVec.msb_eq_toNat, hneg_nat]
        exact decide_eq_true hge
      have hm := toInt_of_msb_true hw1 hmsb
      have hneg_neg : (-(-(BitVec.ofNat w q))).toNat = q := by
        rw [BitVec.neg_neg, hnat]
      rw [hneg_neg] at hm
      exact hm.1
  have hdiv_eq : ∀ (x y : BitVec w), x / y = BitVec.ofNat w (x.toNat / y.toNat) := by
    intro x y
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_udiv, BitVec.toNat_ofNat]
    have hdiv_lt : x.toNat / y.toNat < 2 ^ w :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
    exact (Nat.mod_eq_of_lt hdiv_lt).symm
  change (match a.msb, b.msb with
    | false, false => a / b
    | false, true => -(a / (-b))
    | true, false => -((-a) / b)
    | true, true => (-a) / (-b)).toInt = a.toInt.tdiv b.toInt
  cases ha : a.msb <;> cases hb : b.msb
  · have ⟨hai, ha_lt⟩ := toInt_of_msb_false hw1 ha
    have ⟨hbi, _⟩ := toInt_of_msb_false hw1 hb
    have hq_lt : a.toNat / b.toNat < 2 ^ (w - 1) :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha_lt
    rw [hdiv_eq a b, toInt_ofNat_lt hq_lt, hai, hbi]
    exact Int.ofNat_tdiv a.toNat b.toNat
  · have ⟨hai, ha_lt⟩ := toInt_of_msb_false hw1 ha
    have ⟨hbi, _, _⟩ := toInt_of_msb_true hw1 hb
    have hq_le : a.toNat / (-b).toNat ≤ 2 ^ (w - 1) :=
      Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha_lt)
    rw [hdiv_eq a (-b), toInt_neg_ofNat_le hq_le, hai, hbi, Int.tdiv_neg]
    exact congrArg (-·) (Int.ofNat_tdiv a.toNat (-b).toNat)
  · have ⟨hai, _, ha_le⟩ := toInt_of_msb_true hw1 ha
    have ⟨hbi, _⟩ := toInt_of_msb_false hw1 hb
    have hq_le : (-a).toNat / b.toNat ≤ 2 ^ (w - 1) :=
      Nat.le_trans (Nat.div_le_self _ _) ha_le
    rw [hdiv_eq (-a) b, toInt_neg_ofNat_le hq_le, hai, hbi, Int.neg_tdiv]
    exact congrArg (-·) (Int.ofNat_tdiv (-a).toNat b.toNat)
  · have ⟨hai, _, ha_le⟩ := toInt_of_msb_true hw1 ha
    have ⟨hbi, hb_pos, hb_le⟩ := toInt_of_msb_true hw1 hb
    have hq_lt : (-a).toNat / (-b).toNat < 2 ^ (w - 1) := by
      cases Nat.eq_or_lt_of_le hb_pos with
      | inr hb2 =>
        have h1 : (-a).toNat / (-b).toNat ≤ 2 ^ (w - 1) / (-b).toNat :=
          Nat.div_le_div_right ha_le
        have h2 : 2 ^ (w - 1) / (-b).toNat ≤ 2 ^ (w - 1) / 2 :=
          Nat.div_le_div_left hb2 (by decide : 0 < 2)
        have h3 : 2 ^ (w - 1) / 2 < 2 ^ (w - 1) :=
          Nat.div_lt_self (pow2_pos (w - 1)) (by decide : 1 < 2)
        exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) h3
      | inl hb1 =>
        have hbn1 : b.toInt = -1 := by rw [hbi, ← hb1]; rfl
        have hb_all : b = BitVec.allOnes w := (toInt_eq_neg_one_iff hw1 b).mp hbn1
        have ha_ne : a ≠ BitVec.intMin w := fun heq => hno ⟨heq, hb_all⟩
        have ha_abs : (-a).toNat = a.toInt.natAbs := by rw [hai, Int.natAbs_neg]; rfl
        have ha_ne_pow : (-a).toNat ≠ 2 ^ (w - 1) := by
          rw [ha_abs]
          intro heq
          exact ha_ne ((toInt_natAbs_eq_pow2_pred_iff hw1 a).mp heq)
        have ha_lt : (-a).toNat < 2 ^ (w - 1) := Nat.lt_of_le_of_ne ha_le ha_ne_pow
        rw [← hb1, Nat.div_one]
        exact ha_lt
    rw [hdiv_eq (-a) (-b), toInt_ofNat_lt hq_lt, hai, hbi, Int.neg_tdiv, Int.tdiv_neg, Int.neg_neg]
    exact Int.ofNat_tdiv (-a).toNat (-b).toNat

/-- Characterization: For all `w >= 2` and nonzero `b`, `a.toInt.tdiv b.toInt` overflows
`inSignedRange w` **if and only if** `a = BitVec.intMin w ∧ b = BitVec.allOnes w`. -/
theorem sdiv_overflow_iff_intMin_negOne {w : Nat} (hw : 2 ≤ w) (a b : BitVec w)
    (hb0 : b ≠ 0#w) :
    ¬ inSignedRange w (a.toInt.tdiv b.toInt) ↔ (a = BitVec.intMin w ∧ b = BitVec.allOnes w) := by
  have hw1 : 1 ≤ w := Nat.le_trans (by decide : 1 ≤ 2) hw
  constructor
  · intro hnov
    cases ha : (a == BitVec.intMin w) with
    | false =>
      have hno : ¬ (a = BitVec.intMin w ∧ b = BitVec.allOnes w) :=
        fun ⟨h1, _⟩ => beq_eq_false_iff_ne.mp ha h1
      exact False.elim (hnov (sdiv_inSignedRange_of_guarded hw a b hb0 hno).1)
    | true =>
      cases hb : (b == BitVec.allOnes w) with
      | false =>
        have hno : ¬ (a = BitVec.intMin w ∧ b = BitVec.allOnes w) :=
          fun ⟨_, h2⟩ => beq_eq_false_iff_ne.mp hb h2
        exact False.elim (hnov (sdiv_inSignedRange_of_guarded hw a b hb0 hno).1)
      | true =>
        exact ⟨beq_iff_eq.mp ha, beq_iff_eq.mp hb⟩
  · intro ⟨ha, hb⟩ hrange
    subst ha
    subst hb
    rw [intMinBv_toInt hw1, allOnesBv_toInt hw1, Int.tdiv_neg, Int.tdiv_one, sMinInt_neg_eq] at hrange
    have hlt := (inSignedRange_iff_lt _).mp hrange |>.2
    exact Int.lt_irrefl _ hlt

/-- Signed Remainder Range & Paradox Theorem: For all `w >= 1` and ANY nonzero `b : BitVec w`,
`a.toInt.tmod b.toInt` ALWAYS lies inside `inSignedRange w`, AND `(a.srem b).toInt = a.toInt.tmod b.toInt`,
INCLUDING on `(BitVec.intMin w, BitVec.allOnes w)` where `tmod = 0`!
Yet LLVM `srem` (`LangRef.md:11674-11678`) still defines `(INT_MIN, -1)` as immediate UB because
hardware `idiv` computes quotient and remainder together. -/
theorem srem_inSignedRange_of_nonzero {w : Nat} (hw : 1 ≤ w) (a b : BitVec w)
    (hb0 : b ≠ 0#w) :
    inSignedRange w (a.toInt.tmod b.toInt) ∧
    (a.srem b).toInt = a.toInt.tmod b.toInt := by
  have hbz : b.toInt ≠ 0 := fun h => hb0 ((toInt_eq_zero_iff b).mp h)
  have hb_abs_pos : 0 < b.toInt.natAbs := Int.natAbs_pos.mpr hbz
  have hb_abs_le : b.toInt.natAbs ≤ 2 ^ (w - 1) := toInt_natAbs_le_pow2_pred hw b
  have hmod_lt : (a.toInt.tmod b.toInt).natAbs < b.toInt.natAbs := by
    rw [Int.natAbs_tmod]
    exact Nat.mod_lt a.toInt.natAbs hb_abs_pos
  have hrange : inSignedRange w (a.toInt.tmod b.toInt) :=
    inSignedRange_of_natAbs_lt (Nat.lt_of_lt_of_le hmod_lt hb_abs_le)
  refine ⟨hrange, ?_⟩
  have toInt_ofNat_lt : ∀ {m : Nat}, m < 2 ^ (w - 1) → (BitVec.ofNat w m).toInt = Int.ofNat m := by
    intro m hm
    have hmlt : m < 2 ^ w := Nat.lt_trans hm (pow2_pred_lt_pow2 hw)
    have hnat : (BitVec.ofNat w m).toNat = m := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hmlt
    have h2 : 2 * m < 2 ^ w := by
      rw [← pow2_twice_pred_eq hw]
      exact Nat.mul_lt_mul_of_pos_left hm (by decide : 0 < 2)
    rw [BitVec.toInt_eq_toNat_cond, hnat]
    simp only [h2, ↓reduceIte]
    rfl
  have toInt_neg_ofNat_le : ∀ {m : Nat}, m ≤ 2 ^ (w - 1) → (-(BitVec.ofNat w m)).toInt = -Int.ofNat m := by
    intro m hm
    cases Nat.eq_zero_or_pos m with
    | inl hm0 =>
      subst hm0
      have hz : -(BitVec.ofNat w 0) = 0#w := BitVec.neg_zero w
      rw [hz, BitVec.toInt_zero]
      rfl
    | inr hmpos =>
      have hmlt : m < 2 ^ w := Nat.lt_of_le_of_lt hm (pow2_pred_lt_pow2 hw)
      have hnat : (BitVec.ofNat w m).toNat = m := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt hmlt
      have hneg_lt : 2 ^ w - m < 2 ^ w := Nat.sub_lt (pow2_pos w) hmpos
      have hneg_nat : (-(BitVec.ofNat w m)).toNat = 2 ^ w - m := by
        rw [BitVec.toNat_neg, hnat]
        exact Nat.mod_eq_of_lt hneg_lt
      have hge : 2 ^ (w - 1) ≤ 2 ^ w - m := by
        have heq := pow2_twice_pred_eq hw
        rw [Nat.two_mul] at heq
        have hsum : 2 ^ (w - 1) + m ≤ 2 ^ w := by
          rw [← heq]
          exact Nat.add_le_add_left hm _
        exact Nat.le_sub_of_add_le hsum
      have hmsb : (-(BitVec.ofNat w m)).msb = true := by
        rw [BitVec.msb_eq_toNat, hneg_nat]
        exact decide_eq_true hge
      have hm_true := toInt_of_msb_true hw hmsb
      have hneg_neg : (-(-(BitVec.ofNat w m))).toNat = m := by
        rw [BitVec.neg_neg, hnat]
      rw [hneg_neg] at hm_true
      exact hm_true.1
  have hmod_eq : ∀ (x y : BitVec w), x % y = BitVec.ofNat w (x.toNat % y.toNat) := by
    intro x y
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_umod, BitVec.toNat_ofNat]
    have hmod_lt : x.toNat % y.toNat < 2 ^ w :=
      Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt
    exact (Nat.mod_eq_of_lt hmod_lt).symm
  change (match a.msb, b.msb with
    | false, false => a % b
    | false, true => a % (-b)
    | true, false => -((-a) % b)
    | true, true => -((-a) % (-b))).toInt = a.toInt.tmod b.toInt
  cases ha : a.msb <;> cases hb : b.msb
  · have ⟨hai, ha_lt⟩ := toInt_of_msb_false hw ha
    have ⟨hbi, _⟩ := toInt_of_msb_false hw hb
    have hm_lt : a.toNat % b.toNat < 2 ^ (w - 1) :=
      Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha_lt
    rw [hmod_eq a b, toInt_ofNat_lt hm_lt, hai, hbi]
    exact Int.ofNat_tmod a.toNat b.toNat
  · have ⟨hai, ha_lt⟩ := toInt_of_msb_false hw ha
    have ⟨hbi, _, _⟩ := toInt_of_msb_true hw hb
    have hm_lt : a.toNat % (-b).toNat < 2 ^ (w - 1) :=
      Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha_lt
    rw [hmod_eq a (-b), toInt_ofNat_lt hm_lt, hai, hbi, Int.tmod_neg]
    exact Int.ofNat_tmod a.toNat (-b).toNat
  · have ⟨hai, _, ha_le⟩ := toInt_of_msb_true hw ha
    have ⟨hbi, _⟩ := toInt_of_msb_false hw hb
    have hm_le : (-a).toNat % b.toNat ≤ 2 ^ (w - 1) :=
      Nat.le_trans (Nat.mod_le _ _) ha_le
    rw [hmod_eq (-a) b, toInt_neg_ofNat_le hm_le, hai, hbi, Int.neg_tmod]
    exact congrArg (-·) (Int.ofNat_tmod (-a).toNat b.toNat)
  · have ⟨hai, _, ha_le⟩ := toInt_of_msb_true hw ha
    have ⟨hbi, _, _⟩ := toInt_of_msb_true hw hb
    have hm_le : (-a).toNat % (-b).toNat ≤ 2 ^ (w - 1) :=
      Nat.le_trans (Nat.mod_le _ _) ha_le
    rw [hmod_eq (-a) (-b), toInt_neg_ofNat_le hm_le, hai, hbi, Int.neg_tmod, Int.tmod_neg]
    exact congrArg (-·) (Int.ofNat_tmod (-a).toNat (-b).toNat)

theorem srem_intMin_negOne_math_zero {w : Nat} (hw : 1 ≤ w) :
    ((BitVec.intMin w).toInt.tmod (BitVec.allOnes w).toInt) = 0 ∧
    inSignedRange w ((BitVec.intMin w).toInt.tmod (BitVec.allOnes w).toInt) := by
  rw [allOnesBv_toInt hw, Int.tmod_neg, Int.tmod_one]
  refine ⟨rfl, ?_⟩
  rw [inSignedRange_iff_lt]
  have hpos : 0 < Int.ofNat (2 ^ (w - 1)) := Int.ofNat_lt.mpr (pow2_pos (w - 1))
  exact ⟨Int.neg_nonpos_of_nonneg (Int.le_of_lt hpos), hpos⟩

/-- Main Theorem 1a: Safe division and remainder are 100% profile-independent across
`-C overflow-checks=on` and `-C overflow-checks=off`. -/
theorem safeDiv_profile_independent {w : Nat} (s : Signedness) (a b : BitVec w) :
    evalRustSafeDiv .checksOn s a b = evalRustSafeDiv .checksOff s a b := rfl

theorem safeRem_profile_independent {w : Nat} (s : Signedness) (a b : BitVec w) :
    evalRustSafeRem .checksOn s a b = evalRustSafeRem .checksOff s a b := rfl

/-- Main Theorem 1b (Safe Division/Remainder UB-Freedom Theorem): Across ALL `w >= 2`, all
profiles, and all inputs `(a, b)`, `evalRustSafeDiv` and `evalRustSafeRem` NEVER produce
`.immediateUB` or `.poison`. Every failing input traps deterministically with `.panic`, and
every passing input satisfies `llvmDivRemDefined s a b = true` and yields an `.ok` value whose
mathematical semantics agrees with `Nat.div`/`Nat.mod` or `Int.tdiv`/`Int.tmod`. -/
theorem safeDiv_ub_free {w : Nat} (_hw : 2 ≤ w) (prof : OverflowProfile)
    (s : Signedness) (a b : BitVec w) :
    evalRustSafeDiv prof s a b ≠ .immediateUB ∧
    evalRustSafeDiv prof s a b ≠ .poison := by
  dsimp [evalRustSafeDiv]
  cases hz : divZeroGuard b with
  | true =>
    exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | false =>
    cases s with
    | unsigned =>
      dsimp [evalLlvmDiv, llvmDivRemDefined]
      rw [hz]
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | signed =>
      cases hof : sdivOverflowGuard a b with
      | true =>
        exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | false =>
        dsimp [evalLlvmDiv, llvmDivRemDefined]
        rw [hz, hof]
        exact ⟨(fun h => by cases h), (fun h => by cases h)⟩

theorem safeRem_ub_free {w : Nat} (_hw : 2 ≤ w) (prof : OverflowProfile)
    (s : Signedness) (a b : BitVec w) :
    evalRustSafeRem prof s a b ≠ .immediateUB ∧
    evalRustSafeRem prof s a b ≠ .poison := by
  dsimp [evalRustSafeRem]
  cases hz : divZeroGuard b with
  | true =>
    exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | false =>
    cases s with
    | unsigned =>
      dsimp [evalLlvmRem, llvmDivRemDefined]
      rw [hz]
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | signed =>
      cases hof : sdivOverflowGuard a b with
      | true =>
        exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
      | false =>
        dsimp [evalLlvmRem, llvmDivRemDefined]
        rw [hz, hof]
        exact ⟨(fun h => by cases h), (fun h => by cases h)⟩

/-- Safe division and remainder refine raw LLVM `udiv`/`sdiv`/`urem`/`srem` (`tgt ⊑ src`) for
ALL inputs: on guarded failures `.panic` refines `.immediateUB`; on valid inputs both yield the
exact same `.ok` value. -/
theorem safeDiv_refines_llvmDiv {w : Nat} (prof : OverflowProfile)
    (s : Signedness) (a b : BitVec w) :
    ExecOutcome.Refines (evalRustSafeDiv prof s a b) (evalLlvmDiv s a b) := by
  dsimp [evalRustSafeDiv, evalLlvmDiv, llvmDivRemDefined]
  cases divZeroGuard b with
  | true =>
    cases s <;> simp [ExecOutcome.Refines]
  | false =>
    cases s with
    | unsigned =>
      simp [ExecOutcome.Refines]
    | signed =>
      cases sdivOverflowGuard a b with
      | true => simp [ExecOutcome.Refines]
      | false => simp [ExecOutcome.Refines]

theorem safeRem_refines_llvmRem {w : Nat} (prof : OverflowProfile)
    (s : Signedness) (a b : BitVec w) :
    ExecOutcome.Refines (evalRustSafeRem prof s a b) (evalLlvmRem s a b) := by
  dsimp [evalRustSafeRem, evalLlvmRem, llvmDivRemDefined]
  cases divZeroGuard b with
  | true =>
    cases s <;> simp [ExecOutcome.Refines]
  | false =>
    cases s with
    | unsigned =>
      simp [ExecOutcome.Refines]
    | signed =>
      cases sdivOverflowGuard a b with
      | true => simp [ExecOutcome.Refines]
      | false => simp [ExecOutcome.Refines]

/-- On `i32` (`w = 32`), `i32::MIN / -1` and `i32::MIN % -1` both unconditionally panic even under
`-C overflow-checks=off`, while raw LLVM `sdiv`/`srem` has `.immediateUB`. -/
theorem witness_i32_min_div_rem_panics :
    evalRustSafeDiv .checksOff .signed (BitVec.intMin 32) (BitVec.allOnes 32) = .panic ∧
    evalRustSafeRem .checksOff .signed (BitVec.intMin 32) (BitVec.allOnes 32) = .panic ∧
    evalLlvmDiv .signed (BitVec.intMin 32) (BitVec.allOnes 32) = .immediateUB ∧
    evalLlvmRem .signed (BitVec.intMin 32) (BitVec.allOnes 32) = .immediateUB := by
  have hm_t : (BitVec.intMin 32 == BitVec.intMin 32) = true := rfl
  dsimp [evalRustSafeDiv, evalRustSafeRem, evalLlvmDiv, evalLlvmRem,
         llvmDivRemDefined, divZeroGuard, sdivOverflowGuard]
  rw [hm_t]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Part IV: Checked, Wrapping, LLVM `nuw`/`nsw`, and Miri `unchecked_*` Arithmetic -/

/-- Ring arithmetic operator class corresponding to `MirBinOp` `+`, `-`, `*`. -/
inductive ArithOp where
  | add
  | sub
  | mul

/-- Overflow predicate parameterized by `(op, s, a, b)`. -/
noncomputable def arithOverflow {w : Nat} (op : ArithOp) (s : Signedness)
    (a b : BitVec w) : Bool :=
  match op, s with
  | .add, .unsigned => uAddOv a b
  | .add, .signed => sAddOv a b
  | .sub, .unsigned => uSubOv a b
  | .sub, .signed => sSubOv a b
  | .mul, .unsigned => uMulOv a b
  | .mul, .signed => sMulOv a b

/-- Core two's-complement bitvector operation (`BitVec.add`, `sub`, `mul`). -/
noncomputable def bvArith {w : Nat} (op : ArithOp) (a b : BitVec w) : BitVec w :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

/-- Mathematical integer evaluation (unsigned `toNat` vs. signed `toInt`). -/
noncomputable def mathArith {w : Nat} (op : ArithOp) (s : Signedness) (a b : BitVec w) : Int :=
  match op, s with
  | .add, .unsigned => Int.ofNat a.toNat + Int.ofNat b.toNat
  | .add, .signed => a.toInt + b.toInt
  | .sub, .unsigned => Int.ofNat a.toNat - Int.ofNat b.toNat
  | .sub, .signed => a.toInt - b.toInt
  | .mul, .unsigned => Int.ofNat a.toNat * Int.ofNat b.toNat
  | .mul, .signed => a.toInt * b.toInt

/-- Checked-overflow evaluation (`-C overflow-checks=on`: `AddWithOverflow` + `Assert`). -/
noncomputable def evalCheckedArith {w : Nat} (op : ArithOp) (s : Signedness)
    (a b : BitVec w) : ExecOutcome w :=
  match arithOverflow op s a b with
  | true => .panic
  | false => .ok (bvArith op a b)

/-- Wrapping two's-complement evaluation (`-C overflow-checks=off` `BinOp::Add/Sub/Mul`,
or `wrapping_{add,sub,mul}`). -/
noncomputable def evalWrappingArith {w : Nat} (op : ArithOp) (a b : BitVec w) : ExecOutcome w :=
  .ok (bvArith op a b)

/-- Profile-parameterized safe Rust arithmetic (`-C overflow-checks=on` vs. `off`). -/
noncomputable def evalRustSafeArith {w : Nat} (prof : OverflowProfile)
    (op : ArithOp) (s : Signedness) (a b : BitVec w) : ExecOutcome w :=
  match prof with
  | .checksOn => evalCheckedArith op s a b
  | .checksOff => evalWrappingArith op a b

/-- LLVM IR arithmetic with explicit `nuw` / `nsw` flags (`PoisonVal w`, matching
`compiler/rustc_codegen_llvm/src/builder.rs:557-594` and `LangRef.md:11266-11270`). -/
noncomputable def evalLlvmArithPoison {w : Nat} (op : ArithOp) (nuw nsw : Bool)
    (a b : BitVec w) : PoisonVal w :=
  let uOv := nuw && arithOverflow op .unsigned a b
  let sOv := nsw && arithOverflow op .signed a b
  match uOv || sOv with
  | true => .poison
  | false => .val (bvArith op a b)

/-- `rustc` `unchecked_*` LLVM lowering (`nuw` for unsigned, `nsw` for signed). -/
noncomputable def evalRustLlvmUnchecked {w : Nat} (op : ArithOp) (s : Signedness)
    (a b : BitVec w) : PoisonVal w :=
  match s with
  | .unsigned => evalLlvmArithPoison op true false a b
  | .signed => evalLlvmArithPoison op false true a b

/-- Rust Abstract Machine / Miri `unchecked_{add,sub,mul}` semantics
(`operator.rs:231, 288`): immediate UB on overflow even if result is unused. -/
noncomputable def evalMiriUncheckedArith {w : Nat} (op : ArithOp) (s : Signedness)
    (a b : BitVec w) : ExecOutcome w :=
  match arithOverflow op s a b with
  | true => .immediateUB
  | false => .ok (bvArith op a b)

/-- Theorem: `evalMiriUncheckedArith` equals `ExecOutcome.lowerNoundef (evalRustLlvmUnchecked ...)`. -/
theorem miriUnchecked_eq_lowerNoundef_llvm {w : Nat} (op : ArithOp) (s : Signedness)
    (a b : BitVec w) :
    evalMiriUncheckedArith op s a b = ExecOutcome.lowerNoundef (evalRustLlvmUnchecked op s a b) := by
  dsimp [evalMiriUncheckedArith, evalRustLlvmUnchecked, evalLlvmArithPoison]
  cases s with
  | unsigned =>
    cases arithOverflow op .unsigned a b <;> simp [ExecOutcome.lowerNoundef]
  | signed =>
    cases arithOverflow op .signed a b <;> simp [ExecOutcome.lowerNoundef]

/-- Mathematical faithfulness of `bvArith` when `arithOverflow op s a b = false`. -/
theorem bvArith_eq_math_of_noOv {w : Nat} (hw : 1 ≤ w) (op : ArithOp) (s : Signedness)
    (a b : BitVec w) (hno : arithOverflow op s a b = false) :
    match s with
    | .unsigned => Int.ofNat (bvArith op a b).toNat = mathArith op .unsigned a b
    | .signed => (bvArith op a b).toInt = mathArith op .signed a b := by
  cases op <;> cases s <;> dsimp only [arithOverflow] at hno <;> dsimp only [bvArith, mathArith]
  · rw [toNat_add_eq_of_noOv hno]; rfl
  · exact toInt_add_eq_of_noOv hw hno
  · rw [toNat_sub_eq_of_noOv hno]
    exact Int.ofNat_sub ((uSubOv_false_iff a b).mp hno)
  · exact toInt_sub_eq_of_noOv hw hno
  · rw [toNat_mul_eq_of_noOv hno]; rfl
  · exact toInt_mul_eq_of_noOv hw hno

/-- Main Theorem 2a (Bit-Exact Three-Way Equivalence on Non-Overflowing Inputs):
Whenever `arithOverflow op s a b = false`, checked (`-C overflow-checks=on`), wrapping
(`-C overflow-checks=off`), LLVM `nuw`/`nsw` (`evalRustLlvmUnchecked`), and Miri
`unchecked_*` ALL produce the exact same bitvector `.ok (bvArith op a b)`, matching exact
mathematical integer arithmetic! -/
theorem non_overflowing_four_way_bit_identical {w : Nat} (hw : 1 ≤ w)
    (op : ArithOp) (s : Signedness) (a b : BitVec w)
    (hno : arithOverflow op s a b = false) :
    evalCheckedArith op s a b = .ok (bvArith op a b) ∧
    evalWrappingArith op a b = .ok (bvArith op a b) ∧
    evalRustLlvmUnchecked op s a b = .val (bvArith op a b) ∧
    evalMiriUncheckedArith op s a b = .ok (bvArith op a b) ∧
    (match s with
     | .unsigned => Int.ofNat (bvArith op a b).toNat = mathArith op .unsigned a b
     | .signed => (bvArith op a b).toInt = mathArith op .signed a b) := by
  refine ⟨?_, rfl, ?_, ?_, bvArith_eq_math_of_noOv hw op s a b hno⟩
  · dsimp [evalCheckedArith]; rw [hno]
  · dsimp [evalRustLlvmUnchecked, evalLlvmArithPoison]
    cases s <;> simp [hno]
  · dsimp [evalMiriUncheckedArith]; rw [hno]

/-- Main Theorem 2b (Anneal Profile Subsumption `checksOn` -> `checksOff`):
If checked evaluation succeeds (no panic), `-C overflow-checks=on` and `-C overflow-checks=off`
produce bit-identical `.ok` outputs (and equal `nuw`/`nsw` and Miri `unchecked_*` outputs). -/
theorem checked_nopanic_implies_all_agree {w : Nat} (op : ArithOp) (s : Signedness)
    (a b : BitVec w) (hnopanic : evalCheckedArith op s a b ≠ .panic) :
    evalCheckedArith op s a b = evalWrappingArith op a b ∧
    evalCheckedArith op s a b = ExecOutcome.ofPoisonVal (evalRustLlvmUnchecked op s a b) ∧
    evalCheckedArith op s a b = evalMiriUncheckedArith op s a b := by
  dsimp [evalCheckedArith] at hnopanic ⊢
  cases hov : arithOverflow op s a b with
  | true =>
    rw [hov] at hnopanic
    exact False.elim (hnopanic rfl)
  | false =>
    dsimp [evalWrappingArith, evalRustLlvmUnchecked, evalLlvmArithPoison,
           evalMiriUncheckedArith, ExecOutcome.ofPoisonVal]
    cases s <;> simp [hov]

/-- Main Theorem 2c (Unconditional Refinement Chain `wrapping ⊑ llvm_poison ⊑ miri_ub`):
Across ALL inputs (including overflowing ones!), `-C overflow-checks=off` wrapping arithmetic
refines LLVM `nuw`/`nsw` poison (`ExecOutcome.ofPoisonVal`) and Miri immediate UB. -/
theorem wrapping_refines_llvm_and_miri {w : Nat} (op : ArithOp) (s : Signedness)
    (a b : BitVec w) :
    ExecOutcome.Refines (evalWrappingArith op a b)
      (ExecOutcome.ofPoisonVal (evalRustLlvmUnchecked op s a b)) ∧
    ExecOutcome.Refines (evalWrappingArith op a b) (evalMiriUncheckedArith op s a b) ∧
    ExecOutcome.Refines (ExecOutcome.ofPoisonVal (evalRustLlvmUnchecked op s a b))
      (evalMiriUncheckedArith op s a b) := by
  dsimp [evalWrappingArith, evalRustLlvmUnchecked, evalLlvmArithPoison,
         evalMiriUncheckedArith, ExecOutcome.ofPoisonVal]
  cases s with
  | unsigned => cases arithOverflow op .unsigned a b <;> simp [ExecOutcome.Refines]
  | signed => cases arithOverflow op .signed a b <;> simp [ExecOutcome.Refines]

/-- Unary signed negation (`as_rvalue.rs:97-118`, `MirSemantics.lean:1174-1175`):
Checked negation panics iff `a == BitVec.intMin w`; otherwise checked, wrapping, and
LLVM `sub nsw 0, a` agree bit-for-bit with `-a.toInt`. -/
noncomputable def evalCheckedNeg {w : Nat} (a : BitVec w) : ExecOutcome w :=
  match sNegOv a with
  | true => .panic
  | false => .ok (-a)

noncomputable def evalWrappingNeg {w : Nat} (a : BitVec w) : ExecOutcome w :=
  .ok (-a)

noncomputable def evalLlvmNegNsw {w : Nat} (a : BitVec w) : PoisonVal w :=
  match sNegOv a with
  | true => .poison
  | false => .val (-a)

theorem non_overflowing_neg_agree {w : Nat} (hw : 1 ≤ w) (a : BitVec w)
    (hne : a ≠ BitVec.intMin w) :
    evalCheckedNeg a = .ok (-a) ∧
    evalWrappingNeg a = .ok (-a) ∧
    evalLlvmNegNsw a = .val (-a) ∧
    (-a).toInt = -a.toInt := by
  have hno : sNegOv a = false := (sNegOv_false_iff hw a).mpr hne
  refine ⟨?_, rfl, ?_, BitVec.toInt_neg_of_ne_intMin hne⟩
  · dsimp [evalCheckedNeg]; rw [hno]
  · dsimp [evalLlvmNegNsw]; rw [hno]

/-- Main Theorem 4a (Wrapping Determinism): `-C overflow-checks=off` ring arithmetic ALWAYS
terminates normally with `.ok (bvArith op a b)` (never panics, never yields poison or UB). -/
theorem wrapping_always_ok {w : Nat} (op : ArithOp) (a b : BitVec w) :
    ∃ res : BitVec w, evalWrappingArith op a b = .ok res :=
  ⟨bvArith op a b, rfl⟩

/-- Main Theorem 4b (Wrapping vs. `unchecked_add` Non-Refinement Witness on `u8`):
On `(255#8, 1#8)`, wrapping returns `.ok 0#8`, checked returns `.panic`, `nuw` yields `.poison`,
Miri yields `.immediateUB`, and neither `nuw` nor Miri refines wrapping! -/
theorem witness_u8_add_overflow_separation :
    evalWrappingArith .add (255#8) (1#8) = .ok (0#8) ∧
    evalCheckedArith .add .unsigned (255#8) (1#8) = .panic ∧
    evalRustLlvmUnchecked .add .unsigned (255#8) (1#8) = .poison ∧
    evalMiriUncheckedArith .add .unsigned (255#8) (1#8) = .immediateUB ∧
    ¬ ExecOutcome.Refines
        (ExecOutcome.ofPoisonVal (evalRustLlvmUnchecked .add .unsigned (255#8) (1#8)))
        (evalWrappingArith .add (255#8) (1#8)) ∧
    ¬ ExecOutcome.Refines
        (evalMiriUncheckedArith .add .unsigned (255#8) (1#8))
        (evalWrappingArith .add (255#8) (1#8)) := by
  have hov : arithOverflow .add .unsigned (255#8) (1#8) = true := rfl
  have hwrap : evalWrappingArith .add (255#8) (1#8) = .ok (0#8) := rfl
  refine ⟨hwrap, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [evalCheckedArith]; rw [hov]
  · dsimp [evalRustLlvmUnchecked, evalLlvmArithPoison]; rw [hov]; rfl
  · dsimp [evalMiriUncheckedArith]; rw [hov]
  · dsimp [evalRustLlvmUnchecked, evalLlvmArithPoison, evalWrappingArith, ExecOutcome.ofPoisonVal]
    rw [hov]
    exact ExecOutcome.not_poison_refines_ok _
  · dsimp [evalMiriUncheckedArith, evalWrappingArith]
    rw [hov]
    exact ExecOutcome.not_immediateUB_refines_ok _

/-- `nuw` and `nsw` are incomparable: `127#8 + 1#8` overflows signed `nsw` while staying in
unsigned range (`nuw` valid), whereas `255#8 + 1#8` (`-1 + 1 = 0`) overflows unsigned `nuw`
while staying in signed range (`nsw` valid). -/
theorem nuw_nsw_incomparable_u8_i8 :
    (evalLlvmArithPoison .add false true (127#8) (1#8) = .poison ∧
     evalLlvmArithPoison .add true false (127#8) (1#8) = .val (128#8)) ∧
    (evalLlvmArithPoison .add true false (255#8) (1#8) = .poison ∧
     evalLlvmArithPoison .add false true (255#8) (1#8) = .val (0#8)) := by
  have h1 : arithOverflow .add .signed (127#8) (1#8) = true := rfl
  have h2 : arithOverflow .add .unsigned (127#8) (1#8) = false := rfl
  have h3 : arithOverflow .add .unsigned (255#8) (1#8) = true := rfl
  have h4 : arithOverflow .add .signed (255#8) (1#8) = false := rfl
  dsimp [evalLlvmArithPoison]
  rw [h1, h2, h3, h4]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Soundness of LLVM's `nsw` comparison folding (`nsw_allows_sgt_fold` in `probe_results.json`):
For ALL `w >= 2` and `x : BitVec w`, if `0 < x.toInt`, then `add nsw x, 1` either produces
`.poison` OR produces `.val y` with `0 < y.toInt` (`y > 0` holds unconditionally!), whereas
two's-complement wrapping at `x = BitVec.intMax 32` satisfies `0 < x.toInt` yet `(x + 1).toInt < 0`. -/
theorem nsw_sgt_fold_sound {w : Nat} (hw : 2 ≤ w) (x : BitVec w) (hx : 0 < x.toInt) :
    evalLlvmArithPoison .add false true x (1#w) = .poison ∨
    ∃ y : BitVec w, evalLlvmArithPoison .add false true x (1#w) = .val y ∧ 0 < y.toInt := by
  have hw1 : 1 ≤ w := Nat.le_trans (by decide : 1 ≤ 2) hw
  have hpow2 : 2 ≤ 2 ^ (w - 1) := pow2_pred_ge_two_of_ge_two hw
  have h1_lt : (1 : Nat) < 2 ^ (w - 1) := Nat.lt_of_lt_of_le (by decide : 1 < 2) hpow2
  have h1_range : inSignedRange w (1 : Int) := by
    rw [inSignedRange_iff_lt]
    refine ⟨?_, Int.ofNat_lt.mpr h1_lt⟩
    exact Int.le_trans (Int.neg_nonpos_of_nonneg (Int.natCast_nonneg _)) (by decide : (0 : Int) ≤ 1)
  have h1_toInt : (1#w : BitVec w).toInt = 1 := by
    change (BitVec.ofNat w 1).toInt = 1
    have h1_nat : (1 : Nat) < 2 ^ w :=
      Nat.lt_of_lt_of_le h1_lt (Nat.le_of_lt (pow2_pred_lt_pow2 hw1))
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_nat]
    have h2 : 2 * 1 < 2 ^ w := by
      have h4 : 4 ≤ 2 ^ w := by
        rw [← pow2_twice_pred_eq hw1]
        exact Nat.mul_le_mul_left 2 hpow2
      exact Nat.lt_of_lt_of_le (by decide : 2 < 4) h4
    simp [h2]
  cases hov : arithOverflow .add .signed x (1#w) with
  | true =>
    left
    dsimp [evalLlvmArithPoison]
    rw [hov]
    rfl
  | false =>
    right
    refine ⟨x + 1#w, ?_, ?_⟩
    · dsimp [evalLlvmArithPoison]
      rw [hov]
      rfl
    · have hs : sAddOv x (1#w) = false := hov
      rw [toInt_add_eq_of_noOv hw1 hs, h1_toInt]
      exact Int.lt_trans hx (Int.lt_add_of_pos_right x.toInt (by decide : (0 : Int) < 1))

theorem wrapping_sgt_fold_counterexample_i32 :
    0 < (BitVec.intMax 32).toInt ∧
    (BitVec.intMax 32 + 1#32).toInt < 0 := by
  have hpos : 0 < (BitVec.intMax 32).toInt := by
    rw [intMaxBv_toInt (by decide : 1 ≤ 32)]
    decide
  have hwrap : BitVec.intMax 32 + 1#32 = BitVec.intMin 32 := by
    apply BitVec.eq_of_toNat_eq
    decide
  have hneg : (BitVec.intMax 32 + 1#32).toInt < 0 := by
    rw [hwrap, intMinBv_toInt (by decide : 1 ≤ 32)]
    decide
  exact ⟨hpos, hneg⟩

/-! ## Part V: Safe Shift Bit-Width Masking (`base.rs`) vs. Unchecked Raw Shifts -/

/-- Shift direction (`<<` vs. `>>`). -/
inductive ShiftKind where
  | shl
  | shr

/-- Raw LLVM shift (`shl`, `lshr`, `ashr`) over bit-width `w = 2 ^ k` (`LangRef.md`
`11766-11768`, `11814-11815`, `11859-11860`): returns `.poison` whenever `amount ≥ 2^k`. -/
noncomputable def evalLlvmShift {k : Nat} (kind : ShiftKind) (s : Signedness)
    (a : BitVec (2 ^ k)) (amount : Nat) : PoisonVal (2 ^ k) :=
  match decide (2 ^ k ≤ amount) with
  | true => .poison
  | false =>
    match kind, s with
    | .shl, _ => .val (a <<< amount)
    | .shr, .unsigned => .val (a >>> amount)
    | .shr, .signed => .val (a.sshiftRight amount)

/-- Rust codegen shift-amount mask (`compiler/rustc_codegen_ssa/src/common.rs:99-115` and
`base.rs:340-343`): `b.toNat &&& (2^k - 1)`. -/
noncomputable def rustShiftMask {v : Nat} (k : Nat) (b : BitVec v) : Nat :=
  b.toNat &&& (2 ^ k - 1)

/-- Shift-count bounds predicate checked by `-C overflow-checks=on` and Miri `unchecked_{shl,shr}`:
when `rhsSigned` is unsigned, `b.toNat < 2^k`; when signed, `0 ≤ b.toInt < 2^k`. -/
noncomputable def shiftInBounds {v : Nat} (k : Nat) (rhsSigned : Signedness) (b : BitVec v) : Bool :=
  match rhsSigned with
  | .unsigned => decide (b.toNat < 2 ^ k)
  | .signed => decide (0 ≤ b.toInt) && decide (b.toInt < Int.ofNat (2 ^ k))

/-- Safe Rust shift lowering (`as_rvalue.rs:471-519` + `base.rs:330-367`):
- When `-C overflow-checks=on`, checks `(unsigned_rhs < 2^k)` (`AssertKind::Overflow`) and
  panics if `b.toNat ≥ 2^k` (or if signed `b.toInt < 0`);
- When `-C overflow-checks=off` (or after passing the check), masks `b` with `b.toNat &&& (2^k - 1)`
  before emitting LLVM `shl`/`lshr`/`ashr`. -/
noncomputable def evalRustSafeShift {k v : Nat} (prof : OverflowProfile)
    (kind : ShiftKind) (lhsSigned rhsSigned : Signedness)
    (a : BitVec (2 ^ k)) (b : BitVec v) : ExecOutcome (2 ^ k) :=
  match prof.toBool && !(shiftInBounds k rhsSigned b) with
  | true => .panic
  | false => ExecOutcome.ofPoisonVal (evalLlvmShift kind lhsSigned a (rustShiftMask k b))

/-- Miri / Rust AM `unchecked_shl` / `unchecked_shr` semantics (`operator.rs:125-170`):
immediate UB if shift amount `< 0` or `≥ 2^k`. -/
noncomputable def evalMiriUncheckedShift {k v : Nat}
    (kind : ShiftKind) (lhsSigned rhsSigned : Signedness)
    (a : BitVec (2 ^ k)) (b : BitVec v) : ExecOutcome (2 ^ k) :=
  match !(shiftInBounds k rhsSigned b) with
  | true => .immediateUB
  | false => ExecOutcome.ofPoisonVal (evalLlvmShift kind lhsSigned a b.toNat)

/-- Main Theorem 3a (Bitwise Mask Equals Modulo Power of Two): For ALL `k : Nat` and ALL
`b : BitVec v`, `rustShiftMask k b = b.toNat % 2 ^ k`. -/
theorem testBit_zero_nat (i : Nat) : (0 : Nat).testBit i = false := by
  cases i with
  | zero => rfl
  | succ j =>
    rw [Nat.testBit_succ]
    change (0 : Nat).testBit j = false
    exact testBit_zero_nat j

theorem testBit_two_pow_sub_one_clean (n i : Nat) :
    (2 ^ n - 1).testBit i = decide (i < n) := by
  induction n generalizing i with
  | zero =>
    change (0 : Nat).testBit i = decide (i < 0)
    rw [testBit_zero_nat]
    rfl
  | succ k ih =>
    have hge : 1 ≤ 2 ^ k := pow2_pos k
    have h1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have h2 : 2 ^ k = (2 ^ k - 1) + 1 := (Nat.sub_add_cancel hge).symm
    have hrew : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      calc
        2 ^ (k + 1) - 1 = 2 * ((2 ^ k - 1) + 1) - 1 := by rw [h1, ← h2]
        _ = 2 * (2 ^ k - 1) + 2 - 1 := by rw [Nat.mul_add, Nat.mul_one]
        _ = 2 * (2 ^ k - 1) + 1 := rfl
    rw [hrew]
    cases i with
    | zero =>
      rw [Nat.testBit_zero, Nat.mul_add_mod]
      rfl
    | succ j =>
      rw [Nat.testBit_succ]
      have hdiv : (2 * (2 ^ k - 1) + 1) / 2 = 2 ^ k - 1 := by
        rw [Nat.mul_add_div (by decide : 0 < 2)]
        exact Nat.add_zero _
      rw [hdiv, ih j]
      exact decide_eq_decide.mpr Nat.succ_lt_succ_iff.symm

theorem shiftMask_eq_mod_pow2 {v : Nat} (k : Nat) (b : BitVec v) :
    rustShiftMask k b = b.toNat % 2 ^ k := by
  dsimp [rustShiftMask]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mod_two_pow, testBit_two_pow_sub_one_clean]
  exact Bool.and_comm _ _

/-- Main Theorem 3b (Strict Width-Bound Invariant): For ALL `k : Nat` and ALL `b : BitVec v`,
`rustShiftMask k b < 2 ^ k`. -/
theorem shiftMask_lt_pow2 {v : Nat} (k : Nat) (b : BitVec v) :
    rustShiftMask k b < 2 ^ k := by
  rw [shiftMask_eq_mod_pow2]
  exact Nat.mod_lt b.toNat (pow2_pos k)

/-- Main Theorem 3c (Safe Shift Masking Total-Safety Theorem):
Passing `rustShiftMask k b` to LLVM `shl`/`lshr`/`ashr` NEVER produces `.poison` for ANY
`k`, `v`, `a`, `b`. Consequently:
- Under `-C overflow-checks=off`, `evalRustSafeShift` ALWAYS succeeds with `.ok _` (never
  panics, never yields `.poison`, never triggers `.immediateUB`).
- Under `-C overflow-checks=on`, `evalRustSafeShift` NEVER yields `.poison` or `.immediateUB`
  (either panics cleanly or returns `.ok _`). -/
theorem evalLlvmShift_masked_never_poison {k v : Nat} (kind : ShiftKind) (s : Signedness)
    (a : BitVec (2 ^ k)) (b : BitVec v) :
    evalLlvmShift kind s a (rustShiftMask k b) ≠ .poison := by
  dsimp [evalLlvmShift]
  have hlt : rustShiftMask k b < 2 ^ k := shiftMask_lt_pow2 k b
  have hdec : decide (2 ^ k ≤ rustShiftMask k b) = false := decide_eq_false (Nat.not_le_of_gt hlt)
  rw [hdec]
  cases kind <;> cases s <;> exact fun h => by cases h

theorem safeShift_checksOff_always_ok {k v : Nat} (kind : ShiftKind)
    (lhsSigned rhsSigned : Signedness) (a : BitVec (2 ^ k)) (b : BitVec v) :
    ∃ res : BitVec (2 ^ k),
      evalRustSafeShift .checksOff kind lhsSigned rhsSigned a b = .ok res := by
  dsimp [evalRustSafeShift, OverflowProfile.toBool]
  have hlt : rustShiftMask k b < 2 ^ k := shiftMask_lt_pow2 k b
  have hdec : decide (2 ^ k ≤ rustShiftMask k b) = false := decide_eq_false (Nat.not_le_of_gt hlt)
  dsimp [evalLlvmShift]
  rw [hdec]
  cases kind <;> cases lhsSigned <;> exact ⟨_, rfl⟩

theorem safeShift_never_poison_or_ub {k v : Nat} (prof : OverflowProfile)
    (kind : ShiftKind) (lhsSigned rhsSigned : Signedness)
    (a : BitVec (2 ^ k)) (b : BitVec v) :
    evalRustSafeShift prof kind lhsSigned rhsSigned a b ≠ .poison ∧
    evalRustSafeShift prof kind lhsSigned rhsSigned a b ≠ .immediateUB := by
  dsimp [evalRustSafeShift]
  cases prof.toBool && !(shiftInBounds k rhsSigned b) with
  | true =>
    exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | false =>
    have hnp := evalLlvmShift_masked_never_poison kind lhsSigned a b
    dsimp [ExecOutcome.ofPoisonVal]
    cases hres : evalLlvmShift kind lhsSigned a (rustShiftMask k b) with
    | poison => exact False.elim (hnp hres)
    | val bv => exact ⟨(fun h => by cases h), (fun h => by cases h)⟩

/-- Main Theorem 3d (In-Bounds Shift Equivalence): When the shift count `b` is strictly within
`[0, 2^k)`, `-C overflow-checks=on`, `-C overflow-checks=off` (masked), LLVM raw `shl`/`lshr`/`ashr`,
and Miri `unchecked_shl`/`unchecked_shr` ALL return the exact same `.ok` bit-vector. -/
theorem safeShift_inBounds_four_way_agree {k v : Nat}
    (kind : ShiftKind) (lhsSigned rhsSigned : Signedness)
    (a : BitVec (2 ^ k)) (b : BitVec v)
    (hbNat : b.toNat < 2 ^ k)
    (hbSigned : rhsSigned = .signed → 0 ≤ b.toInt ∧ b.toInt < Int.ofNat (2 ^ k)) :
    evalRustSafeShift .checksOn kind lhsSigned rhsSigned a b =
      evalRustSafeShift .checksOff kind lhsSigned rhsSigned a b ∧
    evalRustSafeShift .checksOff kind lhsSigned rhsSigned a b =
      ExecOutcome.ofPoisonVal (evalLlvmShift kind lhsSigned a b.toNat) ∧
    evalRustSafeShift .checksOff kind lhsSigned rhsSigned a b =
      evalMiriUncheckedShift kind lhsSigned rhsSigned a b := by
  have hmask : rustShiftMask k b = b.toNat := by
    rw [shiftMask_eq_mod_pow2]
    exact Nat.mod_eq_of_lt hbNat
  have hin : shiftInBounds k rhsSigned b = true := by
    dsimp [shiftInBounds]
    cases rhsSigned with
    | unsigned => exact decide_eq_true hbNat
    | signed =>
      have ⟨h0, h1⟩ := hbSigned rfl
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨h0, h1⟩
  refine ⟨?_, ?_, ?_⟩
  · dsimp [evalRustSafeShift, OverflowProfile.toBool]
    rw [hin]
    rfl
  · dsimp [evalRustSafeShift, OverflowProfile.toBool]
    rw [hmask]
    rfl
  · dsimp [evalRustSafeShift, evalMiriUncheckedShift, OverflowProfile.toBool]
    rw [hin, hmask]
    rfl

/-- Mixed-width signed RHS `zext` soundness (`compiler/rustc_codegen_ssa/src/base.rs:355-363`
and `compiler/rustc_const_eval/src/interpret/operator.rs:130-133`):
When `k ≤ r` (covering all Rust primitive widths `8, 16, 32, 64, 128` where `k ≤ 7 ≤ 8 ≤ r`),
`2^k` divides `2^r`. Therefore, taking the low `k` bits of the unsigned representation `b.toNat`
(as `zext` followed by `& (2^k - 1)` does) produces the EXACT same Euclidean remainder modulo `2^k`
as `b.toInt.emod (2^k)`. -/
theorem pow2_dvd_of_le {k r : Nat} (hle : k ≤ r) : 2 ^ k ∣ 2 ^ r := by
  have hdiff : k + (r - k) = r := Nat.add_sub_of_le hle
  refine ⟨2 ^ (r - k), ?_⟩
  rw [← Nat.pow_add, hdiff]

theorem toNat_mod_pow2_eq_toInt_emod {k r : Nat} (hle : k ≤ r) (b : BitVec r) :
    Int.ofNat (rustShiftMask k b) = b.toInt.emod (Int.ofNat (2 ^ k)) := by
  rw [shiftMask_eq_mod_pow2]
  have hdvd : (Int.ofNat (2 ^ k)) ∣ (↑(2 ^ r) : Int) :=
    Int.ofNat_dvd.mpr (pow2_dvd_of_le hle)
  rw [BitVec.toInt_eq_toNat_cond]
  cases h : decide (2 * b.toNat < 2 ^ r) with
  | true =>
    have hlt : 2 * b.toNat < 2 ^ r := decide_eq_true_eq.mp h
    simp only [hlt, ↓reduceIte]
    rfl
  | false =>
    have hge : ¬ (2 * b.toNat < 2 ^ r) := decide_eq_false_iff_not.mp h
    simp only [hge, ↓reduceIte]
    have hdvd_neg : (Int.ofNat (2 ^ k)) ∣ -(↑(2 ^ r) : Int) :=
      Int.dvd_neg.mpr hdvd
    rw [Int.sub_eq_add_neg]
    change Int.ofNat (b.toNat % 2 ^ k) = (↑b.toNat + -↑(2 ^ r)) % Int.ofNat (2 ^ k)
    rw [Int.add_emod, Int.emod_eq_zero_of_dvd hdvd_neg, Int.add_zero, Int.emod_emod]
    rfl

/-- Concrete confirmation of the `512`-bit hazard noted in `compiler/rustc_codegen_ssa/src/base.rs:360-362`:
For a hypothetical `512`-bit LHS (`k = 9`, `2^9 = 512`) and an `i8` RHS (`r = 8`, `b = -1#8`),
`zext(-1#8) &&& 511 = 255`, whereas `(-1 : Int).emod 512 = 511`! -/
theorem base_rs_512bit_i8_mismatch_witness :
    Int.ofNat (rustShiftMask 9 (-1#8)) = 255 ∧
    (-1#8 : BitVec 8).toInt.emod (Int.ofNat (2 ^ 9)) = 511 ∧
    Int.ofNat (rustShiftMask 9 (-1#8)) ≠ (-1#8 : BitVec 8).toInt.emod (Int.ofNat (2 ^ 9)) := by
  exact ⟨rfl, rfl, of_decide_eq_true rfl⟩

/-- For all actual Rust widths up to `256` (`k ≤ 8`), shifting a `2^k`-bit value by `-1#8`
satisfies `rustShiftMask k (-1#8) = 2^k - 1` (e.g. `31` for `u32`, matching `SHL_NEG_I8=0x80000000`
observed in `probe_results.json`). -/
theorem witness_u32_shl_neg1_i8 :
    rustShiftMask 5 (-1#8) = 31 ∧
    evalRustSafeShift (k := 5) .checksOff .shl .unsigned .signed (1#32) (-1#8) = .ok (0x80000000#32) ∧
    evalRustSafeShift (k := 5) .checksOn .shl .unsigned .signed (1#32) (-1#8) = .panic ∧
    evalMiriUncheckedShift (k := 5) .shl .unsigned .signed (1#32) (-1#8) = .immediateUB := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Overshift separation witness on `1#32 << 32#32`:
- `-C overflow-checks=off` safe masked shift returns `.ok (1#32)`;
- `-C overflow-checks=on` panics (`attempt to shift left with overflow`);
- LLVM bare `shl i32 1, 32` returns `.poison`;
- Miri `1u32.unchecked_shl(32)` triggers `.immediateUB`. -/
theorem witness_u32_shl_32_four_tiers :
    evalRustSafeShift (k := 5) .checksOff .shl .unsigned .unsigned (1#32) (32#32) = .ok (1#32) ∧
    evalRustSafeShift (k := 5) .checksOn .shl .unsigned .unsigned (1#32) (32#32) = .panic ∧
    evalLlvmShift (k := 5) .shl .unsigned (1#32) 32 = .poison ∧
    evalMiriUncheckedShift (k := 5) .shl .unsigned .unsigned (1#32) (32#32) = .immediateUB := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Part VI: Unified End-to-End `rustc` Three-Tier MIR Operator Dispatch & Width Instantiations -/

/-- Complete `rustc` binary integer operator set modeled across all three tiers. -/
inductive RustcIntBinOp where
  | add | sub | mul
  | div | rem
  | shl | shr
  | addUnchecked | subUnchecked | mulUnchecked
  | shlUnchecked | shrUnchecked

/-- Map `RustcIntBinOp` to its `ExecOutcome (2 ^ k)` at bit-width `w = 2^k`. -/
noncomputable def evalRustcIntBinOp {k v : Nat} (prof : OverflowProfile)
    (op : RustcIntBinOp) (lhsSigned rhsSigned : Signedness)
    (a : BitVec (2 ^ k)) (bSame : BitVec (2 ^ k)) (bShift : BitVec v) :
    ExecOutcome (2 ^ k) :=
  match op with
  | .add => evalRustSafeArith prof .add lhsSigned a bSame
  | .sub => evalRustSafeArith prof .sub lhsSigned a bSame
  | .mul => evalRustSafeArith prof .mul lhsSigned a bSame
  | .div => evalRustSafeDiv prof lhsSigned a bSame
  | .rem => evalRustSafeRem prof lhsSigned a bSame
  | .shl => evalRustSafeShift prof .shl lhsSigned rhsSigned a bShift
  | .shr => evalRustSafeShift prof .shr lhsSigned rhsSigned a bShift
  | .addUnchecked => evalMiriUncheckedArith .add lhsSigned a bSame
  | .subUnchecked => evalMiriUncheckedArith .sub lhsSigned a bSame
  | .mulUnchecked => evalMiriUncheckedArith .mul lhsSigned a bSame
  | .shlUnchecked => evalMiriUncheckedShift .shl lhsSigned rhsSigned a bShift
  | .shrUnchecked => evalMiriUncheckedShift .shr lhsSigned rhsSigned a bShift

/-- Safe operations (`add`, `sub`, `mul`, `div`, `rem`, `shl`, `shr`) NEVER exhibit `.poison` or
`.immediateUB` across ALL widths `2^k` with `1 ≤ k` (covering `8, 16, 32, 64, 128` bits) and ALL
profiles (`checksOn`, `checksOff`). -/
noncomputable def isSafeRustcBinOp : RustcIntBinOp → Bool
  | .add | .sub | .mul | .div | .rem | .shl | .shr => true
  | .addUnchecked | .subUnchecked | .mulUnchecked | .shlUnchecked | .shrUnchecked => false

theorem safe_rustc_binop_never_ub_or_poison {k v : Nat} (hk : 1 ≤ k)
    (prof : OverflowProfile) (op : RustcIntBinOp) (hsafe : isSafeRustcBinOp op = true)
    (lhsSigned rhsSigned : Signedness)
    (a : BitVec (2 ^ k)) (bSame : BitVec (2 ^ k)) (bShift : BitVec v) :
    evalRustcIntBinOp prof op lhsSigned rhsSigned a bSame bShift ≠ .immediateUB ∧
    evalRustcIntBinOp prof op lhsSigned rhsSigned a bSame bShift ≠ .poison := by
  have hw2 : 2 ≤ 2 ^ k := pow2_ge_two_of_pos hk
  cases op with
  | add | sub | mul =>
    dsimp [evalRustcIntBinOp, evalRustSafeArith]
    cases prof with
    | checksOff =>
      dsimp [evalWrappingArith]
      exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
    | checksOn =>
      dsimp [evalCheckedArith]
      cases arithOverflow _ lhsSigned a bSame <;>
        exact ⟨(fun h => by cases h), (fun h => by cases h)⟩
  | div =>
    exact safeDiv_ub_free hw2 prof lhsSigned a bSame
  | rem =>
    exact safeRem_ub_free hw2 prof lhsSigned a bSame
  | shl =>
    have h := safeShift_never_poison_or_ub prof .shl lhsSigned rhsSigned a bShift
    exact ⟨h.2, h.1⟩
  | shr =>
    have h := safeShift_never_poison_or_ub prof .shr lhsSigned rhsSigned a bShift
    exact ⟨h.2, h.1⟩
  | addUnchecked | subUnchecked | mulUnchecked | shlUnchecked | shrUnchecked =>
    exact False.elim (Bool.noConfusion hsafe)

/-- Under `-C overflow-checks=off`, ALL safe Rust integer operations EXCEPT `div` and `rem` are
100% total and panic-free (yielding `.ok _` on every input pair). -/
noncomputable def isAlwaysTotalWhenChecksOff : RustcIntBinOp → Bool
  | .add | .sub | .mul | .shl | .shr => true
  | _ => false

theorem checksOff_non_divrem_always_ok {k v : Nat}
    (op : RustcIntBinOp) (htot : isAlwaysTotalWhenChecksOff op = true)
    (lhsSigned rhsSigned : Signedness)
    (a : BitVec (2 ^ k)) (bSame : BitVec (2 ^ k)) (bShift : BitVec v) :
    ∃ res : BitVec (2 ^ k),
      evalRustcIntBinOp .checksOff op lhsSigned rhsSigned a bSame bShift = .ok res := by
  cases op with
  | add => exact wrapping_always_ok .add a bSame
  | sub => exact wrapping_always_ok .sub a bSame
  | mul => exact wrapping_always_ok .mul a bSame
  | shl => exact safeShift_checksOff_always_ok .shl lhsSigned rhsSigned a bShift
  | shr => exact safeShift_checksOff_always_ok .shr lhsSigned rhsSigned a bShift
  | div | rem | addUnchecked | subUnchecked | mulUnchecked | shlUnchecked | shrUnchecked =>
    exact False.elim (Bool.noConfusion htot)

/-- Concrete Rust integer-width instantiations (`i8/u8` `k=3`, `i16/u16` `k=4`,
`i32/u32` `k=5`, `i64/u64` `k=6`, `i128/u128` `k=7`) confirming all theorems instantiate cleanly
to every Rust fixed-width integer type. -/
theorem rust_all_widths_div_rem_ub_free :
    (∀ (prof : OverflowProfile) (s : Signedness) (a b : BitVec 8),
      evalRustSafeDiv prof s a b ≠ .immediateUB ∧ evalRustSafeRem prof s a b ≠ .immediateUB) ∧
    (∀ (prof : OverflowProfile) (s : Signedness) (a b : BitVec 16),
      evalRustSafeDiv prof s a b ≠ .immediateUB ∧ evalRustSafeRem prof s a b ≠ .immediateUB) ∧
    (∀ (prof : OverflowProfile) (s : Signedness) (a b : BitVec 32),
      evalRustSafeDiv prof s a b ≠ .immediateUB ∧ evalRustSafeRem prof s a b ≠ .immediateUB) ∧
    (∀ (prof : OverflowProfile) (s : Signedness) (a b : BitVec 64),
      evalRustSafeDiv prof s a b ≠ .immediateUB ∧ evalRustSafeRem prof s a b ≠ .immediateUB) ∧
    (∀ (prof : OverflowProfile) (s : Signedness) (a b : BitVec 128),
      evalRustSafeDiv prof s a b ≠ .immediateUB ∧ evalRustSafeRem prof s a b ≠ .immediateUB) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro prof s a b
    exact ⟨(safeDiv_ub_free (by decide : 2 ≤ 8) prof s a b).1,
           (safeRem_ub_free (by decide : 2 ≤ 8) prof s a b).1⟩
  · intro prof s a b
    exact ⟨(safeDiv_ub_free (by decide : 2 ≤ 16) prof s a b).1,
           (safeRem_ub_free (by decide : 2 ≤ 16) prof s a b).1⟩
  · intro prof s a b
    exact ⟨(safeDiv_ub_free (by decide : 2 ≤ 32) prof s a b).1,
           (safeRem_ub_free (by decide : 2 ≤ 32) prof s a b).1⟩
  · intro prof s a b
    exact ⟨(safeDiv_ub_free (by decide : 2 ≤ 64) prof s a b).1,
           (safeRem_ub_free (by decide : 2 ≤ 64) prof s a b).1⟩
  · intro prof s a b
    exact ⟨(safeDiv_ub_free (by decide : 2 ≤ 128) prof s a b).1,
           (safeRem_ub_free (by decide : 2 ≤ 128) prof s a b).1⟩

/-- Concrete non-vacuity and differential boundary suite across `u8`, `i8`, `i32`, `u32`, `i64`:
confirms every empirical result from `probe_results.json` inside the kernel-checked model. -/
theorem probe_correspondence_canary_suite :
    evalRustcIntBinOp (k := 3) .checksOn .add .unsigned .unsigned (255#8) (1#8) (0#32) = .panic ∧
    evalRustcIntBinOp (k := 3) .checksOff .add .unsigned .unsigned (255#8) (1#8) (0#32) = .ok (0#8) ∧
    evalRustcIntBinOp (k := 3) .checksOn .add .signed .signed (127#8) (1#8) (0#32) = .panic ∧
    evalRustcIntBinOp (k := 3) .checksOff .add .signed .signed (127#8) (1#8) (0#32) = .ok (128#8) ∧
    evalRustcIntBinOp (k := 3) .checksOn .sub .unsigned .unsigned (0#8) (1#8) (0#32) = .panic ∧
    evalRustcIntBinOp (k := 3) .checksOff .sub .unsigned .unsigned (0#8) (1#8) (0#32) = .ok (255#8) ∧
    evalRustcIntBinOp (k := 3) .checksOn .mul .unsigned .unsigned (16#8) (16#8) (0#32) = .panic ∧
    evalRustcIntBinOp (k := 3) .checksOff .mul .unsigned .unsigned (16#8) (16#8) (0#32) = .ok (0#8) ∧
    evalRustcIntBinOp (k := 5) .checksOff .shr .signed .unsigned (BitVec.ofInt 32 (-8)) (0#32) (32#32) =
      .ok (BitVec.ofInt 32 (-8)) ∧
    evalRustcIntBinOp (k := 3) .checksOff .shr .signed .unsigned (BitVec.ofInt 8 (-8)) (0#8) (9#32) =
      .ok (BitVec.ofInt 8 (-4)) ∧
    evalRustcIntBinOp (k := 5) .checksOff .addUnchecked .unsigned .unsigned (BitVec.allOnes 32) (1#32) (0#32) =
      .immediateUB ∧
    evalRustcIntBinOp (k := 5) .checksOff .shlUnchecked .unsigned .unsigned (1#32) (0#32) (32#32) =
      .immediateUB ∧
    evalRustcIntBinOp (k := 5) .checksOff .shlUnchecked .unsigned .unsigned (1#32) (0#32) (31#32) =
      .ok (0x80000000#32) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end RustcIntOverflow
