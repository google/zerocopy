/-!
# MIR `UnOp::PtrMetadata`, `AggregateKind::RawPtr`, Custom-DST `GVN` Folding Asymmetry,
# `FakeForPtrMetadata`, `CastKind::BoxDerefTransmute`, and `size_of_val` Layout Soundness

Standalone, dependency-free Lean `v4.34.1` formalization establishing kernel-checked
ground truth for `rustc`'s wide-pointer metadata pipeline and operational semantics across:
- `compiler/rustc_mir_transform/src/{lower_intrinsics,lower_slice_len,instsimplify,gvn,elaborate_box_derefs,validate}.rs`
- `compiler/rustc_middle/src/{mir/syntax,ty/sty}.rs`
- `compiler/rustc_const_eval/src/interpret/{operator,cast,place,projection,step}.rs`
- `compiler/rustc_codegen_ssa/src/{size_of_val,mir/{place,rvalue,operand}}.rs`
- `joshlf/anneal` MIR capture/TCB boundary (`Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, `Trusted/Correspondence.lean`)

Purity invariants strictly enforced throughout this module:
- Zero external imports (`Lean` `Init` prelude only).
- Zero `sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, or `partial def`.
- Zero `deriving` clauses (avoiding generated `._unsafe_rec` constants).
- All boolean branching uses primitive `match ... with | true => ... | false => ...` over
  computable `Nat.beq` / `Nat.ble` predicates so every concrete theorem reduces via `rfl`.
-/

namespace MirPtrMetadataGvnCustomDstAndRawPtrSoundness

/-! ## 1. Primitive Arithmetic Helpers & Alignment Galois Closure (`size_of_val.rs`) -/

/-- Branchless Boolean negation (avoids `@ite` / `Decidable` WHNF bloat). -/
noncomputable def boolNot : Bool → Bool
  | true => false
  | false => true

/-- Boolean conjunction. -/
noncomputable def boolAnd : Bool → Bool → Bool
  | true, true => true
  | _, _ => false

/-- Boolean disjunction. -/
noncomputable def boolOr : Bool → Bool → Bool
  | false, false => false
  | _, _ => true

theorem boolAnd_eq_true {a b : Bool} (h : boolAnd a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | exact Bool.noConfusion h

/-- Maximum of two natural numbers using `Nat.ble`. -/
noncomputable def fastMax (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true => b
  | false => a

/-- Minimum of two natural numbers using `Nat.ble`. -/
noncomputable def fastMin (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true => a
  | false => b

theorem ble_false_not_true {a b : Nat} (h : Nat.ble a b = false) : ¬(Nat.ble a b = true) :=
  fun ht => Bool.noConfusion (h.symm.trans ht)

theorem fastMax_ge_left (a b : Nat) : a ≤ fastMax a b := by
  unfold fastMax
  cases h : Nat.ble a b with
  | true => exact Nat.le_of_ble_eq_true h
  | false => exact Nat.le_refl a

theorem fastMax_ge_right (a b : Nat) : b ≤ fastMax a b := by
  unfold fastMax
  cases h : Nat.ble a b with
  | true => exact Nat.le_refl b
  | false =>
    exact Nat.le_of_lt (Nat.lt_of_not_le (Nat.not_le_of_not_ble_eq_true (ble_false_not_true h)))

theorem fastMin_le_left (a b : Nat) : fastMin a b ≤ a := by
  unfold fastMin
  cases h : Nat.ble a b with
  | true => exact Nat.le_refl a
  | false =>
    exact Nat.le_of_lt (Nat.lt_of_not_le (Nat.not_le_of_not_ble_eq_true (ble_false_not_true h)))

theorem fastMin_le_right (a b : Nat) : fastMin a b ≤ b := by
  unfold fastMin
  cases h : Nat.ble a b with
  | true => exact Nat.le_of_ble_eq_true h
  | false => exact Nat.le_refl b

/-- Align `n` upward to the next multiple of `a` (identity when `a = 0`).
    Models `rustc_abi::Align::align_to` / `size_of_val.rs:173` `(size + (align - 1)) & -align`
    over unbounded naturals. -/
noncomputable def alignUp (n a : Nat) : Nat :=
  match a with
  | 0 => n
  | k + 1 => ((n + k) / (k + 1)) * (k + 1)

theorem alignUp_zero (n : Nat) : alignUp n 0 = n := rfl

theorem alignUp_ge (n a : Nat) : n ≤ alignUp n a := by
  cases a with
  | zero => exact Nat.le_refl n
  | succ k =>
    change n ≤ ((n + k) / (k + 1)) * (k + 1)
    have hdiv : ((n + k) / (k + 1)) * (k + 1) + (n + k) % (k + 1) = n + k :=
      Nat.div_add_mod' (n + k) (k + 1)
    have hmod_lt : (n + k) % (k + 1) < k + 1 := Nat.mod_lt (n + k) (Nat.succ_pos k)
    have hmod_le : (n + k) % (k + 1) ≤ k := Nat.le_of_lt_succ hmod_lt
    have hle1 : n + k ≤ ((n + k) / (k + 1)) * (k + 1) + k :=
      calc n + k
          = ((n + k) / (k + 1)) * (k + 1) + (n + k) % (k + 1) := hdiv.symm
        _ ≤ ((n + k) / (k + 1)) * (k + 1) + k := Nat.add_le_add_left hmod_le _
    exact Nat.add_le_add_iff_right.mp hle1

theorem alignUp_dvd {n a : Nat} (ha : 0 < a) : a ∣ alignUp n a := by
  cases a with
  | zero => exact False.elim (Nat.lt_irrefl 0 ha)
  | succ k =>
    exact ⟨(n + k) / (k + 1), Nat.mul_comm ((n + k) / (k + 1)) (k + 1)⟩

theorem alignUp_minimal {n a y : Nat} (ha : 0 < a) (hxy : n ≤ y) (hdy : a ∣ y) :
    alignUp n a ≤ y := by
  cases a with
  | zero => exact False.elim (Nat.lt_irrefl 0 ha)
  | succ k =>
    rcases hdy with ⟨t, rfl⟩
    change ((n + k) / (k + 1)) * (k + 1) ≤ (k + 1) * t
    cases Nat.lt_or_ge t ((n + k) / (k + 1)) with
    | inr hle =>
      calc ((n + k) / (k + 1)) * (k + 1)
          ≤ t * (k + 1) := Nat.mul_le_mul_right (k + 1) hle
        _ = (k + 1) * t := Nat.mul_comm t (k + 1)
    | inl hlt =>
      have hsucc : t + 1 ≤ (n + k) / (k + 1) := Nat.succ_le_of_lt hlt
      have hmul1 : (t + 1) * (k + 1) ≤ ((n + k) / (k + 1)) * (k + 1) :=
        Nat.mul_le_mul_right (k + 1) hsucc
      have hdiv : ((n + k) / (k + 1)) * (k + 1) ≤ n + k :=
        Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq (Nat.div_add_mod' (n + k) (k + 1)))
      have hupper : n + k < (t + 1) * (k + 1) := by
        have h1 : n + k ≤ (k + 1) * t + k := Nat.add_le_add_right hxy k
        have h2 : (k + 1) * t + k < (k + 1) * t + (k + 1) :=
          Nat.add_lt_add_left (Nat.lt_succ_self k) ((k + 1) * t)
        have h3 : (k + 1) * t + (k + 1) = (t + 1) * (k + 1) := by
          rw [Nat.mul_comm (k + 1) t, Nat.succ_mul]
        exact h3 ▸ Nat.lt_of_le_of_lt h1 h2
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans hmul1 hdiv) hupper))

theorem alignUp_eq_iff {n a y : Nat} (ha : 0 < a) :
    alignUp n a = y ↔ (n ≤ y ∧ a ∣ y ∧ ∀ z, n ≤ z → a ∣ z → y ≤ z) := by
  constructor
  · intro heq
    subst heq
    exact ⟨alignUp_ge n a, alignUp_dvd ha, fun _ hz hd => alignUp_minimal ha hz hd⟩
  · intro ⟨h1, h2, h3⟩
    exact Nat.le_antisymm (alignUp_minimal ha h1 h2) (h3 (alignUp n a) (alignUp_ge n a) (alignUp_dvd ha))

theorem alignUp_monotone {n₁ n₂ a : Nat} (h : n₁ ≤ n₂) :
    alignUp n₁ a ≤ alignUp n₂ a := by
  cases a with
  | zero => exact h
  | succ k =>
    exact alignUp_minimal (Nat.succ_pos k) (Nat.le_trans h (alignUp_ge n₂ (k + 1))) (alignUp_dvd (Nat.succ_pos k))

theorem alignUp_idem (n a : Nat) : alignUp (alignUp n a) a = alignUp n a := by
  cases a with
  | zero => rfl
  | succ k =>
    exact Nat.le_antisymm
      (alignUp_minimal (Nat.succ_pos k) (Nat.le_refl _) (alignUp_dvd (Nat.succ_pos k)))
      (alignUp_ge _ (k + 1))

theorem alignUp_of_dvd {n a : Nat} (ha : 0 < a) (hd : a ∣ n) : alignUp n a = n :=
  Nat.le_antisymm (alignUp_minimal ha (Nat.le_refl n) hd) (alignUp_ge n a)

/-- **Core Algebraic Alignment-Absorption Theorem (`size_of_val.rs:148-160`).**
    Because an unsized tail's `uSize` is a multiple of `uAlign`, and `fAlign = max(sizedAlign, uAlign)`
    satisfies `uAlign ∣ fAlign` for power-of-two alignments, `size_and_align_of_dst` may omit
    the intermediate `.align_to(uAlign)` on `tailOffsetUnadj`:
    `alignUp (alignUp off uAlign + uSize) fAlign = alignUp (off + uSize) fAlign`. -/
theorem alignUp_add_mul_absorb {off uSize uAlign fAlign : Nat}
    (hu : 0 < uAlign) (hf : 0 < fAlign)
    (h_sz_dvd : uAlign ∣ uSize) (h_al_dvd : uAlign ∣ fAlign) :
    alignUp (alignUp off uAlign + uSize) fAlign = alignUp (off + uSize) fAlign := by
  apply Nat.le_antisymm
  · have hrhs_ge : off + uSize ≤ alignUp (off + uSize) fAlign := alignUp_ge (off + uSize) fAlign
    have hrhs_dvd_f : fAlign ∣ alignUp (off + uSize) fAlign := alignUp_dvd hf
    have hrhs_dvd_u : uAlign ∣ alignUp (off + uSize) fAlign := Nat.dvd_trans h_al_dvd hrhs_dvd_f
    rcases hrhs_dvd_u with ⟨t, ht⟩
    rcases h_sz_dvd with ⟨s, hs⟩
    have h_st : uAlign * s ≤ uAlign * t := by
      calc uAlign * s = uSize := hs.symm
        _ ≤ off + uSize := Nat.le_add_left uSize off
        _ ≤ alignUp (off + uSize) fAlign := hrhs_ge
        _ = uAlign * t := ht
    have hs_le_t : s ≤ t := Nat.le_of_mul_le_mul_left h_st hu
    have h_diff_mul : uAlign * (t - s) + uSize = alignUp (off + uSize) fAlign := by
      calc uAlign * (t - s) + uSize
          = uAlign * (t - s) + uAlign * s := by rw [hs]
        _ = uAlign * ((t - s) + s) := (Nat.mul_add uAlign (t - s) s).symm
        _ = uAlign * t := by rw [Nat.sub_add_cancel hs_le_t]
        _ = alignUp (off + uSize) fAlign := ht.symm
    have h_off_le_diff : off ≤ uAlign * (t - s) := by
      have hsum : off + uSize ≤ uAlign * (t - s) + uSize := h_diff_mul ▸ hrhs_ge
      exact Nat.add_le_add_iff_right.mp hsum
    have h_round_le_diff : alignUp off uAlign ≤ uAlign * (t - s) :=
      alignUp_minimal hu h_off_le_diff ⟨t - s, rfl⟩
    have h_lhs_in_le_rhs : alignUp off uAlign + uSize ≤ alignUp (off + uSize) fAlign := by
      calc alignUp off uAlign + uSize
          ≤ uAlign * (t - s) + uSize := Nat.add_le_add_right h_round_le_diff uSize
        _ = alignUp (off + uSize) fAlign := h_diff_mul
    exact alignUp_minimal hf h_lhs_in_le_rhs hrhs_dvd_f
  · exact alignUp_monotone (Nat.add_le_add_right (alignUp_ge off uAlign) uSize)

/-- Two powers of two satisfy ordered divisibility: smaller exponent divides larger exponent. -/
theorem pow2_le_dvd {e₁ e₂ : Nat} (hle : e₁ ≤ e₂) : Nat.pow 2 e₁ ∣ Nat.pow 2 e₂ := by
  refine ⟨Nat.pow 2 (e₂ - e₁), ?_⟩
  change 2 ^ e₂ = 2 ^ e₁ * 2 ^ (e₂ - e₁)
  rw [← Nat.pow_add, Nat.add_sub_cancel' hle]

/-- Maximum of two powers of two is divisible by both operands (`fullAlign = max(sized, unsized)`). -/
theorem pow2_max_both_dvd (e₁ e₂ : Nat) :
    Nat.pow 2 e₁ ∣ fastMax (Nat.pow 2 e₁) (Nat.pow 2 e₂) ∧
    Nat.pow 2 e₂ ∣ fastMax (Nat.pow 2 e₁) (Nat.pow 2 e₂) := by
  cases Nat.le_total e₁ e₂ with
  | inl h =>
    have hpow : Nat.pow 2 e₁ ≤ Nat.pow 2 e₂ := Nat.pow_le_pow_right (Nat.succ_pos 1) h
    have hmax : fastMax (Nat.pow 2 e₁) (Nat.pow 2 e₂) = Nat.pow 2 e₂ := by
      unfold fastMax
      have hble : Nat.ble (Nat.pow 2 e₁) (Nat.pow 2 e₂) = true := Nat.ble_eq.mpr hpow
      rw [hble]
    rw [hmax]
    exact ⟨pow2_le_dvd h, Nat.dvd_refl _⟩
  | inr h =>
    have hpow : Nat.pow 2 e₂ ≤ Nat.pow 2 e₁ := Nat.pow_le_pow_right (Nat.succ_pos 1) h
    have hlt : fastMax (Nat.pow 2 e₁) (Nat.pow 2 e₂) = Nat.pow 2 e₁ := by
      unfold fastMax
      cases hble : Nat.ble (Nat.pow 2 e₁) (Nat.pow 2 e₂) with
      | true => exact (Nat.le_antisymm (Nat.le_of_ble_eq_true hble) hpow).symm
      | false => rfl
    rw [hlt]
    exact ⟨Nat.dvd_refl _, pow2_le_dvd h⟩

/-- Packed alignment helper: `min(2^e, 2^p)` is a power of two that divides `2^e`. -/
noncomputable def capPackAlign (pack : Option Nat) (uAlignRaw : Nat) : Nat :=
  match pack with
  | none => uAlignRaw
  | some pLog => fastMin uAlignRaw (Nat.pow 2 pLog)

theorem capPackAlign_pow2_dvd {pack : Option Nat} {eu uSize : Nat}
    (hu_dvd : Nat.pow 2 eu ∣ uSize) :
    ∃ eu', capPackAlign pack (Nat.pow 2 eu) = Nat.pow 2 eu' ∧
           capPackAlign pack (Nat.pow 2 eu) ∣ uSize := by
  cases pack with
  | none => exact ⟨eu, rfl, hu_dvd⟩
  | some pLog =>
    unfold capPackAlign
    dsimp only
    cases Nat.le_total eu pLog with
    | inl hle =>
      have hp : Nat.pow 2 eu ≤ Nat.pow 2 pLog := Nat.pow_le_pow_right (Nat.succ_pos 1) hle
      have hmin : fastMin (Nat.pow 2 eu) (Nat.pow 2 pLog) = Nat.pow 2 eu := by
        unfold fastMin
        rw [Nat.ble_eq.mpr hp]
      rw [hmin]
      exact ⟨eu, rfl, hu_dvd⟩
    | inr hle =>
      have hp : Nat.pow 2 pLog ≤ Nat.pow 2 eu := Nat.pow_le_pow_right (Nat.succ_pos 1) hle
      have hmin : fastMin (Nat.pow 2 eu) (Nat.pow 2 pLog) = Nat.pow 2 pLog := by
        unfold fastMin
        cases hble : Nat.ble (Nat.pow 2 eu) (Nat.pow 2 pLog) with
        | true => exact Nat.le_antisymm (Nat.le_of_ble_eq_true hble) hp
        | false => rfl
      rw [hmin]
      exact ⟨pLog, rfl, Nat.dvd_trans (pow2_le_dvd hle) hu_dvd⟩

/-- Combined alignment helper for ADT fields (`fullAlign = max(2^szAlLog, capPackAlign ...)`). -/
theorem fastMax_pow2_witness (e₁ e₂ : Nat) :
    ∃ ef, fastMax (Nat.pow 2 e₁) (Nat.pow 2 e₂) = Nat.pow 2 ef := by
  cases Nat.le_total e₁ e₂ with
  | inl h =>
    have hp : Nat.pow 2 e₁ ≤ Nat.pow 2 e₂ := Nat.pow_le_pow_right (Nat.succ_pos 1) h
    have hmax : fastMax (Nat.pow 2 e₁) (Nat.pow 2 e₂) = Nat.pow 2 e₂ := by
      unfold fastMax
      rw [Nat.ble_eq.mpr hp]
    exact ⟨e₂, hmax⟩
  | inr h =>
    have hp : Nat.pow 2 e₂ ≤ Nat.pow 2 e₁ := Nat.pow_le_pow_right (Nat.succ_pos 1) h
    have hmax : fastMax (Nat.pow 2 e₁) (Nat.pow 2 e₂) = Nat.pow 2 e₁ := by
      unfold fastMax
      cases hble : Nat.ble (Nat.pow 2 e₁) (Nat.pow 2 e₂) with
      | true => exact (Nat.le_antisymm (Nat.le_of_ble_eq_true hble) hp).symm
      | false => rfl
    exact ⟨e₁, hmax⟩

/-! ## 2. Custom-DST Pointee Types, Metadata Shapes, and `ptr_metadata_ty` Typing -/

/-- Pointer mutability matching `rustc_middle::mir::Mutability` (`Not` vs `Mut`). -/
inductive PtrMut where
  | shared
  | mutable

noncomputable def PtrMut.beq : PtrMut → PtrMut → Bool
  | .shared, .shared => true
  | .mutable, .mutable => true
  | _, _ => false

/-- Raw-pointer borrowing kind (`rustc_middle/src/mir/syntax.rs`: `RawPtrKind`).
    `fakeForPtrMetadata` models `RawPtrKind::FakeForPtrMetadata`, emitted for slice bounds
    checks when indexing non-trivially-`Copy` slice places (`&raw const (fake) ((*wu).1).1`). -/
inductive MirRawPtrKind where
  | regular (mutbl : PtrMut)
  | fakeForPtrMetadata

/-- MIR cast variants modeled (`CastKind`), separating `rustc 1.98.0-nightly`'s `Transmute`
    from `rust-lang/rust` HEAD's `BoxDerefTransmute`. -/
inductive MirCastKind where
  | ptrToPtr
  | unsize
  | transmute
  | boxDerefTransmute

/-- Cross-version interpreter & MIR policy selector comparing `rustc 1.98.0-nightly`
    (`14210df0e`) against `rust-lang/rust` HEAD (`fde8dfd638`). -/
inductive CompilerVersionProfile where
  | v198LegacyTransmute
  | vHeadBoxDerefTransmute

/-- First-order pointee type algebra (`rustc_middle/src/ty/sty.rs`, `rustc_abi/src/layout.rs`).
    Each `adt` carries its nominal `adtId`, optional `#[repr(packed(2^p))]` cap, static prefix
    size & align exponent, and `tailOffsetUnadj` (unaligned offset of the last field prior to
    alignment rounding, matching `size_of_val.rs:98`). -/
inductive CustomDstTy where
  | sized (tyId : Nat) (size : Nat) (alignLog2 : Nat)
  | array (elem : CustomDstTy) (len : Nat)
  | slice (elem : CustomDstTy)
  | dynTrait (traitId : Nat)
  | adt (adtId : Nat) (packLog2 : Option Nat) (prefixSize : Nat) (prefixAlignLog2 : Nat)
        (tailOffsetUnadj : Nat) (tail : CustomDstTy)

noncomputable def optNatBeq : Option Nat → Option Nat → Bool
  | none, none => true
  | some a, some b => Nat.beq a b
  | _, _ => false

theorem optNatBeq_refl (x : Option Nat) : optNatBeq x x = true := by
  cases x with
  | none => rfl
  | some a => exact Nat.beq_refl a

theorem eq_of_optNatBeq {x y : Option Nat} (h : optNatBeq x y = true) : x = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some _ => exact Bool.noConfusion h
  | some a =>
    cases y with
    | none => exact Bool.noConfusion h
    | some b => exact congrArg some (Nat.eq_of_beq_eq_true h)

noncomputable def CustomDstTy.beq : CustomDstTy → CustomDstTy → Bool
  | .sized id₁ s₁ a₁, .sized id₂ s₂ a₂ =>
    boolAnd (Nat.beq id₁ id₂) (boolAnd (Nat.beq s₁ s₂) (Nat.beq a₁ a₂))
  | .array e₁ n₁, .array e₂ n₂ =>
    boolAnd (CustomDstTy.beq e₁ e₂) (Nat.beq n₁ n₂)
  | .slice e₁, .slice e₂ => CustomDstTy.beq e₁ e₂
  | .dynTrait t₁, .dynTrait t₂ => Nat.beq t₁ t₂
  | .adt i₁ p₁ ps₁ pa₁ to₁ t₁, .adt i₂ p₂ ps₂ pa₂ to₂ t₂ =>
    boolAnd (Nat.beq i₁ i₂)
      (boolAnd (optNatBeq p₁ p₂)
        (boolAnd (Nat.beq ps₁ ps₂)
          (boolAnd (Nat.beq pa₁ pa₂)
            (boolAnd (Nat.beq to₁ to₂) (CustomDstTy.beq t₁ t₂)))))
  | _, _ => false

theorem CustomDstTy.beq_refl (t : CustomDstTy) : CustomDstTy.beq t t = true := by
  induction t with
  | sized id s a =>
    unfold CustomDstTy.beq boolAnd
    rw [Nat.beq_refl id, Nat.beq_refl s, Nat.beq_refl a]
  | array e n ih =>
    unfold CustomDstTy.beq boolAnd
    rw [ih, Nat.beq_refl n]
  | slice e ih =>
    unfold CustomDstTy.beq
    exact ih
  | dynTrait t =>
    unfold CustomDstTy.beq
    exact Nat.beq_refl t
  | adt i p ps pa to t ih =>
    unfold CustomDstTy.beq boolAnd
    rw [Nat.beq_refl i, optNatBeq_refl p, Nat.beq_refl ps, Nat.beq_refl pa, Nat.beq_refl to, ih]

theorem CustomDstTy.eq_of_beq {t₁ t₂ : CustomDstTy} (h : CustomDstTy.beq t₁ t₂ = true) : t₁ = t₂ := by
  induction t₁ generalizing t₂ with
  | sized id₁ s₁ a₁ =>
    cases t₂ with
    | sized id₂ s₂ a₂ =>
      unfold CustomDstTy.beq at h
      rcases boolAnd_eq_true h with ⟨hid, hrest⟩
      rcases boolAnd_eq_true hrest with ⟨hs, ha⟩
      rw [Nat.eq_of_beq_eq_true hid, Nat.eq_of_beq_eq_true hs, Nat.eq_of_beq_eq_true ha]
    | array _ _ => exact Bool.noConfusion h
    | slice _ => exact Bool.noConfusion h
    | dynTrait _ => exact Bool.noConfusion h
    | adt _ _ _ _ _ _ => exact Bool.noConfusion h
  | array e₁ n₁ ih =>
    cases t₂ with
    | array e₂ n₂ =>
      unfold CustomDstTy.beq at h
      rcases boolAnd_eq_true h with ⟨he, hn⟩
      rw [ih he, Nat.eq_of_beq_eq_true hn]
    | sized _ _ _ => exact Bool.noConfusion h
    | slice _ => exact Bool.noConfusion h
    | dynTrait _ => exact Bool.noConfusion h
    | adt _ _ _ _ _ _ => exact Bool.noConfusion h
  | slice e₁ ih =>
    cases t₂ with
    | slice e₂ =>
      unfold CustomDstTy.beq at h
      rw [ih h]
    | sized _ _ _ => exact Bool.noConfusion h
    | array _ _ => exact Bool.noConfusion h
    | dynTrait _ => exact Bool.noConfusion h
    | adt _ _ _ _ _ _ => exact Bool.noConfusion h
  | dynTrait tr₁ =>
    cases t₂ with
    | dynTrait tr₂ =>
      unfold CustomDstTy.beq at h
      rw [Nat.eq_of_beq_eq_true h]
    | sized _ _ _ => exact Bool.noConfusion h
    | array _ _ => exact Bool.noConfusion h
    | slice _ => exact Bool.noConfusion h
    | adt _ _ _ _ _ _ => exact Bool.noConfusion h
  | adt i₁ p₁ ps₁ pa₁ to₁ t₁ ih =>
    cases t₂ with
    | adt i₂ p₂ ps₂ pa₂ to₂ t₂ =>
      unfold CustomDstTy.beq at h
      rcases boolAnd_eq_true h with ⟨hi, h1⟩
      rcases boolAnd_eq_true h1 with ⟨hp, h2⟩
      rcases boolAnd_eq_true h2 with ⟨hps, h3⟩
      rcases boolAnd_eq_true h3 with ⟨hpa, h4⟩
      rcases boolAnd_eq_true h4 with ⟨hto, ht⟩
      rw [Nat.eq_of_beq_eq_true hi, eq_of_optNatBeq hp, Nat.eq_of_beq_eq_true hps,
          Nat.eq_of_beq_eq_true hpa, Nat.eq_of_beq_eq_true hto, ih ht]
    | sized _ _ _ => exact Bool.noConfusion h
    | array _ _ => exact Bool.noConfusion h
    | slice _ => exact Bool.noConfusion h
    | dynTrait _ => exact Bool.noConfusion h

/-- Normalize to the structural tail pointee (`tcx.struct_tail_raw`, `ty/sty.rs`). -/
noncomputable def structTail : CustomDstTy → CustomDstTy
  | .adt _ _ _ _ _ tail => structTail tail
  | other => other

/-- Static sizedness check (`tail.is_sized`). -/
noncomputable def isSized : CustomDstTy → Bool
  | .sized _ _ _ => true
  | .array elem _ => isSized elem
  | .slice _ => false
  | .dynTrait _ => false
  | .adt _ _ _ _ _ tail => isSized tail

/-- Static shape of `Pointee::Metadata` (`rustc_middle/src/ty/sty.rs`: `ptr_metadata_ty_or_tail`). -/
inductive MetaShape where
  | unitShape
  | usizeShape
  | vtableShape (traitId : Nat)

noncomputable def MetaShape.beq : MetaShape → MetaShape → Bool
  | .unitShape, .unitShape => true
  | .usizeShape, .usizeShape => true
  | .vtableShape t₁, .vtableShape t₂ => Nat.beq t₁ t₂
  | _, _ => false

/-- Compute expected `Pointee::Metadata` type shape for any pointee `ty`. -/
noncomputable def expectedMetaShape : CustomDstTy → MetaShape
  | .sized _ _ _ => .unitShape
  | .array _ _ => .unitShape
  | .slice _ => .usizeShape
  | .dynTrait traitId => .vtableShape traitId
  | .adt _ _ _ _ _ tail => expectedMetaShape tail

theorem expectedMetaShape_structTail (ty : CustomDstTy) :
    expectedMetaShape ty = expectedMetaShape (structTail ty) := by
  induction ty with
  | adt _ _ _ _ _ tail ih => exact ih
  | _ => rfl

/-- Wrapper nesting depth around the leaf/unsized struct tail. -/
noncomputable def wrapperDepth : CustomDstTy → Nat
  | .adt _ _ _ _ _ tail => wrapperDepth tail + 1
  | _ => 0

/-- Vtable entry modeled for `DynMetadata<dyn Trait>` (`COMMON_VTABLE_ENTRIES_{SIZE,ALIGN}`
    in `rustc_codegen_ssa/src/size_of_val.rs:31-35`). -/
structure VtableEntry where
  vtableId : Nat
  traitId : Nat
  dynSize : Nat
  dynAlignLog2 : Nat
  isValid : Bool

/-- Runtime metadata value carried in a MIR `ScalarPair` or dropped for thin pointers. -/
inductive MetaVal where
  | unit
  | sliceLen (len : Nat)
  | dynVtable (vtId : Nat)

noncomputable def MetaVal.beq : MetaVal → MetaVal → Bool
  | .unit, .unit => true
  | .sliceLen n₁, .sliceLen n₂ => Nat.beq n₁ n₂
  | .dynVtable v₁, .dynVtable v₂ => Nat.beq v₁ v₂
  | _, _ => false

noncomputable def metaMatchesShape (m : MetaVal) (s : MetaShape) : Bool :=
  match m, s with
  | .unit, .unitShape => true
  | .sliceLen _, .usizeShape => true
  | .dynVtable _, .vtableShape _ => true
  | _, _ => false

noncomputable def lookupVtable (vtables : List VtableEntry) (vtId : Nat) : Option VtableEntry :=
  match vtables with
  | [] => none
  | v :: vs =>
    match Nat.beq v.vtableId vtId with
    | true => some v
    | false => lookupVtable vs vtId

noncomputable def vtableValidFor (vtables : List VtableEntry) (traitId vtId : Nat) : Bool :=
  match lookupVtable vtables vtId with
  | none => false
  | some vt => boolAnd vt.isValid (Nat.beq vt.traitId traitId)

noncomputable def metaValidForTy (vtables : List VtableEntry) (ty : CustomDstTy) (m : MetaVal) : Bool :=
  match expectedMetaShape ty, m with
  | .unitShape, .unit => true
  | .usizeShape, .sliceLen _ => true
  | .vtableShape tid, .dynVtable vtId => vtableValidFor vtables tid vtId
  | _, _ => false

theorem metaValidForTy_structTail (vtables : List VtableEntry) (ty : CustomDstTy) (m : MetaVal) :
    metaValidForTy vtables ty m = metaValidForTy vtables (structTail ty) m := by
  unfold metaValidForTy
  rw [expectedMetaShape_structTail ty]

theorem metaValidForTy_implies_shape {vtables : List VtableEntry} {ty : CustomDstTy} {m : MetaVal}
    (h : metaValidForTy vtables ty m = true) :
    metaMatchesShape m (expectedMetaShape ty) = true := by
  unfold metaValidForTy at h
  cases hs : expectedMetaShape ty with
  | unitShape =>
    cases m with
    | unit => rfl
    | sliceLen _ => rw [hs] at h; exact Bool.noConfusion h
    | dynVtable _ => rw [hs] at h; exact Bool.noConfusion h
  | usizeShape =>
    cases m with
    | sliceLen _ => rfl
    | unit => rw [hs] at h; exact Bool.noConfusion h
    | dynVtable _ => rw [hs] at h; exact Bool.noConfusion h
  | vtableShape tid =>
    cases m with
    | dynVtable _ => rfl
    | unit => rw [hs] at h; exact Bool.noConfusion h
    | sliceLen _ => rw [hs] at h; exact Bool.noConfusion h

/-- Unsizing relation `PointerCoercion::Unsize` from `src` to `dst`, supporting
    direct `[T; N] -> [T]`, `Concrete -> dyn Trait`, and arbitrary-depth custom-DST
    struct-tail unsizing `Wrapper<..., [T; N]> -> Wrapper<..., [T]>`. -/
noncomputable def unsizeRel (vtables : List VtableEntry) : CustomDstTy → CustomDstTy → Bool
  | .array e₁ _, .slice e₂ => CustomDstTy.beq e₁ e₂
  | .sized tid _ _, .dynTrait trId => vtableValidFor vtables trId tid
  | .adt i₁ p₁ ps₁ pa₁ to₁ t₁, .adt i₂ p₂ ps₂ pa₂ to₂ t₂ =>
    boolAnd (Nat.beq i₁ i₂)
      (boolAnd (optNatBeq p₁ p₂)
        (boolAnd (Nat.beq ps₁ ps₂)
          (boolAnd (Nat.beq pa₁ pa₂)
            (boolAnd (Nat.beq to₁ to₂) (unsizeRel vtables t₁ t₂)))))
  | _, _ => false

/-- Deterministically compute runtime metadata produced by `CastKind::Unsize`. -/
noncomputable def unsizeMetadata : CustomDstTy → CustomDstTy → Option MetaVal
  | .array _ n, .slice _ => some (.sliceLen n)
  | .sized tid _ _, .dynTrait _ => some (.dynVtable tid)
  | .adt _ _ _ _ _ t₁, .adt _ _ _ _ _ t₂ => unsizeMetadata t₁ t₂
  | _, _ => none

theorem unsize_nested_array_to_slice_meta {vtables : List VtableEntry} {src dst : CustomDstTy}
    {elem : CustomDstTy} {n : Nat}
    (hrel : unsizeRel vtables src dst = true)
    (htail : structTail src = .array elem n) :
    unsizeMetadata src dst = some (.sliceLen n) := by
  induction src generalizing dst with
  | array e m =>
    cases dst with
    | slice e₂ =>
      cases htail
      rfl
    | sized _ _ _ => exact Bool.noConfusion hrel
    | array _ _ => exact Bool.noConfusion hrel
    | dynTrait _ => exact Bool.noConfusion hrel
    | adt _ _ _ _ _ _ => exact Bool.noConfusion hrel
  | adt i p ps pa to tail ih =>
    cases dst with
    | adt i₂ p₂ ps₂ pa₂ to₂ tail₂ =>
      unfold unsizeRel at hrel
      rcases boolAnd_eq_true hrel with ⟨_, h1⟩
      rcases boolAnd_eq_true h1 with ⟨_, h2⟩
      rcases boolAnd_eq_true h2 with ⟨_, h3⟩
      rcases boolAnd_eq_true h3 with ⟨_, h4⟩
      rcases boolAnd_eq_true h4 with ⟨_, htail_rel⟩
      exact ih htail_rel htail
    | sized _ _ _ => exact Bool.noConfusion hrel
    | array _ _ => exact Bool.noConfusion hrel
    | slice _ => exact Bool.noConfusion hrel
    | dynTrait _ => exact Bool.noConfusion hrel
  | sized _ _ _ => cases htail
  | slice _ => cases htail
  | dynTrait _ => cases htail

theorem unsize_produces_valid_meta {vtables : List VtableEntry} {src dst : CustomDstTy} {m : MetaVal}
    (hrel : unsizeRel vtables src dst = true)
    (hmeta : unsizeMetadata src dst = some m) :
    metaValidForTy vtables dst m = true := by
  induction src generalizing dst with
  | array e n =>
    cases dst with
    | slice e₂ =>
      cases hmeta
      rfl
    | sized _ _ _ => exact Bool.noConfusion hrel
    | array _ _ => exact Bool.noConfusion hrel
    | dynTrait _ => exact Bool.noConfusion hrel
    | adt _ _ _ _ _ _ => exact Bool.noConfusion hrel
  | sized tid _ _ =>
    cases dst with
    | dynTrait trId =>
      cases hmeta
      unfold metaValidForTy expectedMetaShape
      exact hrel
    | sized _ _ _ => exact Bool.noConfusion hrel
    | array _ _ => exact Bool.noConfusion hrel
    | slice _ => exact Bool.noConfusion hrel
    | adt _ _ _ _ _ _ => exact Bool.noConfusion hrel
  | adt i p ps pa to tail ih =>
    cases dst with
    | adt i₂ p₂ ps₂ pa₂ to₂ tail₂ =>
      unfold unsizeRel at hrel
      rcases boolAnd_eq_true hrel with ⟨_, h1⟩
      rcases boolAnd_eq_true h1 with ⟨_, h2⟩
      rcases boolAnd_eq_true h2 with ⟨_, h3⟩
      rcases boolAnd_eq_true h3 with ⟨_, h4⟩
      rcases boolAnd_eq_true h4 with ⟨_, htail_rel⟩
      unfold unsizeMetadata at hmeta
      have ih_res := ih htail_rel hmeta
      unfold metaValidForTy expectedMetaShape
      exact ih_res
    | sized _ _ _ => exact Bool.noConfusion hrel
    | array _ _ => exact Bool.noConfusion hrel
    | slice _ => exact Bool.noConfusion hrel
    | dynTrait _ => exact Bool.noConfusion hrel
  | slice _ => exact Bool.noConfusion hrel
  | dynTrait _ => exact Bool.noConfusion hrel

/-! ## 3. `size_of_val` / `PlaceRef::project_field` Dynamic Layout & Alignment Rounding -/

/-- Dynamic `(size, align)` computation matching `compiler/rustc_codegen_ssa/src/size_of_val.rs:15-180`. -/
noncomputable def sizeAndAlignOfDst (vtables : List VtableEntry) :
    CustomDstTy → MetaVal → Option (Nat × Nat)
  | .sized _ sz alLog, .unit =>
    let al := Nat.pow 2 alLog
    some (alignUp sz al, al)
  | .array elem len, .unit =>
    match sizeAndAlignOfDst vtables elem .unit with
    | none => none
    | some (esz, eal) => some (esz * len, eal)
  | .slice elem, .sliceLen n =>
    match sizeAndAlignOfDst vtables elem .unit with
    | none => none
    | some (esz, eal) => some (esz * n, eal)
  | .dynTrait trId, .dynVtable vtId =>
    match lookupVtable vtables vtId with
    | none => none
    | some vt =>
      match boolAnd vt.isValid (Nat.beq vt.traitId trId) with
      | false => none
      | true => some (vt.dynSize, Nat.pow 2 vt.dynAlignLog2)
  | .adt _ pack _ szAlLog tailOffUnadj tail, m =>
    match sizeAndAlignOfDst vtables tail m with
    | none => none
    | some (uSize, uAlignRaw) =>
      let uAlign := capPackAlign pack uAlignRaw
      let fAlign := fastMax (Nat.pow 2 szAlLog) uAlign
      let fullSize := alignUp (tailOffUnadj + uSize) fAlign
      some (fullSize, fAlign)
  | _, _ => none

noncomputable def wellFormedVtables : List VtableEntry → Bool
  | [] => true
  | v :: vs =>
    boolAnd (Nat.beq (v.dynSize % Nat.pow 2 v.dynAlignLog2) 0) (wellFormedVtables vs)

theorem lookupVtable_wf {vtables : List VtableEntry} {vtId : Nat} {vt : VtableEntry}
    (hwf : wellFormedVtables vtables = true) (hlook : lookupVtable vtables vtId = some vt) :
    Nat.pow 2 vt.dynAlignLog2 ∣ vt.dynSize := by
  induction vtables with
  | nil => cases hlook
  | cons v vs ih =>
    unfold wellFormedVtables at hwf
    rcases boolAnd_eq_true hwf with ⟨hdvd, hrest⟩
    unfold lookupVtable at hlook
    cases heq : Nat.beq v.vtableId vtId with
    | true =>
      rw [heq] at hlook
      injection hlook with hv
      rw [← hv]
      exact Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true hdvd)
    | false =>
      rw [heq] at hlook
      exact ih hrest hlook

/-- `sizeAndAlignOfDst` preserves two fundamental ABI invariants at every type level:
    (1) the dynamic alignment is a positive power of two (witnessed by exponent `e`), and
    (2) the dynamic byte size is always a multiple of the dynamic alignment (`fullAlign ∣ fullSize`),
    justifying `size_of_val.rs:151` (*"`unsized_size` is a multiple of `unsized_align`"*). -/
theorem sizeAndAlignOfDst_pow2_and_dvd {vtables : List VtableEntry}
    (hwfV : wellFormedVtables vtables = true)
    (ty : CustomDstTy) (m : MetaVal) {sz al : Nat}
    (hsz : sizeAndAlignOfDst vtables ty m = some (sz, al)) :
    ∃ e : Nat, al = Nat.pow 2 e ∧ 0 < al ∧ al ∣ sz := by
  induction ty generalizing m sz al with
  | sized _ s a =>
    cases m with
    | unit =>
      unfold sizeAndAlignOfDst at hsz
      injection hsz with hpair
      have h1 : alignUp s (Nat.pow 2 a) = sz := congrArg Prod.fst hpair
      have h2 : Nat.pow 2 a = al := congrArg Prod.snd hpair
      rw [← h1, ← h2]
      have hpos : 0 < Nat.pow 2 a := Nat.pow_pos (Nat.succ_pos 1)
      exact ⟨a, rfl, hpos, alignUp_dvd hpos⟩
    | sliceLen _ => cases hsz
    | dynVtable _ => cases hsz
  | array elem len ih =>
    cases m with
    | unit =>
      unfold sizeAndAlignOfDst at hsz
      cases helem : sizeAndAlignOfDst vtables elem .unit with
      | none => rw [helem] at hsz; cases hsz
      | some p =>
        rcases p with ⟨esz, eal⟩
        rw [helem] at hsz
        injection hsz with hpair
        have h1 : esz * len = sz := congrArg Prod.fst hpair
        have h2 : eal = al := congrArg Prod.snd hpair
        rw [← h1, ← h2]
        rcases ih .unit helem with ⟨e, heq, hpos, hdvd⟩
        exact ⟨e, heq, hpos, Nat.dvd_trans hdvd ⟨len, rfl⟩⟩
    | sliceLen _ => cases hsz
    | dynVtable _ => cases hsz
  | slice elem ih =>
    cases m with
    | unit => cases hsz
    | dynVtable _ => cases hsz
    | sliceLen n =>
      unfold sizeAndAlignOfDst at hsz
      cases helem : sizeAndAlignOfDst vtables elem .unit with
      | none => rw [helem] at hsz; cases hsz
      | some p =>
        rcases p with ⟨esz, eal⟩
        rw [helem] at hsz
        injection hsz with hpair
        have h1 : esz * n = sz := congrArg Prod.fst hpair
        have h2 : eal = al := congrArg Prod.snd hpair
        rw [← h1, ← h2]
        rcases ih .unit helem with ⟨e, heq, hpos, hdvd⟩
        exact ⟨e, heq, hpos, Nat.dvd_trans hdvd ⟨n, rfl⟩⟩
  | dynTrait trId =>
    cases m with
    | unit => cases hsz
    | sliceLen _ => cases hsz
    | dynVtable vtId =>
      unfold sizeAndAlignOfDst at hsz
      cases hlook : lookupVtable vtables vtId with
      | none => rw [hlook] at hsz; cases hsz
      | some vt =>
        rw [hlook] at hsz
        dsimp only at hsz
        cases hchk : boolAnd vt.isValid (Nat.beq vt.traitId trId) with
        | false => rw [hchk] at hsz; cases hsz
        | true =>
          rw [hchk] at hsz
          injection hsz with hpair
          have h1 : vt.dynSize = sz := congrArg Prod.fst hpair
          have h2 : Nat.pow 2 vt.dynAlignLog2 = al := congrArg Prod.snd hpair
          rw [← h1, ← h2]
          have hpos : 0 < Nat.pow 2 vt.dynAlignLog2 := Nat.pow_pos (Nat.succ_pos 1)
          exact ⟨vt.dynAlignLog2, rfl, hpos, lookupVtable_wf hwfV hlook⟩
  | adt _ pack _ szAlLog tailOffUnadj tail ih =>
    unfold sizeAndAlignOfDst at hsz
    cases htail : sizeAndAlignOfDst vtables tail m with
    | none => rw [htail] at hsz; cases hsz
    | some p =>
      rcases p with ⟨uSize, uAlignRaw⟩
      rw [htail] at hsz
      injection hsz with hpair
      have hsz_eq : alignUp (tailOffUnadj + uSize) (fastMax (Nat.pow 2 szAlLog) (capPackAlign pack uAlignRaw)) = sz :=
        congrArg Prod.fst hpair
      have hal_eq : fastMax (Nat.pow 2 szAlLog) (capPackAlign pack uAlignRaw) = al :=
        congrArg Prod.snd hpair
      rcases ih m htail with ⟨eu, heu_eq, _, hu_dvd⟩
      rw [heu_eq] at hu_dvd
      rcases capPackAlign_pow2_dvd (pack := pack) hu_dvd with ⟨eu', heu', _⟩
      rw [heu_eq] at hsz_eq hal_eq
      rw [heu'] at hsz_eq hal_eq
      rcases fastMax_pow2_witness szAlLog eu' with ⟨ef, hef⟩
      rw [hef] at hsz_eq hal_eq
      rw [← hsz_eq, ← hal_eq]
      have hpos : 0 < Nat.pow 2 ef := Nat.pow_pos (Nat.succ_pos 1)
      exact ⟨ef, rfl, hpos, alignUp_dvd hpos⟩

/-- Models `PlaceRef::project_field` tail offset computation (`compiler/rustc_codegen_ssa/src/mir/place.rs:175-258`):
    - Sized tail, `Slice`/`Str`, or `unalignedOffset = 0`: skips dynamic alignment rounding (`offset = unalignedOffset`).
    - Otherwise (e.g., nested custom-DST `adt` at `offset > 0` such as `Inner<[u8]>` inside `Wrapper<[u8]>`):
      computes `sizeAndAlignOfDst` of the field type, caps by `pack`, and returns `alignUp unalignedOffset effAlign`. -/
noncomputable def projectTailOffset (vtables : List VtableEntry) (outerTy : CustomDstTy) (m : MetaVal) :
    Option Nat :=
  match outerTy with
  | .adt _ pack _ _ unadj tail =>
    match isSized tail with
    | true => some unadj
    | false =>
      match tail with
      | .slice _ => some unadj
      | _ =>
        match Nat.beq unadj 0 with
        | true => some 0
        | false =>
          match sizeAndAlignOfDst vtables tail m with
          | none => none
          | some (_, uAlignRaw) =>
            some (alignUp unadj (capPackAlign pack uAlignRaw))
  | _ => none

/-- **`size_of_val.rs` & `PlaceRef::project_field` Equivalence + In-Bounds Soundness:**
    1. Adjusting the tail field offset explicitly by `alignUp tailOffUnadj (capPackAlign pack uAlRaw)`
       before computing `alignUp (adjustedOffset + uSz) fullAlign` agrees bit-for-bit with
       `sizeAndAlignOfDst`'s elided formula `alignUp (tailOffUnadj + uSz) fullAlign`.
    2. For ANY valid metadata `m`, the projected tail region `[adjustedOffset, adjustedOffset + uSz]`
       lies strictly within `[0, fullSz]`. -/
theorem sizeAndAlign_adjustedOffset_equiv_and_tail_inbounds {vtables : List VtableEntry}
    (hwfV : wellFormedVtables vtables = true)
    (id : Nat) (pack : Option Nat) (ps paLog tailOffUnadj : Nat) (tail : CustomDstTy)
    (m : MetaVal) {fullSz fullAl uSz uAlRaw : Nat}
    (hfull : sizeAndAlignOfDst vtables (.adt id pack ps paLog tailOffUnadj tail) m = some (fullSz, fullAl))
    (htail : sizeAndAlignOfDst vtables tail m = some (uSz, uAlRaw)) :
    alignUp (alignUp tailOffUnadj (capPackAlign pack uAlRaw) + uSz) fullAl = fullSz ∧
    alignUp tailOffUnadj (capPackAlign pack uAlRaw) + uSz ≤ fullSz := by
  unfold sizeAndAlignOfDst at hfull
  rw [htail] at hfull
  injection hfull with hpair
  have hsz_eq : alignUp (tailOffUnadj + uSz) (fastMax (Nat.pow 2 paLog) (capPackAlign pack uAlRaw)) = fullSz :=
    congrArg Prod.fst hpair
  have hal_eq : fastMax (Nat.pow 2 paLog) (capPackAlign pack uAlRaw) = fullAl :=
    congrArg Prod.snd hpair
  rcases sizeAndAlignOfDst_pow2_and_dvd hwfV tail m htail with ⟨eu, heu_eq, _, hu_dvd_sz⟩
  rw [heu_eq] at hu_dvd_sz
  rcases capPackAlign_pow2_dvd (pack := pack) hu_dvd_sz with ⟨eu', heu', heff_dvd_sz⟩
  have heff_dvd_full : capPackAlign pack uAlRaw ∣ fullAl := by
    rw [← hal_eq, heu_eq, heu']
    exact (pow2_max_both_dvd paLog eu').2
  have heff_pos : 0 < capPackAlign pack uAlRaw := by
    rw [heu_eq, heu']
    exact Nat.pow_pos (Nat.succ_pos 1)
  have hfull_pos : 0 < fullAl := by
    rw [← hal_eq]
    exact Nat.lt_of_lt_of_le (Nat.pow_pos (Nat.succ_pos 1)) (fastMax_ge_left _ _)
  have heff_sz_dvd' : capPackAlign pack uAlRaw ∣ uSz := by
    rw [heu_eq]
    exact heff_dvd_sz
  have hequiv : alignUp (alignUp tailOffUnadj (capPackAlign pack uAlRaw) + uSz) fullAl = fullSz :=
    calc alignUp (alignUp tailOffUnadj (capPackAlign pack uAlRaw) + uSz) fullAl
        = alignUp (tailOffUnadj + uSz) fullAl :=
          alignUp_add_mul_absorb heff_pos hfull_pos heff_sz_dvd' heff_dvd_full
      _ = fullSz := by rw [← hal_eq]; exact hsz_eq
  exact ⟨hequiv, hequiv ▸ alignUp_ge _ fullAl⟩

/-! ## 4. Typed `(AddrProvenance, Metadata)` Operational Semantics for MIR Pointers -/

/-- Pointer provenance tag separating no-provenance / dangling raw integers (`null` or
    `ptr::without_provenance`) from live/freed heap or stack allocations. -/
inductive Provenance where
  | none
  | alloc (allocId : Nat)

noncomputable def Provenance.beq : Provenance → Provenance → Bool
  | .none, .none => true
  | .alloc a, .alloc b => Nat.beq a b
  | _, _ => false

/-- Thin pointer carrying `(address, provenance)` — identical to MIR `*const ()` / `Scalar`. -/
structure ThinPtr where
  addr : Nat
  prov : Provenance

/-- Abstract allocation record modeling Miri Stacked Borrows (`sbReadable`), Tree Borrows
    (`tbReadable`), liveness, and byte range `[baseAddr, baseAddr + allocSize)`. -/
structure AllocRecord where
  allocId : Nat
  live : Bool
  baseAddr : Nat
  allocSize : Nat
  writable : Bool
  sbReadable : Bool
  tbReadable : Bool

/-- Machine memory/vtable environment (`isizeMax` fixed per target pointer width). -/
structure MemEnv where
  isizeMax : Nat
  allocs : List AllocRecord
  vtables : List VtableEntry

noncomputable def lookupAlloc (allocs : List AllocRecord) (aid : Nat) : Option AllocRecord :=
  match allocs with
  | [] => none
  | a :: as =>
    match Nat.beq a.allocId aid with
    | true => some a
    | false => lookupAlloc as aid

/-- Wide (or thin, when `meta = .unit`) MIR pointer value (`Scalar` or `ScalarPair`). -/
structure WidePtr where
  data : ThinPtr
  ptrMeta : MetaVal
  pointee : CustomDstTy

/-- How a pointer is being dereferenced or inspected. -/
inductive PtrCategory where
  | rawPtr
  | sharedRef
  | mutRef
  | boxPtr

/-- Precision error categories distinguishing every Miri UB diagnostic captured in `l01..l14b`. -/
inductive SemError where
  | invalidMetaShape
  | nullReference
  | danglingUseAfterFree
  | unalignedPointer
  | outOfBoundsPointer
  | sizeOverflowsIsizeMax
  | invalidOrForgedVtable
  | danglingInboundsOffset
  | aliasingBorrowConflict
  | invalidBoxTransmute
  | unsupportedOp

/-- Evaluation result type for MIR wide-pointer operations. -/
inductive EvalRes (α : Type) where
  | ok (v : α)
  | err (e : SemError)

/-- Check `deref_pointer` validity (`compiler/rustc_const_eval/src/interpret/place.rs:468-538`).
    - For `rawPtr`: validates ONLY `DynMetadata` vtable validity when `pointee`'s tail is `dyn Trait`,
      performing NO null, provenance, liveness, bounds, or alignment checks (`// Nothing to check`).
    - For `sharedRef | mutRef | boxPtr`: checks non-null, live provenance, alignment, `[addr, addr + sz]`
      in-bounds inside allocation `[base, base + allocSize)`, `sz ≤ isizeMax`, and aliasing/write access. -/
noncomputable def checkPtrValidity (env : MemEnv) (cat : PtrCategory) (p : WidePtr) : EvalRes Unit :=
  match metaValidForTy env.vtables p.pointee p.ptrMeta with
  | false =>
    match expectedMetaShape p.pointee, p.ptrMeta with
    | .vtableShape _, .dynVtable _ => .err .invalidOrForgedVtable
    | _, _ => .err .invalidMetaShape
  | true =>
    match cat with
    | .rawPtr => .ok ()
    | _ =>
      match sizeAndAlignOfDst env.vtables p.pointee p.ptrMeta with
      | none => .err .invalidOrForgedVtable
      | some (sz, al) =>
        match Nat.beq p.data.addr 0 with
        | true => .err .nullReference
        | false =>
          match Nat.ble sz env.isizeMax with
          | false => .err .sizeOverflowsIsizeMax
          | true =>
            match Nat.beq (p.data.addr % al) 0 with
            | false => .err .unalignedPointer
            | true =>
              match p.data.prov with
              | .none => .err .danglingUseAfterFree
              | .alloc aid =>
                match lookupAlloc env.allocs aid with
                | none => .err .danglingUseAfterFree
                | some rec =>
                  match rec.live with
                  | false => .err .danglingUseAfterFree
                  | true =>
                    match boolAnd (Nat.ble rec.baseAddr p.data.addr)
                                  (Nat.ble (p.data.addr + sz) (rec.baseAddr + rec.allocSize)) with
                    | false => .err .outOfBoundsPointer
                    | true =>
                      match cat with
                      | .mutRef =>
                        match rec.writable with
                        | true => .ok ()
                        | false => .err .aliasingBorrowConflict
                      | _ => .ok ()

/-- Semantics of `Rvalue::UnaryOp(UnOp::PtrMetadata, op)` (`operator.rs:487-514`). -/
noncomputable def evalPtrMetadata (prof : CompilerVersionProfile) (env : MemEnv) (cat : PtrCategory)
    (p : WidePtr) : EvalRes MetaVal :=
  let preCheck : EvalRes Unit :=
    match prof with
    | .v198LegacyTransmute =>
      match metaValidForTy env.vtables p.pointee p.ptrMeta with
      | false =>
        match expectedMetaShape p.pointee, p.ptrMeta with
        | .vtableShape _, .dynVtable _ => .err .invalidOrForgedVtable
        | _, _ => .err .invalidMetaShape
      | true => .ok ()
    | .vHeadBoxDerefTransmute => checkPtrValidity env cat p
  match preCheck with
  | .err e => .err e
  | .ok () => .ok p.ptrMeta

noncomputable def invalidMetaErr (ty : CustomDstTy) (mv : MetaVal) : SemError :=
  match expectedMetaShape ty, mv with
  | .vtableShape _, .dynVtable _ => .invalidOrForgedVtable
  | _, _ => .invalidMetaShape

/-- Semantics of `Rvalue::Aggregate(AggregateKind::RawPtr(pointee, mutbl), [data, meta])`
    (`ptr::from_raw_parts`, `LowerIntrinsics`, `rustc_codegen_ssa/src/mir/rvalue.rs:807-842`). -/
noncomputable def evalAggregateRawPtr (env : MemEnv) (pointee : CustomDstTy)
    (data : ThinPtr) (mv : MetaVal) : EvalRes WidePtr :=
  match metaValidForTy env.vtables pointee mv with
  | false => .err (invalidMetaErr pointee mv)
  | true => .ok { data := data, ptrMeta := mv, pointee := pointee }

/-- Thin data pointer projection (`Cast(PtrToPtr)` from `*const T` to `*const ()`). -/
noncomputable def toThinData (p : WidePtr) : ThinPtr := p.data

/-- Semantics of `&raw const (*p).field` with `OffsetMode::Inbounds` vs `FakeForPtrMetadata`
    (`rustc_const_eval/src/interpret/projection.rs:200`, `step.rs:257`). -/
noncomputable def evalProjectFieldRaw (env : MemEnv) (kind : MirRawPtrKind) (cat : PtrCategory)
    (p : WidePtr) (fieldOffset : Nat) (fieldTy : CustomDstTy) : EvalRes WidePtr :=
  let nextData : ThinPtr := { addr := p.data.addr + fieldOffset, prov := p.data.prov }
  let inboundsCheck : EvalRes WidePtr :=
    match p.data.prov with
    | .none => .err .danglingInboundsOffset
    | .alloc aid =>
      match lookupAlloc env.allocs aid with
      | none => .err .danglingInboundsOffset
      | some rec =>
        match boolAnd rec.live
                (boolAnd (Nat.ble rec.baseAddr p.data.addr)
                         (Nat.ble (p.data.addr + fieldOffset) (rec.baseAddr + rec.allocSize))) with
        | false => .err .danglingInboundsOffset
        | true => .ok { data := nextData, ptrMeta := p.ptrMeta, pointee := fieldTy }
  match kind with
  | .fakeForPtrMetadata =>
    match Nat.beq fieldOffset 0 with
    | true => .ok { data := p.data, ptrMeta := p.ptrMeta, pointee := fieldTy }
    | false =>
      match cat with
      | .rawPtr => inboundsCheck
      | _ =>
        match checkPtrValidity env cat p with
        | .err e => .err e
        | .ok () => .ok { data := nextData, ptrMeta := p.ptrMeta, pointee := fieldTy }
  | .regular _ =>
    match Nat.beq fieldOffset 0 with
    | true => .ok { data := p.data, ptrMeta := p.ptrMeta, pointee := fieldTy }
    | false => inboundsCheck

/-- Semantics of `&raw const (*b)` vs `&(*b)` after `ElaborateBoxDerefs` across `1.98` vs `HEAD`. -/
noncomputable def evalBoxRawDeref (prof : CompilerVersionProfile) (env : MemEnv) (b : WidePtr) : EvalRes WidePtr :=
  match prof with
  | .v198LegacyTransmute =>
    match Nat.beq b.data.addr 0 with
    | true => .err .nullReference
    | false =>
      match metaValidForTy env.vtables b.pointee b.ptrMeta with
      | false => .err .invalidOrForgedVtable
      | true => .ok b
  | .vHeadBoxDerefTransmute =>
    match checkPtrValidity env .boxPtr b with
    | .err e => .err e
    | .ok () => .ok b

noncomputable def evalBoxRefReborrow (env : MemEnv) (b : WidePtr) : EvalRes WidePtr :=
  match checkPtrValidity env .sharedRef b with
  | .err e => .err e
  | .ok () => .ok b

/-- Semantics of `CastKind::Unsize`: updates pointee type and metadata while preserving thin
    address & provenance identically (`p.data`). -/
noncomputable def evalUnsizeCast (env : MemEnv) (dst : CustomDstTy) (p : WidePtr) : EvalRes WidePtr :=
  match unsizeRel env.vtables p.pointee dst with
  | false => .err .unsupportedOp
  | true =>
    match unsizeMetadata p.pointee dst with
    | none => .err .unsupportedOp
    | some newMeta => .ok { data := p.data, ptrMeta := newMeta, pointee := dst }

/-! ## 5. Exact Round-Trip, Provenance Preservation, Memory Independence, & `Box` Discriminators -/

/-- **Theorem 1 (`from_raw_parts ∘ (to_thin_data, ptr_metadata)` Exact Round-Trip & Provenance Preservation):**
    For EVERY wide (or thin) pointer `p` whose metadata shape & vtable entry are well-typed under `env`,
    extracting `ptr::metadata` as `.rawPtr` and reconstructing via `from_raw_parts` (`AggregateKind::RawPtr`)
    recovers the EXACT original pointer (`addr`, `prov`, `meta`, `pointee`)—regardless of whether
    `p.data.addr` is null, unaligned, out-of-bounds, freed, or `.none`. -/
theorem fromRawParts_after_decompose_exact (prof : CompilerVersionProfile) (env : MemEnv)
    (p : WidePtr) (hm : metaValidForTy env.vtables p.pointee p.ptrMeta = true) :
    (match evalPtrMetadata prof env .rawPtr p with
     | .err (e : SemError) => EvalRes.err e
     | .ok m => evalAggregateRawPtr env p.pointee (toThinData p) m) = .ok p := by
  have hmeta : evalPtrMetadata prof env .rawPtr p = .ok p.ptrMeta := by
    unfold evalPtrMetadata
    cases prof with
    | v198LegacyTransmute => rw [hm]
    | vHeadBoxDerefTransmute =>
      unfold checkPtrValidity
      rw [hm]
  rw [hmeta]
  unfold evalAggregateRawPtr toThinData
  dsimp only
  rw [hm]

/-- **Theorem 2 (`(to_thin_data, ptr_metadata) ∘ from_raw_parts` Left-Inverse):**
    Whenever `from_raw_parts(d, m)` succeeds producing `w`, both `toThinData w = d` and
    `evalPtrMetadata prof env .rawPtr w = .ok m`. -/
theorem decompose_after_fromRawParts_exact (prof : CompilerVersionProfile) (env : MemEnv)
    (ty : CustomDstTy) (d : ThinPtr) (m : MetaVal) {w : WidePtr}
    (hagg : evalAggregateRawPtr env ty d m = .ok w) :
    toThinData w = d ∧ evalPtrMetadata prof env .rawPtr w = .ok m := by
  unfold evalAggregateRawPtr at hagg
  cases hm : metaValidForTy env.vtables ty m with
  | false =>
    rw [hm] at hagg
    cases hagg
  | true =>
    rw [hm] at hagg
    injection hagg with hw
    rw [← hw]
    constructor
    · rfl
    · unfold evalPtrMetadata
      cases prof with
      | v198LegacyTransmute => rw [hm]
      | vHeadBoxDerefTransmute =>
        unfold checkPtrValidity
        rw [hm]

/-- **Theorem 3 (Memory / Allocation / Dangling / Alignment Independence of Raw `ptr::metadata`):**
    Changing `allocs`, `isizeMax`, or `p.data` (`addr` and `prov`) leaves `evalPtrMetadata prof env .rawPtr`
    strictly invariant across allocations and data pointers. -/
theorem ptrMetadata_dangling_uninit_data_independent (prof : CompilerVersionProfile)
    (isizeMax₁ isizeMax₂ : Nat) (allocs₁ allocs₂ : List AllocRecord)
    (vtables : List VtableEntry) (d₁ d₂ : ThinPtr) (m : MetaVal) (ty : CustomDstTy) :
    evalPtrMetadata prof ⟨isizeMax₁, allocs₁, vtables⟩ .rawPtr ⟨d₁, m, ty⟩ =
    evalPtrMetadata prof ⟨isizeMax₂, allocs₂, vtables⟩ .rawPtr ⟨d₂, m, ty⟩ := by
  cases prof <;> rfl

/-- Helper showing `Wrapper<[u8]>` with non-zero metadata is invalid as a shared ref/box at `⟨addr, .none⟩`. -/
theorem dangling_wrapper_checkPtrValidity_err (env : MemEnv) (cat : PtrCategory)
    (hnotraw : match cat with | .rawPtr => False | _ => True)
    (addr n : Nat) (hprov : Provenance.none = Provenance.none) :
    let customTy : CustomDstTy := .adt 1 none 3 1 2 (.adt 2 none 2 1 2 (.slice (.sized 10 1 0)))
    let ptr : WidePtr := ⟨⟨addr, .none⟩, .sliceLen n, customTy⟩
    ∃ e : SemError, checkPtrValidity env cat ptr = .err e := by
  intro customTy ptr
  have _ := hprov
  unfold checkPtrValidity
  have hvalid : metaValidForTy env.vtables customTy (.sliceLen n) = true := rfl
  have hsz : sizeAndAlignOfDst env.vtables customTy (.sliceLen n) =
      some (alignUp (2 + alignUp (2 + 1 * n) 2) 2, 2) := rfl
  change ∃ e : SemError,
      (match metaValidForTy env.vtables customTy (.sliceLen n) with
       | false => EvalRes.err (invalidMetaErr customTy (.sliceLen n))
       | true =>
         match cat with
         | .rawPtr => EvalRes.ok ()
         | _ =>
           match sizeAndAlignOfDst env.vtables customTy (.sliceLen n) with
           | none => EvalRes.err .invalidOrForgedVtable
           | some (sz, al) =>
             match Nat.beq addr 0 with
             | true => EvalRes.err .nullReference
             | false =>
               match Nat.ble sz env.isizeMax with
               | false => EvalRes.err .sizeOverflowsIsizeMax
               | true =>
                 match Nat.beq (addr % al) 0 with
                 | false => EvalRes.err .unalignedPointer
                 | true => EvalRes.err .danglingUseAfterFree) = EvalRes.err e
  rw [hvalid, hsz]
  dsimp only
  cases cat with
  | rawPtr => exact False.elim hnotraw
  | sharedRef =>
    dsimp only
    cases Nat.beq addr 0 with
    | true => exact ⟨.nullReference, rfl⟩
    | false =>
      dsimp only
      cases Nat.ble (alignUp (2 + alignUp (2 + 1 * n) 2) 2) env.isizeMax with
      | false => exact ⟨.sizeOverflowsIsizeMax, rfl⟩
      | true =>
        dsimp only
        cases Nat.beq (addr % 2) 0 with
        | false => exact ⟨.unalignedPointer, rfl⟩
        | true => exact ⟨.danglingUseAfterFree, rfl⟩
  | mutRef =>
    dsimp only
    cases Nat.beq addr 0 with
    | true => exact ⟨.nullReference, rfl⟩
    | false =>
      dsimp only
      cases Nat.ble (alignUp (2 + alignUp (2 + 1 * n) 2) 2) env.isizeMax with
      | false => exact ⟨.sizeOverflowsIsizeMax, rfl⟩
      | true =>
        dsimp only
        cases Nat.beq (addr % 2) 0 with
        | false => exact ⟨.unalignedPointer, rfl⟩
        | true => exact ⟨.danglingUseAfterFree, rfl⟩
  | boxPtr =>
    dsimp only
    cases Nat.beq addr 0 with
    | true => exact ⟨.nullReference, rfl⟩
    | false =>
      dsimp only
      cases Nat.ble (alignUp (2 + alignUp (2 + 1 * n) 2) 2) env.isizeMax with
      | false => exact ⟨.sizeOverflowsIsizeMax, rfl⟩
      | true =>
        dsimp only
        cases Nat.beq (addr % 2) 0 with
        | false => exact ⟨.unalignedPointer, rfl⟩
        | true => exact ⟨.danglingUseAfterFree, rfl⟩

/-- **Theorem 4 (`OffsetMode::Inbounds` vs Direct Raw `ptr::metadata` Sharpness):**
    On a dangling/no-provenance custom-DST raw pointer `(addr := 2, prov := .none)` (`l02` vs `l12`),
    direct `ptr::metadata(p)` succeeds while `&raw const (*p).inner` (`fieldOffset = 2 > 0`) fails with
    `SemError.danglingInboundsOffset` and `&*p` fails unconditionally. -/
theorem dangling_rawPtr_metadata_passes_while_nonzero_field_and_ref_fail
    (prof : CompilerVersionProfile) (env : MemEnv) (tailTy : CustomDstTy) (n : Nat) :
    let customTy : CustomDstTy := .adt 1 none 3 1 2 (.adt 2 none 2 1 2 (.slice (.sized 10 1 0)))
    let ptr : WidePtr := ⟨⟨2, .none⟩, .sliceLen n, customTy⟩
    evalPtrMetadata prof env .rawPtr ptr = .ok (.sliceLen n) ∧
    evalProjectFieldRaw env (.regular .shared) .rawPtr ptr 2 tailTy = .err .danglingInboundsOffset ∧
    (∃ e : SemError, checkPtrValidity env .sharedRef ptr = .err e) := by
  intro customTy ptr
  have h1 : evalPtrMetadata prof env .rawPtr ptr = .ok (.sliceLen n) := by
    cases prof <;> rfl
  have h2 : evalProjectFieldRaw env (.regular .shared) .rawPtr ptr 2 tailTy = .err .danglingInboundsOffset := rfl
  have h3 := dangling_wrapper_checkPtrValidity_err env .sharedRef trivial 2 n rfl
  exact ⟨h1, h2, h3⟩

/-- **Theorem 5 (`BoxDerefTransmute` (`HEAD`) vs Generic `Transmute` (`1.98`) Discriminator — `l14a` vs `l14b`):**
    Consider an unaligned `Box<Wrapper<[u8]>>` at odd address `2 * q + 1` (`≠ 0`, required alignment `2`):
    1. Under `v198LegacyTransmute`, `evalBoxRawDeref` (`&raw const (*b)`) **succeeds** (`l14a`), silently
       eliding alignment UB because `ElaborateBoxDerefs` stops at `NonNull` + generic `Transmute`.
    2. Under `vHeadBoxDerefTransmute`, `evalBoxRawDeref` **fails** (`BoxDerefTransmute` enforces
       `Box<T>` dereference validity).
    3. Reborrowing as `&(*b)` (`l14b`) **always fails** in both profiles. -/
theorem boxDeref_unaligned_legacy198_elides_vs_head_catches (env : MemEnv) (q n : Nat) :
    let customTy : CustomDstTy := .adt 1 none 3 1 2 (.adt 2 none 2 1 2 (.slice (.sized 10 1 0)))
    let b : WidePtr := ⟨⟨2 * q + 1, .none⟩, .sliceLen n, customTy⟩
    evalBoxRawDeref .v198LegacyTransmute env b = .ok b ∧
    (∃ e₁ : SemError, evalBoxRawDeref .vHeadBoxDerefTransmute env b = .err e₁) ∧
    (∃ e₂ : SemError, evalBoxRefReborrow env b = .err e₂) := by
  intro customTy b
  have hnz : Nat.beq (2 * q + 1) 0 = false := rfl
  have h1 : evalBoxRawDeref .v198LegacyTransmute env b = .ok b := by
    change (match Nat.beq (2 * q + 1) 0 with
            | true => EvalRes.err .nullReference
            | false =>
              match metaValidForTy env.vtables customTy (.sliceLen n) with
              | false => EvalRes.err .invalidOrForgedVtable
              | true => EvalRes.ok b) = .ok b
    rw [hnz]
    rfl
  have hfailBox := dangling_wrapper_checkPtrValidity_err env .boxPtr trivial (2 * q + 1) n rfl
  have hfailRef := dangling_wrapper_checkPtrValidity_err env .sharedRef trivial (2 * q + 1) n rfl
  have h2 : ∃ e₁ : SemError, evalBoxRawDeref .vHeadBoxDerefTransmute env b = .err e₁ := by
    rcases hfailBox with ⟨e, he⟩
    refine ⟨e, ?_⟩
    unfold evalBoxRawDeref
    change (match checkPtrValidity env .boxPtr b with | EvalRes.err (e : SemError) => EvalRes.err e | EvalRes.ok () => EvalRes.ok b) = EvalRes.err e
    rw [he]
  have h3 : ∃ e₂ : SemError, evalBoxRefReborrow env b = .err e₂ := by
    rcases hfailRef with ⟨e, he⟩
    refine ⟨e, ?_⟩
    unfold evalBoxRefReborrow
    change (match checkPtrValidity env .sharedRef b with | EvalRes.err (e : SemError) => EvalRes.err e | EvalRes.ok () => EvalRes.ok b) = EvalRes.err e
    rw [he]
  exact ⟨h1, h2, h3⟩

/-- **Theorem 6 (`FakeForPtrMetadata` Preserves Mutable Backing Across Interleaving `&mut` Calls — `l06`):**
    Evaluating `&raw const (fake) (*wu).inner.tail` for slice bounds checking preserves `wu.ptrMeta` and
    does not require invalidating `rec.writable` under Stacked/Tree Borrows. -/
theorem fakeForPtrMetadata_preserves_meta_without_mut_conflict
    (prof : CompilerVersionProfile) (env : MemEnv) (p : WidePtr) (off : Nat) (tailTy : CustomDstTy)
    (hp : checkPtrValidity env .mutRef p = .ok ())
    (hm : metaValidForTy env.vtables tailTy p.ptrMeta = true) :
    ∃ p', evalProjectFieldRaw env .fakeForPtrMetadata .mutRef p off tailTy = .ok p' ∧
          evalPtrMetadata prof env .rawPtr p' = .ok p.ptrMeta := by
  unfold evalProjectFieldRaw
  cases Nat.beq off 0 with
  | true =>
    refine ⟨⟨p.data, p.ptrMeta, tailTy⟩, rfl, ?_⟩
    unfold evalPtrMetadata
    cases prof with
    | v198LegacyTransmute => rw [hm]
    | vHeadBoxDerefTransmute =>
      unfold checkPtrValidity
      rw [hm]
  | false =>
    rw [hp]
    refine ⟨⟨⟨p.data.addr + off, p.data.prov⟩, p.ptrMeta, tailTy⟩, rfl, ?_⟩
    unfold evalPtrMetadata
    cases prof with
    | v198LegacyTransmute => rw [hm]
    | vHeadBoxDerefTransmute =>
      unfold checkPtrValidity
      rw [hm]

/-! ## 6. `GVN` `UnOp::PtrMetadata` Folding Asymmetry & Generalized Struct-Tail Soundness -/

/-- Projection elements appearing in `Value::Address` inside `rustc_mir_transform/src/gvn.rs`. -/
inductive MirPlaceProj where
  | field (idx : Nat) (byteOffset : Nat) (projTy : CustomDstTy)

/-- Symbolic GVN value representation mirroring `rustc_mir_transform/src/gvn.rs`:
    `Constant`, `RawPtr { pointer, metadata }`, `Cast { kind, value }`, and `Address { place, projection }`. -/
inductive MirSymVal where
  | constMeta (m : MetaVal)
  | rawPtrVal (pointee : CustomDstTy) (data : ThinPtr) (metaVal : MirSymVal)
  | castUnsize (srcTy dstTy : CustomDstTy) (inner : MirSymVal)
  | castPtrToPtr (srcTy dstTy : CustomDstTy) (inner : MirSymVal)
  | castBoxDerefTransmute (srcBoxTy dstPtrTy : CustomDstTy) (inner : MirSymVal)
  | addressOf (base : MirSymVal) (projs : List MirPlaceProj)
  | validPtr (p : WidePtr)
  | rawDanglingPtr (p : WidePtr)

/-- Extract the top-level target pointee type associated with a `MirSymVal`, if known. -/
noncomputable def symValPointee : MirSymVal → Option CustomDstTy
  | .rawPtrVal pt _ _ => some pt
  | .castUnsize _ dst _ => some dst
  | .castPtrToPtr _ dst _ => some dst
  | .castBoxDerefTransmute _ dst _ => some dst
  | .validPtr p => some p.pointee
  | .rawDanglingPtr p => some p.pointee
  | .addressOf base projs =>
    match projs.getLast? with
    | some (.field _ _ ty) => some ty
    | none =>
      match base with
      | .rawPtrVal pt _ _ => some pt
      | .castUnsize _ dst _ => some dst
      | .castPtrToPtr _ dst _ => some dst
      | .castBoxDerefTransmute _ dst _ => some dst
      | .validPtr p => some p.pointee
      | .rawDanglingPtr p => some p.pointee
      | _ => none
  | .constMeta _ => none

/-- `pointers_have_same_metadata` (`gvn.rs:1328`): checks whether `Cast(PtrToPtr)` between
    `t₁` and `t₂` preserves pointee metadata. -/
noncomputable def pointersHaveSameMetadata (t₁ t₂ : CustomDstTy) : Bool :=
  match expectedMetaShape t₁, expectedMetaShape t₂ with
  | .unitShape, .unitShape => true
  | .usizeShape, .usizeShape => CustomDstTy.beq (structTail t₁) (structTail t₂)
  | .vtableShape a, .vtableShape b => Nat.beq a b
  | _, _ => false

theorem pointersHaveSameMetadata_valid_preserves {vtables : List VtableEntry}
    {t₁ t₂ : CustomDstTy} {m : MetaVal}
    (hsame : pointersHaveSameMetadata t₁ t₂ = true)
    (hm : metaValidForTy vtables t₁ m = true) :
    metaValidForTy vtables t₂ m = true := by
  unfold pointersHaveSameMetadata at hsame
  unfold metaValidForTy at hm ⊢
  cases h₁ : expectedMetaShape t₁ with
  | unitShape =>
    cases h₂ : expectedMetaShape t₂ with
    | unitShape => rw [h₁] at hm; exact hm
    | usizeShape => rw [h₁, h₂] at hsame; exact Bool.noConfusion hsame
    | vtableShape _ => rw [h₁, h₂] at hsame; exact Bool.noConfusion hsame
  | usizeShape =>
    cases h₂ : expectedMetaShape t₂ with
    | unitShape => rw [h₁, h₂] at hsame; exact Bool.noConfusion hsame
    | usizeShape => rw [h₁] at hm; exact hm
    | vtableShape _ => rw [h₁, h₂] at hsame; exact Bool.noConfusion hsame
  | vtableShape a =>
    cases h₂ : expectedMetaShape t₂ with
    | unitShape => rw [h₁, h₂] at hsame; exact Bool.noConfusion hsame
    | usizeShape => rw [h₁, h₂] at hsame; exact Bool.noConfusion hsame
    | vtableShape b =>
      rw [h₁] at hm
      rw [h₁, h₂] at hsame
      have heq := Nat.eq_of_beq_eq_true hsame
      rw [← heq]
      exact hm

/-- Exact model of `GVN::simplify_unary`'s peeling loop (`gvn.rs:1310-1345`):
    - Peels `Cast(PtrToPtr)` whenever `pointersHaveSameMetadata src dst = true`.
    - Peels `Address { base, projection }` **ONLY if `projection.isEmpty`** (`[]`), refusing
      to cross non-empty `.field` projections such as `&raw const (fake) (*wu).inner.tail`. -/
noncomputable def stockGvnPeel : MirSymVal → MirSymVal
  | .castPtrToPtr src dst inner =>
    match pointersHaveSameMetadata src dst with
    | true => stockGvnPeel inner
    | false => .castPtrToPtr src dst inner
  | .addressOf base [] => stockGvnPeel base
  | other => other

/-- Exact model of `GVN::simplify_unary`'s `UnOp::PtrMetadata` matcher (`gvn.rs:1357-1375`):
    1. Folds `Value::RawPtr { metadata, .. } => metadata` unconditionally (even for custom DSTs).
    2. Folds `Value::Cast { kind: Unsize, .. }` **ONLY** when `from` is `ty::Array(_, len)` and
       `to` is `ty::Slice(..)`, leaving nested struct-tail `Unsize` unfolded. -/
noncomputable def stockGvnSimplifyPtrMetadata (v : MirSymVal) : Option MirSymVal :=
  match stockGvnPeel v with
  | .rawPtrVal _ _ metaV => some metaV
  | .castUnsize (.array _ len) (.slice _) _ => some (.constMeta (.sliceLen len))
  | _ => none

/-- Extended recursive struct-tail GVN simplification for `UnOp::PtrMetadata`:
    - Retains `stockGvnSimplifyPtrMetadata` rules (`RawPtr` and `[T; N] -> [T]`), AND
    - Descends arbitrary nested wrapper ADTs via `unsizeRel` + `unsizeMetadata` whenever
      `structTail src = .array _ len` and `unsizeRel vtables src dst = true`. -/
noncomputable def extGvnUnsizeSimplify (vtables : List VtableEntry) (v : MirSymVal) : Option MirSymVal :=
  match stockGvnPeel v with
  | .rawPtrVal _ _ metaV => some metaV
  | .castUnsize src dst _ =>
    match unsizeRel vtables src dst with
    | false => none
    | true =>
      match structTail src with
      | .array _ _ =>
        match unsizeMetadata src dst with
        | some m => some (.constMeta m)
        | none => none
      | _ => none
  | _ => none

/-- Check that every field projection step down `projs` projects cleanly along an ADT tail chain. -/
noncomputable def projChainPreservesMeta : CustomDstTy → List MirPlaceProj → Bool
  | _, [] => true
  | .adt _ _ _ _ _ tail, (.field _ _ projTy) :: rest =>
    boolAnd (CustomDstTy.beq tail projTy) (projChainPreservesMeta projTy rest)
  | _, _ => false

/-- Experimental tail-field peeling helper (`&raw const (fake) (*p).tail`) highlighting why
    non-empty projections require live-allocation / no-`Inbounds`-UB side conditions. -/
noncomputable def peelUnsafeTailFieldProjs : MirSymVal → Option MirSymVal
  | .addressOf base projs =>
    match symValPointee base with
    | none => none
    | some baseTy =>
      match projChainPreservesMeta baseTy projs with
      | true => peelUnsafeTailFieldProjs base
      | false => none
  | .castPtrToPtr src dst inner =>
    match pointersHaveSameMetadata src dst with
    | true => peelUnsafeTailFieldProjs inner
    | false => none
  | other => some other

/-- Structurally recursive field-projection evaluator (`evalSymVal` delegates here so it remains
    strictly structural with zero well-founded recursion artifacts). -/
noncomputable def evalProjectChain (env : MemEnv) (cat : PtrCategory) (p : WidePtr) :
    List MirPlaceProj → EvalRes WidePtr
  | [] => .ok p
  | .field _ off fTy :: rest =>
    match evalProjectFieldRaw env (.regular .shared) cat p off fTy with
    | .err e => .err e
    | .ok p' => evalProjectChain env .rawPtr p' rest

/-- Operational evaluator for `MirSymVal` (mirrors MIR `Rvalue` execution sequentially). -/
noncomputable def evalSymVal (prof : CompilerVersionProfile) (env : MemEnv) : MirSymVal → EvalRes WidePtr
  | .constMeta _ => .err .unsupportedOp
  | .validPtr p => .ok p
  | .rawDanglingPtr p => .ok p
  | .rawPtrVal pt d (.constMeta m) => evalAggregateRawPtr env pt d m
  | .rawPtrVal _ _ _ => .err .unsupportedOp
  | .castUnsize src dst inner =>
    match evalSymVal prof env inner with
    | .err e => .err e
    | .ok p =>
      match CustomDstTy.beq p.pointee src with
      | false => .err .unsupportedOp
      | true => evalUnsizeCast env dst p
  | .castPtrToPtr src dst inner =>
    match evalSymVal prof env inner with
    | .err e => .err e
    | .ok p =>
      match pointersHaveSameMetadata src dst with
      | false => .err .unsupportedOp
      | true =>
        match CustomDstTy.beq p.pointee src with
        | false => .err .unsupportedOp
        | true => .ok { data := p.data, ptrMeta := p.ptrMeta, pointee := dst }
  | .castBoxDerefTransmute _ dst inner =>
    match evalSymVal prof env inner with
    | .err e => .err e
    | .ok b =>
      match evalBoxRawDeref prof env b with
      | .err e => .err e
      | .ok b' => .ok { data := b'.data, ptrMeta := b'.ptrMeta, pointee := dst }
  | .addressOf base [] => evalSymVal prof env base
  | .addressOf base projs =>
    match evalSymVal prof env base with
    | .err e => .err e
    | .ok p =>
      let cat := match base with | .validPtr _ => .sharedRef | _ => .rawPtr
      evalProjectChain env cat p projs

/-- **Theorem 7 (`stockGvnSimplifyPtrMetadata` Folding Asymmetry):**
    (a) On `&[T; N] -> &[T]`, `stockGvnSimplifyPtrMetadata` folds to `constMeta (.sliceLen N)`.
    (b) On `&ADT<..., srcTail> -> &ADT<..., dstTail>` (any custom DST of depth ≥ 1, such as
        `&Wrapper<[u8; 3]> -> &Wrapper<[u8]>`), `stockGvnSimplifyPtrMetadata` ALWAYS returns `none`.
    (c) On `*const Wrapper<[u8]> from (data, constMeta (.sliceLen 9))`, `stockGvnSimplifyPtrMetadata`
        DOES fold to `constMeta (.sliceLen 9)` directly (`probe_d`), yet blocks
        `&raw const (fake) (*wu).inner.tail` when the `addressOf` projection list is non-empty! -/
theorem stockGvn_folding_asymmetry
    (elem : CustomDstTy) (n : Nat) (inner : MirSymVal)
    (id₁ : Nat) (pk : Option Nat) (ps₁ pa₁ to₁ : Nat) (srcTail dstTail : CustomDstTy)
    (id₂ : Nat) (pk₂ : Option Nat) (ps₂ pa₂ to₂ : Nat)
    (custTy : CustomDstTy) (d : ThinPtr) (projHead : MirPlaceProj) (projRest : List MirPlaceProj) :
    stockGvnSimplifyPtrMetadata (.castUnsize (.array elem n) (.slice elem) inner) =
      some (.constMeta (.sliceLen n)) ∧
    stockGvnSimplifyPtrMetadata
      (.castUnsize (.adt id₁ pk ps₁ pa₁ to₁ srcTail) (.adt id₂ pk₂ ps₂ pa₂ to₂ dstTail) inner) =
      none ∧
    stockGvnSimplifyPtrMetadata (.rawPtrVal custTy d (.constMeta (.sliceLen 9))) =
      some (.constMeta (.sliceLen 9)) ∧
    stockGvnSimplifyPtrMetadata (.addressOf (.rawPtrVal custTy d (.constMeta (.sliceLen 9))) (projHead :: projRest)) =
      none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Strengthening lemma: `stockGvnPeel` preserves evaluated metadata AND transports
    metadata validity backward from the peeled node `w'` to the outer node `w`. -/
theorem stockGvnPeel_preserves_meta_and_valid {prof : CompilerVersionProfile} {env : MemEnv}
    {v : MirSymVal} {w : WidePtr}
    (heval : evalSymVal prof env v = .ok w) :
    ∃ w', evalSymVal prof env (stockGvnPeel v) = .ok w' ∧ w'.ptrMeta = w.ptrMeta ∧
          (metaValidForTy env.vtables w'.pointee w'.ptrMeta = true →
           metaValidForTy env.vtables w.pointee w.ptrMeta = true) := by
  induction v generalizing w with
  | castPtrToPtr src dst inner ih =>
    unfold evalSymVal at heval
    cases hinner : evalSymVal prof env inner with
    | err e => rw [hinner] at heval; cases heval
    | ok pi =>
      rw [hinner] at heval
      dsimp only at heval
      cases hsame : pointersHaveSameMetadata src dst with
      | false =>
        rw [hsame] at heval
        cases heval
      | true =>
        rw [hsame] at heval
        dsimp only at heval
        cases hty : CustomDstTy.beq pi.pointee src with
        | false =>
          rw [hty] at heval
          cases heval
        | true =>
          rw [hty] at heval
          dsimp only at heval
          injection heval with hw
          rw [← hw]
          unfold stockGvnPeel
          rw [hsame]
          rcases ih hinner with ⟨w', heval', hmeq, hvalid⟩
          refine ⟨w', heval', hmeq, ?_⟩
          intro hmw'
          have hmpi := hvalid hmw'
          have hpi_src : pi.pointee = src := CustomDstTy.eq_of_beq hty
          rw [hpi_src] at hmpi
          exact pointersHaveSameMetadata_valid_preserves hsame hmpi
  | addressOf base projs ih_base =>
    cases projs with
    | nil =>
      unfold evalSymVal at heval
      unfold stockGvnPeel
      exact ih_base heval
    | cons hd tl =>
      unfold stockGvnPeel
      exact ⟨w, heval, rfl, id⟩
  | _ =>
    unfold stockGvnPeel
    exact ⟨w, heval, rfl, id⟩

/-- **Theorem 8 (Soundness of Generalized Recursive Struct-Tail GVN `PtrMetadata` Folding):**
    Whenever `extGvnUnsizeSimplify` folds `PtrMetadata(v)` across arbitrarily deep nested custom-DST
    struct-tail unsizes (`Wrapper_1<...Wrapper_k<[T; N]>...>`) or `RawPtr` aggregates to `constMeta m`,
    and `v` evaluates cleanly to `w`, `evalPtrMetadata prof env .rawPtr w` equals `.ok m`! -/
theorem extGvnUnsizeSimplify_sound {prof : CompilerVersionProfile} {env : MemEnv}
    {v : MirSymVal} {m : MetaVal} {w : WidePtr}
    (hsimp : extGvnUnsizeSimplify env.vtables v = some (.constMeta m))
    (heval : evalSymVal prof env v = .ok w) :
    evalPtrMetadata prof env .rawPtr w = .ok m := by
  rcases stockGvnPeel_preserves_meta_and_valid heval with ⟨w', heval', hmeq, hvalid_up⟩
  unfold extGvnUnsizeSimplify at hsimp
  have hcheck_w' : metaValidForTy env.vtables w'.pointee w'.ptrMeta = true ∧ w'.ptrMeta = m := by
    cases hpeel : stockGvnPeel v with
    | constMeta _ => rw [hpeel] at hsimp; cases hsimp
    | castPtrToPtr _ _ _ => rw [hpeel] at hsimp; cases hsimp
    | castBoxDerefTransmute _ _ _ => rw [hpeel] at hsimp; cases hsimp
    | addressOf _ _ => rw [hpeel] at hsimp; cases hsimp
    | validPtr _ => rw [hpeel] at hsimp; cases hsimp
    | rawDanglingPtr _ => rw [hpeel] at hsimp; cases hsimp
    | rawPtrVal pt d metaNode =>
      rw [hpeel] at hsimp heval'
      dsimp only at hsimp heval'
      injection hsimp with hnode
      rw [hnode] at heval'
      unfold evalSymVal evalAggregateRawPtr at heval'
      cases hmv : metaValidForTy env.vtables pt m with
      | false =>
        rw [hmv] at heval'
        cases heval'
      | true =>
        rw [hmv] at heval'
        injection heval' with hw'
        rw [← hw']
        exact ⟨hmv, rfl⟩
    | castUnsize src dst inner =>
      rw [hpeel] at hsimp heval'
      dsimp only at hsimp heval'
      cases hrel : unsizeRel env.vtables src dst with
      | false => rw [hrel] at hsimp; cases hsimp
      | true =>
        rw [hrel] at hsimp
        dsimp only at hsimp
        cases hst : structTail src with
        | sized _ _ _ => rw [hst] at hsimp; cases hsimp
        | slice _ => rw [hst] at hsimp; cases hsimp
        | dynTrait _ => rw [hst] at hsimp; cases hsimp
        | adt _ _ _ _ _ _ => rw [hst] at hsimp; cases hsimp
        | array elem len =>
          rw [hst] at hsimp
          dsimp only at hsimp
          cases hum : unsizeMetadata src dst with
          | none => rw [hum] at hsimp; cases hsimp
          | some mm =>
            rw [hum] at hsimp
            injection hsimp with hmm
            injection hmm with hm_eq
            subst hm_eq
            unfold evalSymVal at heval'
            cases hi : evalSymVal prof env inner with
            | err _ => rw [hi] at heval'; cases heval'
            | ok pi =>
              rw [hi] at heval'
              dsimp only at heval'
              cases hpt : CustomDstTy.beq pi.pointee src with
              | false => rw [hpt] at heval'; cases heval'
              | true =>
                rw [hpt] at heval'
                dsimp only at heval'
                unfold evalUnsizeCast at heval'
                rw [CustomDstTy.eq_of_beq hpt, hrel, hum] at heval'
                injection heval' with hw'
                rw [← hw']
                exact ⟨unsize_produces_valid_meta hrel hum, rfl⟩
  rcases hcheck_w' with ⟨hmw', hmeq'⟩
  have hmw : metaValidForTy env.vtables w.pointee w.ptrMeta = true := hvalid_up hmw'
  have hwm : w.ptrMeta = m := hmeq.symm.trans hmeq'
  unfold evalPtrMetadata
  cases prof with
  | v198LegacyTransmute =>
    rw [hmw, hwm]
  | vHeadBoxDerefTransmute =>
    unfold checkPtrValidity
    rw [hmw, hwm]

/-- **Theorem 9 (Sharp Side-Condition Boundary for Non-Empty Tail Field Projection Peeling):**
    Blindly peeling non-empty field projections (`&raw const (*p).inner.tail`, `fieldOffset = 2`) on a
    dangling raw pointer `p = ⟨⟨2, .none⟩, .sliceLen 3, Wrapper<[u8]>⟩` would fabricate `const 3_usize`,
    whereas operational MIR evaluation FAILS with `SemError.danglingInboundsOffset` (`l12`)! -/
theorem peelProj_unsound_without_live_ref_side_condition (prof : CompilerVersionProfile) (env : MemEnv) :
    let innerTy : CustomDstTy := .adt 2 none 2 1 2 (.slice (.sized 10 1 0))
    let wrapperTy : CustomDstTy := .adt 1 none 3 1 2 innerTy
    let danglingP : WidePtr := ⟨⟨2, .none⟩, .sliceLen 3, wrapperTy⟩
    let expr : MirSymVal :=
      .addressOf (.rawDanglingPtr danglingP) [.field 1 2 innerTy, .field 1 2 (.slice (.sized 10 1 0))]
    peelUnsafeTailFieldProjs expr = some (.rawDanglingPtr danglingP) ∧
    evalSymVal prof env expr = .err .danglingInboundsOffset := by
  exact ⟨rfl, rfl⟩

/-! ## 7. `rustc_codegen_ssa` `ScalarPair` Codegen (`rvalue.rs`, `operand.rs`) & Concrete Probe Verification -/

/-- `rustc_codegen_ssa` value representation (`OperandValue` in `operand.rs:745-865` & `rvalue.rs:725-842`):
    - `zeroSized`: unit `()` metadata (`PtrMetadata` on sized thin pointer).
    - `immediate data`: thin pointer `*const T` (`Aggregate(RawPtr, [data, ()])` collapses via `InstSimplify`).
    - `pair data meta`: wide pointer `ScalarPair` (`*const [T]`, `*const Wrapper<[u8]>`, `*const dyn Trait`). -/
inductive SsaOperandVal where
  | zeroSized
  | immediate (dataAddr : Nat)
  | pair (dataAddr : Nat) (metaScalar : Nat)

noncomputable def encodeMetaScalar : MetaVal → Nat
  | .unit => 0
  | .sliceLen n => n
  | .dynVtable vtId => vtId

/-- Lower `AggregateKind::RawPtr` in `rustc_codegen_ssa/src/mir/rvalue.rs:807-842`. -/
noncomputable def codegenAggregateRawPtr (ty : CustomDstTy) (dataAddr : Nat) (m : MetaVal) : SsaOperandVal :=
  match expectedMetaShape ty with
  | .unitShape => .immediate dataAddr
  | .usizeShape => .pair dataAddr (encodeMetaScalar m)
  | .vtableShape _ => .pair dataAddr (encodeMetaScalar m)

/-- Lower `UnOp::PtrMetadata` in `rustc_codegen_ssa/src/mir/rvalue.rs:725-734`:
    `if operand.layout.fields.count() > 1 { Scalar(pair.1) } else { ZeroSized }`. -/
noncomputable def codegenPtrMetadata : SsaOperandVal → SsaOperandVal
  | .pair _ metaScalar => .immediate metaScalar
  | .immediate _ => .zeroSized
  | .zeroSized => .zeroSized

/-- **Theorem 10 (`rustc_codegen_ssa` `ScalarPair` Codegen Round-Trip):**
    For any unsized target (`Slice` or `dyn Trait`, including custom-DST wrappers), extracting
    `codegenPtrMetadata (codegenAggregateRawPtr ty d m)` recovers `.immediate (encodeMetaScalar m)`,
    and for any sized thin target (`unitShape`), it produces `.zeroSized`. -/
theorem ssa_codegen_scalarPair_roundtrip (ty : CustomDstTy) (d : Nat) (m : MetaVal) :
    match expectedMetaShape ty with
    | .unitShape => codegenPtrMetadata (codegenAggregateRawPtr ty d m) = .zeroSized
    | .usizeShape => codegenPtrMetadata (codegenAggregateRawPtr ty d m) = .immediate (encodeMetaScalar m)
    | .vtableShape _ => codegenPtrMetadata (codegenAggregateRawPtr ty d m) = .immediate (encodeMetaScalar m) := by
  unfold codegenAggregateRawPtr codegenPtrMetadata
  cases expectedMetaShape ty <;> rfl

/-! ## 8. Kernel-Reduced (`rfl`) Empirical Probe & Litmus Verification Suite -/

/-- Exact types matching the live `rustc 1.98.0-nightly (14210df0e)` probe crate. -/
noncomputable def tyU8 : CustomDstTy := .sized 10 1 0
noncomputable def tyU32 : CustomDstTy := .sized 11 4 2
noncomputable def tyConcrete : CustomDstTy := .sized 12 16 3  -- `Concrete { a: u32, b: u64 }` -> size 16, align 8 (`2^3`)
noncomputable def tyArr4U32 : CustomDstTy := .array tyU32 4
noncomputable def tySliceU32 : CustomDstTy := .slice tyU32
noncomputable def tyDynSummarize : CustomDstTy := .dynTrait 1
noncomputable def tyInnerArr3 : CustomDstTy := .adt 2 none 2 1 2 (.array tyU8 3)
noncomputable def tyWrapperArr3 : CustomDstTy := .adt 1 none 3 1 2 tyInnerArr3
noncomputable def tyInnerSliceU8 : CustomDstTy := .adt 2 none 2 1 2 (.slice tyU8)
noncomputable def tyWrapperSliceU8 : CustomDstTy := .adt 1 none 3 1 2 tyInnerSliceU8

noncomputable def specimenVtables : List VtableEntry :=
  [ { vtableId := 12, traitId := 1, dynSize := 16, dynAlignLog2 := 3, isValid := true } ]

noncomputable def specimenLiveAlloc : AllocRecord :=
  { allocId := 1, live := true, baseAddr := 4096, allocSize := 64,
    writable := true, sbReadable := true, tbReadable := true }

noncomputable def specimenFreedAlloc : AllocRecord :=
  { allocId := 2, live := false, baseAddr := 8192, allocSize := 64,
    writable := false, sbReadable := false, tbReadable := false }

noncomputable def specimenEnv : MemEnv :=
  { isizeMax := 9223372036854775807
  , allocs := [specimenLiveAlloc, specimenFreedAlloc]
  , vtables := specimenVtables }

/-- Probe A (`&[u32; 4] -> &[u32]`): `GVN` folds `PtrMetadata` to `4_usize`; `extGvn` agrees. -/
theorem specimen_probe_a_folded :
    stockGvnSimplifyPtrMetadata (.castUnsize tyArr4U32 tySliceU32 (.validPtr ⟨⟨4096, .alloc 1⟩, .unit, tyArr4U32⟩)) =
      some (.constMeta (.sliceLen 4)) ∧
    extGvnUnsizeSimplify specimenVtables (.castUnsize tyArr4U32 tySliceU32 (.validPtr ⟨⟨4096, .alloc 1⟩, .unit, tyArr4U32⟩)) =
      some (.constMeta (.sliceLen 4)) := ⟨rfl, rfl⟩

/-- Probe B (`Concrete -> dyn Summarize`): `sizeAndAlignOfDst` resolves `(16, 8)` via `vtableId = 12`. -/
theorem specimen_probe_b_dyn_metadata :
    sizeAndAlignOfDst specimenVtables tyDynSummarize (.dynVtable 12) = some (16, 8) ∧
    codegenPtrMetadata (codegenAggregateRawPtr tyDynSummarize 4096 (.dynVtable 12)) = .immediate 12 :=
  ⟨rfl, rfl⟩

/-- Probe C/E (`Wrapper<[u8]>`): exact size `8`, align `2` at `len = 3`; `Inner` aligned offset = `2`;
    stock `GVN` leaves `Unsize` unfolded (`none`), whereas generalized struct-tail `GVN` folds to `3`! -/
theorem specimen_probe_c_e_layout_and_gvn_asymmetry :
    sizeAndAlignOfDst specimenVtables tyWrapperSliceU8 (.sliceLen 3) = some (8, 2) ∧
    projectTailOffset specimenVtables tyWrapperSliceU8 (.sliceLen 3) = some 2 ∧
    stockGvnSimplifyPtrMetadata (.castUnsize tyWrapperArr3 tyWrapperSliceU8 (.validPtr ⟨⟨4096, .alloc 1⟩, .unit, tyWrapperArr3⟩)) =
      none ∧
    extGvnUnsizeSimplify specimenVtables (.castUnsize tyWrapperArr3 tyWrapperSliceU8 (.validPtr ⟨⟨4096, .alloc 1⟩, .unit, tyWrapperArr3⟩)) =
      some (.constMeta (.sliceLen 3)) := ⟨rfl, rfl, rfl, rfl⟩

/-- Probe D (`from_raw_parts` round-trip + custom-DST `RawPtr` GVN folding): exact kernel checks. -/
theorem specimen_probe_d_rawptr_roundtrip_and_const_meta :
    stockGvnSimplifyPtrMetadata (.rawPtrVal tyWrapperSliceU8 ⟨1, .none⟩ (.constMeta (.sliceLen 9))) =
      some (.constMeta (.sliceLen 9)) ∧
    evalAggregateRawPtr specimenEnv tySliceU32 ⟨0, .none⟩ (.sliceLen 17) =
      .ok ⟨⟨0, .none⟩, .sliceLen 17, tySliceU32⟩ ∧
    evalPtrMetadata .v198LegacyTransmute specimenEnv .rawPtr ⟨⟨0, .none⟩, .sliceLen 17, tySliceU32⟩ =
      .ok (.sliceLen 17) := ⟨rfl, rfl, rfl⟩

/-- Litmus matrix alignment checks (`l01..l14b` abstract verification against observed Miri outcomes):
    - `l01` null slice metadata passes
    - `l02` dangling unaligned `Wrapper<[u8]>` metadata passes
    - `l03` freed `Box<[u8]>` raw slice metadata passes
    - `l04` freed `Box<dyn Summarize>` raw metadata + size/align passes
    - `l05` oversized `usize::MAX` raw `[u64]` metadata passes
    - `l09` `&*null_slice` rejects with `.nullReference`
    - `l10` `&*freed_box` rejects with `.danglingUseAfterFree`
    - `l12` `&raw const (*p).inner` (`fieldOffset = 2`) on dangling `0x2` rejects with `.danglingInboundsOffset`
    - `l13` forged vtable in `from_raw_parts::<dyn Summarize>` rejects with `.invalidOrForgedVtable`
    - `l14a` vs `l14b` unaligned `Box` raw deref passes on `1.98` and rejects on `HEAD` and `&*b` -/
theorem specimen_litmus_matrix_exact :
    evalPtrMetadata .vHeadBoxDerefTransmute specimenEnv .rawPtr ⟨⟨0, .none⟩, .sliceLen 42, tySliceU32⟩ =
      .ok (.sliceLen 42) ∧
    evalPtrMetadata .vHeadBoxDerefTransmute specimenEnv .rawPtr ⟨⟨1, .none⟩, .sliceLen 99, tyWrapperSliceU8⟩ =
      .ok (.sliceLen 99) ∧
    evalPtrMetadata .vHeadBoxDerefTransmute specimenEnv .rawPtr ⟨⟨8192, .alloc 2⟩, .sliceLen 4, .slice tyU8⟩ =
      .ok (.sliceLen 4) ∧
    evalPtrMetadata .vHeadBoxDerefTransmute specimenEnv .rawPtr ⟨⟨8192, .alloc 2⟩, .dynVtable 12, tyDynSummarize⟩ =
      .ok (.dynVtable 12) ∧
    evalPtrMetadata .vHeadBoxDerefTransmute specimenEnv .rawPtr ⟨⟨8, .none⟩, .sliceLen 18446744073709551615, .slice (.sized 13 8 3)⟩ =
      .ok (.sliceLen 18446744073709551615) ∧
    checkPtrValidity specimenEnv .sharedRef ⟨⟨0, .none⟩, .sliceLen 4, tySliceU32⟩ =
      .err .nullReference ∧
    checkPtrValidity specimenEnv .sharedRef ⟨⟨8192, .alloc 2⟩, .sliceLen 4, .slice tyU8⟩ =
      .err .danglingUseAfterFree ∧
    evalProjectFieldRaw specimenEnv (.regular .shared) .rawPtr ⟨⟨2, .none⟩, .sliceLen 3, tyWrapperSliceU8⟩ 2 tyInnerSliceU8 =
      .err .danglingInboundsOffset ∧
    evalAggregateRawPtr specimenEnv tyDynSummarize ⟨0, .none⟩ (.dynVtable 9999) =
      .err .invalidOrForgedVtable ∧
    evalBoxRawDeref .v198LegacyTransmute specimenEnv ⟨⟨4097, .none⟩, .sliceLen 3, tyWrapperSliceU8⟩ =
      .ok ⟨⟨4097, .none⟩, .sliceLen 3, tyWrapperSliceU8⟩ ∧
    evalBoxRawDeref .vHeadBoxDerefTransmute specimenEnv ⟨⟨4097, .none⟩, .sliceLen 3, tyWrapperSliceU8⟩ =
      .err .unalignedPointer ∧
    evalBoxRefReborrow specimenEnv ⟨⟨4097, .none⟩, .sliceLen 3, tyWrapperSliceU8⟩ =
      .err .unalignedPointer :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end MirPtrMetadataGvnCustomDstAndRawPtrSoundness
