-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics

public section

namespace Anneal.MirTotal

open Trusted.MirAst Trusted.MirSemantics

/-!
# Total Computable MIR Operators, Layouts, and Memory Mirrors (`MirTotal.Ops`)

Provides total, LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`)
mirrors of all `MirTy`-equality-independent operations in
`Trusted.MirSemantics`—including scalar arithmetic, shifts, overflowing and
unchecked binary operators, integer casts, fieldless enum validation, layouts,
byte codecs, and indirect stack-memory reads/writes—together with unconditional
equational equivalence theorems (`*_eq`) against `Trusted.MirSemantics`.
-/

/-! ## Constructive `Bool`, `Nat`, `Int`, `BitVec`, and `List` Helpers -/

/-- Total computable equality on `Bool`. -/
@[expose] def boolBeqComp (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | true, false => false
  | false, true => false

/-- Agreement between `boolBeqComp` and `(a == b)`. -/
theorem boolBeqComp_eq (a b : Bool) : boolBeqComp a b = (a == b) := by
  cases a <;> cases b <;> rfl

/-- Total list indexing via `List.foldr` (`0` `noncomputable`). -/
@[expose] def compGetElem? {α : Type} (xs : List α) (idx : Nat) : Option α :=
  List.foldr
    (fun (x : α) (ih : Nat → Option α) (n : Nat) =>
      match n with
      | 0 => some x
      | k + 1 => ih k)
    (fun _ => none)
    xs idx

/-- Agreement between `compGetElem?` and `Trusted.MirSemantics.getElem?`. -/
theorem compGetElem?_eq {α : Type} (xs : List α) (idx : Nat) :
    compGetElem? xs idx = Trusted.MirSemantics.getElem? xs idx := by
  induction xs generalizing idx with
  | nil => rfl
  | cons _ _ ih =>
    cases idx with
    | zero => rfl
    | succ k => exact ih k

@[expose] def compSetElemAux {α : Type} (xs : List α) :
    List α × (Nat → α → Option (List α)) :=
  List.foldr
    (fun (x : α) (acc : List α × (Nat → α → Option (List α))) =>
      (x :: acc.1,
       fun (n : Nat) (v : α) =>
         match n with
         | 0 => some (v :: acc.1)
         | k + 1 =>
           match acc.2 k v with
           | some xs' => some (x :: xs')
           | none => none))
    ([], fun _ _ => none)
    xs

/-- Total list update via `List.foldr` (`0` `noncomputable`). -/
@[expose] def compSetElem? {α : Type} (xs : List α) (idx : Nat) (val : α) :
    Option (List α) :=
  (compSetElemAux xs).2 idx val

private theorem compSetElemAux_fst {α : Type} (xs : List α) :
    (compSetElemAux xs).1 = xs := by
  induction xs with
  | nil => rfl
  | cons x _ ih => exact congrArg (List.cons x) ih

/-- Agreement between `compSetElem?` and `Trusted.MirSemantics.setElem?`. -/
theorem compSetElem?_eq {α : Type} (xs : List α) (idx : Nat) (val : α) :
    compSetElem? xs idx val = Trusted.MirSemantics.setElem? xs idx val := by
  induction xs generalizing idx with
  | nil => rfl
  | cons x tl ih =>
    cases idx with
    | zero =>
      change some (val :: (compSetElemAux tl).1) = some (val :: tl)
      rw [compSetElemAux_fst tl]
    | succ k =>
      change (match compSetElem? tl k val with
        | some xs' => some (x :: xs')
        | none => none) =
        (match Trusted.MirSemantics.setElem? tl k val with
        | some xs' => some (x :: xs')
        | none => none)
      rw [ih k]

/-- Pointwise congruence for `List.all`. -/
theorem listAll_congr {α : Type} {f g : α → Bool} (xs : List α)
    (h : ∀ x, f x = g x) :
    xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    change (f x && tl.all f) = (g x && tl.all g)
    rw [h x, ih]

/-- Pointwise congruence for `List.any`. -/
theorem listAny_congr {α : Type} {f g : α → Bool} (xs : List α)
    (h : ∀ x, f x = g x) :
    xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    change (f x || tl.any f) = (g x || tl.any g)
    rw [h x, ih]

private theorem decCasesBool_eq {p : Prop} (b : Bool) (d : Decidable p)
    (hIff : b = true ↔ p) :
    b = @decide p d := by
  cases d with
  | isFalse hNot =>
    cases hb : b with
    | false => exact (@decide_eq_false p (.isFalse hNot) hNot).symm
    | true => exact False.elim (hNot (hIff.mp hb))
  | isTrue hYes =>
    rw [@decide_eq_true p (.isTrue hYes) hYes]
    exact hIff.mpr hYes

/-- Total computable equality on `Int`. -/
@[expose] def intBeqComp (a b : Int) : Bool :=
  match a, b with
  | .ofNat m, .ofNat n => Nat.beq m n
  | .negSucc m, .negSucc n => Nat.beq m n
  | _, _ => false

/-- Logical equivalence `intBeqComp a b = true ↔ a = b`. -/
theorem intBeqComp_iff (a b : Int) : intBeqComp a b = true ↔ a = b := by
  constructor
  · intro h
    cases a with
    | ofNat m =>
      cases b with
      | ofNat n => exact congrArg Int.ofNat (Nat.eq_of_beq_eq_true h)
      | negSucc _ => cases h
    | negSucc m =>
      cases b with
      | ofNat _ => cases h
      | negSucc n => exact congrArg Int.negSucc (Nat.eq_of_beq_eq_true h)
  · intro h
    subst h
    cases a with
    | ofNat m => exact Nat.beq_refl m
    | negSucc m => exact Nat.beq_refl m

/-- Agreement between `intBeqComp` and `(a == b)`. -/
theorem intBeqComp_eq_beq (a b : Int) : intBeqComp a b = (a == b) :=
  decCasesBool_eq (intBeqComp a b) (Int.decEq a b) (intBeqComp_iff a b)

/-- Agreement between `!intBeqComp` and `(a != b)`. -/
theorem intBneComp_eq (a b : Int) : (!intBeqComp a b) = (a != b) := by
  unfold bne
  rw [intBeqComp_eq_beq]

/-- Total computable `≤` comparison on `Int`. -/
@[expose] def intBleComp (a b : Int) : Bool :=
  match a, b with
  | .ofNat m, .ofNat n => Nat.ble m n
  | .ofNat _, .negSucc _ => false
  | .negSucc _, .ofNat _ => true
  | .negSucc m, .negSucc n => Nat.ble n m

/-- Total computable `<` comparison on `Int`. -/
@[expose] def intBltComp (a b : Int) : Bool :=
  intBleComp (a + 1) b

private theorem not_int_nonNeg_negSucc (k : Nat) : ¬ Int.NonNeg (Int.negSucc k) :=
  fun h => nomatch h

private theorem int_subNatNat_nonNeg_iff (x y : Nat) :
    Int.NonNeg (Int.subNatNat x y) ↔ y ≤ x := by
  unfold Int.subNatNat
  cases hSub : y - x with
  | zero =>
    constructor
    · intro _; exact Nat.le_of_sub_eq_zero hSub
    · intro _; constructor
  | succ k =>
    constructor
    · intro hNn; exact False.elim (not_int_nonNeg_negSucc k hNn)
    · intro hLe
      have hZ : y - x = 0 := Nat.sub_eq_zero_of_le hLe
      rw [hSub] at hZ
      cases hZ

/-- Logical equivalence `intBleComp a b = true ↔ a ≤ b`. -/
theorem intBleComp_iff (a b : Int) : intBleComp a b = true ↔ a ≤ b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      cases m with
      | zero =>
        constructor
        · intro _; exact Int.NonNeg.mk n
        · intro _; rfl
      | succ m' =>
        constructor
        · intro hB
          exact (int_subNatNat_nonNeg_iff n (m' + 1)).mpr (Nat.le_of_ble_eq_true hB)
        · intro hLe
          exact Nat.ble_eq.mpr ((int_subNatNat_nonNeg_iff n (m' + 1)).mp hLe)
    | negSucc n =>
      constructor
      · intro hB; cases hB
      · intro hLe
        cases m with
        | zero => exact False.elim (not_int_nonNeg_negSucc n hLe)
        | succ _ => exact False.elim (not_int_nonNeg_negSucc _ hLe)
  | negSucc m =>
    cases b with
    | ofNat n =>
      constructor
      · intro _; exact Int.NonNeg.mk (n + (m + 1))
      · intro _; rfl
    | negSucc n =>
      constructor
      · intro hB
        exact (int_subNatNat_nonNeg_iff (m + 1) (n + 1)).mpr
          (Nat.succ_le_succ (Nat.le_of_ble_eq_true hB))
      · intro hLe
        exact Nat.ble_eq.mpr
          (Nat.le_of_succ_le_succ ((int_subNatNat_nonNeg_iff (m + 1) (n + 1)).mp hLe))

/-- Agreement between `intBleComp` and `decide (a ≤ b)`. -/
theorem intBleComp_eq_dec (a b : Int) :
    intBleComp a b = decide (a ≤ b) :=
  decCasesBool_eq (intBleComp a b) inferInstance (intBleComp_iff a b)

/-- Agreement between `intBltComp` and `decide (a < b)`. -/
theorem intBltComp_eq_dec (a b : Int) :
    intBltComp a b = decide (a < b) :=
  decCasesBool_eq (intBltComp a b) inferInstance (intBleComp_iff (a + 1) b)

/-- Agreement between `intBleComp b a` and `decide (a ≥ b)`. -/
theorem intBgeComp_eq_dec (a b : Int) :
    intBleComp b a = decide (a ≥ b) :=
  decCasesBool_eq (intBleComp b a) inferInstance (intBleComp_iff b a)

/-- Agreement between `intBltComp b a` and `decide (a > b)`. -/
theorem intBgtComp_eq_dec (a b : Int) :
    intBltComp b a = decide (a > b) :=
  decCasesBool_eq (intBltComp b a) inferInstance (intBleComp_iff (b + 1) a)

/-- Total computable equality on `BitVec 128`. -/
@[expose] def bv128BeqComp (x y : BitVec 128) : Bool :=
  Nat.beq x.toNat y.toNat

/-- Logical equivalence `bv128BeqComp x y = true ↔ x = y`. -/
theorem bv128BeqComp_iff (x y : BitVec 128) : bv128BeqComp x y = true ↔ x = y := by
  constructor
  · intro h
    have hNat : x.toNat = y.toNat := Nat.eq_of_beq_eq_true h
    cases x with
    | ofFin fx =>
      cases y with
      | ofFin fy =>
        cases fx with
        | mk vx _ =>
          cases fy with
          | mk vy _ =>
            change vx = vy at hNat
            subst hNat
            rfl
  · intro h
    subst h
    exact Nat.beq_refl x.toNat

/-- Agreement between `bv128BeqComp` and `(x == y)`. -/
theorem bv128BeqComp_eq_beq (x y : BitVec 128) : bv128BeqComp x y = (x == y) :=
  decCasesBool_eq (bv128BeqComp x y) (BitVec.decEq x y) (bv128BeqComp_iff x y)

/-- Agreement between `!bv128BeqComp` and `(x != y)`. -/
theorem bv128BneComp_eq (x y : BitVec 128) : (!bv128BeqComp x y) = (x != y) := by
  unfold bne
  rw [bv128BeqComp_eq_beq]

/-- Total computable equality on `UInt8`. -/
@[expose] def uint8BeqComp (x y : UInt8) : Bool :=
  Nat.beq x.toNat y.toNat

/-- Logical equivalence `uint8BeqComp x y = true ↔ x = y`. -/
theorem uint8BeqComp_iff (x y : UInt8) : uint8BeqComp x y = true ↔ x = y := by
  constructor
  · intro h
    have hNat : x.toNat = y.toNat := Nat.eq_of_beq_eq_true h
    cases x with
    | ofBitVec bx =>
      cases y with
      | ofBitVec by_ =>
        cases bx with
        | ofFin fx =>
          cases by_ with
          | ofFin fy =>
            cases fx with
            | mk vx _ =>
              cases fy with
              | mk vy _ =>
                change vx = vy at hNat
                subst hNat
                rfl
  · intro h
    subst h
    exact Nat.beq_refl x.toNat

/-- Agreement between `uint8BeqComp` and `(x == y)`. -/
theorem uint8BeqComp_eq_beq (x y : UInt8) : uint8BeqComp x y = (x == y) :=
  decCasesBool_eq (uint8BeqComp x y) (UInt8.decEq x y) (uint8BeqComp_iff x y)

/-! ## Computable Type-Metadata, Scalar, Layout, Codec, and Memory Mirrors -/

/-- Computable mirror of `IntWidth.byteSize`. -/
@[expose] def byteSizeComp (w : IntWidth) : Nat :=
  match w with
  | .i8 => 1
  | .i16 => 2
  | .i32 => 4
  | .i64 => 8
  | .i128 => 16
  | .isize => 8

/-- Agreement between `byteSizeComp` and `IntWidth.byteSize`. -/
theorem byteSizeComp_eq (w : IntWidth) : byteSizeComp w = w.byteSize := by
  cases w <;> rfl

/-- Computable mirror of `IntWidth.bitWidth`. -/
@[expose] def bitWidthComp (w : IntWidth) : Nat := byteSizeComp w * 8

/-- Agreement between `bitWidthComp` and `IntWidth.bitWidth`. -/
theorem bitWidthComp_eq (w : IntWidth) : bitWidthComp w = w.bitWidth := by
  unfold bitWidthComp IntWidth.bitWidth
  rw [byteSizeComp_eq]

/-- Computable mirror of `IntWidth.beq`. -/
@[expose] def intWidthBeqComp (a b : IntWidth) : Bool :=
  match a with
  | .i8 => match b with | .i8 => true | .i16 | .i32 | .i64 | .i128 | .isize => false
  | .i16 => match b with | .i16 => true | .i8 | .i32 | .i64 | .i128 | .isize => false
  | .i32 => match b with | .i32 => true | .i8 | .i16 | .i64 | .i128 | .isize => false
  | .i64 => match b with | .i64 => true | .i8 | .i16 | .i32 | .i128 | .isize => false
  | .i128 => match b with | .i128 => true | .i8 | .i16 | .i32 | .i64 | .isize => false
  | .isize => match b with | .isize => true | .i8 | .i16 | .i32 | .i64 | .i128 => false

/-- Agreement between `intWidthBeqComp` and `IntWidth.beq`. -/
theorem intWidthBeqComp_eq (a b : IntWidth) : intWidthBeqComp a b = IntWidth.beq a b := by
  cases a <;> cases b <;> rfl

/-- Computable mirror of `Mutability.beq`. -/
@[expose] def mutabilityBeqComp (a b : Mutability) : Bool :=
  match a with
  | .shared => match b with | .shared => true | .mut => false
  | .mut => match b with | .shared => false | .mut => true

/-- Agreement between `mutabilityBeqComp` and `Mutability.beq`. -/
theorem mutabilityBeqComp_eq (a b : Mutability) :
    mutabilityBeqComp a b = Mutability.beq a b := by
  cases a <;> cases b <;> rfl

/-- Computable mirror of `Trusted.MirAst.natListBeq`. -/
@[expose] def natListBeqComp (xs ys : List Nat) : Bool :=
  List.foldr
    (fun (x : Nat) (ih : List Nat → Bool) (bs : List Nat) =>
      match bs with
      | [] => false
      | y :: tl => Nat.beq x y && ih tl)
    (fun bs => match bs with | [] => true | _ :: _ => false)
    xs ys

/-- Agreement between `natListBeqComp` and `natListBeq`. -/
theorem natListBeqComp_eq (xs ys : List Nat) : natListBeqComp xs ys = natListBeq xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x _ ih =>
    cases ys with
    | nil => rfl
    | cons y tl =>
      change (Nat.beq x y && natListBeqComp _ tl) = (Nat.beq x y && natListBeq _ tl)
      rw [ih tl]

/-- Computable mirror of `EnumTagRepr.beq`. -/
@[expose] def enumTagReprBeqComp (a b : EnumTagRepr) : Bool :=
  match a with
  | .zeroSized => match b with | .zeroSized => true | .scalar _ _ => false
  | .scalar w1 s1 =>
    match b with
    | .zeroSized => false
    | .scalar w2 s2 => intWidthBeqComp w1 w2 && boolBeqComp s1 s2

/-- Agreement between `enumTagReprBeqComp` and `EnumTagRepr.beq`. -/
theorem enumTagReprBeqComp_eq (a b : EnumTagRepr) :
    enumTagReprBeqComp a b = EnumTagRepr.beq a b := by
  cases a <;> cases b <;>
    first
      | rfl
      | (dsimp only [enumTagReprBeqComp, EnumTagRepr.beq]
         rw [intWidthBeqComp_eq, boolBeqComp_eq])

/-- Computable mirror of `EnumTy.beq`. -/
@[expose] def enumTyBeqComp (a b : EnumTy) : Bool :=
  Nat.beq a.id b.id &&
    intWidthBeqComp a.discrWidth b.discrWidth &&
    boolBeqComp a.discrSigned b.discrSigned &&
    enumTagReprBeqComp a.tagRepr b.tagRepr &&
    natListBeqComp a.discriminants b.discriminants

/-- Agreement between `enumTyBeqComp` and `EnumTy.beq`. -/
theorem enumTyBeqComp_eq (a b : EnumTy) : enumTyBeqComp a b = EnumTy.beq a b := by
  unfold enumTyBeqComp EnumTy.beq
  rw [intWidthBeqComp_eq, boolBeqComp_eq, enumTagReprBeqComp_eq, natListBeqComp_eq]

/-- Computable mirror of `Trusted.MirSemantics.isOverflowPairTy`. -/
@[expose] def isOverflowPairTyComp (ty : MirTy) : Bool :=
  match ty with
  | .tuple [.int _ _, .bool] => true
  | _ => false

/-- Agreement between `isOverflowPairTyComp` and `isOverflowPairTy`. -/
theorem isOverflowPairTyComp_eq (ty : MirTy) :
    isOverflowPairTyComp ty = isOverflowPairTy ty := by
  cases ty with
  | tuple fs =>
    cases fs with
    | nil => rfl
    | cons f1 r1 =>
      cases f1 with
      | int _ _ =>
        cases r1 with
        | nil => rfl
        | cons f2 r2 => cases f2 <;> cases r2 <;> rfl
      | bool | unit | never | char | ordering | enum _ | tuple _ | ref _ _ | rawPtr _ _
      | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => rfl
  | bool | int _ _ | unit | never | char | ordering | enum _ | ref _ _ | rawPtr _ _
  | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => rfl

/-- Computable mirror of `BinOp.isShift`. -/
@[expose] def binOpIsShiftComp (op : BinOp) : Bool :=
  match op with
  | .shl | .shlUnchecked | .shr | .shrUnchecked => true
  | _ => false

/-- Agreement between `binOpIsShiftComp` and `BinOp.isShift`. -/
theorem binOpIsShiftComp_eq (op : BinOp) : binOpIsShiftComp op = op.isShift := by
  cases op <;> rfl

/-- Computable mirror of `BinOp.isUnchecked`. -/
@[expose] def binOpIsUncheckedComp (op : BinOp) : Bool :=
  match op with
  | .addUnchecked | .subUnchecked | .mulUnchecked | .shlUnchecked | .shrUnchecked => true
  | _ => false

/-- Agreement between `binOpIsUncheckedComp` and `BinOp.isUnchecked`. -/
theorem binOpIsUncheckedComp_eq (op : BinOp) :
    binOpIsUncheckedComp op = op.isUnchecked := by
  cases op <;> rfl

/-- Computable mirror of `BinOp.isOverflowing`. -/
@[expose] def binOpIsOverflowingComp (op : BinOp) : Bool :=
  match op with
  | .addWithOverflow | .subWithOverflow | .mulWithOverflow => true
  | _ => false

/-- Agreement between `binOpIsOverflowingComp` and `BinOp.isOverflowing`. -/
theorem binOpIsOverflowingComp_eq (op : BinOp) :
    binOpIsOverflowingComp op = op.isOverflowing := by
  cases op <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.intEmod`. -/
@[expose] def intEmodComp (x n : Int) : Int :=
  match x with
  | .ofNat m => .ofNat (Nat.mod m (Int.natAbs n))
  | .negSucc m => Int.subNatNat (Int.natAbs n) (Nat.succ (Nat.mod m (Int.natAbs n)))

/-- Agreement between `intEmodComp` and `intEmod`. -/
theorem intEmodComp_eq (x n : Int) : intEmodComp x n = intEmod x n := by
  cases x <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.intTdiv`. -/
@[expose] def intTdivComp (x y : Int) : Int :=
  match x, y with
  | .ofNat m, .ofNat n => .ofNat (Nat.div m n)
  | .ofNat m, .negSucc n => Int.neg (.ofNat (Nat.div m (Nat.succ n)))
  | .negSucc m, .ofNat n => Int.neg (.ofNat (Nat.div (Nat.succ m) n))
  | .negSucc m, .negSucc n => .ofNat (Nat.div (Nat.succ m) (Nat.succ n))

/-- Agreement between `intTdivComp` and `intTdiv`. -/
theorem intTdivComp_eq (x y : Int) : intTdivComp x y = intTdiv x y := by
  cases x <;> cases y <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.intTmod`. -/
@[expose] def intTmodComp (x y : Int) : Int :=
  match x, y with
  | .ofNat m, .ofNat n => .ofNat (Nat.mod m n)
  | .ofNat m, .negSucc n => .ofNat (Nat.mod m (Nat.succ n))
  | .negSucc m, .ofNat n => Int.neg (.ofNat (Nat.mod (Nat.succ m) n))
  | .negSucc m, .negSucc n => Int.neg (.ofNat (Nat.mod (Nat.succ m) (Nat.succ n)))

/-- Agreement between `intTmodComp` and `intTmod`. -/
theorem intTmodComp_eq (x y : Int) : intTmodComp x y = intTmod x y := by
  cases x <;> cases y <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.intShiftRight`. -/
@[expose] def intShiftRightComp (x : Int) (s : Nat) : Int :=
  match x with
  | .ofNat n => .ofNat (Nat.shiftRight n s)
  | .negSucc n => .negSucc (Nat.shiftRight n s)

/-- Agreement between `intShiftRightComp` and `intShiftRight`. -/
theorem intShiftRightComp_eq (x : Int) (s : Nat) :
    intShiftRightComp x s = intShiftRight x s := by
  cases x <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.intShiftLeft`. -/
@[expose] def intShiftLeftComp (x : Int) (s : Nat) : Int :=
  match x with
  | .ofNat n => .ofNat (Nat.shiftLeft n s)
  | .negSucc n => .negSucc ((Nat.shiftLeft (n + 1) s) - 1)

/-- Agreement between `intShiftLeftComp` and `intShiftLeft`. -/
theorem intShiftLeftComp_eq (x : Int) (s : Nat) :
    intShiftLeftComp x s = intShiftLeft x s := by
  cases x <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.intNot`. -/
@[expose] def intNotComp (x : Int) : Int :=
  match x with
  | .ofNat n => .negSucc n
  | .negSucc n => .ofNat n

/-- Agreement between `intNotComp` and `intNot`. -/
theorem intNotComp_eq (x : Int) : intNotComp x = intNot x := by
  cases x <;> rfl

@[expose] def bvExtractLsb'Comp {n : Nat} (start len : Nat) (x : BitVec n) : BitVec len :=
  BitVec.ofNat len (Nat.shiftRight x.toNat start)

@[expose] def bvExtractLsbComp {n : Nat} (hi lo : Nat) (x : BitVec n) :
    BitVec (hi - lo + 1) :=
  bvExtractLsb'Comp lo (hi - lo + 1) x

/-- Computable mirror of `Trusted.MirSemantics.bvToInt`. -/
@[expose] def bvToIntComp {n : Nat} (x : BitVec n) : Int :=
  if Nat.blt (2 * x.toNat) (Nat.pow 2 n) then
    Int.ofNat x.toNat
  else
    Int.ofNat x.toNat - Int.ofNat (Nat.pow 2 n)

/-- Agreement between `bvToIntComp` and `bvToInt`. -/
theorem bvToIntComp_eq {n : Nat} (x : BitVec n) : bvToIntComp x = bvToInt x := by
  unfold bvToIntComp bvToInt
  cases Nat.decLt (2 * x.toNat) (Nat.pow 2 n) with
  | isTrue hLt =>
    have hBlt : Nat.blt (2 * x.toNat) (Nat.pow 2 n) = true :=
      (Iff.of_eq Nat.blt_eq).mpr hLt
    rw [hBlt]
    rfl
  | isFalse hNotLt =>
    cases hBlt : Nat.blt (2 * x.toNat) (Nat.pow 2 n) with
    | false => rfl
    | true => exact False.elim (hNotLt ((Iff.of_eq Nat.blt_eq).mp hBlt))

/-- Computable mirror of `Trusted.MirSemantics.bvOfInt`. -/
@[expose] def bvOfIntComp (n : Nat) (i : Int) : BitVec n :=
  BitVec.ofNat n (intEmodComp i (Int.ofNat (Nat.pow 2 n))).toNat

/-- Agreement between `bvOfIntComp` and `bvOfInt`. -/
theorem bvOfIntComp_eq (n : Nat) (i : Int) : bvOfIntComp n i = bvOfInt n i := by
  unfold bvOfIntComp bvOfInt
  rw [intEmodComp_eq]

@[expose] def bvZeroExtendComp {w : Nat} (v : Nat) (x : BitVec w) : BitVec v :=
  BitVec.ofNat v x.toNat

/-- Computable mirror of `Trusted.MirSemantics.bvSignExtend`. -/
@[expose] def bvSignExtendComp {w : Nat} (v : Nat) (x : BitVec w) : BitVec v :=
  bvOfIntComp v (bvToIntComp x)

/-- Agreement between `bvSignExtendComp` and `bvSignExtend`. -/
theorem bvSignExtendComp_eq {w : Nat} (v : Nat) (x : BitVec w) :
    bvSignExtendComp v x = bvSignExtend v x := by
  unfold bvSignExtendComp bvSignExtend
  rw [bvToIntComp_eq, bvOfIntComp_eq]

/-- Computable mirror of `Trusted.MirSemantics.truncateBits`. -/
@[expose] def truncateBitsComp (w : IntWidth) (value : BitVec 128) : BitVec 128 :=
  bvZeroExtendComp 128 (bvExtractLsbComp (bitWidthComp w - 1) 0 value)

/-- Agreement between `truncateBitsComp` and `truncateBits`. -/
theorem truncateBitsComp_eq (w : IntWidth) (value : BitVec 128) :
    truncateBitsComp w value = truncateBits w value := by
  cases w <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.signExtendBits`. -/
@[expose] def signExtendBitsComp (w : IntWidth) (value : BitVec 128) : Int :=
  bvToIntComp (bvSignExtendComp 128 (bvExtractLsbComp (bitWidthComp w - 1) 0 value))

/-- Agreement between `signExtendBitsComp` and `signExtendBits`. -/
theorem signExtendBitsComp_eq (w : IntWidth) (value : BitVec 128) :
    signExtendBitsComp w value = signExtendBits w value := by
  cases w <;>
    (unfold signExtendBitsComp signExtendBits;
     rw [bvSignExtendComp_eq, bvToIntComp_eq]; rfl)

@[expose] def bvAndComp (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.land x.toNat y.toNat)

@[expose] def bvOrComp (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.lor x.toNat y.toNat)

@[expose] def bvXorComp (x y : BitVec 128) : BitVec 128 :=
  BitVec.ofNat 128 (Nat.xor x.toNat y.toNat)

/-- Computable mirror of `Trusted.MirSemantics.signedMinInt`. -/
@[expose] def signedMinIntComp (w : IntWidth) : Int :=
  Neg.neg (HPow.hPow (2 : Int) (bitWidthComp w - 1))

/-- Agreement between `signedMinIntComp` and `signedMinInt`. -/
theorem signedMinIntComp_eq (w : IntWidth) : signedMinIntComp w = signedMinInt w := by
  unfold signedMinIntComp signedMinInt
  rw [bitWidthComp_eq]

/-- Computable mirror of `ScalarVal.wf`. -/
@[expose] def scalarWfComp (v : ScalarVal) : Bool :=
  bv128BeqComp (truncateBitsComp v.width v.bits) v.bits

/-- Agreement between `scalarWfComp` and `ScalarVal.wf`. -/
theorem scalarWfComp_eq (v : ScalarVal) : scalarWfComp v = v.wf := by
  unfold scalarWfComp ScalarVal.wf
  rw [bv128BeqComp_eq_beq, truncateBitsComp_eq]

/-- Computable mirror of `Trusted.MirSemantics.decodeScalar`. -/
@[expose] def decodeScalarComp (sv : ScalarVal) : Int :=
  let trunc := truncateBitsComp sv.width sv.bits
  if sv.signed then
    signExtendBitsComp sv.width trunc
  else
    Int.ofNat trunc.toNat

/-- Agreement between `decodeScalarComp` and `decodeScalar`. -/
theorem decodeScalarComp_eq (sv : ScalarVal) : decodeScalarComp sv = decodeScalar sv := by
  dsimp only [decodeScalarComp, decodeScalar]
  rw [truncateBitsComp_eq, signExtendBitsComp_eq]

/-- Computable mirror of `Trusted.MirSemantics.truncateScalar`. -/
@[expose] def truncateScalarComp (w : IntWidth) (s : Bool) (value : Int) :
    Except FaultKind (ScalarVal × Bool) :=
  if s then
    let wrapped := bvToIntComp (bvOfIntComp 128 value)
    if intBltComp wrapped (Neg.neg (HPow.hPow (2 : Int) 127)) ||
        intBleComp (HPow.hPow (2 : Int) 127) wrapped then
      .error .unsupported
    else
      let raw := bvOfIntComp 128 wrapped
      let trunc := truncateBitsComp w raw
      let decoded := signExtendBitsComp w trunc
      .ok (⟨w, s, trunc⟩, !(intBeqComp decoded wrapped))
  else
    let raw := bvOfIntComp 128 value
    let trunc := truncateBitsComp w raw
    .ok (⟨w, s, trunc⟩, !(bv128BeqComp trunc raw))

/-- Agreement between `truncateScalarComp` and `truncateScalar`. -/
theorem truncateScalarComp_eq (w : IntWidth) (s : Bool) (value : Int) :
    truncateScalarComp w s value = truncateScalar w s value := by
  cases s with
  | false =>
    change (Except.ok (ScalarVal.mk w false (truncateBitsComp w (bvOfIntComp 128 value)),
        !(bv128BeqComp (truncateBitsComp w (bvOfIntComp 128 value)) (bvOfIntComp 128 value))) :
        Except FaultKind (ScalarVal × Bool)) =
      Except.ok (ScalarVal.mk w false (truncateBits w (bvOfInt 128 value)),
        truncateBits w (bvOfInt 128 value) != bvOfInt 128 value)
    rw [bvOfIntComp_eq, truncateBitsComp_eq, bv128BneComp_eq]
  | true =>
    let wrappedC := bvToIntComp (bvOfIntComp 128 value)
    let wrappedT := bvToInt (bvOfInt 128 value)
    change ((if (intBltComp wrappedC (Neg.neg (HPow.hPow (2 : Int) 127)) ||
          intBleComp (HPow.hPow (2 : Int) 127) wrappedC) = true then
        Except.error FaultKind.unsupported
      else
        Except.ok (ScalarVal.mk w true (truncateBitsComp w (bvOfIntComp 128 wrappedC)),
          !(intBeqComp (signExtendBitsComp w (truncateBitsComp w (bvOfIntComp 128 wrappedC)))
            wrappedC))) :
        Except FaultKind (ScalarVal × Bool)) =
      (if (decide (wrappedT < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide (HPow.hPow (2 : Int) 127 ≤ wrappedT)) = true then
        Except.error FaultKind.unsupported
      else
        Except.ok (ScalarVal.mk w true (truncateBits w (bvOfInt 128 wrappedT)),
          signExtendBits w (truncateBits w (bvOfInt 128 wrappedT)) != wrappedT))
    have hWrap : wrappedC = wrappedT := by
      dsimp only [wrappedC, wrappedT]
      rw [bvOfIntComp_eq, bvToIntComp_eq]
    rw [hWrap, bvOfIntComp_eq, truncateBitsComp_eq, signExtendBitsComp_eq,
      intBneComp_eq, intBltComp_eq_dec, intBleComp_eq_dec]

/-- Computable mirror of `Trusted.MirSemantics.evalShiftOp`. -/
@[expose] def evalShiftOpComp (op : BinOp) (w : IntWidth) (s : Bool) (l r : Int) :
    Except FaultKind Val :=
  let amount := intEmodComp r (Int.ofNat (bitWidthComp w))
  let overflow := !(intBeqComp amount r)
  let result := match op with
    | .shl | .shlUnchecked => intShiftLeftComp l amount.toNat
    | _ => intShiftRightComp l amount.toNat
  match truncateScalarComp w s result with
  | .error k => .error k
  | .ok (res, _) =>
    if overflow && binOpIsUncheckedComp op then .error .undefined else .ok (.scalar res)

/-- Agreement between `evalShiftOpComp` and `evalShiftOp`. -/
theorem evalShiftOpComp_eq (op : BinOp) (w : IntWidth) (s : Bool) (l r : Int) :
    evalShiftOpComp op w s l r = evalShiftOp op w s l r := by
  cases op <;>
    (dsimp only [evalShiftOpComp, evalShiftOp]
     rw [bitWidthComp_eq, intEmodComp_eq, intBneComp_eq, binOpIsUncheckedComp_eq]
     first
       | (rw [intShiftLeftComp_eq, truncateScalarComp_eq];
          cases truncateScalar w s (intShiftLeft l (intEmod r (Int.ofNat w.bitWidth)).toNat) with
          | error _ => rfl
          | ok p => cases p; rfl)
       | (rw [intShiftRightComp_eq, truncateScalarComp_eq];
          cases truncateScalar w s (intShiftRight l (intEmod r (Int.ofNat w.bitWidth)).toNat) with
          | error _ => rfl
          | ok p => cases p; rfl))

@[expose] def hostOverflowComp (s : Bool) (result : Int) : Bool :=
  if s then
    intBltComp result (Neg.neg (HPow.hPow (2 : Int) 127)) ||
      intBleComp (HPow.hPow (2 : Int) 127) result
  else
    intBltComp result 0 || intBleComp (HPow.hPow (2 : Int) 128) result

/-- Computable mirror of `Trusted.MirSemantics.evalArithOp`. -/
@[expose] def evalArithOpComp (op : BinOp) (w : IntWidth) (s : Bool) (l r : Int) :
    Except FaultKind Val :=
  let isDivOrRem := match op with | .div | .rem => true | _ => false
  if isDivOrRem && intBeqComp r 0 then
    .error .undefined
  else if s && isDivOrRem &&
      (intBeqComp l (signedMinIntComp w) && intBeqComp r (Neg.neg 1)) then
    .error .undefined
  else
    let res? : Option Int := match op with
      | .add | .addUnchecked | .addWithOverflow => some (l + r)
      | .sub | .subUnchecked | .subWithOverflow => some (l - r)
      | .mul | .mulUnchecked | .mulWithOverflow => some (l * r)
      | .div => some (intTdivComp l r)
      | .rem => some (intTmodComp l r)
      | _ => none
    match res? with
    | none => .error .unsupported
    | some result =>
      let hostOverflow := hostOverflowComp s result
      match truncateScalarComp w s result with
      | .error k => .error k
      | .ok (val, lossy) =>
        if (hostOverflow || lossy) && binOpIsUncheckedComp op then
          .error .undefined
        else if binOpIsOverflowingComp op then
          .ok (.tuple [.scalar val, .bool (hostOverflow || lossy)])
        else
          .ok (.scalar val)

private theorem evalArithFinish_eq
    (op : BinOp) (w : IntWidth) (s : Bool) (result : Int) :
    ((match truncateScalarComp w s result with
      | .error k => Except.error k
      | .ok (val, lossy) =>
        if (hostOverflowComp s result || lossy) && binOpIsUncheckedComp op then
          Except.error FaultKind.undefined
        else if binOpIsOverflowingComp op then
          Except.ok (Val.tuple [Val.scalar val, Val.bool (hostOverflowComp s result || lossy)])
        else
          Except.ok (Val.scalar val)) : Except FaultKind Val) =
    (let hostOverflow : Bool :=
       if s then
         decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
         decide (HPow.hPow (2 : Int) 127 ≤ result)
       else
         decide (result < 0) ||
         decide (HPow.hPow (2 : Int) 128 ≤ result)
     match truncateScalar w s result with
     | .error k => Except.error k
     | .ok (val, lossy) =>
       if (hostOverflow || lossy) && op.isUnchecked then
         Except.error FaultKind.undefined
       else if op.isOverflowing then
         Except.ok (Val.tuple [Val.scalar val, Val.bool (hostOverflow || lossy)])
       else
         Except.ok (Val.scalar val)) := by
  rw [truncateScalarComp_eq, binOpIsUncheckedComp_eq, binOpIsOverflowingComp_eq]
  have hHost : hostOverflowComp s result =
      (if s then
         decide (result < Neg.neg (HPow.hPow (2 : Int) 127)) ||
         decide (HPow.hPow (2 : Int) 127 ≤ result)
       else
         decide (result < 0) ||
         decide (HPow.hPow (2 : Int) 128 ≤ result)) := by
    cases s with
    | false =>
      change (intBltComp result 0 || intBleComp (HPow.hPow (2 : Int) 128) result) = _
      rw [intBltComp_eq_dec, intBleComp_eq_dec]
      rfl
    | true =>
      change (intBltComp result (Neg.neg (HPow.hPow (2 : Int) 127)) ||
          intBleComp (HPow.hPow (2 : Int) 127) result) = _
      rw [intBltComp_eq_dec, intBleComp_eq_dec]
      rfl
  rw [hHost]

/-- Agreement between `evalArithOpComp` and `evalArithOp`. -/
theorem evalArithOpComp_eq (op : BinOp) (w : IntWidth) (s : Bool) (l r : Int) :
    evalArithOpComp op w s l r = evalArithOp op w s l r := by
  unfold evalArithOpComp evalArithOp
  rw [intBeqComp_eq_beq r 0, signedMinIntComp_eq w,
      intBeqComp_eq_beq l (signedMinInt w), intBeqComp_eq_beq r (Neg.neg 1),
      intTdivComp_eq, intTmodComp_eq]
  cases s with
  | false =>
    cases op with
    | add | addUnchecked | addWithOverflow => exact evalArithFinish_eq _ w false (l + r)
    | sub | subUnchecked | subWithOverflow => exact evalArithFinish_eq _ w false (l - r)
    | mul | mulUnchecked | mulWithOverflow => exact evalArithFinish_eq _ w false (l * r)
    | div =>
      change (if (r == 0) = true then Except.error FaultKind.undefined else _) =
        (if (r == 0) = true then Except.error FaultKind.undefined else _)
      cases (r == 0) with
      | true => rfl
      | false => exact evalArithFinish_eq .div w false (intTdiv l r)
    | rem =>
      change (if (r == 0) = true then Except.error FaultKind.undefined else _) =
        (if (r == 0) = true then Except.error FaultKind.undefined else _)
      cases (r == 0) with
      | true => rfl
      | false => exact evalArithFinish_eq .rem w false (intTmod l r)
    | shl | shr | shlUnchecked | shrUnchecked | bitXor | bitAnd | bitOr
    | eq | lt | le | ne | ge | gt | cmp | offset => rfl
  | true =>
    cases op with
    | add | addUnchecked | addWithOverflow => exact evalArithFinish_eq _ w true (l + r)
    | sub | subUnchecked | subWithOverflow => exact evalArithFinish_eq _ w true (l - r)
    | mul | mulUnchecked | mulWithOverflow => exact evalArithFinish_eq _ w true (l * r)
    | div =>
      change (if (r == 0) = true then Except.error FaultKind.undefined
          else if ((l == signedMinInt w) && (r == Neg.neg 1)) = true then
            Except.error FaultKind.undefined
          else _) =
        (if (r == 0) = true then Except.error FaultKind.undefined
          else if ((l == signedMinInt w) && (r == Neg.neg 1)) = true then
            Except.error FaultKind.undefined
          else _)
      cases (r == 0) with
      | true => rfl
      | false =>
        cases ((l == signedMinInt w) && (r == Neg.neg 1)) with
        | true => rfl
        | false => exact evalArithFinish_eq .div w true (intTdiv l r)
    | rem =>
      change (if (r == 0) = true then Except.error FaultKind.undefined
          else if ((l == signedMinInt w) && (r == Neg.neg 1)) = true then
            Except.error FaultKind.undefined
          else _) =
        (if (r == 0) = true then Except.error FaultKind.undefined
          else if ((l == signedMinInt w) && (r == Neg.neg 1)) = true then
            Except.error FaultKind.undefined
          else _)
      cases (r == 0) with
      | true => rfl
      | false =>
        cases ((l == signedMinInt w) && (r == Neg.neg 1)) with
        | true => rfl
        | false => exact evalArithFinish_eq .rem w true (intTmod l r)
    | shl | shr | shlUnchecked | shrUnchecked | bitXor | bitAnd | bitOr
    | eq | lt | le | ne | ge | gt | cmp | offset => rfl

/-- Computable mirror of `Trusted.MirSemantics.cmpOrderingOfInt`. -/
@[expose] def cmpOrderingOfIntComp (l r : Int) : OrderingVal :=
  if intBltComp l r then .less else if intBeqComp l r then .equal else .greater

/-- Agreement between `cmpOrderingOfIntComp` and `cmpOrderingOfInt`. -/
theorem cmpOrderingOfIntComp_eq (l r : Int) :
    cmpOrderingOfIntComp l r = cmpOrderingOfInt l r := by
  unfold cmpOrderingOfIntComp cmpOrderingOfInt
  rw [intBltComp_eq_dec, intBeqComp_eq_beq]
  rfl

/-- Computable mirror of `Trusted.MirSemantics.evalBinOp`. -/
@[expose] def evalBinOpComp (op : BinOp) (lhs rhs : Val) : Except FaultKind Val :=
  match lhs, rhs with
  | .scalar l, .scalar r =>
    let lInt := decodeScalarComp l
    let rInt := decodeScalarComp r
    let w := l.width
    let s := l.signed
    if binOpIsShiftComp op then
      evalShiftOpComp op w s lInt rInt
    else if !(intWidthBeqComp l.width r.width && boolBeqComp l.signed r.signed) then
      .error .unsupported
    else
      match op with
      | .eq => .ok (.bool (intBeqComp lInt rInt))
      | .ne => .ok (.bool (!(intBeqComp lInt rInt)))
      | .lt => .ok (.bool (intBltComp lInt rInt))
      | .le => .ok (.bool (intBleComp lInt rInt))
      | .gt => .ok (.bool (intBltComp rInt lInt))
      | .ge => .ok (.bool (intBleComp rInt lInt))
      | .cmp => .ok (.ordering (cmpOrderingOfIntComp lInt rInt))
      | .bitAnd =>
        .ok (.scalar ⟨w, s,
          truncateBitsComp w (bvAndComp (truncateBitsComp w l.bits)
            (truncateBitsComp r.width r.bits))⟩)
      | .bitOr =>
        .ok (.scalar ⟨w, s,
          truncateBitsComp w (bvOrComp (truncateBitsComp w l.bits)
            (truncateBitsComp r.width r.bits))⟩)
      | .bitXor =>
        .ok (.scalar ⟨w, s,
          truncateBitsComp w (bvXorComp (truncateBitsComp w l.bits)
            (truncateBitsComp r.width r.bits))⟩)
      | .add | .sub | .mul | .div | .rem
      | .addUnchecked | .subUnchecked | .mulUnchecked
      | .addWithOverflow | .subWithOverflow | .mulWithOverflow =>
        evalArithOpComp op w s lInt rInt
      | _ => .error .unsupported
  | .bool l, .bool r =>
    match op with
    | .eq => .ok (.bool (boolBeqComp l r))
    | .ne => .ok (.bool (!(boolBeqComp l r)))
    | .lt => .ok (.bool (!l && r))
    | .le => .ok (.bool (!l || r))
    | .gt => .ok (.bool (l && !r))
    | .ge => .ok (.bool (l || !r))
    | .bitAnd => .ok (.bool (l && r))
    | .bitOr => .ok (.bool (l || r))
    | .bitXor => .ok (.bool (bne l r))
    | _ => .error .unsupported
  | .char l, .char r =>
    let lInt := Int.ofNat l.toNat
    let rInt := Int.ofNat r.toNat
    match op with
    | .eq => .ok (.bool (intBeqComp lInt rInt))
    | .ne => .ok (.bool (!(intBeqComp lInt rInt)))
    | .lt => .ok (.bool (intBltComp lInt rInt))
    | .le => .ok (.bool (intBleComp lInt rInt))
    | .gt => .ok (.bool (intBltComp rInt lInt))
    | .ge => .ok (.bool (intBleComp rInt lInt))
    | .cmp => .ok (.ordering (cmpOrderingOfIntComp lInt rInt))
    | _ => .error .unsupported
  | _, _ => .error .unsupported

/-- Agreement between `evalBinOpComp` and `evalBinOp`. -/
theorem evalBinOpComp_eq (op : BinOp) (lhs rhs : Val) :
    evalBinOpComp op lhs rhs = evalBinOp op lhs rhs := by
  cases lhs with
  | scalar l =>
    cases rhs with
    | scalar r =>
      dsimp only [evalBinOpComp, evalBinOp, bvAndComp, bvAnd, bvOrComp, bvOr, bvXorComp, bvXor]
      rw [decodeScalarComp_eq l, decodeScalarComp_eq r, binOpIsShiftComp_eq,
        intWidthBeqComp_eq, boolBeqComp_eq, evalShiftOpComp_eq]
      cases op <;> dsimp only <;>
        first
          | rfl
          | rw [intBneComp_eq]
          | rw [intBeqComp_eq_beq]
          | rw [intBltComp_eq_dec]
          | rw [intBleComp_eq_dec]
          | rw [intBgtComp_eq_dec]
          | rw [intBgeComp_eq_dec]
          | rw [cmpOrderingOfIntComp_eq]
          | exact congrArg
              (fun x => if !(l.width.beq r.width && (l.signed == r.signed)) then
                Except.error FaultKind.unsupported else x)
              (evalArithOpComp_eq _ l.width l.signed (decodeScalar l) (decodeScalar r))
          | rw [truncateBitsComp_eq l.width l.bits, truncateBitsComp_eq r.width r.bits,
              truncateBitsComp_eq l.width _]
    | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl
  | bool l =>
    cases rhs with
    | bool r => cases l <;> cases r <;> cases op <;> rfl
    | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl
  | char l =>
    cases rhs with
    | char r =>
      cases op <;> dsimp only [evalBinOpComp, evalBinOp] <;>
        first
          | rfl
          | rw [intBneComp_eq]
          | rw [intBeqComp_eq_beq]
          | rw [intBltComp_eq_dec]
          | rw [intBleComp_eq_dec]
          | rw [intBgtComp_eq_dec]
          | rw [intBgeComp_eq_dec]
          | rw [cmpOrderingOfIntComp_eq]
    | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | bool _ | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl
  | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
  | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl

/-- Computable mirror of `Trusted.MirSemantics.intLikeBits`. -/
@[expose] def intLikeBitsComp (v : Val) : Option Nat :=
  match v with
  | .scalar sv =>
    if sv.signed then
      some (bvOfIntComp 128 (decodeScalarComp sv)).toNat
    else
      some (truncateBitsComp sv.width sv.bits).toNat
  | .bool b => some (if b then 1 else 0)
  | .char c => some c.toNat
  | _ => none

/-- Agreement between `intLikeBitsComp` and `intLikeBits`. -/
theorem intLikeBitsComp_eq (v : Val) : intLikeBitsComp v = intLikeBits v := by
  cases v with
  | scalar sv =>
    unfold intLikeBitsComp intLikeBits
    dsimp only
    rw [decodeScalarComp_eq, bvOfIntComp_eq, truncateBitsComp_eq]
  | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
  | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl

/-- Computable mirror of `Trusted.MirSemantics.evalIntToIntCast`. -/
@[expose] def evalIntToIntCastComp (v : Val) (castTy : MirTy) : Except FaultKind Val :=
  match intLikeBitsComp v with
  | none => .error .unsupported
  | some bits =>
    match castTy with
    | .int w s => .ok (.scalar ⟨w, s, truncateBitsComp w (BitVec.ofNat 128 bits)⟩)
    | .char =>
      if Nat.ble bits 255 then .ok (.char (Char.ofNat bits)) else .error .unsupported
    | _ => .error .unsupported

/-- Agreement between `evalIntToIntCastComp` and `evalIntToIntCast`. -/
theorem evalIntToIntCastComp_eq (v : Val) (castTy : MirTy) :
    evalIntToIntCastComp v castTy = evalIntToIntCast v castTy := by
  unfold evalIntToIntCastComp evalIntToIntCast
  rw [intLikeBitsComp_eq]
  cases intLikeBits v with
  | none => rfl
  | some bits =>
    cases castTy with
    | int w s =>
      dsimp only
      rw [truncateBitsComp_eq]
    | bool | unit | never | char | ordering | enum _ | tuple _ | ref _ _ | rawPtr _ _
    | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => rfl

/-- Computable mirror of `Trusted.MirSemantics.evalUnOp`. -/
@[expose] def evalUnOpComp (op : UnOp) (v : Val) : Except FaultKind Val :=
  match op, v with
  | .not, .bool b => .ok (.bool (!b))
  | .not, .scalar sv =>
    match truncateScalarComp sv.width sv.signed (intNotComp (decodeScalarComp sv)) with
    | .ok (res, _) => .ok (.scalar res)
    | .error k => .error k
  | .neg, .scalar sv =>
    if sv.signed then
      match truncateScalarComp sv.width sv.signed (Neg.neg (decodeScalarComp sv)) with
      | .ok (res, _) => .ok (.scalar res)
      | .error k => .error k
    else
      .error .unsupported
  | _, _ => .error .unsupported

/-- Agreement between `evalUnOpComp` and `evalUnOp`. -/
theorem evalUnOpComp_eq (op : UnOp) (v : Val) : evalUnOpComp op v = evalUnOp op v := by
  cases op with
  | not =>
    cases v with
    | scalar sv =>
      dsimp only [evalUnOpComp, evalUnOp]
      rw [decodeScalarComp_eq, intNotComp_eq, truncateScalarComp_eq]
      cases truncateScalar sv.width sv.signed (intNot (decodeScalar sv)) with
      | error _ => rfl
      | ok p => cases p; rfl
    | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl
  | neg =>
    cases v with
    | scalar sv =>
      dsimp only [evalUnOpComp, evalUnOp]
      rw [decodeScalarComp_eq, truncateScalarComp_eq]
      cases sv.signed with
      | false => rfl
      | true =>
        cases truncateScalar sv.width true (Neg.neg (decodeScalar sv)) with
        | error _ => rfl
        | ok p => cases p; rfl
    | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
    | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl
  | ptrMetadata => rfl

/-- Computable mirror of `Trusted.MirSemantics.natNotElem`. -/
@[expose] def natNotElemComp (x : Nat) (ys : List Nat) : Bool :=
  List.foldr (fun y acc => !Nat.beq x y && acc) true ys

/-- Agreement between `natNotElemComp` and `natNotElem`. -/
theorem natNotElemComp_eq (x : Nat) (ys : List Nat) :
    natNotElemComp x ys = natNotElem x ys := by
  induction ys with
  | nil => rfl
  | cons y tl ih =>
    change (!Nat.beq x y && natNotElemComp x tl) = (!Nat.beq x y && natNotElem x tl)
    rw [ih]

/-- Computable mirror of `Trusted.MirSemantics.natListPairwiseNe`. -/
@[expose] def natListPairwiseNeComp (xs : List Nat) : Bool :=
  (List.foldr
    (fun (x : Nat) (acc : List Nat × Bool) =>
      (x :: acc.1, natNotElemComp x acc.1 && acc.2))
    ([], true)
    xs).2

private theorem natListPairwiseNeComp_fst (xs : List Nat) :
    (List.foldr
      (fun (x : Nat) (acc : List Nat × Bool) =>
        (x :: acc.1, natNotElemComp x acc.1 && acc.2))
      ([], true)
      xs).1 = xs := by
  induction xs with
  | nil => rfl
  | cons x _ ih => exact congrArg (List.cons x) ih

/-- Agreement between `natListPairwiseNeComp` and `natListPairwiseNe`. -/
theorem natListPairwiseNeComp_eq (xs : List Nat) :
    natListPairwiseNeComp xs = natListPairwiseNe xs := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    change (natNotElemComp x (List.foldr _ ([], true) tl).1 && natListPairwiseNeComp tl) =
      (natNotElem x tl && natListPairwiseNe tl)
    rw [natListPairwiseNeComp_fst tl, natNotElemComp_eq, ih]

/-- Computable elementwise equality on `List UInt8`. -/
@[expose] def listBeqUInt8Comp (xs ys : List UInt8) : Bool :=
  List.foldr
    (fun (x : UInt8) (ih : List UInt8 → Bool) (bs : List UInt8) =>
      match bs with
      | [] => false
      | y :: tl => uint8BeqComp x y && ih tl)
    (fun bs => match bs with | [] => true | _ :: _ => false)
    xs ys

/-- Agreement between `listBeqUInt8Comp` and `List.beq`. -/
theorem listBeqUInt8Comp_eq (xs ys : List UInt8) :
    listBeqUInt8Comp xs ys = List.beq xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x _ ih =>
    cases ys with
    | nil => rfl
    | cons y tl =>
      change (uint8BeqComp x y && listBeqUInt8Comp _ tl) = ((x == y) && List.beq _ tl)
      rw [uint8BeqComp_eq_beq, ih tl]

/-- Computable mirror of `Trusted.MirSemantics.stringBeq`. -/
@[expose] def stringBeqComp (a b : String) : Bool :=
  listBeqUInt8Comp a.toByteArray.data.toList b.toByteArray.data.toList

/-- Agreement between `stringBeqComp` and `stringBeq`. -/
theorem stringBeqComp_eq (a b : String) : stringBeqComp a b = stringBeq a b := by
  unfold stringBeqComp stringBeq
  exact listBeqUInt8Comp_eq _ _

/-- Agreement between `List.isEmpty` on UTF-8 bytes and `stringIsEmpty`. -/
theorem stringIsEmptyComp_eq (s : String) :
    s.toByteArray.data.toList.isEmpty = stringIsEmpty s := rfl

/-- Computable mirror of `Trusted.MirSemantics.tagBitsToDiscrBits`. -/
@[expose] def tagBitsToDiscrBitsComp (tagW : IntWidth) (tagS : Bool) (discrW : IntWidth)
    (tagBits : BitVec 128) : BitVec 128 :=
  let extended :=
    if tagS then bvOfIntComp 128 (signExtendBitsComp tagW tagBits)
    else truncateBitsComp tagW tagBits
  truncateBitsComp discrW extended

/-- Agreement between `tagBitsToDiscrBitsComp` and `tagBitsToDiscrBits`. -/
theorem tagBitsToDiscrBitsComp_eq (tagW : IntWidth) (tagS : Bool) (discrW : IntWidth)
    (tagBits : BitVec 128) :
    tagBitsToDiscrBitsComp tagW tagS discrW tagBits =
      tagBitsToDiscrBits tagW tagS discrW tagBits := by
  unfold tagBitsToDiscrBitsComp tagBitsToDiscrBits
  rw [signExtendBitsComp_eq, bvOfIntComp_eq, truncateBitsComp_eq, truncateBitsComp_eq]

/-- Computable mirror of `Trusted.MirSemantics.enumAdmitted`. -/
@[expose] def enumAdmittedComp (ety : EnumTy) : Bool :=
  !ety.discriminants.isEmpty &&
    Nat.blt ety.discriminants.length (Nat.pow 2 32) &&
    ety.discriminants.all (fun d => Nat.blt d (Nat.pow 2 (bitWidthComp ety.discrWidth))) &&
    natListPairwiseNeComp ety.discriminants &&
    match ety.tagRepr with
    | .zeroSized => Nat.beq ety.discriminants.length 1
    | .scalar tagW tagS =>
      ety.discriminants.all (fun d =>
        let dBits := BitVec.ofNat 128 d
        bv128BeqComp
          (tagBitsToDiscrBitsComp tagW tagS ety.discrWidth (truncateBitsComp tagW dBits))
          dBits)

/-- Agreement between `enumAdmittedComp` and `enumAdmitted`. -/
theorem enumAdmittedComp_eq (ety : EnumTy) : enumAdmittedComp ety = enumAdmitted ety := by
  dsimp only [enumAdmittedComp, enumAdmitted]
  rw [bitWidthComp_eq, natListPairwiseNeComp_eq]
  cases ety.tagRepr with
  | zeroSized => rfl
  | scalar tagW tagS =>
    dsimp only
    have hAll : ety.discriminants.all (fun d =>
        bv128BeqComp
          (tagBitsToDiscrBitsComp tagW tagS ety.discrWidth
            (truncateBitsComp tagW (BitVec.ofNat 128 d)))
          (BitVec.ofNat 128 d)) =
      ety.discriminants.all (fun d =>
        tagBitsToDiscrBits tagW tagS ety.discrWidth
          (truncateBits tagW (BitVec.ofNat 128 d)) ==
          BitVec.ofNat 128 d) :=
      listAll_congr ety.discriminants (fun d => by
        rw [bv128BeqComp_eq_beq, truncateBitsComp_eq, tagBitsToDiscrBitsComp_eq])
    rw [hAll]

/-- Computable mirror of `Trusted.MirSemantics.isZstEnumTy`. -/
@[expose] def isZstEnumTyComp (ety : EnumTy) : Bool :=
  match ety.tagRepr with
  | .zeroSized => enumAdmittedComp ety
  | .scalar _ _ => false

/-- Agreement between `isZstEnumTyComp` and `isZstEnumTy`. -/
theorem isZstEnumTyComp_eq (ety : EnumTy) : isZstEnumTyComp ety = isZstEnumTy ety := by
  unfold isZstEnumTyComp isZstEnumTy
  cases ety.tagRepr <;> first | rfl | exact enumAdmittedComp_eq ety

/-- Computable mirror of `Trusted.MirSemantics.findDiscrVariantAux`. -/
@[expose] def findDiscrVariantAuxComp (idx : Nat) (discrBits : BitVec 128) (ds : List Nat) :
    Option Nat :=
  List.foldr
    (fun (d : Nat) (ih : Nat → Option Nat) (i : Nat) =>
      if bv128BeqComp (BitVec.ofNat 128 d) discrBits then some i else ih (i + 1))
    (fun _ => none)
    ds idx

/-- Agreement between `findDiscrVariantAuxComp` and `findDiscrVariantAux`. -/
theorem findDiscrVariantAuxComp_eq (idx : Nat) (discrBits : BitVec 128) (ds : List Nat) :
    findDiscrVariantAuxComp idx discrBits ds = findDiscrVariantAux idx discrBits ds := by
  induction ds generalizing idx with
  | nil => rfl
  | cons d tl ih =>
    change (if bv128BeqComp (BitVec.ofNat 128 d) discrBits then some idx
        else findDiscrVariantAuxComp (idx + 1) discrBits tl) =
      (if BitVec.ofNat 128 d == discrBits then some idx
        else findDiscrVariantAux (idx + 1) discrBits tl)
    rw [bv128BeqComp_eq_beq, ih (idx + 1)]

/-- Computable mirror of `Trusted.MirSemantics.findDiscrVariant?`. -/
@[expose] def findDiscrVariant?Comp (discrBits : BitVec 128) (ds : List Nat) : Option Nat :=
  findDiscrVariantAuxComp 0 discrBits ds

/-- Agreement between `findDiscrVariant?Comp` and `findDiscrVariant?`. -/
theorem findDiscrVariant?Comp_eq (discrBits : BitVec 128) (ds : List Nat) :
    findDiscrVariant?Comp discrBits ds = findDiscrVariant? discrBits ds :=
  findDiscrVariantAuxComp_eq 0 discrBits ds

/-- Computable mirror of `Trusted.MirSemantics.isUnicodeScalar`. -/
@[expose] def isUnicodeScalarComp (n : Nat) : Bool :=
  Nat.ble n 0x10ffff && !(Nat.ble 0xd800 n && Nat.ble n 0xdfff)

/-- Computable mirror of `Trusted.MirSemantics.orderingTagBits`. -/
@[expose] def orderingTagBitsComp (ord : OrderingVal) : Nat :=
  match ord with
  | .less => 255
  | .equal => 0
  | .greater => 1

/-- Computable mirror of `Trusted.MirSemantics.orderingOfTagBits`. -/
@[expose] def orderingOfTagBitsComp (bits : Nat) : Option OrderingVal :=
  if Nat.beq bits 255 then some .less
  else if Nat.beq bits 0 then some .equal
  else if Nat.beq bits 1 then some .greater
  else none

/-- Computable mirror of `Val.ty?`. -/
@[expose] def valTy?Comp (v : Val) : Option MirTy :=
  match v with
  | .scalar sv => if scalarWfComp sv then some (.int sv.width sv.signed) else none
  | .bool _ => some .bool
  | .char _ => some .char
  | .ordering _ => some .ordering
  | .unit => some .unit
  | .enumVal ety var =>
    if enumAdmittedComp ety && Nat.blt var ety.discriminants.length then some (.enum ety)
    else none
  | .tuple [.scalar sv, .bool _] =>
    if scalarWfComp sv then some (.tuple [.int sv.width sv.signed, .bool]) else none
  | _ => none

/-- Agreement between `valTy?Comp` and `Val.ty?`. -/
theorem valTy?Comp_eq (v : Val) : valTy?Comp v = v.ty? := by
  cases v with
  | scalar sv =>
    dsimp only [valTy?Comp, Val.ty?]
    rw [scalarWfComp_eq]
  | enumVal ety _ =>
    dsimp only [valTy?Comp, Val.ty?]
    rw [enumAdmittedComp_eq]
  | tuple fs =>
    cases fs with
    | nil => rfl
    | cons x1 r1 =>
      cases x1 with
      | scalar sv =>
        cases r1 with
        | nil => rfl
        | cons x2 r2 =>
          cases x2 with
          | bool _ =>
            cases r2 with
            | nil => dsimp only [valTy?Comp, Val.ty?]; rw [scalarWfComp_eq]
            | cons _ _ => rfl
          | scalar _ | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _
          | optionVal _ | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl
      | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
      | bool _ | char _ | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => rfl
  | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | range _ _ | optionVal _
  | bool _ | char _ | ordering _ | unit | array _ | bytes _ => rfl

/-- Computable mirror of `Trusted.MirSemantics.isSupportedScalarOrUnitTy`. -/
@[expose] def isSupportedScalarOrUnitTyComp (ty : MirTy) : Bool :=
  match ty with
  | .bool | .int _ _ | .char | .ordering | .unit | .never => true
  | .enum ety => enumAdmittedComp ety
  | .tuple fs => isOverflowPairTyComp (.tuple fs)
  | _ => false

/-- Agreement between `isSupportedScalarOrUnitTyComp` and
`isSupportedScalarOrUnitTy`. -/
theorem isSupportedScalarOrUnitTyComp_eq (ty : MirTy) :
    isSupportedScalarOrUnitTyComp ty = isSupportedScalarOrUnitTy ty := by
  cases ty with
  | enum ety => exact enumAdmittedComp_eq ety
  | tuple fs => exact isOverflowPairTyComp_eq (.tuple fs)
  | bool | int _ _ | char | ordering | unit | never | ref _ _ | rawPtr _ _
  | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => rfl

/-- Computable mirror of `Trusted.MirSemantics.liveUninitSlot`. -/
@[expose] def liveUninitSlotComp (ty : MirTy) : LocalSlot :=
  match ty with
  | .unit => .immediate (some .unit)
  | .enum ety =>
    if isZstEnumTyComp ety then .immediate (some (.enumVal ety 0)) else .immediate none
  | _ => .immediate none

/-- Agreement between `liveUninitSlotComp` and `liveUninitSlot`. -/
theorem liveUninitSlotComp_eq (ty : MirTy) : liveUninitSlotComp ty = liveUninitSlot ty := by
  cases ty with
  | enum ety =>
    dsimp only [liveUninitSlotComp, liveUninitSlot]
    rw [isZstEnumTyComp_eq]
  | bool | int _ _ | char | ordering | unit | never | tuple _ | ref _ _ | rawPtr _ _
  | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => rfl

/-- Computable mirror of `Trusted.MirSemantics.isPrimitiveReadableTy`. -/
@[expose] def isPrimitiveReadableTyComp (ty : MirTy) : Bool :=
  match ty with
  | .bool | .int _ _ | .char => true
  | .tuple fs => isOverflowPairTyComp (.tuple fs)
  | _ => false

/-- Agreement between `isPrimitiveReadableTyComp` and
`isPrimitiveReadableTy`. -/
theorem isPrimitiveReadableTyComp_eq (ty : MirTy) :
    isPrimitiveReadableTyComp ty = isPrimitiveReadableTy ty := by
  cases ty with
  | tuple fs => exact isOverflowPairTyComp_eq (.tuple fs)
  | bool | int _ _ | char | ordering | unit | never | enum _ | ref _ _ | rawPtr _ _
  | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => rfl

/-- Computable mirror of `Trusted.MirSemantics.isIntLikeTy`. -/
@[expose] def isIntLikeTyComp (ty : MirTy) : Bool :=
  match ty with
  | .bool | .int _ _ | .char => true
  | _ => false

/-- Agreement between `isIntLikeTyComp` and `isIntLikeTy`. -/
theorem isIntLikeTyComp_eq (ty : MirTy) : isIntLikeTyComp ty = isIntLikeTy ty := by
  cases ty <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.intLayout`. -/
@[expose] def intLayoutComp (w : IntWidth) : LayoutData :=
  match w with
  | .i8 => ⟨1, 0⟩
  | .i16 => ⟨2, 1⟩
  | .i32 => ⟨4, 2⟩
  | .i64 => ⟨8, 3⟩
  | .isize => ⟨8, 3⟩
  | .i128 => ⟨16, 4⟩

/-- Agreement between `intLayoutComp` and `intLayout`. -/
theorem intLayoutComp_eq (w : IntWidth) : intLayoutComp w = intLayout w := by
  cases w <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.overflowPairLayout`. -/
@[expose] def overflowPairLayoutComp (w : IntWidth) : LayoutData :=
  ⟨2 * (intLayoutComp w).size, (intLayoutComp w).alignLog2⟩

/-- Agreement between `overflowPairLayoutComp` and `overflowPairLayout`. -/
theorem overflowPairLayoutComp_eq (w : IntWidth) :
    overflowPairLayoutComp w = overflowPairLayout w := by
  unfold overflowPairLayoutComp overflowPairLayout
  rw [intLayoutComp_eq]

/-- Computable mirror of `Trusted.MirSemantics.layoutOfTy`. -/
@[expose] def layoutOfTyComp (ty : MirTy) : Option LayoutData :=
  match ty with
  | .bool => some ⟨1, 0⟩
  | .int w _ => some (intLayoutComp w)
  | .char => some ⟨4, 2⟩
  | .ordering => some ⟨1, 0⟩
  | .unit | .never => some ⟨0, 0⟩
  | .enum ety =>
    if !enumAdmittedComp ety then none
    else
      match ety.tagRepr with
      | .zeroSized => some ⟨0, 0⟩
      | .scalar tagW _ => some (intLayoutComp tagW)
  | .tuple [.int w _, .bool] => some (overflowPairLayoutComp w)
  | _ => none

/-- Agreement between `layoutOfTyComp` and `layoutOfTy`. -/
theorem layoutOfTyComp_eq (ty : MirTy) : layoutOfTyComp ty = layoutOfTy ty := by
  cases ty with
  | int w _ =>
    dsimp only [layoutOfTyComp, layoutOfTy]
    rw [intLayoutComp_eq]
  | enum ety =>
    dsimp only [layoutOfTyComp, layoutOfTy]
    rw [enumAdmittedComp_eq]
    cases ety.tagRepr <;> first | rfl | (dsimp only; rw [intLayoutComp_eq])
  | tuple fs =>
    cases fs with
    | nil => rfl
    | cons t1 r1 =>
      cases t1 with
      | int w _ =>
        cases r1 with
        | nil => rfl
        | cons t2 r2 =>
          cases t2 with
          | bool =>
            cases r2 with
            | nil => dsimp only [layoutOfTyComp, layoutOfTy]; rw [overflowPairLayoutComp_eq]
            | cons _ _ => rfl
          | int _ _ | char | ordering | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _
          | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => rfl
      | bool | char | ordering | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _
      | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => rfl
  | bool | char | ordering | unit | never | ref _ _ | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _
  | rangeFrom _ | range _ | option _ | unsupported => rfl

/-- Computable mirror of `Trusted.MirSemantics.entryMemory`. -/
@[expose] def entryMemoryComp : MemoryState := { nextAllocId := 2, allocations := [] }

/-- Agreement between `entryMemoryComp` and `entryMemory`. -/
theorem entryMemoryComp_eq : entryMemoryComp = entryMemory := rfl

/-- Computable mirror of `Trusted.MirSemantics.findAllocation`. -/
@[expose] def findAllocationComp (id : AllocId) (xs : List Allocation) : Option Allocation :=
  List.foldr (fun a acc => if Nat.beq a.allocId id then some a else acc) none xs

/-- Agreement between `findAllocationComp` and `findAllocation`. -/
theorem findAllocationComp_eq (id : AllocId) (xs : List Allocation) :
    findAllocationComp id xs = findAllocation id xs := by
  induction xs with
  | nil => rfl
  | cons a tl ih =>
    change (if Nat.beq a.allocId id then some a else findAllocationComp id tl) =
      (if Nat.beq a.allocId id then some a else findAllocation id tl)
    rw [ih]

/-- Computable mirror of `Trusted.MirSemantics.replaceAllocation`. -/
@[expose] def replaceAllocationComp (a' : Allocation) (xs : List Allocation) : List Allocation :=
  (List.foldr
    (fun (a : Allocation) (acc : List Allocation × List Allocation) =>
      (a :: acc.1,
       if Nat.beq a.allocId a'.allocId then a' :: acc.1 else a :: acc.2))
    ([], [])
    xs).2

private theorem replaceAllocationComp_fst (a' : Allocation) (xs : List Allocation) :
    (List.foldr
      (fun (a : Allocation) (acc : List Allocation × List Allocation) =>
        (a :: acc.1,
         if Nat.beq a.allocId a'.allocId then a' :: acc.1 else a :: acc.2))
      ([], [])
      xs).1 = xs := by
  induction xs with
  | nil => rfl
  | cons a _ ih => exact congrArg (List.cons a) ih

/-- Agreement between `replaceAllocationComp` and `replaceAllocation`. -/
theorem replaceAllocationComp_eq (a' : Allocation) (xs : List Allocation) :
    replaceAllocationComp a' xs = replaceAllocation a' xs := by
  induction xs with
  | nil => rfl
  | cons a tl ih =>
    change (if Nat.beq a.allocId a'.allocId then a' :: (List.foldr _ ([], []) tl).1
        else a :: replaceAllocationComp a' tl) =
      (if Nat.beq a.allocId a'.allocId then a' :: tl else a :: replaceAllocation a' tl)
    rw [replaceAllocationComp_fst a' tl, ih]

/-- Computable mirror of `Trusted.MirSemantics.deallocateStack`. -/
@[expose] def deallocateStackComp (m : MemoryState) (place : MemPlace) : Except FaultKind MemoryState :=
  if !Nat.beq place.offset 0 then .error .undefined
  else
    match findAllocationComp place.allocId m.allocations with
    | none => .error .undefined
    | some a =>
      if !a.live then .error .undefined
      else
        match a.mutability with
        | .shared => .error .undefined
        | .mut =>
          .ok { m with
            allocations := replaceAllocationComp { a with live := false } m.allocations }

/-- Agreement between `deallocateStackComp` and `deallocateStack`. -/
theorem deallocateStackComp_eq (m : MemoryState) (place : MemPlace) :
    deallocateStackComp m place = deallocateStack m place := by
  unfold deallocateStackComp deallocateStack
  rw [findAllocationComp_eq]
  cases findAllocation place.allocId m.allocations with
  | none => rfl
  | some a =>
    dsimp only
    cases a.mutability <;> dsimp only <;> first | rfl | rw [replaceAllocationComp_eq]

/-- Computable mirror of `Trusted.MirSemantics.isInBounds`. -/
@[expose] def isInBoundsComp (a : Allocation) (offset size : Nat) : Bool :=
  Nat.ble (offset + size) a.bytes.length

/-- Computable mirror of `Trusted.MirSemantics.isAligned`. -/
@[expose] def isAlignedComp (a : Allocation) (offset alignLog2 : Nat) : Bool :=
  Nat.ble alignLog2 a.alignLog2 &&
    Nat.beq (Nat.mod offset (Nat.pow 2 alignLog2)) 0

/-- Computable mirror of `Trusted.MirSemantics.readBytes`. -/
@[expose] def readBytesComp (m : MemoryState) (place : MemPlace) (size alignLog2 : Nat) :
    Except FaultKind (List AllocByte) :=
  match findAllocationComp place.allocId m.allocations with
  | none => .error .undefined
  | some a =>
    if Nat.beq size 0 then
      if !isAlignedComp a place.offset alignLog2 then
        .error .undefined
      else
        .ok []
    else if !a.live || !isInBoundsComp a place.offset size ||
        !isAlignedComp a place.offset alignLog2 then
      .error .undefined
    else
      .ok ((a.bytes.drop place.offset).take size)

/-- Agreement between `readBytesComp` and `readBytes`. -/
theorem readBytesComp_eq (m : MemoryState) (place : MemPlace) (size alignLog2 : Nat) :
    readBytesComp m place size alignLog2 = readBytes m place size alignLog2 := by
  unfold readBytesComp readBytes isInBoundsComp isInBounds isAlignedComp isAligned
  rw [findAllocationComp_eq]
  cases findAllocation place.allocId m.allocations <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.writeBytes`. -/
@[expose] def writeBytesComp (m : MemoryState) (place : MemPlace) (alignLog2 : Nat)
    (bytes : List AllocByte) : Except FaultKind MemoryState :=
  match findAllocationComp place.allocId m.allocations with
  | none => .error .undefined
  | some a =>
    if Nat.beq bytes.length 0 then
      if !isAlignedComp a place.offset alignLog2 then
        .error .undefined
      else
        .ok m
    else if !a.live || !isInBoundsComp a place.offset bytes.length ||
        !isAlignedComp a place.offset alignLog2 then
      .error .undefined
    else
      match a.mutability with
      | .shared => .error .undefined
      | .mut =>
        let bytes' :=
          a.bytes.take place.offset ++ bytes ++ a.bytes.drop (place.offset + bytes.length)
        .ok { m with
          allocations := replaceAllocationComp { a with bytes := bytes' } m.allocations }

/-- Agreement between `writeBytesComp` and `writeBytes`. -/
theorem writeBytesComp_eq (m : MemoryState) (place : MemPlace) (alignLog2 : Nat)
    (bytes : List AllocByte) :
    writeBytesComp m place alignLog2 bytes = writeBytes m place alignLog2 bytes := by
  unfold writeBytesComp writeBytes isInBoundsComp isInBounds isAlignedComp isAligned
  rw [findAllocationComp_eq]
  cases findAllocation place.allocId m.allocations with
  | none => rfl
  | some a =>
    dsimp only
    cases a.mutability <;>
      first | rfl | (dsimp only; rw [replaceAllocationComp_eq]) | rw [replaceAllocationComp_eq]

/-- Computable mirror of `Trusted.MirSemantics.writeUninit`. -/
@[expose] def writeUninitComp (m : MemoryState) (place : MemPlace) (size alignLog2 : Nat) :
    Except FaultKind MemoryState :=
  writeBytesComp m place alignLog2 (List.replicate size .uninit)

/-- Agreement between `writeUninitComp` and `writeUninit`. -/
theorem writeUninitComp_eq (m : MemoryState) (place : MemPlace) (size alignLog2 : Nat) :
    writeUninitComp m place size alignLog2 = writeUninit m place size alignLog2 :=
  writeBytesComp_eq m place alignLog2 (List.replicate size .uninit)

/-- Computable mirror of `Trusted.MirSemantics.evalConstLit`. -/
@[expose] def evalConstLitComp (ty : MirTy) (lit : ConstLit) : Except FaultKind Val :=
  match ty, lit with
  | .int w s, .scalar bits =>
    if !(bv128BeqComp (truncateBitsComp w bits) bits) then .error .unsupported
    else .ok (.scalar ⟨w, s, truncateBitsComp w bits⟩)
  | .bool, .scalar bits =>
    if !(bv128BeqComp (truncateBitsComp .i8 bits) bits) then .error .unsupported
    else
      let v := UInt8.ofNat (truncateBitsComp .i8 bits).toNat
      if uint8BeqComp v 0 then .ok (.bool false)
      else if uint8BeqComp v 1 then .ok (.bool true)
      else .error .undefined
  | .unit, .zeroSized => .ok .unit
  | .char, .scalar bits =>
    if !(bv128BeqComp (truncateBitsComp .i32 bits) bits) then .error .unsupported
    else if isUnicodeScalarComp bits.toNat then .ok (.char (Char.ofNat bits.toNat))
    else .error .undefined
  | .ordering, .scalar bits =>
    if !(bv128BeqComp (truncateBitsComp .i8 bits) bits) then .error .unsupported
    else
      match orderingOfTagBitsComp bits.toNat with
      | some ord => .ok (.ordering ord)
      | none => .error .undefined
  | .enum ety, .zeroSized =>
    if isZstEnumTyComp ety then .ok (.enumVal ety 0) else .error .unsupported
  | .enum ety, .scalar bits =>
    match ety.tagRepr with
    | .zeroSized => .error .unsupported
    | .scalar tagW tagS =>
      if !enumAdmittedComp ety || !(bv128BeqComp (truncateBitsComp tagW bits) bits) then
        .error .unsupported
      else
        let discrBits := tagBitsToDiscrBitsComp tagW tagS ety.discrWidth bits
        match findDiscrVariant?Comp discrBits ety.discriminants with
        | some v => .ok (.enumVal ety v)
        | none => .error .undefined
  | _, _ => .error .unsupported

/-- Agreement between `evalConstLitComp` and `evalConstLit`. -/
theorem evalConstLitComp_eq (ty : MirTy) (lit : ConstLit) :
    evalConstLitComp ty lit = evalConstLit ty lit := by
  cases ty with
  | bool =>
    cases lit with
    | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => rfl
    | scalar bits =>
      dsimp only [evalConstLitComp, evalConstLit]
      rw [bv128BneComp_eq, truncateBitsComp_eq, uint8BeqComp_eq_beq, uint8BeqComp_eq_beq]
  | int w s =>
    cases lit with
    | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => rfl
    | scalar bits =>
      dsimp only [evalConstLitComp, evalConstLit]
      rw [bv128BneComp_eq, truncateBitsComp_eq]
  | char =>
    cases lit with
    | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => rfl
    | scalar bits =>
      dsimp only [evalConstLitComp, evalConstLit, isUnicodeScalarComp, isUnicodeScalar]
      rw [bv128BneComp_eq, truncateBitsComp_eq]
      exact rfl
  | ordering =>
    cases lit with
    | zeroSized | rodataBytes _ | rodataRef _ _ _ _ => rfl
    | scalar bits =>
      dsimp only [evalConstLitComp, evalConstLit]
      rw [bv128BneComp_eq, truncateBitsComp_eq]
      have hOrd : orderingOfTagBitsComp bits.toNat = orderingOfTagBits bits.toNat := rfl
      rw [hOrd]
      cases orderingOfTagBits bits.toNat <;> rfl
  | enum ety =>
    cases lit with
    | zeroSized => dsimp only [evalConstLitComp, evalConstLit]; rw [isZstEnumTyComp_eq]
    | rodataBytes _ | rodataRef _ _ _ _ => rfl
    | scalar bits =>
      dsimp only [evalConstLitComp, evalConstLit]
      cases ety.tagRepr with
      | zeroSized => rfl
      | scalar tagW tagS =>
        dsimp only
        rw [enumAdmittedComp_eq, bv128BneComp_eq, truncateBitsComp_eq,
          tagBitsToDiscrBitsComp_eq, findDiscrVariant?Comp_eq]
        cases findDiscrVariant?
          (tagBitsToDiscrBits tagW tagS ety.discrWidth bits) ety.discriminants <;> rfl
  | unit | never | tuple _ | ref _ _ | rawPtr _ _ | slice _ | str | array _ _
  | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported =>
    cases lit <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.leBytesOfNat`. -/
@[expose] def leBytesOfNatComp (n value : Nat) : List UInt8 :=
  @Nat.rec (fun _ => Nat → List UInt8)
    (fun _ => [])
    (fun _ ih v => UInt8.ofNat (Nat.mod v 256) :: ih (Nat.div v 256))
    n value

/-- Agreement between `leBytesOfNatComp` and `leBytesOfNat`. -/
theorem leBytesOfNatComp_eq (n value : Nat) :
    leBytesOfNatComp n value = leBytesOfNat n value := by
  induction n generalizing value with
  | zero => rfl
  | succ _ ih =>
    change UInt8.ofNat (Nat.mod value 256) :: leBytesOfNatComp _ (Nat.div value 256) =
      UInt8.ofNat (Nat.mod value 256) :: leBytesOfNat _ (Nat.div value 256)
    rw [ih]

/-- Computable mirror of `Trusted.MirSemantics.encodeUInt`. -/
@[expose] def encodeUIntComp (endian : TargetEndian) (n value : Nat) : List UInt8 :=
  match endian with
  | .little => leBytesOfNatComp n value
  | .big => (leBytesOfNatComp n value).reverse

/-- Agreement between `encodeUIntComp` and `encodeUInt`. -/
theorem encodeUIntComp_eq (endian : TargetEndian) (n value : Nat) :
    encodeUIntComp endian n value = encodeUInt endian n value := by
  cases endian <;> (unfold encodeUIntComp encodeUInt; rw [leBytesOfNatComp_eq])

/-- Computable mirror of `Trusted.MirSemantics.natOfLeBytes`. -/
@[expose] def natOfLeBytesComp (bytes : List UInt8) : Nat :=
  List.foldr (fun b acc => b.toNat + 256 * acc) 0 bytes

/-- Agreement between `natOfLeBytesComp` and `natOfLeBytes`. -/
theorem natOfLeBytesComp_eq (bytes : List UInt8) :
    natOfLeBytesComp bytes = natOfLeBytes bytes := by
  induction bytes with
  | nil => rfl
  | cons b tl ih =>
    change b.toNat + 256 * natOfLeBytesComp tl = b.toNat + 256 * natOfLeBytes tl
    rw [ih]

/-- Computable mirror of `Trusted.MirSemantics.decodeUInt`. -/
@[expose] def decodeUIntComp (endian : TargetEndian) (bytes : List UInt8) : Nat :=
  match endian with
  | .little => natOfLeBytesComp bytes
  | .big => natOfLeBytesComp bytes.reverse

/-- Agreement between `decodeUIntComp` and `decodeUInt`. -/
theorem decodeUIntComp_eq (endian : TargetEndian) (bytes : List UInt8) :
    decodeUIntComp endian bytes = decodeUInt endian bytes := by
  cases endian <;> (dsimp only [decodeUIntComp, decodeUInt]; rw [natOfLeBytesComp_eq])

/-- Computable mirror of `Trusted.MirSemantics.initBytes?`. -/
@[expose] def initBytes?Comp (bytes : List AllocByte) : Option (List UInt8) :=
  List.foldr
    (fun ab acc =>
      match ab with
      | .uninit => none
      | .init b _ =>
        match acc with
        | some bs => some (b :: bs)
        | none => none)
    (some [])
    bytes

/-- Agreement between `initBytes?Comp` and `initBytes?`. -/
theorem initBytes?Comp_eq (bytes : List AllocByte) :
    initBytes?Comp bytes = initBytes? bytes := by
  induction bytes with
  | nil => rfl
  | cons ab tl ih =>
    cases ab with
    | uninit => rfl
    | init b _ =>
      change (match initBytes?Comp tl with | some bs => some (b :: bs) | none => none) =
        (match initBytes? tl with | some bs => some (b :: bs) | none => none)
      rw [ih]

/-- Computable mirror of `Trusted.MirSemantics.decodeVal`. -/
@[expose] def decodeValComp (endian : TargetEndian) (ty : MirTy) (bytes : List AllocByte) :
    Except FaultKind (Option Val) :=
  match ty with
  | .never => .ok none
  | .tuple [.int w s, .bool] =>
    if !Nat.beq bytes.length (overflowPairLayoutComp w).size then .error .unsupported
    else
      match initBytes?Comp (bytes.take (byteSizeComp w)),
          initBytes?Comp ((bytes.drop (byteSizeComp w)).take 1) with
      | some intRaw, some boolRaw =>
        match evalConstLitComp (.int w s)
            (.scalar (BitVec.ofNat 128 (decodeUIntComp endian intRaw))) with
        | .error k => .error k
        | .ok intVal =>
          match evalConstLitComp .bool
              (.scalar (BitVec.ofNat 128 (decodeUIntComp endian boolRaw))) with
          | .error k => .error k
          | .ok boolVal => .ok (some (.tuple [intVal, boolVal]))
      | _, _ => .ok none
  | _ =>
    match layoutOfTyComp ty with
    | none => .error .unsupported
    | some layout =>
      if !Nat.beq bytes.length layout.size then .error .unsupported
      else if Nat.beq layout.size 0 then
        match evalConstLitComp ty .zeroSized with
        | .ok v => .ok (some v)
        | .error k => .error k
      else
        match initBytes?Comp bytes with
        | none => .ok none
        | some raw =>
          match evalConstLitComp ty
              (.scalar (BitVec.ofNat 128 (decodeUIntComp endian raw))) with
          | .ok v => .ok (some v)
          | .error k => .error k

/-- Agreement between `decodeValComp` and `decodeVal`. -/
theorem decodeValComp_eq (endian : TargetEndian) (ty : MirTy) (bytes : List AllocByte) :
    decodeValComp endian ty bytes = decodeVal endian ty bytes := by
  cases ty with
  | never => rfl
  | tuple fs =>
    cases fs with
    | nil => rfl
    | cons t1 r1 =>
      cases t1 with
      | int w s =>
        cases r1 with
        | nil => rfl
        | cons t2 r2 =>
          cases t2 with
          | bool =>
            cases r2 with
            | cons _ _ => rfl
            | nil =>
              dsimp only [decodeValComp, decodeVal]
              rw [overflowPairLayoutComp_eq, byteSizeComp_eq,
                initBytes?Comp_eq, initBytes?Comp_eq]
              cases initBytes? (bytes.take w.byteSize) with
              | none => rfl
              | some intRaw =>
                cases initBytes? ((bytes.drop w.byteSize).take 1) with
                | none => rfl
                | some boolRaw =>
                  dsimp only
                  rw [decodeUIntComp_eq, evalConstLitComp_eq,
                    decodeUIntComp_eq, evalConstLitComp_eq]
                  cases evalConstLit (.int w s)
                    (.scalar (BitVec.ofNat 128 (decodeUInt endian intRaw))) with
                  | error _ => rfl
                  | ok _ =>
                    cases evalConstLit .bool
                      (.scalar (BitVec.ofNat 128 (decodeUInt endian boolRaw))) <;> rfl
          | int _ _ | char | ordering | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _
          | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => rfl
      | bool | char | ordering | unit | never | enum _ | tuple _ | ref _ _ | rawPtr _ _
      | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported => rfl
  | bool | int _ _ | char | ordering | unit | enum _ | ref _ _ | rawPtr _ _
  | slice _ | str | array _ _ | rangeTo _ | rangeFrom _ | range _ | option _ | unsupported =>
    dsimp only [decodeValComp, decodeVal]
    rw [layoutOfTyComp_eq]
    cases layoutOfTy _ with
    | none => rfl
    | some layout =>
      dsimp only
      rw [evalConstLitComp_eq, initBytes?Comp_eq]
      cases Nat.beq layout.size 0 with
      | true =>
        cases evalConstLit _ .zeroSized <;> rfl
      | false =>
        cases initBytes? bytes with
        | none => rfl
        | some raw =>
          dsimp only
          rw [decodeUIntComp_eq, evalConstLitComp_eq]
          cases evalConstLit _ (.scalar (BitVec.ofNat 128 (decodeUInt endian raw))) <;> rfl

/-- Computable mirror of `Trusted.MirSemantics.loadIndirect`. -/
@[expose] def loadIndirectComp (mem : MemoryState) (ty : MirTy) (place : MemPlace) :
    Except FaultKind (Option Val) :=
  match layoutOfTyComp ty with
  | none => .error .unsupported
  | some layout =>
    match readBytesComp mem place layout.size layout.alignLog2 with
    | .error k => .error k
    | .ok bytes => decodeValComp .big ty bytes

/-- Agreement between `loadIndirectComp` and `loadIndirect`. -/
theorem loadIndirectComp_eq (mem : MemoryState) (ty : MirTy) (place : MemPlace) :
    loadIndirectComp mem ty place = loadIndirect mem ty place := by
  unfold loadIndirectComp loadIndirect profileTargetEndian
  rw [layoutOfTyComp_eq]
  cases layoutOfTy ty with
  | none => rfl
  | some layout =>
    dsimp only
    rw [readBytesComp_eq]
    cases readBytes mem place layout.size layout.alignLog2 with
    | error _ => rfl
    | ok bytes => exact decodeValComp_eq .big ty bytes

/-- Computable mirror of `Trusted.MirSemantics.deinitIndirect`. -/
@[expose] def deinitIndirectComp (mem : MemoryState) (ty : MirTy) (place : MemPlace) :
    Except FaultKind MemoryState :=
  match layoutOfTyComp ty with
  | none => .error .unsupported
  | some layout => writeUninitComp mem place layout.size layout.alignLog2

/-- Agreement between `deinitIndirectComp` and `deinitIndirect`. -/
theorem deinitIndirectComp_eq (mem : MemoryState) (ty : MirTy) (place : MemPlace) :
    deinitIndirectComp mem ty place = deinitIndirect mem ty place := by
  unfold deinitIndirectComp deinitIndirect
  rw [layoutOfTyComp_eq]
  cases layoutOfTy ty with
  | none => rfl
  | some layout => exact writeUninitComp_eq mem place layout.size layout.alignLog2

/-- Computable mirror of `Trusted.MirSemantics.deallocateLocal`. -/
@[expose] def deallocateLocalComp (mem : MemoryState) (slot : LocalSlot) :
    Except FaultKind MemoryState :=
  match slot with
  | .indirect mplace => deallocateStackComp mem mplace
  | _ => .ok mem

/-- Agreement between `deallocateLocalComp` and `deallocateLocal`. -/
theorem deallocateLocalComp_eq (mem : MemoryState) (slot : LocalSlot) :
    deallocateLocalComp mem slot = deallocateLocal mem slot := by
  cases slot <;> first | rfl | exact deallocateStackComp_eq mem _

end Anneal.MirTotal

end
