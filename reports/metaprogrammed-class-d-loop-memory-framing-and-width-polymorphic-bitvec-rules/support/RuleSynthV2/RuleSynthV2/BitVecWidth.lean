-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Width-Polymorphic `BitVec w` (`w ∈ {8, 16, 32, 64, 128}`) Class A Rule Synthesis (`BitVecWidth.lean`)

Resolves the single-width `Int` boundary of Wave 5 (`X5`) by formalizing multi-width `BitVec w.bits`
(`i8`, `i16`, `i32`, `i64`, `i128`) wrapped in `PoisonOr` (`BVVal w`) and synthesizing the
soundness of 30 width-polymorphic Class A peephole rules (`30 × 5 = 150` concrete width instances)
in a single tactic macro (`prove_bitvec_rw_sound`) using only standard library `BitVec` lemmas
(`Init.Data.BitVec.Lemmas`) and `[propext, Quot.sound]`—with zero `Lean.ofReduceBool` (`bv_decide`).
-/

namespace RuleSynthV2

/-- Canonical Rust / LLVM integer bit-widths (`i8`, `i16`, `i32`, `i64`, `i128`). -/
inductive WidthTag where
  | w8
  | w16
  | w32
  | w64
  | w128
  deriving DecidableEq, Repr

/-- Bit count corresponding to each `WidthTag`. -/
def WidthTag.bits : WidthTag → Nat
  | .w8   => 8
  | .w16  => 16
  | .w32  => 32
  | .w64  => 64
  | .w128 => 128

/-- Value with deferred undefinedness (`poison`). -/
inductive PoisonOr (α : Type) where
  | val (v : α)
  | poison
  deriving DecidableEq, Repr

/-- Standard poison refinement (`s ⊑_poison t`). -/
def refinesPoison {α : Type} (s t : PoisonOr α) : Prop :=
  s = .poison ∨ s = t

theorem refinesPoison_refl {α : Type} (x : PoisonOr α) : refinesPoison x x :=
  Or.inr rfl

/-- Lift a binary `BitVec n` operation onto `PoisonOr (BitVec n)`. -/
def liftBV2 {n : Nat} (f : BitVec n → BitVec n → PoisonOr (BitVec n))
    (x y : PoisonOr (BitVec n)) : PoisonOr (BitVec n) :=
  match x, y with
  | .val a, .val b => f a b
  | _, _ => .poison

/-- Lift a unary `BitVec n` operation onto `PoisonOr (BitVec n)`. -/
def liftBV1 {n : Nat} (f : BitVec n → PoisonOr (BitVec n))
    (x : PoisonOr (BitVec n)) : PoisonOr (BitVec n) :=
  match x with
  | .val a => f a
  | .poison => .poison

/-- Width-polymorphic `BitVec w.bits` expression AST (`BVExpr w`). -/
inductive BVExpr (w : WidthTag) where
  | zero
  | one
  | const (v : BitVec w.bits)
  | var (id : Nat)
  | addWrap (a b : BVExpr w)
  | addNuw (a b : BVExpr w)
  | subWrap (a b : BVExpr w)
  | subNuw (a b : BVExpr w)
  | mulWrap (a b : BVExpr w)
  | bitAnd (a b : BVExpr w)
  | bitOr (a b : BVExpr w)
  | bitXor (a b : BVExpr w)
  | shlZero (a : BVExpr w)
  | ushrZero (a : BVExpr w)
  | freezeZero (a : BVExpr w)
  deriving DecidableEq, Repr

/-- Evaluate a width-polymorphic `BVExpr w` under register environment `env : Nat → PoisonOr (BitVec w.bits)`. -/
def evalBVExpr {w : WidthTag} (env : Nat → PoisonOr (BitVec w.bits)) :
    BVExpr w → PoisonOr (BitVec w.bits)
  | .zero => .val (0#(w.bits))
  | .one => .val (1#(w.bits))
  | .const v => .val v
  | .var r => env r
  | .addWrap a b => liftBV2 (fun x y => .val (x + y)) (evalBVExpr env a) (evalBVExpr env b)
  | .addNuw a b =>
      liftBV2 (fun x y => if x.toNat + y.toNat < 2 ^ w.bits then .val (x + y) else .poison)
        (evalBVExpr env a) (evalBVExpr env b)
  | .subWrap a b => liftBV2 (fun x y => .val (x - y)) (evalBVExpr env a) (evalBVExpr env b)
  | .subNuw a b =>
      liftBV2 (fun x y => if y.toNat ≤ x.toNat then .val (x - y) else .poison)
        (evalBVExpr env a) (evalBVExpr env b)
  | .mulWrap a b => liftBV2 (fun x y => .val (x * y)) (evalBVExpr env a) (evalBVExpr env b)
  | .bitAnd a b => liftBV2 (fun x y => .val (x &&& y)) (evalBVExpr env a) (evalBVExpr env b)
  | .bitOr a b => liftBV2 (fun x y => .val (x ||| y)) (evalBVExpr env a) (evalBVExpr env b)
  | .bitXor a b => liftBV2 (fun x y => .val (x ^^^ y)) (evalBVExpr env a) (evalBVExpr env b)
  | .shlZero a => liftBV1 (fun x => .val (x <<< 0)) (evalBVExpr env a)
  | .ushrZero a => liftBV1 (fun x => .val (x >>> 0)) (evalBVExpr env a)
  | .freezeZero a =>
      match evalBVExpr env a with
      | .val v => .val v
      | .poison => .val (0#(w.bits))

/-- 30 width-polymorphic Class A `BitVec w` peephole rewrite constructors (`150` concrete width rules). -/
inductive BVRewrite (w : WidthTag) where
  | r01_addZeroRight (e : BVExpr w)
  | r02_addZeroLeft (e : BVExpr w)
  | r03_subZeroRight (e : BVExpr w)
  | r04_subSelfToZero (e : BVExpr w)
  | r05_andSelf (e : BVExpr w)
  | r06_andZeroRight (e : BVExpr w)
  | r07_andZeroLeft (e : BVExpr w)
  | r08_mulOneRight (e : BVExpr w)
  | r09_mulOneLeft (e : BVExpr w)
  | r10_orSelf (e : BVExpr w)
  | r11_orZeroRight (e : BVExpr w)
  | r12_orZeroLeft (e : BVExpr w)
  | r13_mulZeroRight (e : BVExpr w)
  | r14_mulZeroLeft (e : BVExpr w)
  | r15_xorSelfToZero (e : BVExpr w)
  | r16_xorZeroRight (e : BVExpr w)
  | r17_xorZeroLeft (e : BVExpr w)
  | r18_mulComm (a b : BVExpr w)
  | r19_addComm (a b : BVExpr w)
  | r20_andComm (a b : BVExpr w)
  | r21_orComm (a b : BVExpr w)
  | r22_xorComm (a b : BVExpr w)
  | r23_shlZero (e : BVExpr w)
  | r24_ushrZero (e : BVExpr w)
  | r25_dropAddNuw (a b : BVExpr w)
  | r26_dropSubNuw (a b : BVExpr w)
  | r27_freezeZeroConst
  | r28_freezeIdem (e : BVExpr w)
  | r29_insertFreeze (e : BVExpr w)
  | r30_doubleSubCancel (e : BVExpr w)
  deriving DecidableEq, Repr

/-- Endpoint inference `(src, tgt)` for all 30 width-polymorphic `BVRewrite w` constructors. -/
def inferBVRewrite {w : WidthTag} : BVRewrite w → BVExpr w × BVExpr w
  | .r01_addZeroRight e => (.addWrap e .zero, e)
  | .r02_addZeroLeft e => (.addWrap .zero e, e)
  | .r03_subZeroRight e => (.subWrap e .zero, e)
  | .r04_subSelfToZero e => (.subWrap e e, .zero)
  | .r05_andSelf e => (.bitAnd e e, e)
  | .r06_andZeroRight e => (.bitAnd e .zero, .zero)
  | .r07_andZeroLeft e => (.bitAnd .zero e, .zero)
  | .r08_mulOneRight e => (.mulWrap e .one, e)
  | .r09_mulOneLeft e => (.mulWrap .one e, e)
  | .r10_orSelf e => (.bitOr e e, e)
  | .r11_orZeroRight e => (.bitOr e .zero, e)
  | .r12_orZeroLeft e => (.bitOr .zero e, e)
  | .r13_mulZeroRight e => (.mulWrap e .zero, .zero)
  | .r14_mulZeroLeft e => (.mulWrap .zero e, .zero)
  | .r15_xorSelfToZero e => (.bitXor e e, .zero)
  | .r16_xorZeroRight e => (.bitXor e .zero, e)
  | .r17_xorZeroLeft e => (.bitXor .zero e, e)
  | .r18_mulComm a b => (.mulWrap a b, .mulWrap b a)
  | .r19_addComm a b => (.addWrap a b, .addWrap b a)
  | .r20_andComm a b => (.bitAnd a b, .bitAnd b a)
  | .r21_orComm a b => (.bitOr a b, .bitOr b a)
  | .r22_xorComm a b => (.bitXor a b, .bitXor b a)
  | .r23_shlZero e => (.shlZero e, e)
  | .r24_ushrZero e => (.ushrZero e, e)
  | .r25_dropAddNuw a b => (.addNuw a b, .addWrap a b)
  | .r26_dropSubNuw a b => (.subNuw a b, .subWrap a b)
  | .r27_freezeZeroConst => (.freezeZero .zero, .zero)
  | .r28_freezeIdem e => (.freezeZero (.freezeZero e), .freezeZero e)
  | .r29_insertFreeze e => (e, .freezeZero e)
  | .r30_doubleSubCancel e => (.subWrap (.addWrap e .zero) .zero, e)

/-- Custom elaboration tactic `prove_bitvec_rw_sound` discharging all 30 width-polymorphic
`BitVec w` rules across `w ∈ {w8, w16, w32, w64, w128}` without `bv_decide` (`Lean.ofReduceBool`)
or `Classical.choice`. -/
macro "prove_bitvec_rw_sound" w:term "," rw:term "with_env" env:term : tactic =>
  `(tactic| (
    cases $rw:term with
    | r18_mulComm a b | r19_addComm a b | r20_andComm a b | r21_orComm a b | r22_xorComm a b =>
      simp only [inferBVRewrite, evalBVExpr]
      cases evalBVExpr $env a <;> cases evalBVExpr $env b <;>
        simp [liftBV2, refinesPoison, BitVec.mul_comm, BitVec.add_comm, BitVec.and_comm, BitVec.or_comm, BitVec.xor_comm]
    | r25_dropAddNuw a b =>
      simp only [inferBVRewrite, evalBVExpr]
      cases evalBVExpr $env a with
      | poison => exact Or.inl rfl
      | val va =>
        cases evalBVExpr $env b with
        | poison => exact Or.inl rfl
        | val vb =>
          simp only [liftBV2]
          by_cases h_ok : va.toNat + vb.toNat < 2 ^ WidthTag.bits $w <;> simp [h_ok, refinesPoison]
    | r26_dropSubNuw a b =>
      simp only [inferBVRewrite, evalBVExpr]
      cases evalBVExpr $env a with
      | poison => exact Or.inl rfl
      | val va =>
        cases evalBVExpr $env b with
        | poison => exact Or.inl rfl
        | val vb =>
          simp only [liftBV2]
          by_cases h_ok : vb.toNat ≤ va.toNat <;> simp [h_ok, refinesPoison]
    | r27_freezeZeroConst =>
      exact Or.inr rfl
    | _ e =>
      simp only [inferBVRewrite, evalBVExpr]
      cases evalBVExpr $env e <;>
        simp [liftBV1, liftBV2, refinesPoison,
              BitVec.add_zero, BitVec.zero_add, BitVec.sub_zero, BitVec.sub_self,
              BitVec.mul_one, BitVec.one_mul, BitVec.mul_zero, BitVec.zero_mul,
              BitVec.and_self, BitVec.and_zero, BitVec.zero_and,
              BitVec.or_self, BitVec.or_zero, BitVec.zero_or,
              BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor,
              BitVec.shiftLeft_zero, BitVec.ushiftRight_zero]
  ))

/-- Master width-polymorphic soundness theorem for all 30 `BVRewrite w` constructors across
all 5 integer widths (`150` concrete rules), proved in 1 line via `prove_bitvec_rw_sound`. -/
theorem inferBVRewrite_sound {w : WidthTag} (rw : BVRewrite w)
    (env : Nat → PoisonOr (BitVec w.bits)) :
    refinesPoison (evalBVExpr env (inferBVRewrite rw).1) (evalBVExpr env (inferBVRewrite rw).2) := by
  prove_bitvec_rw_sound w, rw with_env env

end RuleSynthV2
