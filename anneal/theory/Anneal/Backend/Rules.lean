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
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.Data.Option.Basic
public import Anneal.InitLemmas
public import Anneal.NatBitwise

public section

/-!
# Arena-Free E-Graph Rewrite Algebra and `PoisonOr` (`Anneal.Backend.Rules`)

Decouples pure 64-bit SSA expression semantics (`PoisonOr Nat`), two-polarity
relations (`RelKind.eqExact` vs. `RelKind.refines`), `freeze` monotonicity
guards (`SsaOp.isPoisonMonotone`, `LetBody.isFreezeFree`), and algebraic and
contextual rewrite rules (`BiEqRule`, `DirRefineRule`) from any DAG arena or
proof-trace representation.

Keeping `Rules` arena-free ensures that both offline DAG trace validation
(`Anneal.Backend.CongruenceDagCtx`) and direct pass proofs reuse the same
per-rule soundness theorems.
-/

namespace Anneal.Backend

open Anneal.InitLemmas

/-! ## 1. 64-Bit Word Constants and Normalization -/

/-- `2 ^ 64`, the modulus of 64-bit unsigned arithmetic. -/
@[expose] def u64Mod : Nat := 18446744073709551616

/-- `2 ^ 64 - 1`, the maximum 64-bit unsigned value (`usize::MAX` on LP64). -/
@[expose] def u64Max : Nat := 18446744073709551615

/-- `2 ^ 61 - 1` (`0x1fff_ffff_ffff_ffff`), stride bitmask in 10-bit codecs. -/
@[expose] def mask61 : Nat := 2305843009213693951

/-- `2 ^ 61`, exclusive bound permitting `mask61` elision. -/
@[expose] def pow2_61 : Nat := 2305843009213693952

/-- Normalize a natural number to its 64-bit unsigned residue. -/
@[expose] def word64 (n : Nat) : Nat := Nat.mod n u64Mod

theorem u64Mod_pos : 0 < u64Mod := by decide

theorem u64Max_lt : u64Max < u64Mod := by decide

theorem u64Mod_eq_pow : u64Mod = Nat.pow 2 64 := rfl

theorem pow2_61_eq : pow2_61 = Nat.pow 2 61 := rfl

theorem mask61_eq : mask61 = Nat.pow 2 61 - 1 := rfl

theorem word64_lt (n : Nat) : word64 n < u64Mod :=
  nat_mod_lt n u64Mod_pos

theorem word64_of_lt {n : Nat} (h : n < u64Mod) : word64 n = n :=
  nat_mod_eq_of_lt h

theorem word64_idem (n : Nat) : word64 (word64 n) = word64 n :=
  word64_of_lt (word64_lt n)

/-! ## 2. `PoisonOr` Domain and Two-Polarity Relation Algebra -/

/-- Value domain of pure non-trapping SSA expressions: either a defined value
or deferred undefinedness (`.poison`). -/
inductive PoisonOr (α : Type) where
  | val (v : α)
  | poison

/-- A `PoisonOr Nat` value whose defined payload is normalized `< 2 ^ 64`. -/
@[expose] def WellTypedVal : PoisonOr Nat → Prop
  | .poison => True
  | .val v => v < u64Mod

/-- Polarity of a rewrite or congruence claim in the mid-end e-graph:
- `.eqExact`: exact `PoisonOr` equality (`a = b`), closed under `.symm` and
  valid under all contexts including `freeze`.
- `.refines`: directional poison-monotonic refinement (`a = .poison` or
  `a = b`), forbidden under `.symm` and non-monotonic `freeze`. -/
inductive RelKind where
  | eqExact
  | refines

@[expose] def RelKind.beq : RelKind → RelKind → Bool
  | .eqExact, .eqExact => true
  | .refines, .refines => true
  | _, _ => false

/-- Weakest common polarity of two chained steps. -/
@[expose] def RelKind.join : RelKind → RelKind → RelKind
  | .eqExact, .eqExact => .eqExact
  | _, _ => .refines

/-- Whether `actual` is at least as strong as `required`. -/
@[expose] def RelKind.satisfies (actual required : RelKind) : Bool :=
  match actual, required with
  | .eqExact, _ => true
  | .refines, .refines => true
  | .refines, .eqExact => false

/-- Directional poison refinement (`src ⊑_poison tgt`): `tgt` is at least as
defined as `src` and agrees on all non-poison values. -/
@[expose] def refinesPoison {α : Type} (src tgt : PoisonOr α) : Prop :=
  match src, tgt with
  | .poison, _ => True
  | .val a, .val b => a = b
  | .val _, .poison => False

/-- Semantic interpretation of `RelKind`. -/
@[expose] def evalRel {α : Type} : RelKind → PoisonOr α → PoisonOr α → Prop
  | .eqExact, a, b => a = b
  | .refines, a, b => refinesPoison a b

theorem evalRel_refl {α : Type} (x : PoisonOr α) : evalRel .eqExact x x := rfl

theorem evalRel_symm {α : Type} {x y : PoisonOr α}
    (h : evalRel .eqExact x y) : evalRel .eqExact y x :=
  Eq.symm h

theorem refinesPoison_refl {α : Type} (x : PoisonOr α) : refinesPoison x x := by
  cases x with
  | poison => exact True.intro
  | val _ => rfl

theorem refinesPoison_trans {α : Type} {a b c : PoisonOr α}
    (h1 : refinesPoison a b) (h2 : refinesPoison b c) :
    refinesPoison a c := by
  cases a with
  | poison => exact True.intro
  | val va =>
    cases b with
    | poison => exact False.elim h1
    | val vb =>
      cases c with
      | poison => exact False.elim h2
      | val vc => exact Eq.trans h1 h2

theorem evalRel_upgrade {α : Type} {r1 r2 : RelKind} {x y : PoisonOr α}
    (hSat : RelKind.satisfies r1 r2 = true) (h : evalRel r1 x y) :
    evalRel r2 x y := by
  cases r1 with
  | eqExact =>
    cases r2 with
    | eqExact => exact h
    | refines =>
      rw [h]
      exact refinesPoison_refl y
  | refines =>
    cases r2 with
    | eqExact => nomatch hSat
    | refines => exact h

theorem evalRel_trans {α : Type} {r1 r2 : RelKind} {a b c : PoisonOr α}
    (h1 : evalRel r1 a b) (h2 : evalRel r2 b c) :
    evalRel (RelKind.join r1 r2) a c := by
  cases r1 with
  | eqExact =>
    cases r2 with
    | eqExact => exact Eq.trans h1 h2
    | refines =>
      rw [h1]
      exact h2
  | refines =>
    cases r2 with
    | eqExact =>
      rw [← h2]
      exact h1
    | refines => exact refinesPoison_trans h1 h2

/-! ## 3. Poison-Propagating Combinators and SSA Operators -/

/-- Lift a 1-argument word operation strictly over `.poison`. -/
@[expose] def evalUnaryPoison (f : Nat → PoisonOr Nat) :
    PoisonOr Nat → PoisonOr Nat
  | .val a => f (word64 a)
  | .poison => .poison

/-- Lift a 2-argument word operation strictly over `.poison`. -/
@[expose] def evalBinaryPoison (f : Nat → Nat → PoisonOr Nat) :
    PoisonOr Nat → PoisonOr Nat → PoisonOr Nat
  | .val a, .val b => f (word64 a) (word64 b)
  | _, _ => .poison

theorem evalUnaryPoison_mono (f : Nat → PoisonOr Nat) {x y : PoisonOr Nat}
    (h : refinesPoison x y) :
    refinesPoison (evalUnaryPoison f x) (evalUnaryPoison f y) := by
  cases x with
  | poison => exact True.intro
  | val va =>
    cases y with
    | poison => exact False.elim h
    | val vb =>
      dsimp only [refinesPoison] at h
      rw [h]
      exact refinesPoison_refl _

theorem evalBinaryPoison_mono (f : Nat → Nat → PoisonOr Nat)
    {x1 y1 x2 y2 : PoisonOr Nat}
    (h1 : refinesPoison x1 y1) (h2 : refinesPoison x2 y2) :
    refinesPoison (evalBinaryPoison f x1 x2) (evalBinaryPoison f y1 y2) := by
  cases x1 with
  | poison => exact True.intro
  | val va1 =>
    cases x2 with
    | poison =>
      cases y1 with
      | poison => exact False.elim h1
      | val _ => exact True.intro
    | val va2 =>
      cases y1 with
      | poison => exact False.elim h1
      | val vb1 =>
        cases y2 with
        | poison => exact False.elim h2
        | val vb2 =>
          dsimp only [refinesPoison] at h1 h2
          rw [h1, h2]
          exact refinesPoison_refl _

/-- Pure 64-bit SSA expression operators. -/
inductive SsaOp where
  | var (id : Nat)
  | lit (v : Nat)
  | addWrap
  | addNuw
  | subWrap
  | subNuw
  | mulWrap
  | land
  | lor
  | lshr
  | shl
  | bitNot
  | freeze (defaultVal : Nat)

@[expose] def SsaOp.beq : SsaOp → SsaOp → Bool
  | .var a, .var b => Nat.beq a b
  | .lit a, .lit b => Nat.beq a b
  | .addWrap, .addWrap => true
  | .addNuw, .addNuw => true
  | .subWrap, .subWrap => true
  | .subNuw, .subNuw => true
  | .mulWrap, .mulWrap => true
  | .land, .land => true
  | .lor, .lor => true
  | .lshr, .lshr => true
  | .shl, .shl => true
  | .bitNot, .bitNot => true
  | .freeze d1, .freeze d2 => Nat.beq d1 d2
  | _, _ => false

theorem ssaOp_beq_refl (op : SsaOp) : SsaOp.beq op op = true := by
  cases op with
  | var a => exact nat_beq_refl a
  | lit a => exact nat_beq_refl a
  | freeze d => exact nat_beq_refl d
  | _ => rfl

theorem ssaOp_eq_of_beq : ∀ {o1 o2 : SsaOp}, SsaOp.beq o1 o2 = true → o1 = o2
  | .var _a, .var _b, h => congrArg SsaOp.var (nat_eq_of_beq h)
  | .lit _a, .lit _b, h => congrArg SsaOp.lit (nat_eq_of_beq h)
  | .addWrap, .addWrap, _ => rfl
  | .addNuw, .addNuw, _ => rfl
  | .subWrap, .subWrap, _ => rfl
  | .subNuw, .subNuw, _ => rfl
  | .mulWrap, .mulWrap, _ => rfl
  | .land, .land, _ => rfl
  | .lor, .lor, _ => rfl
  | .lshr, .lshr, _ => rfl
  | .shl, .shl, _ => rfl
  | .bitNot, .bitNot, _ => rfl
  | .freeze _d1, .freeze _d2, h => congrArg SsaOp.freeze (nat_eq_of_beq h)
  | .var _, .lit _, h | .var _, .addWrap, h | .var _, .addNuw, h
  | .var _, .subWrap, h | .var _, .subNuw, h | .var _, .mulWrap, h
  | .var _, .land, h | .var _, .lor, h | .var _, .lshr, h
  | .var _, .shl, h | .var _, .bitNot, h | .var _, .freeze _, h => nomatch h
  | .lit _, .var _, h | .lit _, .addWrap, h | .lit _, .addNuw, h
  | .lit _, .subWrap, h | .lit _, .subNuw, h | .lit _, .mulWrap, h
  | .lit _, .land, h | .lit _, .lor, h | .lit _, .lshr, h
  | .lit _, .shl, h | .lit _, .bitNot, h | .lit _, .freeze _, h => nomatch h
  | .addWrap, .var _, h | .addWrap, .lit _, h | .addWrap, .addNuw, h
  | .addWrap, .subWrap, h | .addWrap, .subNuw, h | .addWrap, .mulWrap, h
  | .addWrap, .land, h | .addWrap, .lor, h | .addWrap, .lshr, h
  | .addWrap, .shl, h | .addWrap, .bitNot, h | .addWrap, .freeze _, h =>
    nomatch h
  | .addNuw, .var _, h | .addNuw, .lit _, h | .addNuw, .addWrap, h
  | .addNuw, .subWrap, h | .addNuw, .subNuw, h | .addNuw, .mulWrap, h
  | .addNuw, .land, h | .addNuw, .lor, h | .addNuw, .lshr, h
  | .addNuw, .shl, h | .addNuw, .bitNot, h | .addNuw, .freeze _, h =>
    nomatch h
  | .subWrap, .var _, h | .subWrap, .lit _, h | .subWrap, .addWrap, h
  | .subWrap, .addNuw, h | .subWrap, .subNuw, h | .subWrap, .mulWrap, h
  | .subWrap, .land, h | .subWrap, .lor, h | .subWrap, .lshr, h
  | .subWrap, .shl, h | .subWrap, .bitNot, h | .subWrap, .freeze _, h =>
    nomatch h
  | .subNuw, .var _, h | .subNuw, .lit _, h | .subNuw, .addWrap, h
  | .subNuw, .addNuw, h | .subNuw, .subWrap, h | .subNuw, .mulWrap, h
  | .subNuw, .land, h | .subNuw, .lor, h | .subNuw, .lshr, h
  | .subNuw, .shl, h | .subNuw, .bitNot, h | .subNuw, .freeze _, h =>
    nomatch h
  | .mulWrap, .var _, h | .mulWrap, .lit _, h | .mulWrap, .addWrap, h
  | .mulWrap, .addNuw, h | .mulWrap, .subWrap, h | .mulWrap, .subNuw, h
  | .mulWrap, .land, h | .mulWrap, .lor, h | .mulWrap, .lshr, h
  | .mulWrap, .shl, h | .mulWrap, .bitNot, h | .mulWrap, .freeze _, h =>
    nomatch h
  | .land, .var _, h | .land, .lit _, h | .land, .addWrap, h
  | .land, .addNuw, h | .land, .subWrap, h | .land, .subNuw, h
  | .land, .mulWrap, h | .land, .lor, h | .land, .lshr, h
  | .land, .shl, h | .land, .bitNot, h | .land, .freeze _, h => nomatch h
  | .lor, .var _, h | .lor, .lit _, h | .lor, .addWrap, h
  | .lor, .addNuw, h | .lor, .subWrap, h | .lor, .subNuw, h
  | .lor, .mulWrap, h | .lor, .land, h | .lor, .lshr, h
  | .lor, .shl, h | .lor, .bitNot, h | .lor, .freeze _, h => nomatch h
  | .lshr, .var _, h | .lshr, .lit _, h | .lshr, .addWrap, h
  | .lshr, .addNuw, h | .lshr, .subWrap, h | .lshr, .subNuw, h
  | .lshr, .mulWrap, h | .lshr, .land, h | .lshr, .lor, h
  | .lshr, .shl, h | .lshr, .bitNot, h | .lshr, .freeze _, h => nomatch h
  | .shl, .var _, h | .shl, .lit _, h | .shl, .addWrap, h
  | .shl, .addNuw, h | .shl, .subWrap, h | .shl, .subNuw, h
  | .shl, .mulWrap, h | .shl, .land, h | .shl, .lor, h
  | .shl, .lshr, h | .shl, .bitNot, h | .shl, .freeze _, h => nomatch h
  | .bitNot, .var _, h | .bitNot, .lit _, h | .bitNot, .addWrap, h
  | .bitNot, .addNuw, h | .bitNot, .subWrap, h | .bitNot, .subNuw, h
  | .bitNot, .mulWrap, h | .bitNot, .land, h | .bitNot, .lor, h
  | .bitNot, .lshr, h | .bitNot, .shl, h | .bitNot, .freeze _, h => nomatch h
  | .freeze _, .var _, h | .freeze _, .lit _, h | .freeze _, .addWrap, h
  | .freeze _, .addNuw, h | .freeze _, .subWrap, h | .freeze _, .subNuw, h
  | .freeze _, .mulWrap, h | .freeze _, .land, h | .freeze _, .lor, h
  | .freeze _, .lshr, h | .freeze _, .shl, h | .freeze _, .bitNot, h =>
    nomatch h

/-- `freeze` observes `.poison` and converts it to a concrete fallback constant,
breaking monotonicity under `refinesPoison`. All other `SsaOp` constructors
propagate `.poison` monotonically. -/
@[expose] def SsaOp.isPoisonMonotone : SsaOp → Bool
  | .freeze _ => false
  | _ => true

/-- Evaluate `freeze d` on a `PoisonOr Nat` operand. -/
@[expose] def evalFreeze (d : Nat) : PoisonOr Nat → PoisonOr Nat
  | .val v => .val (word64 v)
  | .poison => .val (word64 d)

/-- Denotational semantics of a single `SsaOp` over evaluated child operands.
Note that `lshr` and `shl` mask shift amounts modulo 64 (`Nat.mod b 64`),
matching Rust's `wrapping_shr` and `wrapping_shl`; checked shift assertions
(`b < 64`) are modeled separately via `GuardCond.shiftLt64` in `CtxFact`. -/
@[expose] def evalSsaOp (env : Nat → Nat) (op : SsaOp)
    (args : List (PoisonOr Nat)) : PoisonOr Nat :=
  match op, args with
  | .var i, [] => .val (word64 (env i))
  | .lit v, [] => .val (word64 v)
  | .addWrap, [x, y] =>
    evalBinaryPoison (fun a b => .val (word64 (a + b))) x y
  | .addNuw, [x, y] =>
    evalBinaryPoison
      (fun a b =>
        match Nat.blt (a + b) u64Mod with
        | true => .val (a + b)
        | false => .poison)
      x y
  | .subWrap, [x, y] =>
    evalBinaryPoison (fun a b => .val (word64 (u64Mod + a - b))) x y
  | .subNuw, [x, y] =>
    evalBinaryPoison
      (fun a b =>
        match Nat.ble b a with
        | true => .val (a - b)
        | false => .poison)
      x y
  | .mulWrap, [x, y] =>
    evalBinaryPoison (fun a b => .val (word64 (a * b))) x y
  | .land, [x, y] =>
    evalBinaryPoison (fun a b => .val (Nat.land a b)) x y
  | .lor, [x, y] =>
    evalBinaryPoison (fun a b => .val (Nat.lor a b)) x y
  | .lshr, [x, y] =>
    evalBinaryPoison (fun a b => .val (Nat.shiftRight a (Nat.mod b 64))) x y
  | .shl, [x, y] =>
    evalBinaryPoison
      (fun a b => .val (word64 (Nat.shiftLeft a (Nat.mod b 64)))) x y
  | .bitNot, [x] =>
    evalUnaryPoison (fun a => .val (u64Max - a)) x
  | .freeze d, [x] => evalFreeze d x
  | _, _ => .poison

/-- Every `SsaOp` produces a `WellTypedVal` (`< 2 ^ 64` whenever defined). -/
theorem evalSsaOp_wellTyped (env : Nat → Nat) (op : SsaOp)
    (args : List (PoisonOr Nat)) : WellTypedVal (evalSsaOp env op args) := by
  cases op with
  | var i =>
    cases args with
    | nil => exact word64_lt (env i)
    | cons _ _ => exact True.intro
  | lit v =>
    cases args with
    | nil => exact word64_lt v
    | cons _ _ => exact True.intro
  | addWrap =>
    cases args with
    | nil => exact True.intro
    | cons x rest =>
      cases rest with
      | nil => exact True.intro
      | cons y rest2 =>
        cases rest2 with
        | cons _ _ => exact True.intro
        | nil =>
          cases x with
          | poison => exact True.intro
          | val a =>
            cases y with
            | poison => exact True.intro
            | val b => exact word64_lt (word64 a + word64 b)
  | addNuw =>
    cases args with
    | nil => exact True.intro
    | cons x rest =>
      cases rest with
      | nil => exact True.intro
      | cons y rest2 =>
        cases rest2 with
        | cons _ _ => exact True.intro
        | nil =>
          cases x with
          | poison => exact True.intro
          | val a =>
            cases y with
            | poison => exact True.intro
            | val b =>
              dsimp only [evalSsaOp, evalBinaryPoison]
              cases hBlt : Nat.blt (word64 a + word64 b) u64Mod with
              | false => exact True.intro
              | true => exact (nat_blt_iff _ _).1 hBlt
  | subWrap =>
    cases args with
    | nil => exact True.intro
    | cons x rest =>
      cases rest with
      | nil => exact True.intro
      | cons y rest2 =>
        cases rest2 with
        | cons _ _ => exact True.intro
        | nil =>
          cases x with
          | poison => exact True.intro
          | val a =>
            cases y with
            | poison => exact True.intro
            | val b => exact word64_lt (u64Mod + word64 a - word64 b)
  | subNuw =>
    cases args with
    | nil => exact True.intro
    | cons x rest =>
      cases rest with
      | nil => exact True.intro
      | cons y rest2 =>
        cases rest2 with
        | cons _ _ => exact True.intro
        | nil =>
          cases x with
          | poison => exact True.intro
          | val a =>
            cases y with
            | poison => exact True.intro
            | val b =>
              dsimp only [evalSsaOp, evalBinaryPoison]
              cases hBle : Nat.ble (word64 b) (word64 a) with
              | false => exact True.intro
              | true =>
                exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (word64_lt a)
  | mulWrap =>
    cases args with
    | nil => exact True.intro
    | cons x rest =>
      cases rest with
      | nil => exact True.intro
      | cons y rest2 =>
        cases rest2 with
        | cons _ _ => exact True.intro
        | nil =>
          cases x with
          | poison => exact True.intro
          | val a =>
            cases y with
            | poison => exact True.intro
            | val b => exact word64_lt (word64 a * word64 b)
  | land =>
    cases args with
    | nil => exact True.intro
    | cons x rest =>
      cases rest with
      | nil => exact True.intro
      | cons y rest2 =>
        cases rest2 with
        | cons _ _ => exact True.intro
        | nil =>
          cases x with
          | poison => exact True.intro
          | val a =>
            cases y with
            | poison => exact True.intro
            | val b =>
              exact Nat.lt_of_le_of_lt
                (Anneal.NatBitwise.land_le_left _ _) (word64_lt a)
  | lor =>
    cases args with
    | nil => exact True.intro
    | cons x rest =>
      cases rest with
      | nil => exact True.intro
      | cons y rest2 =>
        cases rest2 with
        | cons _ _ => exact True.intro
        | nil =>
          cases x with
          | poison => exact True.intro
          | val a =>
            cases y with
            | poison => exact True.intro
            | val b =>
              dsimp only [evalSsaOp, evalBinaryPoison, WellTypedVal]
              rw [u64Mod_eq_pow]
              exact Anneal.NatBitwise.lor_lt_two_pow
                (by rw [← u64Mod_eq_pow]; exact word64_lt a)
                (by rw [← u64Mod_eq_pow]; exact word64_lt b)
  | lshr =>
    cases args with
    | nil => exact True.intro
    | cons x rest =>
      cases rest with
      | nil => exact True.intro
      | cons y rest2 =>
        cases rest2 with
        | cons _ _ => exact True.intro
        | nil =>
          cases x with
          | poison => exact True.intro
          | val a =>
            cases y with
            | poison => exact True.intro
            | val b =>
              dsimp only [evalSsaOp, evalBinaryPoison, WellTypedVal]
              have hsr :
                  Nat.shiftRight (word64 a) (Nat.mod (word64 b) 64) =
                    Nat.div (word64 a)
                      (Nat.pow 2 (Nat.mod (word64 b) 64)) :=
                Nat.shiftRight_eq_div_pow _ _
              rw [hsr]
              exact Nat.lt_of_le_of_lt (nat_div_le_self _ _) (word64_lt a)
  | shl =>
    cases args with
    | nil => exact True.intro
    | cons x rest =>
      cases rest with
      | nil => exact True.intro
      | cons y rest2 =>
        cases rest2 with
        | cons _ _ => exact True.intro
        | nil =>
          cases x with
          | poison => exact True.intro
          | val a =>
            cases y with
            | poison => exact True.intro
            | val b =>
              exact word64_lt (Nat.shiftLeft (word64 a) (Nat.mod (word64 b) 64))
  | bitNot =>
    cases args with
    | nil => exact True.intro
    | cons x rest =>
      cases rest with
      | cons _ _ => exact True.intro
      | nil =>
        cases x with
        | poison => exact True.intro
        | val a =>
          exact Nat.lt_of_le_of_lt (Nat.sub_le u64Max (word64 a)) u64Max_lt
  | freeze d =>
    cases args with
    | nil => exact True.intro
    | cons x rest =>
      cases rest with
      | cons _ _ => exact True.intro
      | nil =>
        cases x with
        | poison => exact word64_lt d
        | val a => exact word64_lt a

/-- Pointwise directional refinement over two equal-length argument lists. -/
@[expose] def ArgsRefines (xs0 ys0 : List (PoisonOr Nat)) : Prop :=
  List.foldr
    (fun x ih ys =>
      match ys with
      | [] => False
      | y :: ys' => refinesPoison x y ∧ ih ys')
    (fun ys => ys = [])
    xs0 ys0

/-- Exact equality of child lists lifts across every `SsaOp` (including
`.freeze`). -/
theorem evalSsaOp_cong_eqExact (env : Nat → Nat) (op : SsaOp)
    {xs ys : List (PoisonOr Nat)} (hEq : xs = ys) :
    evalRel .eqExact (evalSsaOp env op xs) (evalSsaOp env op ys) := by
  rw [hEq]
  rfl

/-- Directional refinement lifts across every `SsaOp` satisfying
`op.isPoisonMonotone = true`. -/
theorem evalSsaOp_cong_refines (env : Nat → Nat) (op : SsaOp)
    (hMono : op.isPoisonMonotone = true) :
    ∀ {xs ys : List (PoisonOr Nat)},
      ArgsRefines xs ys →
      refinesPoison (evalSsaOp env op xs) (evalSsaOp env op ys) := by
  intro xs ys hArgs
  cases op with
  | freeze _ => nomatch hMono
  | var _ =>
    cases xs with
    | nil =>
      have hY : ys = [] := hArgs
      rw [hY]
      exact refinesPoison_refl _
    | cons _ _ =>
      cases ys with
      | nil => exact False.elim hArgs
      | cons _ _ => exact True.intro
  | lit _ =>
    cases xs with
    | nil =>
      have hY : ys = [] := hArgs
      rw [hY]
      exact refinesPoison_refl _
    | cons _ _ =>
      cases ys with
      | nil => exact False.elim hArgs
      | cons _ _ => exact True.intro
  | bitNot =>
    cases xs with
    | nil =>
      have hY : ys = [] := hArgs
      rw [hY]
      exact True.intro
    | cons x xs' =>
      cases ys with
      | nil => exact False.elim hArgs
      | cons y ys' =>
        cases xs' with
        | nil =>
          have hY' : ys' = [] := hArgs.2
          rw [hY']
          dsimp only [evalSsaOp]
          exact evalUnaryPoison_mono (fun a => .val (u64Max - a)) hArgs.1
        | cons _ _ =>
          cases ys' with
          | nil => exact False.elim hArgs.2
          | cons _ _ => exact True.intro
  | addWrap | addNuw | subWrap | subNuw | mulWrap | land | lor | lshr | shl =>
    cases xs with
    | nil =>
      have hY : ys = [] := hArgs
      rw [hY]
      exact True.intro
    | cons x1 xs1 =>
      cases ys with
      | nil => exact False.elim hArgs
      | cons y1 ys1 =>
        cases xs1 with
        | nil =>
          have hY1 : ys1 = [] := hArgs.2
          rw [hY1]
          exact True.intro
        | cons x2 xs2 =>
          cases ys1 with
          | nil => exact False.elim hArgs.2
          | cons y2 ys2 =>
            cases xs2 with
            | nil =>
              have hY2 : ys2 = [] := hArgs.2.2
              rw [hY2]
              dsimp only [evalSsaOp]
              exact evalBinaryPoison_mono _ hArgs.1 hArgs.2.1
            | cons _ _ =>
              cases ys2 with
              | nil => exact False.elim hArgs.2.2
              | cons _ _ => exact True.intro

/-- Mechanized counterexample: `freeze` is NOT poison-monotone (`.poison ⊑ 5`,
yet `freeze 0 .poison = 0` while `freeze 0 5 = 5`). -/
theorem evalFreeze_not_poisonMonotone :
    refinesPoison (.poison : PoisonOr Nat) (.val 5) ∧
    ¬ refinesPoison (evalFreeze 0 .poison) (evalFreeze 0 (.val 5)) := by
  refine ⟨True.intro, fun h => ?_⟩
  have hEq : word64 0 = word64 5 := h
  exact absurd hEq (by decide)

/-! ## 4. `let`-Binding `isFreezeFree` Monotonicity Contract -/

/-- Scoped `let`-body template referencing a single bound slot `boundVar` to
model `let x = e1 in body(x)` congruence with and without inner `freeze`. -/
inductive LetBody where
  | boundVar
  | constVal (v : Nat)
  | addWrap (a b : LetBody)
  | land (a b : LetBody)
  | freeze (defaultVal : Nat) (inner : LetBody)

/-- `true` iff `body` contains zero `.freeze` occurrences. -/
@[expose] noncomputable def LetBody.isFreezeFree (b0 : LetBody) : Bool :=
  @LetBody.rec (fun _ => Bool)
    true
    (fun _ => true)
    (fun _ _ iha ihb => iha && ihb)
    (fun _ _ iha ihb => iha && ihb)
    (fun _ _ _ => false)
    b0

/-- Evaluate `LetBody` at bound operand `x`. -/
@[expose] noncomputable def LetBody.eval (b0 : LetBody)
    (x : PoisonOr Nat) : PoisonOr Nat :=
  @LetBody.rec (fun _ => PoisonOr Nat)
    x
    (fun v => .val (word64 v))
    (fun _ _ va vb =>
      evalBinaryPoison (fun u w => .val (word64 (u + w))) va vb)
    (fun _ _ va vb =>
      evalBinaryPoison (fun u w => .val (Nat.land u w)) va vb)
    (fun d _ vi => evalFreeze d vi)
    b0

/-- Lifting a directional `.refines` rewrite into `let x = [.] in body` is
sound whenever `body.isFreezeFree = true`. -/
theorem LetBody.eval_mono_of_isFreezeFree :
    ∀ (body : LetBody), body.isFreezeFree = true →
      ∀ {x y : PoisonOr Nat}, refinesPoison x y →
        refinesPoison (body.eval x) (body.eval y)
  | .boundVar => fun _ _ _ h => h
  | .constVal _ => fun _ _ _ _ => refinesPoison_refl _
  | .addWrap a b => fun hF _ _ h =>
    evalBinaryPoison_mono (fun u w => .val (word64 (u + w)))
      (LetBody.eval_mono_of_isFreezeFree a (bool_and_left hF) h)
      (LetBody.eval_mono_of_isFreezeFree b (bool_and_right hF) h)
  | .land a b => fun hF _ _ h =>
    evalBinaryPoison_mono (fun u w => .val (Nat.land u w))
      (LetBody.eval_mono_of_isFreezeFree a (bool_and_left hF) h)
      (LetBody.eval_mono_of_isFreezeFree b (bool_and_right hF) h)
  | .freeze _ _ => fun hF _ _ _ => nomatch hF

/-- Mechanized counterexample: lifting `.refines` into `let x = [.] in freeze 0`
(`isFreezeFree = false`) violates refinement. -/
theorem LetBody.freeze_body_breaks_mono :
    (LetBody.freeze 0 .boundVar).isFreezeFree = false ∧
    refinesPoison (.poison : PoisonOr Nat) (.val 5) ∧
    ¬ refinesPoison
        ((LetBody.freeze 0 .boundVar).eval .poison)
        ((LetBody.freeze 0 .boundVar).eval (.val 5)) :=
  ⟨rfl, evalFreeze_not_poisonMonotone.1, evalFreeze_not_poisonMonotone.2⟩

/-! ## 5. Arena-Free Rewrite Rules and Soundness Proofs -/

/-- Bidirectional `PoisonOr`-exact rewrite rules (`eval lhs = eval rhs`). -/
inductive BiEqRule where
  | addZero
  | addComm
  | andComm
  | mul4ToShl2
  | shrShrAdd
  | notSubOneToNeg
  | maskPow2Elide (factIdx : Nat) (exp : Nat)
  | promoteAddNuw (factIdx : Nat)
  | promoteSubNuw (factIdx : Nat)

/-- Directional poison-monotonic rewrite rules (`eval lhs ⊑_poison eval rhs`).
-/
inductive DirRefineRule where
  | landZero
  | mulZero
  | dropAddNuw
  | dropSubNuw

theorem biEq_addZero_sound (env : Nat → Nat) (x : PoisonOr Nat)
    (hWx : WellTypedVal x) :
    evalSsaOp env .addWrap [x, .val 0] = x := by
  cases x with
  | poison => rfl
  | val v =>
    dsimp only [WellTypedVal] at hWx
    dsimp only [evalSsaOp, evalBinaryPoison]
    have h0 : word64 0 = 0 := rfl
    rw [word64_of_lt hWx, h0, Nat.add_zero, word64_of_lt hWx]

theorem biEq_addComm_sound (env : Nat → Nat) (a b : PoisonOr Nat) :
    evalSsaOp env .addWrap [a, b] = evalSsaOp env .addWrap [b, a] := by
  cases a with
  | poison =>
    cases b <;> rfl
  | val va =>
    cases b with
    | poison => rfl
    | val vb =>
      dsimp only [evalSsaOp, evalBinaryPoison]
      rw [Nat.add_comm (word64 va) (word64 vb)]

theorem biEq_andComm_sound (env : Nat → Nat) (a b : PoisonOr Nat) :
    evalSsaOp env .land [a, b] = evalSsaOp env .land [b, a] := by
  cases a with
  | poison =>
    cases b <;> rfl
  | val va =>
    cases b with
    | poison => rfl
    | val vb =>
      dsimp only [evalSsaOp, evalBinaryPoison]
      rw [Anneal.NatBitwise.land_comm]

theorem biEq_mul4ToShl2_sound (env : Nat → Nat) (x : PoisonOr Nat) :
    evalSsaOp env .mulWrap [x, .val 4] = evalSsaOp env .shl [x, .val 2] := by
  cases x with
  | poison => rfl
  | val v =>
    dsimp only [evalSsaOp, evalBinaryPoison]
    have h4 : word64 4 = 4 := rfl
    have h2 : Nat.mod (word64 2) 64 = 2 := rfl
    have hsl : Nat.shiftLeft (word64 v) 2 = word64 v * Nat.pow 2 2 :=
      Nat.shiftLeft_eq (word64 v) 2
    rw [h4, h2, hsl]

theorem biEq_shrShrAdd_sound (env : Nat → Nat) (x : PoisonOr Nat)
    (k1 k2 : Nat) (hBound : k1 + k2 ≤ 63) :
    evalSsaOp env .lshr [evalSsaOp env .lshr [x, .val k1], .val k2] =
      evalSsaOp env .lshr [x, .val (k1 + k2)] := by
  cases x with
  | poison => rfl
  | val v =>
    have hSum64 : k1 + k2 < 64 := Nat.lt_of_le_of_lt hBound (by decide)
    have hk1_64 : k1 < 64 :=
      Nat.lt_of_le_of_lt (Nat.le_add_right k1 k2) hSum64
    have hk2_64 : k2 < 64 :=
      Nat.lt_of_le_of_lt (Nat.le_add_left k2 k1) hSum64
    have h64_u64 : (64 : Nat) < u64Mod := by decide
    have hk1_w : word64 k1 = k1 := word64_of_lt (Nat.lt_trans hk1_64 h64_u64)
    have hk2_w : word64 k2 = k2 := word64_of_lt (Nat.lt_trans hk2_64 h64_u64)
    have hSum_w : word64 (k1 + k2) = k1 + k2 :=
      word64_of_lt (Nat.lt_trans hSum64 h64_u64)
    have hInLt : Nat.shiftRight (word64 v) k1 < u64Mod := by
      have hsr : Nat.shiftRight (word64 v) k1 =
          Nat.div (word64 v) (Nat.pow 2 k1) :=
        Nat.shiftRight_eq_div_pow _ _
      rw [hsr]
      exact Nat.lt_of_le_of_lt (nat_div_le_self _ _) (word64_lt v)
    dsimp only [evalSsaOp, evalBinaryPoison]
    rw [hk1_w, hk2_w, hSum_w,
      nat_mod_eq_of_lt hk1_64, nat_mod_eq_of_lt hk2_64,
      nat_mod_eq_of_lt hSum64, word64_of_lt hInLt]
    refine congrArg PoisonOr.val ?_
    exact Anneal.NatBitwise.eq_of_testBit_eq (fun i => by
      rw [Anneal.NatBitwise.testBit_shiftRight,
        Anneal.NatBitwise.testBit_shiftRight,
        Anneal.NatBitwise.testBit_shiftRight,
        Nat.add_assoc, Nat.add_comm k2 k1])

/-- Two's-complement identity powering `zerocopy`'s `padding_needed_for`:
`!(len -_w 1) = 0 -_w len` across all 64-bit values and `.poison`. -/
theorem biEq_notSubOneToNeg_sound (env : Nat → Nat) (x : PoisonOr Nat) :
    evalSsaOp env .bitNot [evalSsaOp env .subWrap [x, .val 1]] =
      evalSsaOp env .subWrap [.val 0, x] := by
  cases x with
  | poison => rfl
  | val raw =>
    dsimp only [evalSsaOp, evalBinaryPoison, evalUnaryPoison]
    have h1 : word64 1 = 1 := rfl
    have h0 : word64 0 = 0 := rfl
    rw [h1, h0, Nat.add_zero]
    have hLt : word64 raw < u64Mod := word64_lt raw
    cases hV : word64 raw with
    | zero => rfl
    | succ k =>
      rw [hV] at hLt
      have hkLt : k < u64Mod := Nat.lt_trans (Nat.lt_succ_self k) hLt
      have hSub1 : u64Mod + (k + 1) - 1 = u64Mod + k := by
        rw [← Nat.add_assoc u64Mod k 1, Nat.add_sub_cancel]
      have hMod1 : word64 (u64Mod + k) = k := by
        dsimp only [word64]
        rw [nat_add_mod_self_left, nat_mod_eq_of_lt hkLt]
      have hSubLt : u64Mod - (k + 1) < u64Mod :=
        Nat.sub_lt u64Mod_pos (Nat.succ_pos k)
      have hMod2 : word64 (u64Mod - (k + 1)) = u64Mod - (k + 1) :=
        word64_of_lt hSubLt
      have hMaxSub : u64Max - k = u64Mod - (k + 1) := by
        have hEqMod : u64Mod = u64Max + 1 := rfl
        rw [hEqMod, Nat.succ_sub_succ_eq_sub]
      rw [hSub1, hMod1, word64_of_lt hkLt, hMod2, hMaxSub]

/-- Contextual bitmask elision: when `x < 2 ^ exp` (`exp ≤ 64`) on non-poison
values, `x & (2 ^ exp - 1) = x` holds as an exact `PoisonOr` equality. -/
theorem biEq_maskPow2Elide_sound (env : Nat → Nat) (x : PoisonOr Nat)
    (exp : Nat) (hExp : exp ≤ 64) (hWx : WellTypedVal x)
    (hFact : ∀ v, x = .val v → v < Nat.pow 2 exp) :
    evalSsaOp env .land [x, .val (Nat.pow 2 exp - 1)] = x := by
  cases x with
  | poison => rfl
  | val v =>
    dsimp only [WellTypedVal] at hWx
    have hLtPow : v < Nat.pow 2 exp := hFact v rfl
    have hPowLe : Nat.pow 2 exp ≤ u64Mod := by
      rw [u64Mod_eq_pow]
      exact nat_two_pow_le_of_le hExp
    have hMaskLt : Nat.pow 2 exp - 1 < u64Mod := by
      have hPos : 0 < Nat.pow 2 exp := nat_two_pow_pos exp
      exact Nat.lt_of_lt_of_le (Nat.sub_lt hPos (by decide)) hPowLe
    dsimp only [evalSsaOp, evalBinaryPoison]
    rw [word64_of_lt hWx, word64_of_lt hMaskLt,
      Anneal.NatBitwise.land_two_pow_sub_one_eq_mod,
      nat_mod_eq_of_lt hLtPow]

/-- Contextual promotion of `addWrap` to `addNuw` under proven non-overflow. -/
theorem biEq_promoteAddNuw_sound (env : Nat → Nat) (a b : PoisonOr Nat)
    (hWa : WellTypedVal a) (hWb : WellTypedVal b)
    (hFact : ∀ va vb, a = .val va → b = .val vb → va + vb < u64Mod) :
    evalSsaOp env .addWrap [a, b] = evalSsaOp env .addNuw [a, b] := by
  cases a with
  | poison =>
    cases b <;> rfl
  | val va =>
    cases b with
    | poison => rfl
    | val vb =>
      dsimp only [WellTypedVal] at hWa hWb
      have hNoOvf : va + vb < u64Mod := hFact va vb rfl rfl
      have hBlt : Nat.blt (va + vb) u64Mod = true :=
        (nat_blt_iff _ _).2 hNoOvf
      dsimp only [evalSsaOp, evalBinaryPoison]
      rw [word64_of_lt hWa, word64_of_lt hWb, hBlt, word64_of_lt hNoOvf]

/-- Contextual promotion of `subWrap` to `subNuw` under proven non-underflow. -/
theorem biEq_promoteSubNuw_sound (env : Nat → Nat) (a b : PoisonOr Nat)
    (hWa : WellTypedVal a) (hWb : WellTypedVal b)
    (hFact : ∀ va vb, a = .val va → b = .val vb → vb ≤ va) :
    evalSsaOp env .subWrap [a, b] = evalSsaOp env .subNuw [a, b] := by
  cases a with
  | poison =>
    cases b <;> rfl
  | val va =>
    cases b with
    | poison => rfl
    | val vb =>
      dsimp only [WellTypedVal] at hWa hWb
      have hLe : vb ≤ va := hFact va vb rfl rfl
      have hBle : Nat.ble vb va = true := (nat_ble_iff _ _).2 hLe
      have hAddSub : u64Mod + va - vb = u64Mod + (va - vb) :=
        Nat.add_sub_assoc hLe u64Mod
      have hSubLt : va - vb < u64Mod :=
        Nat.lt_of_le_of_lt (Nat.sub_le va vb) hWa
      have hMod : word64 (u64Mod + (va - vb)) = va - vb := by
        dsimp only [word64]
        rw [nat_add_mod_self_left, nat_mod_eq_of_lt hSubLt]
      dsimp only [evalSsaOp, evalBinaryPoison]
      rw [word64_of_lt hWa, word64_of_lt hWb, hBle, hAddSub, hMod]

theorem dirRefine_landZero_sound (env : Nat → Nat) (x : PoisonOr Nat) :
    refinesPoison (evalSsaOp env .land [x, .val 0]) (.val 0) := by
  cases x with
  | poison => exact True.intro
  | val v =>
    dsimp only [evalSsaOp, evalBinaryPoison, refinesPoison]
    have h0 : word64 0 = 0 := rfl
    rw [h0, Anneal.NatBitwise.land_zero_right]

theorem dirRefine_mulZero_sound (env : Nat → Nat) (x : PoisonOr Nat) :
    refinesPoison (evalSsaOp env .mulWrap [x, .val 0]) (.val 0) := by
  cases x with
  | poison => exact True.intro
  | val v =>
    dsimp only [evalSsaOp, evalBinaryPoison, refinesPoison]
    have h0 : word64 0 = 0 := rfl
    rw [h0, Nat.mul_zero]
    rfl

theorem dirRefine_dropAddNuw_sound (env : Nat → Nat) (a b : PoisonOr Nat) :
    refinesPoison
      (evalSsaOp env .addNuw [a, b])
      (evalSsaOp env .addWrap [a, b]) := by
  cases a with
  | poison => exact True.intro
  | val va =>
    cases b with
    | poison => exact True.intro
    | val vb =>
      dsimp only [evalSsaOp, evalBinaryPoison]
      cases hBlt : Nat.blt (word64 va + word64 vb) u64Mod with
      | false => exact True.intro
      | true =>
        dsimp only [refinesPoison]
        exact Eq.symm (word64_of_lt ((nat_blt_iff _ _).1 hBlt))

theorem dirRefine_dropSubNuw_sound (env : Nat → Nat) (a b : PoisonOr Nat) :
    refinesPoison
      (evalSsaOp env .subNuw [a, b])
      (evalSsaOp env .subWrap [a, b]) := by
  cases a with
  | poison => exact True.intro
  | val va =>
    cases b with
    | poison => exact True.intro
    | val vb =>
      dsimp only [evalSsaOp, evalBinaryPoison]
      cases hBle : Nat.ble (word64 vb) (word64 va) with
      | false => exact True.intro
      | true =>
        dsimp only [refinesPoison]
        have hLe : word64 vb ≤ word64 va := (nat_ble_iff _ _).1 hBle
        have hAddSub :
            u64Mod + word64 va - word64 vb = u64Mod + (word64 va - word64 vb) :=
          Nat.add_sub_assoc hLe u64Mod
        have hSubLt : word64 va - word64 vb < u64Mod :=
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) (word64_lt va)
        have hMod : word64 (u64Mod + (word64 va - word64 vb)) =
            word64 va - word64 vb := by
          dsimp only [word64] at hSubLt
          dsimp only [word64]
          rw [nat_add_mod_self_left, nat_mod_eq_of_lt hSubLt]
        rw [hAddSub, hMod]

end Anneal.Backend

end
