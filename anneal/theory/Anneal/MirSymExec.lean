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
public import Init.SimpLemmas
public import Init.Data.Nat.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.Int.Basic
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.Framework.StepWp
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.MirTotal.StepCore
public import Anneal.PureLift.BvLin

public section

namespace Anneal.MirSymExec

open Trusted.MirAst Trusted.MirSemantics Anneal.Framework.StepWp Anneal.MirWp
open Anneal.MirTotal Anneal.PureLift.BvLin

/-!
# Reflective Multi-Variable MIR Symbolic Executor (`Anneal.MirSymExec`)

General, zero-TCB (`0` `._unsafe_rec`, `["propext"]`-only axioms) reflective
symbolic executor over `Trusted.MirAst` and `Trusted.MirSemantics`. Every
definition is kernel-reducible (`decide`/`rfl`); definitions are marked
`noncomputable` solely so the compiler emits no `._unsafe_rec` auxiliaries
(the same convention as `Anneal.PureLift.BvLin.LinExpr.evalBv`):

1. **Exact Depth-Bounded `MirTy` Equality (`mirTyEqExact`, `symCheckVal`):**
   Kernel-reducible structural type comparison over `MirTy` failing closed
   (`none`) only if nesting exceeds `fuel`, with unconditional soundness against
   `MirTy.beq` and `checkVal`.
2. **Multi-Variable, Width-Parametric Symbolic Expressions (`SymScalar`,
   `SymBool`, `SymVal`):** Symbolic scalars indexed by `(id, width, signed)`,
   bitwise/shift/wrapping-arithmetic/unary/cast expressions, symbolic booleans,
   and overflow-pair tuples, evaluated computably via `MirTotal.Ops`.
3. **Reflective `BvLin` Algebraic Simplification (`toBvLin?`, `symBvLinEq`,
   `symBvLinNe`, `symBvLinDiffConst`):** Bridges all 6 `IntWidth`s (signed and
   unsigned) into `Anneal.PureLift.BvLin`, collapsing modular equalities and
   disequalities statically during symbolic execution.
4. **Single-Path (`symStep`, `symRun`, step-chunked `symRunSteps`) &
   Branched (`symStepBranched`, `symRunPaths`) Symbolic Execution + `MirWp`
   Adequacy:** Lifts symbolic runs by `rfl` / `decide` (without
   `decide +kernel`) into `Executes`, `RunsFrom`, `SafeFrom`, `ReturnsFrom`,
   `Behavior`, and `BodyVerified`.
-/

/-! ## Part I: Exact Depth-Bounded `MirTy` Equality -/

/-- Elementwise comparison over `List MirTy` returning `none` if any pair
exceeds the element comparison's nesting budget. -/
@[expose] noncomputable def mirTyListEqExact (elemEq : MirTy → MirTy → Option Bool)
    (fs1 fs2 : List MirTy) : Option Bool :=
  List.foldr
    (fun (x : MirTy) (ih : List MirTy → Option Bool) (ys : List MirTy) =>
      match ys with
      | [] => some false
      | y :: tl =>
        match elemEq x y with
        | none => none
        | some false => some false
        | some true => ih tl)
    (fun ys => match ys with | [] => some true | _ :: _ => some false)
    fs1 fs2

private theorem mirTyListEqExact_eq
    (elemEq : MirTy → MirTy → Option Bool)
    (hElem : ∀ a b r, elemEq a b = some r → r = MirTy.beq a b) :
    ∀ (fs1 fs2 : List MirTy) (r : Bool),
      mirTyListEqExact elemEq fs1 fs2 = some r → r = MirTy.beqList fs1 fs2
  | [], [], r, h => by
    cases h
    rfl
  | [], _ :: _, r, h => by
    cases h
    rfl
  | _ :: _, [], r, h => by
    cases h
    rfl
  | x :: xs, y :: ys, r, h => by
    change (match elemEq x y with
      | none => none
      | some false => some false
      | some true => mirTyListEqExact elemEq xs ys) = some r at h
    change r = (MirTy.beq x y && MirTy.beqList xs ys)
    cases hE : elemEq x y with
    | none => rw [hE] at h; cases h
    | some b =>
      rw [hE] at h
      have hB := hElem x y b hE
      rw [← hB]
      cases b with
      | false =>
        cases h
        rfl
      | true =>
        exact mirTyListEqExact_eq elemEq hElem xs ys r h

/-- Kernel-reducible structural equality on `MirTy` via `@Nat.rec` returning
`none` only if `.tuple`, `.ref`, or `.rawPtr` nesting exceeds `fuel`. -/
@[expose] noncomputable def mirTyEqExact (fuel : Nat) (a b : MirTy) : Option Bool :=
  @Nat.rec (fun _ => MirTy → MirTy → Option Bool)
    (fun x y =>
      match x, y with
      | .bool, .bool => some true
      | .int w1 s1, .int w2 s2 =>
        some (intWidthBeqComp w1 w2 && boolBeqComp s1 s2)
      | .unit, .unit => some true
      | .never, .never => some true
      | .char, .char => some true
      | .ordering, .ordering => some true
      | .enum e1, .enum e2 => some (enumTyBeqComp e1 e2)
      | .unsupported, .unsupported => some true
      | .tuple _, .tuple _ => none
      | .ref _ _, .ref _ _ => none
      | .rawPtr _ _, .rawPtr _ _ => none
      | .slice _, .slice _ => none
      | .str, .str => some true
      | .array _ _, .array _ _ => none
      | .rangeTo _, .rangeTo _ => none
      | .rangeFrom _, .rangeFrom _ => none
      | .range _, .range _ => none
      | .option _, .option _ => none
      | _, _ => some false)
    (fun _ ih x y =>
      match x, y with
      | .bool, .bool => some true
      | .int w1 s1, .int w2 s2 =>
        some (intWidthBeqComp w1 w2 && boolBeqComp s1 s2)
      | .unit, .unit => some true
      | .never, .never => some true
      | .char, .char => some true
      | .ordering, .ordering => some true
      | .enum e1, .enum e2 => some (enumTyBeqComp e1 e2)
      | .tuple fs1, .tuple fs2 => mirTyListEqExact ih fs1 fs2
      | .ref m1 p1, .ref m2 p2 =>
        if mutabilityBeqComp m1 m2 then ih p1 p2 else some false
      | .rawPtr m1 p1, .rawPtr m2 p2 =>
        if mutabilityBeqComp m1 m2 then ih p1 p2 else some false
      | .slice e1, .slice e2 => ih e1 e2
      | .str, .str => some true
      | .array _ _, .array _ _ => none
      | .rangeTo e1, .rangeTo e2 => ih e1 e2
      | .rangeFrom e1, .rangeFrom e2 => ih e1 e2
      | .range e1, .range e2 => ih e1 e2
      | .option e1, .option e2 => ih e1 e2
      | .unsupported, .unsupported => some true
      | _, _ => some false)
    fuel a b

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_mod_lt (a : Nat) {b : Nat} (hb : 0 < b) : Nat.mod a b < b :=
  Nat.mod_lt a hb

private theorem nat_mul_mod_right (a b : Nat) : Nat.mod (a * b) a = 0 :=
  Nat.mul_mod_right a b

private theorem nat_shiftRight_zero (n : Nat) : Nat.shiftRight n 0 = n := rfl

private theorem nat_mod_mod_pos (a : Nat) {b : Nat} (hb : 0 < b) :
    Nat.mod (Nat.mod a b) b = Nat.mod a b :=
  Nat.mod_eq_of_lt (Nat.mod_lt a hb)

/-- `LawfulBEq`-free `Int` boolean equality, keeping the `["propext"]`
ceiling. -/
theorem int_beq_iff_eq {a b : Int} : (a == b) = true ↔ a = b :=
  ⟨fun h => of_decide_eq_true h, fun h => decide_eq_true h⟩

/-- `LawfulBEq`-free reflexivity of `Int` boolean equality. -/
theorem int_beq_self_eq_true (a : Int) : (a == a) = true :=
  decide_eq_true rfl

/-- `LawfulBEq`-free irreflexivity of `Int` boolean disequality. -/
theorem int_bne_self_eq_false (a : Int) : (a != a) = false :=
  congrArg Bool.not (int_beq_self_eq_true a)

private theorem ite_bool_true {α : Type} (t e : α) :
    (if true = true then t else e) = t :=
  ite_prop_true (rfl : true = true)

private theorem ite_bool_false {α : Type} (t e : α) :
    (if false = true then t else e) = e :=
  ite_prop_false (by decide)

private theorem nat_two_pow_pos : ∀ w : Nat, 0 < Nat.pow 2 w
  | 0 => by decide
  | w + 1 => Nat.mul_pos (nat_two_pow_pos w) (by decide)

private theorem intWidthModulus_eq_pow (w : IntWidth) :
    intWidthModulus w = Nat.pow 2 w.bitWidth := by
  cases w <;> rfl

/-- Unconditional soundness of `mirTyEqExact` against `MirTy.beq`. -/
theorem mirTyEqExact_eq :
    ∀ (fuel : Nat) (a b : MirTy) (r : Bool),
      mirTyEqExact fuel a b = some r → r = MirTy.beq a b
  | 0, a, b, r, h => by
    cases a <;> cases b <;>
      first
        | (cases h; rfl)
        | (change some _ = some r at h; cases h;
           dsimp only [MirTy.beq];
           first
             | (rw [intWidthBeqComp_eq, boolBeqComp_eq])
             | (rw [enumTyBeqComp_eq]))
        | (change none = some r at h; cases h)
  | fuel + 1, a, b, r, h => by
    cases a with
    | bool | unit | never | char | ordering =>
      cases b <;> first | (cases h; rfl) | (change none = some r at h; cases h)
    | int w1 s1 =>
      cases b with
      | int w2 s2 =>
        change some (intWidthBeqComp w1 w2 && boolBeqComp s1 s2) = some r at h
        cases h; dsimp only [MirTy.beq]; rw [intWidthBeqComp_eq, boolBeqComp_eq]
      | _ => cases h; rfl
    | enum e1 =>
      cases b with
      | enum e2 =>
        change some (enumTyBeqComp e1 e2) = some r at h
        cases h; dsimp only [MirTy.beq]; rw [enumTyBeqComp_eq]
      | _ => cases h; rfl
    | tuple ps1 =>
      cases b with
      | tuple ps2 =>
        exact mirTyListEqExact_eq (mirTyEqExact fuel) (mirTyEqExact_eq fuel)
          ps1 ps2 r h
      | _ => cases h; rfl
    | ref m1 p1 =>
      cases b with
      | ref m2 p2 =>
        change (if mutabilityBeqComp m1 m2 then mirTyEqExact fuel p1 p2
          else some false) = some r at h
        dsimp only [MirTy.beq]
        rw [← mutabilityBeqComp_eq m1 m2]
        cases hm : mutabilityBeqComp m1 m2 with
        | false => rw [hm] at h; cases h; rfl
        | true => rw [hm] at h; exact mirTyEqExact_eq fuel p1 p2 r h
      | _ => cases h; rfl
    | rawPtr m1 p1 =>
      cases b with
      | rawPtr m2 p2 =>
        change (if mutabilityBeqComp m1 m2 then mirTyEqExact fuel p1 p2
          else some false) = some r at h
        dsimp only [MirTy.beq]
        rw [← mutabilityBeqComp_eq m1 m2]
        cases hm : mutabilityBeqComp m1 m2 with
        | false => rw [hm] at h; cases h; rfl
        | true => rw [hm] at h; exact mirTyEqExact_eq fuel p1 p2 r h
      | _ => cases h; rfl
    | slice e1 =>
      cases b with
      | slice e2 => exact mirTyEqExact_eq fuel e1 e2 r h
      | _ => cases h; rfl
    | str =>
      cases b <;> (cases h; rfl)
    | array _ _ =>
      cases b <;> first | (cases h; rfl) | (change none = some r at h; cases h)
    | rangeTo e1 =>
      cases b with
      | rangeTo e2 => exact mirTyEqExact_eq fuel e1 e2 r h
      | _ => cases h; rfl
    | rangeFrom e1 =>
      cases b with
      | rangeFrom e2 => exact mirTyEqExact_eq fuel e1 e2 r h
      | _ => cases h; rfl
    | range e1 =>
      cases b with
      | range e2 => exact mirTyEqExact_eq fuel e1 e2 r h
      | _ => cases h; rfl
    | option e1 =>
      cases b with
      | option e2 => exact mirTyEqExact_eq fuel e1 e2 r h
      | _ => cases h; rfl
    | unsupported =>
      cases b <;> (cases h; rfl)

/-- Kernel-reducible `checkVal` mirror returning `none` only if `ty`
nesting exceeds `fuel`. -/
@[expose] noncomputable def symCheckVal (fuel : Nat) (v : Val) (ty : MirTy) : Option Bool :=
  match valTy?Comp v with
  | some vTy => mirTyEqExact fuel vTy ty
  | none => some false

/-- Unconditional soundness of `symCheckVal` against `checkVal`. -/
theorem symCheckVal_eq {fuel : Nat} {v : Val} {ty : MirTy} {r : Bool}
    (h : symCheckVal fuel v ty = some r) : r = checkVal v ty := by
  unfold symCheckVal at h
  unfold checkVal
  rw [← valTy?Comp_eq]
  cases hTy : valTy?Comp v with
  | none => rw [hTy] at h; cases h; rfl
  | some vTy =>
    rw [hTy] at h
    exact mirTyEqExact_eq fuel vTy ty r h

/-! ## Part II: Symbolic Expressions & `BvLin` Integration -/

/-- Variable valuation mapping symbolic variable IDs to MIR values. -/
abbrev SymEnv := Nat → Val

/-- Symbolic scalar expression parameterized by variable ID, `IntWidth`, and
signedness. -/
inductive SymScalar where
  | lit (sv : ScalarVal)
  | var (id : Nat) (width : IntWidth) (signed : Bool)
  | unOp (op : UnOp) (arg : SymScalar)
  | binOp (op : BinOp) (lhs rhs : SymScalar)
  | shift (op : BinOp) (lhs rhs : SymScalar)
  | cast (dstW : IntWidth) (dstS : Bool) (src : SymScalar)

/-- Static integer width of a `SymScalar`. -/
@[expose] noncomputable def SymScalar.width : SymScalar → IntWidth
  | .lit sv => sv.width
  | .var _ w _ => w
  | .unOp _ arg => arg.width
  | .binOp _ lhs _ => lhs.width
  | .shift _ lhs _ => lhs.width
  | .cast dstW _ _ => dstW

/-- Static signedness of a `SymScalar`. -/
@[expose] noncomputable def SymScalar.signed : SymScalar → Bool
  | .lit sv => sv.signed
  | .var _ _ s => s
  | .unOp _ arg => arg.signed
  | .binOp _ lhs _ => lhs.signed
  | .shift _ lhs _ => lhs.signed
  | .cast _ dstS _ => dstS

/-- Decidable static well-formedness invariant on `SymScalar`. -/
@[expose] noncomputable def SymScalar.wf : SymScalar → Bool
  | .lit sv => bv128BeqComp (truncateBitsComp sv.width sv.bits) sv.bits
  | .var _ _ _ => true
  | .unOp .not a => a.wf
  | .unOp .neg a => a.signed && a.wf
  | .unOp .ptrMetadata _ => false
  | .binOp op l r =>
    l.wf && r.wf &&
      intWidthBeqComp l.width r.width &&
      boolBeqComp l.signed r.signed &&
      (match op with
       | .add | .sub | .mul | .bitAnd | .bitOr | .bitXor => true
       | _ => false)
  | .shift op l r =>
    l.wf && r.wf && (match op with | .shl | .shr => true | _ => false)
  | .cast _ _ src => src.wf

/-- Kernel-reducible evaluation of a `SymScalar` under `env`.
Uses `MirTotal.Ops` mirrors so concrete runs reduce by `rfl`/`decide`. -/
@[expose] noncomputable def SymScalar.eval (env : SymEnv) : SymScalar → ScalarVal
  | .lit sv => ⟨sv.width, sv.signed, truncateBitsComp sv.width sv.bits⟩
  | .var id w s =>
    match env id with
    | .scalar sv => ⟨w, s, truncateBitsComp w sv.bits⟩
    | _ => ⟨w, s, BitVec.ofNat 128 0⟩
  | .unOp op arg =>
    let av := arg.eval env
    match evalUnOpComp op (.scalar av) with
    | .ok (.scalar sv) => sv
    | _ => ⟨arg.width, arg.signed, BitVec.ofNat 128 0⟩
  | .binOp op l r =>
    let lv := l.eval env
    let rv := r.eval env
    match evalBinOpComp op (.scalar lv) (.scalar rv) with
    | .ok (.scalar sv) => sv
    | _ => ⟨l.width, l.signed, BitVec.ofNat 128 0⟩
  | .shift op l r =>
    let lv := l.eval env
    let rv := r.eval env
    match evalBinOpComp op (.scalar lv) (.scalar rv) with
    | .ok (.scalar sv) => sv
    | _ => ⟨l.width, l.signed, BitVec.ofNat 128 0⟩
  | .cast dstW dstS src =>
    let sv := src.eval env
    match evalIntToIntCastComp (.scalar sv) (.int dstW dstS) with
    | .ok (.scalar sv') => sv'
    | _ => ⟨dstW, dstS, BitVec.ofNat 128 0⟩

private theorem scalarWf_of_truncateBitsComp (w : IntWidth) (s : Bool)
    (bits : BitVec 128) :
    ScalarVal.wf ⟨w, s, truncateBitsComp w bits⟩ = true := by
  rw [truncateBitsComp_eq]
  exact scalarWf_truncateBits w s bits

private theorem bool_ite_true {α : Type} {c : Bool} (hc : c = true) (t e : α) :
    (if c = true then t else e) = t := by
  cases c <;> first | rfl | cases hc

private theorem ite_false_eq {α : Type} {c : Bool} (hc : c = false) (t e : α) :
    (if c = true then t else e) = e := by
  cases c <;> first | rfl | cases hc

private theorem bool_and_false (b : Bool) : (b && false) = false := by
  cases b <;> rfl

private theorem bool_and3_mid_false (a b : Bool) : (a && false && b) = false := by
  cases a <;> rfl

private theorem evalArithOp_wrap_total (op : BinOp) (w : IntWidth) (s : Bool)
    (l r : Int)
    (hWrap : (match op with | .add | .sub | .mul => true | _ => false) = true) :
    ∃ (sv : ScalarVal) (lossy : Bool),
      evalArithOp op w s l r = .ok (.scalar sv) ∧
      truncateScalar w s
        (match op with | .add => l + r | .sub => l - r | _ => l * r) =
          .ok (sv, lossy) ∧
      sv.width = w ∧ sv.signed = s ∧ ScalarVal.wf sv = true := by
  have hUnc : op.isUnchecked = false := by
    cases op <;> first | rfl | cases hWrap
  have hOvf : op.isOverflowing = false := by
    cases op <;> first | rfl | cases hWrap
  unfold evalArithOp
  rw [hUnc, hOvf]
  cases op with
  | div | rem | addUnchecked | subUnchecked | mulUnchecked
  | addWithOverflow | subWithOverflow | mulWithOverflow
  | shl | shr | shlUnchecked | shrUnchecked | bitAnd | bitOr | bitXor
  | eq | lt | le | ne | ge | gt | cmp | offset => cases hWrap
  | add =>
    let ⟨sv, lossy, hTr, hW, hS, hWf⟩ := truncateScalar_ok w s (l + r)
    refine ⟨sv, lossy, ?_, hTr, hW, hS, hWf⟩
    dsimp only
    rw [hTr]
    dsimp only
    rw [ite_false_eq (bool_and3_mid_false _ _), ite_false_eq (bool_and_false _)]
    rfl
  | sub =>
    let ⟨sv, lossy, hTr, hW, hS, hWf⟩ := truncateScalar_ok w s (l - r)
    refine ⟨sv, lossy, ?_, hTr, hW, hS, hWf⟩
    dsimp only
    rw [hTr]
    dsimp only
    rw [ite_false_eq (bool_and3_mid_false _ _), ite_false_eq (bool_and_false _)]
    rfl
  | mul =>
    let ⟨sv, lossy, hTr, hW, hS, hWf⟩ := truncateScalar_ok w s (l * r)
    refine ⟨sv, lossy, ?_, hTr, hW, hS, hWf⟩
    dsimp only
    rw [hTr]
    dsimp only
    rw [ite_false_eq (bool_and3_mid_false _ _), ite_false_eq (bool_and_false _)]
    rfl

private theorem evalBinOpComp_scalar_total (op : BinOp)
    (l r : ScalarVal) (hw : l.width = r.width) (hs : l.signed = r.signed)
    (hOp : (match op with
      | .add | .sub | .mul | .bitAnd | .bitOr | .bitXor => true
      | _ => false) = true) :
    ∃ sv : ScalarVal,
      evalBinOpComp op (.scalar l) (.scalar r) = .ok (.scalar sv) ∧
      sv.width = l.width ∧ sv.signed = l.signed ∧ ScalarVal.wf sv = true := by
  rw [evalBinOpComp_eq]
  dsimp only [evalBinOp]
  have hNotShift : op.isShift = false := by
    cases op <;> first | rfl | (cases hOp)
  have hMatch :
      (!(IntWidth.beq l.width r.width && (l.signed == r.signed))) = false := by
    rw [hw, hs]
    cases r.width <;> cases r.signed <;> rfl
  rw [hNotShift, hMatch]
  cases op with
  | bitAnd =>
    refine ⟨_, rfl, rfl, rfl, scalarWf_truncateBits l.width l.signed _⟩
  | bitOr =>
    refine ⟨_, rfl, rfl, rfl, scalarWf_truncateBits l.width l.signed _⟩
  | bitXor =>
    refine ⟨_, rfl, rfl, rfl, scalarWf_truncateBits l.width l.signed _⟩
  | add =>
    let ⟨sv, _, hEq, _, hW, hS, hWf⟩ :=
      evalArithOp_wrap_total .add l.width l.signed (decodeScalar l) (decodeScalar r) rfl
    exact ⟨sv, hEq, hW, hS, hWf⟩
  | sub =>
    let ⟨sv, _, hEq, _, hW, hS, hWf⟩ :=
      evalArithOp_wrap_total .sub l.width l.signed (decodeScalar l) (decodeScalar r) rfl
    exact ⟨sv, hEq, hW, hS, hWf⟩
  | mul =>
    let ⟨sv, _, hEq, _, hW, hS, hWf⟩ :=
      evalArithOp_wrap_total .mul l.width l.signed (decodeScalar l) (decodeScalar r) rfl
    exact ⟨sv, hEq, hW, hS, hWf⟩
  | div | rem | addUnchecked | subUnchecked | mulUnchecked
  | addWithOverflow | subWithOverflow | mulWithOverflow
  | shl | shr | shlUnchecked | shrUnchecked
  | eq | lt | le | ne | ge | gt | cmp | offset =>
    cases hOp

private theorem evalShiftComp_scalar_total (op : BinOp) (l r : ScalarVal)
    (hOp : (match op with | .shl | .shr => true | _ => false) = true) :
    ∃ sv : ScalarVal,
      evalBinOpComp op (.scalar l) (.scalar r) = .ok (.scalar sv) ∧
      sv.width = l.width ∧ sv.signed = l.signed ∧ ScalarVal.wf sv = true := by
  rw [evalBinOpComp_eq]
  have hShift : op.isShift = true := by
    cases op <;> first | rfl | (cases hOp)
  dsimp only [evalBinOp]
  rw [hShift]
  dsimp only [evalShiftOp]
  cases op with
  | shl =>
    let amount := intEmod (decodeScalar r) (Int.ofNat l.width.bitWidth)
    let ⟨sv, _, hTr, hW, hS, hWf⟩ :=
      truncateScalar_ok l.width l.signed (intShiftLeft (decodeScalar l) amount.toNat)
    refine ⟨sv, ?_, hW, hS, hWf⟩
    rw [hTr]
    cases (amount != decodeScalar r) <;> rfl
  | shr =>
    let amount := intEmod (decodeScalar r) (Int.ofNat l.width.bitWidth)
    let ⟨sv, _, hTr, hW, hS, hWf⟩ :=
      truncateScalar_ok l.width l.signed (intShiftRight (decodeScalar l) amount.toNat)
    refine ⟨sv, ?_, hW, hS, hWf⟩
    rw [hTr]
    cases (amount != decodeScalar r) <;> rfl
  | add | sub | mul | div | rem | addUnchecked | subUnchecked | mulUnchecked
  | addWithOverflow | subWithOverflow | mulWithOverflow
  | shlUnchecked | shrUnchecked | bitAnd | bitOr | bitXor
  | eq | lt | le | ne | ge | gt | cmp | offset =>
    cases hOp

private theorem evalUnOpComp_scalar_total (op : UnOp) (sv : ScalarVal)
    (hOk : op = .not ∨ (op = .neg ∧ sv.signed = true)) :
    ∃ sv' : ScalarVal,
      evalUnOpComp op (.scalar sv) = .ok (.scalar sv') ∧
      sv'.width = sv.width ∧ sv'.signed = sv.signed ∧ ScalarVal.wf sv' = true := by
  rw [evalUnOpComp_eq]
  cases op with
  | not =>
    dsimp only [evalUnOp]
    let ⟨sv', _, hTr, hW, hS, hWf⟩ :=
      truncateScalar_ok sv.width sv.signed (intNot (decodeScalar sv))
    refine ⟨sv', ?_, hW, hS, hWf⟩
    rw [hTr]
  | neg =>
    have hSig : sv.signed = true := by
      cases hOk with
      | inl h => cases h
      | inr h => exact h.2
    dsimp only [evalUnOp]
    rw [hSig]
    let ⟨sv', _, hTr, hW, hS, hWf⟩ :=
      truncateScalar_ok sv.width true (Neg.neg (decodeScalar sv))
    refine ⟨sv', ?_, hW, hS, hWf⟩
    rw [hTr]
    rfl
  | ptrMetadata =>
    cases hOk with
    | inl h => cases h
    | inr h => cases h.1

/-- Soundness of `SymScalar.eval`: well-formed expressions preserve width,
signedness, and `ScalarVal.wf` under every `SymEnv`. -/
theorem symScalar_eval_meta (env : SymEnv) :
    ∀ (s : SymScalar), s.wf = true →
      (s.eval env).width = s.width ∧
      (s.eval env).signed = s.signed ∧
      ScalarVal.wf (s.eval env) = true
  | .lit sv, _ =>
    ⟨rfl, rfl, scalarWf_of_truncateBitsComp sv.width sv.signed sv.bits⟩
  | .var id w sg, _ => by
    dsimp only [SymScalar.eval, SymScalar.width, SymScalar.signed]
    cases env id with
    | scalar sv => exact ⟨rfl, rfl, scalarWf_of_truncateBitsComp w sg sv.bits⟩
    | ptr _ | slicePtr _ _ | bool _ | char _ | ordering _ | unit | enumVal _ _
    | tuple _ | array _ | bytes _ | rangeTo _ | rangeFrom _ | optionVal _
    | range _ _ =>
      exact ⟨rfl, rfl, by cases w <;> rfl⟩
  | .unOp op arg, hWf => by
    cases op with
    | ptrMetadata => cases hWf
    | not =>
      have hA := symScalar_eval_meta env arg hWf
      let ⟨sv', hEq, hW, hS, hWf'⟩ :=
        evalUnOpComp_scalar_total .not (arg.eval env) (Or.inl rfl)
      dsimp only [SymScalar.eval, SymScalar.width, SymScalar.signed]
      rw [hEq]
      exact ⟨hW.trans hA.1, hS.trans hA.2.1, hWf'⟩
    | neg =>
      have hAnd := (Bool.and_eq_true _ _).mp hWf
      have hA := symScalar_eval_meta env arg hAnd.2
      have hSig : (arg.eval env).signed = true := hA.2.1.trans hAnd.1
      let ⟨sv', hEq, hW, hS, hWf'⟩ :=
        evalUnOpComp_scalar_total .neg (arg.eval env) (Or.inr ⟨rfl, hSig⟩)
      dsimp only [SymScalar.eval, SymScalar.width, SymScalar.signed]
      rw [hEq]
      exact ⟨hW.trans hA.1, hS.trans hA.2.1, hWf'⟩
  | .binOp op l r, hWf => by
    have h1 := (Bool.and_eq_true _ _).mp hWf
    have h2 := (Bool.and_eq_true _ _).mp h1.1
    have h3 := (Bool.and_eq_true _ _).mp h2.1
    have h4 := (Bool.and_eq_true _ _).mp h3.1
    have hL := symScalar_eval_meta env l h4.1
    have hR := symScalar_eval_meta env r h4.2
    have hW : l.width = r.width := by
      rw [intWidthBeqComp_eq] at h3
      exact IntWidth.beq_iff.mp h3.2
    have hS : l.signed = r.signed := by
      rw [boolBeqComp_eq] at h2
      exact beq_iff_eq.mp h2.2
    let ⟨sv', hEq, hWv, hSv, hWfv⟩ :=
      evalBinOpComp_scalar_total op (l.eval env) (r.eval env)
        (hL.1.trans (hW.trans hR.1.symm))
        (hL.2.1.trans (hS.trans hR.2.1.symm)) h1.2
    dsimp only [SymScalar.eval, SymScalar.width, SymScalar.signed]
    rw [hEq]
    exact ⟨hWv.trans hL.1, hSv.trans hL.2.1, hWfv⟩
  | .shift op l r, hWf => by
    have h1 := (Bool.and_eq_true _ _).mp hWf
    have h2 := (Bool.and_eq_true _ _).mp h1.1
    have hL := symScalar_eval_meta env l h2.1
    let ⟨sv', hEq, hWv, hSv, hWfv⟩ :=
      evalShiftComp_scalar_total op (l.eval env) (r.eval env) h1.2
    dsimp only [SymScalar.eval, SymScalar.width, SymScalar.signed]
    rw [hEq]
    exact ⟨hWv.trans hL.1, hSv.trans hL.2.1, hWfv⟩
  | .cast dstW dstS src, _ => by
    dsimp only [SymScalar.eval, SymScalar.width, SymScalar.signed]
    rw [evalIntToIntCastComp_eq]
    dsimp only [evalIntToIntCast, intLikeBits]
    cases (src.eval env).signed <;>
      exact ⟨rfl, rfl, scalarWf_truncateBits dstW dstS _⟩

/-- Every well-formed `SymScalar` `.lit sv` evaluates to `sv`. -/
theorem symScalar_lit_eval {sv : ScalarVal} {env : SymEnv}
    (hWf : (SymScalar.lit sv).wf = true) :
    (SymScalar.lit sv).eval env = sv := by
  dsimp only [SymScalar.wf] at hWf
  have hTrunc : truncateBitsComp sv.width sv.bits = sv.bits := by
    rw [truncateBitsComp_eq, bv128BeqComp_eq_beq] at hWf
    rw [truncateBitsComp_eq]
    exact beq_iff_eq.mp hWf
  dsimp only [SymScalar.eval]
  cases sv with
  | mk w s b =>
    dsimp only at hTrunc
    rw [hTrunc]

/-- Any `env id` satisfying `checkVal (env id) (.int w s) = true` matches
`.scalar ((SymScalar.var id w s).eval env)`. -/
theorem symScalar_var_eval {env : SymEnv} {id : Nat} {w : IntWidth} {s : Bool}
    (h : checkVal (env id) (.int w s) = true) :
    Val.scalar ((SymScalar.var id w s).eval env) = env id := by
  let ⟨bits, hEq, hTrunc⟩ := checkVal_int_iff.mp h
  dsimp only [SymScalar.eval]
  rw [hEq]
  dsimp only
  rw [truncateBitsComp_eq, hTrunc]

/-! ### `BvLin` Bridge Across All Widths and Signedness Modes -/

private theorem bvPow2_eq_two_pow_local : ∀ w : Nat, bvPow2 w = Nat.pow 2 w
  | 0 => rfl
  | w + 1 => by
    have hSucc : Nat.pow 2 (w + 1) = Nat.pow 2 w * 2 := Nat.pow_succ 2 w
    change 2 * bvPow2 w = Nat.pow 2 (w + 1)
    rw [bvPow2_eq_two_pow_local w, hSucc, Nat.mul_comm]

private theorem bvOfInt_eq_mirBvOfInt (w : Nat) :
    ∀ (x : Int), Anneal.PureLift.BvLin.bvOfInt w x = Trusted.MirSemantics.bvOfInt w x
  | .ofNat n => by
    apply bv_eq_of_toNat_eq
    unfold Anneal.PureLift.BvLin.bvOfInt Trusted.MirSemantics.bvOfInt intEmod
    dsimp only [Int.natAbs, Int.toNat]
    rw [bv_toNat_ofNat, bv_toNat_ofNat,
      nat_mod_eq_of_lt (nat_mod_lt n (nat_two_pow_pos w))]
  | .negSucc n => by
    apply bv_eq_of_toNat_eq
    rw [Anneal.PureLift.BvLin.bvOfInt_toNat_eq_intModPow2]
    unfold Trusted.MirSemantics.bvOfInt intEmod
    dsimp only [Int.natAbs]
    let m := Nat.pow 2 w
    have hm : 0 < m := nat_two_pow_pos w
    have hModLt : Nat.mod n m < m := nat_mod_lt n hm
    have hSuccLe : Nat.succ (Nat.mod n m) ≤ m := hModLt
    have hSub :
        Int.subNatNat m (Nat.succ (Nat.mod n m)) =
          Int.ofNat (m - Nat.succ (Nat.mod n m)) := by
      unfold Int.subNatNat
      rw [Nat.sub_eq_zero_of_le hSuccLe]
    rw [hSub]
    dsimp only [Int.toNat]
    have hSubLt : m - Nat.succ (Nat.mod n m) < m :=
      Nat.sub_lt hm (Nat.succ_pos _)
    rw [bv_toNat_ofNat, nat_mod_eq_of_lt hSubLt]
    unfold intModPow2
    rw [bvPow2_eq_two_pow_local]
    dsimp only
    change cond (Nat.beq (Nat.mod (n + 1) m) 0) 0 (m - Nat.mod (n + 1) m) = _
    have hN1Mod : Nat.mod (n + 1) m = Nat.mod (Nat.succ (Nat.mod n m)) m := by
      have hDm : m * Nat.div n m + Nat.mod n m = n := Nat.div_add_mod n m
      have hEq : n + 1 = m * Nat.div n m + Nat.succ (Nat.mod n m) :=
        (congrArg (fun t => t + 1) hDm.symm).trans (Nat.add_assoc _ _ _)
      have hMulMod := Nat.mul_add_mod_self_left m (Nat.div n m)
        (Nat.succ (Nat.mod n m))
      rw [hEq]
      exact hMulMod
    cases Nat.lt_or_ge (Nat.succ (Nat.mod n m)) m with
    | inl hLt =>
      have hModEq : Nat.mod (n + 1) m = Nat.succ (Nat.mod n m) :=
        hN1Mod.trans (Nat.mod_eq_of_lt hLt)
      have hNz : Nat.beq (Nat.mod (n + 1) m) 0 = false := by
        rw [hModEq]
        rfl
      rw [hNz, hModEq]
      rfl
    | inr hGe =>
      have hEqM : Nat.succ (Nat.mod n m) = m := Nat.le_antisymm hSuccLe hGe
      have hModZero : Nat.mod (n + 1) m = 0 := by
        rw [hN1Mod, hEqM]
        exact Nat.mod_self m
      have hZ : Nat.beq (Nat.mod (n + 1) m) 0 = true := by
        rw [hModZero]
        rfl
      rw [hZ, hEqM, Nat.sub_self]
      rfl

private theorem intWidth_pow128_factor (w : IntWidth) :
    ∃ k : Nat, Nat.pow 2 128 = Nat.pow 2 w.bitWidth * k := by
  cases w with
  | i8 => exact ⟨Nat.pow 2 120, by decide⟩
  | i16 => exact ⟨Nat.pow 2 112, by decide⟩
  | i32 => exact ⟨Nat.pow 2 96, by decide⟩
  | i64 | isize => exact ⟨Nat.pow 2 64, by decide⟩
  | i128 => exact ⟨1, by decide⟩

private theorem nat_mod_mod_of_mul {n a b : Nat} :
    Nat.mod (Nat.mod n (a * b)) a = Nat.mod n a := by
  have hDm : (a * b) * Nat.div n (a * b) + Nat.mod n (a * b) = n :=
    Nat.div_add_mod n (a * b)
  have hEq : n = a * (b * Nat.div n (a * b)) + Nat.mod n (a * b) := by
    rw [← Nat.mul_assoc, hDm]
  have h1 : Nat.mod (a * (b * Nat.div n (a * b)) + Nat.mod n (a * b)) a =
      Nat.mod (Nat.mod n (a * b)) a := Nat.mul_add_mod_self_left a _ _
  rw [← hEq] at h1
  exact h1.symm

private theorem bitVec_ofNat_pow128_zero (w : IntWidth) :
    BitVec.ofNat w.bitWidth (Nat.pow 2 128) = bvZero w.bitWidth := by
  apply bv_eq_of_toNat_eq
  let ⟨k, hK⟩ := intWidth_pow128_factor w
  rw [bv_toNat_ofNat, hK, nat_mul_mod_right]
  rfl

private theorem toNat_truncateBits_bvOfInt (w : IntWidth) (x : Int) :
    BitVec.ofNat w.bitWidth
      (truncateBits w (Trusted.MirSemantics.bvOfInt 128 x)).toNat =
      Anneal.PureLift.BvLin.bvOfInt w.bitWidth x := by
  rw [toNat_truncateBits, intWidthModulus_eq_pow, ← bvOfInt_eq_mirBvOfInt 128 x]
  change BitVec.ofNat w.bitWidth
    (Nat.mod (Anneal.PureLift.BvLin.bvOfInt 128 x).toNat (Nat.pow 2 w.bitWidth)) = _
  rw [bv_ofNat_mod]
  let ⟨k, hK⟩ := intWidth_pow128_factor w
  cases x with
  | ofNat n =>
    unfold Anneal.PureLift.BvLin.bvOfInt
    rw [bv_toNat_ofNat, hK]
    dsimp only
    apply bv_eq_of_toNat_eq
    rw [bv_toNat_ofNat, bv_toNat_ofNat, nat_mod_mod_of_mul]
  | negSucc n =>
    rw [Anneal.PureLift.BvLin.bvOfInt_toNat_eq_intModPow2]
    unfold intModPow2
    rw [bvPow2_eq_two_pow_local]
    dsimp only
    let r128 := Nat.mod (n + 1) (Nat.pow 2 128)
    let rW := Nat.mod (n + 1) (Nat.pow 2 w.bitWidth)
    have hR : Nat.mod r128 (Nat.pow 2 w.bitWidth) = rW := by
      dsimp only [r128, rW]
      rw [hK]
      exact nat_mod_mod_of_mul
    change BitVec.ofNat w.bitWidth
        (cond (Nat.beq r128 0) 0 (Nat.pow 2 128 - r128)) =
      bvNeg (BitVec.ofNat w.bitWidth (n + 1))
    cases hZ : Nat.beq r128 0 with
    | true =>
      have hr0 : r128 = 0 := Nat.eq_of_beq_eq_true hZ
      have hrw0 : rW = 0 := by rw [← hR, hr0]; rfl
      have hNeg0 : BitVec.ofNat w.bitWidth (n + 1) = bvZero w.bitWidth := by
        apply bv_eq_of_toNat_eq
        rw [bv_toNat_ofNat]
        exact hrw0
      rw [hNeg0]
      dsimp only [cond]
      have hNegZ : bvNeg (bvZero w.bitWidth) = bvZero w.bitWidth :=
        (bv_neg_unique (bv_add_zero (bvZero w.bitWidth))).symm
      rw [hNegZ]
      rfl
    | false =>
      dsimp only [cond]
      have hLe : r128 ≤ Nat.pow 2 128 :=
        Nat.le_of_lt (Nat.mod_lt (n + 1) (Nat.two_pow_pos 128))
      have hSum : (Nat.pow 2 128 - r128) + r128 = Nat.pow 2 128 :=
        Nat.sub_add_cancel hLe
      have hAdd0 :
          BitVec.ofNat w.bitWidth (n + 1) +
            BitVec.ofNat w.bitWidth (Nat.pow 2 128 - r128) =
            bvZero w.bitWidth := by
        rw [← bv_ofNat_mod w.bitWidth (n + 1)]
        change BitVec.ofNat w.bitWidth rW +
            BitVec.ofNat w.bitWidth (Nat.pow 2 128 - r128) =
          bvZero w.bitWidth
        rw [← hR]
        rw [bv_ofNat_mod, ← bv_ofNat_add, Nat.add_comm r128 _, hSum]
        exact bitVec_ofNat_pow128_zero w
      exact bv_neg_unique hAdd0

private theorem bvOfInt_bvToInt_128 (w : IntWidth) (y : BitVec 128) :
    Anneal.PureLift.BvLin.bvOfInt w.bitWidth (bvToInt y) = BitVec.ofNat w.bitWidth y.toNat := by
  unfold bvToInt
  cases Nat.lt_or_ge (2 * y.toNat) (Nat.pow 2 128) with
  | inl hLt =>
    rw [ite_prop_true hLt]
    rfl
  | inr hGe =>
    rw [ite_prop_false (Nat.not_lt_of_ge hGe), bvOfInt_sub]
    change Anneal.PureLift.BvLin.bvOfInt w.bitWidth (Int.ofNat y.toNat) -
        BitVec.ofNat w.bitWidth (Nat.pow 2 128) =
      BitVec.ofNat w.bitWidth y.toNat
    rw [bitVec_ofNat_pow128_zero w, bv_sub_eq_add_neg]
    have hNegZ : bvNeg (bvZero w.bitWidth) = bvZero w.bitWidth := by
      apply (bv_neg_unique (bv_add_zero (bvZero w.bitWidth))).symm
    rw [hNegZ, bv_add_zero]
    rfl

/-- Modular `BvLin` projection of `decodeScalar sv` at `sv.width.bitWidth`
agrees with `sv.bits` across both signed and unsigned scalars. -/
theorem bvOfInt_decodeScalar (sv : ScalarVal) :
    Anneal.PureLift.BvLin.bvOfInt sv.width.bitWidth (decodeScalar sv) =
      BitVec.ofNat sv.width.bitWidth sv.bits.toNat := by
  unfold decodeScalar
  have hTruncToNat :
      BitVec.ofNat sv.width.bitWidth (truncateBits sv.width sv.bits).toNat =
        BitVec.ofNat sv.width.bitWidth sv.bits.toNat := by
    rw [toNat_truncateBits, intWidthModulus_eq_pow]
    exact bv_ofNat_mod sv.width.bitWidth sv.bits.toNat
  cases sv.signed with
  | false =>
    exact hTruncToNat
  | true =>
    dsimp only [signExtendBits, bvSignExtend]
    rw [ite_prop_true (rfl : true = true)]
    let low := bvExtractLsb (sv.width.bitWidth - 1) 0 (truncateBits sv.width sv.bits)
    rw [← bvOfInt_eq_mirBvOfInt 128 (bvToInt low),
      bvOfInt_bvToInt_128 sv.width _]
    have hPowMod : Nat.mod (Nat.pow 2 128) (Nat.pow 2 sv.width.bitWidth) = 0 := by
      let ⟨k, hK⟩ := intWidth_pow128_factor sv.width
      rw [hK]
      exact nat_mul_mod_right (Nat.pow 2 sv.width.bitWidth) k
    have hLow : BitVec.ofNat sv.width.bitWidth low.toNat =
        BitVec.ofNat sv.width.bitWidth sv.bits.toNat := by
      apply bv_eq_of_toNat_eq
      dsimp only [low, bvExtractLsb, bvExtractLsb']
      have hSubAdd : sv.width.bitWidth - 1 - 0 + 1 = sv.width.bitWidth := by
        cases sv.width <;> decide
      rw [bv_toNat_ofNat, bv_toNat_ofNat, hSubAdd, nat_shiftRight_zero,
        toNat_truncateBits, intWidthModulus_eq_pow, bv_toNat_ofNat]
      rw [nat_mod_mod_pos (sv.bits.toNat.mod (Nat.pow 2 sv.width.bitWidth))
        (nat_two_pow_pos sv.width.bitWidth)]
      exact nat_mod_mod_pos sv.bits.toNat (nat_two_pow_pos sv.width.bitWidth)
    rw [Anneal.PureLift.BvLin.bvOfInt_toNat_eq_intModPow2]
    unfold intModPow2
    rw [bvPow2_eq_two_pow_local]
    dsimp only
    cases hBt : bvToInt low with
    | ofNat n =>
      dsimp only
      let ⟨k, hK⟩ := intWidth_pow128_factor sv.width
      have h1 : BitVec.ofNat sv.width.bitWidth (Nat.mod n (Nat.pow 2 128)) =
          BitVec.ofNat sv.width.bitWidth n := by
        rw [hK]
        apply bv_eq_of_toNat_eq
        rw [bv_toNat_ofNat, bv_toNat_ofNat, nat_mod_mod_of_mul]
      rw [h1]
      have hRev : Anneal.PureLift.BvLin.bvOfInt sv.width.bitWidth (bvToInt low) =
          BitVec.ofNat sv.width.bitWidth n := by
        rw [hBt]
        rfl
      rw [← hRev]
      have hLowBt : Anneal.PureLift.BvLin.bvOfInt sv.width.bitWidth (bvToInt low) =
          BitVec.ofNat sv.width.bitWidth low.toNat := by
        unfold bvToInt
        have hW : sv.width.bitWidth - 1 - 0 + 1 = sv.width.bitWidth := by
          cases sv.width <;> decide
        cases Nat.lt_or_ge (2 * low.toNat)
            (Nat.pow 2 (sv.width.bitWidth - 1 - 0 + 1)) with
        | inl hLt =>
          rw [ite_prop_true hLt]
          rfl
        | inr hGe =>
          have hPowW : Nat.pow 2 (sv.width.bitWidth - 1 - 0 + 1) =
              Nat.pow 2 sv.width.bitWidth :=
            congrArg (Nat.pow 2) hW
          rw [ite_prop_false (Nat.not_lt_of_ge hGe), hPowW, bvOfInt_sub]
          change _ - BitVec.ofNat sv.width.bitWidth (Nat.pow 2 sv.width.bitWidth) = _
          have hZero : BitVec.ofNat sv.width.bitWidth (Nat.pow 2 sv.width.bitWidth) =
              bvZero sv.width.bitWidth := by
            apply bv_eq_of_toNat_eq
            change Nat.mod (Nat.pow 2 sv.width.bitWidth)
              (Nat.pow 2 sv.width.bitWidth) = 0
            exact Nat.mod_self _
          rw [hZero, bv_sub_eq_add_neg]
          have hNegZ : bvNeg (bvZero sv.width.bitWidth) =
              bvZero sv.width.bitWidth :=
            (bv_neg_unique (bv_add_zero (bvZero sv.width.bitWidth))).symm
          rw [hNegZ, bv_add_zero]
          rfl
      exact hLowBt.trans hLow
    | negSucc n =>
      dsimp only
      let ⟨k, hK⟩ := intWidth_pow128_factor sv.width
      let r128 := Nat.mod (n + 1) (Nat.pow 2 128)
      let rW := Nat.mod (n + 1) (Nat.pow 2 sv.width.bitWidth)
      have hR : Nat.mod r128 (Nat.pow 2 sv.width.bitWidth) = rW := by
        dsimp only [r128, rW]
        rw [hK]
        exact nat_mod_mod_of_mul
      have hCond : BitVec.ofNat sv.width.bitWidth
            (cond (Nat.beq r128 0) 0 (Nat.pow 2 128 - r128)) =
          bvNeg (BitVec.ofNat sv.width.bitWidth (n + 1)) := by
        cases hz : Nat.beq r128 0 with
        | true =>
          have hr0 := Nat.eq_of_beq_eq_true hz
          have hrw0 : rW = 0 := by rw [← hR, hr0]; rfl
          have hZ : BitVec.ofNat sv.width.bitWidth (n + 1) =
              bvZero sv.width.bitWidth := by
            apply bv_eq_of_toNat_eq
            rw [bv_toNat_ofNat]
            exact hrw0
          rw [hZ]
          have hNegZ : bvNeg (bvZero sv.width.bitWidth) =
              bvZero sv.width.bitWidth :=
            (bv_neg_unique (bv_add_zero (bvZero sv.width.bitWidth))).symm
          rw [hNegZ]
          rfl
        | false =>
          dsimp only [cond]
          have hLe : r128 ≤ Nat.pow 2 128 :=
            Nat.le_of_lt (Nat.mod_lt (n + 1) (Nat.two_pow_pos 128))
          have hSum : (Nat.pow 2 128 - r128) + r128 = Nat.pow 2 128 :=
            Nat.sub_add_cancel hLe
          refine bv_neg_unique ?_
          rw [← bv_ofNat_mod sv.width.bitWidth (n + 1)]
          change BitVec.ofNat sv.width.bitWidth rW +
              BitVec.ofNat sv.width.bitWidth (Nat.pow 2 128 - r128) =
            bvZero sv.width.bitWidth
          rw [← hR, bv_ofNat_mod, ← bv_ofNat_add, Nat.add_comm r128 _, hSum]
          exact bitVec_ofNat_pow128_zero sv.width
      rw [hCond]
      have hRev : Anneal.PureLift.BvLin.bvOfInt sv.width.bitWidth (bvToInt low) =
          bvNeg (BitVec.ofNat sv.width.bitWidth (n + 1)) := by
        rw [hBt]
        rfl
      rw [← hRev]
      have hLowBt : Anneal.PureLift.BvLin.bvOfInt sv.width.bitWidth (bvToInt low) =
          BitVec.ofNat sv.width.bitWidth low.toNat := by
        unfold bvToInt
        have hW : sv.width.bitWidth - 1 - 0 + 1 = sv.width.bitWidth := by
          cases sv.width <;> decide
        cases Nat.lt_or_ge (2 * low.toNat)
            (Nat.pow 2 (sv.width.bitWidth - 1 - 0 + 1)) with
        | inl hLt =>
          rw [ite_prop_true hLt]
          rfl
        | inr hGe =>
          have hPowW : Nat.pow 2 (sv.width.bitWidth - 1 - 0 + 1) =
              Nat.pow 2 sv.width.bitWidth :=
            congrArg (Nat.pow 2) hW
          rw [ite_prop_false (Nat.not_lt_of_ge hGe), hPowW, bvOfInt_sub]
          change _ - BitVec.ofNat sv.width.bitWidth (Nat.pow 2 sv.width.bitWidth) = _
          have hZero : BitVec.ofNat sv.width.bitWidth (Nat.pow 2 sv.width.bitWidth) =
              bvZero sv.width.bitWidth := by
            apply bv_eq_of_toNat_eq
            change Nat.mod (Nat.pow 2 sv.width.bitWidth)
              (Nat.pow 2 sv.width.bitWidth) = 0
            exact Nat.mod_self _
          rw [hZero, bv_sub_eq_add_neg]
          have hNegZ : bvNeg (bvZero sv.width.bitWidth) =
              bvZero sv.width.bitWidth :=
            (bv_neg_unique (bv_add_zero (bvZero sv.width.bitWidth))).symm
          rw [hNegZ, bv_add_zero]
          rfl
      exact hLowBt.trans hLow

/-- Compile a linear `SymScalar` subexpression at width `w` into `LinExpr`. -/
@[expose] noncomputable def SymScalar.toBvLin? (w : IntWidth) : SymScalar → Option LinExpr
  | .lit sv =>
    if intWidthBeqComp sv.width w &&
        bv128BeqComp (truncateBitsComp w sv.bits) sv.bits then
      some (.constNat sv.bits.toNat)
    else none
  | .var id w' _ =>
    if intWidthBeqComp w' w then some (.bvVar id) else none
  | .unOp .neg a =>
    match a.toBvLin? w with
    | some ea => if intWidthBeqComp a.width w then some (.neg ea) else none
    | none => none
  | .binOp .add l r =>
    match l.toBvLin? w, r.toBvLin? w with
    | some el, some er =>
      if intWidthBeqComp l.width w && intWidthBeqComp r.width w then
        some (.add el er)
      else none
    | _, _ => none
  | .binOp .sub l r =>
    match l.toBvLin? w, r.toBvLin? w with
    | some el, some er =>
      if intWidthBeqComp l.width w && intWidthBeqComp r.width w then
        some (.sub el er)
      else none
    | _, _ => none
  | .binOp .mul (.lit k) r =>
    match r.toBvLin? w with
    | some er =>
      if intWidthBeqComp k.width w && intWidthBeqComp r.width w && !k.signed then
        some (.scale (Int.ofNat (truncateBitsComp w k.bits).toNat) er)
      else none
    | none => none
  | .binOp .mul (.var id wl sl) (.lit k) =>
    match (SymScalar.var id wl sl).toBvLin? w with
    | some el =>
      if intWidthBeqComp wl w && intWidthBeqComp k.width w && !k.signed then
        some (.scale (Int.ofNat (truncateBitsComp w k.bits).toNat) el)
      else none
    | none => none
  | _ => none

/-- Construct a `BvLinEnv` of width `w.bitWidth` from `env : SymEnv`. -/
@[expose] noncomputable def toBvLinEnv (w : IntWidth) (env : SymEnv) :
    BvLinEnv (bitWidthComp w) where
  bvAtom id :=
    BitVec.ofNat (bitWidthComp w)
      (match env id with | .scalar sv => sv.bits.toNat | _ => 0)
  natAtom _ := 0

private theorem bitWidthComp_eq_bitWidth (w : IntWidth) :
    bitWidthComp w = w.bitWidth :=
  bitWidthComp_eq w

private theorem bitVec_ofNat_toNat_neg {m n : Nat} (h : m = n)
    (x : BitVec m) :
    bvNeg (BitVec.ofNat n x.toNat) = BitVec.ofNat n (bvNeg x).toNat := by
  cases h; rw [bv_ofNat_toNat, bv_ofNat_toNat]

private theorem bitVec_ofNat_toNat_add {m n : Nat} (h : m = n)
    (x y : BitVec m) :
    BitVec.ofNat n x.toNat + BitVec.ofNat n y.toNat =
      BitVec.ofNat n (x + y).toNat := by
  cases h; rw [bv_ofNat_toNat, bv_ofNat_toNat, bv_ofNat_toNat]

private theorem bitVec_ofNat_toNat_sub {m n : Nat} (h : m = n)
    (x y : BitVec m) :
    BitVec.ofNat n x.toNat - BitVec.ofNat n y.toNat =
      BitVec.ofNat n (x - y).toNat := by
  cases h; rw [bv_ofNat_toNat, bv_ofNat_toNat, bv_ofNat_toNat]

private theorem bitVec_ofNat_toNat_scale {m n : Nat} (h : m = n)
    (c : Int) (x : BitVec m) :
    bvScale c (BitVec.ofNat n x.toNat) =
      BitVec.ofNat n (bvScale c x).toNat := by
  cases h; rw [bv_ofNat_toNat, bv_ofNat_toNat]

private theorem mirBvOfInt_bvToInt_128 (x : Int) :
    Trusted.MirSemantics.bvOfInt 128
        (bvToInt (Trusted.MirSemantics.bvOfInt 128 x)) =
      Trusted.MirSemantics.bvOfInt 128 x := by
  have h := bvOfInt_bvToInt_128 .i128
    (Anneal.PureLift.BvLin.bvOfInt 128 x)
  change Anneal.PureLift.BvLin.bvOfInt 128
      (bvToInt (Anneal.PureLift.BvLin.bvOfInt 128 x)) =
    BitVec.ofNat 128 (Anneal.PureLift.BvLin.bvOfInt 128 x).toNat at h
  rw [← bvOfInt_eq_mirBvOfInt 128 x, ← bvOfInt_eq_mirBvOfInt 128 _, h, bv_ofNat_toNat]

private theorem truncateScalar_bits (w : IntWidth) (s : Bool) (x : Int)
    {sv : ScalarVal} {lossy : Bool}
    (hTr : truncateScalar w s x = .ok (sv, lossy)) :
    sv.bits = truncateBits w (Trusted.MirSemantics.bvOfInt 128 x) := by
  unfold truncateScalar at hTr
  cases s with
  | false => cases hTr; rfl
  | true =>
    dsimp only at hTr
    rw [bvToInt_in_i128_range] at hTr
    cases hTr
    dsimp only
    rw [mirBvOfInt_bvToInt_128]

private theorem decodeScalar_symLit_unsigned (k : ScalarVal) (w : IntWidth)
    (hKs : k.signed = false) (hWk : k.width = w) (env : SymEnv) :
    decodeScalar ((SymScalar.lit k).eval env) =
      Int.ofNat (truncateBitsComp w k.bits).toNat := by
  cases k with
  | mk kw ks kb =>
    dsimp only at hKs hWk
    subst hKs; subst hWk
    dsimp only [SymScalar.eval, decodeScalar]
    rw [truncateBitsComp_eq, truncateBits_idem]
    rfl

private theorem int_mul_ofNat_comm :
    ∀ (x : Int) (n : Nat), x * Int.ofNat n = Int.ofNat n * x
  | .ofNat m, n => congrArg Int.ofNat (Nat.mul_comm m n)
  | .negSucc m, n => by
    change Int.negOfNat (Nat.succ m * n) = Int.negOfNat (n * Nat.succ m)
    rw [Nat.mul_comm]

private theorem evalBinOpComp_wrap_arith (op : BinOp)
    (hArith : (match op with | .add | .sub | .mul => true | _ => false) = true)
    (l r : ScalarVal) (hw : l.width = r.width) (hs : l.signed = r.signed) :
    ∃ sv : ScalarVal,
      evalBinOpComp op (.scalar l) (.scalar r) = .ok (.scalar sv) ∧
      sv.width = l.width ∧
      sv.bits = truncateBits l.width (Trusted.MirSemantics.bvOfInt 128
        (match op with
         | .add => decodeScalar l + decodeScalar r
         | .sub => decodeScalar l - decodeScalar r
         | _ => decodeScalar l * decodeScalar r)) := by
  rw [evalBinOpComp_eq]
  dsimp only [evalBinOp]
  have hNotShift : op.isShift = false := by
    cases op <;> first | rfl | cases hArith
  have hMatch :
      (!(IntWidth.beq l.width r.width && (l.signed == r.signed))) = false := by
    rw [hw, hs]
    cases r.width <;> cases r.signed <;> rfl
  rw [hNotShift, hMatch]
  cases op with
  | div | rem | addUnchecked | subUnchecked | mulUnchecked
  | addWithOverflow | subWithOverflow | mulWithOverflow
  | shl | shr | shlUnchecked | shrUnchecked | bitAnd | bitOr | bitXor
  | eq | lt | le | ne | ge | gt | cmp | offset => cases hArith
  | add =>
    let ⟨sv, _, hEq, hTr, hW, _, _⟩ :=
      evalArithOp_wrap_total .add l.width l.signed (decodeScalar l)
        (decodeScalar r) rfl
    exact ⟨sv, hEq, hW, truncateScalar_bits l.width l.signed _ hTr⟩
  | sub =>
    let ⟨sv, _, hEq, hTr, hW, _, _⟩ :=
      evalArithOp_wrap_total .sub l.width l.signed (decodeScalar l)
        (decodeScalar r) rfl
    exact ⟨sv, hEq, hW, truncateScalar_bits l.width l.signed _ hTr⟩
  | mul =>
    let ⟨sv, _, hEq, hTr, hW, _, _⟩ :=
      evalArithOp_wrap_total .mul l.width l.signed (decodeScalar l)
        (decodeScalar r) rfl
    exact ⟨sv, hEq, hW, truncateScalar_bits l.width l.signed _ hTr⟩

/-- Soundness of `SymScalar.toBvLin?`: evaluated modular bits match
`LinExpr.evalBv`. -/
theorem symScalar_toBvLin?_sound (w : IntWidth) (env : SymEnv) :
    ∀ (s : SymScalar) (e : LinExpr),
      s.wf = true → s.toBvLin? w = some e →
      BitVec.ofNat w.bitWidth (s.eval env).bits.toNat =
        BitVec.ofNat w.bitWidth (e.evalBv (toBvLinEnv w env)).toNat
  | .lit sv, e, _, h => by
    dsimp only [SymScalar.toBvLin?] at h
    cases hc : intWidthBeqComp sv.width w &&
        bv128BeqComp (truncateBitsComp w sv.bits) sv.bits with
    | false => rw [hc] at h; cases h
    | true =>
      rw [hc] at h
      cases h
      have hAnd := (Bool.and_eq_true _ _).mp hc
      have hW : sv.width = w := by
        rw [intWidthBeqComp_eq] at hAnd
        exact IntWidth.beq_iff.mp hAnd.1
      dsimp only [SymScalar.eval, LinExpr.evalBv]
      rw [hW, truncateBitsComp_eq, toNat_truncateBits, intWidthModulus_eq_pow,
        bv_ofNat_mod, bitWidthComp_eq_bitWidth, bv_toNat_ofNat]
      exact (bv_ofNat_mod w.bitWidth sv.bits.toNat).symm
  | .var id w' sg, e, _, h => by
    dsimp only [SymScalar.toBvLin?] at h
    cases hc : intWidthBeqComp w' w with
    | false => rw [hc] at h; cases h
    | true =>
      rw [hc] at h
      cases h
      have hW : w' = w := by
        rw [intWidthBeqComp_eq] at hc
        exact IntWidth.beq_iff.mp hc
      dsimp only [SymScalar.eval, LinExpr.evalBv, toBvLinEnv]
      rw [bitWidthComp_eq_bitWidth, bv_toNat_ofNat, bv_ofNat_mod]
      cases env id with
      | scalar sv =>
        dsimp only
        rw [hW, truncateBitsComp_eq, toNat_truncateBits, intWidthModulus_eq_pow,
          bv_ofNat_mod]
      | ptr _ | slicePtr _ _ | bool _ | char _ | ordering _ | unit | enumVal _ _
      | tuple _ | array _ | bytes _ | rangeTo _ | rangeFrom _ | optionVal _
      | range _ _ =>
        cases w <;> rfl
  | .unOp .neg a, e, hWf, h => by
    have h1 := (Bool.and_eq_true _ _).mp hWf
    dsimp only [SymScalar.toBvLin?] at h
    cases ha : a.toBvLin? w with
    | none => rw [ha] at h; cases h
    | some ea =>
      rw [ha] at h
      cases hcw : intWidthBeqComp a.width w with
      | false => rw [hcw] at h; cases h
      | true =>
        rw [hcw] at h
        cases h
        have hWa : a.width = w := by
          rw [intWidthBeqComp_eq] at hcw
          exact IntWidth.beq_iff.mp hcw
        have hA := symScalar_eval_meta env a h1.2
        have hEvalA := symScalar_toBvLin?_sound w env a ea h1.2 ha
        have hSig : (a.eval env).signed = true := hA.2.1.trans h1.1
        let ⟨sv', hEq, _, _, _⟩ :=
          evalUnOpComp_scalar_total .neg (a.eval env) (Or.inr ⟨rfl, hSig⟩)
        dsimp only [SymScalar.eval]
        rw [hEq]
        rw [evalUnOpComp_eq] at hEq
        dsimp only [evalUnOp] at hEq
        rw [hSig] at hEq
        cases hTr : truncateScalar (a.eval env).width true
            (Neg.neg (decodeScalar (a.eval env))) with
        | error k => rw [hTr] at hEq; cases hEq
        | ok p =>
          rw [hTr] at hEq
          cases hEq
          cases p with
          | mk sv'' lossy =>
            have hSv := truncateScalar_bits (a.eval env).width true _ hTr
            have hW1 : (a.eval env).width = w := hA.1.trans hWa
            change BitVec.ofNat w.bitWidth sv''.bits.toNat = _
            rw [hSv, hW1, toNat_truncateBits_bvOfInt]
            change Anneal.PureLift.BvLin.bvOfInt w.bitWidth
                (Int.neg (decodeScalar (a.eval env))) = _
            rw [Anneal.PureLift.BvLin.bvOfInt_neg]
            have hDec := bvOfInt_decodeScalar (a.eval env)
            rw [hW1] at hDec
            rw [hDec, hEvalA]
            dsimp only [LinExpr.evalBv]
            exact bitVec_ofNat_toNat_neg (bitWidthComp_eq_bitWidth w) _
  | .binOp .add l r, e, hWf, h => by
    have h1 := (Bool.and_eq_true _ _).mp hWf
    have h2 := (Bool.and_eq_true _ _).mp h1.1
    have h3 := (Bool.and_eq_true _ _).mp h2.1
    have h4 := (Bool.and_eq_true _ _).mp h3.1
    dsimp only [SymScalar.toBvLin?] at h
    cases hl : l.toBvLin? w with
    | none => rw [hl] at h; cases h
    | some el =>
      cases hr : r.toBvLin? w with
      | none => rw [hl, hr] at h; cases h
      | some er =>
        rw [hl, hr] at h
        dsimp only at h
        cases hcw : intWidthBeqComp l.width w && intWidthBeqComp r.width w with
        | false => rw [hcw] at h; cases h
        | true =>
          rw [hcw] at h
          cases h
          have hC := (Bool.and_eq_true _ _).mp hcw
          have hWl : l.width = w := by
            rw [intWidthBeqComp_eq, intWidthBeqComp_eq] at hC
            exact IntWidth.beq_iff.mp hC.1
          have hWr : r.width = w := by
            rw [intWidthBeqComp_eq, intWidthBeqComp_eq] at hC
            exact IntWidth.beq_iff.mp hC.2
          have hL := symScalar_eval_meta env l h4.1
          have hR := symScalar_eval_meta env r h4.2
          have hWL : (l.eval env).width = w := hL.1.trans hWl
          have hWR : (r.eval env).width = w := hR.1.trans hWr
          have hW : (l.eval env).width = (r.eval env).width := hWL.trans hWR.symm
          have hS : (l.eval env).signed = (r.eval env).signed := by
            rw [boolBeqComp_eq] at h2
            exact hL.2.1.trans ((beq_iff_eq.mp h2.2).trans hR.2.1.symm)
          have hEvalL := symScalar_toBvLin?_sound w env l el h4.1 hl
          have hEvalR := symScalar_toBvLin?_sound w env r er h4.2 hr
          let ⟨sv, hEq, _, hSv⟩ :=
            evalBinOpComp_wrap_arith .add rfl (l.eval env) (r.eval env) hW hS
          change BitVec.ofNat w.bitWidth
              (match evalBinOpComp BinOp.add (.scalar (l.eval env))
                  (.scalar (r.eval env)) with
               | .ok (.scalar sv) => sv
               | _ => ⟨l.width, l.signed, BitVec.ofNat 128 0⟩).bits.toNat = _
          rw [hEq]
          dsimp only
          rw [hSv, hWL, toNat_truncateBits_bvOfInt, Anneal.PureLift.BvLin.bvOfInt_add]
          have hDL := bvOfInt_decodeScalar (l.eval env)
          have hDR := bvOfInt_decodeScalar (r.eval env)
          rw [hWL] at hDL
          rw [hWR] at hDR
          rw [hDL, hDR, hEvalL, hEvalR]
          dsimp only [LinExpr.evalBv]
          exact bitVec_ofNat_toNat_add (bitWidthComp_eq_bitWidth w) _ _
  | .binOp .sub l r, e, hWf, h => by
    have h1 := (Bool.and_eq_true _ _).mp hWf
    have h2 := (Bool.and_eq_true _ _).mp h1.1
    have h3 := (Bool.and_eq_true _ _).mp h2.1
    have h4 := (Bool.and_eq_true _ _).mp h3.1
    dsimp only [SymScalar.toBvLin?] at h
    cases hl : l.toBvLin? w with
    | none => rw [hl] at h; cases h
    | some el =>
      cases hr : r.toBvLin? w with
      | none => rw [hl, hr] at h; cases h
      | some er =>
        rw [hl, hr] at h
        dsimp only at h
        cases hcw : intWidthBeqComp l.width w && intWidthBeqComp r.width w with
        | false => rw [hcw] at h; cases h
        | true =>
          rw [hcw] at h
          cases h
          have hC := (Bool.and_eq_true _ _).mp hcw
          have hWl : l.width = w := by
            rw [intWidthBeqComp_eq, intWidthBeqComp_eq] at hC
            exact IntWidth.beq_iff.mp hC.1
          have hWr : r.width = w := by
            rw [intWidthBeqComp_eq, intWidthBeqComp_eq] at hC
            exact IntWidth.beq_iff.mp hC.2
          have hL := symScalar_eval_meta env l h4.1
          have hR := symScalar_eval_meta env r h4.2
          have hWL : (l.eval env).width = w := hL.1.trans hWl
          have hWR : (r.eval env).width = w := hR.1.trans hWr
          have hW : (l.eval env).width = (r.eval env).width := hWL.trans hWR.symm
          have hS : (l.eval env).signed = (r.eval env).signed := by
            rw [boolBeqComp_eq] at h2
            exact hL.2.1.trans ((beq_iff_eq.mp h2.2).trans hR.2.1.symm)
          have hEvalL := symScalar_toBvLin?_sound w env l el h4.1 hl
          have hEvalR := symScalar_toBvLin?_sound w env r er h4.2 hr
          let ⟨sv, hEq, _, hSv⟩ :=
            evalBinOpComp_wrap_arith .sub rfl (l.eval env) (r.eval env) hW hS
          change BitVec.ofNat w.bitWidth
              (match evalBinOpComp BinOp.sub (.scalar (l.eval env))
                  (.scalar (r.eval env)) with
               | .ok (.scalar sv) => sv
               | _ => ⟨l.width, l.signed, BitVec.ofNat 128 0⟩).bits.toNat = _
          rw [hEq]
          dsimp only
          rw [hSv, hWL, toNat_truncateBits_bvOfInt, Anneal.PureLift.BvLin.bvOfInt_sub]
          have hDL := bvOfInt_decodeScalar (l.eval env)
          have hDR := bvOfInt_decodeScalar (r.eval env)
          rw [hWL] at hDL
          rw [hWR] at hDR
          rw [hDL, hDR, hEvalL, hEvalR]
          dsimp only [LinExpr.evalBv]
          exact bitVec_ofNat_toNat_sub (bitWidthComp_eq_bitWidth w) _ _
  | .binOp .mul (.lit k) r, e, hWf, h => by
    have h1 := (Bool.and_eq_true _ _).mp hWf
    have h2 := (Bool.and_eq_true _ _).mp h1.1
    have h3 := (Bool.and_eq_true _ _).mp h2.1
    have h4 := (Bool.and_eq_true _ _).mp h3.1
    dsimp only [SymScalar.toBvLin?] at h
    cases hr : r.toBvLin? w with
    | none => rw [hr] at h; cases h
    | some er =>
      rw [hr] at h
      cases hcw : intWidthBeqComp k.width w && intWidthBeqComp r.width w &&
          !k.signed with
      | false => rw [hcw] at h; cases h
      | true =>
        rw [hcw] at h
        cases h
        have hC1 := (Bool.and_eq_true _ _).mp hcw
        have hC2 := (Bool.and_eq_true _ _).mp hC1.1
        have hWk : k.width = w := by
          rw [intWidthBeqComp_eq, intWidthBeqComp_eq] at hC2
          exact IntWidth.beq_iff.mp hC2.1
        have hWr : r.width = w := by
          rw [intWidthBeqComp_eq, intWidthBeqComp_eq] at hC2
          exact IntWidth.beq_iff.mp hC2.2
        have hKs : k.signed = false := by
          cases hks : k.signed with
          | false => rfl
          | true => rw [hks] at hC1; cases hC1.2
        have hL := symScalar_eval_meta env (.lit k) h4.1
        have hR := symScalar_eval_meta env r h4.2
        have hWL : ((SymScalar.lit k).eval env).width = w := hL.1.trans hWk
        have hWR : (r.eval env).width = w := hR.1.trans hWr
        have hW : ((SymScalar.lit k).eval env).width = (r.eval env).width :=
          hWL.trans hWR.symm
        have hS : ((SymScalar.lit k).eval env).signed = (r.eval env).signed := by
          rw [boolBeqComp_eq] at h2
          exact hL.2.1.trans ((beq_iff_eq.mp h2.2).trans hR.2.1.symm)
        have hEvalR := symScalar_toBvLin?_sound w env r er h4.2 hr
        let ⟨sv, hEq, _, hSv⟩ :=
          evalBinOpComp_wrap_arith .mul rfl ((SymScalar.lit k).eval env)
            (r.eval env) hW hS
        change BitVec.ofNat w.bitWidth
            (match evalBinOpComp BinOp.mul
                (.scalar ((SymScalar.lit k).eval env))
                (.scalar (r.eval env)) with
             | .ok (.scalar sv) => sv
             | _ => ⟨k.width, k.signed, BitVec.ofNat 128 0⟩).bits.toNat = _
        rw [hEq]
        dsimp only
        rw [hSv, hWL, toNat_truncateBits_bvOfInt, Anneal.PureLift.BvLin.bvOfInt_mul]
        have hDR := bvOfInt_decodeScalar (r.eval env)
        rw [hWR] at hDR
        rw [hDR, hEvalR, decodeScalar_symLit_unsigned k w hKs hWk env]
        dsimp only [LinExpr.evalBv]
        exact bitVec_ofNat_toNat_scale (bitWidthComp_eq_bitWidth w) _ _
  | .binOp .mul (.var id wl sl) (.lit k), e, hWf, h => by
    have h1 := (Bool.and_eq_true _ _).mp hWf
    have h2 := (Bool.and_eq_true _ _).mp h1.1
    have h3 := (Bool.and_eq_true _ _).mp h2.1
    have h4 := (Bool.and_eq_true _ _).mp h3.1
    change (match (SymScalar.var id wl sl).toBvLin? w with
      | some el =>
        if intWidthBeqComp wl w && intWidthBeqComp k.width w && !k.signed then
          some (.scale (Int.ofNat (truncateBitsComp w k.bits).toNat) el)
        else none
      | none => none) = some e at h
    cases hl : (SymScalar.var id wl sl).toBvLin? w with
    | none => rw [hl] at h; cases h
    | some el =>
      rw [hl] at h
      cases hcw : intWidthBeqComp wl w && intWidthBeqComp k.width w &&
          !k.signed with
      | false => rw [hcw] at h; cases h
      | true =>
        rw [hcw] at h
        cases h
        have hC1 := (Bool.and_eq_true _ _).mp hcw
        have hC2 := (Bool.and_eq_true _ _).mp hC1.1
        have hWl : wl = w := by
          rw [intWidthBeqComp_eq, intWidthBeqComp_eq] at hC2
          exact IntWidth.beq_iff.mp hC2.1
        have hWk : k.width = w := by
          rw [intWidthBeqComp_eq, intWidthBeqComp_eq] at hC2
          exact IntWidth.beq_iff.mp hC2.2
        have hKs : k.signed = false := by
          cases hks : k.signed with
          | false => rfl
          | true => rw [hks] at hC1; cases hC1.2
        have hL := symScalar_eval_meta env (.var id wl sl) h4.1
        have hR := symScalar_eval_meta env (.lit k) h4.2
        have hWL : ((SymScalar.var id wl sl).eval env).width = w := hL.1.trans hWl
        have hWR : ((SymScalar.lit k).eval env).width = w := hR.1.trans hWk
        have hW : ((SymScalar.var id wl sl).eval env).width =
            ((SymScalar.lit k).eval env).width := hWL.trans hWR.symm
        have hS : ((SymScalar.var id wl sl).eval env).signed =
            ((SymScalar.lit k).eval env).signed := by
          rw [boolBeqComp_eq] at h2
          exact hL.2.1.trans ((beq_iff_eq.mp h2.2).trans hR.2.1.symm)
        have hEvalL := symScalar_toBvLin?_sound w env (.var id wl sl) el h4.1 hl
        let ⟨sv, hEq, _, hSv⟩ :=
          evalBinOpComp_wrap_arith .mul rfl ((SymScalar.var id wl sl).eval env)
            ((SymScalar.lit k).eval env) hW hS
        change BitVec.ofNat w.bitWidth
            (match evalBinOpComp BinOp.mul
                (.scalar ((SymScalar.var id wl sl).eval env))
                (.scalar ((SymScalar.lit k).eval env)) with
             | .ok (.scalar sv) => sv
             | _ => ⟨wl, sl, BitVec.ofNat 128 0⟩).bits.toNat = _
        rw [hEq]
        dsimp only
        have hDecK := decodeScalar_symLit_unsigned k w hKs hWk env
        rw [hSv, hWL, hDecK, int_mul_ofNat_comm,
          toNat_truncateBits_bvOfInt, Anneal.PureLift.BvLin.bvOfInt_mul]
        have hDL := bvOfInt_decodeScalar ((SymScalar.var id wl sl).eval env)
        rw [hWL] at hDL
        rw [hDL, hEvalL]
        dsimp only [LinExpr.evalBv]
        exact bitVec_ofNat_toNat_scale (bitWidthComp_eq_bitWidth w) _ _
  | .binOp .mul (.unOp op a) (.lit k), e, hWf, h => by
    cases h
  | .binOp .mul (.binOp op la ra) (.lit k), e, hWf, h => by
    cases h
  | .binOp .mul (.shift op la ra) (.lit k), e, hWf, h => by
    cases h
  | .binOp .mul (.cast dw ds sa) (.lit k), e, hWf, h => by
    cases h
  | .unOp .not _, _, _, h => by cases h
  | .unOp .ptrMetadata _, _, _, h => by cases h
  | .binOp .mul (.var _ _ _) (.var _ _ _), _, _, h => by cases h
  | .binOp .mul (.var _ _ _) (.unOp _ _), _, _, h => by cases h
  | .binOp .mul (.var _ _ _) (.binOp _ _ _), _, _, h => by cases h
  | .binOp .mul (.var _ _ _) (.shift _ _ _), _, _, h => by cases h
  | .binOp .mul (.var _ _ _) (.cast _ _ _), _, _, h => by cases h
  | .binOp .mul (.unOp _ _) (.var _ _ _), _, _, h => by cases h
  | .binOp .mul (.unOp _ _) (.unOp _ _), _, _, h => by cases h
  | .binOp .mul (.unOp _ _) (.binOp _ _ _), _, _, h => by cases h
  | .binOp .mul (.unOp _ _) (.shift _ _ _), _, _, h => by cases h
  | .binOp .mul (.unOp _ _) (.cast _ _ _), _, _, h => by cases h
  | .binOp .mul (.binOp _ _ _) (.var _ _ _), _, _, h => by cases h
  | .binOp .mul (.binOp _ _ _) (.unOp _ _), _, _, h => by cases h
  | .binOp .mul (.binOp _ _ _) (.binOp _ _ _), _, _, h => by cases h
  | .binOp .mul (.binOp _ _ _) (.shift _ _ _), _, _, h => by cases h
  | .binOp .mul (.binOp _ _ _) (.cast _ _ _), _, _, h => by cases h
  | .binOp .mul (.shift _ _ _) (.var _ _ _), _, _, h => by cases h
  | .binOp .mul (.shift _ _ _) (.unOp _ _), _, _, h => by cases h
  | .binOp .mul (.shift _ _ _) (.binOp _ _ _), _, _, h => by cases h
  | .binOp .mul (.shift _ _ _) (.shift _ _ _), _, _, h => by cases h
  | .binOp .mul (.shift _ _ _) (.cast _ _ _), _, _, h => by cases h
  | .binOp .mul (.cast _ _ _) (.var _ _ _), _, _, h => by cases h
  | .binOp .mul (.cast _ _ _) (.unOp _ _), _, _, h => by cases h
  | .binOp .mul (.cast _ _ _) (.binOp _ _ _), _, _, h => by cases h
  | .binOp .mul (.cast _ _ _) (.shift _ _ _), _, _, h => by cases h
  | .binOp .mul (.cast _ _ _) (.cast _ _ _), _, _, h => by cases h
  | .binOp .bitAnd _ _, _, _, h | .binOp .bitOr _ _, _, _, h
  | .binOp .bitXor _ _, _, _, h | .binOp .div _ _, _, _, h
  | .binOp .rem _ _, _, _, h | .binOp .addUnchecked _ _, _, _, h
  | .binOp .subUnchecked _ _, _, _, h | .binOp .mulUnchecked _ _, _, _, h
  | .binOp .addWithOverflow _ _, _, _, h
  | .binOp .subWithOverflow _ _, _, _, h
  | .binOp .mulWithOverflow _ _, _, _, h
  | .binOp .shl _ _, _, _, h | .binOp .shr _ _, _, _, h
  | .binOp .shlUnchecked _ _, _, _, h | .binOp .shrUnchecked _ _, _, _, h
  | .binOp .eq _ _, _, _, h | .binOp .ne _ _, _, _, h
  | .binOp .lt _ _, _, _, h | .binOp .le _ _, _, _, h
  | .binOp .gt _ _, _, _, h | .binOp .ge _ _, _, _, h
  | .binOp .cmp _ _, _, _, h | .binOp .offset _ _, _, _, h
  | .shift _ _ _, _, _, h | .cast _ _ _, _, _, h => by cases h

/-- Reflective `BvLin` equality checker for two symbolic scalars at
width `w`. -/
@[expose] noncomputable def symBvLinEq (w : IntWidth) (a b : SymScalar) : Bool :=
  match a.toBvLin? w, b.toBvLin? w with
  | some ea, some eb => bvLinCheckEqMod (bitWidthComp w, ea, eb)
  | _, _ => false

/-- Reflective `BvLin` disequality checker for two symbolic scalars at width
`w`. -/
@[expose] noncomputable def symBvLinNe (w : IntWidth) (a b : SymScalar) : Bool :=
  match a.toBvLin? w, b.toBvLin? w with
  | some ea, some eb => bvLinCheckNeMod (bitWidthComp w, ea, eb)
  | _, _ => false

/-- Reflective `BvLin` constant-offset checker (`a - b ≡ delta (mod 2^w)`). -/
@[expose] noncomputable def symBvLinDiffConst (w : IntWidth) (a b : SymScalar)
    (delta : Nat) : Bool :=
  match a.toBvLin? w, b.toBvLin? w with
  | some ea, some eb => bvLinCheckDiffConstMod (bitWidthComp w, ea, eb, delta)
  | _, _ => false

private theorem scalarVal_bits_eq_of_bvOfNat_eq {w : IntWidth}
    {a b : ScalarVal} (hWa : a.width = w) (hWb : b.width = w)
    (hSa : a.signed = b.signed) (hWfa : ScalarVal.wf a = true)
    (hWfb : ScalarVal.wf b = true)
    (hBv : BitVec.ofNat w.bitWidth a.bits.toNat =
      BitVec.ofNat w.bitWidth b.bits.toNat) :
    a = b := by
  have hTa : a.bits.toNat < Nat.pow 2 w.bitWidth := by
    have hWf : truncateBits a.width a.bits = a.bits := by
      unfold ScalarVal.wf at hWfa
      exact beq_iff_eq.mp hWfa
    rw [← hWf, hWa, toNat_truncateBits, intWidthModulus_eq_pow]
    exact nat_mod_lt _ (nat_two_pow_pos w.bitWidth)
  have hTb : b.bits.toNat < Nat.pow 2 w.bitWidth := by
    have hWf : truncateBits b.width b.bits = b.bits := by
      unfold ScalarVal.wf at hWfb
      exact beq_iff_eq.mp hWfb
    rw [← hWf, hWb, toNat_truncateBits, intWidthModulus_eq_pow]
    exact nat_mod_lt _ (nat_two_pow_pos w.bitWidth)
  have hNat : a.bits.toNat = b.bits.toNat := by
    have h1 := congrArg BitVec.toNat hBv
    rw [bv_toNat_ofNat, bv_toNat_ofNat, nat_mod_eq_of_lt hTa,
      nat_mod_eq_of_lt hTb] at h1
    exact h1
  have hBits : a.bits = b.bits := bv_eq_of_toNat_eq hNat
  cases a with
  | mk wa sa ba =>
    cases b with
    | mk wb sb bb =>
      dsimp only at hWa hWb hSa hBits
      subst hWa; subst hWb; subst hSa; subst hBits
      rfl

/-- Soundness of `symBvLinEq`: equal modular normal forms imply identical
evaluated `ScalarVal`s across all `SymEnv`. -/
theorem symBvLinEq_sound {w : IntWidth} {a b : SymScalar}
    (ha : a.wf = true) (hb : b.wf = true)
    (hWa : a.width = w) (hWb : b.width = w) (hS : a.signed = b.signed)
    (hCheck : symBvLinEq w a b = true) (env : SymEnv) :
    a.eval env = b.eval env := by
  unfold symBvLinEq at hCheck
  cases hla : a.toBvLin? w with
  | none => rw [hla] at hCheck; cases hCheck
  | some ea =>
    cases hlb : b.toBvLin? w with
    | none => rw [hla, hlb] at hCheck; cases hCheck
    | some eb =>
      rw [hla, hlb] at hCheck
      have hBv := bvLin_eq_mod_of_boolCertCut (toBvLinEnv w env) ea eb
        (BoolCertCut.seal bvLinCheckEqMod (bitWidthComp w, ea, eb) hCheck)
      have hMa := symScalar_eval_meta env a ha
      have hMb := symScalar_eval_meta env b hb
      have hEa := symScalar_toBvLin?_sound w env a ea ha hla
      have hEb := symScalar_toBvLin?_sound w env b eb hb hlb
      have hBvW : BitVec.ofNat w.bitWidth (a.eval env).bits.toNat =
          BitVec.ofNat w.bitWidth (b.eval env).bits.toNat := by
        rw [hEa, hEb, ← bitWidthComp_eq_bitWidth w, hBv]
      exact scalarVal_bits_eq_of_bvOfNat_eq (hMa.1.trans hWa) (hMb.1.trans hWb)
        (hMa.2.1.trans (hS.trans hMb.2.1.symm)) hMa.2.2 hMb.2.2 hBvW

/-- Soundness of `symBvLinNe`: nonzero modular constant differences imply
distinct evaluated `ScalarVal`s across all `SymEnv`. -/
theorem symBvLinNe_sound {w : IntWidth} {a b : SymScalar}
    (ha : a.wf = true) (hb : b.wf = true)
    (hCheck : symBvLinNe w a b = true) (env : SymEnv) :
    a.eval env ≠ b.eval env := by
  unfold symBvLinNe at hCheck
  cases hla : a.toBvLin? w with
  | none => rw [hla] at hCheck; cases hCheck
  | some ea =>
    cases hlb : b.toBvLin? w with
    | none => rw [hla, hlb] at hCheck; cases hCheck
    | some eb =>
      rw [hla, hlb] at hCheck
      have hNe := bvLin_ne_mod_of_boolCertCut (toBvLinEnv w env) ea eb
        (BoolCertCut.seal bvLinCheckNeMod (bitWidthComp w, ea, eb) hCheck)
      have hEa := symScalar_toBvLin?_sound w env a ea ha hla
      have hEb := symScalar_toBvLin?_sound w env b eb hb hlb
      intro hEq
      rw [hEq] at hEa
      have hBvEq : BitVec.ofNat w.bitWidth (ea.evalBv (toBvLinEnv w env)).toNat =
          BitVec.ofNat w.bitWidth (eb.evalBv (toBvLinEnv w env)).toNat :=
        hEa.symm.trans hEb
      rw [← bitWidthComp_eq_bitWidth w, bv_ofNat_toNat, bv_ofNat_toNat] at hBvEq
      exact hNe hBvEq

/-- Soundness of `symBvLinDiffConst`: modular difference `a - b ≡ delta`. -/
theorem symBvLinDiffConst_sound {w : IntWidth} {a b : SymScalar}
    {delta : Nat} (ha : a.wf = true) (hb : b.wf = true)
    (hCheck : symBvLinDiffConst w a b delta = true) (env : SymEnv) :
    BitVec.ofNat w.bitWidth (a.eval env).bits.toNat =
      BitVec.ofNat w.bitWidth (b.eval env).bits.toNat +
        BitVec.ofNat w.bitWidth delta := by
  unfold symBvLinDiffConst at hCheck
  cases hla : a.toBvLin? w with
  | none => rw [hla] at hCheck; cases hCheck
  | some ea =>
    cases hlb : b.toBvLin? w with
    | none => rw [hla, hlb] at hCheck; cases hCheck
    | some eb =>
      rw [hla, hlb] at hCheck
      have hDiff := bvLin_diffConst_mod_of_boolCertCut (toBvLinEnv w env) ea eb
        delta (BoolCertCut.seal bvLinCheckDiffConstMod
          (bitWidthComp w, ea, eb, delta) hCheck)
      have hEa := symScalar_toBvLin?_sound w env a ea ha hla
      have hEb := symScalar_toBvLin?_sound w env b eb hb hlb
      rw [hEa, hEb, ← bitWidthComp_eq_bitWidth w, bv_ofNat_toNat, bv_ofNat_toNat]
      exact hDiff

/-! ### Symbolic Booleans and Values -/

/-- Symbolic boolean expression over `SymScalar` comparisons and boolean
connectives. -/
inductive SymBool where
  | lit (b : Bool)
  | var (id : Nat)
  | not (a : SymBool)
  | bin (op : BinOp) (lhs rhs : SymBool)
  | cmp (op : BinOp) (lhs rhs : SymScalar)

/-- Decidable static well-formedness of `SymBool`. -/
@[expose] noncomputable def SymBool.wf : SymBool → Bool
  | .lit _ => true
  | .var _ => true
  | .not a => a.wf
  | .bin op l r =>
    l.wf && r.wf &&
      (match op with
       | .eq | .ne | .lt | .le | .gt | .ge | .bitAnd | .bitOr | .bitXor => true
       | _ => false)
  | .cmp op l r =>
    l.wf && r.wf &&
      intWidthBeqComp l.width r.width &&
      boolBeqComp l.signed r.signed &&
      (match op with
       | .eq | .ne | .lt | .le | .gt | .ge => true
       | _ => false)

/-- Computable evaluation of `SymBool` under `env : SymEnv`. -/
@[expose] noncomputable def SymBool.eval (env : SymEnv) : SymBool → Bool
  | .lit b => b
  | .var id => match env id with | .bool b => b | _ => false
  | .not a => !(a.eval env)
  | .bin op l r =>
    match evalBinOpComp op (.bool (l.eval env)) (.bool (r.eval env)) with
    | .ok (.bool b) => b
    | _ => false
  | .cmp op l r =>
    match evalBinOpComp op (.scalar (l.eval env)) (.scalar (r.eval env)) with
    | .ok (.bool b) => b
    | _ => false

private theorem evalBinOpComp_bool_total (op : BinOp) (l r : Bool)
    (hOp : (match op with
      | .eq | .ne | .lt | .le | .gt | .ge | .bitAnd | .bitOr | .bitXor => true
      | _ => false) = true) :
    ∃ b : Bool, evalBinOpComp op (.bool l) (.bool r) = .ok (.bool b) := by
  rw [evalBinOpComp_eq]
  cases op with
  | eq => exact ⟨l == r, rfl⟩
  | ne => exact ⟨l != r, rfl⟩
  | lt => exact ⟨!l && r, rfl⟩
  | le => exact ⟨!l || r, rfl⟩
  | gt => exact ⟨l && !r, rfl⟩
  | ge => exact ⟨l || !r, rfl⟩
  | bitAnd => exact ⟨l && r, rfl⟩
  | bitOr => exact ⟨l || r, rfl⟩
  | bitXor => exact ⟨bne l r, rfl⟩
  | add | sub | mul | div | rem | addUnchecked | subUnchecked | mulUnchecked
  | addWithOverflow | subWithOverflow | mulWithOverflow
  | shl | shr | shlUnchecked | shrUnchecked | cmp | offset =>
    cases hOp

private theorem evalBinOpComp_cmp_total (op : BinOp) (l r : ScalarVal)
    (hW : l.width = r.width) (hS : l.signed = r.signed)
    (hOp : (match op with
      | .eq | .ne | .lt | .le | .gt | .ge => true
      | _ => false) = true) :
    ∃ b : Bool, evalBinOpComp op (.scalar l) (.scalar r) = .ok (.bool b) := by
  rw [evalBinOpComp_eq]
  dsimp only [evalBinOp]
  have hNotShift : op.isShift = false := by
    cases op <;> first | rfl | (cases hOp)
  have hMatch :
      (!(IntWidth.beq l.width r.width && (l.signed == r.signed))) = false := by
    rw [hW, hS]
    cases r.width <;> cases r.signed <;> rfl
  rw [hNotShift, hMatch]
  cases op with
  | eq => exact ⟨_, rfl⟩
  | ne => exact ⟨_, rfl⟩
  | lt => exact ⟨_, rfl⟩
  | le => exact ⟨_, rfl⟩
  | gt => exact ⟨_, rfl⟩
  | ge => exact ⟨_, rfl⟩
  | add | sub | mul | div | rem | addUnchecked | subUnchecked | mulUnchecked
  | addWithOverflow | subWithOverflow | mulWithOverflow
  | shl | shr | shlUnchecked | shrUnchecked
  | bitAnd | bitOr | bitXor | cmp | offset =>
    cases hOp

private theorem evalBinOp_cmp_eq_ne (op : BinOp) (hOp : op = .eq ∨ op = .ne)
    (l r : ScalarVal) (hw : l.width = r.width) (hs : l.signed = r.signed) :
    evalBinOp op (.scalar l) (.scalar r) =
      .ok (.bool (match op with
                  | .eq => decodeScalar l == decodeScalar r
                  | _ => decodeScalar l != decodeScalar r)) := by
  dsimp only [evalBinOp]
  have hNotShift : op.isShift = false := by
    cases hOp with | inl h => subst h; rfl | inr h => subst h; rfl
  have hMatch :
      (!(IntWidth.beq l.width r.width && (l.signed == r.signed))) = false := by
    rw [hw, hs]; cases r.width <;> cases r.signed <;> rfl
  rw [hNotShift, hMatch]
  cases hOp with | inl h => subst h; rfl | inr h => subst h; rfl

/-- Helper normalizing boolean `evalBinOpComp` results into `SymBool`. -/
@[expose] noncomputable def symBoolOfBinOpResult (op : BinOp) (bl br : Bool) :
    Except FaultKind Val → SymBool
  | .ok (.bool b) => .lit b
  | _ => .bin op (.lit bl) (.lit br)

/-- Binary boolean simplification step for `SymBool.simplify`. -/
@[expose] noncomputable def symBoolSimplifyBin (op : BinOp) (sl sr : SymBool) : SymBool :=
  match op, sl, sr with
  | .bitAnd, .lit false, _ | .bitAnd, _, .lit false => .lit false
  | .bitAnd, .lit true, x | .bitAnd, x, .lit true => x
  | .bitOr, .lit true, _ | .bitOr, _, .lit true => .lit true
  | .bitOr, .lit false, x | .bitOr, x, .lit false => x
  | _, .lit bl, .lit br =>
    symBoolOfBinOpResult op bl br (evalBinOpComp op (.bool bl) (.bool br))
  | _, _, _ => .bin op sl sr

private theorem symBoolOfBinOpResult_wf (op : BinOp) (bl br : Bool)
    (r : Except FaultKind Val)
    (hBase : (SymBool.bin op (.lit bl) (.lit br)).wf = true) :
    (symBoolOfBinOpResult op bl br r).wf = true := by
  cases r with
  | error _ => exact hBase
  | ok v => cases v <;> first | rfl | exact hBase

/-- Algebraic and `BvLin`-backed simplification of `SymBool`. -/
@[expose] noncomputable def SymBool.simplify : SymBool → SymBool
  | .lit b => .lit b
  | .var id => .var id
  | .not a =>
    match a.simplify with
    | .lit b => .lit (!b)
    | .not x => x
    | s => .not s
  | .bin op l r => symBoolSimplifyBin op l.simplify r.simplify
  | .cmp op l r =>
    if intWidthBeqComp l.width r.width && boolBeqComp l.signed r.signed &&
        l.wf && r.wf then
      match op with
      | .eq =>
        if symBvLinEq l.width l r then .lit true
        else if symBvLinNe l.width l r then .lit false
        else .cmp .eq l r
      | .ne =>
        if symBvLinNe l.width l r then .lit true
        else if symBvLinEq l.width l r then .lit false
        else .cmp .ne l r
      | _ => .cmp op l r
    else .cmp op l r

private theorem symBool_simplify_bin_wf (op : BinOp)
    (sl sr : SymBool) (hsl : sl.wf = true) (hsr : sr.wf = true)
    (hOp : (match op with
      | .eq | .ne | .lt | .le | .gt | .ge | .bitAnd | .bitOr | .bitXor => true
      | _ => false) = true) :
    (symBoolSimplifyBin op sl sr).wf = true := by
  have hBase : (SymBool.bin op sl sr).wf = true :=
    (Bool.and_eq_true _ _).mpr ⟨(Bool.and_eq_true _ _).mpr ⟨hsl, hsr⟩, hOp⟩
  dsimp only [symBoolSimplifyBin]
  cases op with
  | add | sub | mul | div | rem | addUnchecked | subUnchecked | mulUnchecked
  | addWithOverflow | subWithOverflow | mulWithOverflow | shl | shr
  | shlUnchecked | shrUnchecked | cmp | offset =>
    cases hOp
  | eq | ne | lt | le | gt | ge =>
    cases sl with
    | lit bl =>
      cases sr with
      | lit br =>
        dsimp only
        exact symBoolOfBinOpResult_wf _ bl br _ hBase
      | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hBase
    | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hBase
  | bitAnd =>
    cases sl with
    | lit bl =>
      cases bl with
      | false => rfl
      | true =>
        cases sr with
        | lit br => cases br <;> rfl
        | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hsr
    | var _ | not _ | bin _ _ _ | cmp _ _ _ =>
      cases sr with
      | lit br => cases br <;> first | rfl | exact hsl
      | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hBase
  | bitOr =>
    cases sl with
    | lit bl =>
      cases bl with
      | true => rfl
      | false =>
        cases sr with
        | lit br => cases br <;> rfl
        | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hsr
    | var _ | not _ | bin _ _ _ | cmp _ _ _ =>
      cases sr with
      | lit br => cases br <;> first | rfl | exact hsl
      | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hBase
  | bitXor =>
    cases sl with
    | lit bl =>
      cases sr with
      | lit br =>
        dsimp only
        exact symBoolOfBinOpResult_wf .bitXor bl br _ hBase
      | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hBase
    | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hBase

theorem symBool_simplify_wf :
    ∀ (b : SymBool), b.wf = true → b.simplify.wf = true
  | .lit _, h => h
  | .var _, h => h
  | .not a, hWf => by
    have ha := symBool_simplify_wf a hWf
    dsimp only [SymBool.simplify]
    cases hs : a.simplify with
    | lit b => rfl
    | not x => rw [hs] at ha; exact ha
    | var _ | bin _ _ _ | cmp _ _ _ => rw [hs] at ha; exact ha
  | .bin op l r, hWf => by
    have h1 := (Bool.and_eq_true _ _).mp hWf
    have h2 := (Bool.and_eq_true _ _).mp h1.1
    exact symBool_simplify_bin_wf op l.simplify r.simplify
      (symBool_simplify_wf l h2.1) (symBool_simplify_wf r h2.2) h1.2
  | .cmp op l r, hWf => by
    dsimp only [SymBool.simplify]
    cases hOk : intWidthBeqComp l.width r.width &&
        boolBeqComp l.signed r.signed && l.wf && r.wf with
    | false => exact hWf
    | true =>
      cases op with
      | eq =>
        cases symBvLinEq l.width l r with
        | true => rfl
        | false =>
          cases symBvLinNe l.width l r <;> first | rfl | exact hWf
      | ne =>
        cases symBvLinNe l.width l r with
        | true => rfl
        | false =>
          cases symBvLinEq l.width l r <;> first | rfl | exact hWf
      | lt | le | gt | ge | add | sub | mul | div | rem
      | addUnchecked | subUnchecked | mulUnchecked
      | addWithOverflow | subWithOverflow | mulWithOverflow
      | shl | shr | shlUnchecked | shrUnchecked
      | bitAnd | bitOr | bitXor | cmp | offset => exact hWf

private theorem eval_symBool_bin (env : SymEnv) (op : BinOp) (l r : SymBool) :
    (SymBool.bin op l r).eval env =
      match evalBinOpComp op (.bool (l.eval env)) (.bool (r.eval env)) with
      | .ok (.bool b) => b
      | _ => false := by
  dsimp only [SymBool.eval]
  rw [evalBinOpComp_eq]
  rfl

private theorem eval_symBool_bin_lits (env : SymEnv) (op : BinOp)
    (bl br : Bool) :
    (SymBool.bin op (.lit bl) (.lit br)).eval env =
      match evalBinOpComp op (.bool bl) (.bool br) with
      | .ok (.bool b) => b
      | _ => false :=
  eval_symBool_bin env op (.lit bl) (.lit br)

private theorem symBoolOfBinOpResult_eval (env : SymEnv) (op : BinOp)
    (bl br : Bool) (r : Except FaultKind Val)
    (hR : evalBinOpComp op (.bool bl) (.bool br) = r) :
    (symBoolOfBinOpResult op bl br r).eval env =
      (SymBool.bin op (.lit bl) (.lit br)).eval env := by
  cases r with
  | error _ => rfl
  | ok v =>
    cases v with
    | bool b =>
      dsimp only [symBoolOfBinOpResult]
      rw [eval_symBool_bin_lits, hR]
      rfl
    | ptr _ | slicePtr _ _ | scalar _ | char _ | ordering _ | unit | enumVal _ _
    | tuple _ | array _ | bytes _ | rangeTo _ | rangeFrom _ | optionVal _
    | range _ _ =>
      rfl

private theorem symBool_simplify_bin_eval (env : SymEnv) (op : BinOp)
    (l r sl sr : SymBool) (hl : sl.eval env = l.eval env)
    (hr : sr.eval env = r.eval env)
    (hOp : (match op with
      | .eq | .ne | .lt | .le | .gt | .ge | .bitAnd | .bitOr | .bitXor => true
      | _ => false) = true) :
    (symBoolSimplifyBin op sl sr).eval env = (SymBool.bin op l r).eval env := by
  have hBase : (SymBool.bin op sl sr).eval env = (SymBool.bin op l r).eval env := by
    dsimp only [SymBool.eval]
    rw [hl, hr]
  dsimp only [symBoolSimplifyBin]
  cases op with
  | add | sub | mul | div | rem | addUnchecked | subUnchecked | mulUnchecked
  | addWithOverflow | subWithOverflow | mulWithOverflow | shl | shr
  | shlUnchecked | shrUnchecked | cmp | offset =>
    cases hOp
  | bitAnd =>
    cases sl with
    | lit bl =>
      cases bl with
      | false =>
        dsimp only [SymBool.eval] at hl
        dsimp only [SymBool.eval]
        rw [← hl, evalBinOpComp_eq]
        rfl
      | true =>
        cases sr with
        | lit br =>
          cases br <;>
            (dsimp only [SymBool.eval] at hl hr; dsimp only [SymBool.eval];
             rw [← hl, ← hr, evalBinOpComp_eq]; rfl)
        | var _ | not _ | bin _ _ _ | cmp _ _ _ =>
          rw [hr, eval_symBool_bin]
          dsimp only [SymBool.eval] at hl
          rw [← hl]
          cases r.eval env <;> rfl
    | var _ | not _ | bin _ _ _ | cmp _ _ _ =>
      cases sr with
      | lit br =>
        cases br with
        | false =>
          dsimp only [SymBool.eval] at hr
          dsimp only [SymBool.eval]
          rw [← hr, evalBinOpComp_eq]
          cases l.eval env <;> rfl
        | true =>
          rw [hl, eval_symBool_bin]
          dsimp only [SymBool.eval] at hr
          rw [← hr]
          cases l.eval env <;> rfl
      | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hBase
  | bitOr =>
    cases sl with
    | lit bl =>
      cases bl with
      | true =>
        dsimp only [SymBool.eval] at hl
        dsimp only [SymBool.eval]
        rw [← hl, evalBinOpComp_eq]
        rfl
      | false =>
        cases sr with
        | lit br =>
          cases br <;>
            (dsimp only [SymBool.eval] at hl hr; dsimp only [SymBool.eval];
             rw [← hl, ← hr, evalBinOpComp_eq]; rfl)
        | var _ | not _ | bin _ _ _ | cmp _ _ _ =>
          rw [hr, eval_symBool_bin]
          dsimp only [SymBool.eval] at hl
          rw [← hl]
          cases r.eval env <;> rfl
    | var _ | not _ | bin _ _ _ | cmp _ _ _ =>
      cases sr with
      | lit br =>
        cases br with
        | true =>
          dsimp only [SymBool.eval] at hr
          dsimp only [SymBool.eval]
          rw [← hr, evalBinOpComp_eq]
          cases l.eval env <;> rfl
        | false =>
          rw [hl, eval_symBool_bin]
          dsimp only [SymBool.eval] at hr
          rw [← hr]
          cases l.eval env <;> rfl
      | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hBase
  | eq | ne | lt | le | gt | ge | bitXor =>
    cases sl with
    | lit bl =>
      cases sr with
      | lit br =>
        dsimp only
        rw [← hBase]
        exact symBoolOfBinOpResult_eval env _ bl br _ rfl
      | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hBase
    | var _ | not _ | bin _ _ _ | cmp _ _ _ => exact hBase

theorem symBool_simplify_eval (env : SymEnv) :
    ∀ (b : SymBool), b.wf = true → b.simplify.eval env = b.eval env
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .not a, hWf => by
    have ih := symBool_simplify_eval env a hWf
    dsimp only [SymBool.simplify]
    cases hs : a.simplify with
    | lit b =>
      dsimp only [SymBool.eval]
      rw [← ih, hs]
      rfl
    | not x =>
      dsimp only [SymBool.eval]
      rw [← ih, hs]
      dsimp only [SymBool.eval]
      cases x.eval env <;> rfl
    | var _ | bin _ _ _ | cmp _ _ _ =>
      dsimp only [SymBool.eval]
      rw [← ih, hs]
      rfl
  | .bin op l r, hWf => by
    have h1 := (Bool.and_eq_true _ _).mp hWf
    have h2 := (Bool.and_eq_true _ _).mp h1.1
    exact symBool_simplify_bin_eval env op l r l.simplify r.simplify
      (symBool_simplify_eval env l h2.1) (symBool_simplify_eval env r h2.2) h1.2
  | .cmp op l r, _ => by
    dsimp only [SymBool.simplify]
    cases hOk : intWidthBeqComp l.width r.width &&
        boolBeqComp l.signed r.signed && l.wf && r.wf with
    | false => rfl
    | true =>
      have ha1 := (Bool.and_eq_true _ _).mp hOk
      have ha2 := (Bool.and_eq_true _ _).mp ha1.1
      have ha3 := (Bool.and_eq_true _ _).mp ha2.1
      have hW : l.width = r.width := by
        rw [intWidthBeqComp_eq] at ha3
        exact IntWidth.beq_iff.mp ha3.1
      have hS : l.signed = r.signed := by
        rw [boolBeqComp_eq] at ha3
        exact beq_iff_eq.mp ha3.2
      have hMl := symScalar_eval_meta env l ha2.2
      have hMr := symScalar_eval_meta env r ha1.2
      have hWlr : (l.eval env).width = (r.eval env).width :=
        hMl.1.trans (hW.trans hMr.1.symm)
      have hSlr : (l.eval env).signed = (r.eval env).signed :=
        hMl.2.1.trans (hS.trans hMr.2.1.symm)
      have hMatch :
          (!(IntWidth.beq (l.eval env).width (r.eval env).width &&
            ((l.eval env).signed == (r.eval env).signed))) = false := by
        rw [hWlr, hSlr]
        cases (r.eval env).width <;> cases (r.eval env).signed <;> rfl
      cases op with
      | eq =>
        dsimp only
        cases hEqB : symBvLinEq l.width l r with
        | true =>
          have hEq := symBvLinEq_sound ha2.2 ha1.2 rfl hW.symm hS hEqB env
          dsimp only [SymBool.eval]
          rw [evalBinOpComp_eq,
            evalBinOp_cmp_eq_ne .eq (Or.inl rfl) (l.eval env) (r.eval env) hWlr hSlr]
          dsimp only
          rw [hEq]
          exact (int_beq_self_eq_true (decodeScalar (r.eval env))).symm
        | false =>
          cases hNeB : symBvLinNe l.width l r with
          | false => rfl
          | true =>
            have hNe := symBvLinNe_sound ha2.2 ha1.2 hNeB env
            dsimp only [SymBool.eval]
            rw [evalBinOpComp_eq,
              evalBinOp_cmp_eq_ne .eq (Or.inl rfl) (l.eval env) (r.eval env) hWlr hSlr]
            dsimp only
            cases hDec : decodeScalar (l.eval env) == decodeScalar (r.eval env) with
            | false => rfl
            | true =>
              have hDecEq : decodeScalar (l.eval env) = decodeScalar (r.eval env) :=
                int_beq_iff_eq.mp hDec
              have hBvDec : BitVec.ofNat l.width.bitWidth (l.eval env).bits.toNat =
                  BitVec.ofNat l.width.bitWidth (r.eval env).bits.toNat := by
                have hDl := bvOfInt_decodeScalar (l.eval env)
                have hDr := bvOfInt_decodeScalar (r.eval env)
                rw [hMl.1] at hDl
                rw [hMr.1, ← hW] at hDr
                rw [← hDl, ← hDr, hDecEq]
              exact False.elim (hNe (scalarVal_bits_eq_of_bvOfNat_eq hMl.1
                (hMr.1.trans hW.symm) hSlr hMl.2.2 hMr.2.2 hBvDec))
      | ne =>
        dsimp only
        cases hNeB : symBvLinNe l.width l r with
        | true =>
          have hNe := symBvLinNe_sound ha2.2 ha1.2 hNeB env
          dsimp only [SymBool.eval]
          rw [evalBinOpComp_eq,
            evalBinOp_cmp_eq_ne .ne (Or.inr rfl) (l.eval env) (r.eval env) hWlr hSlr]
          dsimp only
          cases hDec : decodeScalar (l.eval env) != decodeScalar (r.eval env) with
          | true => rfl
          | false =>
            have hDecEq : decodeScalar (l.eval env) = decodeScalar (r.eval env) := by
              cases hb : decodeScalar (l.eval env) == decodeScalar (r.eval env) with
              | true => exact int_beq_iff_eq.mp hb
              | false =>
                have hN : (decodeScalar (l.eval env) !=
                    decodeScalar (r.eval env)) = true := by
                  change (!(decodeScalar (l.eval env) ==
                    decodeScalar (r.eval env))) = true
                  rw [hb]
                  rfl
                rw [hN] at hDec
                cases hDec
            have hBvDec : BitVec.ofNat l.width.bitWidth (l.eval env).bits.toNat =
                BitVec.ofNat l.width.bitWidth (r.eval env).bits.toNat := by
              have hDl := bvOfInt_decodeScalar (l.eval env)
              have hDr := bvOfInt_decodeScalar (r.eval env)
              rw [hMl.1] at hDl
              rw [hMr.1, ← hW] at hDr
              rw [← hDl, ← hDr, hDecEq]
            exact False.elim (hNe (scalarVal_bits_eq_of_bvOfNat_eq hMl.1
              (hMr.1.trans hW.symm) hSlr hMl.2.2 hMr.2.2 hBvDec))
        | false =>
          cases hEqB : symBvLinEq l.width l r with
          | false => rfl
          | true =>
            have hEq := symBvLinEq_sound ha2.2 ha1.2 rfl hW.symm hS hEqB env
            dsimp only [SymBool.eval]
            rw [evalBinOpComp_eq,
              evalBinOp_cmp_eq_ne .ne (Or.inr rfl) (l.eval env) (r.eval env) hWlr hSlr]
            dsimp only
            rw [hEq]
            exact (int_bne_self_eq_false (decodeScalar (r.eval env))).symm
      | lt | le | gt | ge | add | sub | mul | div | rem
      | addUnchecked | subUnchecked | mulUnchecked
      | addWithOverflow | subWithOverflow | mulWithOverflow
      | shl | shr | shlUnchecked | shrUnchecked
      | bitAnd | bitOr | bitXor | cmp | offset => rfl

/-- Symbolic MIR value: concrete `Val`, symbolic `SymScalar`, symbolic
`SymBool`, or symbolic pair (such as overflow-checked arithmetic pairs). -/
inductive SymVal where
  | conc (v : Val)
  | scalar (s : SymScalar)
  | bool (b : SymBool)
  | pair (fst snd : SymVal)

/-- Computes the MIR type of a well-formed `SymVal`, or `none` if ill-formed. -/
@[expose] noncomputable def SymVal.ty? : SymVal → Option MirTy
  | .conc v => valTy?Comp v
  | .scalar s => if s.wf then some (.int s.width s.signed) else none
  | .bool b => if b.wf then some .bool else none
  | .pair (.scalar s) (.bool b) =>
    if s.wf && b.wf then some (.tuple [.int s.width s.signed, .bool]) else none
  | .pair _ _ => none

/-- Decidable well-formedness of `SymVal` (equivalent to `ty?.isSome`). -/
@[expose] noncomputable def SymVal.wf (v : SymVal) : Bool := v.ty?.isSome

/-- Computable evaluation of `SymVal` under `env : SymEnv`. -/
@[expose] noncomputable def SymVal.eval (env : SymEnv) : SymVal → Val
  | .conc v => v
  | .scalar s => .scalar (s.eval env)
  | .bool b => .bool (b.eval env)
  | .pair a b => .tuple [a.eval env, b.eval env]

/-- Soundness of `SymVal.ty?`: well-typed symbolic values evaluate to values
with the exact same `Val.ty?`. -/
theorem symVal_eval_ty? (env : SymEnv) :
    ∀ (v : SymVal) (ty : MirTy), v.ty? = some ty → (v.eval env).ty? = some ty
  | .conc x, ty, h => by
    dsimp only [SymVal.ty?] at h
    rw [valTy?Comp_eq] at h
    exact h
  | .scalar s, ty, h => by
    dsimp only [SymVal.ty?] at h
    cases hWf : s.wf with
    | false => rw [hWf] at h; cases h
    | true =>
      rw [bool_ite_true hWf] at h
      cases h
      have hM := symScalar_eval_meta env s hWf
      dsimp only [SymVal.eval, Val.ty?]
      rw [hM.2.2, hM.1, hM.2.1, ite_prop_true (rfl : true = true)]
  | .bool b, ty, h => by
    dsimp only [SymVal.ty?] at h
    cases hWf : b.wf with
    | false => rw [hWf] at h; cases h
    | true => rw [bool_ite_true hWf] at h; cases h; rfl
  | .pair a b, ty, h => by
    cases a with
    | conc _ | bool _ | pair _ _ => cases h
    | scalar s =>
      cases b with
      | conc _ | scalar _ | pair _ _ => cases h
      | bool bb =>
        dsimp only [SymVal.ty?] at h
        cases hWf : s.wf && bb.wf with
        | false => rw [hWf] at h; cases h
        | true =>
          rw [bool_ite_true hWf] at h
          cases h
          have hAnd := (Bool.and_eq_true _ _).mp hWf
          have hM := symScalar_eval_meta env s hAnd.1
          dsimp only [SymVal.eval, Val.ty?]
          rw [hM.2.2, hM.1, hM.2.1, ite_prop_true (rfl : true = true)]

/-- Static symbolic type check against `dstTy` (`none` if type depth exceeds
`16`). -/
@[expose] noncomputable def symValCheckTy (v : SymVal) (dstTy : MirTy) : Bool :=
  match v.ty? with
  | some vTy =>
    match mirTyEqExact 16 vTy dstTy with
    | some b => b
    | none => false
  | none => false

/-- Any `SymVal` passing `symValCheckTy` evaluates to a `Val` passing
`checkVal _ dstTy = true` for every `env`. -/
theorem checkVal_of_symValCheckTy {v : SymVal} {dstTy : MirTy}
    (h : symValCheckTy v dstTy = true) (env : SymEnv) :
    checkVal (v.eval env) dstTy = true := by
  unfold symValCheckTy at h
  cases hTy : v.ty? with
  | none => rw [hTy] at h; cases h
  | some vTy =>
    rw [hTy] at h
    dsimp only at h
    cases hEq : mirTyEqExact 16 vTy dstTy with
    | none => rw [hEq] at h; cases h
    | some b =>
      rw [hEq] at h
      dsimp only at h
      cases b with
      | false => cases h
      | true =>
        unfold checkVal
        rw [symVal_eval_ty? env v vTy hTy]
        exact (mirTyEqExact_eq 16 vTy dstTy true hEq).symm

/-- Extract a well-formed `SymScalar` when `v` represents a scalar. -/
@[expose] noncomputable def SymVal.asScalar? : SymVal → Option SymScalar
  | .scalar s => if s.wf then some s else none
  | .conc (.scalar sv) =>
    if bv128BeqComp (truncateBitsComp sv.width sv.bits) sv.bits then
      some (.lit sv)
    else none
  | _ => none

/-- Soundness of `SymVal.asScalar?`. -/
theorem symVal_asScalar?_sound {v : SymVal} {s : SymScalar}
    (h : v.asScalar? = some s) (env : SymEnv) :
    s.wf = true ∧ v.eval env = .scalar (s.eval env) := by
  cases v with
  | bool _ | pair _ _ => cases h
  | scalar s0 =>
    dsimp only [SymVal.asScalar?] at h
    cases hWf : s0.wf with
    | false => rw [hWf] at h; cases h
    | true => rw [hWf] at h; cases h; exact ⟨hWf, rfl⟩
  | conc c =>
    cases c with
    | ptr _ | slicePtr _ _ | bool _ | char _ | ordering _ | unit | enumVal _ _
    | tuple _ | array _ | bytes _ | rangeTo _ | rangeFrom _ | optionVal _
    | range _ _ =>
      cases h
    | scalar sv =>
      dsimp only [SymVal.asScalar?] at h
      cases hWf : bv128BeqComp (truncateBitsComp sv.width sv.bits) sv.bits with
      | false => rw [hWf] at h; cases h
      | true =>
        rw [hWf] at h
        cases h
        have hLitWf : (SymScalar.lit sv).wf = true := hWf
        exact ⟨hLitWf, (congrArg Val.scalar (symScalar_lit_eval hLitWf)).symm⟩

/-- Extract a well-formed `SymBool` when `v` represents a boolean. -/
@[expose] noncomputable def SymVal.asBool? : SymVal → Option SymBool
  | .bool b => if b.wf then some b else none
  | .conc (.bool b) => some (.lit b)
  | _ => none

/-- Soundness of `SymVal.asBool?`. -/
theorem symVal_asBool?_sound {v : SymVal} {b : SymBool}
    (h : v.asBool? = some b) (env : SymEnv) :
    b.wf = true ∧ v.eval env = .bool (b.eval env) := by
  cases v with
  | scalar _ | pair _ _ => cases h
  | bool b0 =>
    dsimp only [SymVal.asBool?] at h
    cases hWf : b0.wf with
    | false => rw [hWf] at h; cases h
    | true => rw [hWf] at h; cases h; exact ⟨hWf, rfl⟩
  | conc c =>
    cases c with
    | ptr _ | slicePtr _ _ | scalar _ | char _ | ordering _ | unit | enumVal _ _
    | tuple _ | array _ | bytes _ | rangeTo _ | rangeFrom _ | optionVal _
    | range _ _ =>
      cases h
    | bool b0 =>
      dsimp only [SymVal.asBool?] at h
      cases h
      exact ⟨rfl, rfl⟩

/-! ## Part III: Symbolic Operations, Step Engine, and `MirWp` Adequacy -/

/-- Whether `op` is a shift binary operator handled symbolically. -/
@[expose] noncomputable def symIsShiftOp : BinOp → Bool
  | .shl | .shr => true
  | _ => false

/-- Whether `op` is a boolean-producing binary operator handled symbolically. -/
@[expose] noncomputable def symIsBoolBinOp : BinOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge | .bitAnd | .bitOr | .bitXor => true
  | _ => false

/-- Symbolic binary operator dispatch when at least one operand is symbolic. -/
@[expose] noncomputable def symBinOpSym (op : BinOp) (l r : SymVal) : Option SymVal :=
  match l.asScalar?, r.asScalar? with
  | some sa, some sb =>
    if symIsShiftOp op then
      some (.scalar (.shift op sa sb))
    else if intWidthBeqComp sa.width sb.width &&
        boolBeqComp sa.signed sb.signed then
      match op with
      | .add | .sub | .mul | .bitAnd | .bitOr | .bitXor =>
        some (.scalar (.binOp op sa sb))
      | .eq =>
        if symBvLinEq sa.width sa sb then some (.conc (.bool true))
        else if symBvLinNe sa.width sa sb then some (.conc (.bool false))
        else some (.bool (.cmp .eq sa sb))
      | .ne =>
        if symBvLinNe sa.width sa sb then some (.conc (.bool true))
        else if symBvLinEq sa.width sa sb then some (.conc (.bool false))
        else some (.bool (.cmp .ne sa sb))
      | .lt | .le | .gt | .ge =>
        some (.bool (.cmp op sa sb))
      | _ => none
    else none
  | _, _ =>
    match l.asBool?, r.asBool? with
    | some ba, some bb =>
      if symIsBoolBinOp op then
        some (.bool (.bin op ba bb))
      else none
    | _, _ => none

/-- Symbolic `evalBinOp` with concrete fast-path, `BvLin` equality/disequality
collapse, and symbolic scalar/boolean/shift constructors. -/
@[expose] noncomputable def symBinOp (op : BinOp) (l r : SymVal) : Option SymVal :=
  match l, r with
  | .conc a, .conc b =>
    match evalBinOpComp op a b with
    | .ok v => some (.conc v)
    | .error _ => none
  | _, _ => symBinOpSym op l r

private theorem symBinOpSym_arith (env : SymEnv) (op : BinOp)
    (sa sb : SymScalar)
    (hWfa : sa.wf = true) (hWfb : sb.wf = true)
    (hWab : (sa.eval env).width = (sb.eval env).width)
    (hSab : (sa.eval env).signed = (sb.eval env).signed)
    (hAnd : intWidthBeqComp sa.width sb.width = true ∧
      boolBeqComp sa.signed sb.signed = true)
    (hOp : (match op with
      | .add | .sub | .mul | .bitAnd | .bitOr | .bitXor => true
      | _ => false) = true) :
    evalBinOp op (.scalar (sa.eval env)) (.scalar (sb.eval env)) =
        .ok ((SymVal.scalar (.binOp op sa sb)).eval env) ∧
      (SymVal.scalar (.binOp op sa sb)).wf = true := by
  let ⟨sv, hEq, _⟩ :=
    evalBinOpComp_scalar_total op (sa.eval env) (sb.eval env) hWab hSab hOp
  have hWf : (SymScalar.binOp op sa sb).wf = true := by
    dsimp only [SymScalar.wf]
    rw [hWfa, hWfb, hAnd.1, hAnd.2]
    exact hOp
  refine ⟨?_, ?_⟩
  · rw [← evalBinOpComp_eq]
    dsimp only [SymVal.eval, SymScalar.eval]
    rw [hEq]
  · dsimp only [SymVal.wf, SymVal.ty?]
    rw [hWf]
    rfl

private theorem symBinOpSym_cmp (env : SymEnv) (op : BinOp)
    (sa sb : SymScalar)
    (hWfa : sa.wf = true) (hWfb : sb.wf = true)
    (hWab : (sa.eval env).width = (sb.eval env).width)
    (hSab : (sa.eval env).signed = (sb.eval env).signed)
    (hAnd : intWidthBeqComp sa.width sb.width = true ∧
      boolBeqComp sa.signed sb.signed = true)
    (hOp : (match op with
      | .eq | .ne | .lt | .le | .gt | .ge => true
      | _ => false) = true) :
    evalBinOp op (.scalar (sa.eval env)) (.scalar (sb.eval env)) =
        .ok ((SymVal.bool (.cmp op sa sb)).eval env) ∧
      (SymVal.bool (.cmp op sa sb)).wf = true := by
  let ⟨b, hEq⟩ := evalBinOpComp_cmp_total op (sa.eval env) (sb.eval env) hWab hSab hOp
  have hWf : (SymBool.cmp op sa sb).wf = true := by
    dsimp only [SymBool.wf]
    rw [hWfa, hWfb, hAnd.1, hAnd.2]
    cases op <;> first | rfl | cases hOp
  refine ⟨?_, ?_⟩
  · rw [← evalBinOpComp_eq]
    dsimp only [SymVal.eval, SymBool.eval]
    rw [hEq]
  · dsimp only [SymVal.wf, SymVal.ty?]
    rw [hWf]
    rfl

private theorem symBinOp_sym_sound {op : BinOp} {l r res : SymVal}
    (h : symBinOpSym op l r = some res) (env : SymEnv) :
    evalBinOp op (l.eval env) (r.eval env) = .ok (res.eval env) ∧
      res.wf = true := by
  dsimp only [symBinOpSym] at h
  cases hl : l.asScalar? with
  | some sa =>
    cases hr : r.asScalar? with
    | some sb =>
      rw [hl, hr] at h
      dsimp only at h
      have ⟨hWfa, hEva⟩ := symVal_asScalar?_sound hl env
      have ⟨hWfb, hEvb⟩ := symVal_asScalar?_sound hr env
      rw [hEva, hEvb]
      cases hSh : symIsShiftOp op with
      | true =>
        rw [hSh] at h
        cases h
        let ⟨sv, hEq, _⟩ :=
          evalShiftComp_scalar_total op (sa.eval env) (sb.eval env)
            (by cases op <;> first | rfl | cases hSh)
        rw [← evalBinOpComp_eq]
        have hWf : (SymScalar.shift op sa sb).wf = true := by
          dsimp only [SymScalar.wf]
          rw [hWfa, hWfb]
          cases op <;> first | rfl | cases hSh
        refine ⟨?_, ?_⟩
        · dsimp only [SymVal.eval, SymScalar.eval]
          rw [hEq]
        · dsimp only [SymVal.wf, SymVal.ty?]
          rw [hWf]
          rfl
      | false =>
        rw [hSh] at h
        cases hWS : intWidthBeqComp sa.width sb.width &&
            boolBeqComp sa.signed sb.signed with
        | false => rw [hWS] at h; cases h
        | true =>
          rw [hWS] at h
          have hAnd := (Bool.and_eq_true _ _).mp hWS
          have hW : sa.width = sb.width := by
            rw [intWidthBeqComp_eq] at hAnd
            exact IntWidth.beq_iff.mp hAnd.1
          have hS : sa.signed = sb.signed := by
            rw [boolBeqComp_eq] at hAnd
            exact beq_iff_eq.mp hAnd.2
          have hMa := symScalar_eval_meta env sa hWfa
          have hMb := symScalar_eval_meta env sb hWfb
          have hWab : (sa.eval env).width = (sb.eval env).width :=
            hMa.1.trans (hW.trans hMb.1.symm)
          have hSab : (sa.eval env).signed = (sb.eval env).signed :=
            hMa.2.1.trans (hS.trans hMb.2.1.symm)
          cases op with
          | add | sub | mul | bitAnd | bitOr | bitXor =>
            cases h
            exact symBinOpSym_arith env _ sa sb hWfa hWfb hWab hSab hAnd rfl
          | eq =>
            dsimp only at h
            cases hEqB : symBvLinEq sa.width sa sb with
            | true =>
              rw [hEqB] at h; cases h
              have hEq := symBvLinEq_sound hWfa hWfb rfl hW.symm hS hEqB env
              rw [evalBinOp_cmp_eq_ne .eq (Or.inl rfl) (sa.eval env) (sb.eval env)
                hWab hSab, hEq]
              dsimp only [SymVal.eval]
              rw [int_beq_self_eq_true (decodeScalar (sb.eval env))]
              exact ⟨rfl, rfl⟩
            | false =>
              rw [hEqB] at h
              cases hNeB : symBvLinNe sa.width sa sb with
              | true =>
                rw [hNeB] at h; cases h
                have hNe := symBvLinNe_sound hWfa hWfb hNeB env
                rw [evalBinOp_cmp_eq_ne .eq (Or.inl rfl) (sa.eval env) (sb.eval env)
                  hWab hSab]
                dsimp only
                cases hDec : decodeScalar (sa.eval env) ==
                    decodeScalar (sb.eval env) with
                | false => exact ⟨rfl, rfl⟩
                | true =>
                  have hDecEq := int_beq_iff_eq.mp hDec
                  have hBvDec :
                      BitVec.ofNat sa.width.bitWidth (sa.eval env).bits.toNat =
                        BitVec.ofNat sa.width.bitWidth (sb.eval env).bits.toNat := by
                    have hDa := bvOfInt_decodeScalar (sa.eval env)
                    have hDb := bvOfInt_decodeScalar (sb.eval env)
                    rw [hMa.1] at hDa
                    rw [hMb.1, ← hW] at hDb
                    rw [← hDa, ← hDb, hDecEq]
                  exact False.elim (hNe (scalarVal_bits_eq_of_bvOfNat_eq hMa.1
                    (hMb.1.trans hW.symm) hSab hMa.2.2 hMb.2.2 hBvDec))
              | false =>
                rw [hNeB] at h; cases h
                let ⟨b, hEq⟩ := evalBinOpComp_cmp_total .eq
                  (sa.eval env) (sb.eval env) hWab hSab rfl
                have hWf : (SymBool.cmp .eq sa sb).wf = true := by
                  dsimp only [SymBool.wf]
                  rw [hWfa, hWfb, hAnd.1, hAnd.2]
                  rfl
                refine ⟨?_, ?_⟩
                · rw [← evalBinOpComp_eq]
                  dsimp only [SymVal.eval, SymBool.eval]
                  rw [hEq]
                · dsimp only [SymVal.wf, SymVal.ty?]
                  rw [hWf]
                  rfl
          | ne =>
            dsimp only at h
            cases hNeB : symBvLinNe sa.width sa sb with
            | true =>
              rw [hNeB] at h; cases h
              have hNe := symBvLinNe_sound hWfa hWfb hNeB env
              rw [evalBinOp_cmp_eq_ne .ne (Or.inr rfl) (sa.eval env) (sb.eval env)
                hWab hSab]
              dsimp only
              cases hDec : decodeScalar (sa.eval env) !=
                  decodeScalar (sb.eval env) with
              | true => exact ⟨rfl, rfl⟩
              | false =>
                have hDecEq : decodeScalar (sa.eval env) = decodeScalar (sb.eval env) := by
                  cases hb : decodeScalar (sa.eval env) == decodeScalar (sb.eval env) with
                  | true => exact int_beq_iff_eq.mp hb
                  | false =>
                    have hN : (decodeScalar (sa.eval env) !=
                        decodeScalar (sb.eval env)) = true := by
                      change (!(decodeScalar (sa.eval env) ==
                        decodeScalar (sb.eval env))) = true
                      rw [hb]
                      rfl
                    rw [hN] at hDec
                    cases hDec
                have hBvDec :
                    BitVec.ofNat sa.width.bitWidth (sa.eval env).bits.toNat =
                      BitVec.ofNat sa.width.bitWidth (sb.eval env).bits.toNat := by
                  have hDa := bvOfInt_decodeScalar (sa.eval env)
                  have hDb := bvOfInt_decodeScalar (sb.eval env)
                  rw [hMa.1] at hDa
                  rw [hMb.1, ← hW] at hDb
                  rw [← hDa, ← hDb, hDecEq]
                exact False.elim (hNe (scalarVal_bits_eq_of_bvOfNat_eq hMa.1
                  (hMb.1.trans hW.symm) hSab hMa.2.2 hMb.2.2 hBvDec))
            | false =>
              rw [hNeB] at h
              cases hEqB : symBvLinEq sa.width sa sb with
              | true =>
                rw [hEqB] at h; cases h
                have hEq := symBvLinEq_sound hWfa hWfb rfl hW.symm hS hEqB env
                rw [evalBinOp_cmp_eq_ne .ne (Or.inr rfl) (sa.eval env) (sb.eval env)
                  hWab hSab, hEq]
                dsimp only [SymVal.eval]
                rw [int_bne_self_eq_false (decodeScalar (sb.eval env))]
                exact ⟨rfl, rfl⟩
              | false =>
                rw [hEqB] at h; cases h
                let ⟨b, hEq⟩ := evalBinOpComp_cmp_total .ne
                  (sa.eval env) (sb.eval env) hWab hSab rfl
                have hWf : (SymBool.cmp .ne sa sb).wf = true := by
                  dsimp only [SymBool.wf]
                  rw [hWfa, hWfb, hAnd.1, hAnd.2]
                  rfl
                refine ⟨?_, ?_⟩
                · rw [← evalBinOpComp_eq]
                  dsimp only [SymVal.eval, SymBool.eval]
                  rw [hEq]
                · dsimp only [SymVal.wf, SymVal.ty?]
                  rw [hWf]
                  rfl
          | lt | le | gt | ge =>
            cases h
            exact symBinOpSym_cmp env _ sa sb hWfa hWfb hWab hSab hAnd rfl
          | div | rem | addUnchecked | subUnchecked | mulUnchecked
          | addWithOverflow | subWithOverflow | mulWithOverflow
          | shl | shr | shlUnchecked | shrUnchecked | cmp | offset =>
            cases h
    | none =>
      rw [hl, hr] at h
      dsimp only at h
      cases hBl : l.asBool? with
      | none => rw [hBl] at h; cases h
      | some ba =>
        cases hBr : r.asBool? with
        | none => rw [hBl, hBr] at h; cases h
        | some bb =>
          rw [hBl, hBr] at h
          cases hOp : symIsBoolBinOp op with
          | false => rw [hOp] at h; cases h
          | true =>
            rw [hOp] at h; cases h
            have ⟨hWfa, hEva⟩ := symVal_asBool?_sound hBl env
            have ⟨hWfb, hEvb⟩ := symVal_asBool?_sound hBr env
            rw [hEva, hEvb]
            let ⟨b, hEq⟩ := evalBinOpComp_bool_total op (ba.eval env) (bb.eval env)
              (by cases op <;> first | rfl | cases hOp)
            have hWf : (SymBool.bin op ba bb).wf = true := by
              dsimp only [SymBool.wf]
              rw [hWfa, hWfb]
              cases op <;> first | rfl | cases hOp
            refine ⟨?_, ?_⟩
            · rw [← evalBinOpComp_eq]
              dsimp only [SymVal.eval, SymBool.eval]
              rw [hEq]
            · dsimp only [SymVal.wf, SymVal.ty?]
              rw [hWf]
              rfl
  | none =>
    rw [hl] at h
    dsimp only at h
    cases hBl : l.asBool? with
    | none => rw [hBl] at h; cases h
    | some ba =>
      cases hBr : r.asBool? with
      | none => rw [hBl, hBr] at h; cases h
      | some bb =>
        rw [hBl, hBr] at h
        cases hOp : symIsBoolBinOp op with
        | false => rw [hOp] at h; cases h
        | true =>
          rw [hOp] at h; cases h
          have ⟨hWfa, hEva⟩ := symVal_asBool?_sound hBl env
          have ⟨hWfb, hEvb⟩ := symVal_asBool?_sound hBr env
          rw [hEva, hEvb]
          let ⟨b, hEq⟩ := evalBinOpComp_bool_total op (ba.eval env) (bb.eval env)
            (by cases op <;> first | rfl | cases hOp)
          have hWf : (SymBool.bin op ba bb).wf = true := by
            dsimp only [SymBool.wf]
            rw [hWfa, hWfb]
            cases op <;> first | rfl | cases hOp
          refine ⟨?_, ?_⟩
          · rw [← evalBinOpComp_eq]
            dsimp only [SymVal.eval, SymBool.eval]
            rw [hEq]
          · dsimp only [SymVal.wf, SymVal.ty?]
            rw [hWf]
            rfl

theorem symBinOp_sound {op : BinOp} {l r res : SymVal}
    (h : symBinOp op l r = some res) (env : SymEnv) :
    evalBinOp op (l.eval env) (r.eval env) = .ok (res.eval env) := by
  cases l with
  | conc a =>
    cases r with
    | conc b =>
      dsimp only [symBinOp] at h
      cases hEv : evalBinOpComp op a b with
      | error _ => rw [hEv] at h; cases h
      | ok v =>
        rw [hEv] at h; cases h
        rw [← evalBinOpComp_eq]
        exact hEv
    | scalar _ | bool _ | pair _ _ =>
      dsimp only [symBinOp] at h
      exact (symBinOp_sym_sound h env).1
  | scalar _ | bool _ | pair _ _ =>
    dsimp only [symBinOp] at h
    exact (symBinOp_sym_sound h env).1

/-- Symbolic `evalUnOp`. -/
@[expose] noncomputable def symUnOp (op : UnOp) (v : SymVal) : Option SymVal :=
  match v with
  | .conc a =>
    match evalUnOpComp op a with
    | .ok res => some (.conc res)
    | .error _ => none
  | .scalar s =>
    if !s.wf then none
    else
      match op with
      | .not => some (.scalar (.unOp .not s))
      | .neg => if s.signed then some (.scalar (.unOp .neg s)) else none
      | .ptrMetadata => none
  | .bool b =>
    if !b.wf then none
    else
      match op with
      | .not => some (.bool (.not b))
      | .neg | .ptrMetadata => none
  | .pair _ _ => none

theorem symUnOp_sound {op : UnOp} {v res : SymVal}
    (h : symUnOp op v = some res) (env : SymEnv) :
    evalUnOp op (v.eval env) = .ok (res.eval env) := by
  cases v with
  | pair _ _ => cases h
  | conc a =>
    dsimp only [symUnOp] at h
    cases hEv : evalUnOpComp op a with
    | error _ => rw [hEv] at h; cases h
    | ok r =>
      rw [hEv] at h; cases h
      rw [← evalUnOpComp_eq]
      exact hEv
  | scalar s =>
    dsimp only [symUnOp] at h
    cases hWf : s.wf with
    | false => rw [hWf] at h; cases h
    | true =>
      rw [hWf] at h
      have hM := symScalar_eval_meta env s hWf
      cases op with
      | not =>
        cases h
        let ⟨sv', hEq, _⟩ := evalUnOpComp_scalar_total .not (s.eval env) (Or.inl rfl)
        rw [← evalUnOpComp_eq]
        dsimp only [SymVal.eval, SymScalar.eval]
        rw [hEq]
      | neg =>
        cases hS : s.signed with
        | false => rw [hS] at h; cases h
        | true =>
          rw [hS] at h; cases h
          have hSig : (s.eval env).signed = true := hM.2.1.trans hS
          let ⟨sv', hEq, _⟩ :=
            evalUnOpComp_scalar_total .neg (s.eval env) (Or.inr ⟨rfl, hSig⟩)
          rw [← evalUnOpComp_eq]
          dsimp only [SymVal.eval, SymScalar.eval]
          rw [hEq]
      | ptrMetadata => cases h
  | bool b =>
    dsimp only [symUnOp] at h
    cases hWf : b.wf with
    | false => rw [hWf] at h; cases h
    | true =>
      rw [hWf] at h
      cases op with
      | not => cases h; rfl
      | neg | ptrMetadata => cases h

/-- Symbolic `evalIntToIntCast` supporting concrete values and symbolic scalar
widening/narrowing/sign casts. -/
@[expose] noncomputable def symCastIntToInt (v : SymVal) (castTy : MirTy) : Option SymVal :=
  match v with
  | .conc a =>
    match evalIntToIntCastComp a castTy with
    | .ok res => some (.conc res)
    | .error _ => none
  | .scalar s =>
    if !s.wf then none
    else
      match castTy with
      | .int dstW dstS => some (.scalar (.cast dstW dstS s))
      | _ => none
  | .bool _ | .pair _ _ => none

theorem symCastIntToInt_sound {v res : SymVal} {castTy : MirTy}
    (h : symCastIntToInt v castTy = some res) (env : SymEnv) :
    evalIntToIntCast (v.eval env) castTy = .ok (res.eval env) := by
  cases v with
  | bool _ | pair _ _ => cases h
  | conc a =>
    dsimp only [symCastIntToInt] at h
    cases hEv : evalIntToIntCastComp a castTy with
    | error _ => rw [hEv] at h; cases h
    | ok r =>
      rw [hEv] at h; cases h
      rw [← evalIntToIntCastComp_eq]
      exact hEv
  | scalar s =>
    dsimp only [symCastIntToInt] at h
    cases hWf : s.wf with
    | false => rw [hWf] at h; cases h
    | true =>
      rw [hWf] at h
      cases castTy with
      | int dstW dstS =>
        cases h
        dsimp only [SymVal.eval, SymScalar.eval]
        rw [evalIntToIntCastComp_eq]
        dsimp only [evalIntToIntCast, intLikeBits]
        cases (s.eval env).signed <;> rfl
      | bool | unit | never | char | ordering | enum _ | tuple _
      | ref _ _ | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _ | rangeFrom _
      | unsupported | option _ | range _ => cases h

/-- Symbolic local slot (uninitialized/initialized immediate or dead; indirect
slots are never allocated by `symEntry` / `storageLive`). -/
inductive SymSlot where
  | dead
  | immediate (v : Option SymVal)

/-- Evaluate `SymSlot` to `LocalSlot` under `env`. -/
@[expose] noncomputable def SymSlot.eval (env : SymEnv) : SymSlot → LocalSlot
  | .dead => .dead
  | .immediate opt => .immediate (opt.map (SymVal.eval env))

/-- Uninitialized live `SymSlot` mirror of `liveUninitSlotComp`. -/
@[expose] noncomputable def liveSymUninitSlot (ty : MirTy) : SymSlot :=
  match ty with
  | .unit => .immediate (some (.conc .unit))
  | .enum ety =>
    if isZstEnumTyComp ety then .immediate (some (.conc (.enumVal ety 0)))
    else .immediate none
  | _ => .immediate none

theorem liveSymUninitSlot_eval (env : SymEnv) (ty : MirTy) :
    (liveSymUninitSlot ty).eval env = liveUninitSlot ty := by
  cases ty with
  | enum ety =>
    dsimp only [liveSymUninitSlot, SymSlot.eval, liveUninitSlot]
    rw [isZstEnumTyComp_eq]
    cases isZstEnumTy ety <;> rfl
  | bool | int _ _ | char | ordering | unit | never | tuple _ | ref _ _
  | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _ | rangeFrom _
  | unsupported | option _ | range _ => rfl

/-- Symbolic single-frame MIR execution state (always at `defId = 0`, `mem =
entryMemory`, `callerMem = ⟨[]⟩`). -/
structure SymState where
  block : BasicBlockId
  stmt : Nat
  slots : List SymSlot

/-- Concrete `State` denoted by `SymState` under `env`. -/
@[expose] noncomputable def SymState.toState (env : SymEnv) (s : SymState) : State :=
  { frames := [{ defId := 0, blockIdx := s.block, stmtIdx := s.stmt,
                 locals := s.slots.map (SymSlot.eval env) }],
    callerMem := ⟨[]⟩, mem := entryMemory }

/-- Concrete `FrameState` denoted by `SymState` under `env`. -/
@[expose] noncomputable def SymState.toFrame (env : SymEnv) (s : SymState) : FrameState :=
  { defId := 0, blockIdx := s.block, stmtIdx := s.stmt,
    locals := s.slots.map (SymSlot.eval env) }

private theorem getElem?_symSlots (env : SymEnv) :
    ∀ (ls : List SymSlot) (n : Nat),
      Trusted.MirSemantics.getElem? (ls.map (SymSlot.eval env)) n =
        (compGetElem? ls n).map (SymSlot.eval env)
  | [], _ => by rw [compGetElem?_eq]; rfl
  | _ :: _, 0 => rfl
  | _ :: tl, n + 1 => by
    have ih := getElem?_symSlots env tl n
    rw [compGetElem?_eq] at ih
    rw [compGetElem?_eq]
    exact ih

private theorem setElem?_symSlots (env : SymEnv) :
    ∀ (ls : List SymSlot) (n : Nat) (v : SymSlot),
      Trusted.MirSemantics.setElem? (ls.map (SymSlot.eval env)) n (v.eval env) =
        (compSetElem? ls n v).map (List.map (SymSlot.eval env))
  | [], _, _ => by rw [compSetElem?_eq]; rfl
  | _ :: _, 0, _ => by rw [compSetElem?_eq]; rfl
  | x :: tl, n + 1, v => by
    have ih := setElem?_symSlots env tl n v
    rw [compSetElem?_eq] at ih
    rw [compSetElem?_eq]
    dsimp only [List.map, Trusted.MirSemantics.setElem?]
    rw [ih]
    cases Trusted.MirSemantics.setElem? tl n v <;> rfl

/-- Symbolic `evalOperandToSlot` (immediate locals & constants). -/
@[expose] noncomputable def symOperand (tys : List MirTy) (ls : List SymSlot) :
    Operand → Option (MirTy × Option SymVal × List SymSlot)
  | .copy p =>
    if p.projection.isEmpty then
      match compGetElem? tys p.localId, compGetElem? ls p.localId with
      | some ty, some (.immediate v) => some (ty, v, ls)
      | _, _ => none
    else none
  | .move p =>
    if p.projection.isEmpty then
      match compGetElem? tys p.localId, compGetElem? ls p.localId with
      | some ty, some (.immediate v) =>
        (compSetElem? ls p.localId (liveSymUninitSlot ty)).map
          fun ls' => (ty, v, ls')
      | _, _ => none
    else none
  | .constant c =>
    match evalConstLitComp c.ty c.lit with
    | .ok v => some (c.ty, some (.conc v), ls)
    | .error _ => none

theorem symOperand_sound {tys : List MirTy} {ls ls' : List SymSlot}
    {op : Operand} {ty : MirTy} {v : Option SymVal} {tyOk : MirTy → Bool}
    (h : symOperand tys ls op = some (ty, v, ls')) (env : SymEnv) :
    evalOperandToSlot tys (ls.map (SymSlot.eval env)) entryMemory tyOk op =
      .ok (ty, v.map (SymVal.eval env), ls'.map (SymSlot.eval env), entryMemory) := by
  cases op with
  | copy p =>
    dsimp only [symOperand] at h
    cases hp : p.projection.isEmpty with
    | false => rw [hp] at h; cases h
    | true =>
      rw [hp] at h
      cases ht : compGetElem? tys p.localId with
      | none => rw [ht] at h; cases h
      | some ty0 =>
        cases hs : compGetElem? ls p.localId with
        | none => rw [ht, hs] at h; cases h
        | some sl =>
          cases sl with
          | dead => rw [ht, hs] at h; cases h
          | immediate v0 =>
            rw [ht, hs] at h; cases h
            dsimp only [evalOperandToSlot]
            rw [← compGetElem?_eq, ht, getElem?_symSlots, hs]
            dsimp only [Option.map, SymSlot.eval]
            rw [hp]
            rfl
  | move p =>
    dsimp only [symOperand] at h
    cases hp : p.projection.isEmpty with
    | false => rw [hp] at h; cases h
    | true =>
      rw [hp] at h
      cases ht : compGetElem? tys p.localId with
      | none => rw [ht] at h; cases h
      | some ty0 =>
        cases hs : compGetElem? ls p.localId with
        | none => rw [ht, hs] at h; cases h
        | some sl =>
          cases sl with
          | dead => rw [ht, hs] at h; cases h
          | immediate v0 =>
            rw [ht, hs] at h
            dsimp only at h
            cases hSet : compSetElem? ls p.localId (liveSymUninitSlot ty0) with
            | none => rw [hSet] at h; cases h
            | some l1 =>
              rw [hSet] at h; cases h
              have hMap := setElem?_symSlots env ls p.localId (liveSymUninitSlot ty)
              rw [liveSymUninitSlot_eval, hSet] at hMap
              dsimp only [evalOperandToSlot]
              rw [← compGetElem?_eq, ht, getElem?_symSlots, hs]
              dsimp only [Option.map, SymSlot.eval]
              rw [hp, hMap]
              rfl
  | constant c =>
    dsimp only [symOperand] at h
    cases hc : evalConstLitComp c.ty c.lit with
    | error _ => rw [hc] at h; cases h
    | ok val =>
      rw [hc] at h; cases h
      dsimp only [evalOperandToSlot]
      rw [← evalConstLitComp_eq, hc]
      rfl

/-- Symbolic `evalPrimitiveOperand`. -/
@[expose] noncomputable def symPrim (tys : List MirTy) (ls : List SymSlot) (op : Operand) :
    Option (SymVal × List SymSlot) :=
  match symOperand tys ls op with
  | some (ty, some v, ls') =>
    if isPrimitiveReadableTyComp ty then some (v, ls') else none
  | _ => none

theorem symPrim_sound {tys : List MirTy} {ls ls' : List SymSlot}
    {op : Operand} {v : SymVal}
    (h : symPrim tys ls op = some (v, ls')) (env : SymEnv) :
    evalPrimitiveOperand tys (ls.map (SymSlot.eval env)) entryMemory op =
      .ok (v.eval env, ls'.map (SymSlot.eval env), entryMemory) := by
  dsimp only [symPrim] at h
  cases ho : symOperand tys ls op with
  | none => rw [ho] at h; cases h
  | some triple =>
    cases triple with
    | mk ty rest =>
      cases rest with
      | mk optv l1 =>
        cases optv with
        | none => rw [ho] at h; cases h
        | some v0 =>
          rw [ho] at h
          dsimp only at h
          cases hTy : isPrimitiveReadableTyComp ty with
          | false => rw [hTy] at h; cases h
          | true =>
            rw [hTy] at h; cases h
            dsimp only [evalPrimitiveOperand]
            rw [symOperand_sound ho env]
            dsimp only
            rw [← isPrimitiveReadableTyComp_eq, hTy]
            rfl

/-- Symbolic `evalRvalue` covering `.use`, `.binaryOp`, `.unaryOp`,
`.cast .intToInt`, and `.discriminant` (concrete enum & ordering values). -/
@[expose] noncomputable def symRvalue (tys : List MirTy) (ls : List SymSlot) (dst : MirTy) :
    Rvalue → Option (SymVal × List SymSlot)
  | .use op =>
    match symOperand tys ls op with
    | some (ty, some v, ls') =>
      match mirTyEqExact 16 ty dst with
      | some true => some (v, ls')
      | _ => none
    | _ => none
  | .binaryOp bop a b =>
    match symPrim tys ls a with
    | some (va, l1) =>
      match symPrim tys l1 b with
      | some (vb, l2) =>
        (symBinOp bop va vb).map fun v => (v, l2)
      | none => none
    | none => none
  | .unaryOp uop a =>
    match symPrim tys ls a with
    | some (va, l1) => (symUnOp uop va).map fun v => (v, l1)
    | none => none
  | .cast .intToInt a castTy =>
    match symOperand tys ls a with
    | some (srcTy, some va, l1) =>
      if isIntLikeTyComp srcTy then
        (symCastIntToInt va castTy).map fun v => (v, l1)
      else none
    | _ => none
  | .discriminant p =>
    if p.projection.isEmpty then
      match compGetElem? tys p.localId, compGetElem? ls p.localId with
      | some (.enum ety), some (.immediate (some (.conc v))) =>
        match evalDiscriminantOfValComp ety (some v) [] entryMemoryComp with
        | .ok (d, _, _) => some (.conc d, ls)
        | .error _ => none
      | some .ordering, some (.immediate (some (.conc v))) =>
        match evalOrderingDiscriminantOfValComp (some v) [] entryMemoryComp with
        | .ok (d, _, _) => some (.conc d, ls)
        | .error _ => none
      | _, _ => none
    else none
  | _ => none

theorem symRvalue_sound {tys : List MirTy} {ls ls' : List SymSlot}
    {dst : MirTy} {rv : Rvalue} {v : SymVal}
    (h : symRvalue tys ls dst rv = some (v, ls')) (env : SymEnv) :
    evalRvalue tys (ls.map (SymSlot.eval env)) entryMemory dst rv =
      .ok (v.eval env, ls'.map (SymSlot.eval env), entryMemory) := by
  cases rv with
  | ref _ _ | addressOf _ _ | fakeAddressOf _ | aggregateTuple _
  | aggregateArray _ _
  | repeat_ _ _ _ | useRetag _ | aggregateRangeTo _ _ | aggregateRangeFrom _ _
  | unsupported | aggregateOption _ _ _ | aggregateRange _ _ _ => cases h
  | cast ck a castTy =>
    cases ck with
    | ptrToPtr | intToPtr | unsize | unsupported => cases h
    | intToInt =>
      dsimp only [symRvalue] at h
      cases ho : symOperand tys ls a with
      | none => rw [ho] at h; cases h
      | some triple =>
        cases triple with
        | mk srcTy rest =>
          cases rest with
          | mk optv l1 =>
            cases optv with
            | none => rw [ho] at h; cases h
            | some va =>
              rw [ho] at h
              dsimp only at h
              cases hInt : isIntLikeTyComp srcTy with
              | false => rw [hInt] at h; cases h
              | true =>
                rw [hInt] at h
                cases hC : symCastIntToInt va castTy with
                | none => rw [hC] at h; cases h
                | some res =>
                  rw [hC] at h; cases h
                  dsimp only [evalRvalue]
                  rw [symOperand_sound ho env]
                  dsimp only
                  rw [← isIntLikeTyComp_eq, hInt]
                  rw [Bool.not_true, ite_prop_false (by decide)]
                  dsimp only [Option.map]
                  rw [symCastIntToInt_sound hC env]
  | use op =>
    dsimp only [symRvalue] at h
    cases ho : symOperand tys ls op with
    | none => rw [ho] at h; cases h
    | some triple =>
      cases triple with
      | mk ty rest =>
        cases rest with
        | mk optv l1 =>
          cases optv with
          | none => rw [ho] at h; cases h
          | some v0 =>
            rw [ho] at h
            dsimp only at h
            cases hTy : mirTyEqExact 16 ty dst with
            | none => rw [hTy] at h; cases h
            | some b =>
              cases b with
              | false => rw [hTy] at h; cases h
              | true =>
                rw [hTy] at h; cases h
                have hNotBeq : (!(ty.beq dst)) = false := by
                  rw [← mirTyEqExact_eq 16 ty dst true hTy]
                  rfl
                dsimp only [evalRvalue]
                rw [symOperand_sound ho env]
                dsimp only
                rw [hNotBeq]
                rfl
  | binaryOp bop a b =>
    dsimp only [symRvalue] at h
    cases ha : symPrim tys ls a with
    | none => rw [ha] at h; cases h
    | some pa =>
      cases pa with
      | mk va l1 =>
        rw [ha] at h
        dsimp only at h
        cases hb : symPrim tys l1 b with
        | none => rw [hb] at h; cases h
        | some pb =>
          cases pb with
          | mk vb l2 =>
            rw [hb] at h
            dsimp only at h
            cases hOp : symBinOp bop va vb with
            | none => rw [hOp] at h; cases h
            | some res =>
              rw [hOp] at h; cases h
              dsimp only [evalRvalue]
              rw [symPrim_sound ha env]
              dsimp only
              rw [symPrim_sound hb env]
              dsimp only
              rw [symBinOp_sound hOp env]
  | unaryOp uop a =>
    dsimp only [symRvalue] at h
    cases ha : symPrim tys ls a with
    | none => rw [ha] at h; cases h
    | some pa =>
      cases pa with
      | mk va l1 =>
        rw [ha] at h
        dsimp only at h
        cases hOp : symUnOp uop va with
        | none => rw [hOp] at h; cases h
        | some res =>
          rw [hOp] at h; cases h
          dsimp only [evalRvalue]
          rw [symPrim_sound ha env]
          dsimp only
          rw [symUnOp_sound hOp env]
  | discriminant p =>
    dsimp only [symRvalue] at h
    cases hp : p.projection.isEmpty with
    | false => rw [hp] at h; cases h
    | true =>
      rw [hp] at h
      cases ht : compGetElem? tys p.localId with
      | none => rw [ht] at h; cases h
      | some srcTy =>
        cases hs : compGetElem? ls p.localId with
        | none => cases srcTy <;> (rw [ht, hs] at h; cases h)
        | some sl =>
          cases sl with
          | dead => cases srcTy <;> (rw [ht, hs] at h; cases h)
          | immediate optv =>
            cases optv with
            | none => cases srcTy <;> (rw [ht, hs] at h; cases h)
            | some sv =>
              cases sv with
              | scalar _ | bool _ | pair _ _ =>
                cases srcTy <;> (rw [ht, hs] at h; cases h)
              | conc v0 =>
                cases srcTy with
                | enum ety =>
                  rw [ht, hs] at h
                  dsimp only at h
                  cases hEv : evalDiscriminantOfValComp ety (some v0) []
                      entryMemoryComp with
                  | error _ => rw [hEv] at h; cases h
                  | ok tri =>
                    cases tri with
                    | mk d r1 =>
                      cases r1 with
                      | mk _ _ =>
                        rw [hEv] at h; cases h
                        dsimp only [evalRvalue]
                        rw [← compGetElem?_eq, ht, getElem?_symSlots, hs]
                        dsimp only [Option.map, SymSlot.eval, SymVal.eval]
                        rw [entryMemoryComp_eq, evalDiscriminantOfValComp_eq] at hEv
                        rw [hp]
                        cases hE : evalDiscriminantOfVal ety (some v0) [] entryMemory with
                        | error _ => rw [hE] at hEv; cases hEv
                        | ok t2 =>
                          rw [hE] at hEv; cases hEv
                          dsimp only [evalDiscriminantOfVal] at hE
                          dsimp only [evalDiscriminantOfVal]
                          cases hAdm : enumAdmitted ety with
                          | false =>
                            rw [hAdm, Bool.not_false, ite_prop_true rfl] at hE
                            cases hE
                          | true =>
                            rw [hAdm, Bool.not_true, ite_bool_false] at hE
                            rw [Bool.not_true, ite_bool_false]
                            revert hE
                            cases ety.tagRepr with
                            | zeroSized =>
                              cases v0 with
                              | enumVal ty' var' =>
                                intro hE
                                dsimp only at hE
                                dsimp only
                                cases hB : (ety.beq ty' && Nat.beq var' 0) with
                                | false => rw [hB, ite_bool_false] at hE; cases hE
                                | true =>
                                  rw [hB, ite_bool_true] at hE
                                  rw [ite_bool_true]
                                  cases hDisc : Trusted.MirSemantics.getElem? ety.discriminants 0 with
                                  | none => rw [hDisc] at hE; cases hE
                                  | some _ => rw [hDisc] at hE; cases hE; rfl
                              | ptr _ | slicePtr _ _ | scalar _ | bool _ | char _ | ordering _
                              | unit | tuple _ | array _ | bytes _
                              | rangeTo _ | rangeFrom _ | optionVal _
                              | range _ _ =>
                                intro hE; dsimp only at hE; cases hE
                            | scalar _ _ =>
                              cases v0 with
                              | enumVal ty' var' =>
                                intro hE
                                dsimp only at hE
                                dsimp only
                                cases hB : (ety.beq ty' && Nat.blt var' ety.discriminants.length) with
                                | false => rw [hB, ite_bool_false] at hE; cases hE
                                | true =>
                                  rw [hB, ite_bool_true] at hE
                                  rw [ite_bool_true]
                                  cases hDisc : Trusted.MirSemantics.getElem? ety.discriminants var' with
                                  | none => rw [hDisc] at hE; cases hE
                                  | some _ => rw [hDisc] at hE; cases hE; rfl
                              | ptr _ | slicePtr _ _ | scalar _ | bool _ | char _ | ordering _
                              | unit | tuple _ | array _ | bytes _
                              | rangeTo _ | rangeFrom _ | optionVal _
                              | range _ _ =>
                                intro hE; dsimp only at hE; cases hE
                | ordering =>
                  rw [ht, hs] at h
                  dsimp only at h
                  cases hEv : evalOrderingDiscriminantOfValComp (some v0) []
                      entryMemoryComp with
                  | error _ => rw [hEv] at h; cases h
                  | ok tri =>
                    cases tri with
                    | mk d r1 =>
                      cases r1 with
                      | mk _ _ =>
                        rw [hEv] at h; cases h
                        dsimp only [evalRvalue]
                        rw [← compGetElem?_eq, ht, getElem?_symSlots, hs]
                        dsimp only [Option.map, SymSlot.eval, SymVal.eval]
                        rw [hp]
                        rw [entryMemoryComp_eq, evalOrderingDiscriminantOfValComp_eq] at hEv
                        cases v0 with
                        | ordering ord => cases hEv; rfl
                        | ptr _ | slicePtr _ _ | scalar _ | bool _ | char _ | unit | enumVal _ _
                        | tuple _ | array _ | bytes _ | rangeTo _
                        | rangeFrom _ | range _ _ => cases hEv
                        | optionVal optV => cases optV <;> (cases hEv)
                | bool | int _ _ | char | unit | never | tuple _ | ref _ _
                | rawPtr _ _ | slice _ | str | array _ _ | rangeTo _ | rangeFrom _
                | unsupported | option _ | range _ =>
                  rw [ht, hs] at h; cases h

/-- Symbolic `evalStatement`. -/
@[expose] noncomputable def symStatement (body : Body) (s : SymState) :
    StatementKind → Option SymState
  | .nop => some { s with stmt := s.stmt + 1 }
  | .storageLive l =>
    match compGetElem? body.locals l, compGetElem? s.slots l with
    | some ty, some _ =>
      (compSetElem? s.slots l (liveSymUninitSlot ty)).map fun ls =>
        { s with stmt := s.stmt + 1, slots := ls }
    | _, _ => none
  | .storageDead l =>
    if Nat.beq l 0 then none
    else
      match compGetElem? s.slots l with
      | some _ =>
        (compSetElem? s.slots l .dead).map fun ls =>
          { s with stmt := s.stmt + 1, slots := ls }
      | none => none
  | .assign dst rv =>
    if !dst.projection.isEmpty then none
    else
      match compGetElem? body.locals dst.localId with
      | none => none
      | some dstTy =>
        match symRvalue body.locals s.slots dstTy rv with
        | none => none
        | some (v, ls1) =>
          if symValCheckTy v dstTy then
            match compGetElem? ls1 dst.localId with
            | some (.immediate _) =>
              (compSetElem? ls1 dst.localId (.immediate (some v))).map
                fun ls2 => { s with stmt := s.stmt + 1, slots := ls2 }
            | _ => none
          else none
  | .unsupported => none

private theorem deallocateLocal_symSlot (slot : SymSlot) (env : SymEnv) :
    deallocateLocal entryMemory (slot.eval env) = .ok entryMemory := by
  cases slot <;> rfl

theorem symStatement_sound {body : Body} {s s' : SymState}
    {stmt : StatementKind} (h : symStatement body s stmt = some s')
    (env : SymEnv) :
    evalStatement body (s.toFrame env) entryMemory ⟨[]⟩ stmt =
      .step (s'.toState env) := by
  cases stmt with
  | unsupported => cases h
  | nop =>
    cases h
    rfl
  | storageLive l =>
    dsimp only [symStatement] at h
    cases ht : compGetElem? body.locals l with
    | none => rw [ht] at h; cases h
    | some ty =>
      cases hs : compGetElem? s.slots l with
      | none => rw [ht, hs] at h; cases h
      | some old =>
        rw [ht, hs] at h
        dsimp only at h
        cases hSet : compSetElem? s.slots l (liveSymUninitSlot ty) with
        | none => rw [hSet] at h; cases h
        | some ls' =>
          rw [hSet] at h; cases h
          have hMap := setElem?_symSlots env s.slots l (liveSymUninitSlot ty)
          rw [liveSymUninitSlot_eval, hSet] at hMap
          dsimp only [evalStatement, SymState.toFrame]
          rw [← compGetElem?_eq, ht]
          dsimp only
          rw [getElem?_symSlots, hs]
          dsimp only [Option.map]
          rw [hMap, deallocateLocal_symSlot]
          rfl
  | storageDead l =>
    dsimp only [symStatement] at h
    cases hz : Nat.beq l 0 with
    | true => rw [hz] at h; cases h
    | false =>
      rw [hz] at h
      cases hs : compGetElem? s.slots l with
      | none => rw [hs] at h; cases h
      | some old =>
        rw [hs] at h
        dsimp only at h
        cases hSet : compSetElem? s.slots l .dead with
        | none => rw [hSet] at h; cases h
        | some ls' =>
          rw [hSet] at h; cases h
          have hMap := setElem?_symSlots env s.slots l .dead
          rw [hSet] at hMap
          dsimp only [SymSlot.eval] at hMap
          dsimp only [evalStatement, SymState.toFrame]
          rw [hz, ite_prop_false (by decide), getElem?_symSlots, hs]
          dsimp only [Option.map]
          rw [hMap, deallocateLocal_symSlot]
          rfl
  | assign dst rv =>
    dsimp only [symStatement] at h
    cases hp : dst.projection.isEmpty with
    | false => rw [hp] at h; cases h
    | true =>
      rw [hp, Bool.not_true, ite_prop_false (by decide)] at h
      cases ht : compGetElem? body.locals dst.localId with
      | none => rw [ht] at h; cases h
      | some dstTy =>
        rw [ht] at h
        dsimp only at h
        cases hr : symRvalue body.locals s.slots dstTy rv with
        | none => rw [hr] at h; cases h
        | some p =>
          cases p with
          | mk v ls1 =>
            rw [hr] at h
            dsimp only at h
            cases hChk : symValCheckTy v dstTy with
            | false => rw [hChk] at h; cases h
            | true =>
              rw [hChk] at h
              cases hs : compGetElem? ls1 dst.localId with
              | none => rw [hs] at h; cases h
              | some sl =>
                cases sl with
                | dead => rw [hs] at h; cases h
                | immediate _ =>
                  rw [hs] at h
                  dsimp only at h
                  cases hSet : compSetElem? ls1 dst.localId (.immediate (some v)) with
                  | none => rw [hSet] at h; cases h
                  | some ls2 =>
                    rw [hSet] at h; cases h
                    have hMap := setElem?_symSlots env ls1 dst.localId
                      (.immediate (some v))
                    rw [hSet] at hMap
                    dsimp only [SymSlot.eval, Option.map] at hMap
                    dsimp only [evalStatement, SymState.toFrame]
                    rw [hp, Bool.not_true, ite_bool_false, ← compGetElem?_eq, ht]
                    dsimp only
                    rw [symRvalue_sound hr env]
                    dsimp only [writePlace]
                    rw [checkVal_of_symValCheckTy hChk env, Bool.not_true,
                      ite_bool_false, getElem?_symSlots, hs]
                    dsimp only [Option.map, SymSlot.eval]
                    rw [hMap]
                    rfl

/-- Result of one single-path symbolic execution step. -/
inductive SymRes where
  | step (next : SymState)
  | ret (val : SymVal)
  | stuck

/-- Symbolic `evalTerminator` (concrete or branch-empty `switchInt`, `goto`,
and `return_`). -/
@[expose] noncomputable def symTerminator (body : Body) (bb : BasicBlock) (s : SymState) :
    SymRes :=
  match bb.terminator with
  | .goto t => .step { s with block := t, stmt := 0 }
  | .return_ =>
    if bb.cleanup then .stuck
    else
      match compGetElem? s.slots 0 with
      | some (.immediate (some v)) => .ret v
      | _ => .stuck
  | .switchInt d targets =>
    match symPrim body.locals s.slots d with
    | some (.conc (.scalar sv), ls) =>
      match evalSwitchBranchesComp sv.width sv.bits targets.otherwise
          targets.branches with
      | .ok t => .step { block := t, stmt := 0, slots := ls }
      | .error _ => .stuck
    | some (.conc (.bool b), ls) =>
      match evalBoolSwitchBranchesComp b targets.otherwise targets.branches with
      | .ok t => .step { block := t, stmt := 0, slots := ls }
      | .error _ => .stuck
    | some (.conc (.char c), ls) =>
      match evalCharSwitchBranchesComp c targets.otherwise targets.branches with
      | .ok t => .step { block := t, stmt := 0, slots := ls }
      | .error _ => .stuck
    | some (_, ls) =>
      if targets.branches.isEmpty then
        .step { block := targets.otherwise, stmt := 0, slots := ls }
      else .stuck
    | none => .stuck
  | _ => .stuck

theorem symTerminator_step {body : Body} {bb : BasicBlock}
    {s s' : SymState} (h : symTerminator body bb s = .step s') (env : SymEnv) :
    evalTerminator body bb (s.toFrame env) entryMemory ⟨[]⟩ =
      .step (s'.toState env) := by
  dsimp only [symTerminator] at h
  cases hT : bb.terminator with
  | goto t =>
    rw [hT] at h; cases h
    dsimp only [evalTerminator]
    rw [hT]
    rfl
  | return_ =>
    rw [hT] at h
    dsimp only at h
    cases hCl : bb.cleanup with
    | true => rw [hCl] at h; cases h
    | false =>
      rw [hCl] at h
      cases hs : compGetElem? s.slots 0 with
      | none => rw [hs] at h; cases h
      | some sl =>
        cases sl with
        | dead => rw [hs] at h; cases h
        | immediate o => cases o <;> (rw [hs] at h; cases h)
  | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _
  | sysrootCall _ _ _ _ _
  | coreCall _ _ _ _ _ | unsupported =>
    rw [hT] at h; cases h
  | switchInt d targets =>
    rw [hT] at h
    dsimp only at h
    cases hd : symPrim body.locals s.slots d with
    | none => rw [hd] at h; cases h
    | some pair =>
      cases pair with
      | mk dv ls =>
        rw [hd] at h
        have hP := symPrim_sound hd env
        cases dv with
        | scalar _ | bool _ | pair _ _ =>
          dsimp only at h
          cases hB : targets.branches.isEmpty with
          | false => rw [hB] at h; cases h
          | true =>
            rw [hB] at h; cases h
            have hNil : targets.branches = [] := by
              cases hBr : targets.branches with
              | nil => rfl
              | cons _ _ => rw [hBr] at hB; cases hB
            dsimp only [evalTerminator, SymState.toFrame]
            rw [hT]
            dsimp only
            rw [hP]
            cases (SymVal.eval env _) <;> dsimp only <;>
              first
                | (rw [hNil]; rfl)
                | (unfold evalSwitchBranches; rw [hNil]; rfl)
                | (unfold evalBoolSwitchBranches; rw [hNil]; rfl)
                | (unfold evalCharSwitchBranches; rw [hNil]; rfl)
        | conc cv =>
          cases cv with
          | scalar sv =>
            dsimp only at h
            cases hSw : evalSwitchBranchesComp sv.width sv.bits
                targets.otherwise targets.branches with
            | error _ => rw [hSw] at h; cases h
            | ok t =>
              rw [hSw] at h; cases h
              rw [evalSwitchBranchesComp_eq] at hSw
              dsimp only [evalTerminator, SymState.toFrame]
              rw [hT]
              dsimp only
              rw [hP]
              dsimp only [SymVal.eval]
              rw [hSw]
              rfl
          | bool b =>
            dsimp only at h
            cases hSw : evalBoolSwitchBranchesComp b targets.otherwise
                targets.branches with
            | error _ => rw [hSw] at h; cases h
            | ok t =>
              rw [hSw] at h; cases h
              rw [evalBoolSwitchBranchesComp_eq] at hSw
              dsimp only [evalTerminator, SymState.toFrame]
              rw [hT]
              dsimp only
              rw [hP]
              dsimp only [SymVal.eval]
              rw [hSw]
              rfl
          | char c =>
            dsimp only at h
            cases hSw : evalCharSwitchBranchesComp c targets.otherwise
                targets.branches with
            | error _ => rw [hSw] at h; cases h
            | ok t =>
              rw [hSw] at h; cases h
              rw [evalCharSwitchBranchesComp_eq] at hSw
              dsimp only [evalTerminator, SymState.toFrame]
              rw [hT]
              dsimp only
              rw [hP]
              dsimp only [SymVal.eval]
              rw [hSw]
              rfl
          | ptr _ | slicePtr _ _ | ordering _ | unit | enumVal _ _ | tuple _
          | array _ | bytes _ | rangeTo _ | rangeFrom _ | optionVal _
          | range _ _ =>
            dsimp only at h
            cases hB : targets.branches.isEmpty with
            | false => rw [hB] at h; cases h
            | true =>
              rw [hB] at h; cases h
              have hNil : targets.branches = [] := by
                cases hBr : targets.branches with
                | nil => rfl
                | cons _ _ => rw [hBr] at hB; cases hB
              dsimp only [evalTerminator, SymState.toFrame]
              rw [hT]
              dsimp only
              rw [hP]
              dsimp only [SymVal.eval]
              rw [hNil]
              rfl

theorem symTerminator_ret {body : Body} {bb : BasicBlock} {s : SymState}
    {v : SymVal} (h : symTerminator body bb s = .ret v) (env : SymEnv) :
    evalTerminator body bb (s.toFrame env) entryMemory ⟨[]⟩ =
      .done (.returned ⟨v.eval env, ⟨[]⟩⟩) := by
  dsimp only [symTerminator] at h
  cases hT : bb.terminator with
  | return_ =>
    rw [hT] at h
    cases hCl : bb.cleanup with
    | true => rw [hCl] at h; cases h
    | false =>
      rw [hCl] at h
      dsimp only at h
      cases hs : compGetElem? s.slots 0 with
      | none => rw [hs] at h; cases h
      | some sl =>
        cases sl with
        | dead => rw [hs] at h; cases h
        | immediate opt =>
          cases opt with
          | none => rw [hs] at h; cases h
          | some v0 =>
            rw [hs] at h; cases h
            dsimp only [evalTerminator, SymState.toFrame]
            rw [hT, hCl, getElem?_symSlots, hs]
            rfl
  | goto _ | unreachable | unwindResume | assert _ _ _ _ _ | call _ _ _ _ _
  | sysrootCall _ _ _ _ _
  | coreCall _ _ _ _ _ | unsupported => rw [hT] at h; cases h
  | switchInt d targets =>
    rw [hT] at h
    dsimp only at h
    cases hd : symPrim body.locals s.slots d with
    | none => rw [hd] at h; cases h
    | some pair =>
      cases pair with
      | mk dv ls =>
        rw [hd] at h
        cases dv with
        | scalar _ | bool _ | pair _ _ =>
          dsimp only at h
          cases hbE : targets.branches.isEmpty with
          | true => rw [hbE, ite_prop_true (rfl : true = true)] at h; cases h
          | false => rw [hbE, ite_prop_false (by decide)] at h; cases h
        | conc cv =>
          cases cv with
          | scalar sv =>
            dsimp only at h
            cases hSw : evalSwitchBranchesComp sv.width sv.bits targets.otherwise
                targets.branches <;> (rw [hSw] at h; cases h)
          | bool b =>
            dsimp only at h
            cases hSw : evalBoolSwitchBranchesComp b targets.otherwise
                targets.branches <;> (rw [hSw] at h; cases h)
          | char c =>
            dsimp only at h
            cases hSw : evalCharSwitchBranchesComp c targets.otherwise
                targets.branches <;> (rw [hSw] at h; cases h)
          | ptr _ | slicePtr _ _ | ordering _ | unit | enumVal _ _ | tuple _
          | array _ | bytes _ | rangeTo _ | rangeFrom _ | optionVal _
          | range _ _ =>
            dsimp only at h
            cases hbE : targets.branches.isEmpty with
            | true => rw [hbE, ite_prop_true (rfl : true = true)] at h; cases h
            | false => rw [hbE, ite_prop_false (by decide)] at h; cases h

/-- Single symbolic MIR step. -/
@[expose] noncomputable def symStep (body : Body) (s : SymState) : SymRes :=
  match compGetElem? body.basicBlocks s.block with
  | none => .stuck
  | some bb =>
    match compGetElem? bb.statements s.stmt with
    | some stmt =>
      match symStatement body s stmt with
      | some s' => .step s'
      | none => .stuck
    | none =>
      if Nat.beq s.stmt bb.statements.length then symTerminator body bb s
      else .stuck

theorem symStep_step {body : Body} {s s' : SymState}
    (h : symStep body s = .step s') (env : SymEnv) :
    evalStep (bodyProg body) 0 (s.toState env) = .step (s'.toState env) := by
  dsimp only [symStep] at h
  cases hb : compGetElem? body.basicBlocks s.block with
  | none => rw [hb] at h; cases h
  | some bb =>
    rw [hb] at h
    dsimp only at h
    cases hSt : compGetElem? bb.statements s.stmt with
    | some stmt =>
      rw [hSt] at h
      dsimp only at h
      cases hSim : symStatement body s stmt with
      | none => rw [hSim] at h; cases h
      | some next =>
        rw [hSim] at h; cases h
        dsimp only [evalStep, bodyProg, SymState.toState, activeFrameBody,
          Trusted.MirSemantics.getElem?]
        rw [← compGetElem?_eq, hb]
        dsimp only
        rw [← compGetElem?_eq, hSt]
        exact symStatement_sound hSim env
    | none =>
      rw [hSt] at h
      dsimp only at h
      cases hLen : Nat.beq s.stmt bb.statements.length with
      | false => rw [hLen] at h; cases h
      | true =>
        rw [hLen] at h
        dsimp only [evalStep, bodyProg, SymState.toState, activeFrameBody,
          Trusted.MirSemantics.getElem?]
        rw [← compGetElem?_eq, hb]
        dsimp only
        rw [← compGetElem?_eq, hSt]
        dsimp only
        rw [hLen, ite_prop_true (rfl : true = true)]
        have hS := symTerminator_step h env
        cases hT : bb.terminator <;> first
          | exact hS
          | (dsimp only [symTerminator] at h; rw [hT] at h; cases h)

theorem symStep_ret {body : Body} {s : SymState} {v : SymVal}
    (h : symStep body s = .ret v) (env : SymEnv) :
    evalStep (bodyProg body) 0 (s.toState env) =
      .done (.returned ⟨v.eval env, ⟨[]⟩⟩) := by
  dsimp only [symStep] at h
  cases hb : compGetElem? body.basicBlocks s.block with
  | none => rw [hb] at h; cases h
  | some bb =>
    rw [hb] at h
    dsimp only at h
    cases hSt : compGetElem? bb.statements s.stmt with
    | some stmt =>
      rw [hSt] at h
      dsimp only at h
      cases hSim : symStatement body s stmt <;> (rw [hSim] at h; cases h)
    | none =>
      rw [hSt] at h
      dsimp only at h
      cases hLen : Nat.beq s.stmt bb.statements.length with
      | false => rw [hLen] at h; cases h
      | true =>
        rw [hLen] at h
        dsimp only [evalStep, bodyProg, SymState.toState, activeFrameBody,
          Trusted.MirSemantics.getElem?]
        rw [← compGetElem?_eq, hb]
        dsimp only
        rw [← compGetElem?_eq, hSt]
        dsimp only
        rw [hLen, ite_prop_true (rfl : true = true)]
        have hS := symTerminator_ret h env
        cases hT : bb.terminator <;> first
          | exact hS
          | (dsimp only [symTerminator] at h; rw [hT] at h; cases h)

/-- Fuel-bounded single-path symbolic runner (`@Nat.rec`, `0` `._unsafe_rec`).
-/
@[expose] noncomputable def symRun (body : Body) (fuel : Nat) (s : SymState) : SymRes :=
  @Nat.rec (fun _ => SymState → SymRes)
    (fun _ => .stuck)
    (fun _ ih st =>
      match symStep body st with
      | .step st' => ih st'
      | .ret v => .ret v
      | .stuck => .stuck)
    fuel s

/-- Symbolic entry locals mirror of `initLocalsLoopComp`. -/
@[expose] noncomputable def symInitLocalsLoop (body : Body) (args : List SymVal)
    (startIdx : Nat) (tys : List MirTy) : List SymSlot :=
  List.foldr
    (fun (ty : MirTy) (ih : Nat → List SymSlot) (idx : Nat) =>
      let slot : SymSlot :=
        if Nat.beq idx 0 then liveSymUninitSlot ty
        else if Nat.ble idx body.argumentCount then
          match compGetElem? args (idx - 1) with
          | some v => .immediate (some v)
          | none => .dead
        else if hasStorageAnnotationComp body idx then .dead
        else liveSymUninitSlot ty
      slot :: ih (idx + 1))
    (fun _ => [])
    tys startIdx

/-- Initial symbolic entry state at block `0`, statement `0`. -/
@[expose] noncomputable def symEntry (body : Body) (args : List SymVal) : SymState :=
  { block := 0, stmt := 0, slots := symInitLocalsLoop body args 0 body.locals }

private theorem getElem?_symVal_map (env : SymEnv) :
    ∀ (args : List SymVal) (idx : Nat),
      Trusted.MirSemantics.getElem? (args.map (SymVal.eval env)) idx =
        (compGetElem? args idx).map (SymVal.eval env)
  | [], _ => by rw [compGetElem?_eq]; rfl
  | _ :: _, 0 => rfl
  | _ :: tl, n + 1 => by
    have ih := getElem?_symVal_map env tl n
    rw [compGetElem?_eq] at ih
    rw [compGetElem?_eq]
    exact ih

private theorem symInitLocalsLoop_eval (body : Body) (args : List SymVal)
    (env : SymEnv) :
    ∀ (tys : List MirTy) (idx : Nat),
      (symInitLocalsLoop body args idx tys).map (SymSlot.eval env) =
        initLocalsLoop body (args.map (SymVal.eval env)) idx tys
  | [], _ => rfl
  | ty :: tl, idx => by
    have ih := symInitLocalsLoop_eval body args env tl (idx + 1)
    change SymSlot.eval env
        (if Nat.beq idx 0 then liveSymUninitSlot ty
         else if Nat.ble idx body.argumentCount then
           match compGetElem? args (idx - 1) with
           | some v => .immediate (some v)
           | none => .dead
         else if hasStorageAnnotationComp body idx then .dead
         else liveSymUninitSlot ty) ::
        (symInitLocalsLoop body args (idx + 1) tl).map (SymSlot.eval env) =
      _ :: initLocalsLoop body (args.map (SymVal.eval env)) (idx + 1) tl
    rw [ih]
    have hSlot :
        SymSlot.eval env
          (if Nat.beq idx 0 then liveSymUninitSlot ty
           else if Nat.ble idx body.argumentCount then
             match compGetElem? args (idx - 1) with
             | some v => .immediate (some v)
             | none => .dead
           else if hasStorageAnnotationComp body idx then .dead
           else liveSymUninitSlot ty) =
        (if Nat.beq idx 0 then liveUninitSlot ty
         else if Nat.ble idx body.argumentCount then
           match Trusted.MirSemantics.getElem? (args.map (SymVal.eval env)) (idx - 1) with
           | some v => .immediate (some v)
           | none => .dead
         else if hasStorageAnnotation body idx then .dead
         else liveUninitSlot ty) := by
      rw [← hasStorageAnnotationComp_eq body idx]
      cases Nat.beq idx 0 with
      | true => exact liveSymUninitSlot_eval env ty
      | false =>
        cases Nat.ble idx body.argumentCount with
        | true =>
          rw [getElem?_symVal_map]
          cases compGetElem? args (idx - 1) <;> rfl
        | false =>
          cases hasStorageAnnotationComp body idx with
          | true => rfl
          | false => exact liveSymUninitSlot_eval env ty
    exact congrArg (fun sl => sl :: initLocalsLoop body (args.map (SymVal.eval env)) (idx + 1) tl) hSlot

/-- Unconditional entry-state alignment between `symEntry` and `initLocalsLoop`.
-/
theorem symEntry_toState (body : Body) (args : List SymVal) (env : SymEnv) :
    (symEntry body args).toState env =
      mkState 0 0 (initLocalsLoop body (args.map (SymVal.eval env)) 0 body.locals) := by
  dsimp only [symEntry, SymState.toState, mkState]
  rw [symInitLocalsLoop_eval]

/-- Lift a single-path `symRun` return into `RunsFrom` (and thus `Executes`,
`SafeFrom`, and `ReturnsFrom`). -/
theorem symRun_runsFrom {body : Body} {out : SymVal} :
    ∀ {fuel : Nat} {s : SymState},
      symRun body fuel s = .ret out →
      ∀ (env : SymEnv), RunsFrom body fuel (s.toState env) (out.eval env)
  | 0, _, h, _ => by cases h
  | fuel + 1, s, h, env => by
    change (match symStep body s with
      | .step st' => symRun body fuel st'
      | .ret v => .ret v
      | .stuck => .stuck) = .ret out at h
    dsimp only [RunsFrom, execState, execOutcomeState, execStepOutcome]
    rw [execStepPred_succ_iff]
    cases hStep : symStep body s with
    | stuck => rw [hStep] at h; cases h
    | ret v =>
      rw [hStep] at h; cases h
      rw [symStep_ret hStep env]
    | step st' =>
      rw [hStep] at h
      rw [symStep_step hStep env]
      exact symRun_runsFrom h env

/-- Lift a single-path `symRun` return into `Executes`. -/
theorem symRun_executes {body : Body} {fuel : Nat} {s : SymState}
    {out : SymVal} (h : symRun body fuel s = .ret out) (env : SymEnv) :
    Executes body (s.toState env) (out.eval env) :=
  run_executes (symRun_runsFrom h env)

/-- Lift a `symRun` from `symEntry` into `Runs`, `Safe`, and `Returns`. -/
theorem symRun_entry {body : Body} {fuel : Nat} {args : List SymVal}
    {out : SymVal} (h : symRun body fuel (symEntry body args) = .ret out)
    (env : SymEnv) :
    Runs body fuel (args.map (SymVal.eval env)) (out.eval env) := by
  have hRuns := symRun_runsFrom h env
  rw [symEntry_toState] at hRuns
  exact hRuns

/-- Derive `Safe`, `Returns`, `SafeFrom`/`ReturnsFrom`/`Behavior` over
`entryProgForBody p defId` directly from `symRun` on `symEntry`. -/
theorem symRun_entry_behavior {p : Program} {defId : DefId} {body : Body}
    {fuel : Nat} {args : List SymVal} {out : SymVal}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hAdm : BodyStaticAdmitted p body = true)
    (env : SymEnv)
    (hArgs : ValidEntryArgs body (args.map (SymVal.eval env)))
    (hRun : symRun body fuel (symEntry body args) = .ret out)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    SafeFrom body (mkState 0 0
        (initLocalsLoop body (args.map (SymVal.eval env)) 0 body.locals)) ∧
      ReturnsFrom body (mkState 0 0
        (initLocalsLoop body (args.map (SymVal.eval env)) 0 body.locals))
        (out.eval env) ∧
      Trusted.MirSemantics.Behavior (entryProgForBody p defId)
        { args := args.map (SymVal.eval env) }
        (.returned ⟨out.eval env, ⟨[]⟩⟩) ∧
      ¬ Diverges (entryProgForBody p defId)
          { args := args.map (SymVal.eval env) } ∧
      SatisfiesPost (entryProgForBody p defId)
        { args := args.map (SymVal.eval env) }
        (fun outcome => outcome = .returned ⟨out.eval env, ⟨[]⟩⟩) := by
  have hRuns := symRun_entry hRun env
  have hSucc := run_initial_success hRuns
  have hExecProg :
      execProg (entryProgForBody p defId) fuel
        { args := args.map (SymVal.eval env) }
        (fun outcome => outcome = .returned ⟨out.eval env, ⟨[]⟩⟩) := by
    unfold execProg
    rw [initState_entryProgForBody hBody hAdm hArgs]
    exact execOutcomeState_entryProg_of_noFault hBody
      (isSingleFrame0_mkState 0 0 _) hRuns h_nocall
  have hAll := spec_and_behavior_of_wp_eq (wpProg_of_execProg hExecProg)
  exact ⟨hSucc.1, hSucc.2, hAll.2.1, hAll.2.2.1, hAll.2.2.2 _ rfl⟩

/-- Truncating a `BitVec k` lifted into `BitVec 128` at an `IntWidth` wide
enough to hold `2^k` is the identity. -/
theorem truncateBitsComp_bitVec_of_lt {k : Nat} {w : IntWidth} (x : BitVec k)
    (hk : Nat.pow 2 k ≤ intWidthModulus w) :
    truncateBitsComp w (BitVec.ofNat 128 x.toNat) = BitVec.ofNat 128 x.toNat := by
  rw [truncateBitsComp_eq]
  refine bv_eq_of_toNat_eq ?_
  rw [toNat_truncateBits, bv_toNat_ofNat]
  have hMod128 : Nat.pow 2 k ≤ Nat.pow 2 128 :=
    Nat.le_trans hk (by cases w <;> decide)
  have hx128 : x.toNat < Nat.pow 2 128 := Nat.lt_of_lt_of_le x.isLt hMod128
  have hxw : x.toNat < intWidthModulus w := Nat.lt_of_lt_of_le x.isLt hk
  rw [nat_mod_eq_of_lt hx128, nat_mod_eq_of_lt hxw]

/-- Discharge `BodyVerified p defId body safetyPre` from a single symbolic
run whose `SymVal` argument template covers every admitted entry argument list
satisfying `safetyPre`. -/
theorem symRun_bodyVerified_pre {p : Program} {defId : DefId} {body : Body}
    {fuel : Nat} {safetyPre : List Val → Prop}
    {argsTemplate : List SymVal} {out : SymVal}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hAdm : BodyStaticAdmitted p body = true)
    (hRun : symRun body fuel (symEntry body argsTemplate) = .ret out)
    (hCover : ∀ args : List Val, ValidEntryArgs body args →
      (body.isUnsafe = true → safetyPre args) →
      ∃ env : SymEnv, argsTemplate.map (SymVal.eval env) = args)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    BodyVerified p defId body safetyPre := by
  refine bodyVerified_of_safe hBody hAdm (fun args valid pre => ?_) h_nocall
  let ⟨env, hMap⟩ := hCover args valid pre
  have hSucc := run_initial_success (symRun_entry hRun env)
  rw [hMap] at hSucc
  exact hSucc.1

/-- Discharge `BodyVerified p defId body (fun _ => True)` from a single
symbolic run whose `SymVal` argument template covers every admitted entry
argument list. -/
theorem symRun_bodyVerified {p : Program} {defId : DefId} {body : Body}
    {fuel : Nat} {argsTemplate : List SymVal} {out : SymVal}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hAdm : BodyStaticAdmitted p body = true)
    (hRun : symRun body fuel (symEntry body argsTemplate) = .ret out)
    (hCover : ∀ args : List Val, ValidEntryArgs body args →
      (body.isUnsafe = true → True) →
      ∃ env : SymEnv, argsTemplate.map (SymVal.eval env) = args)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    BodyVerified p defId body (fun _ => True) :=
  symRun_bodyVerified_pre hBody hAdm hRun hCover h_nocall

/-! ### Step-Chunked Single-Path Runs

Elaborating `symRun body fuel s = .ret out := rfl` reduces the whole run in
one term, and that reduction does not share intermediate states: every later
read of a local re-reduces the steps that produced it, so the cost grows much
faster than the number of steps. `symRunSteps` stops after at most `k` steps
and reports the state it reached, so a proof can check short `rfl` chunks
against explicit checkpoint states and compose them with `symRunSteps_add`.
-/

/-- Run at most `k` single-path symbolic steps (`@Nat.rec`, `0`
`._unsafe_rec`). Returns `.step s'` for the state reached after exactly `k`
steps if the body has neither returned nor become stuck by then. -/
@[expose] noncomputable def symRunSteps (body : Body) (k : Nat) (s : SymState) :
    SymRes :=
  @Nat.rec (fun _ => SymState → SymRes)
    (fun st => .step st)
    (fun _ ih st =>
      match symStep body st with
      | .step st' => ih st'
      | .ret v => .ret v
      | .stuck => .stuck)
    k s

theorem symRunSteps_zero (body : Body) (s : SymState) :
    symRunSteps body 0 s = .step s := rfl

theorem symRunSteps_succ (body : Body) (k : Nat) (s : SymState) :
    symRunSteps body (k + 1) s =
      match symStep body s with
      | .step s' => symRunSteps body k s'
      | .ret v => .ret v
      | .stuck => .stuck := rfl

/-- Running `m + n` steps runs `m` steps, then `n` more from the reached state
unless the first `m` steps already returned or became stuck. -/
theorem symRunSteps_add (body : Body) :
    ∀ (m n : Nat) (s : SymState),
      symRunSteps body (m + n) s =
        match symRunSteps body m s with
        | .step s' => symRunSteps body n s'
        | .ret v => .ret v
        | .stuck => .stuck
  | 0, n, s => by rw [Nat.zero_add]; rfl
  | m + 1, n, s => by
    rw [Nat.succ_add, symRunSteps_succ, symRunSteps_succ]
    cases symStep body s with
    | step s' => exact symRunSteps_add body m n s'
    | ret v => rfl
    | stuck => rfl

/-- A chunked run that returns within `k` steps is a `symRun` with fuel `k`. -/
theorem symRunSteps_ret_symRun {body : Body} {v : SymVal} :
    ∀ {k : Nat} {s : SymState},
      symRunSteps body k s = .ret v → symRun body k s = .ret v
  | 0, _, h => by cases h
  | k + 1, s, h => by
    rw [symRunSteps_succ] at h
    change (match symStep body s with
      | .step st' => symRun body k st'
      | .ret v => .ret v
      | .stuck => .stuck) = .ret v
    cases hStep : symStep body s with
    | step s' => rw [hStep] at h; exact symRunSteps_ret_symRun h
    | ret w => rw [hStep] at h; exact h
    | stuck => rw [hStep] at h; cases h

/-- Prefix a concrete `RunsFrom` continuation with `k` symbolic steps. -/
theorem symRunSteps_step_runsFrom {body : Body} :
    ∀ {k : Nat} {s s' : SymState},
      symRunSteps body k s = .step s' →
      ∀ {n : Nat} {out : Val} (env : SymEnv),
        RunsFrom body n (s'.toState env) out →
        RunsFrom body (k + n) (s.toState env) out
  | 0, s, s', h, n, out, env, hRest => by
    cases h
    rw [Nat.zero_add]
    exact hRest
  | k + 1, s, s', h, n, out, env, hRest => by
    rw [symRunSteps_succ] at h
    rw [Nat.succ_add]
    dsimp only [RunsFrom, execState, execOutcomeState, execStepOutcome]
    rw [execStepPred_succ_iff]
    cases hStep : symStep body s with
    | step st' =>
      rw [hStep] at h
      rw [symStep_step hStep env]
      exact symRunSteps_step_runsFrom h env hRest
    | ret v => rw [hStep] at h; cases h
    | stuck => rw [hStep] at h; cases h

/-- Lift a chunked run that returns within `k` steps into `RunsFrom`. -/
theorem symRunSteps_ret_runsFrom {body : Body} {k : Nat} {s : SymState}
    {out : SymVal} (h : symRunSteps body k s = .ret out) (env : SymEnv) :
    RunsFrom body k (s.toState env) (out.eval env) :=
  symRun_runsFrom (symRunSteps_ret_symRun h) env

/-- `symRun_entry_behavior` for a chunked run from `symEntry`. -/
theorem symRunSteps_entry_behavior {p : Program} {defId : DefId} {body : Body}
    {k : Nat} {args : List SymVal} {out : SymVal}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hAdm : BodyStaticAdmitted p body = true)
    (env : SymEnv)
    (hArgs : ValidEntryArgs body (args.map (SymVal.eval env)))
    (hRun : symRunSteps body k (symEntry body args) = .ret out)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    SafeFrom body (mkState 0 0
        (initLocalsLoop body (args.map (SymVal.eval env)) 0 body.locals)) ∧
      ReturnsFrom body (mkState 0 0
        (initLocalsLoop body (args.map (SymVal.eval env)) 0 body.locals))
        (out.eval env) ∧
      Trusted.MirSemantics.Behavior (entryProgForBody p defId)
        { args := args.map (SymVal.eval env) }
        (.returned ⟨out.eval env, ⟨[]⟩⟩) ∧
      ¬ Diverges (entryProgForBody p defId)
          { args := args.map (SymVal.eval env) } ∧
      SatisfiesPost (entryProgForBody p defId)
        { args := args.map (SymVal.eval env) }
        (fun outcome => outcome = .returned ⟨out.eval env, ⟨[]⟩⟩) :=
  symRun_entry_behavior hBody hAdm env hArgs (symRunSteps_ret_symRun hRun)
    h_nocall

/-! ## Part IV: Branched Symbolic Execution with `BvLin` Dead-Branch Pruning -/

/-- Check whether a `SymBool` condition simplifies to `.lit false` (including
`BvLin` contradiction refutation). -/
@[expose] noncomputable def symPathUnsat (pc : SymBool) : Bool :=
  match pc.simplify with
  | .lit false => true
  | _ => false

theorem symPathUnsat_sound {pc : SymBool} (hWf : pc.wf = true)
    (hUnsat : symPathUnsat pc = true) (env : SymEnv) :
    pc.eval env = false := by
  unfold symPathUnsat at hUnsat
  cases hS : pc.simplify with
  | lit b =>
    cases b with
    | true => rw [hS] at hUnsat; cases hUnsat
    | false =>
      rw [← symBool_simplify_eval env pc hWf, hS]
      rfl
  | var _ | not _ | bin _ _ _ | cmp _ _ _ =>
    rw [hS] at hUnsat; cases hUnsat

/-- Conjoin path condition `pc` with `c` and simplify. -/
@[expose] noncomputable def symAndCond (pc c : SymBool) : SymBool :=
  (SymBool.bin .bitAnd pc c).simplify

theorem symAndCond_wf {pc c : SymBool} (hp : pc.wf = true) (hc : c.wf = true) :
    (symAndCond pc c).wf = true := by
  refine symBool_simplify_wf (.bin .bitAnd pc c) ?_
  dsimp only [SymBool.wf]
  rw [hp, hc]
  rfl

theorem symAndCond_eval (pc c : SymBool) (hp : pc.wf = true) (hc : c.wf = true)
    (env : SymEnv) :
    (symAndCond pc c).eval env = (pc.eval env && c.eval env) := by
  have hWf : (SymBool.bin .bitAnd pc c).wf = true := by
    dsimp only [SymBool.wf]
    rw [hp, hc]
    rfl
  exact symBool_simplify_eval env (.bin .bitAnd pc c) hWf

private theorem evalSwitchBranches_cons_eq (w : IntWidth) (discrBits : BitVec 128)
    (caseBits : BitVec 128) (target otherwise : BasicBlockId)
    (rest : List (BitVec 128 × BasicBlockId))
    (hCase : truncateBits w caseBits = caseBits) :
    evalSwitchBranches w discrBits otherwise ((caseBits, target) :: rest) =
      if truncateBits w discrBits == caseBits then .ok target
      else evalSwitchBranches w discrBits otherwise rest := by
  change (if truncateBits w caseBits != caseBits then Except.error FaultKind.unsupported
      else if truncateBits w discrBits == truncateBits w caseBits then Except.ok target
      else evalSwitchBranches w discrBits otherwise rest) = _
  rw [hCase]
  have hBne : (caseBits != caseBits) = false := bne_self_eq_false caseBits
  rw [hBne]
  rfl

private theorem evalBoolSwitchBranches_cons_eq (discr : Bool)
    (caseBits : BitVec 128) (target otherwise : BasicBlockId)
    (rest : List (BitVec 128 × BasicBlockId)) (caseBool : Bool)
    (hLit : evalConstLit .bool (.scalar caseBits) = .ok (.bool caseBool)) :
    evalBoolSwitchBranches discr otherwise ((caseBits, target) :: rest) =
      if discr == caseBool then .ok target
      else evalBoolSwitchBranches discr otherwise rest := by
  change (match (evalConstLit .bool (.scalar caseBits) : Except FaultKind Val) with
      | Except.ok (Val.bool false) =>
        if !discr then Except.ok target
        else evalBoolSwitchBranches discr otherwise rest
      | Except.ok (Val.bool true) =>
        if discr then Except.ok target
        else evalBoolSwitchBranches discr otherwise rest
      | Except.error k => Except.error k
      | Except.ok _ => Except.error FaultKind.unsupported) = _
  rw [hLit]
  cases caseBool <;> cases discr <;> rfl

/-- Outcome of one branched symbolic step. -/
inductive SymBranchStep where
  | done (pc : SymBool) (val : SymVal)
  | next (branches : List (SymBool × SymState))
  | stuck

/-- Symbolic branch expansion for `.bool` `switchInt` targets. -/
@[expose] noncomputable def symBoolBranches (pc : SymBool) (b : SymBool)
    (slots : List SymSlot) (otherwise : BasicBlockId) :
    List (BitVec 128 × BasicBlockId) → Option (List (SymBool × SymState))
  | [] =>
    if symPathUnsat pc then some []
    else some [(pc, { block := otherwise, stmt := 0, slots := slots })]
  | (caseBits, target) :: rest =>
    match evalConstLitComp .bool (.scalar caseBits) with
    | .ok (.bool caseBool) =>
      let eqCond : SymBool := if caseBool then b else .not b
      let neCond : SymBool := if caseBool then .not b else b
      let pcYes := symAndCond pc eqCond
      let pcNo := symAndCond pc neCond
      match symBoolBranches pcNo b slots otherwise rest with
      | none => none
      | some restBs =>
        if symPathUnsat pcYes then some restBs
        else some ((pcYes, { block := target, stmt := 0, slots := slots }) :: restBs)
    | _ => none

/-- Symbolic branch expansion for `.scalar` `switchInt` targets. -/
@[expose] noncomputable def symScalarBranches (pc : SymBool) (sc : SymScalar)
    (slots : List SymSlot) (otherwise : BasicBlockId) :
    List (BitVec 128 × BasicBlockId) → Option (List (SymBool × SymState))
  | [] =>
    if symPathUnsat pc then some []
    else some [(pc, { block := otherwise, stmt := 0, slots := slots })]
  | (caseBits, target) :: rest =>
    if !bv128BeqComp (truncateBitsComp sc.width caseBits) caseBits then none
    else
      let caseLit : SymScalar := .lit ⟨sc.width, sc.signed, caseBits⟩
      let eqCond : SymBool := .cmp .eq sc caseLit
      let neCond : SymBool := .cmp .ne sc caseLit
      let pcYes := symAndCond pc eqCond
      let pcNo := symAndCond pc neCond
      match symScalarBranches pcNo sc slots otherwise rest with
      | none => none
      | some restBs =>
        if symPathUnsat pcYes then some restBs
        else some ((pcYes, { block := target, stmt := 0, slots := slots }) :: restBs)

private theorem symBoolBranches_wf {b : SymBool} (hb : b.wf = true)
    (slots : List SymSlot) (otherwise : BasicBlockId) :
    ∀ (branches : List (BitVec 128 × BasicBlockId)) (pc : SymBool)
      (out : List (SymBool × SymState)),
      pc.wf = true →
      symBoolBranches pc b slots otherwise branches = some out →
      ∀ p, p ∈ out → p.1.wf = true
  | [], pc, out, hPc, h, p, hp => by
    dsimp only [symBoolBranches] at h
    cases hu : symPathUnsat pc with
    | true => rw [hu] at h; cases h; cases hp
    | false =>
      rw [hu] at h; cases h
      cases hp with
      | head _ => exact hPc
      | tail _ hT => cases hT
  | (caseBits, target) :: rest, pc, out, hPc, h, p, hp => by
    dsimp only [symBoolBranches] at h
    cases hLit : evalConstLitComp .bool (.scalar caseBits) with
    | error _ => rw [hLit] at h; cases h
    | ok v =>
      cases v with
      | ptr _ | slicePtr _ _ | scalar _ | char _ | ordering _ | unit
      | enumVal _ _ | tuple _ | array _ | bytes _ | rangeTo _ | rangeFrom _
      | optionVal _ | range _ _ =>
        rw [hLit] at h; cases h
      | bool caseBool =>
        rw [hLit] at h
        dsimp only at h
        have hEqWf : (if caseBool then b else SymBool.not b).wf = true := by
          cases caseBool <;> exact hb
        have hNeWf : (if caseBool then SymBool.not b else b).wf = true := by
          cases caseBool <;> exact hb
        have hYesWf := symAndCond_wf hPc hEqWf
        have hNoWf := symAndCond_wf hPc hNeWf
        cases hRest : symBoolBranches (symAndCond pc
            (if caseBool then SymBool.not b else b)) b slots otherwise rest with
        | none => rw [hRest] at h; cases h
        | some restBs =>
          rw [hRest] at h
          dsimp only at h
          cases hu : symPathUnsat (symAndCond pc
              (if caseBool then b else SymBool.not b)) with
          | true =>
            rw [hu] at h; cases h
            exact symBoolBranches_wf hb slots otherwise rest _ _ hNoWf hRest p hp
          | false =>
            rw [hu] at h; cases h
            cases hp with
            | head _ => exact hYesWf
            | tail _ hT =>
              exact symBoolBranches_wf hb slots otherwise rest _ _ hNoWf hRest p hT

private theorem symBoolBranches_sound {b : SymBool} (hb : b.wf = true)
    (slots : List SymSlot) (otherwise : BasicBlockId) :
    ∀ (branches : List (BitVec 128 × BasicBlockId)) (pc : SymBool)
      (out : List (SymBool × SymState)) (env : SymEnv),
      pc.wf = true → pc.eval env = true →
      symBoolBranches pc b slots otherwise branches = some out →
      ∃ t : BasicBlockId,
        evalBoolSwitchBranches (b.eval env) otherwise branches = .ok t ∧
        ∃ p, p ∈ out ∧ p.1.eval env = true ∧
          p.2 = { block := t, stmt := 0, slots := slots }
  | [], pc, out, env, hPc, hPcEv, h => by
    dsimp only [symBoolBranches] at h
    cases hu : symPathUnsat pc with
    | true =>
      have hFalse := symPathUnsat_sound hPc hu env
      rw [hFalse] at hPcEv
      cases hPcEv
    | false =>
      rw [hu] at h; cases h
      refine ⟨otherwise, rfl, (pc, { block := otherwise, stmt := 0, slots := slots }), ?_, hPcEv, rfl⟩
      exact List.Mem.head _
  | (caseBits, target) :: rest, pc, out, env, hPc, hPcEv, h => by
    dsimp only [symBoolBranches] at h
    cases hLit : evalConstLitComp .bool (.scalar caseBits) with
    | error _ => rw [hLit] at h; cases h
    | ok v =>
      cases v with
      | ptr _ | slicePtr _ _ | scalar _ | char _ | ordering _ | unit
      | enumVal _ _ | tuple _ | array _ | bytes _ | rangeTo _ | rangeFrom _
      | optionVal _ | range _ _ =>
        rw [hLit] at h; cases h
      | bool caseBool =>
        rw [hLit] at h
        dsimp only at h
        rw [evalConstLitComp_eq] at hLit
        have hEqWf : (if caseBool then b else SymBool.not b).wf = true := by
          cases caseBool <;> exact hb
        have hNeWf : (if caseBool then SymBool.not b else b).wf = true := by
          cases caseBool <;> exact hb
        have hYesWf := symAndCond_wf hPc hEqWf
        have hNoWf := symAndCond_wf hPc hNeWf
        cases hRest : symBoolBranches (symAndCond pc
            (if caseBool then SymBool.not b else b)) b slots otherwise rest with
        | none => rw [hRest] at h; cases h
        | some restBs =>
          rw [hRest] at h
          dsimp only at h
          cases hMatch : (b.eval env == caseBool) with
          | true =>
            have hYesEv : (symAndCond pc
                (if caseBool then b else SymBool.not b)).eval env = true := by
              rw [symAndCond_eval _ _ hPc hEqWf env, hPcEv]
              cases caseBool <;>
                (first | rw [ite_bool_true] | rw [ite_bool_false]) <;>
                cases hBEv : b.eval env <;>
                (first
                 | rfl
                 | (dsimp only [SymBool.eval]; rw [hBEv]; rfl)
                 | (rw [hBEv] at hMatch; cases hMatch))
            have hNotUnsat : symPathUnsat (symAndCond pc
                (if caseBool then b else SymBool.not b)) = false := by
              cases hu : symPathUnsat (symAndCond pc
                  (if caseBool then b else SymBool.not b)) with
              | false => rfl
              | true =>
                have hF := symPathUnsat_sound hYesWf hu env
                rw [hF] at hYesEv; cases hYesEv
            rw [hNotUnsat] at h; cases h
            refine ⟨target, ?_, (symAndCond pc (if caseBool then b else SymBool.not b),
                { block := target, stmt := 0, slots := slots }), ?_, hYesEv, rfl⟩
            · rw [evalBoolSwitchBranches_cons_eq _ _ _ _ _ caseBool hLit, hMatch]
              rfl
            · exact List.Mem.head _
          | false =>
            have hNoEv : (symAndCond pc
                (if caseBool then SymBool.not b else b)).eval env = true := by
              rw [symAndCond_eval _ _ hPc hNeWf env, hPcEv]
              cases caseBool <;>
                (first | rw [ite_bool_true] | rw [ite_bool_false]) <;>
                cases hBEv : b.eval env <;>
                (first
                 | rfl
                 | (dsimp only [SymBool.eval]; rw [hBEv]; rfl)
                 | (rw [hBEv] at hMatch; cases hMatch))
            let ⟨t, hSw, p, hpMem, hpEv, hpSt⟩ :=
              symBoolBranches_sound hb slots otherwise rest _ restBs env hNoWf hNoEv hRest
            refine ⟨t, ?_, p, ?_, hpEv, hpSt⟩
            · rw [evalBoolSwitchBranches_cons_eq _ _ _ _ _ caseBool hLit, hMatch]
              exact hSw
            · cases hu : symPathUnsat (symAndCond pc
                  (if caseBool then b else SymBool.not b)) with
              | true => rw [hu] at h; cases h; exact hpMem
              | false => rw [hu] at h; cases h; exact List.Mem.tail _ hpMem

private theorem symScalarBranches_wf {sc : SymScalar} (hsc : sc.wf = true)
    (slots : List SymSlot) (otherwise : BasicBlockId) :
    ∀ (branches : List (BitVec 128 × BasicBlockId)) (pc : SymBool)
      (out : List (SymBool × SymState)),
      pc.wf = true →
      symScalarBranches pc sc slots otherwise branches = some out →
      ∀ p, p ∈ out → p.1.wf = true
  | [], pc, out, hPc, h, p, hp => by
    dsimp only [symScalarBranches] at h
    cases hu : symPathUnsat pc with
    | true => rw [hu] at h; cases h; cases hp
    | false =>
      rw [hu] at h; cases h
      cases hp with
      | head _ => exact hPc
      | tail _ hT => cases hT
  | (caseBits, target) :: rest, pc, out, hPc, h, p, hp => by
    dsimp only [symScalarBranches] at h
    cases hCb : bv128BeqComp (truncateBitsComp sc.width caseBits) caseBits with
    | false => rw [hCb] at h; cases h
    | true =>
      rw [hCb] at h
      have hLitWf : (SymScalar.lit ⟨sc.width, sc.signed, caseBits⟩).wf = true := hCb
      have hCondWf : (SymBool.cmp .eq sc (.lit ⟨sc.width, sc.signed, caseBits⟩)).wf = true := by
        dsimp only [SymBool.wf]
        rw [hsc, hLitWf, intWidthBeqComp_eq, boolBeqComp_eq]
        cases sc.width <;> cases sc.signed <;> rfl
      have hNeCondWf : (SymBool.cmp .ne sc (.lit ⟨sc.width, sc.signed, caseBits⟩)).wf = true := by
        dsimp only [SymBool.wf]
        rw [hsc, hLitWf, intWidthBeqComp_eq, boolBeqComp_eq]
        cases sc.width <;> cases sc.signed <;> rfl
      have hYesWf := symAndCond_wf hPc hCondWf
      have hNoWf := symAndCond_wf hPc hNeCondWf
      cases hRest : symScalarBranches (symAndCond pc
          (.cmp .ne sc (.lit ⟨sc.width, sc.signed, caseBits⟩)))
          sc slots otherwise rest with
      | none => rw [hRest] at h; cases h
      | some restBs =>
        rw [hRest] at h
        dsimp only at h
        cases hu : symPathUnsat (symAndCond pc
            (.cmp .eq sc (.lit ⟨sc.width, sc.signed, caseBits⟩))) with
        | true =>
          rw [hu] at h; cases h
          exact symScalarBranches_wf hsc slots otherwise rest _ _ hNoWf hRest p hp
        | false =>
          rw [hu] at h; cases h
          cases hp with
          | head _ => exact hYesWf
          | tail _ hT =>
            exact symScalarBranches_wf hsc slots otherwise rest _ _ hNoWf hRest p hT

private theorem scalarVal_decode_eq_iff (w : IntWidth) (s : Bool)
    (l r : ScalarVal) (hlW : l.width = w) (hrW : r.width = w)
    (hlS : l.signed = s) (hrS : r.signed = s)
    (hlWf : ScalarVal.wf l = true) (hrWf : ScalarVal.wf r = true) :
    (decodeScalar l == decodeScalar r) = (truncateBits w l.bits == r.bits) := by
  have hTrR : truncateBits w r.bits = r.bits := by
    rw [← hrW]
    exact beq_iff_eq.mp hrWf
  have hTrL : truncateBits w l.bits = l.bits := by
    rw [← hlW]
    exact beq_iff_eq.mp hlWf
  cases hEqBits : l.bits == r.bits with
  | true =>
    have hB : l.bits = r.bits := beq_iff_eq.mp hEqBits
    have hLR : l = r := by
      cases l; cases r
      dsimp only at hlW hrW hlS hrS hB
      subst hlW; subst hrW; subst hlS; subst hrS; subst hB
      rfl
    rw [hLR, int_beq_self_eq_true, hTrR, beq_self_eq_true]
  | false =>
    rw [hTrL, hEqBits]
    cases hDec : decodeScalar l == decodeScalar r with
    | false => rfl
    | true =>
      have hDecEq := int_beq_iff_eq.mp hDec
      have hDl := bvOfInt_decodeScalar l
      have hDr := bvOfInt_decodeScalar r
      rw [hlW] at hDl
      rw [hrW] at hDr
      have hBvEq : BitVec.ofNat w.bitWidth l.bits.toNat =
          BitVec.ofNat w.bitWidth r.bits.toNat := by
        rw [← hDl, ← hDr, hDecEq]
      have hLReq := scalarVal_bits_eq_of_bvOfNat_eq hlW hrW (hlS.trans hrS.symm)
        hlWf hrWf hBvEq
      have hBitsEq : l.bits = r.bits := congrArg ScalarVal.bits hLReq
      rw [hBitsEq, beq_self_eq_true] at hEqBits
      cases hEqBits

private theorem symScalarBranches_sound {sc : SymScalar} (hsc : sc.wf = true)
    (slots : List SymSlot) (otherwise : BasicBlockId) :
    ∀ (branches : List (BitVec 128 × BasicBlockId)) (pc : SymBool)
      (out : List (SymBool × SymState)) (env : SymEnv),
      pc.wf = true → pc.eval env = true →
      symScalarBranches pc sc slots otherwise branches = some out →
      ∃ t : BasicBlockId,
        evalSwitchBranches (sc.eval env).width (sc.eval env).bits otherwise branches =
          .ok t ∧
        ∃ p, p ∈ out ∧ p.1.eval env = true ∧
          p.2 = { block := t, stmt := 0, slots := slots }
  | [], pc, out, env, hPc, hPcEv, h => by
    dsimp only [symScalarBranches] at h
    cases hu : symPathUnsat pc with
    | true =>
      have hF := symPathUnsat_sound hPc hu env
      rw [hF] at hPcEv; cases hPcEv
    | false =>
      rw [hu] at h; cases h
      refine ⟨otherwise, rfl, (pc, { block := otherwise, stmt := 0, slots := slots }),
        List.Mem.head _, hPcEv, rfl⟩
  | (caseBits, target) :: rest, pc, out, env, hPc, hPcEv, h => by
    dsimp only [symScalarBranches] at h
    cases hCb : bv128BeqComp (truncateBitsComp sc.width caseBits) caseBits with
    | false => rw [hCb] at h; cases h
    | true =>
      rw [hCb] at h
      have hLitWf : (SymScalar.lit ⟨sc.width, sc.signed, caseBits⟩).wf = true := hCb
      have hTrCase : truncateBits sc.width caseBits = caseBits := by
        rw [bv128BeqComp_eq_beq, truncateBitsComp_eq] at hCb
        exact beq_iff_eq.mp hCb
      have hCaseWf : ScalarVal.wf ⟨sc.width, sc.signed, caseBits⟩ = true :=
        beq_iff_eq.mpr hTrCase
      have hM := symScalar_eval_meta env sc hsc
      have hCondWf : (SymBool.cmp .eq sc (.lit ⟨sc.width, sc.signed, caseBits⟩)).wf = true := by
        dsimp only [SymBool.wf]
        rw [hsc, hLitWf, intWidthBeqComp_eq, boolBeqComp_eq]
        cases sc.width <;> cases sc.signed <;> rfl
      have hNeCondWf : (SymBool.cmp .ne sc (.lit ⟨sc.width, sc.signed, caseBits⟩)).wf = true := by
        dsimp only [SymBool.wf]
        rw [hsc, hLitWf, intWidthBeqComp_eq, boolBeqComp_eq]
        cases sc.width <;> cases sc.signed <;> rfl
      have hYesWf := symAndCond_wf hPc hCondWf
      have hNoWf := symAndCond_wf hPc hNeCondWf
      have hCmpEq :
          (SymBool.cmp .eq sc (.lit ⟨sc.width, sc.signed, caseBits⟩)).eval env =
            (truncateBits sc.width (sc.eval env).bits == caseBits) := by
        dsimp only [SymBool.eval]
        rw [evalBinOpComp_eq,
          evalBinOp_cmp_eq_ne .eq (Or.inl rfl) (sc.eval env)
            ((SymScalar.lit ⟨sc.width, sc.signed, caseBits⟩).eval env) hM.1 hM.2.1]
        dsimp only
        rw [symScalar_lit_eval hLitWf]
        exact scalarVal_decode_eq_iff sc.width sc.signed _ _ hM.1 rfl
          hM.2.1 rfl hM.2.2 hCaseWf
      have hCmpNe :
          (SymBool.cmp .ne sc (.lit ⟨sc.width, sc.signed, caseBits⟩)).eval env =
            !(truncateBits sc.width (sc.eval env).bits == caseBits) := by
        dsimp only [SymBool.eval]
        rw [evalBinOpComp_eq,
          evalBinOp_cmp_eq_ne .ne (Or.inr rfl) (sc.eval env)
            ((SymScalar.lit ⟨sc.width, sc.signed, caseBits⟩).eval env) hM.1 hM.2.1]
        dsimp only
        rw [symScalar_lit_eval hLitWf]
        change (decodeScalar (sc.eval env) != decodeScalar ⟨sc.width, sc.signed, caseBits⟩) = _
        have hEq := scalarVal_decode_eq_iff sc.width sc.signed _ _ hM.1 rfl
          hM.2.1 rfl hM.2.2 hCaseWf
        exact congrArg not hEq
      cases hRest : symScalarBranches (symAndCond pc
          (.cmp .ne sc (.lit ⟨sc.width, sc.signed, caseBits⟩)))
          sc slots otherwise rest with
      | none => rw [hRest] at h; cases h
      | some restBs =>
        rw [hRest] at h
        dsimp only at h
        cases hArm : truncateBits (sc.eval env).width (sc.eval env).bits == caseBits with
        | true =>
          have hArmSc :
              (truncateBits sc.width (sc.eval env).bits == caseBits) = true := by
            rw [← hM.1]; exact hArm
          have hYesEv : (symAndCond pc
              (.cmp .eq sc (.lit ⟨sc.width, sc.signed, caseBits⟩))).eval env = true := by
            rw [symAndCond_eval _ _ hPc hCondWf env, hPcEv, hCmpEq, hArmSc]
            rfl
          have hNotUnsat : symPathUnsat (symAndCond pc
              (.cmp .eq sc (.lit ⟨sc.width, sc.signed, caseBits⟩))) = false := by
            cases hu : symPathUnsat (symAndCond pc
                (.cmp .eq sc (.lit ⟨sc.width, sc.signed, caseBits⟩))) with
            | false => rfl
            | true =>
              have hF := symPathUnsat_sound hYesWf hu env
              rw [hF] at hYesEv; cases hYesEv
          rw [hNotUnsat] at h; cases h
          have hSwCase : truncateBits (sc.eval env).width caseBits = caseBits := by
            rw [hM.1]; exact hTrCase
          refine ⟨target, ?_, (symAndCond pc (.cmp .eq sc (.lit ⟨sc.width, sc.signed, caseBits⟩)),
              { block := target, stmt := 0, slots := slots }), List.Mem.head _, hYesEv, rfl⟩
          rw [evalSwitchBranches_cons_eq _ _ _ _ _ _ hSwCase, hArm]
          rfl
        | false =>
          have hArmSc :
              (truncateBits sc.width (sc.eval env).bits == caseBits) = false := by
            rw [← hM.1]; exact hArm
          have hNoEv : (symAndCond pc
              (.cmp .ne sc (.lit ⟨sc.width, sc.signed, caseBits⟩))).eval env = true := by
            rw [symAndCond_eval _ _ hPc hNeCondWf env, hPcEv, hCmpNe, hArmSc]
            rfl
          let ⟨t, hSw, p, hpMem, hpEv, hpSt⟩ :=
            symScalarBranches_sound hsc slots otherwise rest _ restBs env hNoWf hNoEv hRest
          have hSwCase : truncateBits (sc.eval env).width caseBits = caseBits := by
            rw [hM.1]; exact hTrCase
          refine ⟨t, ?_, p, ?_, hpEv, hpSt⟩
          · rw [evalSwitchBranches_cons_eq _ _ _ _ _ _ hSwCase, hArm]
            exact hSw
          · cases hu : symPathUnsat (symAndCond pc
                (.cmp .eq sc (.lit ⟨sc.width, sc.signed, caseBits⟩))) with
            | true => rw [hu] at h; cases h; exact hpMem
            | false => rw [hu] at h; cases h; exact List.Mem.tail _ hpMem

/-- Single-step branched symbolic execution. -/
@[expose] noncomputable def symStepBranched (body : Body) (pc : SymBool) (s : SymState) :
    SymBranchStep :=
  if symPathUnsat pc then .next []
  else
    match compGetElem? body.basicBlocks s.block with
    | none => .stuck
    | some bb =>
      match compGetElem? bb.statements s.stmt with
      | some stmt =>
        match symStatement body s stmt with
        | some s' => .next [(pc, s')]
        | none => .stuck
      | none =>
        if !Nat.beq s.stmt bb.statements.length then .stuck
        else
          match bb.terminator with
          | .switchInt discr targets =>
            match symPrim body.locals s.slots discr with
            | some (.bool b, ls) =>
              if b.wf then
                match symBoolBranches pc b ls targets.otherwise targets.branches with
                | some bs => .next bs
                | none => .stuck
              else .stuck
            | some (.scalar sc, ls) =>
              if sc.wf then
                match symScalarBranches pc sc ls targets.otherwise targets.branches with
                | some bs => .next bs
                | none => .stuck
              else .stuck
            | _ =>
              match symTerminator body bb s with
              | .step s' => .next [(pc, s')]
              | .ret v => .done pc v
              | .stuck => .stuck
          | _ =>
            match symTerminator body bb s with
            | .step s' => .next [(pc, s')]
            | .ret v => .done pc v
            | .stuck => .stuck

theorem symStepBranched_wf {body : Body} {pc : SymBool} {s : SymState}
    {bs : List (SymBool × SymState)} (hPc : pc.wf = true)
    (h : symStepBranched body pc s = .next bs) :
    (∀ p, p ∈ bs → p.1.wf = true) := by
  unfold symStepBranched at h
  cases hu : symPathUnsat pc with
  | true =>
    rw [hu] at h; cases h
    intro p hp; cases hp
  | false =>
    rw [hu, ite_prop_false (by decide)] at h
    cases hb : compGetElem? body.basicBlocks s.block with
    | none => rw [hb] at h; cases h
    | some bb =>
      rw [hb] at h
      dsimp only at h
      cases hSt : compGetElem? bb.statements s.stmt with
      | some stmt =>
        rw [hSt] at h
        dsimp only at h
        cases hSim : symStatement body s stmt with
        | none => rw [hSim] at h; cases h
        | some s' =>
          rw [hSim] at h; cases h
          intro p hp
          cases hp with
          | head _ => exact hPc
          | tail _ hT => cases hT
      | none =>
        rw [hSt] at h
        cases hLen : !Nat.beq s.stmt bb.statements.length with
        | true => rw [hLen, ite_prop_true rfl] at h; cases h
        | false =>
          rw [hLen, ite_prop_false (by decide)] at h
          cases hT : bb.terminator with
          | goto _ | return_ | unreachable | unwindResume
          | assert _ _ _ _ _ | call _ _ _ _ _ | sysrootCall _ _ _ _ _
          | coreCall _ _ _ _ _
          | unsupported =>
            rw [hT] at h
            cases hTerm : symTerminator body bb s with
            | ret _ | stuck => rw [hTerm] at h; cases h
            | step s' =>
              rw [hTerm] at h; cases h
              intro p hp
              cases hp with
              | head _ => exact hPc
              | tail _ hT2 => cases hT2
          | switchInt discr targets =>
            rw [hT] at h
            dsimp only at h
            cases hPr : symPrim body.locals s.slots discr with
            | none =>
              rw [hPr] at h
              cases hTerm : symTerminator body bb s with
              | ret _ | stuck => rw [hTerm] at h; cases h
              | step s' =>
                rw [hTerm] at h; cases h
                intro p hp
                cases hp with
                | head _ => exact hPc
                | tail _ hT2 => cases hT2
            | some pair =>
              cases pair with
              | mk dv ls =>
                rw [hPr] at h
                cases dv with
                | conc _ | pair _ _ =>
                  cases hTerm : symTerminator body bb s with
                  | ret _ | stuck => rw [hTerm] at h; cases h
                  | step s' =>
                    rw [hTerm] at h; cases h
                    intro p hp
                    cases hp with
                    | head _ => exact hPc
                    | tail _ hT2 => cases hT2
                | bool b =>
                  dsimp only at h
                  cases hWf : b.wf with
                  | false => rw [hWf] at h; cases h
                  | true =>
                    rw [hWf] at h
                    cases hBr : symBoolBranches pc b ls targets.otherwise targets.branches with
                    | none => rw [hBr] at h; cases h
                    | some out =>
                      rw [hBr] at h; cases h
                      exact symBoolBranches_wf hWf ls targets.otherwise
                        targets.branches pc _ hPc hBr
                | scalar sc =>
                  dsimp only at h
                  cases hWf : sc.wf with
                  | false => rw [hWf] at h; cases h
                  | true =>
                    rw [hWf] at h
                    cases hBr : symScalarBranches pc sc ls targets.otherwise targets.branches with
                    | none => rw [hBr] at h; cases h
                    | some out =>
                      rw [hBr] at h; cases h
                      exact symScalarBranches_wf hWf ls targets.otherwise
                        targets.branches pc _ hPc hBr

/-- Whether a Day-1 terminator is a `.call` or `.sysrootCall`, which
`evalStep` dispatches to `evalCallTerminator` rather than `evalTerminator`. -/
private noncomputable def symTermIsCall (t : TerminatorKind) : Bool :=
  match t with
  | .call _ _ _ _ _ | .sysrootCall _ _ _ _ _ => true
  | _ => false

private theorem symStep_sound_general {body : Body} {bb : BasicBlock}
    {s : SymState} {env : SymEnv}
    (hb : compGetElem? body.basicBlocks s.block = some bb)
    (hSt : compGetElem? bb.statements s.stmt = none)
    (hLen : Nat.beq s.stmt bb.statements.length = true)
    (hNC : symTermIsCall bb.terminator = false)
    (res : StepResult State TerminalOut)
    (hTerm : evalTerminator body bb (s.toFrame env) entryMemory ⟨[]⟩ = res) :
    evalStep (bodyProg body) 0 (s.toState env) = res := by
  dsimp only [evalStep, bodyProg, SymState.toState, activeFrameBody,
    Trusted.MirSemantics.getElem?]
  rw [← compGetElem?_eq, hb]
  dsimp only
  rw [← compGetElem?_eq, hSt]
  dsimp only
  rw [hLen, ite_prop_true (rfl : true = true)]
  cases hT : bb.terminator <;> first
    | exact hTerm
    | (rw [hT] at hNC; cases hNC)

theorem symStepBranched_sound {body : Body} {pc : SymBool} {s : SymState}
    (hPc : pc.wf = true) (env : SymEnv) (hPcEv : pc.eval env = true) :
    (∀ pc' out, symStepBranched body pc s = .done pc' out →
      pc'.eval env = true ∧
        evalStep (bodyProg body) 0 (s.toState env) =
          .done (.returned ⟨out.eval env, ⟨[]⟩⟩)) ∧
    (∀ bs, symStepBranched body pc s = .next bs →
      ∃ p, p ∈ bs ∧ p.1.eval env = true ∧
        evalStep (bodyProg body) 0 (s.toState env) = .step (p.2.toState env)) := by
  unfold symStepBranched
  cases hu : symPathUnsat pc with
  | true =>
    have hF := symPathUnsat_sound hPc hu env
    rw [hF] at hPcEv; cases hPcEv
  | false =>
    rw [ite_prop_false (by decide)]
    cases hb : compGetElem? body.basicBlocks s.block with
    | none => exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
    | some bb =>
      dsimp only
      cases hSt : compGetElem? bb.statements s.stmt with
      | some stmt =>
        dsimp only
        cases hSim : symStatement body s stmt with
        | none => exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
        | some s' =>
          refine ⟨(fun _ _ h => by cases h), fun bs h => ?_⟩
          cases h
          refine ⟨(pc, s'), List.Mem.head _, hPcEv, ?_⟩
          dsimp only [evalStep, bodyProg, SymState.toState, activeFrameBody,
            Trusted.MirSemantics.getElem?]
          rw [← compGetElem?_eq, hb]
          dsimp only
          rw [← compGetElem?_eq, hSt]
          exact symStatement_sound hSim env
      | none =>
        dsimp only
        cases hLen : Nat.beq s.stmt bb.statements.length with
        | false =>
          rw [Bool.not_false, ite_prop_true rfl]
          exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
        | true =>
          rw [Bool.not_true, ite_prop_false (by decide)]
          cases hT : bb.terminator with
          | call _ _ _ _ _ | sysrootCall _ _ _ _ _ =>
            dsimp only
            have hStuck : symTerminator body bb s = .stuck := by
              dsimp only [symTerminator]
              rw [hT]
            rw [hStuck]
            exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
          | goto _ | return_ | unreachable | unwindResume
          | assert _ _ _ _ _ | coreCall _ _ _ _ _
          | unsupported =>
            dsimp only
            cases hTerm : symTerminator body bb s with
            | stuck => exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
            | ret v =>
              refine ⟨fun pc' out h => ?_, (fun _ h => by cases h)⟩
              cases h
              exact ⟨hPcEv, symStep_sound_general hb hSt hLen
                (by first | (rw [hT]; rfl) | rw [hT]) _
                (symTerminator_ret hTerm env)⟩
            | step s' =>
              refine ⟨(fun _ _ h => by cases h), fun bs h => ?_⟩
              cases h
              exact ⟨(pc, s'), List.Mem.head _, hPcEv,
                symStep_sound_general hb hSt hLen
                  (by first | (rw [hT]; rfl) | rw [hT]) _ (symTerminator_step hTerm env)⟩
          | switchInt discr targets =>
            dsimp only
            cases hPr : symPrim body.locals s.slots discr with
            | none =>
              dsimp only
              cases hTerm : symTerminator body bb s with
              | stuck => exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
              | ret v =>
                refine ⟨fun pc' out h => ?_, (fun _ h => by cases h)⟩
                cases h
                exact ⟨hPcEv, symStep_sound_general hb hSt hLen
                  (by first | (rw [hT]; rfl) | rw [hT]) _
                  (symTerminator_ret hTerm env)⟩
              | step s' =>
                refine ⟨(fun _ _ h => by cases h), fun bs h => ?_⟩
                cases h
                exact ⟨(pc, s'), List.Mem.head _, hPcEv,
                  symStep_sound_general hb hSt hLen
                    (by first | (rw [hT]; rfl) | rw [hT]) _ (symTerminator_step hTerm env)⟩
            | some pair =>
              cases pair with
              | mk dv ls =>
                cases dv with
                | conc _ | pair _ _ =>
                  dsimp only
                  cases hTerm : symTerminator body bb s with
                  | stuck => exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
                  | ret v =>
                    refine ⟨fun pc' out h => ?_, (fun _ h => by cases h)⟩
                    cases h
                    exact ⟨hPcEv, symStep_sound_general hb hSt hLen
                      (by first | (rw [hT]; rfl) | rw [hT]) _
                      (symTerminator_ret hTerm env)⟩
                  | step s' =>
                    refine ⟨(fun _ _ h => by cases h), fun bs h => ?_⟩
                    cases h
                    exact ⟨(pc, s'), List.Mem.head _, hPcEv,
                      symStep_sound_general hb hSt hLen
                        (by first | (rw [hT]; rfl) | rw [hT]) _ (symTerminator_step hTerm env)⟩
                | bool b =>
                  dsimp only
                  cases hWf : b.wf with
                  | false =>
                    rw [ite_prop_false (by decide)]
                    exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
                  | true =>
                    rw [ite_prop_true rfl]
                    cases hBr : symBoolBranches pc b ls targets.otherwise targets.branches with
                    | none => exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
                    | some out =>
                      refine ⟨(fun _ _ h => by cases h), fun bs h => ?_⟩
                      cases h
                      let ⟨t, hSw, p, hpMem, hpEv, hpSt⟩ :=
                        symBoolBranches_sound hWf ls targets.otherwise
                          targets.branches pc out env hPc hPcEv hBr
                      refine ⟨p, hpMem, hpEv, ?_⟩
                      rw [hpSt]
                      refine symStep_sound_general hb hSt hLen
                        (by first | (rw [hT]; rfl) | rw [hT]) _ ?_
                      dsimp only [evalTerminator, SymState.toFrame]
                      rw [hT]
                      dsimp only
                      rw [symPrim_sound hPr env]
                      dsimp only [SymVal.eval]
                      rw [hSw]
                      rfl
                | scalar sc =>
                  dsimp only
                  cases hWf : sc.wf with
                  | false =>
                    rw [ite_prop_false (by decide)]
                    exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
                  | true =>
                    rw [ite_prop_true rfl]
                    cases hBr : symScalarBranches pc sc ls targets.otherwise targets.branches with
                    | none => exact ⟨(fun _ _ h => by cases h), (fun _ h => by cases h)⟩
                    | some out =>
                      refine ⟨(fun _ _ h => by cases h), fun bs h => ?_⟩
                      cases h
                      let ⟨t, hSw, p, hpMem, hpEv, hpSt⟩ :=
                        symScalarBranches_sound hWf ls targets.otherwise
                          targets.branches pc out env hPc hPcEv hBr
                      refine ⟨p, hpMem, hpEv, ?_⟩
                      rw [hpSt]
                      refine symStep_sound_general hb hSt hLen
                        (by first | (rw [hT]; rfl) | rw [hT]) _ ?_
                      dsimp only [evalTerminator, SymState.toFrame]
                      rw [hT]
                      dsimp only
                      rw [symPrim_sound hPr env]
                      dsimp only [SymVal.eval]
                      rw [hSw]
                      rfl

/-- Worklist `(donePaths, activePaths)` for branched symbolic execution. -/
abbrev SymWorkState := List (SymBool × SymVal) × List (SymBool × SymState)

/-- Advance all active symbolic states by one step. -/
@[expose] noncomputable def symStepAll (body : Body) (doneAcc : List (SymBool × SymVal)) :
    List (SymBool × SymState) → Option SymWorkState
  | [] => some (doneAcc, [])
  | (pc, s) :: rest =>
    match symStepBranched body pc s with
    | .stuck => none
    | .done pc' v =>
      match symStepAll body ((pc', v) :: doneAcc) rest with
      | none => none
      | some (d', a') => some (d', a')
    | .next bs =>
      match symStepAll body doneAcc rest with
      | none => none
      | some (d', a') => some (d', bs ++ a')

/-- Fuel-bounded branched symbolic runner via `@Nat.rec` (`0` `._unsafe_rec`).
-/
@[expose] noncomputable def symRunPathsAux (body : Body) (fuel : Nat) (st : SymWorkState) :
    Option (List (SymBool × SymVal)) :=
  @Nat.rec (fun _ => SymWorkState → Option (List (SymBool × SymVal)))
    (fun cur => if cur.2.isEmpty then some cur.1 else none)
    (fun _ ih cur =>
      if cur.2.isEmpty then some cur.1
      else
        match symStepAll body cur.1 cur.2 with
        | none => none
        | some cur' => ih cur')
    fuel st

/-- Run all feasible symbolic paths of `body` from `(pc, s)` up to `fuel`
steps, failing closed (`none`) if any path gets stuck or runs out of fuel. -/
@[expose] noncomputable def symRunPaths (body : Body) (fuel : Nat) (pc : SymBool)
    (s : SymState) : Option (List (SymBool × SymVal)) :=
  symRunPathsAux body fuel ([], [(pc, s)])

private theorem list_mem_append {α : Type} {x : α} :
    ∀ {xs ys : List α}, x ∈ xs ++ ys ↔ x ∈ xs ∨ x ∈ ys
  | [], _ys =>
    ⟨fun h => Or.inr h, fun h => match h with | Or.inr hy => hy⟩
  | _ :: xs, ys =>
    ⟨fun h =>
      match h with
      | .head _ => Or.inl (List.Mem.head _)
      | .tail _ ht =>
        match (list_mem_append (xs := xs) (ys := ys)).mp ht with
        | Or.inl h1 => Or.inl (List.Mem.tail _ h1)
        | Or.inr h2 => Or.inr h2,
     fun h =>
      match h with
      | Or.inl (.head _) => List.Mem.head _
      | Or.inl (.tail _ ht) =>
        List.Mem.tail _ ((list_mem_append (xs := xs) (ys := ys)).mpr (Or.inl ht))
      | Or.inr hy =>
        List.Mem.tail _ ((list_mem_append (xs := xs) (ys := ys)).mpr (Or.inr hy))⟩

private theorem symStepAll_wf (body : Body) :
    ∀ (active : List (SymBool × SymState)) (doneAcc : List (SymBool × SymVal))
      (res : SymWorkState),
      (∀ p, p ∈ active → p.1.wf = true) →
      symStepAll body doneAcc active = some res →
      ∀ p, p ∈ res.2 → p.1.wf = true
  | [], doneAcc, res, _, h => by
    cases h
    intro p hp; cases hp
  | (pc, s) :: rest, doneAcc, res, hWf, h => by
    dsimp only [symStepAll] at h
    have hPcWf := hWf (pc, s) (List.Mem.head _)
    have hRestWf : ∀ p, p ∈ rest → p.1.wf = true :=
      fun p hp => hWf p (List.Mem.tail _ hp)
    cases hStep : symStepBranched body pc s with
    | stuck => rw [hStep] at h; cases h
    | done pc' v =>
      rw [hStep] at h
      dsimp only at h
      cases hRest : symStepAll body ((pc', v) :: doneAcc) rest with
      | none => rw [hRest] at h; cases h
      | some p =>
        cases p with
        | mk d' a' =>
          rw [hRest] at h; cases h
          exact symStepAll_wf body rest ((pc', v) :: doneAcc) (d', a') hRestWf hRest
    | next bs =>
      rw [hStep] at h
      cases hRest : symStepAll body doneAcc rest with
      | none => rw [hRest] at h; cases h
      | some p =>
        cases p with
        | mk d' a' =>
          rw [hRest] at h; cases h
          intro q hq
          cases list_mem_append.mp hq with
          | inl hb => exact symStepBranched_wf hPcWf hStep q hb
          | inr ha => exact symStepAll_wf body rest doneAcc (d', a') hRestWf hRest q ha

private theorem symStepAll_preserves_done (body : Body) :
    ∀ (active : List (SymBool × SymState)) (doneAcc : List (SymBool × SymVal))
      (res : SymWorkState) (x : SymBool × SymVal),
      symStepAll body doneAcc active = some res →
      x ∈ doneAcc → x ∈ res.1
  | [], doneAcc, res, x, h, hx => by cases h; exact hx
  | (pc, s) :: rest, doneAcc, res, x, h, hx => by
    dsimp only [symStepAll] at h
    cases hStep : symStepBranched body pc s with
    | stuck => rw [hStep] at h; cases h
    | done pc' v =>
      rw [hStep] at h
      dsimp only at h
      cases hRest : symStepAll body ((pc', v) :: doneAcc) rest with
      | none => rw [hRest] at h; cases h
      | some p =>
        cases p with
        | mk d' a' =>
          rw [hRest] at h; cases h
          exact symStepAll_preserves_done body rest ((pc', v) :: doneAcc) (d', a') x
            hRest (List.Mem.tail _ hx)
    | next bs =>
      rw [hStep] at h
      cases hRest : symStepAll body doneAcc rest with
      | none => rw [hRest] at h; cases h
      | some p =>
        cases p with
        | mk d' a' =>
          rw [hRest] at h; cases h
          exact symStepAll_preserves_done body rest doneAcc (d', a') x hRest hx

private theorem symStepAll_sound (body : Body) (env : SymEnv) :
    ∀ (active : List (SymBool × SymState)) (doneAcc : List (SymBool × SymVal))
      (res : SymWorkState) (p : SymBool × SymState),
      (∀ q, q ∈ active → q.1.wf = true) →
      symStepAll body doneAcc active = some res →
      p ∈ active → p.1.eval env = true →
      (∃ out : SymVal, ∃ pc' : SymBool,
        (pc', out) ∈ res.1 ∧ pc'.eval env = true ∧
        evalStep (bodyProg body) 0 (p.2.toState env) =
          .done (.returned ⟨out.eval env, ⟨[]⟩⟩)) ∨
      (∃ q, q ∈ res.2 ∧ q.1.eval env = true ∧
        evalStep (bodyProg body) 0 (p.2.toState env) = .step (q.2.toState env))
  | [], _, _, _, _, _, hp, _ => by cases hp
  | (pc, s) :: rest, doneAcc, res, p, hWf, h, hpMem, hpEv => by
    dsimp only [symStepAll] at h
    have hPcWf := hWf (pc, s) (List.Mem.head _)
    have hRestWf : ∀ q, q ∈ rest → q.1.wf = true :=
      fun q hq => hWf q (List.Mem.tail _ hq)
    cases hStep : symStepBranched body pc s with
    | stuck => rw [hStep] at h; cases h
    | done pc' v =>
      rw [hStep] at h
      dsimp only at h
      cases hRest : symStepAll body ((pc', v) :: doneAcc) rest with
      | none => rw [hRest] at h; cases h
      | some pRes =>
        cases pRes with
        | mk d' a' =>
          rw [hRest] at h; cases h
          cases hpMem with
          | head _ =>
            have ⟨hPc'Ev, hEv⟩ :=
              (symStepBranched_sound hPcWf env hpEv).1 pc' v hStep
            exact Or.inl ⟨v, pc',
              symStepAll_preserves_done body rest ((pc', v) :: doneAcc) (d', a')
                (pc', v) hRest (List.Mem.head _), hPc'Ev, hEv⟩
          | tail _ hpR =>
            exact symStepAll_sound body env rest ((pc', v) :: doneAcc) (d', a') p
              hRestWf hRest hpR hpEv
    | next bs =>
      rw [hStep] at h
      dsimp only at h
      cases hRest : symStepAll body doneAcc rest with
      | none => rw [hRest] at h; cases h
      | some pRes =>
        cases pRes with
        | mk d' a' =>
          rw [hRest] at h; cases h
          cases hpMem with
          | head _ =>
            let ⟨q, hqMem, hqEv, hEv⟩ :=
              (symStepBranched_sound hPcWf env hpEv).2 bs hStep
            exact Or.inr ⟨q, list_mem_append.mpr (Or.inl hqMem), hqEv, hEv⟩
          | tail _ hpR =>
            cases symStepAll_sound body env rest doneAcc (d', a') p
                hRestWf hRest hpR hpEv with
            | inl hl => exact Or.inl hl
            | inr hr =>
              let ⟨q, hqMem, hqEv, hEv⟩ := hr
              exact Or.inr ⟨q, list_mem_append.mpr (Or.inr hqMem), hqEv, hEv⟩

private theorem symRunPathsAux_preserves_done (body : Body) :
    ∀ (fuel : Nat) (st : SymWorkState) (out : List (SymBool × SymVal))
      (x : SymBool × SymVal),
      symRunPathsAux body fuel st = some out →
      x ∈ st.1 → x ∈ out
  | 0, st, out, x, h, hx => by
    change (if st.2.isEmpty then some st.1 else none) = some out at h
    cases he : st.2.isEmpty with
    | false => rw [he] at h; cases h
    | true => rw [he] at h; cases h; exact hx
  | fuel + 1, st, out, x, h, hx => by
    change (if st.2.isEmpty then some st.1
      else match symStepAll body st.1 st.2 with
        | none => none
        | some st' => symRunPathsAux body fuel st') = some out at h
    cases he : st.2.isEmpty with
    | true => rw [he] at h; cases h; exact hx
    | false =>
      rw [he] at h
      cases hStep : symStepAll body st.1 st.2 with
      | none => rw [hStep] at h; cases h
      | some st' =>
        rw [hStep] at h
        exact symRunPathsAux_preserves_done body fuel st' out x h
          (symStepAll_preserves_done body st.2 st.1 st' x hStep hx)

private theorem symRunPathsAux_sound (body : Body) (env : SymEnv) :
    ∀ (fuel : Nat) (st : SymWorkState) (out : List (SymBool × SymVal))
      (p : SymBool × SymState),
      (∀ q, q ∈ st.2 → q.1.wf = true) →
      symRunPathsAux body fuel st = some out →
      p ∈ st.2 → p.1.eval env = true →
      ∃ res, res ∈ out ∧ res.1.eval env = true ∧
        Executes body (p.2.toState env) (res.2.eval env)
  | 0, st, out, p, _, h, hp, _ => by
    change (if st.2.isEmpty then some st.1 else none) = some out at h
    cases he : st.2.isEmpty with
    | false => rw [he] at h; cases h
    | true =>
      cases st with
      | mk d a =>
        cases a with
        | nil => cases hp
        | cons _ _ => cases he
  | fuel + 1, st, out, p, hWf, h, hpMem, hpEv => by
    change (if st.2.isEmpty then some st.1
      else match symStepAll body st.1 st.2 with
        | none => none
        | some st' => symRunPathsAux body fuel st') = some out at h
    cases he : st.2.isEmpty with
    | true =>
      cases st with
      | mk d a =>
        cases a with
        | nil => cases hpMem
        | cons _ _ => cases he
    | false =>
      rw [he] at h
      cases hStep : symStepAll body st.1 st.2 with
      | none => rw [hStep] at h; cases h
      | some st' =>
        rw [hStep] at h
        cases symStepAll_sound body env st.2 st.1 st' p hWf hStep hpMem hpEv with
        | inl hd =>
          let ⟨v, pc', hMem', hEv', hRet⟩ := hd
          exact ⟨(pc', v),
            symRunPathsAux_preserves_done body fuel st' out (pc', v) h hMem',
            hEv', .ret hRet⟩
        | inr hn =>
          let ⟨q, hqMem, hqEv, hStepQ⟩ := hn
          have hWf' := symStepAll_wf body st.2 st.1 st' hWf hStep
          let ⟨res, hResMem, hResEv, hExec⟩ :=
            symRunPathsAux_sound body env fuel st' out q hWf' h hqMem hqEv
          exact ⟨res, hResMem, hResEv, .next hStepQ hExec⟩

/-- Branched symbolic execution adequacy: if `symRunPaths body fuel pc s = some
paths`, then every `env` satisfying `pc` picks a concrete path `(pc', out) ∈
paths` executing `body` cleanly from `s.toState env` to `out.eval env`. -/
theorem symRunPaths_sound {body : Body} {fuel : Nat} {pc : SymBool}
    {s : SymState} {paths : List (SymBool × SymVal)}
    (hPc : pc.wf = true)
    (h : symRunPaths body fuel pc s = some paths)
    (env : SymEnv) (hEv : pc.eval env = true) :
    ∃ res, res ∈ paths ∧ res.1.eval env = true ∧
      Executes body (s.toState env) (res.2.eval env) :=
  symRunPathsAux_sound body env fuel ([], [(pc, s)]) paths (pc, s)
    (fun q hq => by
      cases hq with
      | head _ => exact hPc
      | tail _ hT => cases hT)
    h (List.Mem.head _) hEv

/-- Derive `BodyVerified` from a branched symbolic execution run across all
covered entry arguments. -/
theorem bodyVerified_of_symRunPaths {p : Program} {defId : DefId} {body : Body}
    {fuel : Nat} {argsTemplate : List SymVal}
    {paths : List (SymBool × SymVal)}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hAdm : BodyStaticAdmitted p body = true)
    (hRun : symRunPaths body fuel (.lit true) (symEntry body argsTemplate) =
      some paths)
    (hCover : ∀ args : List Val, ValidEntryArgs body args →
      (body.isUnsafe = true → True) →
      ∃ env : SymEnv, argsTemplate.map (SymVal.eval env) = args)
    (h_nocall : bodyHasAnyCall body = false := by
      first
      | rfl
      | exact bodyHasAnyCall_false_of_basicBlocks
          ‹Trusted.MirAst.Body.basicBlocks _ = _› rfl
      | exact bodyHasAnyCall_false_of_all
          ‹Trusted.MirSemantics.getElem? _ _ = some _› rfl) :
    BodyVerified p defId body (fun _ => True) := by
  refine bodyVerified_of_safe hBody hAdm (fun args valid _ => ?_) h_nocall
  let ⟨env, hMap⟩ := hCover args valid (fun _ => True.intro)
  let ⟨res, _, _, hExec⟩ := symRunPaths_sound rfl hRun env rfl
  rw [symEntry_toState, hMap] at hExec
  exact executes_safe hExec

/-! ## Part V: Self-Contained Kernel-Checked Canaries -/

@[expose] noncomputable def canaryBodyArithBvLin : Body :=
  { identity := "canary::bvlin_arith_branch"
    isUnsafe := false
    argumentCount := 2
    locals := [.int .i64 false, .int .i64 false, .int .i64 false,
               .int .i64 false, .int .i64 false, .bool]
    basicBlocks :=
      [ { statements :=
            [ .assign { localId := 3, projection := [] }
                (.binaryOp .add (.copy { localId := 1, projection := [] })
                  (.constant { ty := .int .i64 false, lit := .scalar 8 })),
              .assign { localId := 4, projection := [] }
                (.binaryOp .add (.copy { localId := 1, projection := [] })
                  (.constant { ty := .int .i64 false, lit := .scalar 16 })),
              .assign { localId := 5, projection := [] }
                (.binaryOp .eq (.copy { localId := 3, projection := [] })
                  (.copy { localId := 4, projection := [] })) ]
          terminator := .switchInt (.move { localId := 5, projection := [] })
            { branches := [(1, 1)], otherwise := 2 }
          cleanup := false },
        { statements := []
          terminator := .unreachable
          cleanup := false },
        { statements :=
            [ .assign { localId := 0, projection := [] }
                (.binaryOp .sub (.copy { localId := 3, projection := [] })
                  (.copy { localId := 2, projection := [] })) ]
          terminator := .return_
          cleanup := false } ] }

/-- Kernel-checked multi-variable `BvLin` symbolic canary (`rfl`, `["propext"]`
only): `x + 8 == x + 16` is statically refuted by `BvLin` in `symStep` so the
`.unreachable` arm is eliminated and `(x + 8) - y` is returned cleanly. -/
theorem symExec_multiVar_bvLin_canary :
    symRun canaryBodyArithBvLin 16
      (symEntry canaryBodyArithBvLin
        [.scalar (.var 0 .i64 false), .scalar (.var 1 .i64 false)]) =
      .ret (.scalar
        (.binOp .sub
          (.binOp .add (.var 0 .i64 false)
            (.lit ⟨.i64, false, BitVec.ofNat 128 8⟩))
          (.var 1 .i64 false))) := rfl

@[expose] noncomputable def canaryBodyBranchCast : Body :=
  { identity := "canary::branch_cast"
    isUnsafe := false
    argumentCount := 2
    locals := [.int .i64 false, .bool, .int .i32 false]
    basicBlocks :=
      [ { statements := []
          terminator := .switchInt (.copy { localId := 1, projection := [] })
            { branches := [(0, 2)], otherwise := 1 }
          cleanup := false },
        { statements :=
            [ .assign { localId := 0, projection := [] }
                (.cast .intToInt (.copy { localId := 2, projection := [] })
                  (.int .i64 false)) ]
          terminator := .return_
          cleanup := false },
        { statements :=
            [ .assign { localId := 0, projection := [] }
                (.use (.constant { ty := .int .i64 false, lit := .scalar 42 })) ]
          terminator := .return_
          cleanup := false } ] }

/-- Kernel-checked branched symbolic execution canary (`rfl`, `["propext"]`
only): exercises symbolic boolean `switchInt` + `u32 as u64` cast across all
paths and lifts directly to `Executes`. -/
theorem symExec_branch_and_cast_canary (flag : Bool) (n : BitVec 32) :
    let args := [.bool flag, .scalar ⟨.i32, false, BitVec.ofNat 128 n.toNat⟩]
    Executes canaryBodyBranchCast
      (mkState 0 0 (initLocalsLoop canaryBodyBranchCast args 0
        canaryBodyBranchCast.locals))
      (if flag then .scalar ⟨.i64, false, BitVec.ofNat 128 n.toNat⟩
       else .scalar ⟨.i64, false, BitVec.ofNat 128 42⟩) := by
  let env : SymEnv := fun i =>
    if Nat.beq i 0 then .bool flag
    else .scalar ⟨.i32, false, BitVec.ofNat 128 n.toNat⟩
  have hMod128 : Nat.mod n.toNat (Nat.pow 2 128) = n.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_trans n.isLt (by decide))
  have hTrunc32 :
      truncateBitsComp .i32 (BitVec.ofNat 128 n.toNat) =
        BitVec.ofNat 128 n.toNat :=
    truncateBitsComp_bitVec_of_lt n (by decide)
  have hTrunc64 :
      truncateBitsComp .i64 (BitVec.ofNat 128 n.toNat) =
        BitVec.ofNat 128 n.toNat :=
    truncateBitsComp_bitVec_of_lt n (by decide)
  have hEq0 : Nat.beq 0 0 = true := rfl
  have hEq1 : Nat.beq 1 0 = false := rfl
  have hArgs :
      ([.bool (.var 0), .scalar (.var 1 .i32 false)] : List SymVal).map
          (SymVal.eval env) =
        [.bool flag, .scalar ⟨.i32, false, BitVec.ofNat 128 n.toNat⟩] := by
    dsimp only [List.map, SymVal.eval, SymBool.eval, SymScalar.eval, env]
    rw [hEq0, hEq1, ite_bool_true, ite_bool_false]
    dsimp only
    rw [hTrunc32]
  have hPaths :
      symRunPaths canaryBodyBranchCast 16 (.lit true)
        (symEntry canaryBodyBranchCast
          [.bool (.var 0), .scalar (.var 1 .i32 false)]) =
        some [(.var 0, .scalar (.cast .i64 false (.var 1 .i32 false))),
              (.not (.var 0), .conc (.scalar ⟨.i64, false, BitVec.ofNat 128 42⟩))] := rfl
  let ⟨res, hMem, hResEv, hExec⟩ := symRunPaths_sound rfl hPaths env rfl
  rw [symEntry_toState, hArgs] at hExec
  cases hMem with
  | head _ =>
    dsimp only [SymBool.eval, env] at hResEv
    cases flag with
    | false => cases hResEv
    | true =>
      dsimp only [SymVal.eval, SymScalar.eval, evalIntToIntCastComp,
        intLikeBitsComp, env] at hExec
      rw [hEq1, ite_bool_false] at hExec
      dsimp only at hExec
      rw [ite_bool_false] at hExec
      dsimp only at hExec
      rw [hTrunc32, hTrunc32] at hExec
      have hToNat : (BitVec.ofNat 128 n.toNat).toNat = n.toNat := by
        rw [bv_toNat_ofNat, hMod128]
      rw [hToNat, hTrunc64] at hExec
      rw [ite_bool_true]
      exact hExec
  | tail _ hTail =>
    cases hTail with
    | head _ =>
      dsimp only [SymBool.eval, env] at hResEv
      cases flag with
      | true => cases hResEv
      | false =>
        rw [ite_bool_false]
        exact hExec
    | tail _ hNil => cases hNil

/-! ### Step-Chunked Canary: `parity_even`

`canaryBodyParityEven` is the MIR that `anneal-rustc-capture` emits for

```rust
#![no_std]
pub fn parity_even(mut b: u8) -> bool {
    b ^= b >> 4;
    b ^= b >> 2;
    b ^= b >> 1;
    (b & 1) == 0
}
```

(edition 2021, no overflow checks), transcribed with the same statements in
the same order. Its 28 statements and `return` take 29 steps. A single
`symRun` over all of them exceeds the default `maxHeartbeats`; four chunks of
at most 8 steps each check quickly. -/

@[expose] noncomputable def canaryBodyParityEven : Body :=
  { identity := "rust-path-v1::parity_even"
    isUnsafe := false
    argumentCount := 1
    locals := [.bool, .int .i8 false, .int .i8 false, .int .i8 false,
               .int .i8 false, .int .i8 false, .int .i8 false, .int .i8 false,
               .int .i8 false, .int .i8 false]
    basicBlocks :=
      [ { statements :=
            [ .storageLive 2,
              .storageLive 3,
              .assign { localId := 3, projection := [] }
                (.use (.copy { localId := 1, projection := [] })),
              .assign { localId := 2, projection := [] }
                (.binaryOp .shr (.move { localId := 3, projection := [] })
                  (.constant { ty := .int .i32 true, lit := .scalar 4 })),
              .storageDead 3,
              .assign { localId := 1, projection := [] }
                (.binaryOp .bitXor (.copy { localId := 1, projection := [] })
                  (.move { localId := 2, projection := [] })),
              .storageDead 2,
              .storageLive 4,
              .storageLive 5,
              .assign { localId := 5, projection := [] }
                (.use (.copy { localId := 1, projection := [] })),
              .assign { localId := 4, projection := [] }
                (.binaryOp .shr (.move { localId := 5, projection := [] })
                  (.constant { ty := .int .i32 true, lit := .scalar 2 })),
              .storageDead 5,
              .assign { localId := 1, projection := [] }
                (.binaryOp .bitXor (.copy { localId := 1, projection := [] })
                  (.move { localId := 4, projection := [] })),
              .storageDead 4,
              .storageLive 6,
              .storageLive 7,
              .assign { localId := 7, projection := [] }
                (.use (.copy { localId := 1, projection := [] })),
              .assign { localId := 6, projection := [] }
                (.binaryOp .shr (.move { localId := 7, projection := [] })
                  (.constant { ty := .int .i32 true, lit := .scalar 1 })),
              .storageDead 7,
              .assign { localId := 1, projection := [] }
                (.binaryOp .bitXor (.copy { localId := 1, projection := [] })
                  (.move { localId := 6, projection := [] })),
              .storageDead 6,
              .storageLive 8,
              .storageLive 9,
              .assign { localId := 9, projection := [] }
                (.use (.copy { localId := 1, projection := [] })),
              .assign { localId := 8, projection := [] }
                (.binaryOp .bitAnd (.move { localId := 9, projection := [] })
                  (.constant { ty := .int .i8 false, lit := .scalar 1 })),
              .storageDead 9,
              .assign { localId := 0, projection := [] }
                (.binaryOp .eq (.move { localId := 8, projection := [] })
                  (.constant { ty := .int .i8 false, lit := .scalar 0 })),
              .storageDead 8 ]
          terminator := .return_
          cleanup := false } ] }

/-- The captured single-body program around `canaryBodyParityEven`. -/
@[expose] noncomputable def canaryProgParityEven : Program :=
  { pointerWidthBits := 64
    mirProfileVersion := 1
    scope := .unit
    entryDefId := 0
    bodies := [canaryBodyParityEven]
    overflowChecks := false
    panicStrategy := .unwind
    hasLocalPanicHandler := false }

/-- Symbolic `b ^ (b >> k)` with the `i32` shift amount rustc emits. -/
@[expose] noncomputable def paritySymFold (b : SymScalar) (k : Nat) :
    SymScalar :=
  .binOp .bitXor b (.shift .shr b (.lit ⟨.i32, true, BitVec.ofNat 128 k⟩))

/-- Checkpoint state between the three `b ^= b >> k` rounds: only `b` (local
`1`) holds a value, and every temporary is dead. -/
@[expose] noncomputable def paritySymState (stmt : Nat) (b : SymScalar) :
    SymState :=
  { block := 0, stmt := stmt,
    slots := [.immediate none, .immediate (some (.scalar b)), .dead, .dead,
              .dead, .dead, .dead, .dead, .dead, .dead] }

/-- The symbolic argument `b`. -/
@[expose] noncomputable def paritySymIn : SymScalar := .var 0 .i8 false

/-- The symbolic return value `(b & 1) == 0` after the three rounds. -/
@[expose] noncomputable def paritySymOut : SymBool :=
  .cmp .eq
    (.binOp .bitAnd
      (paritySymFold (paritySymFold (paritySymFold paritySymIn 4) 2) 1)
      (.lit ⟨.i8, false, BitVec.ofNat 128 1⟩))
    (.lit ⟨.i8, false, BitVec.ofNat 128 0⟩)

theorem parityEven_chunk1 :
    symRunSteps canaryBodyParityEven 7
        (symEntry canaryBodyParityEven [.scalar paritySymIn]) =
      .step (paritySymState 7 (paritySymFold paritySymIn 4)) := rfl

theorem parityEven_chunk2 :
    symRunSteps canaryBodyParityEven 7
        (paritySymState 7 (paritySymFold paritySymIn 4)) =
      .step (paritySymState 14
        (paritySymFold (paritySymFold paritySymIn 4) 2)) := rfl

theorem parityEven_chunk3 :
    symRunSteps canaryBodyParityEven 7
        (paritySymState 14 (paritySymFold (paritySymFold paritySymIn 4) 2)) =
      .step (paritySymState 21
        (paritySymFold (paritySymFold (paritySymFold paritySymIn 4) 2) 1)) :=
  rfl

theorem parityEven_chunk4 :
    symRunSteps canaryBodyParityEven 8
        (paritySymState 21
          (paritySymFold (paritySymFold (paritySymFold paritySymIn 4) 2) 1)) =
      .ret (.bool paritySymOut) := rfl

/-- Kernel-checked step-chunked canary (`["propext"]` only, default
`maxHeartbeats`): the whole captured `parity_even` body returns
`paritySymOut`. -/
theorem symExec_parityEven_canary :
    symRunSteps canaryBodyParityEven 29
        (symEntry canaryBodyParityEven [.scalar paritySymIn]) =
      .ret (.bool paritySymOut) :=
  (symRunSteps_add _ 7 22 _).trans (by
    rw [parityEven_chunk1]
    exact (symRunSteps_add _ 7 15 _).trans (by
      rw [parityEven_chunk2]
      exact (symRunSteps_add _ 7 8 _).trans (by
        rw [parityEven_chunk3]
        exact parityEven_chunk4)))

/-- Number of set bits among the low `fuel` bits of `n`. -/
@[expose] noncomputable def natPopcount (fuel n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih m => Nat.mod m 2 + ih (Nat.div m 2)) fuel n

/-- Whether `f i` holds for every `i` with `lo ≤ i < lo + len`. -/
@[expose] noncomputable def natAllFrom (lo len : Nat) (f : Nat → Bool) : Bool :=
  @Nat.rec (fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih i => f i && ih (i + 1)) len lo

theorem natAllFrom_sound {f : Nat → Bool} :
    ∀ {len lo : Nat}, natAllFrom lo len f = true →
      ∀ {i : Nat}, lo ≤ i → i < lo + len → f i = true
  | 0, lo, _, _, hle, hlt =>
    absurd (Nat.lt_of_le_of_lt hle hlt) (Nat.lt_irrefl lo)
  | len + 1, lo, h, i, hle, hlt => by
    change (f lo && natAllFrom (lo + 1) len f) = true at h
    cases hf : f lo with
    | false => rw [hf] at h; cases h
    | true =>
      rw [hf] at h
      cases Nat.eq_or_lt_of_le hle with
      | inl hEq => rw [← hEq]; exact hf
      | inr hLo =>
        exact natAllFrom_sound h (Nat.succ_le_of_lt hLo)
          (Nat.succ_add lo len ▸ hlt)

/-- Valuation binding the symbolic argument to the `u8` value `n`. -/
@[expose] noncomputable def parityEnv (n : Nat) : SymEnv :=
  fun _ => .scalar ⟨.i8, false, BitVec.ofNat 128 n⟩

/-- Specification: `n` has an even number of set bits in its low byte. -/
@[expose] noncomputable def parityEvenSpec (n : Nat) : Bool :=
  Nat.beq (Nat.mod (natPopcount 8 n) 2) 0

/-- Whether `paritySymOut` meets `parityEvenSpec` at the input `n`. -/
@[expose] noncomputable def parityCheck (n : Nat) : Bool :=
  decide (paritySymOut.eval (parityEnv n) = parityEvenSpec n)

-- Four checks of 64 inputs each: one check over all 256 inputs exceeds the
-- default `maxRecDepth`.
theorem parityCheck_0 : natAllFrom 0 64 parityCheck = true := rfl
theorem parityCheck_64 : natAllFrom 64 64 parityCheck = true := rfl
theorem parityCheck_128 : natAllFrom 128 64 parityCheck = true := rfl
theorem parityCheck_192 : natAllFrom 192 64 parityCheck = true := rfl

/-- `paritySymOut` meets `parityEvenSpec` at every `u8` input (exhaustive). -/
theorem paritySymOut_eval {n : Nat} (hn : n < 256) :
    paritySymOut.eval (parityEnv n) = parityEvenSpec n := by
  have hChk : parityCheck n = true := by
    cases Nat.lt_or_ge n 128 with
    | inl h128 =>
      cases Nat.lt_or_ge n 64 with
      | inl h64 => exact natAllFrom_sound parityCheck_0 (Nat.zero_le n) h64
      | inr h64 => exact natAllFrom_sound parityCheck_64 h64 h128
    | inr h128 =>
      cases Nat.lt_or_ge n 192 with
      | inl h192 => exact natAllFrom_sound parityCheck_128 h128 h192
      | inr h192 => exact natAllFrom_sound parityCheck_192 h192 hn
  exact of_decide_eq_true hChk

/-- End-to-end functional correctness of the captured `parity_even`
(`["propext"]` only): for every `b : u8`, the program returns `true` exactly
when `b` has an even number of set bits. -/
theorem parityEven_behavior (b : BitVec 8) :
    Trusted.MirSemantics.Behavior (entryProgForBody canaryProgParityEven 0)
      { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩] }
      (.returned ⟨.bool (parityEvenSpec b.toNat), ⟨[]⟩⟩) := by
  have hLt : b.toNat < 256 := b.isLt
  have hTrunc :
      truncateBitsComp .i8 (BitVec.ofNat 128 b.toNat) =
        BitVec.ofNat 128 b.toNat :=
    truncateBitsComp_bitVec_of_lt b (by decide)
  have hArgs :
      ([.scalar paritySymIn] : List SymVal).map
          (SymVal.eval (parityEnv b.toNat)) =
        [.scalar ⟨.i8, false, BitVec.ofNat 128 b.toNat⟩] := by
    dsimp only [List.map, SymVal.eval, SymScalar.eval, paritySymIn, parityEnv]
    rw [hTrunc]
  have hValid :
      ValidEntryArgs canaryBodyParityEven
        (([.scalar paritySymIn] : List SymVal).map
          (SymVal.eval (parityEnv b.toNat))) := by
    rw [hArgs]
    have hBits :
        (BitVec.ofNat 128 b.toNat).toNat < intWidthModulus .i8 := by
      rw [bv_toNat_ofNat]
      exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) hLt
    exact checkArgsMatch_cons_iff.mpr
      ⟨_, [], rfl, checkVal_scalar_of_toNat_lt hBits, rfl⟩
  have hB := symRunSteps_entry_behavior (p := canaryProgParityEven)
    (defId := 0) rfl rfl (parityEnv b.toNat) hValid symExec_parityEven_canary
  rw [hArgs] at hB
  have hOut : (SymVal.bool paritySymOut).eval (parityEnv b.toNat) =
      .bool (parityEvenSpec b.toNat) :=
    congrArg Val.bool (paritySymOut_eval hLt)
  rw [hOut] at hB
  exact hB.2.2.1

end Anneal.MirSymExec

end
