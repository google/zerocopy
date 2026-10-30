-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module

public import Std.Tactic.BVDecide
public meta import Lean.Elab.Tactic.BVDecide
public meta import Lean.Meta.Tactic.Grind.Main

@[expose] public section

/-!
# Standalone Core-Lean VC Tactic Benchmark Probe (`Classes A–E`)

Self-contained Lean `v4.34.1` verification condition (VC) probe covering all 14
representative Anneal MIR verification obligations (`A1`–`A3`, `B1`–`B3`,
`C1`–`C2`, `D1`–`D3`, `E1`–`E4`) using core Lean tactics (`omega`, `grind`,
`bv_decide`, `bv_decide_kernel`, and `refine ⟨_, rfl, ...⟩`).

Compile standalone under a 1 GiB memory cap with:
```bash
lean -j1 -M1024 support/CoreVCTacticBenchmarkProbe.lean
```
-/

namespace KernelBVDecide

open Std.Tactic.BVDecide

structure BVar where
  bit : Nat
  var : Nat
  deriving DecidableEq, Repr

def BVar.gt (a b : BVar) : Bool :=
  if a.bit == b.bit then a.var > b.var else a.bit > b.bit

inductive BDD where
  | leaf (b : Bool)
  | node (var : BVar) (low high : BDD)
  deriving DecidableEq, Repr

@[inline]
def mkNode (v : BVar) (low high : BDD) : BDD :=
  if low == high then low else .node v low high

def bddNot : BDD → BDD
  | .leaf b => .leaf (!b)
  | .node v l h => .node v (bddNot l) (bddNot h)

def bddAndNode (va : BVar) (la ha : BDD) (andLa andHa : BDD → BDD) : BDD → BDD
  | .leaf false => .leaf false
  | .leaf true => .node va la ha
  | .node vb lb hb =>
    if va == vb then
      mkNode va (andLa lb) (andHa hb)
    else if va.gt vb then
      mkNode va (andLa (.node vb lb hb)) (andHa (.node vb lb hb))
    else
      mkNode vb (bddAndNode va la ha andLa andHa lb)
                (bddAndNode va la ha andLa andHa hb)

def bddAnd : BDD → BDD → BDD
  | .leaf false, _ => .leaf false
  | .leaf true, b => b
  | .node va la ha, b => bddAndNode va la ha (bddAnd la) (bddAnd ha) b

def bddOrNode (va : BVar) (la ha : BDD) (orLa orHa : BDD → BDD) : BDD → BDD
  | .leaf true => .leaf true
  | .leaf false => .node va la ha
  | .node vb lb hb =>
    if va == vb then
      mkNode va (orLa lb) (orHa hb)
    else if va.gt vb then
      mkNode va (orLa (.node vb lb hb)) (orHa (.node vb lb hb))
    else
      mkNode vb (bddOrNode va la ha orLa orHa lb)
                (bddOrNode va la ha orLa orHa hb)

def bddOr : BDD → BDD → BDD
  | .leaf true, _ => .leaf true
  | .leaf false, b => b
  | .node va la ha, b => bddOrNode va la ha (bddOr la) (bddOr ha) b

def bddXorNode (va : BVar) (la ha : BDD) (xorLa xorHa : BDD → BDD) : BDD → BDD
  | .leaf false => .node va la ha
  | .leaf true => bddNot (.node va la ha)
  | .node vb lb hb =>
    if va == vb then
      mkNode va (xorLa lb) (xorHa hb)
    else if va.gt vb then
      mkNode va (xorLa (.node vb lb hb)) (xorHa (.node vb lb hb))
    else
      mkNode vb (bddXorNode va la ha xorLa xorHa lb)
                (bddXorNode va la ha xorLa xorHa hb)

def bddXor : BDD → BDD → BDD
  | .leaf false, b => b
  | .leaf true, b => bddNot b
  | .node va la ha, b => bddXorNode va la ha (bddXor la) (bddXor ha) b

def bddBeq (a b : BDD) : BDD := bddNot (bddXor a b)

def bddAtLeastTwo (a b c : BDD) : BDD :=
  bddOr (bddAnd a b) (bddAnd (bddXor a b) c)

def bddVar (v : Nat) (i : Nat) : BDD :=
  if v == 1 then
    bddXor (.node ⟨i, 0⟩ (.leaf false) (.leaf true))
           (.node ⟨i, 1⟩ (.leaf false) (.leaf true))
  else
    .node ⟨i, v⟩ (.leaf false) (.leaf true)

def BDD.eval (f : BVar → Bool) : BDD → Bool
  | .leaf b => b
  | .node v low high => bif f v then high.eval f else low.eval f

theorem eval_mkNode (f : BVar → Bool) (v : BVar) (low high : BDD) :
    (mkNode v low high).eval f = (bif f v then high.eval f else low.eval f) := by
  unfold mkNode
  split
  next h =>
    have heq : low = high := LawfulBEq.eq_of_beq h
    subst heq
    cases f v <;> rfl
  next => rfl

@[simp]
theorem eval_bddNot (f : BVar → Bool) (a : BDD) : (bddNot a).eval f = !(a.eval f) := by
  induction a with
  | leaf b => rfl
  | node v l h ihl ihh =>
    simp only [bddNot, BDD.eval, ihl, ihh]
    cases f v <;> rfl

theorem eval_bddAndNode (f : BVar → Bool) (va : BVar) (la ha : BDD) (andLa andHa : BDD → BDD)
    (hla : ∀ x, (andLa x).eval f = (la.eval f && x.eval f))
    (hha : ∀ x, (andHa x).eval f = (ha.eval f && x.eval f))
    (b : BDD) :
    (bddAndNode va la ha andLa andHa b).eval f = ((BDD.node va la ha).eval f && b.eval f) := by
  induction b with
  | leaf bb =>
    cases bb <;> simp [bddAndNode, BDD.eval]
  | node vb lb hb ihlb ihhb =>
    simp only [bddAndNode]
    split
    next heq =>
      have hv : va = vb := LawfulBEq.eq_of_beq heq
      subst hv
      rw [eval_mkNode, hla, hha]
      simp only [BDD.eval]
      cases f va <;> rfl
    next =>
      split
      next =>
        rw [eval_mkNode, hla, hha]
        simp only [BDD.eval]
        cases f va <;> rfl
      next =>
        rw [eval_mkNode, ihlb, ihhb]
        simp only [BDD.eval]
        cases f va <;> cases f vb <;> rfl

@[simp]
theorem eval_bddAnd (f : BVar → Bool) (a b : BDD) :
    (bddAnd a b).eval f = (a.eval f && b.eval f) := by
  induction a generalizing b with
  | leaf ba =>
    cases ba <;> simp [bddAnd, BDD.eval]
  | node va la ha ihla ihha =>
    exact eval_bddAndNode f va la ha (bddAnd la) (bddAnd ha) ihla ihha b

theorem eval_bddOrNode (f : BVar → Bool) (va : BVar) (la ha : BDD) (orLa orHa : BDD → BDD)
    (hla : ∀ x, (orLa x).eval f = (la.eval f || x.eval f))
    (hha : ∀ x, (orHa x).eval f = (ha.eval f || x.eval f))
    (b : BDD) :
    (bddOrNode va la ha orLa orHa b).eval f = ((BDD.node va la ha).eval f || b.eval f) := by
  induction b with
  | leaf bb =>
    cases bb <;> simp [bddOrNode, BDD.eval]
  | node vb lb hb ihlb ihhb =>
    simp only [bddOrNode]
    split
    next heq =>
      have hv : va = vb := LawfulBEq.eq_of_beq heq
      subst hv
      rw [eval_mkNode, hla, hha]
      simp only [BDD.eval]
      cases f va <;> rfl
    next =>
      split
      next =>
        rw [eval_mkNode, hla, hha]
        simp only [BDD.eval]
        cases f va <;> rfl
      next =>
        rw [eval_mkNode, ihlb, ihhb]
        simp only [BDD.eval]
        cases f va <;> cases f vb <;> rfl

@[simp]
theorem eval_bddOr (f : BVar → Bool) (a b : BDD) :
    (bddOr a b).eval f = (a.eval f || b.eval f) := by
  induction a generalizing b with
  | leaf ba =>
    cases ba <;> simp [bddOr, BDD.eval]
  | node va la ha ihla ihha =>
    exact eval_bddOrNode f va la ha (bddOr la) (bddOr ha) ihla ihha b

theorem eval_bddXorNode (f : BVar → Bool) (va : BVar) (la ha : BDD) (xorLa xorHa : BDD → BDD)
    (hla : ∀ x, (xorLa x).eval f = (la.eval f ^^ x.eval f))
    (hha : ∀ x, (xorHa x).eval f = (ha.eval f ^^ x.eval f))
    (b : BDD) :
    (bddXorNode va la ha xorLa xorHa b).eval f = ((BDD.node va la ha).eval f ^^ b.eval f) := by
  induction b with
  | leaf bb =>
    cases bb <;> simp [bddXorNode, BDD.eval]
  | node vb lb hb ihlb ihhb =>
    simp only [bddXorNode]
    split
    next heq =>
      have hv : va = vb := LawfulBEq.eq_of_beq heq
      subst hv
      rw [eval_mkNode, hla, hha]
      simp only [BDD.eval]
      cases f va <;> rfl
    next =>
      split
      next =>
        rw [eval_mkNode, hla, hha]
        simp only [BDD.eval]
        cases f va <;> rfl
      next =>
        rw [eval_mkNode, ihlb, ihhb]
        simp only [BDD.eval]
        cases f va <;> cases f vb <;> rfl

@[simp]
theorem eval_bddXor (f : BVar → Bool) (a b : BDD) :
    (bddXor a b).eval f = (a.eval f ^^ b.eval f) := by
  induction a generalizing b with
  | leaf ba =>
    cases ba <;> simp [bddXor, BDD.eval]
  | node va la ha ihla ihha =>
    exact eval_bddXorNode f va la ha (bddXor la) (bddXor ha) ihla ihha b

@[simp]
theorem eval_bddBeq (f : BVar → Bool) (a b : BDD) :
    (bddBeq a b).eval f = (a.eval f == b.eval f) := by
  simp only [bddBeq, eval_bddNot, eval_bddXor]
  cases a.eval f <;> cases b.eval f <;> rfl

@[simp]
theorem eval_bddAtLeastTwo (f : BVar → Bool) (a b c : BDD) :
    (bddAtLeastTwo a b c).eval f = Bool.atLeastTwo (a.eval f) (b.eval f) (c.eval f) := by
  simp only [bddAtLeastTwo, eval_bddOr, eval_bddAnd, eval_bddXor, Bool.atLeastTwo]
  cases a.eval f <;> cases b.eval f <;> cases c.eval f <;> rfl

def assignToBDDEnv (assign : BVExpr.Assignment) (bv : BVar) : Bool :=
  if bv.var == 1 then
    (assign.get 0).bv.getLsbD bv.bit ^^ (assign.get 1).bv.getLsbD bv.bit
  else
    (assign.get bv.var).bv.getLsbD bv.bit

@[simp]
theorem eval_bddVar (assign : BVExpr.Assignment) (v i : Nat) :
    (bddVar v i).eval (assignToBDDEnv assign) = (assign.get v).bv.getLsbD i := by
  unfold bddVar
  split
  next hv =>
    have hv1 : v = 1 := LawfulBEq.eq_of_beq hv
    subst hv1
    simp only [eval_bddXor, BDD.eval, assignToBDDEnv]
    have h0 : (0 == 1) = false := rfl
    have h1 : (1 == 1) = true := rfl
    simp only [h0, h1, ↓reduceIte]
    cases (assign.get 0).bv.getLsbD i <;> cases (assign.get 1).bv.getLsbD i <;> rfl
  next hv =>
    simp only [BDD.eval, assignToBDDEnv, hv]
    cases (assign.get v).bv.getLsbD i <;> rfl

def getBit : List BDD → Nat → BDD
  | [], _ => .leaf false
  | x :: _, 0 => x
  | _ :: xs, i + 1 => getBit xs i

def ofBitFn : Nat → (Nat → BDD) → List BDD
  | 0, _ => []
  | w + 1, g => g 0 :: ofBitFn w (fun i => g (i + 1))

theorem getBit_ofBitFn (w : Nat) (g : Nat → BDD) (i : Nat) :
    getBit (ofBitFn w g) i = if i < w then g i else .leaf false := by
  induction w generalizing g i with
  | zero =>
    simp [ofBitFn, getBit]
  | succ w ih =>
    cases i with
    | zero =>
      simp [ofBitFn, getBit]
    | succ i =>
      simp only [ofBitFn, getBit, ih, Nat.succ_lt_succ_iff]

def carryLoop (bl br : List BDD) (c : Bool) : Nat → BDD
  | 0 => .leaf c
  | k + 1 => bddAtLeastTwo (getBit bl k) (getBit br k) (carryLoop bl br c k)

theorem eval_carryLoop (f : BVar → Bool) (bl br : List BDD) (xl xr : BitVec w) (c : Bool)
    (hl : ∀ k, (getBit bl k).eval f = xl.getLsbD k)
    (hr : ∀ k, (getBit br k).eval f = xr.getLsbD k)
    (i : Nat) :
    (carryLoop bl br c i).eval f = BitVec.carry i xl xr c := by
  induction i with
  | zero =>
    simp [carryLoop, BDD.eval, BitVec.carry_zero]
  | succ k ih =>
    simp only [carryLoop, eval_bddAtLeastTwo, hl, hr, ih, BitVec.carry_succ]

theorem eval_ofBitFn_eq (f : BVar → Bool) (w : Nat) (g : Nat → BDD) (bv : BitVec w)
    (h : ∀ i, i < w → (g i).eval f = bv.getLsbD i) (i : Nat) :
    (getBit (ofBitFn w g) i).eval f = bv.getLsbD i := by
  rw [getBit_ofBitFn]
  split
  next hi => exact h i hi
  next hi =>
    have hge : w ≤ i := Nat.le_of_not_lt hi
    simp [BDD.eval, BitVec.getLsbD_of_ge bv i hge]

def eqLoop (bl br : List BDD) : Nat → BDD
  | 0 => .leaf true
  | k + 1 => bddAnd (eqLoop bl br k) (bddBeq (getBit bl k) (getBit br k))

theorem eval_eqLoop_iff (f : BVar → Bool) (bl br : List BDD) (xl xr : BitVec w)
    (hl : ∀ k, (getBit bl k).eval f = xl.getLsbD k)
    (hr : ∀ k, (getBit br k).eval f = xr.getLsbD k)
    (n : Nat) :
    ((eqLoop bl br n).eval f = true) ↔ (∀ k < n, xl.getLsbD k = xr.getLsbD k) := by
  induction n with
  | zero =>
    simp [eqLoop, BDD.eval]
  | succ n ih =>
    simp only [eqLoop, eval_bddAnd, eval_bddBeq, hl, hr, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | rfl
      · exact h1 k hlt
      · exact h2
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩

theorem eval_eqLoop (f : BVar → Bool) (bl br : List BDD) (xl xr : BitVec w)
    (hl : ∀ k, (getBit bl k).eval f = xl.getLsbD k)
    (hr : ∀ k, (getBit br k).eval f = xr.getLsbD k) :
    (eqLoop bl br w).eval f = (xl == xr) := by
  apply Bool.eq_iff_iff.mpr
  rw [eval_eqLoop_iff f bl br xl xr hl hr w, beq_iff_eq]
  constructor
  · intro h
    exact BitVec.eq_of_getLsbD_eq h
  · rintro rfl _ _
    rfl

def blastExpr : BVExpr w → Option (List BDD)
  | .var v =>
    some (ofBitFn w (fun i => bddVar v i))
  | .const val =>
    some (ofBitFn w (fun i => .leaf (val.getLsbD i)))
  | .extract start len expr =>
    match blastExpr expr with
    | some b => some (ofBitFn len (fun i => getBit b (start + i)))
    | none => none
  | .append (l := _l) (r := r) lhs rhs _ =>
    match blastExpr lhs, blastExpr rhs with
    | some bl, some br =>
      some (ofBitFn w (fun i => if i < r then getBit br i else getBit bl (i - r)))
    | _, _ => none
  | .un .not operand =>
    match blastExpr operand with
    | some b => some (ofBitFn w (fun i => bddNot (getBit b i)))
    | none => none
  | .bin lhs .and rhs =>
    match blastExpr lhs, blastExpr rhs with
    | some bl, some br => some (ofBitFn w (fun i => bddAnd (getBit bl i) (getBit br i)))
    | _, _ => none
  | .bin lhs .or rhs =>
    match blastExpr lhs, blastExpr rhs with
    | some bl, some br => some (ofBitFn w (fun i => bddOr (getBit bl i) (getBit br i)))
    | _, _ => none
  | .bin lhs .xor rhs =>
    match blastExpr lhs, blastExpr rhs with
    | some bl, some br => some (ofBitFn w (fun i => bddXor (getBit bl i) (getBit br i)))
    | _, _ => none
  | .bin lhs .add rhs =>
    match blastExpr lhs, blastExpr rhs with
    | some bl, some br =>
      some (ofBitFn w (fun i => bddXor (bddXor (getBit bl i) (getBit br i)) (carryLoop bl br false i)))
    | _, _ => none
  | _ => none

theorem eval_blastExpr (assign : BVExpr.Assignment) (e : BVExpr w) (bits : List BDD)
    (h : blastExpr e = some bits) (i : Nat) :
    (getBit bits i).eval (assignToBDDEnv assign) = (e.eval assign).getLsbD i := by
  induction e generalizing bits i with
  | var v =>
    simp only [blastExpr, Option.some.injEq] at h
    subst h
    apply eval_ofBitFn_eq
    intro k hk
    simp [eval_bddVar, hk]
  | const val =>
    simp only [blastExpr, Option.some.injEq] at h
    subst h
    apply eval_ofBitFn_eq
    intro k _
    rfl
  | extract start len expr ih =>
    simp only [blastExpr] at h
    split at h
    next b hb =>
      simp only [Option.some.injEq] at h
      subst h
      apply eval_ofBitFn_eq
      intro k hk
      simp [ih b hb (start + k), hk]
    next => contradiction
  | append lhs rhs heq ihl ihr =>
    simp only [blastExpr] at h
    split at h
    next bl br hbl hbr =>
      simp only [Option.some.injEq] at h
      subst h
      subst heq
      apply eval_ofBitFn_eq
      intro k hk
      simp only [BVExpr.eval_append, BitVec.getLsbD_append]
      split
      next hkr =>
        simp [hkr, ihr br hbr k]
      next =>
        simp [ihl bl hbl (k - _)]
    next => contradiction
  | un op operand ih =>
    cases op with
    | not =>
      simp only [blastExpr] at h
      split at h
      next b hb =>
        simp only [Option.some.injEq] at h
        subst h
        apply eval_ofBitFn_eq
        intro k hk
        simp [ih b hb k, hk]
      next => contradiction
    | _ => simp [blastExpr] at h
  | bin lhs op rhs ihl ihr =>
    cases op with
    | and =>
      simp only [blastExpr] at h
      split at h
      next bl br hbl hbr =>
        simp only [Option.some.injEq] at h
        subst h
        apply eval_ofBitFn_eq
        intro k _
        simp [ihl bl hbl k, ihr br hbr k]
      next => contradiction
    | or =>
      simp only [blastExpr] at h
      split at h
      next bl br hbl hbr =>
        simp only [Option.some.injEq] at h
        subst h
        apply eval_ofBitFn_eq
        intro k _
        simp [ihl bl hbl k, ihr br hbr k]
      next => contradiction
    | xor =>
      simp only [blastExpr] at h
      split at h
      next bl br hbl hbr =>
        simp only [Option.some.injEq] at h
        subst h
        apply eval_ofBitFn_eq
        intro k _
        simp [ihl bl hbl k, ihr br hbr k]
      next => contradiction
    | add =>
      simp only [blastExpr] at h
      split at h
      next bl br hbl hbr =>
        simp only [Option.some.injEq] at h
        subst h
        apply eval_ofBitFn_eq
        intro k hk
        rw [eval_bddXor, eval_bddXor, ihl bl hbl k, ihr br hbr k,
            eval_carryLoop (assignToBDDEnv assign) bl br (lhs.eval assign) (rhs.eval assign) false
              (ihl bl hbl) (ihr br hbr) k]
        simp only [BVExpr.eval_bin, BVBinOp.eval_add, BitVec.getLsbD_add hk, Bool.bne_assoc]
      next => contradiction
    | _ => simp [blastExpr] at h
  | _ => simp [blastExpr] at h

def blastPred : BVPred → Option BDD
  | .getLsbD expr idx =>
    match blastExpr expr with
    | some b => some (getBit b idx)
    | none => none
  | .bin (w := w) lhs .eq rhs =>
    match blastExpr lhs, blastExpr rhs with
    | some bl, some br => some (eqLoop bl br w)
    | _, _ => none
  | .bin (w := w) lhs .ult rhs =>
    match blastExpr lhs, blastExpr rhs with
    | some bl, some br =>
      let brNot := ofBitFn w (fun i => bddNot (getBit br i))
      some (bddNot (carryLoop bl brNot true w))
    | _, _ => none

theorem eval_blastPred (assign : BVExpr.Assignment) (p : BVPred) (bdd : BDD)
    (h : blastPred p = some bdd) :
    bdd.eval (assignToBDDEnv assign) = p.eval assign := by
  cases p with
  | getLsbD expr idx =>
    simp only [blastPred] at h
    split at h
    next b hb =>
      simp only [Option.some.injEq] at h
      subst h
      simp [BVPred.eval_getLsbD, eval_blastExpr assign expr b hb idx]
    next => contradiction
  | bin lhs op rhs =>
    rename_i w
    cases op with
    | eq =>
      simp only [blastPred] at h
      split at h
      next bl br hbl hbr =>
        simp only [Option.some.injEq] at h
        subst h
        simp only [BVPred.eval_bin, BVBinPred.eval_eq]
        exact eval_eqLoop (assignToBDDEnv assign) bl br (lhs.eval assign) (rhs.eval assign)
          (eval_blastExpr assign lhs bl hbl) (eval_blastExpr assign rhs br hbr)
      next => contradiction
    | ult =>
      simp only [blastPred] at h
      split at h
      next bl br hbl hbr =>
        simp only [Option.some.injEq] at h
        subst h
        simp only [BVPred.eval_bin, BVBinPred.eval_ult, eval_bddNot, BitVec.ult_eq_not_carry]
        congr 1
        apply eval_carryLoop (assignToBDDEnv assign) bl
          (ofBitFn w (fun i => bddNot (getBit br i))) (lhs.eval assign) (~~~(rhs.eval assign)) true
        · exact eval_blastExpr assign lhs bl hbl
        · intro k
          apply eval_ofBitFn_eq
          intro i hi
          simp [eval_blastExpr assign rhs br hbr i, hi]
      next => contradiction

def blastLogical : BVLogicalExpr → Option BDD
  | .const b => some (.leaf b)
  | .literal p => blastPred p
  | .not x =>
    match blastLogical x with
    | some b => some (bddNot b)
    | none => none
  | .gate g lhs rhs =>
    match blastLogical lhs, blastLogical rhs with
    | some bl, some br =>
      match g with
      | .and => some (bddAnd bl br)
      | .xor => some (bddXor bl br)
      | .beq => some (bddBeq bl br)
      | .or => some (bddOr bl br)
    | _, _ => none
  | .ite d l r =>
    match blastLogical d, blastLogical l, blastLogical r with
    | some bd, some bl, some br =>
      some (bddOr (bddAnd bd bl) (bddAnd (bddNot bd) br))
    | _, _, _ => none

theorem eval_blastLogical (assign : BVExpr.Assignment) (expr : BVLogicalExpr) (bdd : BDD)
    (h : blastLogical expr = some bdd) :
    bdd.eval (assignToBDDEnv assign) = expr.eval assign := by
  induction expr generalizing bdd with
  | const b =>
    simp only [blastLogical, Option.some.injEq] at h
    subst h
    rfl
  | literal p =>
    exact eval_blastPred assign p bdd h
  | not x ih =>
    simp only [blastLogical] at h
    split at h
    next b hb =>
      simp only [Option.some.injEq] at h
      subst h
      simp [ih b hb]
    next => contradiction
  | gate g lhs rhs ihl ihr =>
    simp only [blastLogical] at h
    split at h
    next bl br hbl hbr =>
      cases g <;> {
        simp only [Option.some.injEq] at h
        subst h
        simp [Gate.eval, ihl bl hbl, ihr br hbr]
      }
    next => contradiction
  | ite d l r ihd ihl ihr =>
    simp only [blastLogical] at h
    split at h
    next bd bl br hbd hbl hbr =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [eval_bddOr, eval_bddAnd, eval_bddNot, BVLogicalExpr.eval_ite,
        ihd bd hbd, ihl bl hbl, ihr br hbr]
      cases BVLogicalExpr.eval assign d <;> cases BVLogicalExpr.eval assign l <;>
        cases BVLogicalExpr.eval assign r <;> rfl
    next => contradiction

def checkBVLogicalUnsat (expr : BVLogicalExpr) : Bool :=
  match blastLogical expr with
  | some (.leaf false) => true
  | _ => false

theorem unsat_of_checkBVLogicalUnsat (expr : BVLogicalExpr)
    (h : checkBVLogicalUnsat expr = true) :
    expr.Unsat := by
  intro assign
  unfold checkBVLogicalUnsat at h
  split at h
  next hbl =>
    have heval := eval_blastLogical assign expr (.leaf false) hbl
    simpa [BDD.eval] using heval.symm
  next => contradiction

open Lean Meta Elab Tactic Lean.Meta.Tactic.BVDecide

meta def kernelBddProver (ctx : TacticContext) : UnsatProver Unit :=
  fun (_goal : MVarId) (reflectionResult : ReflectionResult)
      (_atomsAssignment : Std.HashMap Nat (Nat × Expr × Bool)) => do
    withOptions (fun opt => opt.set `compiler.extract_closed false) do
      addAndCompile <| .defnDecl {
        name := ctx.exprDef
        levelParams := []
        type := mkConst ``BVLogicalExpr
        value := reflectionResult.expr
        hints := .abbrev
        safety := .safe
      }
    let reflectedExpr := mkConst ctx.exprDef
    let expectedProp :=
      mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
        (mkApp (mkConst ``checkBVLogicalUnsat) reflectedExpr)
        (mkConst ``Bool.true)
    let rflProof :=
      mkApp2 (mkConst ``eagerReduce [0]) expectedProp
        (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
    let proof := mkApp2 (mkConst ``unsat_of_checkBVLogicalUnsat) reflectedExpr rflProof
    return .ok ⟨proof, ()⟩

meta def bvDecideKernel (g : MVarId) (ctx : TacticContext) : Grind.GrindM Unit := do
  Normalize.PreProcessM.run' ctx.preProcessContext (.mvarIdTarget g) do
    let solved ← Normalize.bvNormalize
    if solved then return ()
    let targetG ← Normalize.PreProcessM.getTargetMVarId
    let hyps ← Normalize.PreProcessM.getHyps
    let _ ← M.run (hypotheses := hyps) do
      closeWithBVReflection targetG (kernelBddProver ctx)
    return ()

elab "bv_decide_kernel" : tactic => do
  IO.FS.withTempFile fun _ lratFile => do
    let ctx ← TacticContext.new lratFile {} none
    liftMetaFinishingTactic fun g => do
      let params ← Grind.mkDefaultParams {}
      Grind.GrindM.run (params := params) <| bvDecideKernel g ctx

end KernelBVDecide

namespace BenchmarkSuite

open KernelBVDecide

/-!
## Class A: Layout & Alignment Arithmetic (`#71`, `#73`)
-/

/-- `#[repr(C)]` struct field byte-offset calculation. -/
@[grind =]
def fieldEnd (off sz pad : Nat) : Nat :=
  off + sz + pad

/-- `alignUp offset align` given `rem = offset % align`. -/
@[grind =]
def alignUpFromRem (offset align rem : Nat) : Nat :=
  if rem = 0 then offset else offset + (align - rem)

-- Problem A1: Struct field offset non-overlap (`#[repr(C)]` 3-field layout)
theorem A1_struct_field_nonoverlap_omega
    (base off0 sz0 pad0 off1 sz1 pad1 off2 sz2 total i j : Nat)
    (h_off1 : off1 = fieldEnd off0 sz0 pad0)
    (h_off2 : off2 = fieldEnd off1 sz1 pad1)
    (h_tot : fieldEnd off2 sz2 0 ≤ total)
    (hi : i < sz0) (hj : j < sz2) :
    base + off0 + i < base + off2 + j ∧ base + off2 + j < base + total := by
  unfold fieldEnd at *
  omega

theorem A1_struct_field_nonoverlap_grind_oob
    (base off0 sz0 pad0 off1 sz1 pad1 off2 sz2 total i j : Nat)
    (h_off1 : off1 = off0 + sz0 + pad0)
    (h_off2 : off2 = off1 + sz1 + pad1)
    (h_tot : off2 + sz2 ≤ total)
    (hi : i < sz0) (hj : j < sz2) :
    base + off0 + i < base + off2 + j ∧ base + off2 + j < base + total := by
  grind

theorem A1_struct_field_nonoverlap_grind_hint
    (base off0 sz0 pad0 off1 sz1 pad1 off2 sz2 total i j : Nat)
    (h_off1 : off1 = fieldEnd off0 sz0 pad0)
    (h_off2 : off2 = fieldEnd off1 sz1 pad1)
    (h_tot : fieldEnd off2 sz2 0 ≤ total)
    (hi : i < sz0) (hj : j < sz2) :
    base + off0 + i < base + off2 + j ∧ base + off2 + j < base + total := by
  grind

-- Problem A2: `alignUp offset align` bounds
-- (`offset ≤ alignUp ∧ alignUp < offset + align`)
theorem A2_alignUp_bounds_omega
    (offset align rem : Nat)
    (_h_align : 0 < align)
    (h_rem : rem < align) :
    offset ≤ alignUpFromRem offset align rem ∧
    alignUpFromRem offset align rem < offset + align := by
  unfold alignUpFromRem
  split <;> omega

theorem A2_alignUp_bounds_grind_oob
    (offset align rem : Nat)
    (h_align : 0 < align)
    (h_rem : rem < align) :
    offset ≤ (if rem == 0 then offset else offset + (align - rem)) ∧
    (if rem == 0 then offset else offset + (align - rem)) < offset + align := by
  grind

theorem A2_alignUp_bounds_grind_hint
    (offset align rem : Nat)
    (h_align : 0 < align)
    (h_rem : rem < align) :
    offset ≤ alignUpFromRem offset align rem ∧
    alignUpFromRem offset align rem < offset + align := by
  grind

-- Problem A3: Power-of-two bitmask alignment `(x + (a - 1)) &&& ~~~(a - 1)`
-- on `BitVec 64`
theorem A3_bitmask_align_bv64_kernel
    (x : BitVec 64) (h : x ≤ 0xffff_ffff_ffff_fff8#64) :
    let aligned := (x + 7#64) &&& 0xffff_ffff_ffff_fff8#64
    aligned ≥ x ∧ aligned ≤ x + 7#64 ∧ (aligned &&& 7#64 == 0#64) := by
  bv_decide_kernel

/-!
## Class B: `ByteMemory` / Allocation Frame Disjointness (`#72`)
-/

abbrev ByteMemory := Nat → UInt8

@[grind =]
def ByteMemory.writeByte (mem : ByteMemory) (addr : Nat) (b : UInt8) (a : Nat) : UInt8 :=
  if a == addr then b else mem a

@[grind =]
def ByteMemory.writeWord32 (mem : ByteMemory) (base : Nat) (b0 b1 b2 b3 : UInt8) (a : Nat) : UInt8 :=
  ByteMemory.writeByte
    (ByteMemory.writeByte
      (ByteMemory.writeByte
        (ByteMemory.writeByte mem base b0)
        (base + 1) b1)
      (base + 2) b2)
    (base + 3) b3 a

@[grind =]
theorem ByteMemory.read_writeByte_ne (mem : ByteMemory) (addr a : Nat) (b : UInt8)
    (hne : a ≠ addr) :
    ByteMemory.writeByte mem addr b a = mem a := by
  unfold ByteMemory.writeByte
  have hbeq : (a == addr) = false := beq_false_of_ne hne
  rw [hbeq]
  rfl

-- Problem B1: Quantified byte-range disjointness
-- (`∀ i < n, ∀ j < m, base1 + i ≠ base2 + j`)
theorem B1_byte_range_disjoint_omega
    (base1 n base2 m : Nat) (h_sep : base1 + n ≤ base2) :
    ∀ i, i < n → ∀ j, j < m → base1 + i ≠ base2 + j := by
  intro i hi j hj
  omega

theorem B1_byte_range_disjoint_grind_oob
    (base1 n base2 m : Nat) (h_sep : base1 + n ≤ base2) :
    ∀ i, i < n → ∀ j, j < m → base1 + i ≠ base2 + j := by
  grind

-- Problem B2: Reading from an updated `ByteMemory` map after a disjoint
-- 4-byte write
theorem B2_byte_memory_disjoint_read_omega
    (mem : ByteMemory) (base1 base2 _m j : Nat) (b0 b1 b2 b3 : UInt8)
    (h_sep : base1 + 4 ≤ base2) (_hj : j < _m) :
    ByteMemory.writeWord32 mem base1 b0 b1 b2 b3 (base2 + j) = mem (base2 + j) := by
  unfold ByteMemory.writeWord32 ByteMemory.writeByte
  have h0 : (base2 + j == base1) = false := beq_false_of_ne (by omega)
  have h1 : (base2 + j == base1 + 1) = false := beq_false_of_ne (by omega)
  have h2 : (base2 + j == base1 + 2) = false := beq_false_of_ne (by omega)
  have h3 : (base2 + j == base1 + 3) = false := beq_false_of_ne (by omega)
  rw [h3, h2, h1, h0]
  rfl

theorem B2_byte_memory_disjoint_read_grind_oob
    (mem : ByteMemory) (base1 base2 _m j : Nat) (b0 b1 b2 b3 : UInt8)
    (h_sep : base1 + 4 ≤ base2) (_hj : j < _m) :
    ByteMemory.writeByte
      (ByteMemory.writeByte
        (ByteMemory.writeByte
          (ByteMemory.writeByte mem base1 b0)
          (base1 + 1) b1)
        (base1 + 2) b2)
      (base1 + 3) b3 (base2 + j)
      = mem (base2 + j) := by
  grind [ByteMemory.writeByte]

theorem B2_byte_memory_disjoint_read_grind_hint
    (mem : ByteMemory) (base1 base2 _m j : Nat) (b0 b1 b2 b3 : UInt8)
    (h_sep : base1 + 4 ≤ base2) (_hj : j < _m) :
    ByteMemory.writeWord32 mem base1 b0 b1 b2 b3 (base2 + j) = mem (base2 + j) := by
  grind

-- Problem B3: Quantified allocation-frame preservation over disjoint byte
-- ranges
theorem B3_quantified_frame_grind_oob
    (mem mem' : ByteMemory) (base1 n base2 m : Nat)
    (h_write : ∀ a, (∀ i, i < n → a ≠ base1 + i) → mem' a = mem a)
    (h_disj : ∀ i, i < n → ∀ j, j < m → base1 + i ≠ base2 + j) :
    ∀ j, j < m → mem' (base2 + j) = mem (base2 + j) := by
  grind

/-!
## Class C: Coupled Existential Witness Obligations (`MirLang.SpecOn`)
-/

@[simp, grind =]
def evalInc (z : Int) : Option Int :=
  some z

-- Problem C1: `∃ (retVal : Int), evalInc (x + 1) = some retVal ∧ retVal > x`
theorem C1_coupled_existential_refine_omega (x : Int) :
    ∃ (retVal : Int), evalInc (x + 1) = some retVal ∧ retVal > x := by
  refine ⟨_, rfl, by omega⟩

theorem C1_coupled_existential_refine_grind (x : Int) :
    ∃ (retVal : Int), evalInc (x + 1) = some retVal ∧ retVal > x := by
  refine ⟨_, rfl, by grind⟩

-- Problem C2: `MirLang.SpecOn` / `Partial` coupled refinement witness
-- obligation
structure SimplePartial (B : Type) where
  defined : Prop
  val : defined → B

@[simp, grind =]
def SimplePartial.leProp (p1 p2 : SimplePartial (Int → Prop)) : Prop :=
  ∀ h2 : p2.defined, ∃ h1 : p1.defined, ∀ out, p1.val h1 out → p2.val h2 out

@[simp, grind =]
def progSem (x : Int) : SimplePartial (Int → Prop) where
  defined := x ≥ 0
  val _ out := out = x + 1

@[simp, grind =]
def specOnNonneg (x : Int) : SimplePartial (Int → Prop) where
  defined := x ≥ 0
  val _ out := ∃ retVal : Int, some out = some retVal ∧ retVal > x ∧ retVal ≥ 1

theorem C2_spec_on_refinement_refine_omega (x : Int) :
    SimplePartial.leProp (progSem x) (specOnNonneg x) := by
  unfold SimplePartial.leProp progSem specOnNonneg
  intro h2
  refine ⟨h2, fun out hout => ⟨_, rfl, by omega, by omega⟩⟩

theorem C2_spec_on_refinement_refine_grind (x : Int) :
    SimplePartial.leProp (progSem x) (specOnNonneg x) := by
  intro h2
  refine ⟨h2, fun out hout => ⟨_, rfl, by grind⟩⟩

/-!
## Class D: 64-bit `BitVec` Overflow & Checked Arithmetic (`#71`)
-/

-- Problem D1: `BitVec 64` unsigned addition overflow detection
theorem D1_uadd_overflow_iff_bv64_kernel (x y : BitVec 64) :
    (!BitVec.uaddOverflow x y) = (x + y ≥ x) := by
  bv_decide_kernel


-- Problem D2: `BitVec 64` two's complement signed range bounds & non-overflow
theorem D2_sadd_overflow_signed_bounds_bv64_kernel (x y : BitVec 64)
    (hx0 : BitVec.sle 0#64 x) (hx1 : BitVec.sle x 0x3fff_ffff_ffff_ffff#64)
    (hy0 : BitVec.sle 0#64 y) (hy1 : BitVec.sle y 0x3fff_ffff_ffff_ffff#64) :
    !BitVec.saddOverflow x y ∧ BitVec.sle 0#64 (x + y) := by
  bv_decide_kernel


-- Problem D3: `BitVec 64` 32-bit bitfield packing & extraction round-trip
theorem D3_bitfield_extract_pack_bv64_kernel (lo hi : BitVec 32) :
    let w : BitVec 64 := (hi.zeroExtend 64 <<< 32) ||| lo.zeroExtend 64
    w.extractLsb' 0 32 = lo ∧ w.extractLsb' 32 32 = hi := by
  bv_decide_kernel


theorem D3_bitfield_extract_pack_bv64_grind_oob (lo hi : BitVec 32) :
    let w : BitVec 64 := (hi.zeroExtend 64 <<< 32) ||| lo.zeroExtend 64
    w.extractLsb' 0 32 = lo ∧ w.extractLsb' 32 32 = hi := by
  grind

/-!
## Class E: First-Order Relational and Reachability Lemmas (`#77`)
-/

inductive Perm where
  | Disabled
  | Frozen
  | SharedRO
  | SharedRW
  | Unique
  deriving DecidableEq, Repr

inductive PermLe : Perm → Perm → Prop where
  | refl (p : Perm) : PermLe p p
  | trans {p1 p2 p3 : Perm} : PermLe p1 p2 → PermLe p2 p3 → PermLe p1 p3
  | disabled_frozen : PermLe .Disabled .Frozen
  | frozen_sharedRO : PermLe .Frozen .SharedRO
  | sharedRO_sharedRW : PermLe .SharedRO .SharedRW
  | sharedRW_unique : PermLe .SharedRW .Unique

attribute [grind →] PermLe.trans

-- Problem E1: Tree Borrows transitive tag ancestry & permission propagation
section TreeBorrows

variable (Tag Loc : Type)
variable (Parent : Tag → Tag → Prop)
variable (Ancestor : Tag → Tag → Prop)
variable (HasPerm : Tag → Loc → Perm → Prop)
variable (PreservesValid : Tag → Tag → Loc → Prop)

-- With a forward-triggerable base step (`Parent t1 t2 → Ancestor t1 t2`),
-- `grind`'s E-matching cascades through the 3-step `Parent` chain.
theorem E1_tree_borrows_ancestry_grind_hint
    (h_refl : ∀ t, Ancestor t t)
    (h_step : ∀ t1 t2 t3, Parent t1 t2 → Ancestor t2 t3 → Ancestor t1 t3)
    (h_prop : ∀ t1 t2 loc, Ancestor t1 t2 → HasPerm t1 loc .Unique →
      HasPerm t2 loc .Frozen → PreservesValid t1 t2 loc)
    (t0 t1 t2 t3 : Tag) (loc : Loc)
    (hp01 : Parent t0 t1) (hp12 : Parent t1 t2) (hp23 : Parent t2 t3)
    (hperm0 : HasPerm t0 loc .Unique) (hperm3 : HasPerm t3 loc .Frozen) :
    PreservesValid t0 t3 loc := by
  have h_base : ∀ a b, Parent a b → Ancestor a b := fun a b hp => h_step a b b hp (h_refl b)
  grind

end TreeBorrows

-- Problem E2: Stacked Borrows permission lattice and stack inclusion
-- compatibility
section StackedBorrows

variable (Tag Stack : Type)
variable (InStack : Tag → Stack → Prop)
variable (TagPerm : Tag → Perm)
variable (ReadAllowed : Tag → Stack → Prop)

theorem E2_stacked_borrows_lattice_grind_hint
    (h_read : ∀ t s, InStack t s → PermLe .SharedRO (TagPerm t) → ReadAllowed t s)
    (s1 s2 : Stack) (t : Tag)
    (h_incl : ∀ x, InStack x s1 → InStack x s2)
    (h_in : InStack t s1)
    (h_perm : TagPerm t = .Unique) :
    ReadAllowed t s2 := by
  have h1 := PermLe.sharedRO_sharedRW
  have h2 := PermLe.sharedRW_unique
  grind

end StackedBorrows

-- Problem E3 & E4: Higher-order set-inclusion and multi-step relational
-- witness synthesis
section SetDisjointness

variable (Tag Loc : Type)

theorem E3_higher_order_footprint_disjoint_grind_oob
    (S1 S2 T1 T2 : Loc → Prop)
    (Active1 Active2 : Tag → Prop)
    (proj : Tag → Loc)
    (h_sub1 : ∀ x, S1 x → T1 x)
    (h_sub2 : ∀ x, S2 x → T2 x)
    (h_disj : ∀ x, T1 x → T2 x → False)
    (h_act1 : ∀ t, Active1 t → S1 (proj t))
    (h_act2 : ∀ t, Active2 t → S2 (proj t))
    (t1 t2 : Tag) (ha1 : Active1 t1) (ha2 : Active2 t2) :
    proj t1 ≠ proj t2 := by
  grind

theorem E4_relational_witness_chain_grind_oob
    (R : Tag → Tag → Prop)
    (Valid : Tag → Prop)
    (step : Tag → Tag)
    (h_step : ∀ x, Valid x → R x (step x) ∧ Valid (step x))
    (h_trans : ∀ x y z, R x y → R y z → R x z)
    (t0 : Tag) (hv0 : Valid t0) :
    ∃ t2, R t0 t2 ∧ R (step t0) t2 ∧ Valid t2 := by
  grind

end SetDisjointness

/-!
## Axiom Footprint Audit (`#print axioms`)
-/

#print axioms A1_struct_field_nonoverlap_omega
#print axioms A1_struct_field_nonoverlap_grind_oob
#print axioms A1_struct_field_nonoverlap_grind_hint
#print axioms A2_alignUp_bounds_omega
#print axioms A2_alignUp_bounds_grind_oob
#print axioms A2_alignUp_bounds_grind_hint
#print axioms A3_bitmask_align_bv64_kernel
#print axioms B1_byte_range_disjoint_omega
#print axioms B1_byte_range_disjoint_grind_oob
#print axioms B2_byte_memory_disjoint_read_omega
#print axioms B2_byte_memory_disjoint_read_grind_oob
#print axioms B2_byte_memory_disjoint_read_grind_hint
#print axioms B3_quantified_frame_grind_oob
#print axioms C1_coupled_existential_refine_omega
#print axioms C1_coupled_existential_refine_grind
#print axioms C2_spec_on_refinement_refine_omega
#print axioms C2_spec_on_refinement_refine_grind
#print axioms D1_uadd_overflow_iff_bv64_kernel
#print axioms D2_sadd_overflow_signed_bounds_bv64_kernel
#print axioms D3_bitfield_extract_pack_bv64_kernel
#print axioms D3_bitfield_extract_pack_bv64_grind_oob
#print axioms E1_tree_borrows_ancestry_grind_hint
#print axioms E2_stacked_borrows_lattice_grind_hint
#print axioms E3_higher_order_footprint_disjoint_grind_oob
#print axioms E4_relational_witness_chain_grind_oob

end BenchmarkSuite
