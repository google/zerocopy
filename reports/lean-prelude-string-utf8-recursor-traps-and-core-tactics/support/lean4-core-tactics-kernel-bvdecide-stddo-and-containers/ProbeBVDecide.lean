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
# Part 1 Probe: `bv_decide`, `Std.Sat`, and Kernel-Reducible BitVec Reflection

This file demonstrates:
1. The `#print axioms` footprint of standard `bv_decide` in Lean `v4.34.1` on
   64-bit `BitVec` and `UInt64` obligations (`_native.bv_decide.ax_*` injected
   by `Lean.Meta.nativeEqTrue`).
2. A self-contained, `Std.HashMap`-free LRAT/RUP checker (`KernelLRAT`) that
   reduces in the Lean 4 kernel (`decide +kernel` / `rfl`) with **zero axioms**.
3. An end-to-end kernel-reducible `bv_decide_kernel` tactic that reuses
   `bv_decide`'s `Normalize.bvNormalize` and `Reflect.reflectBV` front-end and
   discharges `BVLogicalExpr.Unsat` by in-kernel reduction (`eagerReduce`) with
   **zero `Lean.trustCompiler` and zero `_native` axioms**.
-/

namespace StandardBVDecide

-- 1a. Alignment mask preservation on 64-bit addresses.
theorem align_mask_bv64 (addr : BitVec 64) :
    (addr &&& 7#64 == 0#64) → ((addr + 8#64) &&& 7#64 == 0#64) := by
  bv_decide

#print axioms align_mask_bv64

-- 1b. Checked unsigned addition overflow characterization on 64-bit BitVec.
theorem checked_add_no_overflow_bv64 (x y : BitVec 64) :
    (!BitVec.uaddOverflow x y) = (x + y ≥ x) := by
  bv_decide

#print axioms checked_add_no_overflow_bv64

-- 1c. Bitwise AND upper bound on 64-bit BitVec.
theorem bitwise_and_le_mask_bv64 (x mask : BitVec 64) :
    (x &&& mask) ≤ mask := by
  bv_decide

#print axioms bitwise_and_le_mask_bv64

-- 1d. 64-bit alignment round-up without overflow on UInt64.
theorem uint64_align_roundup (x : UInt64) (h : x ≤ 0xffff_ffff_ffff_fff0) :
    let aligned := (x + 7) &&& 0xffff_ffff_ffff_fff8
    aligned ≥ x ∧ (aligned &&& 7 == 0) := by
  bv_decide

#print axioms uint64_align_roundup

end StandardBVDecide

/-!
## Section 2: Kernel-Reducible LRAT / RUP Checker (`KernelLRAT`)

`Std.Tactic.BVDecide.LRAT.check` cannot reduce in the Lean 4 kernel because:
- `LRAT.Parser.parseActions` uses `partial def` (compiled as `opaque`) and
  `String.toUTF8` (`opaque`).
- `DefaultClause.ofArray.folder`
  (`Std/Tactic/BVDecide/LRAT/Internal/Clause.lean:141`) is marked
  `@[irreducible]` and uses `Std.HashMap` (`opaque mixHash` and
  `opaque System.Platform.getNumBits`).

Below is a total, `Std.HashMap`-free LRAT/RUP checker whose soundness theorem
and kernel execution use zero custom or native axioms.
-/

namespace KernelLRAT

abbrev Lit := Nat × Bool
abbrev Clause := List Lit
abbrev Formula := List Clause

def evalLit (f : Nat → Bool) (l : Lit) : Bool :=
  f l.1 == l.2

def evalClause (f : Nat → Bool) : Clause → Bool
  | [] => false
  | l :: ls => evalLit f l || evalClause f ls

def evalFormula (f : Nat → Bool) : Formula → Bool
  | [] => true
  | c :: cs => evalClause f c && evalFormula f cs

def Formula.Unsat (F : Formula) : Prop :=
  ∀ f, evalFormula f F = false

-- Partial assignment represented as an association list `(var, val)`.
abbrev Assign := List (Nat × Bool)

def Assign.Consistent (f : Nat → Bool) : Assign → Prop
  | [] => True
  | (v, b) :: rest => f v = b ∧ Assign.Consistent f rest

def isFalsified (a : Assign) (l : Lit) : Bool :=
  match a with
  | [] => false
  | (v, b) :: rest => (v == l.1 && b == !l.2) || isFalsified rest l

theorem evalLit_false_of_isFalsified (f : Nat → Bool) (a : Assign) (l : Lit)
    (ha : Assign.Consistent f a) (hf : isFalsified a l = true) :
    evalLit f l = false := by
  induction a with
  | nil => contradiction
  | cons hd rest ih =>
    rcases hd with ⟨v, b⟩
    rcases ha with ⟨hvb, hrest⟩
    simp only [isFalsified, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hf
    rcases hf with ⟨rfl, rfl⟩ | hf'
    · simp only [evalLit, hvb]
      cases l.2 <;> rfl
    · exact ih hrest hf'

-- Filter out falsified literals from a clause under `a`.
def reduceClause (a : Assign) : Clause → Clause
  | [] => []
  | l :: ls => if isFalsified a l then reduceClause a ls else l :: reduceClause a ls

theorem evalClause_reduceClause (f : Nat → Bool) (a : Assign) (c : Clause)
    (ha : Assign.Consistent f a) :
    evalClause f (reduceClause a c) = evalClause f c := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    simp only [reduceClause]
    split
    next hf =>
      have hfalse := evalLit_false_of_isFalsified f a l ha hf
      simp [evalClause, hfalse, ih]
    next =>
      simp [evalClause, ih]

def getClause : Formula → Nat → Option Clause
  | [], _ => none
  | c :: _, 0 => some c
  | _ :: cs, i + 1 => getClause cs i

theorem evalClause_of_getClause (f : Nat → Bool) (F : Formula) (idx : Nat) (c : Clause)
    (hF : evalFormula f F = true) (hc : getClause F idx = some c) :
    evalClause f c = true := by
  induction F generalizing idx with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [evalFormula, Bool.and_eq_true] at hF
    cases idx with
    | zero =>
      simp only [getClause, Option.some.injEq] at hc
      subst hc
      exact hF.1
    | succ idx =>
      exact ih idx hF.2 hc

-- Propagate a list of hint clause indices to derive a conflict (`true`).
def rupPropagate (F : Formula) (a : Assign) : List Nat → Bool
  | [] => false
  | idx :: hints =>
    match getClause F idx with
    | none => false
    | some c =>
      match reduceClause a c with
      | [] => true
      | [unitLit] => rupPropagate F ((unitLit.1, unitLit.2) :: a) hints
      | _ => false

theorem rupPropagate_sound (f : Nat → Bool) (F : Formula) (a : Assign) (hints : List Nat)
    (hF : evalFormula f F = true) (ha : Assign.Consistent f a) :
    rupPropagate F a hints = false := by
  induction hints generalizing a with
  | nil => rfl
  | cons idx rest ih =>
    simp only [rupPropagate]
    split
    · rfl
    next c hc =>
      have hceval := evalClause_of_getClause f F idx c hF hc
      have hred := evalClause_reduceClause f a c ha
      rw [hceval] at hred
      split
      next hempty =>
        rw [hempty] at hred
        contradiction
      next u hunit =>
        rw [hunit] at hred
        simp only [evalClause, Bool.or_false, evalLit, beq_iff_eq] at hred
        exact ih ((u.1, u.2) :: a) ⟨hred, ha⟩
      next => rfl

def negateClause : Clause → Assign
  | [] => []
  | (v, b) :: ls => (v, !b) :: negateClause ls

theorem consistent_negateClause (f : Nat → Bool) (c : Clause)
    (hc : evalClause f c = false) :
    Assign.Consistent f (negateClause c) := by
  induction c with
  | nil => trivial
  | cons l ls ih =>
    rcases l with ⟨v, b⟩
    simp only [evalClause, Bool.or_eq_false_iff, evalLit, beq_eq_false_iff_ne] at hc
    refine ⟨?_, ih hc.2⟩
    cases hfv : f v <;> cases b <;> simp_all

def checkRupStep (F : Formula) (c : Clause) (hints : List Nat) : Bool :=
  rupPropagate F (negateClause c) hints

theorem evalClause_of_checkRupStep (f : Nat → Bool) (F : Formula) (c : Clause) (hints : List Nat)
    (hF : evalFormula f F = true) (hrup : checkRupStep F c hints = true) :
    evalClause f c = true := by
  cases hc : evalClause f c
  · have ha := consistent_negateClause f c hc
    have hfalse := rupPropagate_sound f F (negateClause c) hints hF ha
    unfold checkRupStep at hrup
    rw [hfalse] at hrup
    contradiction
  · rfl

-- An LRAT/RUP certificate is a sequence of `(derivedClause, hintIndices)`,
-- ending with the empty clause `[]`.
def checkCert : Formula → List (Clause × List Nat) → Bool
  | _, [] => false
  | F, (c, hints) :: rest =>
    if checkRupStep F c hints then
      if c.isEmpty then true else checkCert (F ++ [c]) rest
    else
      false

theorem evalFormula_append_singleton (f : Nat → Bool) (F : Formula) (c : Clause)
    (hF : evalFormula f F = true) (hc : evalClause f c = true) :
    evalFormula f (F ++ [c]) = true := by
  induction F with
  | nil => simp [evalFormula, hc]
  | cons hd tl ih =>
    simp only [List.cons_append, evalFormula, Bool.and_eq_true] at hF ⊢
    exact ⟨hF.1, ih hF.2⟩

theorem checkCert_sound (F : Formula) (cert : List (Clause × List Nat))
    (h : checkCert F cert = true) :
    F.Unsat := by
  intro f
  induction cert generalizing F with
  | nil => contradiction
  | cons step rest ih =>
    rcases step with ⟨c, hints⟩
    simp only [checkCert] at h
    split at h
    next hrup =>
      split at h
      next hempty =>
        cases hF : evalFormula f F
        · rfl
        · have hc := evalClause_of_checkRupStep f F c hints hF hrup
          cases c with
          | nil => contradiction
          | cons _ _ => contradiction
      next =>
        cases hF : evalFormula f F
        · rfl
        · have hc := evalClause_of_checkRupStep f F c hints hF hrup
          have hF' := evalFormula_append_singleton f F c hF hc
          have hunsat := ih (F ++ [c]) h
          rw [hunsat] at hF'
          contradiction
    next => contradiction

-- Example: 2-bit adder carry-out contradiction proved in the kernel via
-- `decide +kernel`.
def sampleUnsatCNF : Formula :=
  [ [(0, true), (1, true)]    -- 0: x0 ∨ x1
  , [(0, false), (2, true)]   -- 1: ¬x0 ∨ x2
  , [(1, false), (2, true)]   -- 2: ¬x1 ∨ x2
  , [(2, false), (3, true)]   -- 3: ¬x2 ∨ x3
  , [(3, false), (0, false)]  -- 4: ¬x3 ∨ ¬x0
  , [(3, false), (1, false)]  -- 5: ¬x3 ∨ ¬x1
  ]

def sampleLRATCert : List (Clause × List Nat) :=
  [ ([(2, true)], [1, 2, 0])  -- 6: derive x2 from clauses 1, 2, 0
  , ([(3, true)], [6, 3])     -- 7: derive x3 from clauses 6, 3
  , ([], [7, 4, 5, 0])        -- 8: derive ⊥ from clauses 7, 4, 5, 0
  ]

theorem sampleCNF_unsat : sampleUnsatCNF.Unsat :=
  checkCert_sound sampleUnsatCNF sampleLRATCert (by decide +kernel)

#print axioms sampleCNF_unsat

end KernelLRAT

/-!
## Section 3: Kernel-Reducible `bv_decide_kernel` (`BVLogicalExpr` + ROBDD)

We now connect `Std.Tactic.BVDecide`'s preprocessing (`Normalize.bvNormalize`)
and reflection (`Reflect.reflectBV`) to an in-kernel ROBDD decision procedure
(`checkBVLogicalUnsat`) using interleaved LSB-to-MSB variable ordering and the
propagate-generate basis `(x_i, x_i ^^ y_i)` for variable 1.
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

-- 2a. Alignment mask preservation on 64-bit addresses (kernel reduction).
theorem align_mask_bv64_kernel (addr : BitVec 64) :
    (addr &&& 7#64 == 0#64) → ((addr + 8#64) &&& 7#64 == 0#64) := by
  bv_decide_kernel

#print axioms align_mask_bv64_kernel

-- 2b. Checked unsigned addition overflow on 8, 16, 32, and 64-bit BitVec
-- (kernel reduction).
theorem checked_add_no_overflow_bv8_kernel (x y : BitVec 8) :
    (!BitVec.uaddOverflow x y) = (x + y ≥ x) := by
  bv_decide_kernel

theorem checked_add_no_overflow_bv16_kernel (x y : BitVec 16) :
    (!BitVec.uaddOverflow x y) = (x + y ≥ x) := by
  bv_decide_kernel

theorem checked_add_no_overflow_bv32_kernel (x y : BitVec 32) :
    (!BitVec.uaddOverflow x y) = (x + y ≥ x) := by
  bv_decide_kernel

theorem checked_add_no_overflow_bv64_kernel (x y : BitVec 64) :
    (!BitVec.uaddOverflow x y) = (x + y ≥ x) := by
  bv_decide_kernel

#print axioms checked_add_no_overflow_bv64_kernel

-- 2c. Bitwise AND upper bound on 64-bit BitVec (kernel reduction).
theorem bitwise_and_le_mask_bv64_kernel (x mask : BitVec 64) :
    (x &&& mask) ≤ mask := by
  bv_decide_kernel

#print axioms bitwise_and_le_mask_bv64_kernel

-- 2d. 64-bit alignment round-up without overflow on UInt64 (kernel reduction).
theorem uint64_align_roundup_kernel (x : UInt64) (h : x ≤ 0xffff_ffff_ffff_fff0) :
    let aligned := (x + 7) &&& 0xffff_ffff_ffff_fff8
    aligned ≥ x ∧ (aligned &&& 7 == 0) := by
  bv_decide_kernel

#print axioms uint64_align_roundup_kernel

end KernelBVDecide
