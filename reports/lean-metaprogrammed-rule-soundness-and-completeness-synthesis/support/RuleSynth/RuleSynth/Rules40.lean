-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RuleSynth.Semantics

namespace RuleSynth

/-- 25 expression rewrite constructors (`R01`..`R25`) spanning Class A
(algebraic, bitwise, constant-folding, double-negation, and `freeze` peepholes)
and Class B (recursive expression congruence). -/
inductive ExprRewrite where
  | refl (e : Expr)
  | addZeroRight (e : Expr)
  | addZeroLeft (e : Expr)
  | subZeroRight (e : Expr)
  | subSelf (e : Expr)
  | mulOneRight (e : Expr)
  | mulOneLeft (e : Expr)
  | mulZeroRight (e : Expr)
  | mulZeroLeft (e : Expr)
  | negNeg (e : Expr)
  | addNegSelf (e : Expr)
  | subNegToAdd (a b : Expr)
  | addComm (a b : Expr)
  | mulComm (a b : Expr)
  | bitAndSelf (e : Expr)
  | bitAndZeroRight (e : Expr)
  | bitAndZeroLeft (e : Expr)
  | bitAndComm (a b : Expr)
  | bitOrSelf (e : Expr)
  | bitOrZeroRight (e : Expr)
  | bitOrZeroLeft (e : Expr)
  | bitOrComm (a b : Expr)
  | bitXorSelf (e : Expr)
  | shiftLeftZeroId (e : Expr)
  | freezeIdemp (e : Expr)
  deriving DecidableEq, Repr

/-- Endpoint synthesizer `inferExprRewrite` mapping each `ExprRewrite` constructor
to its exact `(src, tgt)` expression pair (`PITFALL-3` resolution). -/
def inferExprRewrite : ExprRewrite → Expr × Expr
  | .refl e => (e, e)
  | .addZeroRight e => (.add e (.const 0), e)
  | .addZeroLeft e => (.add (.const 0) e, e)
  | .subZeroRight e => (.sub e (.const 0), e)
  | .subSelf e => (.sub e e, .const 0)
  | .mulOneRight e => (.mul e (.const 1), e)
  | .mulOneLeft e => (.mul (.const 1) e, e)
  | .mulZeroRight e => (.mul e (.const 0), .const 0)
  | .mulZeroLeft e => (.mul (.const 0) e, .const 0)
  | .negNeg e => (.neg (.neg e), e)
  | .addNegSelf e => (.add e (.neg e), .const 0)
  | .subNegToAdd a b => (.sub a (.neg b), .add a b)
  | .addComm a b => (.add a b, .add b a)
  | .mulComm a b => (.mul a b, .mul b a)
  | .bitAndSelf e => (.bitAnd e e, e)
  | .bitAndZeroRight e => (.bitAnd e (.const 0), .const 0)
  | .bitAndZeroLeft e => (.bitAnd (.const 0) e, .const 0)
  | .bitAndComm a b => (.bitAnd a b, .bitAnd b a)
  | .bitOrSelf e => (.bitOr e e, e)
  | .bitOrZeroRight e => (.bitOr e (.const 0), e)
  | .bitOrZeroLeft e => (.bitOr (.const 0) e, e)
  | .bitOrComm a b => (.bitOr a b, .bitOr b a)
  | .bitXorSelf e => (.bitXor e e, .const 0)
  | .shiftLeftZeroId e => (.shiftLeftZero e, e)
  | .freezeIdemp e => (.freezeVal (.freezeVal e), .freezeVal e)

def checkDisjointNoAlias (s1 s2 : SlotId) (t1 t2 : AliasTag) : Bool :=
  decide (s1 ≠ s2 ∧ t1 ≠ t2)

/-- 15 statement derivation constructors (`R26`..`R40`) spanning Class B
(structural congruence, `JumpThreading` branch folding, `Unwind-LandingPadMerge`,
`DbgValue` stripping, and transitivity) and Class C (`SROA` slot promotion,
`GVN`/`LICM` `noalias` store forwarding, `DSE` overwritten store elimination,
`ReadOnly` call forwarding, and `Atomic-OrderLattice` non-atomic forwarding).
Combined with `ExprRewrite` (25 constructors), this yields 40 `-O3` rules. -/
inductive StmtDeriv where
  | refl (s : Stmt)
  | rewriteAssign (dst : RegId) (rw : ExprRewrite)
  | promoteSlotToAssign (slot : SlotId) (tag : AliasTag) (dst : RegId) (e : Expr)
  | forwardStoreAcrossNoAlias (s1 s2 : SlotId) (t1 t2 : AliasTag) (dst : RegId) (e1 e2 : Expr)
  | forwardAtomicAcrossNoAlias (s1 s2 : SlotId) (t1 t2 : AliasTag) (dst : RegId) (e1 e2 : Expr)
  | elimOverwrittenStore (slot : SlotId) (t1 t2 : AliasTag) (e1 e2 : Expr)
  | elimOverwrittenAssign (dst : RegId) (v1 v2 : Int)
  | foldReadOnlyCall (dst : RegId) (arg : Expr)
  | elimSkipLeft (s : Stmt)
  | elimSkipRight (s : Stmt)
  | elimDbgValue (r : RegId) (metaId : Nat)
  | elimAssumeOverflowUB (r : RegId) (limit : Int)
  | elimAssumeNonNegUB (r : RegId)
  | foldIfZeroTrue (thenBr elseBr : Stmt)
  | seqCong (d1 d2 : StmtDeriv)
  deriving DecidableEq, Repr

/-- Executable boolean checker `checkStmtDeriv` over the 15-constructor `Stmt` AST. -/
def checkStmtDeriv (src tgt : Stmt) : StmtDeriv → Bool
  | .refl s =>
      decide (src = s ∧ tgt = s)
  | .rewriteAssign dst rw =>
      let (eSrc, eTgt) := inferExprRewrite rw
      decide (src = .assign dst eSrc ∧ tgt = .assign dst eTgt)
  | .promoteSlotToAssign slot tag dst e =>
      decide (src = .seq (.storeSlot slot tag e) (.loadSlot dst slot tag) ∧
              tgt = .seq (.storeSlot slot tag e) (.assign dst e))
  | .forwardStoreAcrossNoAlias s1 s2 t1 t2 dst e1 e2 =>
      checkDisjointNoAlias s1 s2 t1 t2 &&
      decide (src = .seq (.seq (.storeSlot s1 t1 e1) (.storeSlot s2 t2 e2)) (.loadSlot dst s1 t1) ∧
              tgt = .seq (.seq (.storeSlot s1 t1 e1) (.storeSlot s2 t2 e2)) (.assign dst e1))
  | .forwardAtomicAcrossNoAlias s1 s2 t1 t2 dst e1 e2 =>
      checkDisjointNoAlias s1 s2 t1 t2 &&
      decide (src = .seq (.seq (.storeSlot s1 t1 e1) (.atomicStore s2 t2 e2)) (.loadSlot dst s1 t1) ∧
              tgt = .seq (.seq (.storeSlot s1 t1 e1) (.atomicStore s2 t2 e2)) (.assign dst e1))
  | .elimOverwrittenStore slot t1 t2 e1 e2 =>
      decide (src = .seq (.storeSlot slot t1 e1) (.storeSlot slot t2 e2) ∧
              tgt = .storeSlot slot t2 e2)
  | .elimOverwrittenAssign dst v1 v2 =>
      decide (src = .seq (.assign dst (.const v1)) (.assign dst (.const v2)) ∧
              tgt = .assign dst (.const v2))
  | .foldReadOnlyCall dst arg =>
      decide (src = .callReadOnly dst arg ∧ tgt = .assign dst arg)
  | .elimSkipLeft s =>
      decide (src = .seq .skip s ∧ tgt = s)
  | .elimSkipRight s =>
      decide (src = .seq s .skip ∧ tgt = s)
  | .elimDbgValue r metaId =>
      decide (src = .dbgValue r metaId ∧ tgt = .skip)
  | .elimAssumeOverflowUB r limit =>
      decide (src = .assumeNoOverflowUB r limit ∧ tgt = .skip)
  | .elimAssumeNonNegUB r =>
      decide (src = .assumeKnownNonNegUB r ∧ tgt = .skip)
  | .foldIfZeroTrue thenBr elseBr =>
      decide (src = .ifZeroCond 0 thenBr elseBr ∧ tgt = thenBr)
  | .seqCong d1 d2 =>
      match src, tgt with
      | .seq s1 s2, .seq t1 t2 => checkStmtDeriv s1 t1 d1 && checkStmtDeriv s2 t2 d2
      | _, _ => false

/-- Declarative validity relation `ValidStmtDeriv` for completeness & inversion. -/
inductive ValidStmtDeriv : Stmt → Stmt → StmtDeriv → Prop where
  | refl (s : Stmt) :
      ValidStmtDeriv s s (.refl s)
  | rewriteAssign (dst : RegId) (rw : ExprRewrite) :
      ValidStmtDeriv
        (.assign dst (inferExprRewrite rw).1)
        (.assign dst (inferExprRewrite rw).2)
        (.rewriteAssign dst rw)
  | promoteSlotToAssign (slot : SlotId) (tag : AliasTag) (dst : RegId) (e : Expr) :
      ValidStmtDeriv
        (.seq (.storeSlot slot tag e) (.loadSlot dst slot tag))
        (.seq (.storeSlot slot tag e) (.assign dst e))
        (.promoteSlotToAssign slot tag dst e)
  | forwardStoreAcrossNoAlias
      (s1 s2 : SlotId) (t1 t2 : AliasTag) (dst : RegId) (e1 e2 : Expr)
      (h_slot : s1 ≠ s2) (h_tag : t1 ≠ t2) :
      ValidStmtDeriv
        (.seq (.seq (.storeSlot s1 t1 e1) (.storeSlot s2 t2 e2)) (.loadSlot dst s1 t1))
        (.seq (.seq (.storeSlot s1 t1 e1) (.storeSlot s2 t2 e2)) (.assign dst e1))
        (.forwardStoreAcrossNoAlias s1 s2 t1 t2 dst e1 e2)
  | forwardAtomicAcrossNoAlias
      (s1 s2 : SlotId) (t1 t2 : AliasTag) (dst : RegId) (e1 e2 : Expr)
      (h_slot : s1 ≠ s2) (h_tag : t1 ≠ t2) :
      ValidStmtDeriv
        (.seq (.seq (.storeSlot s1 t1 e1) (.atomicStore s2 t2 e2)) (.loadSlot dst s1 t1))
        (.seq (.seq (.storeSlot s1 t1 e1) (.atomicStore s2 t2 e2)) (.assign dst e1))
        (.forwardAtomicAcrossNoAlias s1 s2 t1 t2 dst e1 e2)
  | elimOverwrittenStore (slot : SlotId) (t1 t2 : AliasTag) (e1 e2 : Expr) :
      ValidStmtDeriv
        (.seq (.storeSlot slot t1 e1) (.storeSlot slot t2 e2))
        (.storeSlot slot t2 e2)
        (.elimOverwrittenStore slot t1 t2 e1 e2)
  | elimOverwrittenAssign (dst : RegId) (v1 v2 : Int) :
      ValidStmtDeriv
        (.seq (.assign dst (.const v1)) (.assign dst (.const v2)))
        (.assign dst (.const v2))
        (.elimOverwrittenAssign dst v1 v2)
  | foldReadOnlyCall (dst : RegId) (arg : Expr) :
      ValidStmtDeriv (.callReadOnly dst arg) (.assign dst arg) (.foldReadOnlyCall dst arg)
  | elimSkipLeft (s : Stmt) :
      ValidStmtDeriv (.seq .skip s) s (.elimSkipLeft s)
  | elimSkipRight (s : Stmt) :
      ValidStmtDeriv (.seq s .skip) s (.elimSkipRight s)
  | elimDbgValue (r : RegId) (metaId : Nat) :
      ValidStmtDeriv (.dbgValue r metaId) .skip (.elimDbgValue r metaId)
  | elimAssumeOverflowUB (r : RegId) (limit : Int) :
      ValidStmtDeriv (.assumeNoOverflowUB r limit) .skip (.elimAssumeOverflowUB r limit)
  | elimAssumeNonNegUB (r : RegId) :
      ValidStmtDeriv (.assumeKnownNonNegUB r) .skip (.elimAssumeNonNegUB r)
  | foldIfZeroTrue (thenBr elseBr : Stmt) :
      ValidStmtDeriv (.ifZeroCond 0 thenBr elseBr) thenBr (.foldIfZeroTrue thenBr elseBr)
  | seqCong {s1 t1 s2 t2 : Stmt} {d1 d2 : StmtDeriv}
      (h1 : ValidStmtDeriv s1 t1 d1) (h2 : ValidStmtDeriv s2 t2 d2) :
      ValidStmtDeriv (.seq s1 s2) (.seq t1 t2) (.seqCong d1 d2)

end RuleSynth
