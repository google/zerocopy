-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import W6Proto.Derivations

namespace W6Proto

/-- Synthesize the verified source and target expressions of an `ExprRewrite`. -/
def inferExprRewrite : ExprRewrite → Expr × Expr
  | .refl e => (e, e)
  | .addZeroRight e => (.add e (.const 0), e)
  | .addZeroLeft e => (.add (.const 0) e, e)
  | .subSelf e => (.sub e e, .const 0)
  | .mulOneRight e => (.mul e (.const 1), e)
  | .constAdd a b => (.add (.const a) (.const b), .const (a + b))
  | .constMul a b => (.mul (.const a) (.const b), .const (a * b))
  | .congAdd r1 r2 =>
      let (s1, t1) := inferExprRewrite r1
      let (s2, t2) := inferExprRewrite r2
      (.add s1 s2, .add t1 t2)
  | .congSub r1 r2 =>
      let (s1, t1) := inferExprRewrite r1
      let (s2, t2) := inferExprRewrite r2
      (.sub s1 s2, .sub t1 t2)
  | .congMul r1 r2 =>
      let (s1, t1) := inferExprRewrite r1
      let (s2, t2) := inferExprRewrite r2
      (.mul s1 s2, .mul t1 t2)

/-- Decidable boolean checker for expression rewrites. -/
def checkExprRewrite (src tgt : Expr) (rw : ExprRewrite) : Bool :=
  let (s, t) := inferExprRewrite rw
  decide (s = src ∧ t = tgt)

/-- Decidable side condition: expression `e` does not read register `r`. -/
def exprNotReadsReg (r : RegId) : Expr → Bool
  | .const _ => true
  | .var r' => decide (r' ≠ r)
  | .add a b => exprNotReadsReg r a && exprNotReadsReg r b
  | .sub a b => exprNotReadsReg r a && exprNotReadsReg r b
  | .mul a b => exprNotReadsReg r a && exprNotReadsReg r b

/-- Decidable side condition: disjoint `noalias` tags and distinct slots. -/
def checkDisjointNoAlias (s1 s2 : SlotId) (t1 t2 : AliasTag) : Bool :=
  decide (s1 ≠ s2 ∧ t1 ≠ t2)

/-- Executable boolean derivation checker for statements. -/
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
  | .elimOverwrittenStore slot t1 t2 e1 e2 =>
      decide (src = .seq (.storeSlot slot t1 e1) (.storeSlot slot t2 e2) ∧
              tgt = .storeSlot slot t2 e2)
  | .elimSkipLeft s =>
      decide (src = .seq .skip s ∧ tgt = s)
  | .elimSkipRight s =>
      decide (src = .seq s .skip ∧ tgt = s)
  | .elimAssumeUB r limit =>
      decide (src = .assumeNoOverflowUB r limit ∧ tgt = .skip)
  | .seqCong d1 d2 =>
      match src, tgt with
      | .seq s1 s2, .seq t1 t2 => checkStmtDeriv s1 t1 d1 && checkStmtDeriv s2 t2 d2
      | _, _ => false
  | .trans mid d1 d2 =>
      checkStmtDeriv src mid d1 && checkStmtDeriv mid tgt d2

/-- Top-level executable derivation checker `checkDeriv`. -/
def checkDeriv (src tgt : Prog) (d : Derivation) : Bool :=
  decide (src.retReg = d.retReg ∧ tgt.retReg = d.retReg) &&
  checkStmtDeriv src.body tgt.body d.bodyDeriv

end W6Proto
