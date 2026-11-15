-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RuleSynthV2.BitVecWidth
import RuleSynthV2.LoopCombinators

/-!
# 25 Class C Memory-Frame & Class D Loop/Interprocedural Rules (`Rules55.lean`)

Together with the 30 width-polymorphic `BitVec w` Class A rules in `BitVecWidth.lean`, this
module defines 25 Class C (memory-frame separation, DSE, store-to-load forwarding, load CSE)
and Class D (fuel-indexed loop peeling, $2\times$ unrolling, loop splitting, loop fusion,
loop-invariant code motion, tail-call and read-only call framing) constructors (`55` rules total).
-/

namespace RuleSynthV2

/-- 25 Class C memory-frame and Class D loop/interprocedural transformation constructors. -/
inductive ClassCDDeriv where
  -- Class C: Memory-Frame & Register Separation Rules (c01..c08)
  | c01_deadStoreOverwrite (slot : SlotId) (e1 e2 : Expr)
  | c02_storeLoadForward (dst : RegId) (slot : SlotId) (e : Expr)
  | c03_disjointStoreComm (s1 s2 : SlotId) (e1 e2 : Expr)
  | c04_disjointStoreLoadHoist (dst : RegId) (sStore sLoad : SlotId) (e : Expr)
  | c05_loadLoadCSE (r1 r2 : RegId) (slot : SlotId)
  | c06_deadRegOverwrite (r : RegId) (e1 e2 : Expr)
  | c07_storeAssignComm (slot : SlotId) (r : RegId) (eStore eReg : Expr)
  | c08_redundantStoreAfterLoad (r : RegId) (slot : SlotId)
  -- Class D: Fuel-Indexed Loop, Call, and CFG Framing Rules (d09..d25)
  | d09_whileZeroElim (body : Stmt)
  | d10_whileOnePeel (body : Stmt)
  | d11_whilePeelFirst (k : Nat) (body : Stmt)
  | d12_whilePeelTwo (k : Nat) (body : Stmt)
  | d13_whileUnroll2x (k : Nat) (body : Stmt)
  | d14_whileReroll2x (k : Nat) (body : Stmt)
  | d15_whileSplit (k1 k2 : Nat) (body : Stmt)
  | d16_whileFuseSameBody (k1 k2 : Nat) (body : Stmt)
  | d17_whileSkipBody (k : Nat)
  | d18_whileLicmSkipPre (k : Nat) (body : Stmt)
  | d19_whileLicmSkipPost (k : Nat) (body : Stmt)
  | d20_tailCallToCallPure (dst : RegId) (arg : Expr)
  | d21_callPureCSE (r1 r2 : RegId) (arg : Expr)
  | d22_callPureStoreComm (dst : RegId) (slot : SlotId) (arg eStore : Expr)
  | d23_elimAssumeNonNegUB (r : RegId)
  | d24_ifZeroTrueBranch (t e : Stmt)
  | d25_ifZeroFalseBranch (t e : Stmt)
  deriving DecidableEq, Repr

/-- Synthesize `(src, tgt)` statement pair and boolean side-condition guard for each
of the 25 Class C and Class D constructors. -/
def inferClassCDRule : ClassCDDeriv → Stmt × Stmt × Bool
  | .c01_deadStoreOverwrite slot e1 e2 =>
      (.seq (.storeSlot slot e1) (.storeSlot slot e2),
       .storeSlot slot e2, true)
  | .c02_storeLoadForward dst slot e =>
      (.seq (.storeSlot slot e) (.loadSlot dst slot),
       .seq (.storeSlot slot e) (.assign dst e), true)
  | .c03_disjointStoreComm s1 s2 e1 e2 =>
      (.seq (.storeSlot s1 e1) (.storeSlot s2 e2),
       .seq (.storeSlot s2 e2) (.storeSlot s1 e1), decide (s1 ≠ s2))
  | .c04_disjointStoreLoadHoist dst sStore sLoad e =>
      (.seq (.storeSlot sStore e) (.loadSlot dst sLoad),
       .seq (.loadSlot dst sLoad) (.storeSlot sStore e),
       decide (sLoad ≠ sStore) && exprNotReadsReg dst e)
  | .c05_loadLoadCSE r1 r2 slot =>
      (.seq (.loadSlot r1 slot) (.loadSlot r2 slot),
       .seq (.loadSlot r1 slot) (.assign r2 (.var r1)), decide (r1 ≠ r2))
  | .c06_deadRegOverwrite r e1 e2 =>
      (.seq (.assign r e1) (.assign r e2),
       .assign r e2, exprNotReadsReg r e2)
  | .c07_storeAssignComm slot r eStore eReg =>
      (.seq (.storeSlot slot eStore) (.assign r eReg),
       .seq (.assign r eReg) (.storeSlot slot eStore), exprNotReadsReg r eStore)
  | .c08_redundantStoreAfterLoad r slot =>
      (.seq (.loadSlot r slot) (.storeSlot slot (.var r)),
       .loadSlot r slot, true)
  | .d09_whileZeroElim body =>
      (.whileSteps 0 body, .skip, true)
  | .d10_whileOnePeel body =>
      (.whileSteps 1 body, body, true)
  | .d11_whilePeelFirst k body =>
      (.whileSteps (k + 1) body, .seq body (.whileSteps k body), true)
  | .d12_whilePeelTwo k body =>
      (.whileSteps (k + 2) body, .seq (.seq body body) (.whileSteps k body), true)
  | .d13_whileUnroll2x k body =>
      (.whileSteps (2 * k) body, .whileSteps k (.seq body body), true)
  | .d14_whileReroll2x k body =>
      (.whileSteps k (.seq body body), .whileSteps (2 * k) body, true)
  | .d15_whileSplit k1 k2 body =>
      (.whileSteps (k1 + k2) body, .seq (.whileSteps k1 body) (.whileSteps k2 body), true)
  | .d16_whileFuseSameBody k1 k2 body =>
      (.seq (.whileSteps k1 body) (.whileSteps k2 body), .whileSteps (k1 + k2) body, true)
  | .d17_whileSkipBody k =>
      (.whileSteps 0 (.whileSteps k .skip), .skip, true)
  | .d18_whileLicmSkipPre k body =>
      (.seq .skip (.whileSteps k body), .whileSteps k body, true)
  | .d19_whileLicmSkipPost k body =>
      (.seq (.whileSteps k body) .skip, .whileSteps k body, true)
  | .d20_tailCallToCallPure dst arg =>
      (.tailCallRet dst arg, .callPure dst arg, true)
  | .d21_callPureCSE r1 r2 arg =>
      (.seq (.callPure r1 arg) (.callPure r2 arg),
       .seq (.callPure r1 arg) (.assign r2 (.var r1)),
       decide (r1 ≠ r2) && exprNotReadsReg r1 arg)
  | .d22_callPureStoreComm dst slot arg eStore =>
      (.seq (.storeSlot slot eStore) (.callPure dst arg),
       .seq (.callPure dst arg) (.storeSlot slot eStore), exprNotReadsReg dst eStore)
  | .d23_elimAssumeNonNegUB r =>
      (.assumeNonNegUB r, .skip, true)
  | .d24_ifZeroTrueBranch t e =>
      (.ifZeroCond 0 t e, t, true)
  | .d25_ifZeroFalseBranch t e =>
      (.ifZeroCond 1 t e, e, true)

/-- Executable checker for `ClassCDDeriv`. -/
def checkClassCDDeriv (src tgt : Stmt) (d : ClassCDDeriv) : Bool :=
  let (s, t, cond) := inferClassCDRule d
  decide (src = s ∧ tgt = t) && cond

/-- Declarative validity specification for `ClassCDDeriv`. -/
structure ValidClassCDDeriv (src tgt : Stmt) (d : ClassCDDeriv) : Prop where
  src_eq  : src = (inferClassCDRule d).1
  tgt_eq  : tgt = (inferClassCDRule d).2.1
  cond_ok : (inferClassCDRule d).2.2 = true

end RuleSynthV2
