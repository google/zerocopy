-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import RegAllocCert.Semantics

namespace RegAllocCert

/-- Check that a spill slot lies strictly within `[0, frameSize)` with positive byte size. -/
def checkSpillInBounds (frameSize : Nat) (s : SpillSlot) : Bool :=
  decide (0 < s.sizeBytes ∧ s.offset + s.sizeBytes ≤ frameSize)

/-- Check that two spill slots `[o1, o1 + sz1)` and `[o2, o2 + sz2)` are byte-disjoint. -/
def checkSpillDisjoint (s1 s2 : SpillSlot) : Bool :=
  decide (s1.offset + s1.sizeBytes ≤ s2.offset ∨ s2.offset + s2.sizeBytes ≤ s1.offset)

/-- Check that all spill slots in a list lie in bounds `[0, frameSize)` and are pairwise disjoint. -/
def checkSpillListValid (frameSize : Nat) : List SpillSlot → Bool
  | [] => true
  | s :: ss =>
      checkSpillInBounds frameSize s &&
      ss.all (checkSpillDisjoint s) &&
      checkSpillListValid frameSize ss

/-- Check that a scratch/clobbered physical register `scratch` does not alias the locations of
specific virtual registers. -/
def checkScratchDisjoint2 (l1 l2 : Loc) (mode : CycleResolution) : Bool :=
  match mode with
  | .viaScratch scratch =>
      decide (Loc.preg scratch ≠ l1 ∧ Loc.preg scratch ≠ l2 ∧ l1 ≠ l2)
  | .viaXchg =>
      decide (l1 ≠ l2)

def checkScratchDisjoint3 (l1 l2 l3 : Loc) (scratch : PReg) : Bool :=
  let sLoc := Loc.preg scratch
  decide (sLoc ≠ l1 ∧ sLoc ≠ l2 ∧ sLoc ≠ l3 ∧ l1 ≠ l2 ∧ l1 ≠ l3 ∧ l2 ≠ l3)

/-- Per-instruction certificate witness for `RegAlloc2`-style lowering (`MiniSSA → MiniMach`). -/
inductive InstCert where
  | constI (dst : VReg) (val : Int)
  | binOp  (op : BinOp) (dst lhs rhs : VReg)
  | copyVReg (dst src : VReg)
  | parSwap2 (v1 v2 : VReg) (mode : CycleResolution)
  | parRotate3 (v1 v2 v3 : VReg) (scratch : PReg)
  | callClobber (dst arg : VReg) (delta : Int) (clob : PReg)
  | assertBoundsPanic (v : VReg) (bound : Int)
  | assumeNonNegUB (v : VReg)
  | seq (c1 c2 : InstCert)
  deriving DecidableEq, Repr

/-- Synthesize the verified `(SSAInst × MachInst)` pair from an `InstCert` under allocation
map `alloc : VReg → Loc`. Following `PITFALL-3` from `W6Proto`, functional endpoint synthesis
eliminates nested `match` splitters and makes completeness 1-line per constructor. -/
def inferInstPair (alloc : VReg → Loc) : InstCert → SSAInst × MachInst
  | .constI dst val =>
      (.constI dst val, .constLoc (alloc dst) val)
  | .binOp op dst lhs rhs =>
      (.binOp op dst lhs rhs, .binOpLoc op (alloc dst) (alloc lhs) (alloc rhs))
  | .copyVReg dst src =>
      (.copyVReg dst src, .moveLoc (alloc dst) (alloc src))
  | .parSwap2 v1 v2 mode =>
      (.parSwap2 v1 v2, .swap2Loc (alloc v1) (alloc v2) mode)
  | .parRotate3 v1 v2 v3 scratch =>
      (.parRotate3 v1 v2 v3, .rotate3Scratch (alloc v1) (alloc v2) (alloc v3) scratch)
  | .callClobber dst arg delta clob =>
      (.callClobber dst arg delta clob, .callClobberLoc (alloc dst) (alloc arg) delta clob)
  | .assertBoundsPanic v bound =>
      (.assertBoundsPanic v bound, .assertBoundsPanicLoc (alloc v) bound)
  | .assumeNonNegUB v =>
      (.assumeNonNegUB v, .assumeNonNegUBLoc (alloc v))
  | .seq c1 c2 =>
      let (s1, m1) := inferInstPair alloc c1
      let (s2, m2) := inferInstPair alloc c2
      (.seq s1 s2, .seq m1 m2)

/-- Check side conditions on an `InstCert` under `alloc : VReg → Loc` and reserved
scratch/clobber register `reservedScratch`:
- For `parSwap2`, the cycle-resolution scratch register must not alias `alloc v1` or `alloc v2`;
- For `parRotate3`, `Loc.preg scratch` must equal `Loc.preg reservedScratch` and not alias `v1, v2, v3`;
- For `callClobber`, `clob` must either be overwritten by `alloc dst` or equal `reservedScratch`. -/
def checkCertSideConds (alloc : VReg → Loc) (reservedScratch : PReg) : InstCert → Bool
  | .constI _ _ => true
  | .binOp _ _ _ _ => true
  | .copyVReg _ _ => true
  | .parSwap2 v1 v2 mode =>
      checkScratchDisjoint2 (alloc v1) (alloc v2) mode &&
      match mode with
      | .viaScratch s => decide (s = reservedScratch)
      | .viaXchg      => true
  | .parRotate3 v1 v2 v3 scratch =>
      checkScratchDisjoint3 (alloc v1) (alloc v2) (alloc v3) scratch &&
      decide (scratch = reservedScratch)
  | .callClobber _dst _arg _delta clob =>
      decide (clob = reservedScratch)
  | .assertBoundsPanic _ _ => true
  | .assumeNonNegUB _ => true
  | .seq c1 c2 =>
      checkCertSideConds alloc reservedScratch c1 &&
      checkCertSideConds alloc reservedScratch c2

/-- Executable instruction-level certificate checker `checkInstCert`. -/
def checkInstCert
    (alloc : VReg → Loc) (reservedScratch : PReg)
    (ssa : SSAInst) (mach : MachInst) (cert : InstCert) : Bool :=
  let (sExpected, mExpected) := inferInstPair alloc cert
  decide (ssa = sExpected ∧ mach = mExpected) &&
  checkCertSideConds alloc reservedScratch cert

/-- Check ABI prologue/epilogue callee-saved register matching and spill-slot bounds. -/
def checkABICalleeSaved (frameSize : Nat) (saves restores : List (PReg × SpillSlot)) : Bool :=
  decide (saves = restores) &&
  checkSpillListValid frameSize (saves.map Prod.snd)

/-- Top-level `RegAllocCert` certificate bundle for a function `MiniSSA → MiniMach`. -/
structure RegAllocCertBundle where
  alloc           : VReg → Loc
  reservedScratch : PReg
  spillSlots      : List SpillSlot
  bodyCert        : InstCert

/-- Total, linear-time executable certificate checker `checkRegAllocCert`. -/
def checkRegAllocCert
    (ssaFn : SSAFunc) (machFn : MachFunc) (cert : RegAllocCertBundle) : Bool :=
  decide (cert.alloc ssaFn.argVReg = machFn.argLoc ∧
          cert.alloc ssaFn.retVReg = machFn.retLoc) &&
  checkSpillListValid machFn.frameSize cert.spillSlots &&
  checkABICalleeSaved machFn.frameSize machFn.calleeSaved machFn.epilogueRestores &&
  checkInstCert cert.alloc cert.reservedScratch ssaFn.body machFn.body cert.bodyCert

end RegAllocCert
