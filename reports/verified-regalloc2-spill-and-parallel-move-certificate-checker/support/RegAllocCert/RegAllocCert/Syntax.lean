-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

namespace RegAllocCert

/-- Virtual register identifier in `MiniSSA`. -/
abbrev VReg := Nat

/-- Physical register bank in `MiniMach`: 16 GPRs and 16 XMMs. -/
inductive PRegBank where
  | gpr
  | xmm
  deriving DecidableEq, Repr

/-- Physical register in `MiniMach` (0..15 within bank). -/
structure PReg where
  bank : PRegBank
  idx  : Nat
  deriving DecidableEq, Repr

/-- Stack frame spill slot `[offset, offset + sizeBytes)` within `[0, frameSize)`. -/
structure SpillSlot where
  offset    : Nat
  sizeBytes : Nat
  deriving DecidableEq, Repr

/-- Allocation location for a virtual register: physical register or stack spill slot. -/
inductive Loc where
  | preg  (p : PReg)
  | spill (s : SpillSlot)
  deriving DecidableEq, Repr

/-- Binary ALU operation shared between `MiniSSA` and `MiniMach`. -/
inductive BinOp where
  | add
  | sub
  | mul
  | bitAnd
  | bitXor
  deriving DecidableEq, Repr

/-- Parallel-move cycle resolution strategy in `MiniMach`:
- `viaScratch`: breaks a 2-register or 3-register cycle using a dedicated caller-saved scratch
  register (`saveScratch`, `mov`, `loadScratch`);
- `viaXchg`: breaks a 2-register cycle in-place using hardware `xchg`. -/
inductive CycleResolution where
  | viaScratch (scratch : PReg)
  | viaXchg
  deriving DecidableEq, Repr

/-- `MiniSSA` instruction stream with virtual registers, live-range split moves,
parallel 2-cycle and 3-cycle edge swaps ($\phi$-nodes), calls with caller-saved clobbers,
checked bounds panics (`Outcome.panic`), and UB assumptions (`Outcome.ub`). -/
inductive SSAInst where
  | constI (dst : VReg) (val : Int)
  | binOp  (op : BinOp) (dst lhs rhs : VReg)
  | copyVReg (dst src : VReg)
  | parSwap2 (v1 v2 : VReg)
  | parRotate3 (v1 v2 v3 : VReg)
  | callClobber (dst arg : VReg) (calleeDelta : Int) (clobberedPReg : PReg)
  | assertBoundsPanic (v : VReg) (bound : Int)
  | assumeNonNegUB (v : VReg)
  | seq (i1 i2 : SSAInst)
  deriving DecidableEq, Repr

/-- `MiniMach` lowered instruction stream operating over `Loc` (`PReg ⊎ SpillSlot`),
cycle-resolved parallel moves, stack spill loads/stores, and ABI clobber masks. -/
inductive MachInst where
  | constLoc (dst : Loc) (val : Int)
  | binOpLoc (op : BinOp) (dst lhs rhs : Loc)
  | moveLoc  (dst src : Loc)
  | swap2Loc (l1 l2 : Loc) (mode : CycleResolution)
  | rotate3Scratch (l1 l2 l3 : Loc) (scratch : PReg)
  | callClobberLoc (dst arg : Loc) (calleeDelta : Int) (clobberedPReg : PReg)
  | assertBoundsPanicLoc (l : Loc) (bound : Int)
  | assumeNonNegUBLoc (l : Loc)
  | seq (m1 m2 : MachInst)
  deriving DecidableEq, Repr

/-- Complete `MiniSSA` function representation. -/
structure SSAFunc where
  argVReg : VReg
  retVReg : VReg
  body    : SSAInst
  deriving DecidableEq, Repr

/-- Complete `MiniMach` function representation with frame layout and ABI saves/restores. -/
structure MachFunc where
  frameSize        : Nat
  calleeSaved      : List (PReg × SpillSlot)
  argLoc           : Loc
  retLoc           : Loc
  body             : MachInst
  epilogueRestores : List (PReg × SpillSlot)
  deriving DecidableEq, Repr

end RegAllocCert
