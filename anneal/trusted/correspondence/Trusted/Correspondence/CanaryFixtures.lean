-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# Correspondence Canary Fixtures (`Trusted.Correspondence.CanaryFixtures`)

Concrete programs and queries (`D6`–`D9`) referenced by the locked Pass 2
correspondence canary claims in `Trusted.Correspondence`.

`D6`–`D9` are self-consistency canaries of Anneal's deliberately stricter
move-deinitialization rule (`deinitMovedPlace := true` in `refExecutionConfig`,
verified by `MiriMoveDeinitWiringClaim`): `eval_operand` at `rustc@8144389c`
evaluates `Move` like `Copy`, so these canaries check that $M_{\text{anneal}}$
and $M_{\text{ref}}$ agree on the stricter rule rather than anchoring either
model independently against upstream Miri or MiniRust.
-/

/-- `D6` (Use-After-Move UB):
`_2 = move _1; _0 = copy _1; return` deinitializes `_1` on `move _1` and
faults with `.fault .undefined` (`.ub` in $M_{\text{ref}}$) on the subsequent
`copy _1`. -/
noncomputable def progUseAfterMoveD6 : Program where
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Input query `(42u32)` for canaries `D6`–`D8`. -/
noncomputable def queryU32_42 : Query where
  args := [u32Val 42]

/-- `D7a` (`BinaryOp` left-to-right `copy _1` then `move _1` succeeds):
`_0 = BinOp(Add, copy _1, move _1); return` reads `_1` in `lhs`, then reads
and deinitializes `_1` in `rhs`, and returns `84`. -/
noncomputable def progBinOpCopyThenMoveD7a : Program where
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩) (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D7b` (`BinaryOp` left-to-right `move _1` then `copy _1` faults with UB):
`_0 = BinOp(Add, move _1, copy _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = copy _1`. -/
noncomputable def progBinOpMoveThenCopyD7b : Program where
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.move ⟨1, []⟩) (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D7c` (`BinaryOp` left-to-right `move _1` then `move _1` faults with UB):
`_0 = BinOp(Add, move _1, move _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = move _1`. -/
noncomputable def progBinOpMoveThenMoveD7c : Program where
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.move ⟨1, []⟩) (.move ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D8` (Self-move `_1 = move _1` preserves initialized value):
`_1 = move _1; _0 = copy _1; return` reads `42` from `_1`, deinitializes `_1`
to `.immediate none`, and then writes `42` back into `_1`, so the subsequent
`_0 = copy _1` succeeds and returns `42`. -/
noncomputable def progSelfMoveD8 : Program where
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨1, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- `D9` (Move of 0-Byte ZST `MirTy.unit` Remains Initialized):
`_2 = move _1; _0 = copy _1; return` where `_1 : ()` sets `_1` to
`liveUninitSlot .unit = .immediate (some .unit)`, so subsequent `_0 = copy _1`
succeeds and returns `.unit`. -/
noncomputable def progMoveUnitZstD9 : Program where
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit, .unit, .unit]
    basicBlocks := [{
      statements := [
        .assign ⟨2, []⟩ (.use (.move ⟨1, []⟩)),
        .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))
      ]
      terminator := .return_
    }]
  }]

/-- Input query `(19u16)` for `D17` intra-crate direct `.call`. -/
noncomputable def queryU16_19 : Query where
  args := [scalarNatVal .i16 false 19]

/-- `D17a` (Multi-frame intra-crate `.call` push and return):
body `0` calls body `1` with `copy _1`, adding `23u16` and returning `42u16`. -/
noncomputable def progDirectCallD17 : Program where
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies :=
    [{
      identity := "canary::d17_call_caller"
      argumentCount := 1
      locals := [.int .i16 false, .int .i16 false]
      basicBlocks := [
        {
          statements := []
          terminator := .call 1 [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .continue_
        },
        {
          statements := []
          terminator := .return_
        }
      ]
    },
    {
      identity := "canary::d17_call_callee"
      argumentCount := 1
      locals := [.int .i16 false, .int .i16 false]
      basicBlocks := [{
        statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨1, []⟩)
            (.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 23)⟩))
        ]
        terminator := .return_
      }]
    }]

/-- `D17b` (`.sysrootCall` `uncheckedAdd` in-bounds on `u16`):
computes `19u16 + 23u16 = 42u16` across frame push/return. -/
noncomputable def progSysrootUncheckedAddOkD17 : Program where
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "canary::d17_sysroot_ok"
    argumentCount := 0
    locals := [.int .i16 false]
    basicBlocks := [
      {
        statements := []
        terminator := .sysrootCall
          { kind := .uncheckedAdd, width := .i16, signed := false }
          [.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 19)⟩,
           .constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 23)⟩]
          ⟨0, []⟩ (some 1) .continue_
      },
      {
        statements := []
        terminator := .return_
      }
    ]
  }]

/-- `D17c` (`.sysrootCall` `uncheckedAdd` overflow UB on `u16`):
`65500u16 + 100u16` faults `.undefined` / `.ub` in both machines. -/
noncomputable def progSysrootUncheckedAddUbD17 : Program where
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "canary::d17_sysroot_ub"
    argumentCount := 0
    locals := [.int .i16 false]
    basicBlocks := [
      {
        statements := []
        terminator := .sysrootCall
          { kind := .uncheckedAdd, width := .i16, signed := false }
          [.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 65500)⟩,
           .constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 100)⟩]
          ⟨0, []⟩ (some 1) .continue_
      },
      {
        statements := []
        terminator := .return_
      }
    ]
  }]

end Trusted.Correspondence
