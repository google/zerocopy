-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Trusted.MirAst
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.SccSharding.BinChunkTree
public import Anneal.SccSharding.InterprocCallModel

public section

/-!
# Interprocedural Mutual-Recursion Canary over `BinChunkTree`

Kernel-checked canary exercising multi-frame `TerminatorKind.call` push/return
execution (`InterprocReturns` / `InterprocExecutes`) over a balanced 3-shard
`BinChunkTree Body` containing:
1. Leaf helper `leaf_base` (`DefId = 0`) in `Shard_000`;
2. 2-body mutual recursion `even_step <-> odd_step` (`DefId = 1, 2`) in
   `Shard_001` calling down into `Shard_000`; and
3. 3-body mutual recursion ring `ring_a -> ring_b -> ring_c -> ring_a`
   (`DefId = 3, 4, 5`) in `Shard_002` calling down into `Shard_001`.

As noted in `InterprocCallModel`, this canary exercises the standalone zero-TCB
interprocedural evaluator over `BinChunkTree` call dispatch.
-/

namespace Anneal.SccSharding.Canary

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp Anneal.SccSharding

@[expose] def canaryU8Ty : MirTy := .int .i8 false

@[expose] def constU8 (n : Nat) : Operand :=
  .constant ⟨canaryU8Ty, .scalar (BitVec.ofNat 128 n)⟩

@[expose] def sc8 (n : Nat) : Val :=
  .scalar ⟨.i8, false, BitVec.ofNat 128 n⟩

@[expose] def idLeaf : String :=
  String.ofList [
    Char.ofNat 108, Char.ofNat 101,
    Char.ofNat 97, Char.ofNat 102]

@[expose] def idEven : String :=
  String.ofList [
    Char.ofNat 101, Char.ofNat 118,
    Char.ofNat 101, Char.ofNat 110]

@[expose] def idOdd : String :=
  String.ofList [
    Char.ofNat 111, Char.ofNat 100, Char.ofNat 100]

@[expose] def idRingA : String :=
  String.ofList [Char.ofNat 114, Char.ofNat 97]

@[expose] def idRingB : String :=
  String.ofList [Char.ofNat 114, Char.ofNat 98]

@[expose] def idRingC : String :=
  String.ofList [Char.ofNat 114, Char.ofNat 99]

/-- `DefId = 0` (`Shard_000`, leaf): returns `10 : u8`. -/
@[expose] def body_leaf_base : Body := {
  argumentCount := 0,
  isUnsafe := false,
  locals := [canaryU8Ty],
  basicBlocks := [
    { statements := [.assign ⟨0, []⟩ (.use (constU8 10))],
      terminator := .return_,
      cleanup := false }
  ],
  identity := idLeaf
}

/-- `DefId = 1` (`Shard_001`, 2-cycle member A):
`even_step(n)`: if `n == 0` call `leaf_base()` (`DefId 0`) and return;
else call `odd_step(n - 1)` (`DefId 2`), add `1`, and return. -/
@[expose] def body_even_step : Body := {
  argumentCount := 1,
  isUnsafe := false,
  locals := [canaryU8Ty, canaryU8Ty, canaryU8Ty],
  basicBlocks := [
    { statements := [],
      terminator := .switchInt (.copy ⟨1, []⟩) ⟨[(BitVec.ofNat 128 0, 1)], 2⟩,
      cleanup := false },
    { statements := [],
      terminator := .call 0 [] ⟨0, []⟩ (some 4) .continue_,
      cleanup := false },
    { statements := [
        .assign ⟨2, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩) (constU8 1))
      ],
      terminator := .call 2 [.copy ⟨2, []⟩] ⟨0, []⟩ (some 3) .continue_,
      cleanup := false },
    { statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (constU8 1))
      ],
      terminator := .goto 4,
      cleanup := false },
    { statements := [],
      terminator := .return_,
      cleanup := false }
  ],
  identity := idEven
}

/-- `DefId = 2` (`Shard_001`, 2-cycle member B):
`odd_step(n)`: if `n == 0` return `0`;
else call `even_step(n - 1)` (`DefId 1`), add `2`, and return. -/
@[expose] def body_odd_step : Body := {
  argumentCount := 1,
  isUnsafe := false,
  locals := [canaryU8Ty, canaryU8Ty, canaryU8Ty],
  basicBlocks := [
    { statements := [],
      terminator := .switchInt (.copy ⟨1, []⟩) ⟨[(BitVec.ofNat 128 0, 1)], 2⟩,
      cleanup := false },
    { statements := [.assign ⟨0, []⟩ (.use (constU8 0))],
      terminator := .return_,
      cleanup := false },
    { statements := [
        .assign ⟨2, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩) (constU8 1))
      ],
      terminator := .call 1 [.copy ⟨2, []⟩] ⟨0, []⟩ (some 3) .continue_,
      cleanup := false },
    { statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (constU8 2))
      ],
      terminator := .return_,
      cleanup := false }
  ],
  identity := idOdd
}

/-- `DefId = 3` (`Shard_002`, 3-cycle member A):
`ring_a(k)`: if `k == 0` call `even_step(2)` (`DefId 1`, cross-shard) else
`ring_b(k - 1)`. -/
@[expose] def body_ring_a : Body := {
  argumentCount := 1,
  isUnsafe := false,
  locals := [canaryU8Ty, canaryU8Ty, canaryU8Ty],
  basicBlocks := [
    { statements := [],
      terminator := .switchInt (.copy ⟨1, []⟩) ⟨[(BitVec.ofNat 128 0, 1)], 2⟩,
      cleanup := false },
    { statements := [],
      terminator := .call 1 [constU8 2] ⟨0, []⟩ (some 3) .continue_,
      cleanup := false },
    { statements := [
        .assign ⟨2, []⟩ (.binaryOp .sub (.copy ⟨1, []⟩) (constU8 1))
      ],
      terminator := .call 4 [.copy ⟨2, []⟩] ⟨0, []⟩ (some 3) .continue_,
      cleanup := false },
    { statements := [],
      terminator := .return_,
      cleanup := false }
  ],
  identity := idRingA
}

/-- `DefId = 4` (`Shard_002`, 3-cycle member B): calls `ring_c(k)` (`DefId 5`).
-/
@[expose] def body_ring_b : Body := {
  argumentCount := 1,
  isUnsafe := false,
  locals := [canaryU8Ty, canaryU8Ty],
  basicBlocks := [
    { statements := [],
      terminator := .call 5 [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .continue_,
      cleanup := false },
    { statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (constU8 5))
      ],
      terminator := .return_,
      cleanup := false }
  ],
  identity := idRingB
}

/-- `DefId = 5` (`Shard_002`, 3-cycle member C): closes 3-cycle
`ring_c -> ring_a` (`DefId 3`). -/
@[expose] def body_ring_c : Body := {
  argumentCount := 1,
  isUnsafe := false,
  locals := [canaryU8Ty, canaryU8Ty],
  basicBlocks := [
    { statements := [],
      terminator := .call 3 [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .continue_,
      cleanup := false },
    { statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (constU8 7))
      ],
      terminator := .return_,
      cleanup := false }
  ],
  identity := idRingC
}

@[expose] def shard0Tree : BinChunkTree Body := .leaf body_leaf_base

@[expose] def shard1Tree : BinChunkTree Body :=
  .branch 1 (.leaf body_even_step) (.leaf body_odd_step)

@[expose] def shard2Tree : BinChunkTree Body :=
  .branch 1 (.leaf body_ring_a)
    (.branch 1 (.leaf body_ring_b) (.leaf body_ring_c))

@[expose] def crateCallTree : BinChunkTree Body :=
  .branch 3 (.branch 1 shard0Tree shard1Tree) shard2Tree

theorem crateCallTree_wf : BinChunkTree.wf crateCallTree = true := rfl

-- Normalized multi-frame checkpoints (2-3 transitions per `rfl`):

private def mkFrame (d : DefId) (b : BasicBlockId) (s : Nat)
    (l : List LocalSlot) : FrameState :=
  { defId := d, blockIdx := b, stmtIdx := s, locals := l }

private noncomputable def st_e0 : CallStackState :=
  CallStackState.mk
    (mkFrame 1 0 0
      (initLocalsLoop body_even_step [sc8 2] 0 body_even_step.locals))
    [] entryMemory

private noncomputable def st_e1 : CallStackState :=
  CallStackState.mk
    (mkFrame 2 0 0
      [.immediate none, .immediate (some (sc8 1)), .immediate none])
    [SavedCallerFrame.mk 1 0 3
      [.immediate none, .immediate (some (sc8 2)), .immediate (some (sc8 1))]]
    entryMemory

private noncomputable def st_e2 : CallStackState :=
  CallStackState.mk
    (mkFrame 1 0 0
      [.immediate none, .immediate (some (sc8 0)), .immediate none])
    [SavedCallerFrame.mk 2 0 3
      [.immediate none, .immediate (some (sc8 1)), .immediate (some (sc8 0))],
     SavedCallerFrame.mk 1 0 3
      [.immediate none, .immediate (some (sc8 2)), .immediate (some (sc8 1))]]
    entryMemory

private noncomputable def st_e3 : CallStackState :=
  CallStackState.mk
    (mkFrame 0 0 0 [.immediate none])
    (SavedCallerFrame.mk 1 0 4
      [.immediate none, .immediate (some (sc8 0)), .immediate none] ::
      st_e2.callers)
    entryMemory

private noncomputable def st_e4 : CallStackState :=
  CallStackState.mk
    (mkFrame 2 3 0
      [.immediate (some (sc8 10)), .immediate (some (sc8 1)),
       .immediate (some (sc8 0))])
    st_e1.callers
    entryMemory

private noncomputable def st_e5 : CallStackState :=
  CallStackState.mk
    (mkFrame 1 3 0
      [.immediate (some (sc8 12)), .immediate (some (sc8 2)),
       .immediate (some (sc8 1))])
    []
    entryMemory

private theorem seg_e_1 :
    stepInterprocFuel crateCallTree 3 st_e0 = .step st_e1 := rfl
private theorem seg_e_2 :
    stepInterprocFuel crateCallTree 3 st_e1 = .step st_e2 := rfl
private theorem seg_e_3 :
    stepInterprocFuel crateCallTree 2 st_e2 = .step st_e3 := rfl
private theorem seg_e_4 :
    stepInterprocFuel crateCallTree 3 st_e3 = .step st_e4 := rfl
private theorem seg_e_5 :
    stepInterprocFuel crateCallTree 2 st_e4 = .step st_e5 := rfl
private theorem seg_e_6 :
    stepInterprocFuel crateCallTree 3 st_e5 = .done (sc8 13) := rfl

/-- Kernel-checked 2-cycle and cross-shard call execution (`16` transitions):
`even_step(2) -> odd_step(1) -> even_step(0) -> leaf_base() = 10`, returning
`10 + 2 + 1 = 13`. -/
theorem canary_2cycle_even_2 :
    InterprocRuns crateCallTree 16 1 [sc8 2] (sc8 13) :=
  interprocExecutes_of_fuel3 seg_e_1
    (interprocExecutes_of_fuel3 seg_e_2
      (interprocExecutes_of_fuel2 seg_e_3
        (interprocExecutes_of_fuel3 seg_e_4
          (interprocExecutes_of_fuel2 seg_e_5
            (interprocExecutes_done_fuel3 seg_e_6)))))

-- 3-cycle ring `ring_a(1) -> ring_b(0) -> ring_c(0) -> ring_a(0) ->
-- even_step(2) = 13 -> +7 -> +5 = 25`:

private noncomputable def st_r0 : CallStackState :=
  CallStackState.mk
    (mkFrame 3 0 0
      (initLocalsLoop body_ring_a [sc8 1] 0 body_ring_a.locals))
    [] entryMemory

private noncomputable def st_r1 : CallStackState :=
  CallStackState.mk
    (mkFrame 4 0 0 [.immediate none, .immediate (some (sc8 0))])
    [SavedCallerFrame.mk 3 0 3
      [.immediate none, .immediate (some (sc8 1)), .immediate (some (sc8 0))]]
    entryMemory

private def cs_ring_full : List SavedCallerFrame := [
  SavedCallerFrame.mk 3 0 3
    [.immediate none, .immediate (some (sc8 0)), .immediate none],
  SavedCallerFrame.mk 5 0 1 [.immediate none, .immediate (some (sc8 0))],
  SavedCallerFrame.mk 4 0 1 [.immediate none, .immediate (some (sc8 0))],
  SavedCallerFrame.mk 3 0 3
    [.immediate none, .immediate (some (sc8 1)), .immediate (some (sc8 0))]
]

private noncomputable def st_r2 : CallStackState :=
  CallStackState.mk
    (mkFrame 3 0 0
      [.immediate none, .immediate (some (sc8 0)), .immediate none])
    (cs_ring_full.drop 1)
    entryMemory

private noncomputable def st_r3 : CallStackState :=
  CallStackState.mk
    (mkFrame 1 0 0
      [.immediate none, .immediate (some (sc8 2)), .immediate none])
    cs_ring_full
    entryMemory

private noncomputable def st_r4 : CallStackState :=
  CallStackState.mk st_e1.active (st_e1.callers ++ cs_ring_full) entryMemory

private noncomputable def st_r5 : CallStackState :=
  CallStackState.mk st_e2.active (st_e2.callers ++ cs_ring_full) entryMemory

private noncomputable def st_r6 : CallStackState :=
  CallStackState.mk st_e3.active (st_e3.callers ++ cs_ring_full) entryMemory

private noncomputable def st_r7 : CallStackState :=
  CallStackState.mk st_e4.active (st_e4.callers ++ cs_ring_full) entryMemory

private noncomputable def st_r8 : CallStackState :=
  CallStackState.mk st_e5.active cs_ring_full entryMemory

private noncomputable def st_r8b : CallStackState :=
  CallStackState.mk
    (mkFrame 3 3 0
      [.immediate (some (sc8 13)), .immediate (some (sc8 0)), .immediate none])
    (cs_ring_full.drop 1)
    entryMemory

private noncomputable def st_r9 : CallStackState :=
  CallStackState.mk
    (mkFrame 5 1 0
      [.immediate (some (sc8 13)), .immediate (some (sc8 0))])
    (cs_ring_full.drop 2)
    entryMemory

private noncomputable def st_r10 : CallStackState :=
  CallStackState.mk
    (mkFrame 4 1 0
      [.immediate (some (sc8 20)), .immediate (some (sc8 0))])
    (cs_ring_full.drop 3)
    entryMemory

private theorem seg_r_1 :
    stepInterprocFuel crateCallTree 3 st_r0 = .step st_r1 := rfl
private theorem seg_r_2 :
    stepInterprocFuel crateCallTree 2 st_r1 = .step st_r2 := rfl
private theorem seg_r_3 :
    stepInterprocFuel crateCallTree 2 st_r2 = .step st_r3 := rfl
private theorem seg_r_4 :
    stepInterprocFuel crateCallTree 3 st_r3 = .step st_r4 := rfl
private theorem seg_r_5 :
    stepInterprocFuel crateCallTree 3 st_r4 = .step st_r5 := rfl
private theorem seg_r_6 :
    stepInterprocFuel crateCallTree 2 st_r5 = .step st_r6 := rfl
private theorem seg_r_7 :
    stepInterprocFuel crateCallTree 3 st_r6 = .step st_r7 := rfl
private theorem seg_r_8 :
    stepInterprocFuel crateCallTree 2 st_r7 = .step st_r8 := rfl
private theorem seg_r_9a :
    stepInterprocFuel crateCallTree 3 st_r8 = .step st_r8b := rfl
private theorem seg_r_9b :
    evalInterprocStep crateCallTree st_r8b = .step st_r9 := rfl
private theorem seg_r_10 :
    stepInterprocFuel crateCallTree 2 st_r9 = .step st_r10 := rfl
private theorem seg_r_11 :
    stepInterprocFuel crateCallTree 3 st_r10 = .done (sc8 25) := rfl

/-- Kernel-checked 3-cycle, 2-cycle, and leaf 3-shard call execution (`29`
transitions): `ring_a(1) -> ring_b(0) -> ring_c(0) -> ring_a(0) ->
even_step(2) = 13`, returning `13 + 7 + 5 = 25`. -/
theorem canary_3cycle_ring_1 :
    InterprocRuns crateCallTree 29 3 [sc8 1] (sc8 25) :=
  interprocExecutes_of_fuel3 seg_r_1
    (interprocExecutes_of_fuel2 seg_r_2
      (interprocExecutes_of_fuel2 seg_r_3
        (interprocExecutes_of_fuel3 seg_r_4
          (interprocExecutes_of_fuel3 seg_r_5
            (interprocExecutes_of_fuel2 seg_r_6
              (interprocExecutes_of_fuel3 seg_r_7
                (interprocExecutes_of_fuel2 seg_r_8
                  (interprocExecutes_of_fuel3 seg_r_9a
                    (interprocExecutes_of_step seg_r_9b
                      (interprocExecutes_of_fuel2 seg_r_10
                        (interprocExecutes_done_fuel3 seg_r_11)))))))))))

/-- Kernel-checked `rfl` canary exercising both `ByteDecisionTree.splitTag`
(`byteListTag` threshold) and `ByteDecisionTree.splitLex` (lexicographic pivot
fallback via `byteListCmp8`) on a 3-entry tag-collision set (`"AB"`, `"CA"`,
`"AC"`). -/
theorem canary_decisionTree_splitTag_and_splitLex :
    let dt : ByteDecisionTree :=
      .splitTag 198
        (.splitLex
          (List.append [(UInt8.ofNat 65)]
            [(UInt8.ofNat 66)])
          (.leaf 0)
          (.leaf 1))
        (.leaf 2)
    ByteDecisionTree.eval dt
      [UInt8.ofNat 65, UInt8.ofNat 66] = some 0 ∧
    ByteDecisionTree.eval dt
      [UInt8.ofNat 67, UInt8.ofNat 65] = some 1 ∧
    ByteDecisionTree.eval dt
      [UInt8.ofNat 65, UInt8.ofNat 67] = some 2 :=
  ⟨rfl, rfl, rfl⟩

end Anneal.SccSharding.Canary

end
