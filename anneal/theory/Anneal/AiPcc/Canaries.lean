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
public import Init.Data.BitVec.BasicAux
public import Init.Data.List.Basic
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirTotal.Ops
public import Anneal.MirWp.Execution
public import Anneal.AiPcc.BitArith
public import Anneal.AiPcc.Tnum
public import Anneal.AiPcc.WrappedInterval
public import Anneal.AiPcc.ReducedProduct
public import Anneal.AiPcc.MirBridge
public import Anneal.AiPcc.MirTransfer
public import Anneal.AiPcc.MirPcc

public section

namespace Anneal.AiPcc

open Trusted.MirAst Trusted.MirSemantics Anneal.MirTotal Anneal.MirWp

/-!
# End-to-End MIR AI PCC Canaries & Negative Tests (`Anneal.AiPcc.Canaries`)

Exercises the full `Anneal.AiPcc` stack (`BitArith`, `Tnum`, `WrappedInterval`,
`ReducedProduct`, `MirBridge`, `MirTransfer`, and `MirPcc`) on concrete
`Trusted.MirAst.Body` programs:

1. Positive 64-bit 8-byte-aligned loop canary discharging `addUnchecked`,
   `subUnchecked`, `shlUnchecked`, `shrUnchecked`, and dead `.unreachable` trap
   elimination with a single loop-header cutpoint, proving unbounded-iteration
   `SafeFrom` and exact return value `1024`.
2. Positive 32-bit-to-64-bit bitmask + nonzero `div`/`rem` + `intToInt` cast
   canary proving `SafeFrom` and return value `< 2^32` (from a certified
   divisor in `[1, 255]`).
3. Positive controls, `Operand.move` aliasing, `RelGuard` preservation across
   unrelated writes, and acyclic CFG merge canaries (`switchInt` on
   `AbsVal.topInit` and straddling `WrappedInterval` diamond join).
4. Fail-closed negative regression suite rejecting unchecked overflow,
   underflow, out-of-range shift, division by zero, reachable `.unreachable`,
   uninitialized live local reads and returns, `Operand.move` use-after-move,
   clobbered `RelGuard` branch refinement, invalid/duplicate/incomplete or
   misordered `rpoOrder` schedules, `RelGuard`-carrying return invariants,
   non-inductive loop cutpoints, and `StorageDead` violations.
-/

/-- Constant `u64` MIR `Operand` constructor. -/
@[expose] def mkU64Const (n : Nat) : Operand :=
  .constant ⟨.int .i64 false, .scalar (BitVec.ofNat 128 n)⟩

/-- Constant `u32` MIR `Operand` constructor. -/
@[expose] def mkU32Const (n : Nat) : Operand :=
  .constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 n)⟩

/-- Constant `u8` MIR `Operand` constructor. -/
@[expose] def mkU8Const (n : Nat) : Operand :=
  .constant ⟨.int .i8 false, .scalar (BitVec.ofNat 128 n)⟩

/-- Unprojected `Operand.copy` constructor for `r`. -/
@[expose] def mkCopy (r : LocalId) : Operand := .copy ⟨r, []⟩

/-- Unprojected `Operand.move` constructor for `r`. -/
@[expose] def mkMove (r : LocalId) : Operand := .move ⟨r, []⟩

/-- Unprojected `Place` constructor for `r`. -/
@[expose] def mkPlace (r : LocalId) : Place := ⟨r, []⟩

/-- 64-bit 8-byte-aligned strided loop body:
- `_0 : u64` (return value)
- `_1 : u64` (stride-8 index, `0, 8, 16, ..., 1024`)
- `_2 : bool` (loop guard & post-loop equality check)
- `_3 : u64` (scratch for `addUnchecked`, `subUnchecked`, `shlUnchecked`,
  `shrUnchecked`)

After the loop exits (`_1 ≥ 1024` combined with header invariant `_1 ≤ 1024`),
`bb3` tests `_1 == 1024` and branches to a dead `.unreachable` trap at `bb4` on
`false` and normal return at `bb5` on `true`. -/
@[expose] def alignedStride8LoopBody : Body :=
  { identity := "ai_pcc_aligned_stride8_loop"
    argumentCount := 0
    locals := [.int .i64 false, .int .i64 false, .bool, .int .i64 false]
    basicBlocks := [
      -- bb0: entry
      { statements := [
          .storageLive 1,
          .assign (mkPlace 1) (.use (mkU64Const 0)),
          .storageLive 2,
          .storageLive 3
        ]
        terminator := .goto 1
        cleanup := false },
      -- bb1: loop header (single Bourdoncle cutpoint)
      { statements := [
          .assign (mkPlace 2) (.binaryOp .lt (mkCopy 1) (mkU64Const 1024))
        ]
        terminator := .switchInt (mkCopy 2) ⟨[(BitVec.ofNat 128 0, 3)], 2⟩
        cleanup := false },
      -- bb2: loop body (`_1 < 1024` and `_1 ≡ 0 (mod 8)` => `_1 ≤ 1016`)
      { statements := [
          .assign (mkPlace 3) (.binaryOp .addUnchecked (mkCopy 1) (mkU64Const 8)),
          .assign (mkPlace 3) (.binaryOp .subUnchecked (mkCopy 3) (mkU64Const 8)),
          .assign (mkPlace 3) (.binaryOp .shlUnchecked (mkCopy 1) (mkU64Const 3)),
          .assign (mkPlace 3) (.binaryOp .shrUnchecked (mkCopy 3) (mkU64Const 3)),
          .assign (mkPlace 1) (.binaryOp .addUnchecked (mkCopy 1) (mkU64Const 8))
        ]
        terminator := .goto 1
        cleanup := false },
      -- bb3: loop exit (`_1 ≥ 1024` and `_1 ≤ 1024` => `_1 = 1024`)
      { statements := [
          .assign (mkPlace 2) (.binaryOp .eq (mkCopy 1) (mkU64Const 1024))
        ]
        terminator := .switchInt (mkCopy 2) ⟨[(BitVec.ofNat 128 0, 4)], 5⟩
        cleanup := false },
      -- bb4: dead `.unreachable` trap (pruned by `decideEq? = some true`)
      { statements := []
        terminator := .unreachable
        cleanup := false },
      -- bb5: return `_1` (`= 1024`)
      { statements := [
          .assign (mkPlace 0) (.use (mkCopy 1)),
          .storageDead 3,
          .storageDead 2,
          .storageDead 1
        ]
        terminator := .return_
        cleanup := false }
    ] }

/-- Certified loop-header abstract value for `_1`: `0 ≤ _1 ≤ 1024` and low 3
bits known zero (`_1 ≡ 0 (mod 8)`). -/
@[expose] def stride8HeaderIdxAbs : AbsVal :=
  reduceAbsVal 64
    { init := .init
      tnum := ⟨0, 2040⟩  -- bits 3..10 unknown (0x7F8 = 2040), bits 0..2 = 0
      wi := .iv 0 1024
      sc := .cong 8 0 }

/-- Entry abstract environment for `alignedStride8LoopBody`. -/
@[expose] def alignedStride8EntryEnv : MirAbsEnv :=
  [.uint .i64 (AbsVal.uninit 64), .dead, .dead, .dead]

/-- Certified Bourdoncle cutpoint map for `alignedStride8LoopBody` (`bb1`). -/
@[expose] def alignedStride8Cutpoints : List (BasicBlockId × MirAbsEnv) :=
  [(1, [.uint .i64 (AbsVal.uninit 64),
        .uint .i64 stride8HeaderIdxAbs,
        .bool .uninit,
        .uint .i64 (AbsVal.uninit 64)])]

/-- Single-pass certificate check of `alignedStride8LoopBody` by `rfl`. -/
theorem alignedStride8Loop_cert_ok :
    verifyMirCutpoints alignedStride8LoopBody alignedStride8EntryEnv
      (.uint .i64 (AbsVal.const 64 1024))
      alignedStride8Cutpoints [0, 1, 2, 3, 4, 5] = true := rfl

/-- End-to-end PCC soundness for `alignedStride8LoopBody`: proves unbounded
prefix fault-freedom (`SafeFrom`) and exact return value `1024` directly on
`Trusted.MirSemantics.evalStep`. -/
theorem canary_aligned_stride8_loop_pcc_safe :
    let start := mkState 0 0 (initLocalsLoop alignedStride8LoopBody [] 0
      alignedStride8LoopBody.locals)
    SafeFrom alignedStride8LoopBody start ∧
    ∀ retVal, ReturnsFrom alignedStride8LoopBody start retVal →
      retVal = .scalar ⟨.i64, false, BitVec.ofNat 128 1024⟩ := by
  have hEntry :
      mirAbsEnvDenote alignedStride8LoopBody.locals alignedStride8EntryEnv
        (initLocalsLoop alignedStride8LoopBody [] 0
          alignedStride8LoopBody.locals) := by
    refine ⟨rfl, rfl, ?_⟩
    intro i ty s cs hTy hS hCs
    cases i with
    | zero =>
      injection hTy with ht; injection hS with hs; injection hCs with hcs
      subst ht; subst hs; subst hcs
      exact ⟨rfl, absVal_uninit_sound_none⟩
    | succ i1 =>
      cases i1 with
      | zero =>
        injection hTy with ht; injection hS with hs; injection hCs with hcs
        subst ht; subst hs; subst hcs; rfl
      | succ i2 =>
        cases i2 with
        | zero =>
          injection hTy with ht; injection hS with hs; injection hCs with hcs
          subst ht; subst hs; subst hcs; rfl
        | succ i3 =>
          cases i3 with
          | zero =>
            injection hTy with ht; injection hS with hs; injection hCs with hcs
            subst ht; subst hs; subst hcs; rfl
          | succ _ => nomatch hTy
  have hSound := verifyMirCutpoints_sound
    (start := mkState 0 0 (initLocalsLoop alignedStride8LoopBody [] 0
      alignedStride8LoopBody.locals))
    alignedStride8Loop_cert_ok rfl hEntry
  refine ⟨hSound.1, ?_⟩
  intro retVal hRet
  cases hSound.2 retVal hRet with | intro retTy hS2 =>
  have hTy0 := hS2.1
  have hDen := hS2.2
  injection hTy0 with ht; subst ht
  cases retVal with
  | scalar sv =>
    cases sv with | mk sw ss sb =>
    have hW := hDen.2.1
    have hS := hDen.2.2.1
    have hA := hDen.2.2.2.2
    dsimp only at hW hS hA
    subst hW; subst hS
    have hEqN : sb.toNat = 1024 := by
      have hEx := absVal_exactVal?_sound (w := 64) (a := AbsVal.const 64 1024)
        (c := 1024) rfl hA
      injection hEx.1
    have hBv : sb = BitVec.ofNat 128 1024 := by
      have h1 := bitVec128_ofNat_toNat sb
      rw [hEqN] at h1
      exact h1.symm
    rw [hBv]
  | ptr _ | bool _ | char _ | ordering _ | unit
  | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDen.2

/-- 32-bit bitmask (`& 0xFF | 1` guaranteeing nonzero divisor in `[1, 255]`),
safe `div`/`rem`, and widening `u32 -> u64` cast body. -/
@[expose] def bitmaskDivCastBody : Body :=
  { identity := "ai_pcc_bitmask_div_cast"
    argumentCount := 2
    locals := [.int .i64 false, .int .i32 false, .int .i32 false,
               .int .i32 false, .int .i32 false]
    basicBlocks := [
      { statements := [
          .storageLive 3,
          .storageLive 4,
          .assign (mkPlace 3) (.binaryOp .bitAnd (mkCopy 2) (mkU32Const 255)),
          .assign (mkPlace 3) (.binaryOp .bitOr (mkCopy 3) (mkU32Const 1)),
          .assign (mkPlace 4) (.binaryOp .rem (mkCopy 1) (mkCopy 3)),
          .assign (mkPlace 4) (.binaryOp .div (mkCopy 1) (mkCopy 3)),
          .assign (mkPlace 0) (.cast .intToInt (mkCopy 4) (.int .i64 false)),
          .storageDead 4,
          .storageDead 3
        ]
        terminator := .return_
        cleanup := false }
    ] }

/-- Entry abstract environment for arbitrary `u32` inputs `(_1, _2)`. -/
@[expose] def bitmaskDivCastEntryEnv : MirAbsEnv :=
  [.uint .i64 (AbsVal.uninit 64),
   .uint .i32 (AbsVal.topInit 32),
   .uint .i32 (AbsVal.topInit 32),
   .dead, .dead]

/-- Certified return abstract value: widening `u32` cast yields `≤ 2^32 - 1`. -/
@[expose] def bitmaskDivCastRetSlot : MirAbsSlot :=
  .uint .i64 ⟨.init, Tnum.top 32, .iv 0 (modPow2 32 - 1), .top⟩

/-- Single-pass certificate check for `bitmaskDivCastBody` by `rfl`. -/
theorem bitmaskDivCast_cert_ok :
    verifyMirCutpoints bitmaskDivCastBody bitmaskDivCastEntryEnv
      bitmaskDivCastRetSlot [] [0] = true := rfl

/-- End-to-end PCC soundness for `bitmaskDivCastBody` across all `u32` inputs
`(a, b)`. -/
theorem canary_bitmask_div_cast_pcc_safe (a b : BitVec 128)
    (ha : a.toNat < modPow2 32) (hb : b.toNat < modPow2 32) :
    let args : List Val := [.scalar ⟨.i32, false, a⟩, .scalar ⟨.i32, false, b⟩]
    let start := mkState 0 0 (initLocalsLoop bitmaskDivCastBody args 0
      bitmaskDivCastBody.locals)
    SafeFrom bitmaskDivCastBody start ∧
    ∀ retVal, ReturnsFrom bitmaskDivCastBody start retVal →
      ∃ sb, retVal = .scalar ⟨.i64, false, sb⟩ ∧ sb.toNat < modPow2 32 := by
  have hEntry :
      mirAbsEnvDenote bitmaskDivCastBody.locals bitmaskDivCastEntryEnv
        (initLocalsLoop bitmaskDivCastBody
          [.scalar ⟨.i32, false, a⟩, .scalar ⟨.i32, false, b⟩] 0
          bitmaskDivCastBody.locals) := by
    refine ⟨rfl, rfl, ?_⟩
    intro i ty s cs hTy hS hCs
    cases i with
    | zero =>
      injection hTy with ht; injection hS with hs; injection hCs with hcs
      subst ht; subst hs; subst hcs; exact ⟨rfl, absVal_uninit_sound_none⟩
    | succ i1 =>
      cases i1 with
      | zero =>
        injection hTy with ht; injection hS with hs; injection hCs with hcs
        subst ht; subst hs; subst hcs
        exact ⟨rfl, rfl, rfl, ha, absVal_topInit_sound ha⟩
      | succ i2 =>
        cases i2 with
        | zero =>
          injection hTy with ht; injection hS with hs; injection hCs with hcs
          subst ht; subst hs; subst hcs
          exact ⟨rfl, rfl, rfl, hb, absVal_topInit_sound hb⟩
        | succ i3 =>
          cases i3 with
          | zero =>
            injection hTy with ht; injection hS with hs; injection hCs with hcs
            subst ht; subst hs; subst hcs; rfl
          | succ i4 =>
            cases i4 with
            | zero =>
              injection hTy with ht; injection hS with hs; injection hCs with hcs
              subst ht; subst hs; subst hcs; rfl
            | succ _ => nomatch hTy
  have hSound := verifyMirCutpoints_sound
    (start := mkState 0 0 (initLocalsLoop bitmaskDivCastBody
      [.scalar ⟨.i32, false, a⟩, .scalar ⟨.i32, false, b⟩] 0
      bitmaskDivCastBody.locals))
    bitmaskDivCast_cert_ok rfl hEntry
  refine ⟨hSound.1, ?_⟩
  intro retVal hRet
  cases hSound.2 retVal hRet with | intro retTy hS2 =>
  have hTy0 := hS2.1
  have hDen := hS2.2
  injection hTy0 with ht; subst ht
  cases retVal with
  | scalar sv =>
    cases sv with | mk sw ss sb =>
    have hW := hDen.2.1
    have hS := hDen.2.2.1
    have hA := hDen.2.2.2.2
    dsimp only at hW hS hA
    subst hW; subst hS
    have hLe : sb.toNat ≤ modPow2 32 - 1 := by
      have hWi := hA.2.2.1
      dsimp only [bitmaskDivCastRetSlot, WrappedInterval.denote] at hWi
      exact hWi.2.2.2.2
    have hLt32 : sb.toNat < modPow2 32 :=
      Nat.lt_of_le_of_lt hLe (Nat.sub_lt (modPow2_pos 32) (Nat.zero_lt_succ 0))
    exact ⟨sb, rfl, hLt32⟩
  | ptr _ | bool _ | char _ | ordering _ | unit
  | enumVal _ _ | tuple _ | bytes _ => exact False.elim hDen.2

/-! ## Positive Controls, Aliasing, Guards, and CFG Merge Canaries -/

@[expose] def mkOneBlockU8Body (stmts : List StatementKind)
    (term : TerminatorKind) : Body :=
  { identity := "one_block_u8"
    argumentCount := 1
    locals := [.int .i8 false, .int .i8 false]
    basicBlocks := [{ statements := stmts, terminator := term, cleanup := false }] }

/-- Guard-refinement test helper: compares `_1 < 8` into `_2`, runs `midStmt`,
and branches on `_2` to `shlUnchecked(1, _1)` on the `true` arm. -/
@[expose] def mkGuardShiftBody (midStmts : List StatementKind) : Body :=
  { identity := "guard_shift_u8"
    argumentCount := 1
    locals := [.int .i8 false, .int .i8 false, .bool, .int .i8 false]
    basicBlocks := [
      -- bb0: `_2 = _1 < 8`, optional `midStmts`, branch on `_2`
      { statements :=
          [.storageLive 2,
           .storageLive 3,
           .assign (mkPlace 2) (.binaryOp .lt (mkCopy 1) (mkU8Const 8))] ++
          midStmts
        terminator := .switchInt (mkCopy 2) ⟨[(BitVec.ofNat 128 0, 2)], 1⟩
        cleanup := false },
      -- bb1: true arm (`_1 < 8`), so `shlUnchecked(1, _1)` is safe on `u8`
      { statements := [
          .assign (mkPlace 0) (.binaryOp .shlUnchecked (mkU8Const 1) (mkCopy 1))
        ]
        terminator := .goto 3
        cleanup := false },
      -- bb2: false arm
      { statements := [.assign (mkPlace 0) (.use (mkU8Const 0))]
        terminator := .goto 3
        cleanup := false },
      -- bb3: join and return
      { statements := [.storageDead 3, .storageDead 2]
        terminator := .return_
        cleanup := false }
    ] }

/-- Acyclic `switchInt` merge over an unconstrained `u8` parameter
(`topInit 8`). -/
@[expose] def switchJoinTopU8Body : Body :=
  { identity := "switch_join_top_u8"
    argumentCount := 1
    locals := [.int .i8 false, .int .i8 false]
    basicBlocks := [
      { statements := []
        terminator := .switchInt (mkCopy 1) ⟨[(BitVec.ofNat 128 0, 1)], 1⟩
        cleanup := false },
      { statements := [.assign (mkPlace 0) (.use (mkCopy 1))]
        terminator := .return_
        cleanup := false }
    ] }

/-- 4-block diamond whose branches produce `[128, 12]` (straddling `255 -> 0`)
and `[0, 140]` (covering the full `u8` ring upon join at `bb3`). -/
@[expose] def diamondWrapJoinU8Body : Body :=
  { identity := "diamond_wrap_join_u8"
    argumentCount := 2
    locals := [.int .i8 false, .int .i8 false, .bool]
    basicBlocks := [
      { statements := []
        terminator := .switchInt (mkCopy 2) ⟨[(BitVec.ofNat 128 0, 2)], 1⟩
        cleanup := false },
      { statements := [
          .assign (mkPlace 0) (.binaryOp .add (mkCopy 1) (mkU8Const 128))
        ]
        terminator := .goto 3
        cleanup := false },
      { statements := [.assign (mkPlace 0) (.use (mkCopy 1))]
        terminator := .goto 3
        cleanup := false },
      { statements := []
        terminator := .return_
        cleanup := false }
    ] }

/-- Positive controls for `mkOneBlockU8Body`, `Operand.move` sequencing,
`RelGuard` preservation across unrelated writes, initialized vs.
uninitialized live-local reads, and full-ring CFG joins. -/
theorem canary_positive_controls_move_guard_and_cfg_joins :
    let u8Entry : MirAbsEnv :=
      [.uint .i8 (AbsVal.uninit 8), .uint .i8 (AbsVal.topInit 8)]
    let u8Ret : MirAbsSlot := .uint .i8 (AbsVal.topInit 8)
    let guardEntry : MirAbsEnv :=
      [.uint .i8 (AbsVal.uninit 8), .uint .i8 (AbsVal.topInit 8), .dead, .dead]
    let diamondEntry : MirAbsEnv :=
      [.uint .i8 (AbsVal.uninit 8),
       .uint .i8 (reduceAbsVal 8 ⟨.init, Tnum.top 8, .iv 0 140, .top⟩),
       .bool (.top .none)]
    -- 1. Benign copy-return on `mkOneBlockU8Body`:
    verifyMirCutpoints
      (mkOneBlockU8Body [.assign (mkPlace 0) (.use (mkCopy 1))] .return_)
      u8Entry u8Ret [] [0] = true ∧
    -- 2. Wrapping `add` on `mkOneBlockU8Body`:
    verifyMirCutpoints
      (mkOneBlockU8Body
        [.assign (mkPlace 0) (.binaryOp .add (mkCopy 1) (mkU8Const 1))] .return_)
      u8Entry u8Ret [] [0] = true ∧
    -- 3. In-bounds `shlUnchecked` (`7 < 8`) on `mkOneBlockU8Body`:
    verifyMirCutpoints
      (mkOneBlockU8Body
        [.assign (mkPlace 0) (.binaryOp .shlUnchecked (mkCopy 1) (mkU8Const 7))]
        .return_)
      u8Entry u8Ret [] [0] = true ∧
    -- 4. Nonzero constant divisor (`10 / 3`) on `mkOneBlockU8Body`:
    verifyMirCutpoints
      (mkOneBlockU8Body
        [.assign (mkPlace 0) (.binaryOp .div (mkU8Const 10) (mkU8Const 3))]
        .return_)
      u8Entry u8Ret [] [0] = true ∧
    -- 5. Safe `copy _1` followed by `move _1` in one binary operation:
    verifyMirCutpoints
      (mkOneBlockU8Body
        [.assign (mkPlace 0) (.binaryOp .add (mkCopy 1) (mkMove 1))] .return_)
      u8Entry u8Ret [] [0] = true ∧
    -- 6. Relational guard `_1 < 8` preserved across unrelated write to `_3`:
    verifyMirCutpoints
      (mkGuardShiftBody [.assign (mkPlace 3) (.use (mkU8Const 99))])
      guardEntry u8Ret [] [0, 1, 2, 3] = true ∧
    -- 7. Acyclic `switchInt` merge on `AbsVal.topInit 8`:
    verifyMirCutpoints switchJoinTopU8Body u8Entry u8Ret [] [0, 1] = true ∧
    -- 8. Diamond join where `[128, 12] ⊔ [0, 140]` covers the full `u8` ring:
    verifyMirCutpoints diamondWrapJoinU8Body diamondEntry u8Ret []
      [0, 1, 2, 3] = true ∧
    -- 9. Positive twin of `neg_uninit_read` (`_3 = copy _1; _0 = copy _1`):
    verifyMirCutpoints
      { identity := "pos_init_read"
        argumentCount := 1
        locals := [.int .i8 false, .int .i8 false, .int .i8 false,
                   .int .i8 false]
        basicBlocks := [
          { statements := [
              .storageLive 2, .storageLive 3,
              .assign (mkPlace 3) (.use (mkCopy 1)),
              .assign (mkPlace 0) (.use (mkCopy 1))
            ]
            terminator := .return_
            cleanup := false }
        ] }
      guardEntry u8Ret [] [0] = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Direct positive and fail-closed unit checks for standalone reduced-product
domain helpers (`InitDom.meet`, `AbsVal.isAligned8`,
`AbsVal.noOverflowAddConst`, `AbsVal.addConstWrap`, and
`AbsVal.subConstWrap`). -/
theorem canary_domain_helpers_tests :
    InitDom.meet .uninit .init = .init ∧
    InitDom.meet .init .bot = .bot ∧
    stride8HeaderIdxAbs.isAligned8 = true ∧
    (AbsVal.const 64 12).isAligned8 = false ∧
    stride8HeaderIdxAbs.noOverflowAddConst 64 8 = true ∧
    (AbsVal.topInit 8).noOverflowAddConst 8 1 = false ∧
    (AbsVal.addConstWrap 8 (AbsVal.const 8 250) 10).exactVal? 8 = some 4 ∧
    (AbsVal.subConstWrap 8 (AbsVal.const 8 4) 10).exactVal? 8 = some 250 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Fail-Closed Negative Regression Suite -/

/-- Fail-closed negative regression suite verifying that `verifyMirCutpoints`
rejects:
1. potential `addUnchecked` overflow (`u8` `topInit + 1`);
2. potential `subUnchecked` underflow (`u8` `topInit - 1`);
3. out-of-range `shlUnchecked` shift (`u8 << 8`);
4. potential division by zero (`u8 / topInit`);
5. reachable `.unreachable` trap;
6. returning uninitialized `_0`;
7. non-inductive loop cutpoint invariant (claiming `_1 ≤ 100` on `stride8`);
8. `StorageDead 0` on the return place;
9. reading an uninitialized live local into scratch `_3` while returning
   initialized `_0`:
   `StorageLive 2; StorageLive 3; _3 = copy _2; _0 = copy _1`;
10. `Operand.move` use-after-move (`Add(move _1, copy _1)`);
11. clobbered `RelGuard` (`_2 = _1 < 8; _1 = _1 + 1` before `switchInt _2`,
    which keeps `_1 = topInit 8` so removing `clearGuardsFor` would accept);
12. non-`0`-headed, duplicate, out-of-range, incomplete, or misordered
    `rpoOrder` schedules (validated by `validRpoSchedule` and rejected by
    `verifyMirCutpoints`);
13. `retInv` carrying a frame-relative `RelGuard`;
14. `entryEnv` length mismatch against `body.locals`. -/
theorem canary_negative_fail_closed_pcc_tests :
    let u8Entry : MirAbsEnv :=
      [.uint .i8 (AbsVal.uninit 8), .uint .i8 (AbsVal.topInit 8)]
    let u8Ret : MirAbsSlot := .uint .i8 (AbsVal.topInit 8)
    let guardEntry : MirAbsEnv :=
      [.uint .i8 (AbsVal.uninit 8), .uint .i8 (AbsVal.topInit 8), .dead, .dead]
    -- 1. Potential `addUnchecked` overflow:
    verifyMirCutpoints
      (mkOneBlockU8Body
        [.assign (mkPlace 0) (.binaryOp .addUnchecked (mkCopy 1) (mkU8Const 1))]
        .return_)
      u8Entry u8Ret [] [0] = false ∧
    -- 2. Potential `subUnchecked` underflow:
    verifyMirCutpoints
      (mkOneBlockU8Body
        [.assign (mkPlace 0) (.binaryOp .subUnchecked (mkCopy 1) (mkU8Const 1))]
        .return_)
      u8Entry u8Ret [] [0] = false ∧
    -- 3. Out-of-bounds `shlUnchecked` (`shift = 8 = bitWidth i8`):
    verifyMirCutpoints
      (mkOneBlockU8Body
        [.assign (mkPlace 0) (.binaryOp .shlUnchecked (mkCopy 1) (mkU8Const 8))]
        .return_)
      u8Entry u8Ret [] [0] = false ∧
    -- 4. Potential division by zero (`topInit` includes 0):
    verifyMirCutpoints
      (mkOneBlockU8Body
        [.assign (mkPlace 0) (.binaryOp .div (mkU8Const 10) (mkCopy 1))]
        .return_)
      u8Entry u8Ret [] [0] = false ∧
    -- 5. Reachable `.unreachable` trap:
    verifyMirCutpoints
      (mkOneBlockU8Body [] .unreachable)
      u8Entry u8Ret [] [0] = false ∧
    -- 6. Returning uninitialized `_0`:
    verifyMirCutpoints
      (mkOneBlockU8Body [] .return_)
      u8Entry u8Ret [] [0] = false ∧
    -- 7. Non-inductive loop cutpoint (`_1 ≤ 100` violated on loop back-edge):
    (let badHeader : AbsVal :=
       reduceAbsVal 64
         { init := .init, tnum := ⟨0, 120⟩, wi := .iv 0 100, sc := .cong 8 0 }
     verifyMirCutpoints alignedStride8LoopBody alignedStride8EntryEnv
       (.uint .i64 (AbsVal.topInit 64))
       [(1, [.uint .i64 (AbsVal.uninit 64), .uint .i64 badHeader,
             .bool .uninit, .uint .i64 (AbsVal.uninit 64)])]
       [0, 1, 2, 3, 4, 5] = false) ∧
    -- 8. `StorageDead 0` on the return place:
    verifyMirCutpoints
      (mkOneBlockU8Body
        [.assign (mkPlace 0) (.use (mkCopy 1)), .storageDead 0] .return_)
      u8Entry u8Ret [] [0] = false ∧
    -- 9. Reading an uninitialized live local (`_3 = copy _2; _0 = copy _1`),
    --    isolating `evalOperandAbs` from the return-slot initialization check:
    verifyMirCutpoints
      { identity := "neg_uninit_read"
        argumentCount := 1
        locals := [.int .i8 false, .int .i8 false, .int .i8 false,
                   .int .i8 false]
        basicBlocks := [
          { statements := [
              .storageLive 2, .storageLive 3,
              .assign (mkPlace 3) (.use (mkCopy 2)),
              .assign (mkPlace 0) (.use (mkCopy 1))
            ]
            terminator := .return_
            cleanup := false }
        ] }
      guardEntry u8Ret [] [0] = false ∧
    -- 10. `Operand.move` use-after-move (`Add(move _1, copy _1)`):
    verifyMirCutpoints
      (mkOneBlockU8Body
        [.assign (mkPlace 0) (.binaryOp .add (mkMove 1) (mkCopy 1))] .return_)
      u8Entry u8Ret [] [0] = false ∧
    -- 11. Clobbered `RelGuard` (`_1` overwritten with `_1 + 1` = `topInit 8`
    --     before `switchInt _2`, isolating `clearGuardsFor`):
    verifyMirCutpoints
      (mkGuardShiftBody [.assign (mkPlace 1) (.binaryOp .add (mkCopy 1) (mkU8Const 1))])
      guardEntry u8Ret [] [0, 1, 2, 3] = false ∧
    -- 12. Invalid `rpoOrder` schedules (non-`0` head, duplicate, OOB,
    --     incomplete, and misordered on `alignedStride8LoopBody`):
    verifyMirCutpoints alignedStride8LoopBody alignedStride8EntryEnv
      (.uint .i64 (AbsVal.const 64 1024))
      alignedStride8Cutpoints [1, 0, 2, 3, 4, 5] = false ∧
    verifyMirCutpoints alignedStride8LoopBody alignedStride8EntryEnv
      (.uint .i64 (AbsVal.const 64 1024))
      alignedStride8Cutpoints [0, 1, 1, 2, 3, 4] = false ∧
    verifyMirCutpoints alignedStride8LoopBody alignedStride8EntryEnv
      (.uint .i64 (AbsVal.const 64 1024))
      alignedStride8Cutpoints [0, 99, 2, 3, 4, 5] = false ∧
    verifyMirCutpoints alignedStride8LoopBody alignedStride8EntryEnv
      (.uint .i64 (AbsVal.const 64 1024))
      alignedStride8Cutpoints [0, 1, 2, 3, 5] = false ∧
    verifyMirCutpoints alignedStride8LoopBody alignedStride8EntryEnv
      (.uint .i64 (AbsVal.const 64 1024))
      alignedStride8Cutpoints [0, 1, 2, 5, 3, 4] = false ∧
    -- 13. Return invariant carrying a non-`.none` `RelGuard`:
    verifyMirCutpoints
      { identity := "neg_relguard_ret"
        argumentCount := 1
        locals := [.bool, .int .i8 false]
        basicBlocks := [
          { statements := [
              .assign (mkPlace 0) (.binaryOp .lt (mkCopy 1) (mkU8Const 8))
            ]
            terminator := .return_
            cleanup := false }
        ] }
      [.bool .uninit, .uint .i8 (AbsVal.topInit 8)]
      (.bool (.top (.uleConst 1 .i8 7))) [] [0] = false ∧
    -- 14. Entry environment length mismatch (`3` slots on `2`-local body):
    verifyMirCutpoints
      (mkOneBlockU8Body [.assign (mkPlace 0) (.use (mkCopy 1))] .return_)
      [.uint .i8 (AbsVal.uninit 8), .uint .i8 (AbsVal.topInit 8), .dead]
      u8Ret [] [0] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl⟩

/-- Direct schedule-validation regression pinning `validRpoSchedule` on the
valid loop schedule and each invalid `rpoOrder` shape independently of
block-reachability materialization. -/
theorem canary_validRpoSchedule_tests :
    validRpoSchedule alignedStride8LoopBody alignedStride8Cutpoints
      [0, 1, 2, 3, 4, 5] = true ∧
    validRpoSchedule alignedStride8LoopBody alignedStride8Cutpoints
      [1, 0, 2, 3, 4, 5] = false ∧
    validRpoSchedule alignedStride8LoopBody alignedStride8Cutpoints
      [0, 1, 1, 2, 3, 4] = false ∧
    validRpoSchedule alignedStride8LoopBody alignedStride8Cutpoints
      [0, 99, 2, 3, 4, 5] = false ∧
    validRpoSchedule alignedStride8LoopBody alignedStride8Cutpoints
      [0, 1, 2, 3, 5] = false ∧
    validRpoSchedule alignedStride8LoopBody alignedStride8Cutpoints
      [0, 1, 2, 5, 3, 4] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.AiPcc

end
