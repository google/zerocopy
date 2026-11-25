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
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.ConjunctiveWp.Wlp
public import Anneal.SafeTwin.Equiv
public import Anneal.SafeTwin.BiAlign

public section

/-!
# Concrete MIR & Relational Canaries for `Anneal.SafeTwin`

End-to-end positive witnesses and single-cause loophole refutations exercising
`Anneal.SafeTwin`:

1. **Canary 1 (`canary1_mir_safeTwin_stride4_trans_and_bodyVerified`,
   `canary1_mir_bounded_biAlign_terminating_tiles`):**
   3-way transitive `SafeTwinQueryEquiv` across a scalar `4 * k`-iteration MIR
   loop (`progSafeScalar4x`, `165` MIR steps at `k = 10`), a 4-way unrolled MIR
   loop (`progCandUnrolled4x`, `75` steps), and a shift-stepped vector-tile MIR
   loop (`progCandSimdTile4x`, `46` steps), plus `SatisfiesPost` and
   `terminatesWith` transfer, `TotalSafeTwinBodyEquiv`,
   `Trusted.MirSemantics.BodyVerified`, and a terminating
   `MirBiAlignBoundedTileSpec` + `mirBiAlign_bounded_tiled_sound` witness
   aligning `16` scalar steps per tile against `4` SIMD-tile steps on
   `progSafeScalar4x` vs. `progCandSimdTile4x` (`tiles = 2`, returning `56`).
2. **Canary 2 (`canary2_loopholes_L1_L2_L3_L4_refuted_on_mir`):**
   Refutes all three weak relational predicates across four loophole cases
   (`L1`–`L4`):
   - `L1` & `L2`: `ReturnOnlyMirEquiv` accepts both unchecked division-by-zero
     UB (`progBadDivZeroUb`) and `TerminatorKind.unreachable` UB
     (`progBadUnreachableUb`) against safe `progSafeCheckedDiv`, while
     `SafeTwinQueryEquiv` rejects both MIR candidates.
   - `L3`: `PartialMirEquiv` accepts silent non-termination (`progLoopSelf1`)
     against terminating `progSafeReturnU32`, while `SafeTwinQueryEquiv`
     rejects the MIR candidate.
   - `L4`: `DiscrimOnlyTermEq` accepts torn pre-unwind `CallerMemory`, while
     exact `TerminalOut` equality rejects it (a `TerminalOut` data inequality;
     Profile v1 `evalStep` does not emit `.unwound`).
3. **Canary 3 (`canary3_productive_diverging_twins_and_mirBiAlign`):**
   Proves constructive `SafeTwinQueryEquiv` (`0` `Classical.choice`) and
   non-terminating 2-to-1 `MirBiAlignTileSpec` + `mirBiAlign_tiled_sound` +
   `reaches_of_mirStepsDet` between a 2-block ping-pong reactive loop and a
   1-block self-loop.
4. **Canary 4 (`canary4_biAlign_epilogue_narrowWrap_and_ct_2safety`):**
   Exercises 4-lane vector + scalar-tail `biAlign_tiled_with_epilogue_sound`
   (`4 * numTiles + rem`), `biAlign_lockstep_fails_on_stride4`, 16-bit
   `narrowAddMod` soundness vs. `32768 + 32768 = 65536` wrap divergence, and
   `SecScalar` / `LeakObs` 2-safety transfer vs. McLean's Refinement Paradox on
   a secret-branching declassified twin.
-/

namespace Anneal.SafeTwin

open Trusted.MirAst Trusted.MirSemantics
open Anneal.MirWp Anneal.ConjunctiveWp

/-! ## Shared MIR Scalar Helpers -/

/-- Computable `u32` MIR type descriptor. -/
@[expose] def stU32Ty : MirTy := .int .i32 false

/-- Computable `u32` scalar `Val` constructor. -/
@[expose] def stU32Val (n : Nat) : Val :=
  .scalar ⟨.i32, false, BitVec.ofNat 128 n⟩

/-- Computable `u32` constant `Operand` constructor. -/
@[expose] def stU32Const (n : Nat) : Operand :=
  .constant ⟨stU32Ty, .scalar (BitVec.ofNat 128 n)⟩

/-- Computable `Query` constructor with empty `callerMem`. -/
@[expose] def stQuery (args : List Val) : Query :=
  { args := args, callerMem := ⟨[]⟩ }

/-- Expected `TerminalOut.returned` wrapper with empty `callerMem`. -/
@[expose] def stRetU32 (n : Nat) : TerminalOut :=
  .returned ⟨stU32Val n, ⟨[]⟩⟩

/-! ## Canary 1: 3-Way Transitive MIR `SafeTwin` & `BodyVerified` -/

/-- Safe scalar reference body `fn sum_scalar_4x(val: u32, tiles: u32) -> u32`:
computes `count = tiles * 4` and loops `count` times adding `val` (`165` MIR
steps at `tiles = 10`). -/
@[expose] def bodySafeScalar4x : Body where
  identity := "safe_twin::sum_scalar_4x"
  isUnsafe := false
  argumentCount := 2
  locals := [stU32Ty, stU32Ty, stU32Ty, stU32Ty]
  basicBlocks := [
    { statements := [
        .assign ⟨0, []⟩ (.use (stU32Const 0)),
        .assign ⟨3, []⟩ (.binaryOp .mul (.copy ⟨2, []⟩) (stU32Const 4))
      ]
      terminator := .goto 1 },
    { statements := []
      terminator := .switchInt (.copy ⟨3, []⟩) {
        branches := [(BitVec.ofNat 128 0, 3)]
        otherwise := 2
      } },
    { statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨1, []⟩)),
        .assign ⟨3, []⟩ (.binaryOp .sub (.copy ⟨3, []⟩) (stU32Const 1))
      ]
      terminator := .goto 1 },
    { statements := []
      terminator := .return_ }
  ]

/-- Safe scalar reference `Program`. -/
@[expose] def progSafeScalar4x : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [bodySafeScalar4x]

/-- 4-way unrolled middle twin `fn sum_unrolled_4x(val: u32, tiles: u32) -> u32`
executing `tiles` iterations of 4 consecutive `add`s (`75` MIR steps at
`tiles = 10`). -/
@[expose] def progCandUnrolled4x : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "safe_twin::sum_unrolled_4x"
    isUnsafe := false
    argumentCount := 2
    locals := [stU32Ty, stU32Ty, stU32Ty, stU32Ty]
    basicBlocks := [
      { statements := [
          .assign ⟨0, []⟩ (.use (stU32Const 0)),
          .assign ⟨3, []⟩ (.use (.copy ⟨2, []⟩))
        ]
        terminator := .goto 1 },
      { statements := []
        terminator := .switchInt (.copy ⟨3, []⟩) {
          branches := [(BitVec.ofNat 128 0, 3)]
          otherwise := 2
        } },
      { statements := [
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨1, []⟩)),
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨1, []⟩)),
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨1, []⟩)),
          .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨1, []⟩)),
          .assign ⟨3, []⟩ (.binaryOp .sub (.copy ⟨3, []⟩) (stU32Const 1))
        ]
        terminator := .goto 1 },
      { statements := []
        terminator := .return_ }
    ]
  }]

/-- Unsafe SIMD-tile twin body `unsafe fn sum_simd_tile_4x(val: u32, tiles: u32)
-> u32` computing `lane4 = val << 2` once and iterating `tiles` times (`46` MIR
steps at `tiles = 10`). -/
@[expose] def bodyCandSimdTile4x : Body where
  identity := "safe_twin::sum_simd_tile_4x"
  isUnsafe := true
  argumentCount := 2
  locals := [stU32Ty, stU32Ty, stU32Ty, stU32Ty, stU32Ty]
  basicBlocks := [
    { statements := [
        .assign ⟨0, []⟩ (.use (stU32Const 0)),
        .assign ⟨3, []⟩ (.use (.copy ⟨2, []⟩)),
        .assign ⟨4, []⟩ (.binaryOp .shl (.copy ⟨1, []⟩) (stU32Const 2))
      ]
      terminator := .goto 1 },
    { statements := []
      terminator := .switchInt (.copy ⟨3, []⟩) {
        branches := [(BitVec.ofNat 128 0, 3)]
        otherwise := 2
      } },
    { statements := [
        .assign ⟨0, []⟩ (.binaryOp .add (.copy ⟨0, []⟩) (.copy ⟨4, []⟩)),
        .assign ⟨3, []⟩ (.binaryOp .sub (.copy ⟨3, []⟩) (stU32Const 1))
      ]
      terminator := .goto 1 },
    { statements := []
      terminator := .return_ }
  ]

/-- Unsafe SIMD-tile `Program`. -/
@[expose] def progCandSimdTile4x : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [bodyCandSimdTile4x]

/-- Canary 1 (`[propext]` only): proves 3-way transitive `SafeTwinQueryEquiv`
across `165`-step scalar, `75`-step unrolled, and `46`-step SIMD-tile MIR loops
at `(7, 10) -> 280`, transfers `SatisfiesPost` and total termination, and
discharges `Trusted.MirSemantics.BodyVerified` via
`bodyVerified_of_totalSafeTwinBodyEquiv`. -/
theorem canary1_mir_safeTwin_stride4_trans_and_bodyVerified :
    let args₀ := [stU32Val 7, stU32Val 10]
    let q₀ := stQuery args₀
    let post₂₈₀ := fun out : TerminalOut => out = stRetU32 280
    let pre₀ := fun args : List Val => args = args₀
    SafeTwinQueryEquiv progSafeScalar4x progCandUnrolled4x q₀ ∧
    SafeTwinQueryEquiv progCandUnrolled4x progCandSimdTile4x q₀ ∧
    SafeTwinQueryEquiv progSafeScalar4x progCandSimdTile4x q₀ ∧
    SafeTwinQueryEquiv progCandSimdTile4x progSafeScalar4x q₀ ∧
    SafeTwinQueryEquiv progSafeScalar4x progSafeScalar4x q₀ ∧
    SatisfiesPost progCandSimdTile4x q₀ post₂₈₀ ∧
    (¬ Diverges progCandSimdTile4x q₀ ∧
      ∃ out, Behavior progCandSimdTile4x q₀ out ∧ post₂₈₀ out) ∧
    TotalSafeTwinBodyEquiv
      progSafeScalar4x 0 bodySafeScalar4x
      progCandSimdTile4x 0 bodyCandSimdTile4x pre₀ ∧
    BodyVerified progCandSimdTile4x 0 bodyCandSimdTile4x pre₀ := by
  intro args₀ q₀ post₂₈₀ pre₀
  have hExecSafe : execProgPow2 progSafeScalar4x 8 q₀ post₂₈₀ := rfl
  have hExecUnroll : execProgPow2 progCandUnrolled4x 7 q₀ post₂₈₀ := rfl
  have hExecSimd : execProgPow2 progCandSimdTile4x 6 q₀ post₂₈₀ := rfl
  have hEqSU : SafeTwinQueryEquiv progSafeScalar4x progCandUnrolled4x q₀ :=
    safeTwinQueryEquiv_of_execProgPow2_sameOut hExecSafe hExecUnroll
  have hEqUS : SafeTwinQueryEquiv progCandUnrolled4x progCandSimdTile4x q₀ :=
    safeTwinQueryEquiv_of_execProgPow2_sameOut hExecUnroll hExecSimd
  have hEqSSimd : SafeTwinQueryEquiv progSafeScalar4x progCandSimdTile4x q₀ :=
    safeTwinQueryEquiv_trans hEqSU hEqUS
  have hSafeAdq :=
    wellFormed_and_spec_of_wpProgPow2 (wpProgPow2_of_execProgPow2 hExecSafe)
  have hSatSimd : SatisfiesPost progCandSimdTile4x q₀ post₂₈₀ :=
    (satisfiesPost_iff_of_safeTwinQueryEquiv hEqSSimd post₂₈₀).mpr hSafeAdq.1
  have hTermSimd :=
    (terminatesWith_iff_of_safeTwinQueryEquiv hEqSSimd post₂₈₀).mpr hSafeAdq.2
  have hBodyTwin :
      TotalSafeTwinBodyEquiv
        progSafeScalar4x 0 bodySafeScalar4x
        progCandSimdTile4x 0 bodyCandSimdTile4x pre₀ := by
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro args _ _ hPre
    rw [hPre]
    exact hEqSSimd
  have hBodyVer :
      BodyVerified progCandSimdTile4x 0 bodyCandSimdTile4x pre₀ := by
    apply bodyVerified_of_totalSafeTwinBodyEquiv hBodyTwin
    intro args _ hUnsafePre
    have hEqArgs : args = args₀ := hUnsafePre rfl
    rw [hEqArgs]
    exact ⟨rfl, rfl⟩
  exact ⟨hEqSU, hEqUS, hEqSSimd, safeTwinQueryEquiv_symm hEqSSimd,
    safeTwinQueryEquiv_refl hEqSSimd.wfSafe, hSatSimd, hTermSimd,
    hBodyTwin, hBodyVer⟩

/-- Reachable loop-header state of `progSafeScalar4x` at `(val = 7, tiles = 2)`
with accumulator `acc`, remaining scalar iterations `rem`, and `entryMemory`
`⟨2, []⟩`. -/
@[expose] def stateScalar4xHeader (acc rem : Nat) : State :=
  { frames := [{
      defId := 0
      locals := [
        .immediate (some (stU32Val acc)),
        .immediate (some (stU32Val 7)),
        .immediate (some (stU32Val 2)),
        .immediate (some (stU32Val rem))
      ]
      blockIdx := 1
      stmtIdx := 0
    }]
    callerMem := ⟨[]⟩
    mem := ⟨2, []⟩ }

/-- Reachable loop-header state of `progCandSimdTile4x` at `(val = 7,
tiles = 2)` with accumulator `acc`, remaining vector tiles `rem`, and
`entryMemory` `⟨2, []⟩`. -/
@[expose] def stateSimdTile4xHeader (acc rem : Nat) : State :=
  { frames := [{
      defId := 0
      locals := [
        .immediate (some (stU32Val acc)),
        .immediate (some (stU32Val 7)),
        .immediate (some (stU32Val 2)),
        .immediate (some (stU32Val rem)),
        .immediate (some (stU32Val 28))
      ]
      blockIdx := 1
      stmtIdx := 0
    }]
    callerMem := ⟨[]⟩
    mem := ⟨2, []⟩ }

/-- Canary 1b (`[propext]` only): chains `initState` -> prologue (`3` vs. `4`
steps) -> terminating `MirBiAlignBoundedTileSpec` +
`mirBiAlign_bounded_tiled_sound` (`2` tiles of `16` vs. `4` MIR steps on
`progSafeScalar4x` vs. `progCandSimdTile4x` at `(7, 2)`) -> exit relation
`rel 0` -> 2-step return epilogue, deriving `Behavior ... q₂ (stRetU32 56)`
directly along both tiled runs. -/
theorem canary1_mir_bounded_biAlign_terminating_tiles :
    let q₂ := stQuery [stU32Val 7, stU32Val 2]
    let rel := fun (k : Nat) (s t : State) =>
      match k with
      | 0 => s = stateScalar4xHeader 56 0 ∧ t = stateSimdTile4xHeader 56 0
      | 1 => s = stateScalar4xHeader 28 4 ∧ t = stateSimdTile4xHeader 28 1
      | 2 => s = stateScalar4xHeader 0 8 ∧ t = stateSimdTile4xHeader 0 2
      | _ => False
    MirBiAlignBoundedTileSpec progSafeScalar4x 16 progCandSimdTile4x 4 rel ∧
    (∃ s₀ t₀ sₑ tₑ sRet tRet : State,
      initState progSafeScalar4x q₂ = .ok s₀ ∧
      initState progCandSimdTile4x q₂ = .ok t₀ ∧
      MirStepsDet progSafeScalar4x 3 s₀ (stateScalar4xHeader 0 8) ∧
      MirStepsDet progCandSimdTile4x 4 t₀ (stateSimdTile4xHeader 0 2) ∧
      MirStepsDet progSafeScalar4x (16 * 2) (stateScalar4xHeader 0 8) sₑ ∧
      MirStepsDet progCandSimdTile4x (4 * 2) (stateSimdTile4xHeader 0 2) tₑ ∧
      rel 0 sₑ tₑ ∧
      MirStepsDet progSafeScalar4x 1 sₑ sRet ∧
      evalStep progSafeScalar4x 0 sRet = .done (stRetU32 56) ∧
      MirStepsDet progCandSimdTile4x 1 tₑ tRet ∧
      evalStep progCandSimdTile4x 0 tRet = .done (stRetU32 56) ∧
      Behavior progSafeScalar4x q₂ (stRetU32 56) ∧
      Behavior progCandSimdTile4x q₂ (stRetU32 56)) := by
  intro q₂ rel
  let s₀ : State :=
    { frames := [{
        defId := 0
        locals := [
          .immediate none,
          .immediate (some (stU32Val 7)),
          .immediate (some (stU32Val 2)),
          .immediate none
        ]
        blockIdx := 0
        stmtIdx := 0
      }]
      callerMem := ⟨[]⟩
      mem := ⟨2, []⟩ }
  let t₀ : State :=
    { frames := [{
        defId := 0
        locals := [
          .immediate none,
          .immediate (some (stU32Val 7)),
          .immediate (some (stU32Val 2)),
          .immediate none,
          .immediate none
        ]
        blockIdx := 0
        stmtIdx := 0
      }]
      callerMem := ⟨[]⟩
      mem := ⟨2, []⟩ }
  let sRet : State :=
    { frames := [{
        defId := 0
        locals := [
          .immediate (some (stU32Val 56)),
          .immediate (some (stU32Val 7)),
          .immediate (some (stU32Val 2)),
          .immediate (some (stU32Val 0))
        ]
        blockIdx := 3
        stmtIdx := 0
      }]
      callerMem := ⟨[]⟩
      mem := ⟨2, []⟩ }
  let tRet : State :=
    { frames := [{
        defId := 0
        locals := [
          .immediate (some (stU32Val 56)),
          .immediate (some (stU32Val 7)),
          .immediate (some (stU32Val 2)),
          .immediate (some (stU32Val 0)),
          .immediate (some (stU32Val 28))
        ]
        blockIdx := 3
        stmtIdx := 0
      }]
      callerMem := ⟨[]⟩
      mem := ⟨2, []⟩ }
  have hInitS : initState progSafeScalar4x q₂ = .ok s₀ := rfl
  have hInitT : initState progCandSimdTile4x q₂ = .ok t₀ := rfl
  have hProS :
      MirStepsDet progSafeScalar4x 3 s₀ (stateScalar4xHeader 0 8) :=
    mirStepsDet_of_execMirStepsDet progSafeScalar4x 3 rfl
  have hProT :
      MirStepsDet progCandSimdTile4x 4 t₀ (stateSimdTile4xHeader 0 2) :=
    mirStepsDet_of_execMirStepsDet progCandSimdTile4x 4 rfl
  have hBounded :
      MirBiAlignBoundedTileSpec progSafeScalar4x 16 progCandSimdTile4x 4
        rel := by
    intro k s t hRel
    cases k with
    | zero =>
      dsimp only [rel] at hRel
      rw [hRel.1, hRel.2]
      exact ⟨stateScalar4xHeader 56 0, stateSimdTile4xHeader 56 0,
        mirStepsDet_of_execMirStepsDet progSafeScalar4x 16 rfl,
        mirStepsDet_of_execMirStepsDet progCandSimdTile4x 4 rfl,
        ⟨rfl, rfl⟩⟩
    | succ k' =>
      cases k' with
      | zero =>
        dsimp only [rel] at hRel
        rw [hRel.1, hRel.2]
        exact ⟨stateScalar4xHeader 28 4, stateSimdTile4xHeader 28 1,
          mirStepsDet_of_execMirStepsDet progSafeScalar4x 16 rfl,
          mirStepsDet_of_execMirStepsDet progCandSimdTile4x 4 rfl,
          ⟨rfl, rfl⟩⟩
      | succ _ =>
        dsimp only [rel] at hRel
        exact False.elim hRel
  have hLifted :=
    mirBiAlign_bounded_tiled_sound hBounded 2
      (s₀ := stateScalar4xHeader 0 8) (t₀ := stateSimdTile4xHeader 0 2)
      ⟨rfl, rfl⟩
  refine ⟨hBounded, ?_⟩
  cases hLifted with
  | intro sₑ hsₑ =>
    cases hsₑ with
    | intro tₑ htₑ =>
      have hExitS : MirStepsDet progSafeScalar4x 1 sₑ sRet := by
        rw [htₑ.2.2.1]
        exact mirStepsDet_of_execMirStepsDet progSafeScalar4x 1 rfl
      have hExitT : MirStepsDet progCandSimdTile4x 1 tₑ tRet := by
        rw [htₑ.2.2.2]
        exact mirStepsDet_of_execMirStepsDet progCandSimdTile4x 1 rfl
      have hDoneS : evalStep progSafeScalar4x 0 sRet = .done (stRetU32 56) :=
        rfl
      have hDoneT : evalStep progCandSimdTile4x 0 tRet = .done (stRetU32 56) :=
        rfl
      have hAllS :=
        mirStepsDet_add progSafeScalar4x (3 + 16 * 2) 1
          (mirStepsDet_add progSafeScalar4x 3 (16 * 2) hProS htₑ.1) hExitS
      have hAllT :=
        mirStepsDet_add progCandSimdTile4x (4 + 4 * 2) 1
          (mirStepsDet_add progCandSimdTile4x 4 (4 * 2) hProT htₑ.2.1) hExitT
      have hBehS : Behavior progSafeScalar4x q₂ (stRetU32 56) := by
        dsimp only [Behavior, ReachesResult]
        rw [hInitS]
        exact ⟨sRet,
          reaches_of_mirStepsDet progSafeScalar4x (3 + 16 * 2 + 1) hAllS,
          ⟨0, rfl, hDoneS⟩⟩
      have hBehT : Behavior progCandSimdTile4x q₂ (stRetU32 56) := by
        dsimp only [Behavior, ReachesResult]
        rw [hInitT]
        exact ⟨tRet,
          reaches_of_mirStepsDet progCandSimdTile4x (4 + 4 * 2 + 1) hAllT,
          ⟨0, rfl, hDoneT⟩⟩
      exact ⟨s₀, t₀, sₑ, tₑ, sRet, tRet, hInitS, hInitT, hProS, hProT,
        htₑ.1, htₑ.2.1, htₑ.2.2, hExitS, hDoneS, hExitT, hDoneT,
        hBehS, hBehT⟩

/-! ## Canary 2: Refutations of Weak Relational Contracts (`L1`–`L4`) -/

/-- Safe total checked division `fn checked_div_or_zero(x: u32, y: u32) -> u32`
returning `0` when `y == 0` and `x / y` otherwise. -/
@[expose] def progSafeCheckedDiv : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "safe_twin::checked_div_or_zero"
    argumentCount := 2
    locals := [stU32Ty, stU32Ty, stU32Ty]
    basicBlocks := [
      { statements := []
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 2
        } },
      { statements := [.assign ⟨0, []⟩ (.use (stU32Const 0))]
        terminator := .return_ },
      { statements := [
          .assign ⟨0, []⟩ (.binaryOp .div (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
        ]
        terminator := .return_ }
    ]
  }]

/-- Faulty unchecked-division candidate (`Loophole L1`: divides by `0` ->
`.fault .undefined`). -/
@[expose] def progBadDivZeroUb : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "safe_twin::bad_div_zero_ub"
    isUnsafe := true
    argumentCount := 2
    locals := [stU32Ty, stU32Ty, stU32Ty]
    basicBlocks := [
      { statements := [
          .assign ⟨0, []⟩ (.binaryOp .div (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
        ]
        terminator := .return_ }
    ]
  }]

/-- Faulty `unreachable_unchecked` candidate (`Loophole L2`: branches on `0` to
`TerminatorKind.unreachable` -> `.fault .undefined`). -/
@[expose] def progBadUnreachableUb : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "safe_twin::bad_unreachable_ub"
    isUnsafe := true
    argumentCount := 2
    locals := [stU32Ty, stU32Ty, stU32Ty]
    basicBlocks := [
      { statements := []
        terminator := .switchInt (.copy ⟨2, []⟩) {
          branches := [(BitVec.ofNat 128 0, 1)]
          otherwise := 2
        } },
      { statements := []
        terminator := .unreachable },
      { statements := [
          .assign ⟨0, []⟩ (.binaryOp .div (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))
        ]
        terminator := .return_ }
    ]
  }]

/-- 1-block infinite self-loop (`Loophole L3`: hangs without faulting). -/
@[expose] def progLoopSelf1 : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "safe_twin::loop_self_1"
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [
      { statements := []
        terminator := .goto 0 }
    ]
  }]

/-- Terminating MIR program returning `42_u32` in 2 steps. -/
@[expose] def progSafeReturnU32 : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "safe_twin::return_u32"
    argumentCount := 0
    locals := [stU32Ty]
    basicBlocks := [
      { statements := [
          .assign ⟨0, []⟩ (.use (stU32Const 42))
        ]
        terminator := .return_ }
    ]
  }]

/-- Initial running state of `progLoopSelf1` at `stQuery []`. -/
@[expose] def stateLoopSelf1 : State :=
  { frames := [{
      defId := 0
      locals := [.immediate (some .unit)]
      blockIdx := 0
      stmtIdx := 0
    }]
    callerMem := ⟨[]⟩
    mem := ⟨2, []⟩ }

/-- Canary 2 (`[propext]` only): refutes `ReturnOnlyMirEquiv` (`L1` div-by-zero
UB & `L2` `unreachable` UB) and `PartialMirEquiv` (`L3` silent non-termination)
on concrete MIR programs where `SafeTwinQueryEquiv` rejects all three unsound
MIR candidates, and refutes `DiscrimOnlyTermEq` (`L4` torn pre-unwind
`CallerMemory`) via exact `TerminalOut` inequality (Profile v1 `evalStep` does
not emit `.unwound`). -/
theorem canary2_loopholes_L1_L2_L3_L4_refuted_on_mir :
    let qZero := stQuery [stU32Val 100, stU32Val 0]
    let qUnit := stQuery []
    Behavior progSafeCheckedDiv qZero (stRetU32 0) ∧
    ReturnOnlyMirEquiv progSafeCheckedDiv progBadDivZeroUb qZero ∧
    ¬ SafeTwinQueryEquiv progSafeCheckedDiv progBadDivZeroUb qZero ∧
    ReturnOnlyMirEquiv progSafeCheckedDiv progBadUnreachableUb qZero ∧
    ¬ SafeTwinQueryEquiv progSafeCheckedDiv progBadUnreachableUb qZero ∧
    PartialMirEquiv progSafeReturnU32 progLoopSelf1 qUnit ∧
    ¬ SafeTwinQueryEquiv progSafeReturnU32 progLoopSelf1 qUnit ∧
    (∃ m₁ m₂ : CallerMemory,
      DiscrimOnlyTermEq (.unwound m₁) (.unwound m₂) ∧
        TerminalOut.unwound m₁ ≠ TerminalOut.unwound m₂) := by
  intro qZero qUnit
  have hSafeDiv :=
    (behavior_iff_eq_of_wpProg_eq (p := progSafeCheckedDiv) (q := qZero)
      (fuel := 3) (out₀ := stRetU32 0) (wpProg_of_execProg rfl)).2.2
      (stRetU32 0)
  have hFaultDiv :=
    reaches_fault_and_exclusive_of_wpFault_base progBadDivZeroUb qZero 3
      .undefined (wpFaultProg_of_execFaultProg rfl)
  have hFaultUnreach :=
    reaches_fault_and_exclusive_of_wpFault_base progBadUnreachableUb qZero 3
      .undefined (wpFaultProg_of_execFaultProg rfl)
  have hwLoop1 :
      ProductiveStepWitness progLoopSelf1 (fun s => s)
        (fun s => s = stateLoopSelf1) := by
    refine ⟨?_, ?_⟩
    · intro s hs
      rw [hs]
      rfl
    · intro s hs
      exact hs
  have hInit1 : initState progLoopSelf1 qUnit = .ok stateLoopSelf1 := rfl
  have hLoop1Adq :=
    wellFormed_and_noBehavior_of_productiveWitness
      (inv := fun s => s = stateLoopSelf1) hInit1 rfl hwLoop1
  have hRetU32 :=
    behavior_iff_eq_of_wpProg_eq (p := progSafeReturnU32) (q := qUnit)
      (fuel := 3) (out₀ := stRetU32 42) (wpProg_of_execProg rfl)
  have hTear := discrimOnlyTermEq_ignores_unwound_callerMem
  refine ⟨hSafeDiv.mpr rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨⟨[]⟩, ⟨[{ allocId := 0, alignLog2 := 0, mutability := .mut,
               bytes := [.init 0xDE none], live := true }]⟩, hTear⟩⟩
  · intro out hBeh
    exact False.elim (hFaultDiv.2.2.1 (.returned out) hBeh)
  · intro hTwin
    exact hFaultDiv.2.2.2.2 hTwin.wfCand
  · intro out hBeh
    exact False.elim (hFaultUnreach.2.2.1 (.returned out) hBeh)
  · intro hTwin
    exact hFaultUnreach.2.2.2.2 hTwin.wfCand
  · exact ⟨hLoop1Adq.1, fun out hBeh => False.elim (hLoop1Adq.2.1 out hBeh)⟩
  · intro hTwin
    exact hRetU32.2.1 (hTwin.divergesIff.mp hLoop1Adq.2.2)

/-! ## Canary 3: Productive Diverging Twins & 2-to-1 `MirBiAlign` -/

/-- 2-block ping-pong reactive loop (`bb0 -> bb1 -> bb0`, 2 MIR steps per
logical cycle vs. `progLoopSelf1`'s 1 MIR step per cycle). -/
@[expose] def progLoopPingPong2 : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    identity := "safe_twin::loop_ping_pong_2"
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [
      { statements := []
        terminator := .goto 1 },
      { statements := []
        terminator := .goto 0 }
    ]
  }]

/-- Running state of `progLoopPingPong2` at block `bbIdx`. -/
@[expose] def statePingPong (bbIdx : Nat) : State :=
  { frames := [{
      defId := 0
      locals := [.immediate (some .unit)]
      blockIdx := bbIdx
      stmtIdx := 0
    }]
    callerMem := ⟨[]⟩
    mem := ⟨2, []⟩ }

/-- Next-step function on `progLoopPingPong2` states. -/
@[expose] def nextPingPong (s : State) : State :=
  match s.frames with
  | [f] =>
    if Nat.beq f.blockIdx 0 then statePingPong 1 else statePingPong 0
  | _ => s

/-- Canary 3 (`[propext]` only, `0` `Classical.choice`): proves constructive
`SafeTwinQueryEquiv progLoopPingPong2 progLoopSelf1 (stQuery [])` AND 2-to-1
`MirBiAlignTileSpec` + `mirBiAlign_tiled_sound` + `reaches_of_mirStepsDet`
across arbitrary `numTiles : Nat`. -/
theorem canary3_productive_diverging_twins_and_mirBiAlign :
    let qUnit := stQuery []
    let relSync := fun (s₂ s₁ : State) =>
      s₂ = statePingPong 0 ∧ s₁ = stateLoopSelf1
    SafeTwinQueryEquiv progLoopPingPong2 progLoopSelf1 qUnit ∧
    MirBiAlignTileSpec progLoopPingPong2 2 progLoopSelf1 1 relSync ∧
    (∀ numTiles : Nat,
      Reaches progLoopPingPong2 (statePingPong 0) (statePingPong 1) ∧
      ∃ (sₖ tₖ : State),
        MirStepsDet progLoopPingPong2 (2 * numTiles) (statePingPong 0) sₖ ∧
        MirStepsDet progLoopSelf1 (1 * numTiles) stateLoopSelf1 tₖ ∧
        relSync sₖ tₖ) := by
  intro qUnit relSync
  have hw1 :
      ProductiveStepWitness progLoopSelf1 (fun s => s)
        (fun s => s = stateLoopSelf1) :=
    ⟨fun s hs => by rw [hs]; rfl, fun _ hs => hs⟩
  have hw2 :
      ProductiveStepWitness progLoopPingPong2 nextPingPong
        (fun s => s = statePingPong 0 ∨ s = statePingPong 1) := by
    refine ⟨?_, ?_⟩
    · intro s hs
      cases hs with
      | inl h0 =>
        rw [h0]
        rfl
      | inr h1 =>
        rw [h1]
        rfl
    · intro s hs
      cases hs with
      | inl h0 =>
        rw [h0]
        exact Or.inr rfl
      | inr h1 =>
        rw [h1]
        exact Or.inl rfl
  have hInitP2 : initState progLoopPingPong2 qUnit = .ok (statePingPong 0) :=
    rfl
  have hInitP1 : initState progLoopSelf1 qUnit = .ok stateLoopSelf1 := rfl
  have hTwin :=
    safeTwinQueryEquiv_of_productiveWitnesses
      (invSafe := fun s => s = statePingPong 0 ∨ s = statePingPong 1)
      (invCand := fun s => s = stateLoopSelf1)
      hInitP2 (Or.inl rfl) hw2 hInitP1 rfl hw1
  have hTile :
      MirBiAlignTileSpec progLoopPingPong2 2 progLoopSelf1 1 relSync := by
    intro s₂ s₁ hRel
    rw [hRel.1, hRel.2]
    exact ⟨statePingPong 0, stateLoopSelf1,
      ⟨statePingPong 1, rfl, ⟨statePingPong 0, rfl, rfl⟩⟩,
      ⟨stateLoopSelf1, rfl, rfl⟩,
      ⟨rfl, rfl⟩⟩
  refine ⟨hTwin, hTile, fun numTiles => ?_⟩
  have hLifted :=
    mirBiAlign_tiled_sound hTile numTiles (s₀ := statePingPong 0)
      (t₀ := stateLoopSelf1) ⟨rfl, rfl⟩
  cases hLifted with
  | intro sₖ hsₖ =>
    cases hsₖ with
    | intro tₖ htₖ =>
      have hStepTo1 :
          MirStepsDet progLoopPingPong2 1 sₖ (statePingPong 1) := by
        rw [htₖ.2.2.1]
        exact ⟨statePingPong 1, rfl, rfl⟩
      have hStepsOdd :
          MirStepsDet progLoopPingPong2 (2 * numTiles + 1)
            (statePingPong 0) (statePingPong 1) :=
        mirStepsDet_add progLoopPingPong2 (2 * numTiles) 1 htₖ.1 hStepTo1
      have hReach :
          Reaches progLoopPingPong2 (statePingPong 0) (statePingPong 1) :=
        reaches_of_mirStepsDet progLoopPingPong2 (2 * numTiles + 1) hStepsOdd
      exact ⟨hReach, sₖ, tₖ, htₖ⟩

/-! ## Canary 4: Pure `BiAlign` Epilogue, Narrow Wrap, & `SecScalar` 2-Safety -/

/-- 4-lane vector accumulator state `(l0, l1, l2, l3)`. -/
structure Vec4Acc where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat

/-- Horizontal lane reduction `l0 + l1 + l2 + l3`. -/
@[expose] def vec4HorizontalSum (v : Vec4Acc) : Nat :=
  v.l0 + v.l1 + v.l2 + v.l3

/-- Branchless constant-time selector over `SecScalar .sec Nat`: emits public
observation trace `[.branch pubMode, .memAddr 0]` independent of `secBit`. -/
@[expose] def ctSafeMaskSelect
    (inp : Bool × SecScalar .sec Nat) : SecScalar .sec Nat × List LeakObs :=
  let out :=
    if inp.1 then secMap (fun b => b + 10) inp.2
    else secMap (fun b => b + 20) inp.2
  (out, [.branch inp.1, .memAddr 0])

/-- Branchless candidate twin using algebraic simplification while preserving
identical `LeakObs` traces. -/
@[expose] def ctAlignedMaskSelect
    (inp : Bool × SecScalar .sec Nat) : SecScalar .sec Nat × List LeakObs :=
  let delta : SecScalar .sec Nat :=
    secClassify ⟨if inp.1 then 10 else 20⟩
  (secMap2 Nat.add inp.2 delta, [.branch inp.1, .memAddr 0])

/-- Leaky candidate twin that declassifies `secBit` to branch on `secBit == 0`:
returns the exact same value as `ctSafeMaskSelect`, yet leaks `secBit` in
`LeakObs` (McLean's Refinement Paradox witness). -/
@[expose] def ctLeakyDeclassifiedSelect
    (inp : Bool × SecScalar .sec Nat) : SecScalar .sec Nat × List LeakObs :=
  let rawBit := (declassifySecScalar inp.2).raw
  let isZero := Nat.beq rawBit 0
  let out :=
    if inp.1 then secMap (fun b => b + 10) inp.2
    else secMap (fun b => b + 20) inp.2
  (out, [.branch inp.1, .branch isZero, .memAddr 0])

private theorem vec4HorizontalSum_add3 (a b c d : Nat) :
    vec4HorizontalSum ⟨a, b, c, d⟩ + 3 + 3 + 3 + 3 =
      vec4HorizontalSum ⟨a + 3, b + 3, c + 3, d + 3⟩ := by
  dsimp only [vec4HorizontalSum]
  rw [← Nat.add_assoc ((a + 3) + (b + 3) + (c + 3)) d 3,
    ← Nat.add_assoc ((a + 3) + (b + 3)) c 3,
    Nat.add_right_comm (((a + 3) + (b + 3)) + c) 3 d,
    ← Nat.add_assoc (a + 3) b 3,
    Nat.add_right_comm ((a + 3) + b) 3 c,
    Nat.add_right_comm (((a + 3) + b) + c) 3 d,
    Nat.add_right_comm a 3 b,
    Nat.add_right_comm (a + b) 3 c,
    Nat.add_right_comm (a + b + c) 3 d]

private theorem narrowAdd16_ok : 30000 + 30000 < 65536 :=
  Nat.lt_of_sub_eq_succ rfl

private theorem narrowHalf16_lt : 32768 < 65536 :=
  Nat.lt_of_sub_eq_succ rfl

/-- Canary 4 (`[propext]` only): exercises `biAlign_tiled_with_epilogue_sound`
across universal `(numTiles, rem)` on a 4-lane vector accumulator + scalar tail,
`biAlign_lockstep_fails_on_stride4`, 16-bit `narrowAddMod` guard vs. wrap
refutation (`32768 + 32768 = 65536`), and `LeakNonInterference` sequential +
aligned transfer (with functional equivalence of `ctAlignedMaskSelect`) vs.
McLean's Refinement Paradox. -/
theorem canary4_biAlign_epilogue_narrowWrap_and_ct_2safety :
    let stepS := fun acc : Nat => acc + 3
    let stepV := fun v : Vec4Acc =>
      ⟨v.l0 + 3, v.l1 + 3, v.l2 + 3, v.l3 + 3⟩
    (∀ numTiles rem : Nat,
      iterSteps stepS (4 * numTiles + rem) 0 =
        iterSteps stepS rem
          (vec4HorizontalSum (iterSteps stepV numTiles ⟨0, 0, 0, 0⟩))) ∧
    (¬ BiAlignTileSpec 1 (fun s t : Nat => s = t)
        (fun n => n + 1) (fun n => n + 4) ∧
      BiAlignTileSpec 4 (fun s t : Nat => s = t)
        (fun n => n + 1) (fun n => n + 4)) ∧
    narrowAddMod 65536 30000 30000 = 60000 ∧
    (narrowAddMod 65536 32768 32768 = 0 ∧
      narrowAddMod 65536 32768 32768 ≠ 32768 + 32768) ∧
    ((∀ inp : Bool × SecScalar .sec Nat,
        (ctAlignedMaskSelect inp).1 = (ctSafeMaskSelect inp).1) ∧
      (∀ (pubMode : Bool) (b₁ b₂ : SecScalar .sec Nat),
        (ctAlignedMaskSelect (pubMode, b₁)).2 =
          (ctAlignedMaskSelect (pubMode, b₂)).2)) ∧
    LeakNonInterference Prod.fst
      (fun inp : Bool × SecScalar .sec Nat =>
        (ctSafeMaskSelect inp).2 ++ [.varTimeOp 1]) ∧
    ((∀ inp : Bool × SecScalar .sec Nat,
        (ctLeakyDeclassifiedSelect inp).1 = (ctSafeMaskSelect inp).1) ∧
      ¬ LeakNonInterference Prod.fst
        (fun inp => (ctLeakyDeclassifiedSelect inp).2)) := by
  intro stepS stepV
  let relBody := fun (s : Nat) (v : Vec4Acc) => s = vec4HorizontalSum v
  let relTail := fun (s u : Nat) => s = u
  have hBody : BiAlignTileSpec 4 relBody stepS stepV := by
    intro s v hEq
    dsimp only [relBody, stepS, stepV, iterSteps]
    rw [hEq]
    exact vec4HorizontalSum_add3 v.l0 v.l1 v.l2 v.l3
  have hTail : BiAlignTileSpec 1 relTail stepS stepS := by
    intro s u hEq
    dsimp only [relTail, stepS, iterSteps]
    rw [hEq]
    rfl
  have hSafeNI :
      LeakNonInterference Prod.fst
        (fun inp : Bool × SecScalar .sec Nat => (ctSafeMaskSelect inp).2) := by
    intro x₁ x₂ hPub
    dsimp only [ctSafeMaskSelect]
    rw [hPub]
  have hConstNI :
      LeakNonInterference
        (Prod.fst : Bool × SecScalar .sec Nat → Bool)
        (fun _ => [LeakObs.varTimeOp 1]) :=
    fun _ _ _ => rfl
  have hAlign :
      ObsTraceAligned (fun _ : Bool × SecScalar .sec Nat => True)
        (fun inp => (ctSafeMaskSelect inp).2)
        (fun inp => (ctAlignedMaskSelect inp).2) :=
    fun _ _ => rfl
  refine ⟨fun numTiles rem =>
    biAlign_tiled_with_epilogue_sound (relTail := relTail)
      (extractTail := vec4HorizontalSum) hBody (fun _ _ h => h) hTail
      numTiles rem rfl,
    biAlign_lockstep_fails_on_stride4,
    narrowAddMod_eq_add_of_lt narrowAdd16_ok,
    narrowAddMod_ne_add_at_modulus narrowHalf16_lt narrowHalf16_lt rfl,
    ⟨fun inp => by cases inp with | mk m s => cases m <;> rfl,
     fun pubMode b₁ b₂ =>
      leakNonInterference_transfer_of_obsAligned hSafeNI hAlign
        True.intro True.intro rfl⟩,
    leakNonInterference_append hSafeNI hConstNI,
    ⟨?_, ?_⟩⟩
  · intro inp
    cases inp with
    | mk pubMode secVal =>
      cases pubMode <;> rfl
  · intro hLeakyNI
    have hBad :=
      hLeakyNI (true, ⟨0⟩) (true, ⟨1⟩) rfl
    dsimp only [ctLeakyDeclassifiedSelect, declassifySecScalar, Nat.beq] at hBad
    injection hBad with _ hTailEq
    injection hTailEq with hHeadEq _
    injection hHeadEq with hBoolEq
    exact Bool.noConfusion hBoolEq

end Anneal.SafeTwin

end
