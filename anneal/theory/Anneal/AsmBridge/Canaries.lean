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
public import Init.Data.Nat.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Trusted.MirAst.Types
public import Trusted.MirModel
public import Trusted.MirSemantics.Memory
public import Anneal.AsmBridge

public section

namespace Anneal.AsmBridge.Canaries

open Trusted.MirAst Trusted.MirSemantics
open Anneal.AsmBridge.RegLeaves
open Anneal.AsmBridge.OperandAndCap
open Anneal.AsmBridge.FlagsAndStack
open Anneal.AsmBridge.MemoryWindow

/-!
# Positive & Single-Cause Negative Canaries for `Anneal.AsmBridge`

Standalone Pass-1 canary suite (`0` `noncomputable`, `0` `._unsafe_rec`,
axioms `⊆ {propext}`) exercising every positive guarantee and single-cause
negative rejection across `RegLeaves`, `OperandAndCap`, `FlagsAndStack`, and
`MemoryWindow`.
-/

/-- Canary 1 (`RegLeaves`): exercises 11-leaf `Zmm512Leaves` lawful lenses,
cross-half orthogonality (`lo .b0_8` vs `zmm_b448_512`), EVEX vs VEX vs SSE
upper-lane behavior, `.zeroExtendTo128` vs `.mergeLowLane` sub-128 asymmetry,
zero-extending 32-bit GP refutation, and AAPCS64 `D8` vs `V8` asymmetry
(`[propext]`). -/
theorem canary_regLeaves_11leaf_zmm_and_encodings :
    let z0 : Zmm512Leaves :=
      ⟨⟨1, 2, 3, 4, 5, 6, 7⟩, ⟨100, 200, 300, 400⟩⟩
    let Llo := zmmLeafLens (.lo .b0_8)
    let Lhi := zmmLeafLens .zmm_b448_512
    let z1 := Lhi.put (Llo.put z0 (99 : UInt8)) (777 : UInt64)
    let vvvv : Vec256Leaves := ⟨11, 22, 33, 600, 700, 777, 666⟩
    let vMerge := writeVecInsnMode .vexZeroUpper .mergeLowLane .w32
      z0.lo256 vvvv ⟨9, 8, 7, 66, 55, 44, 33⟩
    let vZext := writeVecInsnMode .vexZeroUpper .zeroExtendTo128 .w32
      z0.lo256 z0.lo256 ⟨9, 8, 7, 66, 55, 44, 33⟩
    Llo.get z1 = (99 : UInt8) ∧
    Lhi.get z1 = (777 : UInt64) ∧
    (zmmLeafLens .zmm_b256_320).get z1 = (100 : UInt64) ∧
    (zmmLeafLens (.lo .ymm_b192_256)).get z1 = (7 : UInt64) ∧
    (writeZmmInsn .evexZeroUpper512 .w256 z0 z1).hi256 = ZmmHi256.zero ∧
    (writeZmmInsn .legacySsePreserveUpper .w128 z0 z1).hi256.zmm_b448_512 =
      400 ∧
    vMerge.b32_64 = 600 ∧ vMerge.b64_128 = 700 ∧ vMerge.ymm_b128_192 = 0 ∧
    vZext.b32_64 = 0 ∧ vZext.b64_128 = 0 ∧
    Gp64Leaves.beq (putLowZeroHi ⟨1, 2, 3, 42⟩ (getLow32 ⟨1, 2, 3, 42⟩))
      ⟨1, 2, 3, 42⟩ = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary 2 (`OperandAndCap` register allocation): exercises `.clobberLate`
(`clobber_abi("C")` + `in("rdi") x` admitted) vs `.clobberEarly`
(`out("rdi") _` + `in("rdi") x` rejected), `(.inlateout, .in_)` same-value vs
distinct-value `inValId?` coalescing, length/bank mismatches, and
output-output collisions (`[propext]`). -/
theorem canary_operand_timing_positive_and_single_cause_negatives :
    let ops : List AsmOperandSpec :=
      [⟨.outEarly, .gp, 64, none⟩, ⟨.lateout, .gp, 64, none⟩,
       ⟨.in_, .gp, 64, none⟩, ⟨.clobberEarly, .vec, 256, none⟩]
    let r0 : PhysReg := ⟨.gp, 0⟩
    let r1 : PhysReg := ⟨.gp, 1⟩
    let r2 : PhysReg := ⟨.gp, 2⟩
    let rdi : PhysReg := ⟨.gp, 7⟩
    let v0 : PhysReg := ⟨.vec, 0⟩
    -- Positive: distinct registers & lateout aliasing pure in_
    ValidRegAssignment ops [r0, r1, r2, v0] = true ∧
    ValidRegAssignment ops [r0, r2, r2, v0] = true ∧
    -- Positive: in("rdi") x combined with clobber_abi("C") (.clobberLate)
    ValidRegAssignment
      [⟨.in_, .gp, 64, none⟩, ⟨.clobberLate, .gp, 64, none⟩]
      [rdi, rdi] = true ∧
    -- Positive: lateout("rax") x + clobber_abi("C") with rax skipped from
    -- .clobberLate expansion (while volatile rdi stays .clobberLate)
    ValidRegAssignment
      [⟨.lateout, .gp, 64, none⟩, ⟨.in_, .gp, 64, none⟩,
       ⟨.clobberLate, .gp, 64, none⟩]
      [r0, rdi, rdi] = true ∧
    -- Single-cause negative: naive clobberLate on rax collides with lateout
    ValidRegAssignment
      [⟨.lateout, .gp, 64, none⟩, ⟨.clobberLate, .gp, 64, none⟩]
      [r0, r0] = false ∧
    -- Single-cause negative: in("rdi") x with out("rdi") _ (.clobberEarly)
    ValidRegAssignment
      [⟨.in_, .gp, 64, none⟩, ⟨.clobberEarly, .gp, 64, none⟩]
      [rdi, rdi] = false ∧
    -- Positive: (.inlateout, .in_) with matching inValId? = some 7
    ValidRegAssignment
      [⟨.inlateout, .gp, 64, some 7⟩, ⟨.in_, .gp, 64, some 7⟩]
      [r0, r0] = true ∧
    -- Single-cause negative: (.inlateout, .in_) with distinct inValId?
    ValidRegAssignment
      [⟨.inlateout, .gp, 64, some 7⟩, ⟨.in_, .gp, 64, some 8⟩]
      [r0, r0] = false ∧
    -- Single-cause negative: (.inlateout, .in_) with unknown inValId? = none
    ValidRegAssignment
      [⟨.inlateout, .gp, 64, none⟩, ⟨.in_, .gp, 64, none⟩]
      [r0, r0] = false ∧
    -- Positive: (.in_, .in_) with matching inValId? = some 1
    ValidRegAssignment
      [⟨.in_, .gp, 64, some 1⟩, ⟨.in_, .gp, 64, some 1⟩]
      [r0, r0] = true ∧
    -- Single-cause negative: (.in_, .in_) with distinct inValId?
    ValidRegAssignment
      [⟨.in_, .gp, 64, some 1⟩, ⟨.in_, .gp, 64, some 2⟩]
      [r0, r0] = false ∧
    -- Single-cause negative: (.in_, .in_) with unknown inValId? = none
    ValidRegAssignment
      [⟨.in_, .gp, 64, none⟩, ⟨.in_, .gp, 64, none⟩]
      [r0, r0] = false ∧
    -- Single-cause negative: length mismatch, bank mismatch, output collision
    ValidRegAssignment ops [r0, r1, r2] = false ∧
    ValidRegAssignment ops [v0, r1, r2, v0] = false ∧
    ValidRegAssignment ops [r0, r0, r2, v0] = false ∧
    ValidRegAssignment ops [r2, r1, r2, v0] = false ∧
    ValidRegAssignment
      [⟨.inout_, .gp, 64, none⟩, ⟨.in_, .gp, 64, none⟩]
      [r0, r0] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl⟩

/-- Canary 3 (`OperandAndCap` `N`-site register polymorphism): instantiates ONE
register-parametric proof of `twoStepSubExec` across 3 distinct inlined
physical register allocations via `regPolymorphicScheduleSound` (`[propext]`).
-/
theorem canary_reg_polymorphism_three_inlined_sites :
    let tr : RegParamTransition (Nat → Nat) :=
      { ops := twoStepSubEarlyOps
        pre := fun _ _ => True
        step := fun assign rf =>
          match assign with
          | [rDst, rA, rB] => twoStepSubExec rf rDst.idx rA.idx rB.idx
          | _ => rf
        post := fun assign rf0 rf1 =>
          match assign with
          | [rDst, rA, rB] => rf1 rDst.idx = rf0 rA.idx - rf0 rB.idx
          | _ => rf1 = rf0 }
    let site1 : List PhysReg := [⟨.gp, 0⟩, ⟨.gp, 1⟩, ⟨.gp, 2⟩]
    let site2 : List PhysReg := [⟨.gp, 8⟩, ⟨.gp, 9⟩, ⟨.gp, 10⟩]
    let site3 : List PhysReg := [⟨.gp, 12⟩, ⟨.gp, 13⟩, ⟨.gp, 14⟩]
    let sites : List (List PhysReg) := [site1, site2, site3]
    ∀ (assign : List PhysReg) (rf : Nat → Nat),
      assign ∈ sites →
      tr.post assign rf (tr.step assign rf) := by
  intro tr site1 site2 site3 sites assign rf hMem
  have hParam :
      ∀ (a : List PhysReg) (s : Nat → Nat),
        ValidRegAssignment tr.ops a = true →
        tr.pre a s →
        tr.post a s (tr.step a s) := by
    intro a s hV _
    cases a with
    | nil => exact False.elim (Bool.noConfusion hV)
    | cons rDst rest1 =>
      cases rest1 with
      | nil => exact False.elim (Bool.noConfusion hV)
      | cons rA rest2 =>
        cases rest2 with
        | nil => exact False.elim (Bool.noConfusion hV)
        | cons rB rest3 =>
          cases rest3 with
          | cons _ _ => exact False.elim (Bool.noConfusion hV)
          | nil => exact (earlyClobber_twoStep_sub_sound s rDst rA rB hV).1
  exact regPolymorphicScheduleSound tr hParam sites rfl assign rf hMem trivial

/-- Canary 4 (`OperandAndCap` capabilities & ABI): single-cause negative checks
for RFC 2396 safe-call/fn-ptr coercion, `osxsave`, EVEX `ymm16` (`idx = 16`)
under AVX2-only vs `avx512f + avx512vl + osxsave + xcr0Hi16Zmm`, architecture
isolation (`neon` never satisfies `.x86_64`), SysV and Win64 vector-ABI feature
agreement/mismatches, and AAPCS64 NEON HVA spill (`[propext]`). -/
theorem canary_clobber_abi_and_capability_single_cause_negatives :
    let sse2NoOsx : CpuFeatureSet := { sse2 := true, osxsave := false }
    let sse2 : CpuFeatureSet := { sse2 := true, osxsave := true }
    let avx : CpuFeatureSet := { sse2 := true, osxsave := true, avx := true }
    let avx2 : CpuFeatureSet := { avx with avx2 := true }
    let avx512Vl : CpuFeatureSet :=
      { avx2 with avx512f := true, avx512vl := true }
    let avx512Bw : CpuFeatureSet :=
      { avx512Vl with avx512bw := true }
    let neon : CpuFeatureSet := { neon := true }
    let sveBase : CpuFeatureSet := { neon := true, sve := true, sve2 := false }
    let osSse : OsSimdState := { xcr0Sse := true }
    let osYmm : OsSimdState := { xcr0Sse := true, xcr0Ymm := true }
    let osNoYmm : OsSimdState := { xcr0Sse := true, xcr0Ymm := false }
    let osSve256 : OsSimdState := { sveLenBytes := 32 }
    let osZmmNoHi16 : OsSimdState :=
      { xcr0Sse := true, xcr0Ymm := true, xcr0Zmm := true }
    let osZmmFull : OsSimdState :=
      { xcr0Sse := true, xcr0Ymm := true, xcr0Zmm := true,
        xcr0Hi16Zmm := true }
    let ymm16Op : AsmOperandSpec := ⟨.outEarly, .vec, 256, none⟩
    let ymm16Reg : PhysReg := ⟨.vec, 16⟩
    callTargetFeatureSafe sse2 (.safeTargetFeatures avx) = false ∧
    reifySafeFnPtrAllowed (.safeTargetFeatures avx) = false ∧
    -- Baseline x86 SSE2 xmm0 does NOT require osxsave (OSFXSR only)
    asmOperandHardwareReady .x86_64 sse2NoOsx osSse
      ⟨.in_, .vec, 128, none⟩ ⟨.vec, 0⟩ = true ∧
    -- Base AArch64 SVE z0 admitted; preg p0 is clobber-only
    asmOperandHardwareReady .aarch64 sveBase osSve256
      ⟨.outEarly, .vec, 256, none⟩ ⟨.vec, 0⟩ = true ∧
    asmOperandHardwareReady .aarch64 sveBase osSve256
      ⟨.in_, .kMask, 32, none⟩ ⟨.kMask, 0⟩ = false ∧
    asmOperandHardwareReady .aarch64 sveBase osSve256
      ⟨.clobberEarly, .kMask, 32, none⟩ ⟨.kMask, 0⟩ = true ∧
    -- x86 k0 clobber-only; >16-bit kMask needs avx512bw; AVX-512 needs Hi16
    asmOperandHardwareReady .x86_64 avx512Bw osZmmFull
      ⟨.in_, .kMask, 16, none⟩ ⟨.kMask, 0⟩ = false ∧
    asmOperandHardwareReady .x86_64 avx512Vl osZmmFull
      ⟨.clobberEarly, .kMask, 64, none⟩ ⟨.kMask, 1⟩ = false ∧
    asmOperandHardwareReady .x86_64 avx512Bw osZmmNoHi16
      ⟨.outEarly, .vec, 512, none⟩ ⟨.vec, 0⟩ = false ∧
    asmOperandHardwareReady .x86_64 avx512Bw osZmmFull
      ⟨.outEarly, .vec, 1024, none⟩ ⟨.vec, 16⟩ = false ∧
    asmOperandHardwareReady .x86_64 avx osNoYmm
      ⟨.outEarly, .vec, 256, none⟩ ⟨.vec, 0⟩ = false ∧
    -- EVEX ymm16 rejected under AVX2-only, admitted under avx512f+vl+Hi16
    asmOperandHardwareReady .x86_64 avx2 osYmm ymm16Op ymm16Reg = false ∧
    asmOperandHardwareReady .x86_64 avx512Vl osZmmFull ymm16Op ymm16Reg =
      true ∧
    -- Cross-arch isolation: neon never satisfies x86_64 vec128
    asmOperandHardwareReady .x86_64 neon osYmm
      ⟨.in_, .vec, 128, none⟩ ⟨.vec, 0⟩ = false ∧
    -- Full assignment check on AVX-512F+VL+BW with ZMM16 + k1
    asmAssignmentHardwareReady .x86_64 avx512Bw osZmmFull
      [⟨.outEarly, .vec, 512, none⟩, ⟨.clobberEarly, .kMask, 64, none⟩]
      [⟨.vec, 16⟩, ⟨.kMask, 1⟩] = true ∧
    -- SysV & Win64 vector-ABI agreement/mismatches & AAPCS64 HVA
    abiVectorCallCompatible .sysvX86_64 avx sse2 .vec256 = false ∧
    abiVectorCallCompatible .win64X86_64 sse2 neon .vec128 = false ∧
    abiVectorCallCompatible .win64X86_64 avx sse2 .vec256 = false ∧
    abiVectorCallCompatible .win64X86_64 avx512Vl avx2 .vec512 = false ∧
    abiVectorCallCompatible .win64X86_64 sse2 sse2 .vec128 = true ∧
    abiVectorCallCompatible .win64X86_64 avx avx .vec256 = true ∧
    abiVectorCallCompatible .win64X86_64 avx512Vl avx512Vl .vec512 = true ∧
    abiVectorCallCompatible .aapcs64 neon neon (.neonHva 5) = false ∧
    classifyAapcs64NeonHva 0 5 = (.invalidCount, 0) ∧
    classifyAapcs64NeonHva 6 2 = (.vRegs 6 2, 8) ∧
    classifyAapcs64NeonHva 6 3 = (.stackSpill 48, 8) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary 5 (`FlagsAndStack`): single-cause rejections for `nomem`, `readonly`,
invalid option combos, `noreturn`, undeclared `labelJump`, active Win64 vs SysV
red-zone at `curSp = entrySp`, heap buffer below stack, and x87/arch-scoped
Class-3 control flags (`[]` axioms). -/
theorem canary_flags_stack_nomem_noreturn_single_cause_negatives :
    let sysv := sysvX64StackSpec 4096
    let win64 := win64StackSpec 4096
    let entrySp : Nat := 65536
    let mem : MemoryState :=
      { nextAllocId := 3
        allocations :=
          [{ allocId := 1, alignLog2 := 3, mutability := .mut,
             bytes := [.init 1, .init 2, .init 3, .init 4],
             live := true },
           { allocId := 2, alignLog2 := 3, mutability := .mut,
             bytes := [.init 5, .init 6, .init 7, .init 8],
             live := true }] }
    let exposed : List ExposedMirAlloc := [⟨1, entrySp + 16⟩, ⟨2, 8192⟩]
    let baseOpts : InlineAsmOptions :=
      { nostack := false, preservesFlags := false, readonly := false,
        nomem := false, noreturn := false, pure_ := false, mayUnwind := false }
    let optsNoMem : InlineAsmOptions := { baseOpts with nomem := true }
    let optsReadOnly : InlineAsmOptions := { baseOpts with readonly := true }
    let optsNoRet : InlineAsmOptions := { baseOpts with noreturn := true }
    let optsBadPure : InlineAsmOptions := { baseOpts with pure_ := true }
    let optsPureNoMem : InlineAsmOptions :=
      { baseOpts with pure_ := true, nomem := true }
    let readEv : AsmStackAccess := ⟨entrySp + 16, 4, .read⟩
    let writeEv : AsmStackAccess := ⟨entrySp + 16, 4, .write⟩
    let heapWrite : AsmStackAccess := ⟨8192, 4, .write⟩
    let rzWrite : AsmStackAccess := ⟨entrySp - 16, 8, .write⟩
    let oobPtrWrite : AsmStackAccess := ⟨Nat.pow 2 64 - 4, 8, .write⟩
    let rustFrames : List ByteInterval := [⟨entrySp, 64⟩]
    asmStackAccessValid sysv baseOpts mem entrySp entrySp 8 exposed readEv =
      true ∧
    asmStackAccessValid sysv baseOpts mem entrySp entrySp 8 exposed writeEv =
      true ∧
    asmStackAccessValid sysv baseOpts mem entrySp entrySp 8 exposed heapWrite =
      true ∧
    asmStackAccessValid sysv baseOpts mem entrySp entrySp 8 exposed rzWrite =
      true ∧
    asmStackAccessValid win64 baseOpts mem entrySp entrySp 8 exposed rzWrite =
      false ∧
    asmStackAccessValid win64 baseOpts mem entrySp (entrySp - 16) 8 exposed
      rzWrite = true ∧
    -- Pointer-width wraparound past 2^64 rejected
    asmStackAccessValid sysv baseOpts mem entrySp entrySp 8 exposed
      oobPtrWrite = false ∧
    asmStackAccessValid sysv optsNoMem mem entrySp entrySp 8 exposed readEv =
      false ∧
    asmStackAccessValid sysv optsNoMem mem entrySp entrySp 8 exposed writeEv =
      false ∧
    asmStackAccessValid sysv optsReadOnly mem entrySp entrySp 8 exposed readEv =
      true ∧
    asmStackAccessValid sysv optsReadOnly mem entrySp entrySp 8 exposed
      writeEv = false ∧
    asmStackAccessValid sysv optsBadPure mem entrySp entrySp 8 exposed readEv =
      false ∧
    -- Operand/label-aware validInlineAsmSite checks
    validInlineAsmSite optsPureNoMem [⟨.in_, .gp, 64, none⟩] 0 = false ∧
    validInlineAsmSite optsPureNoMem [⟨.clobberEarly, .gp, 64, none⟩] 0 =
      false ∧
    validInlineAsmSite optsPureNoMem [⟨.outEarly, .gp, 64, none⟩] 0 = true ∧
    validInlineAsmSite optsNoRet [⟨.outEarly, .gp, 64, none⟩] 0 = false ∧
    validInlineAsmSite optsNoRet [⟨.in_, .gp, 64, none⟩] 1 = true ∧
    -- Boundary-straddling intervals rejected in isaFootprintSafe
    isaFootprintSafe sysv { baseOpts with nostack := true } entrySp entrySp
      rustFrames (observeIsaEffects [.requireWrite 61436 4100]) = false ∧
    isaFootprintSafe sysv { baseOpts with nostack := true } entrySp entrySp
      rustFrames (observeIsaEffects [.requireWrite 61436 8]) = false ∧
    -- NULL-touching stack write rejected (even when entrySp = headroom)
    asmStackAccessValid (sysvX64StackSpec 128) baseOpts mem 128 64 8 exposed
      ⟨0, 8, .write⟩ = false ∧
    isaFootprintSafe (sysvX64StackSpec 128) baseOpts 128 64 []
      (observeIsaEffects [.requireWrite 0 8]) = false ∧
    -- Red-zone underflow (curSp = 64 < redZoneBytes = 128) rejected
    asmStackAccessValid (sysvX64StackSpec 128) baseOpts mem 192 64 8 exposed
      ⟨64, 8, .write⟩ = false ∧
    isaFootprintSafe (sysvX64StackSpec 128) baseOpts 192 64 []
      (observeIsaEffects [.requireWrite 64 8]) = false ∧
    -- Positive control: curSp = 128 >= redZoneBytes = 128 admitted
    asmStackAccessValid (sysvX64StackSpec 128) baseOpts mem 192 128 8 exposed
      ⟨64, 8, .write⟩ = true ∧
    isaFootprintSafe (sysvX64StackSpec 128) baseOpts 192 128 []
      (observeIsaEffects [.requireWrite 64 8]) = true ∧
    -- Strict stack-region one-past-the-end wraparound at 2^64 rejected
    stackRegionFitsPointerBits sysv (Nat.pow 2 64 - 8) 8 = false ∧
    validAsmExits optsNoRet entrySp [0] [⟨.fallthrough, entrySp⟩] = false ∧
    validAsmExits optsNoRet entrySp [0] [⟨.labelJump 0, entrySp⟩] = true ∧
    validAsmExits baseOpts entrySp [0] [⟨.labelJump 1, entrySp⟩] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary 6 (`MemoryWindow`): single-cause negative rejections for `.uninit`
read, dead read/write, OOB read/write, `.shared` write, unmapped read/write,
return-address slot overlap, duplicate exposed alloc IDs, and stride-24
macroblock overlap, paired with symbolic `stride >= 32` macroblock disjointness
instantiation, `ExposedWindowMapWf -> asmStackAccessValid` bridge check,
provenance stripping, and unexposed-frame preservation (`[propext]`). -/
theorem canary_memory_window_uninit_shared_dead_oob_retaddr_and_macroblock :
    let spec := sysvX64StackSpec 4096
    let entrySp : Nat := 65536
    let liveMut : Allocation :=
      { allocId := 1, alignLog2 := 3, mutability := .mut,
        bytes := [.init 0x42 (some 5), .uninit],
        live := true }
    let liveShared : Allocation :=
      { allocId := 2, alignLog2 := 3, mutability := .shared,
        bytes := [.init 0x99 none],
        live := true }
    let deadMut : Allocation :=
      { allocId := 3, alignLog2 := 3, mutability := .mut,
        bytes := [.init 0x77 none],
        live := false }
    let unexposed : Allocation :=
      { allocId := 4, alignLog2 := 3, mutability := .mut,
        bytes := [.init 0xFE (some 9)],
        live := true }
    let mem : MemoryState :=
      { nextAllocId := 5
        allocations := [liveMut, liveShared, deadMut, unexposed] }
    let base1 : Nat := 16384
    let base2 : Nat := entrySp + 32
    let base3 : Nat := entrySp + 48
    let map : List ExposedMirAlloc :=
      [⟨1, base1⟩, ⟨2, base2⟩, ⟨3, base3⟩]
    let opts : InlineAsmOptions :=
      { nostack := true, preservesFlags := false, readonly := false,
        nomem := false, noreturn := false, pure_ := false, mayUnwind := false }
    readExposedMachineByte mem map base1 = some 0x42 ∧
    readExposedMachineByte mem map (base1 + 1) = none ∧
    readExposedMachineByte mem map (base1 + 2) = none ∧
    readExposedMachineByte mem map base3 = none ∧
    readExposedMachineByte mem map (entrySp + 128) = none ∧
    commitMachineByteWrites mem map [(base2, 0x11)] = none ∧
    commitMachineByteWrites mem map [(base3, 0x11)] = none ∧
    commitMachineByteWrites mem map [(base1 + 2, 0x11)] = none ∧
    ExposedWindowMapWf mem spec entrySp 8 [⟨3, base3⟩] = false ∧
    ExposedWindowMapWf mem spec entrySp 8 [⟨1, entrySp⟩] = false ∧
    ExposedWindowMapWf mem spec entrySp 8 [⟨1, base1⟩, ⟨2, base2⟩] = true ∧
    -- Unified heap-below-stack bridge check: ExposedWindowMapWf -> valid access
    asmStackAccessValid spec opts mem entrySp entrySp 8
      [⟨1, base1⟩, ⟨2, base2⟩] ⟨base1, 1, .read⟩ = true ∧
    (match commitMachineByteWrites mem [⟨1, base1⟩] [(base1, 0x55)] with
     | none => false
     | some m' =>
       match lookupMirAlloc 1 m', lookupMirAlloc 4 m' with
       | some a1, some a4 =>
         match getAllocByteAt a1.bytes 0, getAllocByteAt a4.bytes 0 with
         | some (.init b1 none), some (.init b4 (some p4)) =>
           Nat.beq b1.toNat 0x55 && Nat.beq b4.toNat 0xFE && Nat.beq p4 9
         | _, _ => false
       | _, _ => false) = true ∧
    -- Adjacent exposed allocations: single multi-byte load spanning both fails
    let adjMem : MemoryState :=
      { nextAllocId := 3
        allocations :=
          [{ allocId := 1, alignLog2 := 0, mutability := .mut,
             bytes := [.init 0x11 none], live := true },
           { allocId := 2, alignLog2 := 0, mutability := .mut,
             bytes := [.init 0x22 none], live := true }] }
    let adjMap : List ExposedMirAlloc := [⟨1, 0x20000⟩, ⟨2, 0x20001⟩]
    ExposedWindowMapWf adjMem spec entrySp 8 adjMap = true ∧
    readExposedMachineBytes spec adjMem adjMap 0x20000 1 = some [0x11] ∧
    readExposedMachineBytes spec adjMem adjMap 0x20000 2 = none ∧
    -- ExposedWindowMapWf rejects allocation wrapping past 2^64
    ExposedWindowMapWf adjMem spec entrySp 8 [⟨1, Nat.pow 2 64⟩] = false ∧
    -- Symbolic stride >= 32 instantiation on non-power-of-two stride 40
    patchesDisjoint (subBlockPatch 0x20000 40 3)
      (subBlockPatch 0x20000 40 4) = true ∧
    allSubBlocksDisjoint (entrySp + 64) 32 = true ∧
    allSubBlocksDisjoint (entrySp + 64) 24 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl,
   macroblock16_all_strides_ge32_disjoint 0x20000 40 3 4 rfl rfl rfl rfl,
   allSubBlocksDisjoint_of_stride_ge32 (65536 + 64) 32 rfl,
   allSubBlocksDisjoint_stride24_false (65536 + 64)⟩

/-- Canary 7 (`FlagsAndStack` summary admission): `InlineAsmSummaryAdmitted`
admits a disclosed `pure + nomem` summary with a value-producing `.outEarly`
operand and a disclosed `may_unwind` summary with zero labels, while rejecting
both a disclosed `pure + nomem` summary with no value output (even with a
discarded `.clobberEarly` operand) and a disclosed `may_unwind` summary with
`1` `asm_goto` label (both directly via `validInlineAsmSite` and via
`InlineAsmSummaryAdmitted`, `[]` axioms). -/
theorem canary_inlineAsmSummaryAdmitted_enforces_validSite :
    let optsPureNoMem : InlineAsmOptions :=
      { nostack := true, preservesFlags := false, readonly := false,
        nomem := true, noreturn := false, pure_ := true, mayUnwind := false }
    let optsMayUnwind : InlineAsmOptions :=
      { nostack := true, preservesFlags := false, readonly := false,
        nomem := false, noreturn := false, pure_ := false, mayUnwind := true }
    let sites : List String :=
      ["site_ok", "site_bad", "site_unwind_ok", "site_unwind_bad"]
    let okSummary : InlineAsmContractSummary Unit :=
      { siteId := "site_ok"
        options := optsPureNoMem
        operands := [⟨.in_, .gp, 64, none⟩, ⟨.outEarly, .gp, 64, none⟩]
        numLabels := 0
        pre := fun _ => True
        post := fun _ _ => True }
    let badPureSummary : InlineAsmContractSummary Unit :=
      { siteId := "site_bad"
        options := optsPureNoMem
        operands := [⟨.in_, .gp, 64, none⟩, ⟨.clobberEarly, .gp, 64, none⟩]
        numLabels := 0
        pre := fun _ => True
        post := fun _ _ => True }
    let okMayUnwindSummary : InlineAsmContractSummary Unit :=
      { siteId := "site_unwind_ok"
        options := optsMayUnwind
        operands := []
        numLabels := 0
        pre := fun _ => True
        post := fun _ _ => True }
    let badMayUnwindSummary : InlineAsmContractSummary Unit :=
      { siteId := "site_unwind_bad"
        options := optsMayUnwind
        operands := []
        numLabels := 1
        pre := fun _ => True
        post := fun _ _ => True }
    validInlineAsmSite optsMayUnwind [] 1 = false ∧
    validInlineAsmSite optsMayUnwind [] 0 = true ∧
    validAsmExits optsMayUnwind 65536 [0] [⟨.labelJump 0, 65536⟩] = false ∧
    validAsmExits optsMayUnwind 65536 [] [⟨.fallthrough, 65536⟩] = true ∧
    InlineAsmSummaryAdmitted sites okSummary ∧
    ¬ InlineAsmSummaryAdmitted sites badPureSummary ∧
    InlineAsmSummaryAdmitted sites okMayUnwindSummary ∧
    ¬ InlineAsmSummaryAdmitted sites badMayUnwindSummary := by
  refine ⟨rfl, rfl, rfl, rfl, ⟨?_, List.Mem.head _, rfl⟩, ?_,
          ⟨?_, List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl⟩, ?_⟩
  · intro hEmpty
    have hSz : (7 : Nat) = 0 := congrArg String.utf8ByteSize hEmpty
    cases hSz
  · intro hBad
    exact Bool.noConfusion hBad.2.2
  · intro hEmpty
    have hSz : (14 : Nat) = 0 := congrArg String.utf8ByteSize hEmpty
    cases hSz
  · intro hBadUnwind
    exact Bool.noConfusion hBadUnwind.2.2

/-- Canary 8 (`MemoryWindow` base-address, alignment, ZST, and wraparound
bounds): `ExposedWindowMapWf` rejects a NULL base (`0`), a misaligned base
(`16385` with `alignLog2 = 4`), a zero-length allocation at `2^64`, an
oversized alignment (`alignLog2 = 64`), and a `16`-byte aligned allocation at
`2^64 - 16` (whose one-past-the-end wraps to `0`), while admitting aligned
non-NULL bases (`16384` and `2^64 - 32` with `alignLog2 = 4`) and valid
in-bounds zero-length allocations (`[]` axioms). -/
theorem canary_exposedWindow_null_alignment_and_zst_bounds :
    let spec := sysvX64StackSpec 4096
    let entrySp : Nat := 65536
    let alignedAlloc : Allocation :=
      { allocId := 1, alignLog2 := 4, mutability := .mut,
        bytes := [.init 0x42 none], live := true }
    let zstAlloc : Allocation :=
      { allocId := 2, alignLog2 := 0, mutability := .mut,
        bytes := [], live := true }
    let hugeAlignAlloc : Allocation :=
      { allocId := 3, alignLog2 := 64, mutability := .mut,
        bytes := [.init 0x11 none], live := true }
    let alloc16 : Allocation :=
      { allocId := 4, alignLog2 := 4, mutability := .mut,
        bytes := replicateAllocByte 16 (.init 0x5A none), live := true }
    let mem : MemoryState :=
      { nextAllocId := 5
        allocations := [alignedAlloc, zstAlloc, hugeAlignAlloc, alloc16] }
    ExposedWindowMapWf mem spec entrySp 8 [⟨1, 0⟩] = false ∧
    ExposedWindowMapWf mem spec entrySp 8 [⟨1, 16385⟩] = false ∧
    ExposedWindowMapWf mem spec entrySp 8 [⟨2, Nat.pow 2 64⟩] = false ∧
    ExposedWindowMapWf mem spec entrySp 8 [⟨3, 16384⟩] = false ∧
    ExposedWindowMapWf mem spec entrySp 8 [⟨4, Nat.pow 2 64 - 16⟩] = false ∧
    ExposedWindowMapWf mem spec entrySp 8 [⟨4, Nat.pow 2 64 - 32⟩] = true ∧
    ExposedWindowMapWf mem spec entrySp 8 [⟨1, 16384⟩] = true ∧
    ExposedWindowMapWf mem spec entrySp 8 [⟨1, 16384⟩, ⟨2, 16400⟩] = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary 9 (`OperandAndCap` width bounds, SVE predicate lengths, and
lower-tier consistency): covers `.aarch64, .kMask` predicate width bounds at
`sveLenBytes = 16` (`64`, `0`, `1024` rejected; `16` admitted), invalid SVE
vector lengths (`24`, `512`), GP width bounds (`0`, `128` rejected; `64`
admitted) across all three architectures, zero-width vector operands rejected on
`.x86_64` and `.aarch64`, missing lower-tier CPU features in
`asmOperandHardwareReady` (`avx` without `sse2`, `avx512f` without `avx2`,
`sve` without `neon`), and lower-tier mismatches / incoherent feature sets in
`abiVectorCallCompatible` (`avx2`/`sse2` `.vec512` and `{sse2}`/`empty`
`.vec256` on both SysV and Win64, `[propext]`). -/
theorem canary_operand_widths_sve_pred_and_full_tier_abi :
    let sse2Only : CpuFeatureSet := { sse2 := true, osxsave := true }
    let avx2Cpu : CpuFeatureSet :=
      { sse2 := true, osxsave := true, avx := true, avx2 := true }
    let avxNoSse2 : CpuFeatureSet := { osxsave := true, avx := true }
    let avx512NoAvx2 : CpuFeatureSet :=
      { sse2 := true, osxsave := true, avx := true, avx512f := true }
    let sveBase : CpuFeatureSet := { neon := true, sve := true }
    let sveNoNeon : CpuFeatureSet := { sve := true }
    let osAvx : OsSimdState := { xcr0Sse := true, xcr0Ymm := true }
    let osZmmFull : OsSimdState :=
      { xcr0Sse := true, xcr0Ymm := true, xcr0Zmm := true,
        xcr0Hi16Zmm := true }
    let osSve16 : OsSimdState := { sveLenBytes := 16 }
    let osSveBadAlign : OsSimdState := { sveLenBytes := 24 }
    let osSveTooWide : OsSimdState := { sveLenBytes := 512 }
    -- (1) AArch64 SVE predicate (.kMask) width bounds at sveLenBytes = 16
    asmOperandHardwareReady .aarch64 sveBase osSve16
      ⟨.clobberEarly, .kMask, 64, none⟩ ⟨.kMask, 0⟩ = false ∧
    asmOperandHardwareReady .aarch64 sveBase osSve16
      ⟨.clobberEarly, .kMask, 0, none⟩ ⟨.kMask, 0⟩ = false ∧
    asmOperandHardwareReady .aarch64 sveBase osSve16
      ⟨.clobberEarly, .kMask, 1024, none⟩ ⟨.kMask, 0⟩ = false ∧
    asmOperandHardwareReady .aarch64 sveBase osSve16
      ⟨.clobberEarly, .kMask, 16, none⟩ ⟨.kMask, 0⟩ = true ∧
    -- (2) Invalid SVE vector lengths & missing NEON lower tier
    asmOperandHardwareReady .aarch64 sveBase osSveBadAlign
      ⟨.clobberEarly, .kMask, 16, none⟩ ⟨.kMask, 0⟩ = false ∧
    asmOperandHardwareReady .aarch64 sveBase osSveTooWide
      ⟨.outEarly, .vec, 256, none⟩ ⟨.vec, 0⟩ = false ∧
    asmOperandHardwareReady .aarch64 sveNoNeon osSve16
      ⟨.clobberEarly, .kMask, 16, none⟩ ⟨.kMask, 0⟩ = false ∧
    -- (3) GP width bounds (0 and 128 rejected; 64 admitted) across all 3 arches
    asmOperandHardwareReady .x86_64 sse2Only osAvx
      ⟨.in_, .gp, 0, none⟩ ⟨.gp, 0⟩ = false ∧
    asmOperandHardwareReady .x86_64 sse2Only osAvx
      ⟨.in_, .gp, 128, none⟩ ⟨.gp, 0⟩ = false ∧
    asmOperandHardwareReady .x86_64 sse2Only osAvx
      ⟨.in_, .gp, 64, none⟩ ⟨.gp, 0⟩ = true ∧
    asmOperandHardwareReady .aarch64 sveBase osSve16
      ⟨.in_, .gp, 0, none⟩ ⟨.gp, 0⟩ = false ∧
    asmOperandHardwareReady .aarch64 sveBase osSve16
      ⟨.in_, .gp, 128, none⟩ ⟨.gp, 0⟩ = false ∧
    asmOperandHardwareReady .aarch64 sveBase osSve16
      ⟨.in_, .gp, 64, none⟩ ⟨.gp, 0⟩ = true ∧
    asmOperandHardwareReady .riscv64 CpuFeatureSet.empty osSve16
      ⟨.in_, .gp, 0, none⟩ ⟨.gp, 1⟩ = false ∧
    asmOperandHardwareReady .riscv64 CpuFeatureSet.empty osSve16
      ⟨.in_, .gp, 128, none⟩ ⟨.gp, 1⟩ = false ∧
    asmOperandHardwareReady .riscv64 CpuFeatureSet.empty osSve16
      ⟨.in_, .gp, 64, none⟩ ⟨.gp, 1⟩ = true ∧
    -- (4) Zero-width vector operands rejected on x86_64 and aarch64
    asmOperandHardwareReady .x86_64 avx2Cpu osAvx
      ⟨.in_, .vec, 0, none⟩ ⟨.vec, 0⟩ = false ∧
    asmOperandHardwareReady .aarch64 sveBase osSve16
      ⟨.in_, .vec, 0, none⟩ ⟨.vec, 0⟩ = false ∧
    -- (5) Lower-tier CPU features required in asmOperandHardwareReady
    asmOperandHardwareReady .x86_64 avxNoSse2 osAvx
      ⟨.outEarly, .vec, 256, none⟩ ⟨.vec, 0⟩ = false ∧
    asmOperandHardwareReady .x86_64 avx512NoAvx2 osZmmFull
      ⟨.outEarly, .vec, 512, none⟩ ⟨.vec, 0⟩ = false ∧
    asmOperandHardwareReady .x86_64 avx512NoAvx2 osZmmFull
      ⟨.clobberEarly, .kMask, 16, none⟩ ⟨.kMask, 1⟩ = false ∧
    -- (6) Full-tier x86-64 abiVectorCallCompatible on SysV and Win64
    abiVectorCallCompatible .sysvX86_64 avx2Cpu sse2Only .vec512 = false ∧
    abiVectorCallCompatible .win64X86_64 avx2Cpu sse2Only .vec512 = false ∧
    abiVectorCallCompatible .sysvX86_64 { sse2 := true } CpuFeatureSet.empty
      .vec256 = false ∧
    abiVectorCallCompatible .win64X86_64 { sse2 := true } CpuFeatureSet.empty
      .vec256 = false ∧
    abiVectorCallCompatible .sysvX86_64 avxNoSse2 avxNoSse2 .vec256 = false ∧
    abiVectorCallCompatible .win64X86_64 avx2Cpu avx2Cpu .vec512 = true ∧
    abiVectorCallCompatible .sysvX86_64 sse2Only sse2Only .vec256 = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary 10 (`MemoryWindow` `len = 0` fail-closed resolution & multi-byte
bridge): `readExposedMachineBytes` rejects `(addr = 0, len = 0)` (even against
empty or NULL-containing maps), unmapped `(addr, len = 0)`, dead allocations
at `len = 0`, and `(2^64, len = 0)`, while admitting `len = 0` inside a live
exposed allocation, at one-past-the-end (including a boundary touching
`stackLo`), and on a live ZST; `readInitBytesFromAlloc` rejects out-of-bounds
`off > bs.length` at `len = 0`; `resolveExposedMirAccess` rejects NULL `0`;
and `exposedWindow_readBytes_implies_asmStackAccessValid` certifies the
boundary `len = 0` read under `nostack = true` (`[]` axioms). -/
theorem canary_readExposedMachineBytes_zero_len_and_sweep :
    let spec := sysvX64StackSpec 4096
    let spec32 : AsmStackSpec := ⟨32, 4096, 0⟩
    let entrySp : Nat := 65536
    let liveAlloc : Allocation :=
      { allocId := 1, alignLog2 := 4, mutability := .mut,
        bytes := [.init 0x11 none, .init 0x22 none], live := true }
    let deadAlloc : Allocation :=
      { allocId := 2, alignLog2 := 4, mutability := .mut,
        bytes := [.init 0x33 none], live := false }
    let zstAlloc : Allocation :=
      { allocId := 3, alignLog2 := 0, mutability := .mut,
        bytes := [], live := true }
    let boundaryAlloc : Allocation :=
      { allocId := 4, alignLog2 := 4, mutability := .mut,
        bytes := replicateAllocByte 16 (.init 0x44 none), live := true }
    let mem : MemoryState :=
      { nextAllocId := 5
        allocations := [liveAlloc, deadAlloc, zstAlloc, boundaryAlloc] }
    let map : List ExposedMirAlloc :=
      [⟨1, 0x20000⟩, ⟨3, 0x20010⟩, ⟨4, 61424⟩]
    let optsNoStack : InlineAsmOptions :=
      { nostack := true, preservesFlags := false, readonly := false,
        nomem := false, noreturn := false, pure_ := false, mayUnwind := false }
    -- Negative canaries: len = 0 never short-circuits on NULL/unmapped/dead/OOB
    readExposedMachineBytes spec mem [] 0 0 = none ∧
    readExposedMachineBytes spec mem [⟨1, 0⟩] 0 0 = none ∧
    readExposedMachineBytes spec mem map 0 0 = none ∧
    readExposedMachineBytes spec mem map 0x99999 0 = none ∧
    readExposedMachineBytes spec mem [⟨2, 0x20020⟩] 0x20020 0 = none ∧
    readExposedMachineBytes spec mem [⟨3, Nat.pow 2 64⟩] (Nat.pow 2 64) 0 =
      none ∧
    readExposedMachineBytes spec32 mem [⟨3, Nat.pow 2 32⟩] (Nat.pow 2 32) 0 =
      none ∧
    -- Sweep: readInitBytesFromAlloc rejects OOB off at len = 0; NULL rejected
    readInitBytesFromAlloc liveAlloc.bytes 5 0 = none ∧
    readInitBytesFromAlloc liveAlloc.bytes 2 0 = some [] ∧
    resolveExposedMirAccess mem [⟨1, 0⟩] 0 0 false = false ∧
    -- Positive canaries: len = 0 inside live alloc, ZST, and stackLo boundary
    readExposedMachineBytes spec mem map 0x20000 0 = some [] ∧
    readExposedMachineBytes spec mem map 0x20001 0 = some [] ∧
    readExposedMachineBytes spec mem map 0x20010 0 = some [] ∧
    readExposedMachineBytes spec mem map 61440 0 = some [] ∧
    asmStackAccessValid spec optsNoStack mem entrySp entrySp 8 map
      ⟨61440, 0, .read⟩ = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   exposedWindow_readBytes_implies_asmStackAccessValid _ _ _ _ _ _ _ _ [] _
     rfl rfl rfl rfl rfl rfl⟩

end Anneal.AsmBridge.Canaries

end
