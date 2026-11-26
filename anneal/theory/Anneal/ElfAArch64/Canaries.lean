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
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Anneal.ElfAArch64

public section
namespace Anneal.ElfAArch64.Canaries

open Anneal.ElfAArch64

/-!
# Kernel-Checked Canaries & Fail-Closed Regression Suite
(`Anneal.ElfAArch64.Canaries`)

Clean-room regression suite exercising `Anneal.ElfAArch64` (`Decode`,
`RelocAndElf`, `AbiAndStride`) end-to-end with axioms `⊆ {propext}`:

1. Real AArch64 instruction encodings (checked against `llvm-mc`):
   `ADD`/`SUB`/`SUBS`, bitmask `ANDS`, `MOVZ`/`MOVK`, `SXTW`/`UBFX`/`LSL`,
   `ADD` extended-register, `CMP`/`CSET`/`CSEL`, `MUL`, `B`/`B.cond`/`CBZ`/
   `TBZ`/`RET`/`NOP`/`BTI c`, GP & SIMD `LDR`/`STR`/`LDP`/`STP`, single- and
   multi-reg NEON `LD1`/`ST1` (including `.1D`), and NEON compute (`FCVTZS`,
   `SQRSHRN`/`SQRSHRN2`, `SQSHRUN`/`SQSHRUN2`, `SRI`, `UQADD`, `UQSUB`,
   `UMIN`, `UMAX`, `CMEQ #0`, `BIC`, `UZP1`/`UZP2`).
2. Architectural fail-closed decode exclusions: trailing partial words
   (`len % 4 != 0`), reserved `ADD` `sh >= 2`, invalid `DecodeBitMasks`
   (`sf=0 ∧ N=1`, all-ones `s == levels`), `MOVN/Z/K` `opc=1` and 32-bit
   `hw >= 2`, `SBFM/UBFM` `N != sf`, exception `op2[4:2] != 0`, writeback
   aliasing `Rn == Rt`, `LDP` `Rt == Rt2`, invalid `LD1`/`ST1` `opcode = 3`,
   `FCVTZS` `Q=0 ∧ immh >= 8`, `.rodata` relocations on stores, and
   un-relocated `ADR`/`ADRP`.
3. AAPCS64 upper-32-bit width-safety (`checkAapcs64WidthSafety`):
   - Rejects unextended 64-bit `subs x2, x2, #8` and `lsl x12, x3, #1` when
     `x2`/`x3` are declared `.narrow32` (`i32`/`u32`) parameters;
   - Exhibits a concrete upper-32-bit noninterference violation witness
     (`0x0000_0000_0000_0008` vs `0x0000_0001_0000_0008`);
   - Accepts both the `sxtw`-extended looped NEON kernel AND the pure
     32-bit `subs w2, w2, #8` looped NEON kernel with `checkCfgWidthInvs_sound`
     and `checkAArch64LeafAbiMonotoneBases_sound`.
4. Branchless conditional-select leaf (`cmp`/`cset`/`csel`/`ret`) accepted by
   both width-safety and fixed-base register-discipline gates.
5. AAPCS64 leaf/loop register-discipline fail-closed regressions: callee-saved
   `x19`/`x29`/`x30`, platform `x18`, `SP` touch, direct `v8` write,
   wraparound `ld1 {v6,v7,v8}` clobber, `SVC`/`BRK`/`BL`/`BR`, out-of-bounds
   branch, negative store displacement (`stp x0, x1, [x0, #-16]`), and
   missing `RET x30`.
6. Raw-byte ELF64 `ET_REL` `EM_AARCH64` object parsing (`parseElf64Object?`,
   `objectHasNoForbiddenElfFeatures`, `decodeFuncFromElf?`,
   `resolveAArch64RodataReloc`): positive controls + header (`e_machine`,
   `e_flags`, `EI_PAD`)/section/RELA/`IFUNC`/`IRELATIVE`/`W+X`/`SHF_MERGE`/
   fabricated-reloc/unaligned-slice/preceding 8-byte `ABS64` overlap/
   mismatched `ADRP`->`LO12` pairing rejections.
7. SIMD stride & plane-copy dispatch guard positive certificates and
   fail-closed rejections (base/linesize/chunk alignment, stride containment,
   overflow, zero/negative dimensions).
-/

@[expose] def canaryRelocCfg : DecodeConfig := { requireRelocForPcRel := true }
@[expose] def canaryNoRelocCfg : DecodeConfig :=
  { requireRelocForPcRel := false }

/-! ## 1. Positive AArch64 & NEON Instruction Encodings -/

theorem canary_core_encodings_decode :
    decodeWord canaryRelocCfg [] 0 0x91004020 =
      some (.addSubImm .x64 false false (.gpr .x0) false (.gpr .x1) 16 none) ∧
    decodeWord canaryRelocCfg [] 0 0xF1002042 =
      some (.addSubImm .x64 true true (.gpr .x2) false (.gpr .x2) 8 none) ∧
    decodeWord canaryRelocCfg [] 0 0x71002042 =
      some (.addSubImm .w32 true true (.gpr .x2) false (.gpr .x2) 8 none) ∧
    decodeWord canaryRelocCfg [] 0 0x93407C42 =
      some (.bitfield .x64 .sbfm (.gpr .x2) (.gpr .x2) 0 31) ∧
    decodeWord canaryRelocCfg [] 0 0xD37FF86C =
      some (.bitfield .x64 .ubfm (.gpr .x12) (.gpr .x3) 63 62) ∧
    decodeWord canaryRelocCfg [] 0 0x8B22C400 =
      some (.addSubExt .x64 false false .sxtw 1 (.gpr .x0) false (.gpr .x0)
        (.gpr .x2)) ∧
    decodeWord canaryRelocCfg [] 0 0x6B05009F =
      some (.addSubShift .w32 true true .lsl 0 .zr (.gpr .x4) (.gpr .x5)) ∧
    decodeWord canaryRelocCfg [] 0 0x1A9F37E0 =
      some (.condSel .w32 .csinc .cc (.gpr .x0) .zr .zr) ∧
    decodeWord canaryRelocCfg [] 0 0x1A823062 =
      some (.condSel .w32 .csel .cc (.gpr .x2) (.gpr .x3) (.gpr .x2)) ∧
    decodeWord canaryRelocCfg [] 0 0xD503245F = some (.bti 1) ∧
    decodeWord canaryRelocCfg [] 0 0xD65F03C0 = some (.ret (.gpr .x30)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem canary_neon_ldst_and_compute_decode :
    decodeWord canaryRelocCfg [] 0 0x4CDF7820 =
      some (.simdLdSt1 true true 1 2 .v0 (.gpr .x1) (.imm 16)) ∧
    decodeWord canaryRelocCfg [] 0 0x4C9F7404 =
      some (.simdLdSt1 false true 1 1 .v4 (.gpr .x0) (.imm 16)) ∧
    decodeWord canaryRelocCfg [] 0 0x4CDF6826 =
      some (.simdLdSt1 true true 3 2 .v6 (.gpr .x1) (.imm 48)) ∧
    -- Single- and multi-register `.1D` `ld1` (no-offset & post-index)
    decodeWord canaryRelocCfg [] 0 0x0C407C20 =
      some (.simdLdSt1 true false 1 3 .v0 (.gpr .x1) .none) ∧
    decodeWord canaryRelocCfg [] 0 0x0C40AC20 =
      some (.simdLdSt1 true false 2 3 .v0 (.gpr .x1) .none) ∧
    decodeWord canaryRelocCfg [] 0 0x0CDFAC20 =
      some (.simdLdSt1 true false 2 3 .v0 (.gpr .x1) (.imm 16)) ∧
    decodeWord canaryRelocCfg [] 0 0x4F21FC84 =
      some (.simdShiftImm .fcvtzs true 4 1 .v4 .v4) ∧
    decodeWord canaryRelocCfg [] 0 0x0F109C84 =
      some (.simdShiftImm .sqrshrn false 2 0 .v4 .v4) ∧
    decodeWord canaryRelocCfg [] 0 0x4F109CA4 =
      some (.simdShiftImm .sqrshrn true 2 0 .v4 .v5) ∧
    decodeWord canaryRelocCfg [] 0 0x6E220C20 =
      some (.simdThreeSame .uqadd true 0 .v0 .v1 .v2) ∧
    decodeWord canaryRelocCfg [] 0 0x4E209841 =
      some (.simdCmeqZero true 0 .v1 .v2) ∧
    decodeWord canaryRelocCfg [] 0 0x4E025820 =
      some (.simdPerm .uzp2 true 0 .v0 .v1 .v2) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Fail-Closed Decode Exclusions -/

theorem canary_decode_fail_closed :
    -- Trailing partial words (`len % 4 != 0`) rejected
    decodeStream canaryRelocCfg [] [0xC0, 0x03, 0x5F] = none ∧
    decodeStream canaryRelocCfg [] [0xC0, 0x03, 0x5F, 0xD6, 0x1F] = none ∧
    -- Reserved ADD imm bit 23 = 1 (`sh >= 2`)
    decodeWord canaryRelocCfg [] 0 0x91804020 = none ∧
    -- Invalid DecodeBitMasks: 32-bit N=1 (`0x12400000`) & all-ones `imms=63`
    decodeWord canaryRelocCfg [] 0 0x12400000 = none ∧
    decodeWord canaryRelocCfg [] 0 0x9240FC00 = none ∧
    -- MOV wide: reserved `opc=1` (`0x32800000`) & 32-bit `hw=2` (`0x52C00000`)
    decodeWord canaryRelocCfg [] 0 0x32800000 = none ∧
    decodeWord canaryRelocCfg [] 0 0x52C00000 = none ∧
    -- Bitfield: N != sf (`0x93007C42` has sf=1, N=0)
    decodeWord canaryRelocCfg [] 0 0x93007C42 = none ∧
    -- Exception generation: non-zero `op2[4:2]` (`0xD4000005`, UNALLOCATED)
    decodeWord canaryRelocCfg [] 0 0xD4000005 = none ∧
    -- GP LDR post-index writeback aliasing `Rn == Rt` (`ldr x1, [x1], #8`)
    decodeWord canaryRelocCfg [] 0 0xF8408421 = none ∧
    -- GP LDP load with `Rt == Rt2` (`ldp x4, x4, [x1]`)
    decodeWord canaryRelocCfg [] 0 0xA9401024 = none ∧
    -- Invalid LD1/ST1 `opcode = 0x3` (UNALLOCATED)
    decodeWord canaryRelocCfg [] 0 0x0C403020 = none ∧
    -- FCVTZS (vector fixed-point) with `Q=0 ∧ immh=8` (UNDEFINED)
    decodeWord canaryRelocCfg [] 0 0x0F41FC84 = none ∧
    -- Store (`str q0, [x0]`) with `.rodata` `LDST128_ABS_LO12_NC` rejected
    decodeWord canaryRelocCfg
      [{ offset := 0, kind := .ldst128AbsLo12Nc, secIdx := 2,
         target := Int.ofNat 0 }] 0 0x3D800000 = none ∧
    -- Un-relocated ADRP rejected in relocatable object mode
    decodeWord canaryRelocCfg [] 0 0x90000000 = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. AAPCS64 Upper-32-Bit Width-Safety Canaries -/

/-- Signature `fn(dst: *mut u8, src: *const u8, count: i32, channels: i32)`. -/
@[expose] def canaryNarrowLoopSig : Aapcs64Sig :=
  { params := [(.x0, .full64), (.x1, .full64),
               (.x2, .narrow32), (.x3, .narrow32)] }

/-- Buggy pattern: unextended `subs x2, x2, #8` consumes upper 32 bits of
`i32` parameter `x2`. -/
@[expose] def canaryBuggyUnextendedLoopBytes : List UInt8 :=
  [ 0x42, 0x20, 0x00, 0xF1, -- subs x2, x2, #8        (BUG: reads x2[63:32]!)
    0x20, 0x78, 0xDF, 0x4C, -- ld1  {v0.4s}, [x1], #16
    0x00, 0x78, 0x9F, 0x4C, -- st1  {v0.4s}, [x0], #16
    0xA1, 0xFF, 0xFF, 0x54, -- b.ne #-12              (loops to PC 0)
    0xC0, 0x03, 0x5F, 0xD6  -- ret
  ]

/-- Buggy pattern: unextended `lsl x12, x3, #1` (`ubfm x12, x3, #63, #62`)
consumes bits `[62:32]` of `i32` parameter `x3`. -/
@[expose] def canaryBuggyUnextendedStrideBytes : List UInt8 :=
  [ 0x6C, 0xF8, 0x7F, 0xD3, -- lsl  x12, x3, #1       (BUG: reads x3[62:32]!)
    0x00, 0x00, 0x0C, 0x8B, -- add  x0, x0, x12
    0xC0, 0x03, 0x5F, 0xD6  -- ret
  ]

/-- Fixed pattern A: explicit `sxtw x2, w2` + `sxtw x3, w3` before 64-bit
arithmetic and NEON post-index loop. -/
@[expose] def canaryFixedSxtwLoopBytes : List UInt8 :=
  [ 0x5F, 0x24, 0x03, 0xD5, -- bti  c
    0x42, 0x7C, 0x40, 0x93, -- sxtw x2, w2            (sign-extends [31:0])
    0x63, 0x7C, 0x40, 0x93, -- sxtw x3, w3            (sign-extends [31:0])
    0x6C, 0xF8, 0x7F, 0xD3, -- lsl  x12, x3, #1       (safe: x3 is full64)
    0x42, 0x20, 0x00, 0xF1  -- subs x2, x2, #8        (safe: x2 is full64)
  ] ++
  [ 0x20, 0x78, 0xDF, 0x4C, -- ld1  {v0.4s}, [x1], #16
    0x00, 0x78, 0x9F, 0x4C, -- st1  {v0.4s}, [x0], #16
    0xA1, 0xFF, 0xFF, 0x54, -- b.ne #-12              (loops to PC 4)
    0xC0, 0x03, 0x5F, 0xD6  -- ret
  ]

/-- Fixed pattern B: 32-bit `subs w2, w2, #8` zero-extends `x2[63:32] := 0`. -/
@[expose] def canaryFixedW32LoopBytes : List UInt8 :=
  [ 0x42, 0x20, 0x00, 0x71, -- subs w2, w2, #8        (reads w2[31:0], zeros hi)
    0x20, 0x78, 0xDF, 0x4C, -- ld1  {v0.4s}, [x1], #16
    0x00, 0x78, 0x9F, 0x4C, -- st1  {v0.4s}, [x0], #16
    0xA1, 0xFF, 0xFF, 0x54, -- b.ne #-12              (loops to PC 0)
    0xC0, 0x03, 0x5F, 0xD6  -- ret
  ]

@[expose] def decodeInsnsOnly (bs : List UInt8) : List DecodedInsn :=
  match decodeStream canaryRelocCfg [] bs with
  | some tr => tr.map (fun e => e.2)
  | none => []

theorem canary_aapcs64_width_safety_rejects_unextended_and_accepts_fixed :
    checkAapcs64WidthSafety canaryNarrowLoopSig
      (decodeInsnsOnly canaryBuggyUnextendedLoopBytes) = false ∧
    checkAapcs64WidthSafety canaryNarrowLoopSig
      (decodeInsnsOnly canaryBuggyUnextendedStrideBytes) = false ∧
    checkAapcs64WidthSafety canaryNarrowLoopSig
      (decodeInsnsOnly canaryFixedSxtwLoopBytes) = true ∧
    checkAapcs64WidthSafety canaryNarrowLoopSig
      (decodeInsnsOnly canaryFixedW32LoopBytes) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem canary_aapcs64_width_safety_rejects_indirect_ret_and_x30_write :
    let badRetX0 : List DecodedInsn :=
      [.ret (.gpr .x0),
       .addSubImm .x64 true true (.gpr .x2) false (.gpr .x2) 8 none,
       .ret (.gpr .x30)]
    let badWriteX30 : List DecodedInsn :=
      [.addSubImm .x64 false false (.gpr .x30) false (.gpr .x0) 0 none,
       .ret (.gpr .x30),
       .addSubImm .x64 true true (.gpr .x2) false (.gpr .x2) 8 none,
       .ret (.gpr .x30)]
    -- Non-`x30` `RET` rejected by `insnSuccPcs?`, `allIntraFuncBranchesValid`,
    -- and `checkAapcs64WidthSafety`
    insnSuccPcs? 0 3 (.ret (.gpr .x0)) = none ∧
    allIntraFuncBranchesValid badRetX0 = false ∧
    checkAapcs64WidthSafety canaryNarrowLoopSig badRetX0 = false ∧
    -- Writing `x30` before `RET x30` rejected by `allIntraFuncBranchesValid`
    -- and `checkAapcs64WidthSafety`
    allIntraFuncBranchesValid badWriteX30 = false ∧
    checkAapcs64WidthSafety canaryNarrowLoopSig badWriteX30 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Concrete upper-32-bit noninterference counterexample: `rfClean` has
`x2 = 8`, `rfTainted` has `x2 = 0x1_0000_0008`. Both satisfy AAPCS64 entry
equivalence (`WidthEnvAgree (initWidthEnv canaryNarrowLoopSig)`), yet the
unextended `subs x2, x2, #8` violates `InsnReadsAgree`. -/
@[expose] def rfClean : RegFile64
  | .x0 => 0x1000
  | .x1 => 0x2000
  | .x2 => 8
  | .x3 => 2
  | _   => 0

@[expose] def rfTainted : RegFile64
  | .x0 => 0x1000
  | .x1 => 0x2000
  | .x2 => 4294967304 -- 0x1_0000_0008 (upper 32 bits = 1, low 32 bits = 8)
  | .x3 => 2
  | _   => 0

theorem canary_upper32_taint_is_aapcs64_entry_equiv :
    WidthEnvAgree (initWidthEnv canaryNarrowLoopSig) rfClean rfTainted := by
  intro r
  cases r <;> first | rfl | exact True.intro

theorem canary_unextended_subs_violates_reads_agree :
    ¬InsnReadsAgree
      (.addSubImm .x64 true true (.gpr .x2) false (.gpr .x2) 8 none)
      rfClean rfTainted := by
  intro h
  have hBad := h (.x2, true) (List.Mem.head [])
  change 8 = 4294967304 at hBad
  cases hBad

/-- Kernel-checked monotone-base ABI/SFI certificate on the fixed NEON loop. -/
theorem canary_fixed_neon_loop_abi_sfi_cert :
    AArch64LeafAbiMonotoneBasesCert [.x0]
      (decodeInsnsOnly canaryFixedSxtwLoopBytes) :=
  checkAArch64LeafAbiMonotoneBases_sound [.x0]
    (decodeInsnsOnly canaryFixedSxtwLoopBytes) rfl

/-! ## 4. Branchless Conditional-Select Arithmetic Leaf Canary -/

/-- Signature `fn(w0: u32, w1: u32, w2: u32, w3: u32, w4: u32, w5: u32)`. -/
@[expose] def canaryCondSelSig : Aapcs64Sig :=
  { params := [(.x0, .narrow32), (.x1, .narrow32), (.x2, .narrow32),
               (.x3, .narrow32), (.x4, .narrow32), (.x5, .narrow32)] }

/-- Branchless conditional select (`cmp w4, w5; cset w0, hs`,
`csel w2, w3, w2, lo; csel w1, w5, w1, lo; ret`). -/
@[expose] def canaryCondSelBytes : List UInt8 :=
  [ 0x9F, 0x00, 0x05, 0x6B, -- cmp  w4, w5
    0xE0, 0x37, 0x9F, 0x1A, -- cset w0, hs
    0x62, 0x30, 0x82, 0x1A, -- csel w2, w3, w2, lo
    0xA1, 0x30, 0x81, 0x1A, -- csel w1, w5, w1, lo
    0xC0, 0x03, 0x5F, 0xD6  -- ret
  ]

theorem canary_condsel_leaf_passes_width_and_fixed_sfi :
    localDecodeCoverageOk canaryRelocCfg [] canaryCondSelBytes = true ∧
    checkAapcs64WidthSafety canaryCondSelSig
      (decodeInsnsOnly canaryCondSelBytes) = true ∧
    checkAArch64LeafAbiFixedBases []
      (decodeInsnsOnly canaryCondSelBytes) = true :=
  ⟨rfl, rfl, rfl⟩

/-! ## 5. AAPCS64 ABI/SFI Fail-Closed Regressions -/

theorem canary_abi_sfi_fail_closed :
    -- Callee-saved GPR `x19` write rejected
    checkAArch64LeafAbiFixedBases [.x0]
      [.moveWide .x64 .movz (.gpr .x19) 1 0, .ret (.gpr .x30)] = false ∧
    -- Platform register `x18` write rejected
    checkAArch64LeafAbiFixedBases [.x0]
      [.moveWide .x64 .movz (.gpr .x18) 1 0, .ret (.gpr .x30)] = false ∧
    -- `SP` modification rejected
    checkAArch64LeafAbiFixedBases [.x0]
      [.addSubImm .x64 true false .sp false .sp 16 none,
       .ret (.gpr .x30)] = false ∧
    -- Direct write to callee-saved SIMD `v8` rejected
    checkAArch64LeafAbiFixedBases [.x0]
      [.simdThreeSame .uqadd true 0 .v8 .v0 .v1, .ret (.gpr .x30)] = false ∧
    -- Wraparound multi-reg `ld1 {v6.4s, v7.4s, v8.4s}, [x1], #48` touches `v8`
    checkAArch64LeafAbiMonotoneBases [.x0]
      [.simdLdSt1 true true 3 2 .v6 (.gpr .x1) (.imm 48),
       .ret (.gpr .x30)] = false ∧
    -- `SVC` / `BL` / `BR` rejected
    checkAArch64LeafAbiFixedBases [.x0] [.trapOrSys, .ret (.gpr .x30)] =
      false ∧
    checkAArch64LeafAbiFixedBases [.x0] [.branch true (Int.ofNat 0),
      .ret (.gpr .x30)] = false ∧
    checkAArch64LeafAbiFixedBases [.x0] [.branchReg false (.gpr .x16),
      .ret (.gpr .x30)] = false ∧
    -- Out-of-bounds intra-function branch rejected
    checkAArch64LeafAbiFixedBases [.x0]
      [.branchCond .ne (Int.ofNat 16), .ret (.gpr .x30)] = false ∧
    -- Non-monotone clobber of store base `x0` rejected by Tier 2
    checkAArch64LeafAbiMonotoneBases [.x0]
      [.addSubImm .x64 true false (.gpr .x0) false (.gpr .x0) 16 none,
       .ret (.gpr .x30)] = false ∧
    -- Fixed-base tier rejects post-index store on `x0`
    checkAArch64LeafAbiFixedBases [.x0]
      [.simdLdSt1 false true 1 1 .v4 (.gpr .x0) (.imm 16),
       .ret (.gpr .x30)] = false ∧
    -- Negative signed store displacement (`stp x0, x1, [x0, #-16]`) rejected
    checkAArch64LeafAbiFixedBases [.x0]
      (decodeInsnsOnly [0x00, 0x04, 0x3F, 0xA9, 0xC0, 0x03, 0x5F, 0xD6]) =
      false ∧
    checkAArch64LeafAbiMonotoneBases [.x0]
      (decodeInsnsOnly [0x00, 0x04, 0x3F, 0xA9, 0xC0, 0x03, 0x5F, 0xD6]) =
      false ∧
    -- Aliasing post-index GP load (`ldr x0, [x0], #8`) cannot advance `x0`
    checkAArch64LeafAbiMonotoneBases [.x0]
      [.gpLoadStore true 8 false .x64 (.gpr .x0) (.gpr .x0)
         (.postIndex (Int.ofNat 8)) none,
       .ret (.gpr .x30)] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 6. Complete Raw-Byte ELF64 `EM_AARCH64` Object Canaries -/

/-- Helper: encode a `Nat` as `k` little-endian `UInt8` bytes via `@Nat.rec`. -/
@[expose] def encLeBytes (k v : Nat) : List UInt8 :=
  @Nat.rec (fun _ => Nat → List UInt8)
    (fun _ => [])
    (fun _ ih rem =>
      UInt8.ofNat (Nat.mod rem 256) :: ih (Nat.div rem 256))
    k v

/-- Encode a 64-byte `Elf64_Ehdr` for `EM_AARCH64` (`183`) with right-associated
concatenation for shallow kernel replay. -/
@[expose] def mkElf64Ehdr (eMach eShoff eShnum eShstrndx : Nat)
    (eiVer : Nat := 1) (eVer : Nat := 1) (eiPad9 : Nat := 0)
    (eFlags : Nat := 0) : List UInt8 :=
  [ 0x7F, 0x45, 0x4C, 0x46, 2, 1, UInt8.ofNat eiVer, 0, 0,
    UInt8.ofNat eiPad9, 0, 0, 0, 0, 0, 0,
    1, 0 ] ++ -- ET_REL = 1
  (encLeBytes 2 eMach ++
  (encLeBytes 4 eVer ++
  ([ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ] ++ -- e_entry, e_phoff
  (encLeBytes 8 eShoff ++
  (encLeBytes 4 eFlags ++
  ([ 64, 0, 0, 0, 0, 0, 64, 0 ] ++ -- ehsize=64, phent=0, phnum=0, shent=64
  (encLeBytes 2 eShnum ++
  encLeBytes 2 eShstrndx)))))))

/-- Encode a 64-byte `Elf64_Shdr` with right-associated concatenation. -/
@[expose] def mkElf64Shdr (shName shType shFlags shOffset shSize shLink shInfo
    shEntsize : Nat) (shAlign : Nat := 4) : List UInt8 :=
  encLeBytes 4 shName ++
  (encLeBytes 4 shType ++
  (encLeBytes 8 shFlags ++
  ([ 0, 0, 0, 0, 0, 0, 0, 0 ] ++ -- sh_addr = 0
  (encLeBytes 8 shOffset ++
  (encLeBytes 8 shSize ++
  (encLeBytes 4 shLink ++
  (encLeBytes 4 shInfo ++
  (encLeBytes 8 shAlign ++
  encLeBytes 8 shEntsize))))))))

/-- Encode a 24-byte `Elf64_Sym` with right-associated concatenation. -/
@[expose] def mkElf64Sym (stName stInfo stShndx stValue stSize : Nat) :
    List UInt8 :=
  encLeBytes 4 stName ++
  ([UInt8.ofNat stInfo, 0] ++
  (encLeBytes 2 stShndx ++
  (encLeBytes 8 stValue ++
  encLeBytes 8 stSize)))

/-- Encode a 24-byte `Elf64_Rela` with right-associated concatenation. -/
@[expose] def mkElf64Rela (rOff rSym rType rAddendU64 : Nat) : List UInt8 :=
  encLeBytes 8 rOff ++
  (encLeBytes 8 (4294967296 * rSym + rType) ++
  encLeBytes 8 rAddendU64)

/-- Pre-encoded static 24-byte null symbol (`STN_UNDEF`). -/
@[expose] def canarySym0 : List UInt8 :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]

/-- Pre-encoded static 64-byte `SHT_NULL` section header (`sh0`). -/
@[expose] def canarySh0 : List UInt8 :=
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ] ++
  [ 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]

/-- Parameterized tail section headers (`sh3` `.symtab`, `sh4` `.strtab`,
`sh5` `.rela.text`, `sh6` `.shstrtab`), where byte 9 of each header encodes
bits `[15:8]` of `sh_flags` (`8` = `0x0800` = `SHF_COMPRESSED`). -/
@[expose] def mkCanaryShTail
    (symFHi strFHi relaFHi shstrFHi : UInt8 := 0) : List UInt8 :=
  -- sh3: .symtab (name=15, type=2, off=92, sz=48, link=4, info=2, esz=24)
  [ 15, 0, 0, 0, 2, 0, 0, 0, 0, symFHi, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 92, 0, 0, 0, 0, 0, 0, 0 ] ++
  ([ 48, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0,
     4, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0 ] ++
  -- sh4: .strtab (name=23, type=3, off=140, sz=4)
  ([ 23, 0, 0, 0, 3, 0, 0, 0, 0, strFHi, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 140, 0, 0, 0, 0, 0, 0, 0 ] ++
  ([ 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ] ++
  -- sh5: .rela.text (name=31, type=4, off=144, sz=48, link=3, info=1, esz=24)
  ([ 31, 0, 0, 0, 4, 0, 0, 0, 0, relaFHi, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 144, 0, 0, 0, 0, 0, 0, 0 ] ++
  ([ 48, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0,
     4, 0, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0 ] ++
  -- sh6: .shstrtab (name=42, type=3, off=192, sz=52)
  ([ 42, 0, 0, 0, 3, 0, 0, 0, 0, shstrFHi, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 192, 0, 0, 0, 0, 0, 0, 0 ] ++
  [ 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ]))))))

/-- Pre-encoded static tail section headers (`sh3`..`sh6`) with zero flags. -/
@[expose] def canaryStaticShTail : List UInt8 := mkCanaryShTail 0 0 0 0

/-- Minimal `.shstrtab`: `""` (0), `".text"` (1), `".rodata"` (7), `".symtab"`
(15), `".strtab"` (23), `".rela.text"` (31), `".shstrtab"` (42). Total = 52 B.
-/
@[expose] def canaryShstrtab : List UInt8 :=
  [ 0,
    0x2E, 0x74, 0x65, 0x78, 0x74, 0,                             -- .text (1)
    0x2E, 0x72, 0x6F, 0x64, 0x61, 0x74, 0x61, 0,                 -- .rodata (7)
    0x2E, 0x73, 0x79, 0x6D, 0x74, 0x61, 0x62, 0                  -- .symtab (15)
  ] ++
  [ 0x2E, 0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0,                 -- .strtab (23)
    0x2E, 0x72, 0x65, 0x6C, 0x61, 0x2E, 0x74, 0x65, 0x78, 0x74, 0, -- .rela.text
    0x2E, 0x73, 0x68, 0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0      -- .shstrtab
  ]

/-- Minimal `.strtab`: `"" (0), "c0" (1)`. Total = 4 bytes. -/
@[expose] def canaryStrtab : List UInt8 := [0, 0x63, 0x30, 0]

/-- 12-byte `.text`: `adrp x0, c0; ldr q0, [x0, #0]; ret` with two `.rodata`
relocations (`R_AARCH64_ADR_PREL_PG_HI21` at 0, `R_AARCH64_LDST128_ABS_LO12_NC`
at 4). -/
@[expose] def canaryElfText : List UInt8 :=
  [ 0x00, 0x00, 0x00, 0x90, -- adrp x0, #0
    0x00, 0x00, 0xC0, 0x3D, -- ldr  q0, [x0]
    0xC0, 0x03, 0x5F, 0xD6  -- ret
  ]

/-- 16-byte `.rodata` constant payload. -/
@[expose] def canaryElfRodata : List UInt8 :=
  [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16 ]

/-- Build a parameterized complete ELF64 `EM_AARCH64` object image for positive
and negative regression testing.
Layout:
- `[0, 64)`: `Elf64_Ehdr`
- `[64, 76)`: `.text` (12B)
- `[76, 92)`: `.rodata` (16B)
- `[92, 140)`: `.symtab` (2 × 24B = 48B)
- `[140, 144)`: `.strtab` (4B)
- `[144, 192)`: `.rela.text` (2 × 24B = 48B)
- `[192, 244)`: `.shstrtab` (52B)
- `[244, 692)`: 7 × 64B `Elf64_Shdr` (448B). -/
@[expose] def mkCanaryElfObj
    (eMach : Nat := EM_AARCH64)
    (roFlags : Nat := SHF_ALLOC)
    (roEntsize : Nat := 0)
    (symInfo : Nat := 1) -- STB_LOCAL (0) | STT_OBJECT (1)
    (rela0Off : Nat := 0)
    (rela0Type : Nat := R_AARCH64_ADR_PREL_PG_HI21)
    (rela0Add : Nat := 0)
    (rela1Off : Nat := 4)
    (rela1Type : Nat := R_AARCH64_LDST128_ABS_LO12_NC)
    (rela1Add : Nat := 0)
    (textFlags : Nat := SHF_ALLOC + SHF_EXECINSTR)
    (sh1Name : Nat := 1)
    (eiPad9 : Nat := 0)
    (eFlags : Nat := 0)
    (roAlign : Nat := 16)
    (roSize : Nat := 16)
    (sym1Val : Nat := 0)
    (rela1Sym : Nat := 1)
    (sym0Bytes : List UInt8 := canarySym0)
    (shTail : List UInt8 := canaryStaticShTail)
    (textBytes : List UInt8 := canaryElfText) : List UInt8 :=
  let hdr := mkElf64Ehdr eMach 244 7 6 1 1 eiPad9 eFlags
  let sym1 := mkElf64Sym 1 symInfo 2 sym1Val 16
  let rela0 := mkElf64Rela rela0Off 1 rela0Type rela0Add
  let rela1 := mkElf64Rela rela1Off rela1Sym rela1Type rela1Add
  let sh1 := mkElf64Shdr sh1Name SHT_PROGBITS textFlags 64 12 0 0 0 4
  let sh2 := mkElf64Shdr 7 SHT_PROGBITS roFlags 76 roSize 0 0 roEntsize roAlign
  hdr ++ (textBytes ++ (canaryElfRodata ++ (sym0Bytes ++ (sym1 ++
    (canaryStrtab ++ (rela0 ++ (rela1 ++ (canaryShstrtab ++
    (canarySh0 ++ (sh1 ++ (sh2 ++ shTail)))))))))))

/-- 12-byte `.text` with wrong `ADRP` register (`adrp x1, c0; ldr q0, [x0]`).
-/
@[expose] def canaryWrongAdrpRegText : List UInt8 :=
  [ 0x01, 0x00, 0x00, 0x90, -- adrp x1, #0
    0x00, 0x00, 0xC0, 0x3D, -- ldr  q0, [x0]  (reads x0, not x1!)
    0xC0, 0x03, 0x5F, 0xD6  -- ret
  ]

/-- 12-byte `.text` with 8 bytes of literal pool before `ret` at offset 8. -/
@[expose] def canaryLitPoolBeforeRetText : List UInt8 :=
  [ 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00,
    0xC0, 0x03, 0x5F, 0xD6  -- ret at offset 8
  ]

@[expose] def canaryValidElfObj : List UInt8 := mkCanaryElfObj

theorem canary_elf64_positive_valid :
    objectHasNoForbiddenElfFeatures canaryValidElfObj = true ∧
    (decodeFuncFromElf? canaryRelocCfg canaryValidElfObj 1 0 12).isSome =
      true ∧
    resolveAArch64RodataReloc canaryValidElfObj 1 0
      { rOffset := 4, rSym := 1, rType := R_AARCH64_LDST128_ABS_LO12_NC,
        rAddend := Int.ofNat 0 } =
      some { offset := 4, kind := .ldst128AbsLo12Nc, secIdx := 2,
             target := Int.ofNat 0 } :=
  ⟨rfl, rfl, rfl⟩

theorem canary_elf64_positive_merge :
    -- SHF_MERGE same-entry positive control (`entsize = 16`, `sym.stValue = 0`)
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (roFlags := SHF_ALLOC + SHF_MERGE) (roEntsize := 16))
      1 0 12).isSome = true :=
  rfl

theorem canary_elf64_positive_nonoverlap_and_jump26 :
    -- Non-overlapping 8B `R_AARCH64_ABS64` (257) at offset 0 (`[0, 8)`)
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (rela0Off := 0) (rela0Type := 257)
        (rela1Off := 0) (rela1Type := 257)
        (textBytes := canaryLitPoolBeforeRetText))
      1 8 4).isSome = true ∧
    -- Preceding 4B `R_AARCH64_JUMP26` (282) at offset 4 (`[4, 8)`)
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (rela0Off := 4) (rela0Type := 282)
        (rela1Off := 0) (rela1Type := 257)
        (textBytes := canaryLitPoolBeforeRetText))
      1 8 4).isSome = true :=
  ⟨rfl, rfl⟩

theorem canary_elf64_reject_header_fields :
    -- Wrong machine (`EM_X86_64`), non-zero `EI_PAD[9]`, non-zero `e_flags`
    (parseElf64Object? (mkCanaryElfObj (eMach := 62))).isNone = true ∧
    (parseElf64Object? (mkCanaryElfObj (eiPad9 := 1))).isNone = true ∧
    (parseElf64Object? (mkCanaryElfObj (eFlags := 1))).isNone = true :=
  ⟨rfl, rfl, rfl⟩

theorem canary_elf64_reject_wx_and_ifunc :
    -- `W+X` `.text` and `STT_GNU_IFUNC` (`stInfo = 10`) rejected
    objectHasNoForbiddenElfFeatures
      (mkCanaryElfObj (textFlags := SHF_ALLOC + SHF_WRITE + SHF_EXECINSTR)) =
      false ∧
    objectHasNoForbiddenElfFeatures
      (mkCanaryElfObj (symInfo := STT_GNU_IFUNC)) = false :=
  ⟨rfl, rfl⟩

theorem canary_elf64_reject_irelative_and_rodata_write :
    -- `R_AARCH64_IRELATIVE` (1032) and writable `.rodata` (`SHF_WRITE`)
    objectHasNoForbiddenElfFeatures
      (mkCanaryElfObj (rela1Type := R_AARCH64_IRELATIVE)) = false ∧
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (roFlags := SHF_ALLOC + SHF_WRITE)) 1 0 12).isNone =
      true :=
  ⟨rfl, rfl⟩

theorem canary_elf64_reject_global_sym_and_merge_section :
    -- Non-local symbol (`STB_GLOBAL = 1`) and `SHF_MERGE` + `STT_SECTION`
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (symInfo := 17)) 1 0 12).isNone = true ∧
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (roFlags := SHF_ALLOC + SHF_MERGE) (roEntsize := 16)
        (symInfo := STT_SECTION)) 1 0 12).isNone = true :=
  ⟨rfl, rfl⟩

theorem canary_elf64_reject_merge_escape_and_abs64_overlap :
    -- `SHF_MERGE` cross-entry escape (`entsize = 8`, 16B load) rejected
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (roFlags := SHF_ALLOC + SHF_MERGE) (roEntsize := 8))
      1 0 12).isNone = true ∧
    -- Preceding 8B `R_AARCH64_ABS64` (257) at offset 4 overlaps `[8, 12)`
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (rela0Off := 4) (rela0Type := 257)
        (rela1Off := 0) (rela1Type := 257)
        (textBytes := canaryLitPoolBeforeRetText))
      1 8 4).isNone = true :=
  ⟨rfl, rfl⟩

theorem canary_elf64_reject_adrp_lo12_mismatch :
    -- Mismatched `ADRP` (`addend = 8`) vs `LO12` (`addend = 0`) rejected
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (rela0Add := 8) (rela1Add := 0)) 1 0 12).isNone = true ∧
    -- Mismatched `ADRP` register (`x1`) vs `LO12` base (`x0`) rejected
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (textBytes := canaryWrongAdrpRegText)) 1 0 12).isNone =
      true :=
  ⟨rfl, rfl⟩

theorem canary_elf64_reject_misaligned_or_oob_reloc :
    -- Misaligned `funcOff = 2` or out-of-section `rOffset = 12` rejected
    resolveAArch64RodataReloc
      (mkCanaryElfObj (rela1Off := 2)) 1 2
      { rOffset := 2, rSym := 1, rType := R_AARCH64_LDST128_ABS_LO12_NC,
        rAddend := Int.ofNat 0 } = none ∧
    resolveAArch64RodataReloc
      (mkCanaryElfObj (rela1Off := 12)) 1 0
      { rOffset := 12, rSym := 1, rType := R_AARCH64_LDST128_ABS_LO12_NC,
        rAddend := Int.ofNat 0 } = none :=
  ⟨rfl, rfl⟩

theorem canary_elf64_reject_fabricated_reloc_and_bad_slice :
    -- Fabricated `Elf64Rela` not present in `.rela.text` rejected
    resolveAArch64RodataReloc canaryValidElfObj 1 0
      { rOffset := 8, rSym := 1, rType := R_AARCH64_LDST128_ABS_LO12_NC,
        rAddend := Int.ofNat 0 } = none ∧
    -- Non-executable section index (`2` = `.rodata`) rejected
    (decodeFuncFromElf? canaryRelocCfg canaryValidElfObj 2 0 12).isNone =
      true ∧
    -- Unaligned `funcOff = 2` or out-of-bounds `funcSize = 16` rejected
    (decodeFuncFromElf? canaryRelocCfg canaryValidElfObj 1 2 8).isNone =
      true ∧
    (decodeFuncFromElf? canaryRelocCfg canaryValidElfObj 1 0 16).isNone =
      true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Complete ELF64 object adding an `SHT_RELA` section (`sh7`, reusing the
`.rela.text` name string, targeting `sh_info = 2` `.rodata`) with
`R_AARCH64_ABS64` (257) mutating `.rodata[0..8)` at link time. -/
@[expose] def canaryRodataRelaElfObj : List UInt8 :=
  let hdr := mkElf64Ehdr EM_AARCH64 268 8 6
  let sym1 := mkElf64Sym 1 1 2 0 16
  let rela0 := mkElf64Rela 0 1 R_AARCH64_ADR_PREL_PG_HI21 0
  let rela1 := mkElf64Rela 4 1 R_AARCH64_LDST128_ABS_LO12_NC 0
  let relaRo := mkElf64Rela 0 1 257 0 -- R_AARCH64_ABS64 mutating .rodata[0..8)
  let sh1 := mkElf64Shdr 1 SHT_PROGBITS (SHF_ALLOC + SHF_EXECINSTR) 64 12 0 0 0
  let sh2 := mkElf64Shdr 7 SHT_PROGBITS SHF_ALLOC 76 16 0 0 0 16
  let sh7 := mkElf64Shdr 31 SHT_RELA 0 244 24 3 2 24 -- targets sec 2 (.rodata)
  hdr ++ (canaryElfText ++ (canaryElfRodata ++ (canarySym0 ++ (sym1 ++
    (canaryStrtab ++ (rela0 ++ (rela1 ++ (canaryShstrtab ++ (relaRo ++
    (canarySh0 ++ (sh1 ++ (sh2 ++ (canaryStaticShTail ++ sh7)))))))))))))

theorem canary_elf64_reject_relocated_rodata :
    -- Object passes header/hygiene, yet `.rodata` target is rejected
    objectHasNoForbiddenElfFeatures canaryRodataRelaElfObj = true ∧
    (decodeFuncFromElf? canaryRelocCfg canaryRodataRelaElfObj 1 0 12).isNone =
      true ∧
    resolveAArch64RodataReloc canaryRodataRelaElfObj 1 0
      { rOffset := 4, rSym := 1, rType := R_AARCH64_LDST128_ABS_LO12_NC,
        rAddend := Int.ofNat 0 } = none :=
  ⟨rfl, rfl, rfl⟩

theorem canary_elf64_extract_relocs_validates_slice :
    -- Positive control on valid executable slice
    (extractFuncRodataRelocs? canaryValidElfObj 1 0 12).isSome = true ∧
    -- Rejects `.rodata` (non-exec), invalid section, misaligned, zero, OOB
    extractFuncRodataRelocs? canaryValidElfObj 2 0 12 = none ∧
    extractFuncRodataRelocs? canaryValidElfObj 999 0 12 = none ∧
    extractFuncRodataRelocs? canaryValidElfObj 1 2 8 = none ∧
    extractFuncRodataRelocs? canaryValidElfObj 1 8 2 = none ∧
    extractFuncRodataRelocs? canaryValidElfObj 1 0 0 = none ∧
    extractFuncRodataRelocs? canaryValidElfObj 1 0 16 = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem canary_elf64_reject_stn_undef :
    -- Non-zero `sym[0]` (`STN_UNDEF` violation) rejected by parser
    (parseElf64Object?
      (mkCanaryElfObj (sym0Bytes := mkElf64Sym 1 1 2 0 16))).isNone = true :=
  rfl

theorem canary_elf64_reject_rsym_zero :
    -- Defense-in-depth `r_sym == 0` guard in `resolveParsedRodataReloc?`,
    -- isolated against a synthetic `Elf64Object` with valid `symbols[0]`
    let hdr : Elf64Header :=
      { eType := ET_REL, eMachine := EM_AARCH64, eVersion := EV_CURRENT,
        eShoff := 0, eFlags := 0, eEhsize := 64, eShentsz := 64,
        eShnum := 3, eShstrndx := 0 }
    let roSec : Elf64Section :=
      { idx := 2, shName := 0, name := [], shType := SHT_PROGBITS,
        shFlags := SHF_ALLOC, shAddr := 0, shOffset := 0, shSize := 16,
        shLink := 0, shInfo := 0, shAddral := 16, shEntsize := 0 }
    let nullSec : Elf64Section :=
      { idx := 0, shName := 0, name := [], shType := SHT_NULL,
        shFlags := 0, shAddr := 0, shOffset := 0, shSize := 0,
        shLink := 0, shInfo := 0, shAddral := 0, shEntsize := 0 }
    let sym0 : Elf64Symbol :=
      { idx := 0, stName := 1, name := [], stInfo := STT_OBJECT,
        stOther := 0, stShndx := 2, stValue := 0, stSize := 16 }
    let obj : Elf64Object :=
      { header := hdr, sections := [nullSec, nullSec, roSec],
        symtabIdx := some 1, symbols := [sym0], relaSections := [] }
    resolveParsedRodataReloc? obj 0
      { rOffset := 4, rSym := 0, rType := R_AARCH64_LDST128_ABS_LO12_NC,
        rAddend := Int.ofNat 0 } = none :=
  rfl

theorem canary_elf64_reject_shf_tls :
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (roFlags := SHF_ALLOC + SHF_TLS)) 1 0 12).isNone =
      true :=
  rfl

theorem canary_elf64_reject_stt_tls :
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (symInfo := STT_TLS)) 1 0 12).isNone = true :=
  rfl

theorem canary_elf64_reject_shf_compressed :
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (roFlags := SHF_ALLOC + SHF_COMPRESSED))
      1 0 12).isNone = true :=
  rfl

theorem canary_elf64_reject_shf_exclude_text :
    (funcTextBytes?
      (mkCanaryElfObj (textFlags := SHF_ALLOC + SHF_EXECINSTR + SHF_EXCLUDE))
      1 0 12).isNone = true :=
  rfl

theorem canary_elf64_reject_merge_partial_entry :
    -- Isolates `shSize % shEntsize == 0` (`24 % 16 != 0`) with `sym1Val = 0`
    resolveAArch64RodataReloc
      (mkCanaryElfObj (roFlags := SHF_ALLOC + SHF_MERGE) (roEntsize := 16)
        (roSize := 24) (sym1Val := 0)
        (rela1Type := R_AARCH64_LDST64_ABS_LO12_NC))
      1 0
      { rOffset := 4, rSym := 1, rType := R_AARCH64_LDST64_ABS_LO12_NC,
        rAddend := Int.ofNat 0 } = none :=
  rfl

theorem canary_elf64_reject_merge_misaligned_entsize :
    -- Isolates `shEntsize % accBytes == 0` (`24 % 16 != 0`) for `LDST128`
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (roFlags := SHF_ALLOC + SHF_MERGE) (roEntsize := 24)
        (roSize := 24))
      1 0 12).isNone = true :=
  rfl

theorem canary_elf64_reject_misaligned_effoff :
    -- Misaligned `effOff = 4` on `R_AARCH64_LDST128_ABS_LO12_NC` (`roSize=20`)
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (roSize := 20) (rela0Add := 4) (rela1Add := 4))
      1 0 12).isNone = true :=
  rfl

theorem canary_elf64_reject_insufficient_rodata_align :
    -- Insufficient `.rodata` `sh_addralign = 4` for `LDST128` (`16` required)
    (decodeFuncFromElf? canaryRelocCfg
      (mkCanaryElfObj (roAlign := 4)) 1 0 12).isNone = true :=
  rfl

theorem canary_elf64_reject_compressed_shstrtab :
    -- Byte 9 = `8` sets `sh_flags = 0x0800 = SHF_COMPRESSED` on `.shstrtab`
    (parseElf64Object?
      (mkCanaryElfObj (shTail := mkCanaryShTail (shstrFHi := 8)))).isNone =
      true :=
  rfl

theorem canary_elf64_reject_compressed_rela :
    -- Byte 9 = `8` sets `sh_flags = 0x0800 = SHF_COMPRESSED` on `.rela.text`
    (parseElf64Object?
      (mkCanaryElfObj (shTail := mkCanaryShTail (relaFHi := 8)))).isNone =
      true :=
  rfl

theorem canary_elf64_reject_compressed_symtab :
    -- Byte 9 = `8` sets `sh_flags = 0x0800 = SHF_COMPRESSED` on `.symtab`
    (parseElf64Object?
      (mkCanaryElfObj (shTail := mkCanaryShTail (symFHi := 8)))).isNone =
      true :=
  rfl

theorem canary_elf64_reject_compressed_strtab :
    -- Byte 9 = `8` sets `sh_flags = 0x0800 = SHF_COMPRESSED` on `.strtab`
    (parseElf64Object?
      (mkCanaryElfObj (shTail := mkCanaryShTail (strFHi := 8)))).isNone =
      true :=
  rfl

theorem canary_elf64_reject_duplicate_rodata_reloc :
    -- Duplicate `LDST128` relocation at `rOffset = 4` rejected
    resolveAArch64RodataReloc
      (mkCanaryElfObj (rela0Off := 4)
        (rela0Type := R_AARCH64_LDST128_ABS_LO12_NC))
      1 0
      { rOffset := 4, rSym := 1, rType := R_AARCH64_LDST128_ABS_LO12_NC,
        rAddend := Int.ofNat 0 } = none :=
  rfl

theorem canary_elf64_reject_overlapping_abs64_reloc :
    -- Sibling 8-byte `R_AARCH64_ABS64` (257) at `rOffset = 0` overlaps `[4, 8)`
    resolveAArch64RodataReloc
      (mkCanaryElfObj (rela0Off := 0) (rela0Type := 257))
      1 0
      { rOffset := 4, rSym := 1, rType := R_AARCH64_LDST128_ABS_LO12_NC,
        rAddend := Int.ofNat 0 } = none :=
  rfl

theorem canary_elf64_reject_decode_without_pcrel_reloc_req :
    -- `ET_REL` ELF decoding requires `cfg.requireRelocForPcRel = true`
    (decodeFuncFromElf? canaryNoRelocCfg canaryValidElfObj 1 0 12).isNone =
      true :=
  rfl

theorem canary_adrp_lo12_rejects_bl_target_and_indirect_branch :
    let rHi : AArch64Reloc :=
      { offset := 0, kind := .adrPrelPgHi21, secIdx := 2,
        target := Int.ofNat 0 }
    let rLo : AArch64Reloc :=
      { offset := 4, kind := .ldst128AbsLo12Nc, secIdx := 2,
        target := Int.ofNat 0 }
    let iAdrp := DecodedInsn.pcRelAddr true (.gpr .x0) (Int.ofNat 0) (some rHi)
    let iLdr := DecodedInsn.simdLoadStore true 16 .v0 (.gpr .x0)
      (.unsignedOff 0) (some rLo)
    -- `BL` writes link register `x30` in `adrpKillGprs`; `B` does not
    adrpKillGprs (.branch true (Int.ofNat 0)) = [.x30] ∧
    adrpKillGprs (.branch false (Int.ofNat 0)) = [] ∧
    -- `bl #-8` at PC 12 targets LO12 instruction at PC 4 -> rejected
    adrpLo12PairingOk
      [(0, iAdrp), (4, iLdr), (8, .ret (.gpr .x30)),
       (12, .branch true (Int.negSucc 7))] = false ∧
    -- Indirect `br x16`, `blr x16`, non-`x30` `ret x16`, or `x30` write
    adrpLo12PairingOk
      [(0, iAdrp), (4, iLdr), (8, .branchReg false (.gpr .x16)),
       (12, .ret (.gpr .x30))] = false ∧
    adrpLo12PairingOk
      [(0, iAdrp), (4, iLdr), (8, .branchReg true (.gpr .x16)),
       (12, .ret (.gpr .x30))] = false ∧
    adrpLo12PairingOk
      [(0, iAdrp), (4, iLdr), (8, .ret (.gpr .x16)),
       (12, .ret (.gpr .x30))] = false ∧
    adrpLo12PairingOk
      [(0, .pcRelAddr false (.gpr .x30) (Int.ofNat 12) none),
       (4, .ret (.gpr .x30)), (8, iAdrp), (12, iLdr),
       (16, .ret (.gpr .x30))] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 7. Stride & Plane-Copy Dispatch Guard Canaries -/

@[expose] def canaryMaxPtrdiff : Nat := 9223372036854775807 -- 2^63 - 1

theorem canary_stride_and_plane_copy_guards :
    -- Positive 16-byte chunk tail stride guard (`w = 18 -> w1 = 32 <= 32`)
    checkVecTailStrideGuard 18 16 32 32 2147483647 = true ∧
    -- Negative tight stride (`w = 2 -> w1 = 16 > 2`, 14B overrun prevented)
    checkVecTailStrideGuard 2 16 2 2 2147483647 = false ∧
    -- Positive 64B-chunk, 16B-aligned plane-copy dispatch
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1000) (Int.ofNat 0x2000) (Int.ofNat 64) (Int.ofNat 64)
      (Int.ofNat 64) (Int.ofNat 4) 64 16 canaryMaxPtrdiff = true ∧
    -- Negative 1: unaligned `src` (`+1`)
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1001) (Int.ofNat 0x2000) (Int.ofNat 64) (Int.ofNat 64)
      (Int.ofNat 64) (Int.ofNat 1) 64 16 canaryMaxPtrdiff = false ∧
    -- Negative 2: unaligned `dst` (`+1`)
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1000) (Int.ofNat 0x2001) (Int.ofNat 64) (Int.ofNat 64)
      (Int.ofNat 64) (Int.ofNat 1) 64 16 canaryMaxPtrdiff = false ∧
    -- Negative 3: `bytewidth` overflows `PTRDIFF_MAX - 63`
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1000) (Int.ofNat 0x2000) (Int.ofNat 64) (Int.ofNat 64)
      (Int.ofNat (canaryMaxPtrdiff - 30)) (Int.ofNat 1)
      64 16 canaryMaxPtrdiff = false ∧
    -- Negative 4: zero `bytewidth`
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1000) (Int.ofNat 0x2000) (Int.ofNat 64) (Int.ofNat 64)
      (Int.ofNat 0) (Int.ofNat 1) 64 16 canaryMaxPtrdiff = false ∧
    -- Negative 5: zero `height`
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1000) (Int.ofNat 0x2000) (Int.ofNat 64) (Int.ofNat 64)
      (Int.ofNat 64) (Int.ofNat 0) 64 16 canaryMaxPtrdiff = false ∧
    -- Negative 6: negative `height`
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1000) (Int.ofNat 0x2000) (Int.ofNat 64) (Int.ofNat 64)
      (Int.ofNat 64) (Int.negSucc 0) 64 16 canaryMaxPtrdiff = false ∧
    -- Negative 7: unaligned `dstLinesize` (`72 % 16 = 8 != 0`)
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1000) (Int.ofNat 0x2000) (Int.ofNat 72) (Int.ofNat 64)
      (Int.ofNat 64) (Int.ofNat 2) 64 16 canaryMaxPtrdiff = false ∧
    -- Negative 8: unaligned `srcLinesize` (`72 % 16 = 8 != 0`)
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1000) (Int.ofNat 0x2000) (Int.ofNat 64) (Int.ofNat 72)
      (Int.ofNat 64) (Int.ofNat 2) 64 16 canaryMaxPtrdiff = false ∧
    -- Negative 9: `dstLinesize` smaller than aligned 64B chunk (`32 < 64`)
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1000) (Int.ofNat 0x2000) (Int.ofNat 32) (Int.ofNat 64)
      (Int.ofNat 64) (Int.ofNat 2) 64 16 canaryMaxPtrdiff = false ∧
    -- Negative 10: `srcLinesize` smaller than aligned 64B chunk (`32 < 64`)
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1000) (Int.ofNat 0x2000) (Int.ofNat 64) (Int.ofNat 32)
      (Int.ofNat 64) (Int.ofNat 2) 64 16 canaryMaxPtrdiff = false ∧
    -- Negative 11: `chunkBytes` not a multiple of `alignBytes` (`24 % 16 = 8`)
    checkPlaneCopyDispatchGuard
      (Int.ofNat 0x1000) (Int.ofNat 0x2000) (Int.ofNat 48) (Int.ofNat 48)
      (Int.ofNat 48) (Int.ofNat 2) 24 16 canaryMaxPtrdiff = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.ElfAArch64.Canaries
