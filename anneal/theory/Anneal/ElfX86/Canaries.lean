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
public import Anneal.ElfX86

public section
namespace Anneal.ElfX86.Canaries

open Anneal.ElfX86

/-!
# Kernel-Checked Canaries & Fail-Closed Regression Suite
(`Anneal.ElfX86.Canaries`)

Exercises `Anneal.ElfX86.{PrefixDecode, RelocAndElf, DeadFlagAndSfi}` end to
end with zero axioms (`[]`):

1. Real AVX2 + `R_X86_64_PC32` `.rodata` + `vzeroupper` + `ret` kernel stream
   with 1-to-1 relocation consumption and `StraightLineLeafAbiFixedBasesCert`.
2. Architectural decode-fault exclusions: `>15`-byte `#GP(0)`, `0x66`/REX+VEX
   `#UD` (including sticky `seenRex` across intermediate legacy prefixes
   `48 2E C5 F8 77 C3` and `48 F3 0F 1E FA`), illegal `LOCK` `#UD` and
   conservative rejection of combined `LOCK`+`F2`/`F3` HLE hints
   (`F3 F0 01 07`), `41 90`/`49 90` `xchgAx` vs. `nop`/`F3 90`, `bmi1`-gated
   `F3 0F BC` `tzcnt` vs. `bsf`, `67 48 8B 05 78 56 34 12` `addr32`
   EIP-relative `[eip+disp32]`, `F3 0F 1E FA` `endbr64`, and `66 C3`/`66 EB`/
   `66 E8`/`66 E9`/`66 FF` rejection.
3. Repaired prefix semantics: `0x64`/`0x65` (`FS:`/`GS:`) preservation across
   null segment prefixes, and `d64` `REX.W` precedence (`66 48 50` vs.
   `48 66 50`).
4. Stream & SFI fail-closed regressions: trailing bare prefixes, unconsumed
   extra relocations, missing `vzeroupper`, callee-saved `rbx` clobber,
   `rbp` frame-pointer store (`48 89 45 08`), fixed-base clobber & indexed
   store rejection, `.ripRel` store, `FS:` escape, and traps/syscalls/branches.
5. Complete raw-byte ELF64 `ET_REL` object parsing (`parseElf64Header?`,
   `parseElf64Object?`, `objectHasNoForbiddenElfFeatures`,
   `resolvePc32RodataReloc`, `extractFuncPcRelRelocs?`, `funcTextBytes?`,
   `decodeFuncFromElf?`): header identity rejections (`EI_VERSION`, `e_version`,
   `e_ehsize`, `e_shentsize`, `EI_PAD`), all-zero `SHT_NULL` at section `0`,
   `STN_UNDEF`/`SHN_UNDEF`/`SHN_LORESERVE` rejections, `textSecIdx`
   executable-section (`!SHF_GROUP`, `!SHF_COMPRESSED`) and
   `funcOff + funcSize ≤ shSize` checks, `.rodata` flag exclusions
   (`!SHF_COMPRESSED`, `!SHF_TLS`, `!SHF_STRINGS`), per-operand `.rodata`
   bounds and `SHF_MERGE` enforcement in `decodeFuncFromElf?`, duplicate-RELA
   rejection on a real executable `.text` section, `.shstrtab` & forbidden
   section rejections, `SHF_MERGE` same-entry positive control vs. cross-entry
   and `STT_SECTION` rejections, `STB_LOCAL`, `SHF_GROUP`, writable `.data`,
   `IFUNC`, `IRELATIVE`, and `R_X86_64_32S`.
6. Backward `DeadFlagCollapse` including exact Intel SDM shift-count masking,
   `add; call; adc` / `add; syscall; adc` clobber rejection, and a non-trivial
   flag-reading `TraceStepReadsAgree` witness.
-/

/-! ## 1. Positive AVX2 + `R_X86_64_PC32` `.rodata` + `vzeroupper` + `ret` -/

/-- Minimal real AVX2 sequence extracted from H.264 10-bit IDCT kernels:
`movsxd rdx, edx; vbroadcasti128 ymm0, [rsi]`,
`vpaddd ymm0, ymm0, [rip+0]; vzeroupper; ret`. -/
@[expose] def canaryAvx2Text : List UInt8 :=
  [ 0x48, 0x63, 0xD2,
    0xC4, 0xE2, 0x7D, 0x5A, 0x06,
    0xC5, 0xFD, 0xFE, 0x05, 0x00, 0x00, 0x00, 0x00,
    0xC5, 0xF8, 0x77,
    0xC3 ]

/-- Matching `R_X86_64_PC32` relocation at offset `12` (`disp32` of `vpaddd`)
targeting `.rodata` section `0` with `symValue + addend = -4`. -/
@[expose] def canaryAvx2Relocs : List PcRelReloc :=
  [ { offset := 12, secIdx := 0, target := Int.negSucc 3 } ]

@[expose] def canaryRelocCfg : DecodeConfig :=
  { requireRelocForRip := true, bmi1 := false }

@[expose] def canaryBmi1Cfg : DecodeConfig :=
  { requireRelocForRip := true, bmi1 := true }

@[expose] def canaryNoRelocCfg : DecodeConfig :=
  { requireRelocForRip := false, bmi1 := false }

@[expose] def canaryDecodedAvx2 : List DecodedInsn :=
  match decodeStream canaryRelocCfg canaryAvx2Relocs canaryAvx2Text with
  | some tr => tr.map (fun e => e.2.2)
  | none => []

theorem canary_avx2_local_coverage :
    localDecodeCoverageOk canaryRelocCfg canaryAvx2Relocs canaryAvx2Text =
      true := rfl

theorem canary_avx2_dirty_ymm_cleared :
    dirtyYmmClearedBeforeRet canaryDecodedAvx2 = true := rfl

theorem canary_avx2_abi_sfi_ok :
    checkStraightLineAbiSfiFixedBases [.rdi, .rsi] canaryDecodedAvx2 =
      true := rfl

theorem canary_avx2_abi_sfi_cert :
    StraightLineLeafAbiFixedBasesCert [.rdi, .rsi] canaryDecodedAvx2 :=
  checkStraightLineAbiSfiFixedBases_sound [.rdi, .rsi] canaryDecodedAvx2
    canary_avx2_abi_sfi_ok

theorem canary_avx2_missing_reloc_rejected :
    localDecodeCoverageOk canaryRelocCfg [] canaryAvx2Text = false := rfl

/-- Unconsumed extra relocation in `relocs` is rejected by 1-to-1 relocation
accounting in `localDecodeCoverageOk`. -/
theorem canary_avx2_unconsumed_extra_reloc_rejected :
    localDecodeCoverageOk canaryRelocCfg
      [ { offset := 12, secIdx := 0, target := Int.negSucc 3 },
        { offset := 0, secIdx := 0, target := Int.ofNat 0 } ]
      canaryAvx2Text = false := rfl

/-- Un-relocated base-less SIB `[disp32]` (`48 8B 04 25 00 00 00 00`) is
rejected in relocatable object mode. -/
theorem canary_baseless_sib_rejected_in_reloc_mode :
    decodeOne canaryRelocCfg [] 0
      [0x48, 0x8B, 0x04, 0x25, 0x00, 0x00, 0x00, 0x00] = none := rfl

/-! ## 2. Prefix/Opcode Errata: `#GP(0)`, VEX/REX `#UD`, `LOCK`/`REP`,
`addr32`, `xchg`, `bmi1` `tzcnt`, `endbr64`, `66 C3/EB/E8/E9/FF` -/

@[expose] def overlong16Bytes : List UInt8 :=
  [ 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x90 ]

@[expose] def exact15Bytes : List UInt8 :=
  [ 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x90 ]

theorem canary_overlong16_gp0_rejected :
    decodeOne canaryRelocCfg [] 0 overlong16Bytes = none := rfl

theorem canary_exact15_accepted :
    decodeOne canaryRelocCfg [] 0 exact15Bytes = some (.nop, 15) := rfl

/-- Legacy `0x66` or any REX byte anywhere in the prefix run (including
`seenRex` separated by `0x2E`/`0xF3`) before VEX or `endbr64` is rejected. -/
theorem canary_legacy_and_sticky_rex_vex_endbr_rejected :
    decodeOne canaryRelocCfg [] 0 [0x66, 0xC5, 0xF8, 0x77] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x66, 0xC4, 0xE2, 0x7D, 0x5A, 0x06] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x48, 0xC5, 0xF8, 0x77] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x48, 0x2E, 0xC5, 0xF8, 0x77, 0xC3] = none ∧
    localDecodeCoverageOk canaryRelocCfg []
      [0x48, 0x2E, 0xC5, 0xF8, 0x77, 0xC3] = false ∧
    decodeOne canaryRelocCfg [] 0
      [0x48, 0x2E, 0xC4, 0xE2, 0x7D, 0x5A, 0x06] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x48, 0xF3, 0x0F, 0x1E, 0xFA] = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `LOCK` legality and conservative rejection of combined `LOCK`+`F2`/`F3`
HLE (`XACQUIRE`/`XRELEASE`) prefix hints (unmodeled in this AST). -/
theorem canary_lock_legality_and_hle_policy :
    decodeOne canaryRelocCfg [] 0 [0xF0, 0x90] = none ∧
    decodeOne canaryRelocCfg [] 0 [0xF0, 0x01, 0xC0] = none ∧
    decodeOne canaryRelocCfg [] 0 [0xF3, 0xF0, 0x01, 0x07] = none ∧
    decodeOne canaryRelocCfg [] 0 [0xF0, 0xF3, 0x01, 0x07] = none ∧
    decodeOne canaryRelocCfg [] 0 [0xF2, 0xF0, 0x83, 0x07, 0x01] = none ∧
    decodeOne canaryRelocCfg [] 0 [0xF0, 0x01, 0x07] =
      some (.aluRmReg .s32 true .add
        (.mem (.gpr none false (some .rdi) none 0)) .rax, 3) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- In 64-bit mode, `0x67` + `mod=00, r/m=101` (`67 48 8B 05 ...`,
`67 48 8D 05 ...`) is EIP-relative `[eip+disp32]`, decoded as `.ripRel` with
`addr32 = true` under `requireRelocForRip = false` and rejected fail-closed in
relocatable mode (even with a relocation), `insnHasAddr32`, and both SFI tiers.
-/
theorem canary_addr32_mod0_rm5_eip_relative :
    let movInsn : DecodedInsn :=
      .movRegRm .s64 .rax
        (.mem (.ripRel none true none none (Int.ofNat 0x12345678)))
    let leaInsn : DecodedInsn :=
      .lea .s64 .rax (.ripRel none true none none (Int.ofNat 0x10))
    decodeOne canaryRelocCfg [] 0
      [0x67, 0x48, 0x8B, 0x05, 0x78, 0x56, 0x34, 0x12] = none ∧
    decodeOne canaryRelocCfg
      [ { offset := 4, secIdx := 2, target := Int.negSucc 3 } ] 0
      [0x67, 0x48, 0x8B, 0x05, 0x00, 0x00, 0x00, 0x00] = none ∧
    decodeOne canaryNoRelocCfg [] 0
      [0x67, 0x48, 0x8B, 0x05, 0x78, 0x56, 0x34, 0x12] =
      some (movInsn, 8) ∧
    decodeOne canaryNoRelocCfg [] 0
      [0x67, 0x48, 0x8D, 0x05, 0x10, 0x00, 0x00, 0x00] =
      some (leaInsn, 8) ∧
    insnHasAddr32 movInsn = true ∧
    insnHasAddr32 leaInsn = true ∧
    checkStraightLineAbiSfiArgStores [movInsn, .ret] = false ∧
    checkStraightLineAbiSfiStoreBaseNamesOnly [.rdi, .rsi] [leaInsn, .ret] =
      false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `41 90` (`xchg r8d, eax`), `49 90` (`xchg r8, rax`), and `F3 90`
(`pause` rejected) vs. plain `90` (`nop`). -/
theorem canary_xchg_r8_and_pause :
    decodeOne canaryRelocCfg [] 0 [0x41, 0x90] =
      some (.xchgAx .s32 .r8, 2) ∧
    decodeOne canaryRelocCfg [] 0 [0x49, 0x90] =
      some (.xchgAx .s64 .r8, 2) ∧
    decodeOne canaryRelocCfg [] 0 [0xF3, 0x90] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x90] = some (.nop, 1) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `F3 0F BC C1` (`tzcnt eax, ecx`) requires `cfg.bmi1 = true` (fails closed
when `bmi1 = false`), while `0F BC C1` (`bsf`) works regardless and
`F2 0F BC C1` is rejected. -/
theorem canary_tzcnt_bmi1_gated_vs_bsf :
    decodeOne canaryRelocCfg [] 0 [0xF3, 0x0F, 0xBC, 0xC1] = none ∧
    decodeOne canaryBmi1Cfg [] 0 [0xF3, 0x0F, 0xBC, 0xC1] =
      some (.tzcnt .s32 .rax (.reg .rcx), 4) ∧
    decodeOne canaryRelocCfg [] 0 [0x0F, 0xBC, 0xC1] =
      some (.bsf .s32 .rax (.reg .rcx), 3) ∧
    decodeOne canaryBmi1Cfg [] 0 [0xF2, 0x0F, 0xBC, 0xC1] = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- CET `F3 0F 1E FA` (`endbr64`) decodes cleanly and passes leaf SFI. -/
theorem canary_endbr64_accepted :
    decodeOne canaryRelocCfg [] 0 [0xF3, 0x0F, 0x1E, 0xFA] =
      some (.endbr64, 4) ∧
    checkStraightLineAbiSfiArgStores [.endbr64, .ret] = true :=
  ⟨rfl, rfl⟩

/-- Group-1 `F2`/`F3` prefix conflicts and non-canonical prefixes on mandatory
`F3` instructions (`tzcnt` and `endbr64`) are rejected fail-closed. -/
theorem canary_f2_f3_conflict_and_canonical_mandatory_prefix_rejected :
    decodeOne canaryBmi1Cfg [] 0 [0xF2, 0xF3, 0x0F, 0xBC, 0xC1] = none ∧
    decodeOne canaryBmi1Cfg [] 0 [0xF3, 0xF2, 0x0F, 0xBC, 0xC1] = none ∧
    decodeOne canaryBmi1Cfg [] 0 [0xF3, 0xF3, 0x0F, 0xBC, 0xC1] = none ∧
    decodeOne canaryBmi1Cfg [] 0 [0x64, 0xF3, 0x0F, 0xBC, 0xC1] = none ∧
    decodeOne canaryBmi1Cfg [] 0 [0x67, 0xF3, 0x0F, 0xBC, 0xC1] = none ∧
    decodeOne canaryBmi1Cfg [] 0 [0x66, 0xF3, 0x0F, 0xBC, 0xC1] = none ∧
    decodeOne canaryBmi1Cfg [] 0 [0x48, 0xF3, 0x0F, 0xBC, 0xC1] = none ∧
    decodeOne canaryBmi1Cfg [] 0 [0xF3, 0x48, 0x0F, 0xBC, 0xC1] = none ∧
    decodeOne canaryRelocCfg [] 0 [0xF2, 0xF3, 0x0F, 0x1E, 0xFA] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x64, 0xF3, 0x0F, 0x1E, 0xFA] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x67, 0xF3, 0x0F, 0x1E, 0xFA] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x2E, 0xF3, 0x0F, 0x1E, 0xFA] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x66, 0xF3, 0x0F, 0x1E, 0xFA] = none ∧
    decodeOne canaryRelocCfg [] 0 [0xF3, 0xF3, 0x0F, 0x1E, 0xFA] = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Non-mandatory `F2`/`F3` prefixes on 1-byte opcodes and silently-ignored
`FS:`/`0x67` prefixes on non-memory ops are rejected, while standard 10-byte
`CS:`-prefixed multi-byte NOP (`66 2E 0F 1F 84 00 00 00 00 00`) decodes. -/
theorem canary_non_mandatory_rep_and_ignored_seg_a32_rejected :
    decodeOne canaryRelocCfg [] 0 [0xF2, 0xC3] = none ∧
    decodeOne canaryRelocCfg [] 0 [0xF3, 0xC3] = none ∧
    decodeOne canaryRelocCfg [] 0 [0xF2, 0xE8, 0x00, 0x00, 0x00, 0x00] = none ∧
    decodeOne canaryRelocCfg [] 0 [0xF3, 0x8B, 0x00] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x64, 0xC3] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x67, 0xC3] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x64, 0x90] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x67, 0x90] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x64, 0xC5, 0xF8, 0x77] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x67, 0xC5, 0xF8, 0x77] = none ∧
    decodeOne canaryRelocCfg [] 0
      [0x66, 0x2E, 0x0F, 0x1F, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] =
      some (.nop, 10) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `0x66` on `ret` (`66 C3`, `48 66 C3`, `66 48 C3`) and 16-bit IP-truncating
control transfers (`66 EB`, `66 E8`, `66 E9`, `66 FF /2`, `66 FF /4`) are all
rejected fail-closed. -/
theorem canary_66_ret_and_control_ops_rejected :
    decodeOne canaryRelocCfg [] 0 [0x66, 0xC3] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x48, 0x66, 0xC3] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x66, 0x48, 0xC3] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x66, 0xEB, 0x00] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x66, 0xE8, 0x00, 0x00, 0x00, 0x00] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x66, 0xE9, 0x00, 0x00, 0x00, 0x00] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x66, 0xFF, 0xD0] = none ∧
    decodeOne canaryRelocCfg [] 0 [0x66, 0xFF, 0xE0] = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. `FS:`/`GS:` vs. Null Prefix & `d64` `REX.W` Precedence -/

theorem canary_fs_gs_and_d64_precedence :
    decodeOne canaryRelocCfg [] 0 [0x64, 0x26, 0x48, 0x8B, 0x00] =
      some (.movRegRm .s64 .rax
        (.mem (.gpr (some .fs) false (some .rax) none 0)), 5) ∧
    decodeOne canaryRelocCfg [] 0 [0x64, 0x65, 0x2E, 0x48, 0x8B, 0x00] =
      some (.movRegRm .s64 .rax
        (.mem (.gpr (some .gs) false (some .rax) none 0)), 6) ∧
    decodeOne canaryRelocCfg [] 0 [0x66, 0x48, 0x50] =
      some (.pushReg .s64 .rax, 3) ∧
    decodeOne canaryRelocCfg [] 0 [0x48, 0x66, 0x50] =
      some (.pushReg .s16 .rax, 3) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## 4. Trailing Bare Prefix, Missing `vzeroupper`, `rbp` Frame, & Store
Confinement Rejections -/

theorem canary_trailing_bare_prefixes_rejected :
    localDecodeCoverageOk canaryRelocCfg [] [0xC3, 0x66] = false ∧
    localDecodeCoverageOk canaryRelocCfg [] [0xC3, 0x41] = false ∧
    localDecodeCoverageOk canaryRelocCfg [] [0xC3, 0xF0] = false ∧
    localDecodeCoverageOk canaryRelocCfg [] [0xC3, 0x64] = false :=
  ⟨rfl, rfl, rfl, rfl⟩

@[expose] def missingVzeroupperStream : List DecodedInsn :=
  [ .vbin .paddd true 0 0 (.reg 1), .ret ]

theorem canary_missing_vzeroupper_rejected :
    dirtyYmmClearedBeforeRet missingVzeroupperStream = false ∧
    checkStraightLineAbiSfiArgStores missingVzeroupperStream = false ∧
    checkStraightLineAbiSfiStoreBaseNamesOnly [.rdi, .rsi]
      missingVzeroupperStream = false :=
  ⟨rfl, rfl, rfl⟩

@[expose] def decodeOnlyInsns (bs : List UInt8) : List DecodedInsn :=
  match decodeStream canaryRelocCfg [] bs with
  | some tr => tr.map (fun e => e.2.2)
  | none => []

/-- `mov rbx, rax; ret` (`48 89 C3 C3`) clobbers callee-saved `rbx`
(non-vacuous: asserts exact decoded length and first instruction). -/
theorem canary_callee_saved_rbx_clobber_rejected :
    let insns := decodeOnlyInsns [0x48, 0x89, 0xC3, 0xC3]
    insns.length = 2 ∧
    listGet? insns 0 = some (.movRmReg .s64 (.reg .rbx) .rax) ∧
    checkStraightLineAbiSfiArgStores insns = false ∧
    checkStraightLineAbiSfiStoreBaseNamesOnly [.rdi, .rsi] insns = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `mov [rbp+8], rax; ret` (`48 89 45 08 C3`) writes caller's frame via `rbp`
(non-vacuous: asserts exact decoded length and first instruction). -/
theorem canary_rbp_frame_store_rejected :
    let insns := decodeOnlyInsns [0x48, 0x89, 0x45, 0x08, 0xC3]
    insns.length = 2 ∧
    listGet? insns 0 =
      some (.movRmReg .s64 (.mem (.gpr none false (some .rbp) none 8)) .rax) ∧
    checkStraightLineAbiSfiFixedBases [.rdi, .rsi, .rbp] insns = false ∧
    checkStraightLineAbiSfiStoreBaseNamesOnly [.rdi, .rsi, .rbp] insns =
      false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Strict fixed-base confinement rejects clobbering an allowed store base
(`48 89 C7; 48 89 07; C3` = `mov rdi, rax; mov [rdi], rax; ret`) and rejects
any indexed store (`48 89 04 17; C3` = `mov [rdi+rdx], rax; ret`), asserting
non-vacuous decode lengths and first instructions. -/
theorem canary_fixed_base_clobber_and_index_rejected :
    let clobInsns := decodeOnlyInsns [0x48, 0x89, 0xC7, 0x48, 0x89, 0x07, 0xC3]
    let idxInsns := decodeOnlyInsns [0x48, 0x89, 0x04, 0x17, 0xC3]
    clobInsns.length = 3 ∧
    listGet? clobInsns 0 = some (.movRmReg .s64 (.reg .rdi) .rax) ∧
    checkStraightLineAbiSfiArgStores clobInsns = false ∧
    idxInsns.length = 2 ∧
    listGet? idxInsns 0 =
      some (.movRmReg .s64
        (.mem (.gpr none false (some .rdi) (some (.rdx, 1)) 0)) .rax) ∧
    checkStraightLineAbiSfiArgStores idxInsns = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Store-base allowlist: `mov [rdx], rax; ret` (`48 89 02 C3`) is rejected
under `[.rdi, .rsi]` and admitted under `[.rdx]`; `.ripRel` store is always
rejected (non-vacuous decode assertions included). -/
theorem canary_store_base_confinement :
    let insns := decodeOnlyInsns [0x48, 0x89, 0x02, 0xC3]
    insns.length = 2 ∧
    listGet? insns 0 =
      some (.movRmReg .s64 (.mem (.gpr none false (some .rdx) none 0)) .rax) ∧
    checkStraightLineAbiSfiArgStores insns = false ∧
    checkStraightLineAbiSfiFixedBases [.rdx] insns = true ∧
    checkStraightLineAbiSfiArgStores
      [ .movRmReg .s64 (.mem (.ripRel none false (some 0) (some 3) 0)) .rax,
        .ret ] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem canary_fs_stack_and_traps_rejected :
    checkStraightLineAbiSfiArgStores
      [ .movRegRm .s64 .rax
          (.mem (.gpr (some .fs) false (some .rax) none 0)),
        .ret ] = false ∧
    checkStraightLineAbiSfiArgStores
      [ .pushReg .s64 .rbp, .popReg .s64 .rbp, .ret ] = false ∧
    checkStraightLineAbiSfiArgStores [.syscall, .ret] = false ∧
    checkStraightLineAbiSfiArgStores [.ud2, .ret] = false ∧
    checkStraightLineAbiSfiArgStores [.jmpInd (.reg .rax), .ret] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 5. Raw-Byte ELF64 Header & Complete Object Relocation Controls -/

@[expose] def u8 (n : Nat) : UInt8 := UInt8.ofNat (Nat.mod n 256)

@[expose] def encU16 (n : Nat) : List UInt8 :=
  [u8 n, u8 (Nat.div n 256)]

@[expose] def encU32 (n : Nat) : List UInt8 :=
  [u8 n, u8 (Nat.div n 256), u8 (Nat.div n 65536), u8 (Nat.div n 16777216)]

@[expose] def encU64 (n : Nat) : List UInt8 :=
  let lo := Nat.mod n 4294967296
  let hi := Nat.div n 4294967296
  [u8 lo, u8 (Nat.div lo 256), u8 (Nat.div lo 65536),
   u8 (Nat.div lo 16777216),
   u8 hi, u8 (Nat.div hi 256), u8 (Nat.div hi 65536),
   u8 (Nat.div hi 16777216)]

@[expose] def encI64 (x : Int) : List UInt8 :=
  match x with
  | Int.ofNat n => encU64 n
  | Int.negSucc k => encU64 (18446744073709551615 - k)

@[expose] def encZero8 : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def encAlign1 : List UInt8 :=
  [1, 0, 0, 0, 0, 0, 0, 0]

@[expose] def encZeroSym : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def encZero32 : List UInt8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- All-zero 64-byte `SHT_NULL` section header (`sections[0]`), chunked as two
32-byte literals to avoid kernel `Nat.div` overhead and stay under 33 items. -/
@[expose] def encNullShdr : List UInt8 :=
  encZero32 ++ encZero32

@[expose] def encShdr (nameOff shTy shFlg shOff shSz shLnk shInf shEnt : Nat) :
    List UInt8 :=
  encU32 nameOff ++ (encU32 shTy ++ (encU64 shFlg ++ (encZero8 ++
  (encU64 shOff ++ (encU64 shSz ++ (encU32 shLnk ++ (encU32 shInf ++
  (encAlign1 ++ encU64 shEnt))))))))

@[expose] def encSym (nameOff stBind stType stShndx stVal stSz : Nat) :
    List UInt8 :=
  encU32 nameOff ++ ([u8 (stBind * 16 + stType), 0] ++ (encU16 stShndx ++
  (encU64 stVal ++ encU64 stSz)))

@[expose] def encRela (rOff rSym rType : Nat) (rAdd : Int) : List UInt8 :=
  encU64 rOff ++ (encU64 (rSym * 4294967296 + rType) ++ encI64 rAdd)

/-- Parameterized synthetic ELF64 `ET_REL` byte-image builder (521B–617B)
keeping kernel replay well under the 2048 MiB Pass-1 cap:
sections `0:SHT_NULL` (all-zero when `nullShdrZero = true`), `1:.strtab`
(`e_shstrndx = 1`), `2:.rodata`, `3:.text` (`SHT_PROGBITS`, `shSize = 20`,
carrying `canaryAvx2Text` when `includeText = true`), `4:.symtab`
(`sym[0] = STN_UNDEF`, `sym[1]` targeting `symShndx`), `5:.rela.text`
(`shLink = 4`, `shInfo = 3`, `r_sym = relaSymIdx`), plus optional
`6:.init_array`. -/
@[expose] def mkSynElf64Ex
    (eiVer eVer ehSz shEntSz : Nat) (eiPad9 : Nat)
    (dataFlags dataSz dataEnt textFlags : Nat)
    (symBind symType symShndx symVal : Nat)
    (relaOff relaSymIdx relaTy : Nat) (relaAdd : Int)
    (nullShdrZero extraInitArray includeText : Bool) : List UInt8 :=
  -- Minimal string table: `[0]` unless `.init_array` needs name offset 1.
  let strtab : List UInt8 :=
    if extraInitArray then
      [0, 46, 105, 110, 105, 116, 95, 97, 114, 114, 97, 121, 0]
    else [0]
  let strOff : Nat := 64
  let strLen : Nat := if extraInitArray then 13 else 1
  let textBytes : List UInt8 := if includeText then canaryAvx2Text else []
  let textFileOff : Nat := if includeText then strOff + strLen else 0
  let textStoredLen : Nat := if includeText then 20 else 0
  let symOff : Nat := strOff + strLen + textStoredLen
  let symBytes : List UInt8 :=
    encZeroSym ++ encSym 0 symBind symType symShndx symVal 16
  let symSz : Nat := 48
  let relaOffFile : Nat := symOff + symSz
  let relaBytes : List UInt8 := encRela relaOff relaSymIdx relaTy relaAdd
  let relaSz : Nat := 24
  let shOff : Nat := relaOffFile + relaSz
  let shNum : Nat := if extraInitArray then 7 else 6
  let hdr : List UInt8 :=
    [0x7F, 0x45, 0x4C, 0x46, 2, 1, u8 eiVer, 0, 0, u8 eiPad9,
     0, 0, 0, 0, 0, 0,
     1, 0, 62, 0] ++
    (encU32 eVer ++
    (encZero8 ++ (encZero8 ++ (encU64 shOff ++
    ([0, 0, 0, 0] ++ (encU16 ehSz ++ ([0, 0, 0, 0] ++
    (encU16 shEntSz ++ (encU16 shNum ++ [1, 0])))))))))
  let sh0 : List UInt8 :=
    if nullShdrZero then encNullShdr
    else encShdr 0 shtProgbits shfAlloc 0 64 0 0 0
  let shdrs : List UInt8 :=
    sh0 ++
    (encShdr 0 shtStrtab 0 strOff strLen 0 0 0 ++
    (encShdr 0 shtProgbits dataFlags 0 dataSz 0 0 dataEnt ++
    (encShdr 0 shtProgbits textFlags textFileOff 20 0 0 0 ++
    (encShdr 0 shtSymtab 0 symOff symSz 1 2 24 ++
    (encShdr 0 shtRela 0 relaOffFile relaSz 4 3 24 ++
    (if extraInitArray then
      encShdr 1 shtInitArray (shfWrite + shfAlloc) 0 8 0 0 8
     else []))))))
  hdr ++ (strtab ++ (textBytes ++ (symBytes ++ (relaBytes ++ shdrs))))

/-- Compact synthetic ELF64 `ET_REL` builder with all-zero `SHT_NULL` at `0`,
executable `.text` at `3`, `.rodata` at `2`, and `r_sym = 1` (without embedding
`.text` payload bytes for pure relocation/header tests). -/
@[expose] def mkSynElf64
    (eiVer eVer ehSz shEntSz : Nat) (eiPad9 : Nat)
    (dataFlags dataSz dataEnt : Nat)
    (symBind symType symVal : Nat)
    (relaOff relaTy : Nat) (relaAdd : Int)
    (extraInitArray : Bool) : List UInt8 :=
  mkSynElf64Ex eiVer eVer ehSz shEntSz eiPad9
    dataFlags dataSz dataEnt (shfAlloc + shfExecInstr)
    symBind symType 2 symVal relaOff 1 relaTy relaAdd true extraInitArray false

/-- Full-code synthetic ELF64 `ET_REL` builder embedding `canaryAvx2Text` in
executable `.text` section `3` for `funcTextBytes?` / `decodeFuncFromElf?`. -/
@[expose] def mkSynElf64WithText
    (dataFlags dataSz dataEnt : Nat)
    (symBind symType symVal : Nat)
    (relaOff relaTy : Nat) (relaAdd : Int) : List UInt8 :=
  mkSynElf64Ex 1 1 64 64 0 dataFlags dataSz dataEnt (shfAlloc + shfExecInstr)
    symBind symType 2 symVal relaOff 1 relaTy relaAdd true false true

/-- Clean raw ELF64 images covering `SHF_MERGE` `.LCPI0_0` (`shEntsize = 32`
and `16`) and non-merge `STT_SECTION` `.rodata`. -/
@[expose] def cleanMerge32Elf : List UInt8 :=
  mkSynElf64WithText (shfAlloc + shfMerge) 64 32 stbLocal 0 0
    12 rX86_64_PC32 (Int.negSucc 3)

@[expose] def cleanNonMergeSecSymElf : List UInt8 :=
  mkSynElf64 1 1 64 64 0 shfAlloc 64 0 stbLocal sttSection 0
    12 rX86_64_PC32 (Int.negSucc 3) false

@[expose] def cleanMerge16SameEntryElf : List UInt8 :=
  mkSynElf64 1 1 64 64 0 (shfAlloc + shfMerge) 32 16 stbLocal 0 0
    12 rX86_64_PC32 (Int.negSucc 3) false

/-- Header identity rejections: bad `EI_VERSION`, `e_version`, `e_ehsize`,
oversized `e_shentsize = 72`, and non-zero `EI_PAD[9]`. -/
theorem canary_elf64_header_identity_rejections :
    (parseElf64Header? (mkSynElf64 0 1 64 64 0 shfAlloc 32 0 stbLocal 0 0
      12 rX86_64_PC32 (Int.negSucc 3) false)).isNone = true ∧
    (parseElf64Header? (mkSynElf64 1 0 64 64 0 shfAlloc 32 0 stbLocal 0 0
      12 rX86_64_PC32 (Int.negSucc 3) false)).isNone = true ∧
    (parseElf64Header? (mkSynElf64 1 1 63 64 0 shfAlloc 32 0 stbLocal 0 0
      12 rX86_64_PC32 (Int.negSucc 3) false)).isNone = true ∧
    (parseElf64Header? (mkSynElf64 1 1 64 72 0 shfAlloc 32 0 stbLocal 0 0
      12 rX86_64_PC32 (Int.negSucc 3) false)).isNone = true ∧
    (parseElf64Header? (mkSynElf64 1 1 64 64 1 shfAlloc 32 0 stbLocal 0 0
      12 rX86_64_PC32 (Int.negSucc 3) false)).isNone = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Positive raw-object `objectHasNoForbiddenElfFeatures`,
`resolvePc32RodataReloc`, and `extractFuncPcRelRelocs?` controls on
`cleanMerge32Elf` targeting executable `.text` section `3`. -/
theorem canary_pc32_rodata_positive :
    objectHasNoForbiddenElfFeatures cleanMerge32Elf = true ∧
    resolvePc32RodataReloc cleanMerge32Elf 3 0 16 32 =
      some { secIdx := 2, byteOff := 0, accessBytes := 32 } ∧
    extractFuncPcRelRelocs? cleanMerge32Elf 3 0 20 =
      some [ { offset := 12, secIdx := 2, target := Int.negSucc 3 } ] :=
  ⟨rfl, rfl, rfl⟩

/-- Positive non-merge `STT_SECTION` `.rodata` control. -/
theorem canary_pc32_non_merge_sec_sym_positive :
    resolvePc32RodataReloc cleanNonMergeSecSymElf 3 0 16 32 =
      some { secIdx := 2, byteOff := 0, accessBytes := 32 } := rfl

/-- End-to-end raw-ELF function decode canary: `funcTextBytes?` slices
`canaryAvx2Text` verbatim out of executable `.text` section `3`,
`decodeFuncFromElf?` decodes all 5 instructions with 1-to-1 relocation coverage
and per-operand `.rodata` bounds validation, and certifies
`dirtyYmmClearedBeforeRet` + `checkStraightLineAbiSfiFixedBases` purely from
raw bytes `cleanMerge32Elf`. -/
theorem canary_decode_func_from_elf_end_to_end :
    let insns :=
      match decodeFuncFromElf? canaryRelocCfg cleanMerge32Elf 3 0 20 with
      | some tr => tr.map (fun e => e.2.2)
      | none => []
    funcTextBytes? cleanMerge32Elf 3 0 20 = some canaryAvx2Text ∧
    insns.length = 5 ∧
    dirtyYmmClearedBeforeRet insns = true ∧
    checkStraightLineAbiSfiFixedBases [.rdi, .rsi] insns = true ∧
    decodeFuncFromElf? canaryRelocCfg cleanMerge32Elf 3 0 21 = none ∧
    decodeFuncFromElf? canaryRelocCfg cleanMerge32Elf 2 0 20 = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Negative `decodeFuncFromElf?` canary: negative effective offset
(`rAddend = -100` -> `effOff = -96`) is rejected fail-closed. -/
theorem canary_decode_func_rejects_neg_off :
    decodeFuncFromElf? canaryRelocCfg
      (mkSynElf64WithText shfAlloc 64 0 stbLocal 0 0
        12 rX86_64_PC32 (Int.negSucc 99)) 3 0 20 = none := rfl

/-- Negative `decodeFuncFromElf?` canary: 32-byte OOB `.rodata` read
(`rAddend = 40` -> `[44, 76)` of 64B `.rodata`) is rejected fail-closed. -/
theorem canary_decode_func_rejects_oob32 :
    decodeFuncFromElf? canaryRelocCfg
      (mkSynElf64WithText shfAlloc 64 0 stbLocal 0 0
        12 rX86_64_PC32 (Int.ofNat 40)) 3 0 20 = none := rfl

/-- Negative `decodeFuncFromElf?` canary: `SHF_MERGE` cross-entry escape
(`shEntsize = 16`, `rAddend = 12` -> `effOff = 16`) is rejected fail-closed. -/
theorem canary_decode_func_rejects_merge_cross_entry :
    decodeFuncFromElf? canaryRelocCfg
      (mkSynElf64WithText (shfAlloc + shfMerge) 32 16 stbLocal 0 0
        12 rX86_64_PC32 (Int.ofNat 12)) 3 0 20 = none := rfl

/-- Negative `textSecIdx` validation controls: out-of-range section (`99`) and
non-executable sections (`SHT_NULL` at `0`, `.strtab` at `1`, `.rodata` at `2`)
are rejected fail-closed. -/
theorem canary_text_sec_oob_and_non_exec_rejected :
    extractFuncPcRelRelocs? cleanMerge32Elf 99 0 20 = none ∧
    resolvePc32RodataReloc cleanMerge32Elf 99 0 16 32 = none ∧
    funcTextBytes? cleanMerge32Elf 99 0 20 = none ∧
    extractFuncPcRelRelocs? cleanMerge32Elf 2 0 20 = none ∧
    resolvePc32RodataReloc cleanMerge32Elf 2 0 16 32 = none ∧
    funcTextBytes? cleanMerge32Elf 2 0 20 = none ∧
    extractFuncPcRelRelocs? cleanMerge32Elf 1 0 1 = none ∧
    extractFuncPcRelRelocs? cleanMerge32Elf 0 0 0 = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Negative `textSecIdx` oversize function bounds (`funcSize = 21` and
`16 + 8 > 20`) are rejected fail-closed. -/
theorem canary_text_sec_oversize_rejected :
    extractFuncPcRelRelocs? cleanMerge32Elf 3 0 21 = none ∧
    funcTextBytes? cleanMerge32Elf 3 0 21 = none ∧
    extractFuncPcRelRelocs? cleanMerge32Elf 3 16 8 = none ∧
    funcTextBytes? cleanMerge32Elf 3 16 8 = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Negative `SHT_NULL` (`sections[0]`) and `STN_UNDEF` (`r_sym = 0`)
rejections. -/
theorem canary_non_null_sec0_and_rsym_zero_rejected :
    let nonNullSec0Elf :=
      mkSynElf64Ex 1 1 64 64 0 shfAlloc 64 0 (shfAlloc + shfExecInstr)
        stbLocal 0 2 0 12 1 rX86_64_PC32 (Int.negSucc 3) false false false
    let rSymZeroElf :=
      mkSynElf64Ex 1 1 64 64 0 shfAlloc 64 0 (shfAlloc + shfExecInstr)
        stbLocal 0 2 0 12 0 rX86_64_PC32 (Int.negSucc 3) true false false
    (parseElf64Object? nonNullSec0Elf).isNone = true ∧
    resolvePc32RodataReloc rSymZeroElf 3 0 16 32 = none ∧
    extractFuncPcRelRelocs? rSymZeroElf 3 0 20 = none :=
  ⟨rfl, rfl, rfl⟩

/-- Negative `SHN_UNDEF` (`st_shndx = 0`) and `SHN_ABS` (`0xFFF1`)
rejections. -/
theorem canary_shn_undef_and_abs_rejected :
    let shnUndefElf :=
      mkSynElf64Ex 1 1 64 64 0 shfAlloc 64 0 (shfAlloc + shfExecInstr)
        stbLocal 0 0 0 12 1 rX86_64_PC32 (Int.negSucc 3) true false false
    let shnAbsElf :=
      mkSynElf64Ex 1 1 64 64 0 shfAlloc 64 0 (shfAlloc + shfExecInstr)
        stbLocal 0 0xFFF1 0 12 1 rX86_64_PC32 (Int.negSucc 3) true false false
    resolvePc32RodataReloc shnUndefElf 3 0 16 32 = none ∧
    extractFuncPcRelRelocs? shnUndefElf 3 0 20 = none ∧
    resolvePc32RodataReloc shnAbsElf 3 0 16 32 = none ∧
    extractFuncPcRelRelocs? shnAbsElf 3 0 20 = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Negative `SHN_COMMON` (`0xFFF2`) and `SHN_XINDEX` (`0xFFFF`) rejections. -/
theorem canary_shn_common_and_xindex_rejected :
    let shnCommonElf :=
      mkSynElf64Ex 1 1 64 64 0 shfAlloc 64 0 (shfAlloc + shfExecInstr)
        stbLocal 0 0xFFF2 0 12 1 rX86_64_PC32 (Int.negSucc 3) true false false
    let shnXindexElf :=
      mkSynElf64Ex 1 1 64 64 0 shfAlloc 64 0 (shfAlloc + shfExecInstr)
        stbLocal 0 0xFFFF 0 12 1 rX86_64_PC32 (Int.negSucc 3) true false false
    resolvePc32RodataReloc shnCommonElf 3 0 16 32 = none ∧
    extractFuncPcRelRelocs? shnCommonElf 3 0 20 = none ∧
    resolvePc32RodataReloc shnXindexElf 3 0 16 32 = none ∧
    extractFuncPcRelRelocs? shnXindexElf 3 0 20 = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Negative `.text` flag exclusions: `SHF_GROUP` and `SHF_COMPRESSED` on
`.text` are rejected fail-closed. -/
theorem canary_text_rejects_group_and_compressed :
    let textGroupElf :=
      mkSynElf64Ex 1 1 64 64 0 shfAlloc 64 0
        (shfAlloc + shfExecInstr + shfGroup)
        stbLocal 0 2 0 12 1 rX86_64_PC32 (Int.negSucc 3) true false false
    let textCompElf :=
      mkSynElf64Ex 1 1 64 64 0 shfAlloc 64 0
        (shfAlloc + shfExecInstr + shfCompressed)
        stbLocal 0 2 0 12 1 rX86_64_PC32 (Int.negSucc 3) true false false
    funcTextBytes? textGroupElf 3 0 20 = none ∧
    extractFuncPcRelRelocs? textGroupElf 3 0 20 = none ∧
    decodeFuncFromElf? canaryRelocCfg textGroupElf 3 0 20 = none ∧
    funcTextBytes? textCompElf 3 0 20 = none ∧
    decodeFuncFromElf? canaryRelocCfg textCompElf 3 0 20 = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Negative `.rodata` flag exclusions: `SHF_COMPRESSED` and `SHF_TLS` are
rejected fail-closed. -/
theorem canary_rodata_rejects_compressed_and_tls :
    let roCompElf :=
      mkSynElf64 1 1 64 64 0 (shfAlloc + shfCompressed) 64 0 stbLocal 0 0
        12 rX86_64_PC32 (Int.negSucc 3) false
    let roTlsElf :=
      mkSynElf64 1 1 64 64 0 (shfAlloc + shfTls) 64 0 stbLocal 0 0
        12 rX86_64_PC32 (Int.negSucc 3) false
    resolvePc32RodataReloc roCompElf 3 0 16 32 = none ∧
    extractFuncPcRelRelocs? roCompElf 3 0 20 = none ∧
    resolvePc32RodataReloc roTlsElf 3 0 16 32 = none ∧
    extractFuncPcRelRelocs? roTlsElf 3 0 20 = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Negative `.rodata` `SHF_STRINGS` rejection. -/
theorem canary_rodata_rejects_strings :
    let roStrElf :=
      mkSynElf64 1 1 64 64 0 (shfAlloc + shfMerge + shfStrings) 64 1 stbLocal
        0 0 12 rX86_64_PC32 (Int.negSucc 3) false
    resolvePc32RodataReloc roStrElf 3 0 16 32 = none ∧
    extractFuncPcRelRelocs? roStrElf 3 0 20 = none :=
  ⟨rfl, rfl⟩

/-- Negative raw-object ELF64 controls (split per-pair to bound kernel WHNF
memory): `SHF_MERGE` straddle and `STB_GLOBAL` symbol rejections. -/
theorem canary_pc32_rejects_merge_straddle_and_global :
    resolvePc32RodataReloc
      (mkSynElf64 1 1 64 64 0 (shfAlloc + shfMerge) 64 32 stbLocal 0 0
        12 rX86_64_PC32 (Int.ofNat 12) false) 3 0 16 32 = none ∧
    resolvePc32RodataReloc
      (mkSynElf64 1 1 64 64 0 shfAlloc 64 0 stbGlobal 1 0
        12 rX86_64_PC32 (Int.negSucc 3) false) 3 0 16 32 = none :=
  ⟨rfl, rfl⟩

/-- Negative raw-object ELF64 controls: `SHF_GROUP` and writable `.data`. -/
theorem canary_pc32_rejects_group_and_writable :
    resolvePc32RodataReloc
      (mkSynElf64 1 1 64 64 0 (shfAlloc + shfGroup) 64 0 stbLocal 0 0
        12 rX86_64_PC32 (Int.negSucc 3) false) 3 0 16 32 = none ∧
    resolvePc32RodataReloc
      (mkSynElf64 1 1 64 64 0 (shfWrite + shfAlloc) 64 0 stbLocal 0 0
        12 rX86_64_PC32 (Int.negSucc 3) false) 3 0 16 32 = none :=
  ⟨rfl, rfl⟩

/-- Negative raw-object ELF64 controls: OOB offset and `R_X86_64_IRELATIVE`. -/
theorem canary_pc32_rejects_oob_and_irelative :
    resolvePc32RodataReloc
      (mkSynElf64 1 1 64 64 0 shfAlloc 64 0 stbLocal 0 0
        12 rX86_64_PC32 (Int.ofNat 40) false) 3 0 16 32 = none ∧
    resolvePc32RodataReloc
      (mkSynElf64 1 1 64 64 0 shfAlloc 64 0 stbLocal 0 0
        12 rX86_64_IRelative (Int.ofNat 0) false) 3 0 16 32 = none :=
  ⟨rfl, rfl⟩

/-- Negative raw-object ELF64 controls: `STT_GNU_IFUNC` and `.init_array`. -/
theorem canary_pc32_rejects_ifunc_and_init_array :
    resolvePc32RodataReloc
      (mkSynElf64 1 1 64 64 0 shfAlloc 64 0 stbLocal sttGnuIfunc 0
        12 rX86_64_PC32 (Int.negSucc 3) false) 3 0 16 32 = none ∧
    resolvePc32RodataReloc
      (mkSynElf64 1 1 64 64 0 shfAlloc 64 0 stbLocal 0 0
        12 rX86_64_PC32 (Int.negSucc 3) true) 3 0 16 32 = none :=
  ⟨rfl, rfl⟩

/-- Negative raw-object ELF64 control: `R_X86_64_32S` in `.rela.text`. -/
theorem canary_extract_rejects_32s :
    extractFuncPcRelRelocs?
      (mkSynElf64 1 1 64 64 0 shfAlloc 64 0 stbLocal 0 0
        4 rX86_64_32S (Int.ofNat 0) false) 3 0 20 = none := rfl

/-- Synthetic raw ELF64 object containing all-zero `SHT_NULL` at index `0`, a
real executable `.text` section at index `3` (`SHT_PROGBITS`,
`SHF_ALLOC | SHF_EXECINSTR`, `shSize = 20`), and TWO `SHT_RELA` sections both
targeting `textSecIdx = 3` (`shInfo = 3`), each carrying a valid `R_X86_64_PC32`
entry. `objectHasNoForbiddenElfFeatures` and `funcTextBytes?` succeed
(confirming rejection is due strictly to duplicate RELA), while
`extractFuncPcRelRelocs?`, `resolvePc32RodataReloc`, and `decodeFuncFromElf?`
all fail closed. -/
@[expose] def dupRelaSameTextElf : List UInt8 :=
  let strtab : List UInt8 := [0]
  let symBytes : List UInt8 :=
    encZeroSym ++ encSym 0 stbLocal 0 2 0 16
  let rela1Bytes : List UInt8 := encRela 12 1 rX86_64_PC32 (Int.negSucc 3)
  let rela2Bytes : List UInt8 := encRela 4 1 rX86_64_PC32 (Int.negSucc 3)
  -- Offsets: hdr=0..63, strtab=64, text=65..84, sym=85..132,
  -- rela1=133..156, rela2=157..180, shOff=181 (7 shdrs = 448B -> total 629B).
  let hdr : List UInt8 :=
    [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 62, 0, 1, 0, 0, 0] ++
    (encZero8 ++ (encZero8 ++ (encU64 181 ++
    [0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 64, 0, 7, 0, 1, 0])))
  let shdrs : List UInt8 :=
    encNullShdr ++
    (encShdr 0 shtStrtab 0 64 1 0 0 0 ++
    (encShdr 0 shtProgbits shfAlloc 0 64 0 0 0 ++
    (encShdr 0 shtProgbits (shfAlloc + shfExecInstr) 65 20 0 0 0 ++
    (encShdr 0 shtSymtab 0 85 48 1 2 24 ++
    (encShdr 0 shtRela 0 133 24 4 3 24 ++
    encShdr 0 shtRela 0 157 24 4 3 24)))))
  hdr ++ (strtab ++ (canaryAvx2Text ++ (symBytes ++
    (rela1Bytes ++ (rela2Bytes ++ shdrs)))))

theorem canary_duplicate_rela_for_same_text_rejected :
    objectHasNoForbiddenElfFeatures dupRelaSameTextElf = true ∧
    funcTextBytes? dupRelaSameTextElf 3 0 20 = some canaryAvx2Text ∧
    extractFuncPcRelRelocs? dupRelaSameTextElf 3 0 20 = none ∧
    resolvePc32RodataReloc dupRelaSameTextElf 3 0 16 32 = none ∧
    decodeFuncFromElf? canaryRelocCfg dupRelaSameTextElf 3 0 20 = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Synthetic raw ELF64 object containing a valid `.rela.text` (`shInfo = 3`)
PLUS a `.rela.rodata` section (`shInfo = 2`) carrying an `R_X86_64_64`
relocation at offset `0` overlapping the certified `.rodata` access. -/
@[expose] def relaTargetingRodataElf : List UInt8 :=
  let strtab : List UInt8 := [0]
  let symBytes : List UInt8 :=
    encZeroSym ++ encSym 0 stbLocal 0 2 0 32
  let relaTextBytes : List UInt8 := encRela 12 1 rX86_64_PC32 (Int.negSucc 3)
  let relaRodataBytes : List UInt8 := encRela 0 1 rX86_64_64 (Int.ofNat 0)
  -- Offsets: hdr=0..63, strtab=64, text=65..84, sym=85..132,
  -- relaText=133..156, relaRodata=157..180, shOff=181 (7 shdrs = 448B).
  let hdr : List UInt8 :=
    [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 62, 0, 1, 0, 0, 0] ++
    (encZero8 ++ (encZero8 ++ (encU64 181 ++
    [0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 64, 0, 7, 0, 1, 0])))
  let shdrs : List UInt8 :=
    encNullShdr ++
    (encShdr 0 shtStrtab 0 64 1 0 0 0 ++
    (encShdr 0 shtProgbits shfAlloc 0 64 0 0 0 ++
    (encShdr 0 shtProgbits (shfAlloc + shfExecInstr) 65 20 0 0 0 ++
    (encShdr 0 shtSymtab 0 85 48 1 2 24 ++
    (encShdr 0 shtRela 0 133 24 4 3 24 ++
    encShdr 0 shtRela 0 157 24 4 2 24)))))
  hdr ++ (strtab ++ (canaryAvx2Text ++ (symBytes ++
    (relaTextBytes ++ (relaRodataBytes ++ shdrs)))))

/-- Negative `.rela.rodata` canary: any `SHT_RELA` section targeting the
resolved `.rodata` section (`shInfo = sym.stShndx = 2`) is rejected by
`resolvePc32RodataReloc`, `extractFuncPcRelRelocs?`, and `decodeFuncFromElf?`.
-/
theorem canary_rela_targeting_rodata_rejected :
    objectHasNoForbiddenElfFeatures relaTargetingRodataElf = true ∧
    funcTextBytes? relaTargetingRodataElf 3 0 20 = some canaryAvx2Text ∧
    resolvePc32RodataReloc relaTargetingRodataElf 3 0 16 32 = none ∧
    extractFuncPcRelRelocs? relaTargetingRodataElf 3 0 20 = none ∧
    decodeFuncFromElf? canaryRelocCfg relaTargetingRodataElf 3 0 20 = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Compact ELF64 builder with parameterized metadata flags on `.shstrtab`,
`SHT_SYMTAB`, distinct linked `.strtab`, and `SHT_RELA` (plus `relaLink`). -/
@[expose] def mkMetaFlagElf64 (shstrFlg symFlg strFlg relaFlg relaLink : Nat) :
    List UInt8 :=
  let strtab : List UInt8 := [0]
  let symBytes : List UInt8 :=
    encZeroSym ++ encSym 0 stbLocal 0 2 0 16
  let relaBytes : List UInt8 := encRela 12 1 rX86_64_PC32 (Int.negSucc 3)
  -- Offsets: hdr=0..63, shstr=64, str=65, sym=66..113, rela=114..137,
  -- shOff=138 (7 shdrs: 0:NULL, 1:.shstrtab, 2:.rodata, 3:.text, 4:.symtab,
  -- 5:.rela.text, 6:.strtab).
  let hdr : List UInt8 :=
    [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 62, 0, 1, 0, 0, 0] ++
    (encZero8 ++ (encZero8 ++ (encU64 138 ++
    [0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 64, 0, 7, 0, 1, 0])))
  let shdrs : List UInt8 :=
    encNullShdr ++
    (encShdr 0 shtStrtab shstrFlg 64 1 0 0 0 ++
    (encShdr 0 shtProgbits shfAlloc 0 64 0 0 0 ++
    (encShdr 0 shtProgbits (shfAlloc + shfExecInstr) 0 20 0 0 0 ++
    (encShdr 0 shtSymtab symFlg 66 48 6 2 24 ++
    (encShdr 0 shtRela relaFlg 114 24 relaLink 3 24 ++
    encShdr 0 shtStrtab strFlg 65 1 0 0 0)))))
  hdr ++ (strtab ++ (strtab ++ (symBytes ++ (relaBytes ++ shdrs))))

/-- Negative `SHF_COMPRESSED` metadata canaries: compressed `.shstrtab` and
compressed `SHT_SYMTAB` are rejected by `parseElf64Object?`. -/
theorem canary_compressed_shstrtab_and_symtab_rejected :
    (parseElf64Object? (mkMetaFlagElf64 0 0 0 0 4)).isSome = true ∧
    (parseElf64Object? (mkMetaFlagElf64 shfCompressed 0 0 0 4)).isNone = true ∧
    (parseElf64Object? (mkMetaFlagElf64 0 shfCompressed 0 0 4)).isNone = true :=
  ⟨rfl, rfl, rfl⟩

/-- Negative `SHF_COMPRESSED` metadata canaries: compressed linked `.strtab`
and compressed `SHT_RELA` are rejected by `parseElf64Object?`. -/
theorem canary_compressed_strtab_and_rela_rejected :
    (parseElf64Object? (mkMetaFlagElf64 0 0 shfCompressed 0 4)).isNone = true ∧
    (parseElf64Object? (mkMetaFlagElf64 0 0 0 shfCompressed 4)).isNone = true :=
  ⟨rfl, rfl⟩

/-- Proactive ELF metadata & relocation-link canaries: bad `SHT_RELA.shLink`,
COMDAT `SHF_GROUP` on `.rela.text`, `SHF_EXCLUDE` on `.rodata`/`.text`, and
overlapping sibling relocation on the same `PC32` slot are rejected. -/
theorem canary_rela_bad_shlink_and_group_rejected :
    let groupRelaElf := mkMetaFlagElf64 0 0 0 shfGroup 4
    (parseElf64Object? (mkMetaFlagElf64 0 0 0 0 0)).isNone = true ∧
    resolvePc32RodataReloc groupRelaElf 3 0 16 32 = none ∧
    extractFuncPcRelRelocs? groupRelaElf 3 0 20 = none :=
  ⟨rfl, rfl, rfl⟩

/-- Proactive `SHF_EXCLUDE` and overlapping sibling `PC32` relocation
rejections. -/
theorem canary_exclude_flag_and_overlap_pc32_rejected :
    let exRoElf :=
      mkSynElf64 1 1 64 64 0 (shfAlloc + shfExclude) 64 0 stbLocal 0 0
        12 rX86_64_PC32 (Int.negSucc 3) false
    let exTxtElf :=
      mkSynElf64Ex 1 1 64 64 0 shfAlloc 64 0
        (shfAlloc + shfExecInstr + shfExclude)
        stbLocal 0 2 0 12 1 rX86_64_PC32 (Int.negSucc 3) true false false
    let ovRelas : List UInt8 :=
      encRela 12 1 rX86_64_PC32 (Int.negSucc 3) ++
      encRela 13 1 rX86_64_PC32 (Int.negSucc 3)
    let ovHdr : List UInt8 :=
      [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       1, 0, 62, 0, 1, 0, 0, 0] ++
      (encZero8 ++ (encZero8 ++ (encU64 161 ++
      [0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 64, 0, 6, 0, 1, 0])))
    let ovShdrs : List UInt8 :=
      encNullShdr ++
      (encShdr 0 shtStrtab 0 64 1 0 0 0 ++
      (encShdr 0 shtProgbits shfAlloc 0 64 0 0 0 ++
      (encShdr 0 shtProgbits (shfAlloc + shfExecInstr) 0 20 0 0 0 ++
      (encShdr 0 shtSymtab 0 65 48 1 2 24 ++
      encShdr 0 shtRela 0 113 48 4 3 24))))
    let ovElf : List UInt8 :=
      ovHdr ++ ([0] ++ (encZeroSym ++ encSym 0 stbLocal 0 2 0 16 ++
        (ovRelas ++ ovShdrs)))
    resolvePc32RodataReloc exRoElf 3 0 16 32 = none ∧
    funcTextBytes? exTxtElf 3 0 20 = none ∧
    resolvePc32RodataReloc ovElf 3 0 16 32 = none :=
  ⟨rfl, rfl, rfl⟩

/-- Synthetic ELF64 object whose `.text` section `3` holds a base-less SIB
absolute load `48 8B 04 25 78 56 34 12; C3` (`mov rax, [0x12345678]; ret`). -/
@[expose] def baselessSibElf : List UInt8 :=
  let code : List UInt8 :=
    [0x48, 0x8B, 0x04, 0x25, 0x78, 0x56, 0x34, 0x12, 0xC3]
  -- Offsets: hdr=0..63, strtab=64, text=65..73, shOff=74 (4 shdrs).
  let hdr : List UInt8 :=
    [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 62, 0, 1, 0, 0, 0] ++
    (encZero8 ++ (encZero8 ++ (encU64 74 ++
    [0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 64, 0, 4, 0, 1, 0])))
  let shdrs : List UInt8 :=
    encNullShdr ++
    (encShdr 0 shtStrtab 0 64 1 0 0 0 ++
    (encShdr 0 shtProgbits shfAlloc 0 64 0 0 0 ++
    encShdr 0 shtProgbits (shfAlloc + shfExecInstr) 65 9 0 0 0))
  hdr ++ ([0] ++ (code ++ shdrs))

/-- `decodeFuncFromElf?` fails closed when `cfg.requireRelocForRip = false`
and rejects base-less SIB `[disp32]` under any `cfg`; SFI tiers also reject
base-less SIB loads directly. -/
theorem canary_decode_func_rejects_noreloc_cfg_and_baseless_sib :
    let rawInsns :=
      match decodeStream canaryNoRelocCfg []
          [0x48, 0x8B, 0x04, 0x25, 0x78, 0x56, 0x34, 0x12, 0xC3] with
      | some tr => tr.map (fun e => e.2.2)
      | none => []
    decodeFuncFromElf? canaryNoRelocCfg cleanMerge32Elf 3 0 20 = none ∧
    decodeFuncFromElf? canaryRelocCfg baselessSibElf 3 0 9 = none ∧
    decodeFuncFromElf? canaryNoRelocCfg baselessSibElf 3 0 9 = none ∧
    rawInsns.length = 2 ∧
    checkStraightLineAbiSfiArgStores rawInsns = false ∧
    checkStraightLineAbiSfiStoreBaseNamesOnly [.rdi, .rsi] rawInsns = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Proactive ELF64 `ET_REL` header checks: non-zero `e_flags` and non-zero
`e_phnum` are rejected by `parseElf64Header?`. -/
theorem canary_header_nonzero_eflags_and_phnum_rejected :
    let badFlagsHdr : List UInt8 :=
      [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       1, 0, 62, 0, 1, 0, 0, 0] ++
      (encZero8 ++ (encZero8 ++ (encU64 64 ++
      [1, 0, 0, 0, 64, 0, 0, 0, 0, 0, 64, 0, 2, 0, 1, 0]))) ++
      encNullShdr ++ encNullShdr
    let badPhnumHdr : List UInt8 :=
      [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
       1, 0, 62, 0, 1, 0, 0, 0] ++
      (encZero8 ++ (encZero8 ++ (encU64 64 ++
      [0, 0, 0, 0, 64, 0, 0, 0, 1, 0, 64, 0, 2, 0, 1, 0]))) ++
      encNullShdr ++ encNullShdr
    (parseElf64Header? badFlagsHdr).isNone = true ∧
    (parseElf64Header? badPhnumHdr).isNone = true :=
  ⟨rfl, rfl⟩

/-- Compact ELF64 builder with 36-byte `.text` (`text36`) and two relocations
in `.rela.text` (`shInfo = 3`) for testing adjacent relaxable/TLS relocations
(`REX_GOTPCRELX`, `TLSGD`). -/
@[expose] def mkTwoRelaText36Elf (text36 : List UInt8)
    (r0Off r0Ty : Nat) (r0Add : Int)
    (r1Off r1Ty : Nat) (r1Add : Int) : List UInt8 :=
  let symBytes : List UInt8 :=
    encZeroSym ++ encSym 0 stbLocal 0 2 0 32
  let relaBytes : List UInt8 :=
    encRela r0Off 1 r0Ty r0Add ++ encRela r1Off 1 r1Ty r1Add
  -- Offsets: hdr=0..63, strtab=64, text36=65..100, sym=101..148,
  -- rela=149..196, shOff=197 (6 shdrs).
  let hdr : List UInt8 :=
    [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 62, 0, 1, 0, 0, 0] ++
    (encZero8 ++ (encZero8 ++ (encU64 197 ++
    [0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 64, 0, 6, 0, 1, 0])))
  let shdrs : List UInt8 :=
    encNullShdr ++
    (encShdr 0 shtStrtab 0 64 1 0 0 0 ++
    (encShdr 0 shtProgbits shfAlloc 0 64 0 0 0 ++
    (encShdr 0 shtProgbits (shfAlloc + shfExecInstr) 65 36 0 0 0 ++
    (encShdr 0 shtSymtab 0 101 48 1 2 24 ++
    encShdr 0 shtRela 0 149 48 4 3 24))))
  hdr ++ ([0] ++ (text36 ++ (symBytes ++ (relaBytes ++ shdrs))))

/-- Relaxable `R_X86_64_REX_GOTPCRELX` at function end (`rOffset = 20` for
`[0, 20)`) is never treated as disjoint and is rejected fail-closed. -/
theorem canary_relaxable_gotpcrelx_at_func_end_rejected :
    let text36 := canaryAvx2Text ++ (encZero8 ++ encZero8)
    let elf := mkTwoRelaText36Elf text36
      12 rX86_64_PC32 (Int.negSucc 3)
      20 rX86_64_REX_GOTPCRELX (Int.ofNat 0)
    relaDisjointFromFunc 0 20
      { rOffset := 20, rSymIdx := 1, rType := rX86_64_REX_GOTPCRELX,
        rAddend := Int.ofNat 0 } = false ∧
    extractFuncPcRelRelocs? elf 3 0 20 = none ∧
    resolvePc32RodataReloc elf 3 0 16 32 = none ∧
    decodeFuncFromElf? canaryRelocCfg elf 3 0 20 = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Relaxable `R_X86_64_TLSGD` before function start (`rOffset = 8` for
`[16, 36)`) is never treated as disjoint and is rejected fail-closed. -/
theorem canary_tlsgd_before_func_start_rejected :
    let text36 := (encZero8 ++ encZero8) ++ canaryAvx2Text
    let elf := mkTwoRelaText36Elf text36
      28 rX86_64_PC32 (Int.negSucc 3)
      8 rX86_64_TLSGD (Int.ofNat 0)
    relaDisjointFromFunc 16 20
      { rOffset := 8, rSymIdx := 1, rType := rX86_64_TLSGD,
        rAddend := Int.ofNat 0 } = false ∧
    extractFuncPcRelRelocs? elf 3 16 20 = none ∧
    resolvePc32RodataReloc elf 3 0 32 32 = none ∧
    decodeFuncFromElf? canaryRelocCfg elf 3 16 20 = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Sibling relaxable relocations (`REX_GOTPCRELX` at `targetOff + 4` and
`TLSGD` at `targetOff - 8`) fail closed in both `otherRelaOverlapsPc32` and
`resolvePc32RodataReloc`. -/
theorem canary_sibling_relaxable_overlaps_pc32_rejected :
    let pc32R : Elf64Rela :=
      { rOffset := 12, rSymIdx := 1, rType := rX86_64_PC32,
        rAddend := Int.negSucc 3 }
    let gotR : Elf64Rela :=
      { rOffset := 16, rSymIdx := 1, rType := rX86_64_REX_GOTPCRELX,
        rAddend := Int.ofNat 0 }
    let tlsR : Elf64Rela :=
      { rOffset := 4, rSymIdx := 1, rType := rX86_64_TLSGD,
        rAddend := Int.ofNat 0 }
    let text36 := canaryAvx2Text ++ (encZero8 ++ encZero8)
    let elf := mkTwoRelaText36Elf text36
      12 rX86_64_PC32 (Int.negSucc 3)
      16 rX86_64_REX_GOTPCRELX (Int.ofNat 0)
    otherRelaOverlapsPc32 [pc32R, gotR] 0 12 = true ∧
    otherRelaOverlapsPc32 [pc32R, tlsR] 0 12 = true ∧
    resolvePc32RodataReloc elf 3 0 16 32 = none :=
  ⟨rfl, rfl, rfl⟩

/-- Synthetic ELF64 object carrying `64 C5 FD FE 05 00 00 00 00; C5 F8 77; C3`
(`fs vpaddd ymm0, ymm0, [rip+0]; vzeroupper; ret`, 13 bytes) with matching
`R_X86_64_PC32` at offset `5`. -/
@[expose] def fsRipRelElf : List UInt8 :=
  let code : List UInt8 :=
    [0x64, 0xC5, 0xFD, 0xFE, 0x05, 0x00, 0x00, 0x00, 0x00,
     0xC5, 0xF8, 0x77, 0xC3]
  let symBytes : List UInt8 :=
    encZeroSym ++ encSym 0 stbLocal 0 2 0 32
  let relaBytes : List UInt8 := encRela 5 1 rX86_64_PC32 (Int.negSucc 3)
  -- Offsets: hdr=0..63, strtab=64, code=65..77, sym=78..125,
  -- rela=126..149, shOff=150 (6 shdrs).
  let hdr : List UInt8 :=
    [0x7F, 0x45, 0x4C, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     1, 0, 62, 0, 1, 0, 0, 0] ++
    (encZero8 ++ (encZero8 ++ (encU64 150 ++
    [0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 64, 0, 6, 0, 1, 0])))
  let shdrs : List UInt8 :=
    encNullShdr ++
    (encShdr 0 shtStrtab 0 64 1 0 0 0 ++
    (encShdr 0 shtProgbits shfAlloc 0 64 0 0 0 ++
    (encShdr 0 shtProgbits (shfAlloc + shfExecInstr) 65 13 0 0 0 ++
    (encShdr 0 shtSymtab 0 78 48 1 2 24 ++
    encShdr 0 shtRela 0 126 24 4 3 24))))
  hdr ++ ([0] ++ (code ++ (symBytes ++ (relaBytes ++ shdrs))))

/-- Active `FS:`/`GS:` segment overrides on RIP-relative operands
(`64 C5 FD FE 05 ...`, `65 C5 FD FE 05 ...`) are rejected in relocatable
`resolveMemAddr`, `traceEntryRipRelocOk`, and `decodeFuncFromElf?`. -/
theorem canary_fs_gs_rip_rel_rejected :
    let fsBytes : List UInt8 :=
      [0x64, 0xC5, 0xFD, 0xFE, 0x05, 0x00, 0x00, 0x00, 0x00]
    let gsBytes : List UInt8 :=
      [0x65, 0xC5, 0xFD, 0xFE, 0x05, 0x00, 0x00, 0x00, 0x00]
    let rels : List PcRelReloc :=
      [ { offset := 5, secIdx := 2, target := Int.negSucc 3 } ]
    let fsInsn : DecodedInsn :=
      .vbin .paddd true 0 0
        (.mem (.ripRel (some .fs) false (some 2) (some 5) (Int.ofNat 0)))
    decodeOne canaryRelocCfg rels 0 fsBytes = none ∧
    decodeOne canaryRelocCfg rels 0 gsBytes = none ∧
    decodeOne canaryNoRelocCfg rels 0 fsBytes = some (fsInsn, 9) ∧
    traceEntryRipRelocOk fsRipRelElf
      [ { rOffset := 5, rSymIdx := 1, rType := rX86_64_PC32,
          rAddend := Int.negSucc 3 } ] 3 0 (0, 9, fsInsn) = false ∧
    (funcTextBytes? fsRipRelElf 3 0 13).isSome = true ∧
    decodeFuncFromElf? canaryRelocCfg fsRipRelElf 3 0 13 = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `SHF_MERGE` `.rodata.cst16` (`shEntsize = 16`, 32 bytes) positive
same-entry control. -/
theorem canary_merge_same_entry_positive :
    resolvePc32RodataReloc cleanMerge16SameEntryElf 3 0 16 16 =
      some { secIdx := 2, byteOff := 0, accessBytes := 16 } := rfl

/-- `SHF_MERGE` `.rodata.cst16` cross-entry `.LCPI0_0 + 16` and `STT_SECTION`
into `SHF_MERGE` rejections. -/
theorem canary_merge_cross_entry_and_sec_sym_rejected :
    let crossEntryElf :=
      mkSynElf64 1 1 64 64 0 (shfAlloc + shfMerge) 32 16 stbLocal 0 0
        12 rX86_64_PC32 (Int.ofNat 12) false
    let mergeSecSymElf :=
      mkSynElf64 1 1 64 64 0 (shfAlloc + shfMerge) 32 16 stbLocal sttSection 0
        12 rX86_64_PC32 (Int.negSucc 3) false
    resolvePc32RodataReloc crossEntryElf 3 0 16 16 = none ∧
    resolvePc32RodataReloc mergeSecSymElf 3 0 16 16 = none ∧
    extractFuncPcRelRelocs? mergeSecSymElf 3 0 20 = none :=
  ⟨rfl, rfl, rfl⟩

/-- `.shstrtab` string parsing and forbidden `.ctors`/`.dtors`/`.init`/`.fini`
section rejections. -/
theorem canary_shstrtab_and_forbidden_sections :
    let baseSec : Elf64SectionHdr :=
      { name := ".rodata", shType := shtProgbits, shFlags := shfAlloc,
        shOffset := 0, shSize := 16, shLink := 0, shInfo := 0, shEntsize := 0 }
    readNullTermString? [0, 46, 99, 116, 111, 114, 115, 0] 1 =
      some ".ctors" ∧
    sectionIsForbidden { baseSec with name := ".ctors.100" } = true ∧
    sectionIsForbidden { baseSec with name := ".dtors" } = true ∧
    sectionIsForbidden { baseSec with name := ".init" } = true ∧
    sectionIsForbidden { baseSec with name := ".fini.startup" } = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## 6. Backward `DeadFlagCollapse`, `call`/`syscall` Clobber, &
Non-Trivial `TraceStepReadsAgree` Canaries -/

/-- `0F BC C0; C1 E1 00; 13 D6` (`bsf eax, eax; shl ecx, 0; adc edx, esi`):
`shl ecx, 0` preserves all flags, so undefined `CF` from `bsf` reaches `adc`
and MUST be rejected (`none`). -/
theorem canary_p0a_bsf_shl0_adc_rejected :
    let insns := decodeOnlyInsns
      [0x0F, 0xBC, 0xC0, 0xC1, 0xE1, 0x00, 0x13, 0xD6]
    insns.length = 3 ∧
    listGet? insns 0 = some (.bsf .s32 .rax (.reg .rax)) ∧
    backwardLiveFlags FlagMask.dead insns = none :=
  ⟨rfl, rfl, rfl⟩

/-- `66 C1 E0 11; 48 13 C3` (`shl ax, 17; adc rbx, rax`): 16-bit shift with
masked count `17 ≥ 16` leaves `CF` undefined, so `adc` MUST be rejected
(`none`). -/
theorem canary_p0b_shl16_cnt17_adc_rejected :
    let insns := decodeOnlyInsns [0x66, 0xC1, 0xE0, 0x11, 0x48, 0x13, 0xC3]
    insns.length = 2 ∧
    listGet? insns 0 = some (.shiftRmImm .s16 .shl (.reg .rax) 17) ∧
    backwardLiveFlags FlagMask.dead insns = none :=
  ⟨rfl, rfl, rfl⟩

/-- `add eax, ecx; call +0; adc eax, edx` (`03 C1; E8 00 00 00 00; 13 C2`)
and `add; syscall; adc` are rejected fail-closed because `call`/`syscall` leave
all 6 status flags undefined (wildcard-free `insnFlagEffect`). -/
theorem canary_call_and_syscall_flag_clobber_rejected :
    let callInsns := decodeOnlyInsns
      [0x03, 0xC1, 0xE8, 0x00, 0x00, 0x00, 0x00, 0x13, 0xC2]
    callInsns.length = 3 ∧
    listGet? callInsns 1 = some (.callRel 0) ∧
    backwardLiveFlags FlagMask.dead callInsns = none ∧
    backwardLiveFlags FlagMask.dead
      [ .aluRegRm .s32 .add .rax (.reg .rcx),
        .syscall,
        .aluRegRm .s32 .adc .rax (.reg .rdx) ] = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `syscall`, `sysenter`, `int n`, `int3`, and `ud2` observe all six status
flags (`reads := FlagMask.all`), so undefined flags from `bsf` flowing into any
of them are rejected by `backwardLiveFlags`, whereas fully defined flags from
`add` before `syscall` pass. -/
theorem canary_trap_and_syscall_flag_reads_rejected :
    backwardLiveFlags FlagMask.dead
      [ .bsf .s32 .rax (.reg .rax), .syscall ] = none ∧
    backwardLiveFlags FlagMask.dead
      [ .bsf .s32 .rax (.reg .rax), .sysenter ] = none ∧
    backwardLiveFlags FlagMask.dead
      [ .bsf .s32 .rax (.reg .rax), .intImm 0x80 ] = none ∧
    backwardLiveFlags FlagMask.dead
      [ .bsf .s32 .rax (.reg .rax), .int3 ] = none ∧
    backwardLiveFlags FlagMask.dead
      [ .bsf .s32 .rax (.reg .rax), .ud2 ] = none ∧
    backwardLiveFlags FlagMask.dead
      [ .aluRegRm .s32 .add .rax (.reg .rcx), .syscall ] =
      some FlagMask.dead :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `shl eax, 1` defines `OF` while `shl eax, 2` leaves `OF` undefined;
`tzcnt` defines `CF` (feeding `adc`), whereas `bsf` leaves `CF` undefined. -/
theorem canary_shift1_of_and_tzcnt_cf :
    backwardLiveFlags ⟨false, false, false, false, false, true⟩
      [ .shiftRmImm .s32 .shl (.reg .rax) 1 ] = some FlagMask.dead ∧
    backwardLiveFlags ⟨false, false, false, false, false, true⟩
      [ .shiftRmImm .s32 .shl (.reg .rax) 2 ] = none ∧
    backwardLiveFlags FlagMask.dead
      [ .tzcnt .s32 .rax (.reg .rcx),
        .aluRegRm .s32 .adc .rdx (.reg .rsi) ] = some FlagMask.dead ∧
    backwardLiveFlags FlagMask.dead
      [ .bsf .s32 .rax (.reg .rcx),
        .aluRegRm .s32 .adc .rdx (.reg .rsi) ] = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Non-trivial `TraceStepReadsAgree` witness: in `xor eax, eax`,
`add eax, ecx`, `adc eax, edx`, `ret`, the `adc` step genuinely reads `CF`
(`detFn` depends on `fl.cf`), and `backwardLiveFlags_volatileRet_reads_agree`
certifies that `adc` observes identical `CF` across arbitrary demonic
`UndefFlags` choices despite volatile `FlagMask.dead` exit. -/
@[expose] def canaryFlagReadTrace (nd0 nd1 nd2 : UndefFlags) :
    List FlagStep :=
  [ { ins := .aluRmReg .s32 false .xor (.reg .rax) .rax
      detFn := fun _ => FlagMask.dead
      nd := nd0
      respectsReads := fun _ _ _ => rfl },
    { ins := .aluRegRm .s32 .add .rax (.reg .rcx)
      detFn := fun _ => ⟨true, false, false, false, false, false⟩
      nd := nd1
      respectsReads := fun _ _ _ => rfl },
    { ins := .aluRegRm .s32 .adc .rax (.reg .rdx)
      detFn := fun fl => ⟨fl.cf, false, false, false, false, false⟩
      nd := nd2
      respectsReads := fun a b h => by
        dsimp only [FlagsAgreeOn, insnFlagEffect, aluFlagEffect] at h
        have hcf : a.cf = b.cf := h.1 rfl
        rw [hcf] },
    { ins := .ret
      detFn := fun _ => FlagMask.dead
      nd := FlagMask.dead
      respectsReads := fun _ _ _ => rfl } ]

theorem canary_volatile_ret_reads_agree_nontrivial
    (nd0 nd1 nd2 f1 f2 : RFlags) :
    TraceStepReadsAgree f1 f2 (canaryFlagReadTrace nd0 nd1 nd2) :=
  backwardLiveFlags_volatileRet_reads_agree
    (canaryFlagReadTrace nd0 nd1 nd2) FlagMask.dead f1 f2 rfl
    (flagsAgreeOn_dead f1 f2)

@[expose] def demonicFlagStream : List DecodedInsn :=
  [ .aluRmReg .s32 false .xor (.reg .rax) .rax,
    .shiftRmImm .s64 .shl (.reg .rcx) 3,
    .imulRegRm .s64 .rax (.reg .rcx),
    .bsf .s64 .rdx (.reg .rax),
    .ret ]

theorem canary_dead_flag_collapse_positive_and_af_reject :
    backwardLiveFlags FlagMask.dead demonicFlagStream = some FlagMask.dead ∧
    backwardLiveFlags ⟨false, false, true, false, false, false⟩
      [ .aluRmReg .s32 false .xor (.reg .rax) .rax ] = none :=
  ⟨rfl, rfl⟩

end Anneal.ElfX86.Canaries
end
