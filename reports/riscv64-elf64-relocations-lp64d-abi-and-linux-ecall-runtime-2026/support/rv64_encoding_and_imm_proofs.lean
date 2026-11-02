-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# RV64GC Instruction Encoding, Large-Frame Immediate Compensation, Branch
# Relaxation, ELF64 Relocations, and LP64D / Linux Syscall ABI Proofs

Self-contained Lean 4.34.1 verification probe covering:
1. 32-bit `RV64GC` instruction word encoding (`R`, `I`, `S`, `B`, `U`, `J`
   formats), little-endian byte serialization (`leBytes32` / `readU32LE`
   round-trip), and `.fence` (`0x0ff0000f`) vs. zero-mask `.fence` (`0x0000000f`)
   bitfield layouts.
2. 12-bit signed immediate overflow (`[-2048, 2047]`) in large stack frames
   (such as `112` slots = `2,720` bytes) and exact 32-bit signed offset
   materialization via `lui` + `addi` sign-extension compensation
   (`hi20 = (imm + 0x800) >> 12`, `lo12 = imm & 0xfff`) using dedicated scratch
   registers `t3` (`x28`) and `t4` (`x29`).
3. Conditional `B`-type (`[-4096, 4094]` bytes) and `J`-type (`[-1048576,
   1048574]` bytes) bit-scrambling layouts, branch condition inversion
   (`funct3 ^^^ 1`), and multi-round fixed-point cascading branch relaxation.
4. RISC-V ELF64 `.symtab` local-before-global ordering (`sh_info`), indirect
   `R_RISCV_PCREL_LO12_I` / `R_RISCV_PCREL_LO12_S` (`r_sym -> P_auipc`) address
   calculation, `LP64D` aggregate return classification, 3-word trait-object
   vtable offsets, and freestanding Linux `riscv64` `ecall` + bump-allocator
   spatial disjointness.
-/

namespace Rv64ElfAbiProbe

-- ============================================================================
-- 1. RV64GC Registers, Raw Instruction Formats, and Little-Endian Round-Trip
-- ============================================================================

/-- The 32 general-purpose 64-bit integer registers of RV64I (`x0`..`x31`). -/
inductive Rv64Reg where
  | x0  | x1  | x2  | x3  | x4  | x5  | x6  | x7
  | x8  | x9  | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x18 | x19 | x20 | x21 | x22 | x23
  | x24 | x25 | x26 | x27 | x28 | x29 | x30 | x31
  deriving DecidableEq, Repr

/-- 5-bit architectural register index (`0..31`). -/
def Rv64Reg.idx : Rv64Reg → Nat
  | .x0  => 0  | .x1  => 1  | .x2  => 2  | .x3  => 3
  | .x4  => 4  | .x5  => 5  | .x6  => 6  | .x7  => 7
  | .x8  => 8  | .x9  => 9  | .x10 => 10 | .x11 => 11
  | .x12 => 12 | .x13 => 13 | .x14 => 14 | .x15 => 15
  | .x16 => 16 | .x17 => 17 | .x18 => 18 | .x19 => 19
  | .x20 => 20 | .x21 => 21 | .x22 => 22 | .x23 => 23
  | .x24 => 24 | .x25 => 25 | .x26 => 26 | .x27 => 27
  | .x28 => 28 | .x29 => 29 | .x30 => 30 | .x31 => 31

/-- Standard RISC-V LP64D ABI register aliases. -/
abbrev zero : Rv64Reg := .x0
abbrev ra   : Rv64Reg := .x1
abbrev sp   : Rv64Reg := .x2
abbrev gp   : Rv64Reg := .x3
abbrev tp   : Rv64Reg := .x4
abbrev t0   : Rv64Reg := .x5
abbrev t1   : Rv64Reg := .x6
abbrev t2   : Rv64Reg := .x7
abbrev s0   : Rv64Reg := .x8
abbrev s1   : Rv64Reg := .x9
abbrev a0   : Rv64Reg := .x10
abbrev a1   : Rv64Reg := .x11
abbrev a2   : Rv64Reg := .x12
abbrev a3   : Rv64Reg := .x13
abbrev a4   : Rv64Reg := .x14
abbrev a5   : Rv64Reg := .x15
abbrev a6   : Rv64Reg := .x16
abbrev a7   : Rv64Reg := .x17
abbrev t3   : Rv64Reg := .x28
abbrev t4   : Rv64Reg := .x29
abbrev t5   : Rv64Reg := .x30
abbrev t6   : Rv64Reg := .x31

/-- Base 32-bit instruction formats from the RISC-V Unprivileged ISA Manual. -/
inductive Rv64RawInsn where
  | rType (opcode funct3 funct7 : Nat) (rd rs1 rs2 : Rv64Reg)
  | iType (opcode funct3 : Nat) (rd rs1 : Rv64Reg) (imm12 : Nat)
  | sType (opcode funct3 : Nat) (rs1 rs2 : Rv64Reg) (imm12 : Nat)
  | bType (opcode funct3 : Nat) (rs1 rs2 : Rv64Reg) (imm13 : Nat)
  | uType (opcode : Nat) (rd : Rv64Reg) (imm20 : Nat)
  | jType (opcode : Nat) (rd : Rv64Reg) (imm21 : Nat)
  deriving DecidableEq, Repr

/-- Encode a 32-bit RV64GC instruction word into its architectural bit layout. -/
def encodeRv64RawInsn : Rv64RawInsn → Nat
  | .rType op f3 f7 rd rs1 rs2 =>
      (op % 128) +
      (rd.idx * 128) +
      ((f3 % 8) * 4096) +
      (rs1.idx * 32768) +
      (rs2.idx * 1048576) +
      ((f7 % 128) * 33554432)
  | .iType op f3 rd rs1 imm12 =>
      (op % 128) +
      (rd.idx * 128) +
      ((f3 % 8) * 4096) +
      (rs1.idx * 32768) +
      ((imm12 % 4096) * 1048576)
  | .sType op f3 rs1 rs2 imm12 =>
      let imm := imm12 % 4096
      let imm4_0 := imm % 32
      let imm11_5 := imm / 32
      (op % 128) +
      (imm4_0 * 128) +
      ((f3 % 8) * 4096) +
      (rs1.idx * 32768) +
      (rs2.idx * 1048576) +
      (imm11_5 * 33554432)
  | .bType op f3 rs1 rs2 imm13 =>
      let imm := imm13 % 8192
      let b11 := (imm / 2048) % 2
      let b4_1 := (imm / 2) % 16
      let b10_5 := (imm / 32) % 64
      let b12 := (imm / 4096) % 2
      (op % 128) +
      (b11 * 128) +
      (b4_1 * 256) +
      ((f3 % 8) * 4096) +
      (rs1.idx * 32768) +
      (rs2.idx * 1048576) +
      (b10_5 * 33554432) +
      (b12 * 2147483648)
  | .uType op rd imm20 =>
      (op % 128) +
      (rd.idx * 128) +
      ((imm20 % 1048576) * 4096)
  | .jType op rd imm21 =>
      let imm := imm21 % 2097152
      let b19_12 := (imm / 4096) % 256
      let b11 := (imm / 2048) % 2
      let b10_1 := (imm / 2) % 1024
      let b20 := (imm / 1048576) % 2
      (op % 128) +
      (rd.idx * 128) +
      (b19_12 * 4096) +
      (b11 * 1048576) +
      (b10_1 * 2097152) +
      (b20 * 2147483648)

/-- Serialize a 32-bit instruction word into 4 little-endian bytes (`WriteWord32`). -/
def leBytes32 (w : Nat) : List Nat :=
  [ w % 256,
    (w / 256) % 256,
    (w / 65536) % 256,
    (w / 16777216) % 256 ]

/-- Reconstruct a 32-bit word from 4 little-endian bytes (`ReadWord32`). -/
def readU32LE (b0 b1 b2 b3 : Nat) : Nat :=
  (b0 % 256) + 256 * (b1 % 256) + 65536 * (b2 % 256) + 16777216 * (b3 % 256)

/-- Universal little-endian 32-bit byte round-trip (`ReadWord32 (WriteWord32 w) = w`). -/
theorem readU32LE_leBytes32 (w : Nat) (hw : w < 4294967296) :
    readU32LE (w % 256) ((w / 256) % 256)
      ((w / 65536) % 256) ((w / 16777216) % 256) = w := by
  unfold readU32LE
  omega

/-- Every encoded RV64GC instruction word fits in an unsigned 32-bit integer. -/
theorem encodeRv64RawInsn_lt_2pow32 (insn : Rv64RawInsn) :
    encodeRv64RawInsn insn < 4294967296 := by
  cases insn with
  | rType op f3 f7 rd rs1 rs2 =>
    have hrd : rd.idx < 32 := by cases rd <;> decide
    have hrs1 : rs1.idx < 32 := by cases rs1 <;> decide
    have hrs2 : rs2.idx < 32 := by cases rs2 <;> decide
    dsimp [encodeRv64RawInsn]
    omega
  | iType op f3 rd rs1 imm12 =>
    have hrd : rd.idx < 32 := by cases rd <;> decide
    have hrs1 : rs1.idx < 32 := by cases rs1 <;> decide
    dsimp [encodeRv64RawInsn]
    omega
  | sType op f3 rs1 rs2 imm12 =>
    have hrs1 : rs1.idx < 32 := by cases rs1 <;> decide
    have hrs2 : rs2.idx < 32 := by cases rs2 <;> decide
    dsimp [encodeRv64RawInsn]
    omega
  | bType op f3 rs1 rs2 imm13 =>
    have hrs1 : rs1.idx < 32 := by cases rs1 <;> decide
    have hrs2 : rs2.idx < 32 := by cases rs2 <;> decide
    dsimp [encodeRv64RawInsn]
    omega
  | uType op rd imm20 =>
    have hrd : rd.idx < 32 := by cases rd <;> decide
    dsimp [encodeRv64RawInsn]
    omega
  | jType op rd imm21 =>
    have hrd : rd.idx < 32 := by cases rd <;> decide
    dsimp [encodeRv64RawInsn]
    omega

/-- Universal round-trip from any `Rv64RawInsn` through `leBytes32` and `readU32LE`. -/
theorem readU32LE_encodeRv64RawInsn (insn : Rv64RawInsn) :
    let w := encodeRv64RawInsn insn
    readU32LE (w % 256) ((w / 256) % 256)
      ((w / 65536) % 256) ((w / 16777216) % 256) = w :=
  readU32LE_leBytes32 (encodeRv64RawInsn insn) (encodeRv64RawInsn_lt_2pow32 insn)

/-- `fence iorw, iorw` (`opcode = 0x0f`, `funct3 = 0`, `rd = x0`, `rs1 = x0`,
`fm = 0`, `pred = 0xf`, `succ = 0xf`, so `imm12 = 0x0ff`) encodes to `0x0ff0000f`
with little-endian bytes `[0x0f, 0x00, 0xf0, 0x0f]`. -/
theorem fence_iorw_encoding :
    encodeRv64RawInsn (.iType 0x0f 0x0 .x0 .x0 0x0ff) = 0x0ff0000f ∧
    leBytes32 (encodeRv64RawInsn (.iType 0x0f 0x0 .x0 .x0 0x0ff)) =
      [0x0f, 0x00, 0xf0, 0x0f] := by
  decide

/-- Negative control: omitting the `pred=0xf, succ=0xf` mask (`imm12 = 0`)
produces `0x0000000f` with empty predecessor/successor ordering sets (`pred = 0`,
`succ = 0`), which differs from `fence iorw, iorw` (`0x0ff0000f`). -/
theorem control_fence_zero_imm_omits_pred_succ :
    let badWord := encodeRv64RawInsn (.iType 0x0f 0x0 .x0 .x0 0x000)
    let goodWord := encodeRv64RawInsn (.iType 0x0f 0x0 .x0 .x0 0x0ff)
    badWord = 0x0000000f ∧
    (badWord / 1048576) % 256 = 0x00 ∧
    (goodWord / 1048576) % 256 = 0xff ∧
    badWord ≠ goodWord := by
  decide

/-- `ecall` (`opcode = 0x73`, `funct3 = 0`, `rd = x0`, `rs1 = x0`, `imm12 = 0`)
encodes to `0x00000073` with little-endian bytes `[0x73, 0x00, 0x00, 0x00]`. -/
theorem ecall_encoding :
    encodeRv64RawInsn (.iType 0x73 0x0 .x0 .x0 0x000) = 0x00000073 ∧
    leBytes32 (encodeRv64RawInsn (.iType 0x73 0x0 .x0 .x0 0x000)) =
      [0x73, 0x00, 0x00, 0x00] := by
  decide

-- ============================================================================
-- 2. 12-Bit Signed Immediate Overflow & `lui` + `addi` Compensation
-- ============================================================================

/-- Architectural 12-bit two's-complement sign extension performed by RV64I
I-type (`addi`, `ld`, `lw`, `lbu`, `jalr`) and S-type (`sd`, `sw`, `sb`)
instructions: bit 11 (`2048`) is the sign bit, mapping `[0, 2047]` to
`[0, 2047]` and `[2048, 4095]` to `[-2048, -1]`. -/
def signExtend12 (imm12 : Nat) : Int :=
  if imm12 % 4096 >= 2048 then ((imm12 % 4096 : Nat) : Int) - 4096
  else ((imm12 % 4096 : Nat) : Int)

/-- Stack frame byte size for `slotCount` 8-byte spill slots plus 16 bytes for
saved `ra` (`[s0 - 8]`) and `s0` (`[s0 - 16]`), rounded up to a 16-byte ABI
boundary. -/
def rv64FrameBytes (slotCount : Nat) : Nat :=
  ((16 + 8 * (slotCount + 1) + 15) / 16) * 16

/-- Negative control: when a stack frame expands beyond `2,047` bytes (for
example, `2,720` bytes = `0xaa0` for a large function frame), encoding
`frameBytes` or `-frameBytes` directly into a 12-bit I-type/S-type immediate
truncates modulo `4096` and sign-extends bit 11 (`0x800`), turning `+2720` into
`-1376` and `-2720` (`(-2720) mod 4096 = 1376 = 0x560`) into `+1376`. In a
prologue `addi sp, sp, -2720`, this advances `sp` upward by `+1376` bytes into
the caller's frame instead of allocating stack space. -/
theorem control_large_frame_2720_direct_imm12_sign_flips :
    signExtend12 2047 = 2047 ∧
    signExtend12 2048 = -2048 ∧
    signExtend12 2720 = -1376 ∧
    signExtend12 ((4096 - (2720 % 4096)) % 4096) = 1376 := by
  decide

/-- Naive uncompensated splitting (`hi20_naive = imm / 4096`, `lo12 = imm % 4096`)
without adding `0x800` (`2048`) before shifting fails by `-4096` whenever bit 11
of `imm` is set (`imm % 4096 >= 2048`). -/
theorem control_naive_uncompensated_split_fails_when_bit11_set (imm : Nat)
    (hbit11 : imm % 4096 >= 2048) :
    ((imm / 4096 : Nat) : Int) * 4096 + signExtend12 (imm % 4096) =
      (imm : Int) - 4096 := by
  unfold signExtend12
  omega

/-- Compensated upper-20 / lower-12 decomposition for `lui` + `addi`:
adding `2048` (`0x800`) before dividing by `4096` (`>> 12`) increments `hi20`
by `1` (`+4096` after `<< 12`) if and only if `imm % 4096 >= 2048`, which
exactly cancels the `-4096` subtracted when `addi` sign-extends bit 11 of
`lo12 = imm % 4096`. -/
def hi20CompensatedNat (imm : Nat) : Nat :=
  (imm + 2048) / 4096

def lo12FieldNat (imm : Nat) : Nat :=
  imm % 4096

/-- Universal correctness of `lui` + `addi` sign-extension compensation for all
non-negative byte offsets `imm : Nat`:
`(hi20CompensatedNat imm << 12) + signExtend12 (lo12FieldNat imm) = imm`. -/
theorem lui_addi_compensated_exact (imm : Nat) :
    ((hi20CompensatedNat imm : Int) * 4096) + signExtend12 (lo12FieldNat imm) =
      (imm : Int) := by
  unfold hi20CompensatedNat lo12FieldNat signExtend12
  omega

/-- Signed 32-bit offset decomposition (`imm : Int` in `[-2147483648, 2147483647]`):
`hi20 = Int.fdiv (imm + 2048) 4096` and `lo12 = Int.emod imm 4096` (encoded in
12 bits), where `hi20 * 4096 + signExtend12 (Int.toNat lo12) = imm`. -/
def hi20Signed (imm : Int) : Int :=
  (imm + 2048) / 4096

def lo12Signed (imm : Int) : Nat :=
  Int.toNat (imm % 4096)

/-- Universal correctness of signed `lui` + `addi` offset materialization across
all signed integers `imm : Int` (covering both positive and negative stack-frame
displacements such as `+2720` and `-2720`). -/
theorem lui_addi_signed_exact (imm : Int) :
    hi20Signed imm * 4096 + signExtend12 (lo12Signed imm) = imm := by
  unfold hi20Signed lo12Signed signExtend12
  omega

/-- Concrete verification of the boundary offsets `2047`, `2048`, `2720`,
`-2048`, `-2049`, and `-2720` used in large stack-frame prologues, epilogues,
and slot accesses. -/
theorem large_frame_boundary_offsets_verified :
    (hi20Signed 2047 = 0 ∧ signExtend12 (lo12Signed 2047) = 2047) ∧
    (hi20Signed 2048 = 1 ∧ signExtend12 (lo12Signed 2048) = -2048 ∧
      1 * 4096 + (-2048) = (2048 : Int)) ∧
    (hi20Signed 2720 = 1 ∧ signExtend12 (lo12Signed 2720) = -1376 ∧
      1 * 4096 + (-1376) = (2720 : Int)) ∧
    (hi20Signed (-2048) = 0 ∧ signExtend12 (lo12Signed (-2048)) = -2048) ∧
    (hi20Signed (-2049) = -1 ∧ signExtend12 (lo12Signed (-2049)) = 2047 ∧
      (-1) * 4096 + 2047 = (-2049 : Int)) ∧
    (hi20Signed (-2720) = -1 ∧ signExtend12 (lo12Signed (-2720)) = 1376 ∧
      (-1) * 4096 + 1376 = (-2720 : Int)) := by
  decide

/-- Scratch registers `t3` (`x28`) and `t4` (`x29`) used for large stack-frame
address materialization (`lui t4, hi20; addi t4, t4, lo12; add t4, sp, t4`) are
strictly disjoint from the frame/stack/return/thread pointers (`s0`, `sp`, `ra`,
`gp`, `tp`), primary expression temporaries (`t0`, `t1`, `t2`), and all LP64D
argument/return registers (`a0`..`a7`). -/
theorem scratch_t3_t4_disjoint_from_abi_and_frame_regs :
    let liveRegs : List Rv64Reg :=
      [zero, ra, sp, gp, tp, t0, t1, t2, s0, s1, a0, a1, a2, a3, a4, a5, a6, a7]
    t3 ≠ t4 ∧
    (∀ r ∈ liveRegs, r ≠ t3 ∧ r ≠ t4) := by
  decide

-- ============================================================================
-- 3. Conditional `B`-Type vs. `J`-Type Layout & Cascading Branch Relaxation
-- ============================================================================

/-- Reconstruct a 13-bit even branch offset from its four scrambled B-type
subfields `imm[11]`, `imm[4:1]`, `imm[10:5]`, and `imm[12]`. -/
def reconstructBImm13 (imm13 : Nat) : Nat :=
  let imm := imm13 % 8192
  let b11 := (imm / 2048) % 2
  let b4_1 := (imm / 2) % 16
  let b10_5 := (imm / 32) % 64
  let b12 := (imm / 4096) % 2
  b4_1 * 2 + b10_5 * 32 + b11 * 2048 + b12 * 4096

/-- Universal round-trip of B-type bit scrambling (`imm[12|10:5|4:1|11]`) for
every even 13-bit byte offset `imm13 < 8192` (`[-4096, 4094]` in two's
complement). -/
theorem reconstructBImm13_roundtrip (imm13 : Nat)
    (hbound : imm13 < 8192) (heven : imm13 % 2 = 0) :
    reconstructBImm13 imm13 = imm13 := by
  dsimp [reconstructBImm13]
  omega

/-- Extract the 13-bit even immediate field `imm13` (`imm[12:0]` with `imm[0]=0`)
from an encoded `B`-type instruction word. -/
def decodeBImm13Unsigned (word : Nat) : Nat :=
  ((word / 256) % 16) * 2 +
  ((word / 33554432) % 64) * 32 +
  ((word / 128) % 2) * 2048 +
  ((word / 2147483648) % 2) * 4096

/-- Reconstruct a 21-bit even jump offset from its four scrambled J-type
subfields `imm[19:12]`, `imm[11]`, `imm[10:1]`, and `imm[20]`. -/
def reconstructJImm21 (imm21 : Nat) : Nat :=
  let imm := imm21 % 2097152
  let b19_12 := (imm / 4096) % 256
  let b11 := (imm / 2048) % 2
  let b10_1 := (imm / 2) % 1024
  let b20 := (imm / 1048576) % 2
  b10_1 * 2 + b11 * 2048 + b19_12 * 4096 + b20 * 1048576

/-- Universal round-trip of J-type bit scrambling (`imm[20|10:1|11|19:12]`) for
every even 21-bit byte offset `imm21 < 2097152` (`[-1048576, 1048574]` in two's
complement). -/
theorem reconstructJImm21_roundtrip (imm21 : Nat)
    (hbound : imm21 < 2097152) (heven : imm21 % 2 = 0) :
    reconstructJImm21 imm21 = imm21 := by
  dsimp [reconstructJImm21]
  omega

/-- Extract the 21-bit even immediate field `imm21` (`imm[20:0]` with `imm[0]=0`)
from an encoded `J`-type (`jal`) instruction word. -/
def decodeJImm21Unsigned (word : Nat) : Nat :=
  ((word / 2097152) % 1024) * 2 +
  ((word / 1048576) % 2) * 2048 +
  ((word / 4096) % 256) * 4096 +
  ((word / 2147483648) % 2) * 1048576

/-- Concrete verification of B-type (`±4 KiB`) and J-type (`±1 MiB`) full-word
encoding and extraction at the positive and negative architectural range limits
and relaxation trampoline offsets (`+8`, `+12`, `+4094`, `-4096`, `+1048574`,
`-1048576`). -/
theorem bType_and_jType_boundary_encodings_verified :
    decodeBImm13Unsigned (encodeRv64RawInsn (.bType 0x63 0x1 a0 a1 8)) = 8 ∧
    decodeBImm13Unsigned (encodeRv64RawInsn (.bType 0x63 0x1 a0 a1 12)) = 12 ∧
    decodeBImm13Unsigned (encodeRv64RawInsn (.bType 0x63 0x0 a0 a1 4094)) = 4094 ∧
    decodeBImm13Unsigned (encodeRv64RawInsn (.bType 0x63 0x0 a0 a1 4096)) = 4096 ∧
    decodeJImm21Unsigned (encodeRv64RawInsn (.jType 0x6f zero 4096)) = 4096 ∧
    decodeJImm21Unsigned (encodeRv64RawInsn (.jType 0x6f zero 1048574)) = 1048574 ∧
    decodeJImm21Unsigned (encodeRv64RawInsn (.jType 0x6f zero 1048576)) = 1048576 := by
  decide

/-- Invert an RV64I conditional branch `funct3` code by flipping bit 0:
`0 (beq) <-> 1 (bne)`, `4 (blt) <-> 5 (bge)`, `6 (bltu) <-> 7 (bgeu)`. -/
def invertBranchFunct3 (f3 : Nat) : Nat :=
  if f3 % 2 == 0 then f3 + 1 else f3 - 1

/-- Branch condition inversion is an involution on all valid RV64I branch
`funct3` codes (`0, 1, 4, 5, 6, 7`). -/
theorem invertBranchFunct3_involutive (f3 : Nat)
    (h : f3 = 0 ∨ f3 = 1 ∨ f3 = 4 ∨ f3 = 5 ∨ f3 = 6 ∨ f3 = 7) :
    invertBranchFunct3 (invertBranchFunct3 f3) = f3 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Semantic equivalence of a direct conditional branch `if cond then target
else pc + 4` and the relaxed 8-byte (`B_inv_cond +8; jal x0, target`) or
12-byte (`B_inv_cond +12; auipc t6, hi20; jalr x0, lo12(t6)`) sequence:
when `!cond`, the inverted branch jumps to `pc + 8` (or `pc + 12`), which is the
fallthrough instruction immediately after the relaxed sequence; when `cond`, the
inverted branch falls through into the unconditional jump to `target`. -/
theorem relaxed_branch_control_flow_equiv (cond : Bool) (target fallthrough : Nat) :
    (if !cond then fallthrough else target) =
      (if cond then target else fallthrough) := by
  cases cond <;> rfl

/-- Model of two nested conditional branches `(outerSpan, innerSpan)` where the
outer branch spans across the inner branch. Relaxing a branch that exceeds the
`B`-type limit (`4094` bytes) replaces the 4-byte `B`-type instruction with an
8-byte `B_inv +8; jal` sequence, adding `+4` bytes to any outer branch that
spans across it. -/
structure NestedBranchPair where
  outerBaseBytes : Nat
  innerBaseBytes : Nat
  outerRelaxed : Bool
  innerRelaxed : Bool
  deriving DecidableEq, Repr

/-- Effective byte span of the inner branch. -/
def NestedBranchPair.innerDisplacement (p : NestedBranchPair) : Nat :=
  p.innerBaseBytes

/-- Effective byte span of the outer branch: if the inner branch inside its span
has been relaxed from 4 bytes to 8 bytes (`+4` bytes), the outer branch's target
shifts by `+4` bytes. -/
def NestedBranchPair.outerDisplacement (p : NestedBranchPair) : Nat :=
  p.outerBaseBytes + (if p.innerRelaxed then 4 else 0)

/-- Layout verification predicate: every unrelaxed `B`-type branch must have a
displacement `<= 4094` bytes (`1023` instructions). -/
def NestedBranchPair.layoutValid (p : NestedBranchPair) : Bool :=
  (p.innerRelaxed || decide (p.innerDisplacement <= 4094)) &&
  (p.outerRelaxed || decide (p.outerDisplacement <= 4094))

/-- One relaxation pass: marks any branch whose current displacement exceeds
`4094` bytes as relaxed. -/
def relaxStep (p : NestedBranchPair) : NestedBranchPair :=
  { p with
    innerRelaxed := p.innerRelaxed || decide (p.innerDisplacement > 4094)
    outerRelaxed := p.outerRelaxed || decide (p.outerDisplacement > 4094) }

/-- Multi-round fixed-point branch relaxation. -/
def relaxFixpoint (fuel : Nat) (p : NestedBranchPair) : NestedBranchPair :=
  match fuel with
  | 0 => p
  | fuel' + 1 =>
      let p' := relaxStep p
      if p' == p then p else relaxFixpoint fuel' p'

/-- Cascading branch relaxation witness: when `outerBaseBytes = 4092` (`<= 4094`,
initially within `B`-type range) and `innerBaseBytes = 4096` (`> 4094`,
initially out of `B`-type range), a single relaxation pass (`relaxStep`) relaxes
only the inner branch. That `+4`-byte expansion pushes `outerDisplacement` from
`4092` to `4096 > 4094`, so single-pass relaxation fails `layoutValid`, whereas
the multi-round fixed-point loop (`relaxFixpoint`) relaxes the outer branch in
round 2 and satisfies `layoutValid`. -/
theorem cascading_relaxation_single_pass_fails_and_fixpoint_succeeds :
    let init : NestedBranchPair :=
      { outerBaseBytes := 4092
        innerBaseBytes := 4096
        outerRelaxed := false
        innerRelaxed := false }
    let pass1 := relaxStep init
    let fixed := relaxFixpoint 4 init
    pass1.innerRelaxed = true ∧
    pass1.outerRelaxed = false ∧
    pass1.outerDisplacement = 4096 ∧
    pass1.layoutValid = false ∧
    fixed.innerRelaxed = true ∧
    fixed.outerRelaxed = true ∧
    fixed.layoutValid = true := by
  decide

-- ============================================================================
-- 4. ELF64 `.symtab` Ordering, Indirect `PCREL_LO12`, `LP64D`, Vtables & Syscalls
-- ============================================================================

/-- ELF64 symbol binding class (`st_info >> 4`): `0 = STB_LOCAL`, `1 = STB_GLOBAL`,
`2 = STB_WEAK`. -/
inductive ElfSymBinding where
  | local_  -- STB_LOCAL  = 0
  | global_ -- STB_GLOBAL = 1
  | weak_   -- STB_WEAK   = 2
  deriving DecidableEq, Repr

def ElfSymBinding.isLocal : ElfSymBinding → Bool
  | .local_ => true
  | .global_ | .weak_ => false

/-- ELF64 `.symtab` ordering and `sh_info` invariant enforced by `lld`:
1. Symbol `0` (`STN_UNDEF`) is local (`0 < sh_info`).
2. Every symbol at index `i < sh_info` has `STB_LOCAL` binding.
3. Every symbol at index `i >= sh_info` has non-local (`STB_GLOBAL` or
   `STB_WEAK`) binding. -/
def checkSymtabOrdering (syms : List ElfSymBinding) (shInfo : Nat) : Bool :=
  decide (0 < shInfo ∧ shInfo <= syms.length) &&
  (syms.take shInfo).all ElfSymBinding.isLocal &&
  (syms.drop shInfo).all (fun b => !b.isLocal)

/-- Positive `.symtab` layout vs. two negative controls rejected by `rust-lld`:
1. `validSymtab`: `[STN_UNDEF (local), .text (local), .Lpcrel_hi0 (local),
   _start (global)]` with `sh_info = 3` is accepted.
2. `badShInfo`: same symbol list with `sh_info = 1` (failing to count local
   section/label symbols) is rejected.
3. `localAfterGlobal`: placing `.Lpcrel_hi0 (local)` after `_start (global)` is
   rejected (`local symbol in global part of symbol table`). -/
theorem symtab_local_before_global_and_sh_info_controls :
    let validSyms : List ElfSymBinding := [.local_, .local_, .local_, .global_]
    let localAfterGlobal : List ElfSymBinding := [.local_, .local_, .global_, .local_]
    checkSymtabOrdering validSyms 3 = true ∧
    checkSymtabOrdering validSyms 1 = false ∧
    checkSymtabOrdering localAfterGlobal 2 = false ∧
    checkSymtabOrdering localAfterGlobal 3 = false := by
  decide

/-- Address calculation for an `auipc rd, %pcrel_hi(S)` instruction at PC
`pcAuipc` paired with an `addi/ld/sd` instruction at `pcLo = pcAuipc + 4`:
`auipc` writes `pcAuipc + hi20Signed (S - pcAuipc) * 4096` to `rd`.
When `R_RISCV_PCREL_LO12_I` / `R_RISCV_PCREL_LO12_S` is indirect—referencing the
local symbol at `pcAuipc` so the linker computes `lo12Signed (S - pcAuipc)`—the
sum `rd + signExtend12 lo12` equals `S` for every target address `S` and every
`pcAuipc`. -/
theorem pcrel_lo12_indirect_via_auipc_exact (targetAddr pcAuipc : Int) :
    let deltaAuipc := targetAddr - pcAuipc
    let auipcVal := pcAuipc + hi20Signed deltaAuipc * 4096
    let lo12Indirect := signExtend12 (lo12Signed deltaAuipc)
    auipcVal + lo12Indirect = targetAddr := by
  dsimp only
  have h := lui_addi_signed_exact (targetAddr - pcAuipc)
  omega

/-- Negative control: if `R_RISCV_PCREL_LO12_I` were computed relative to its
own PC `pcLo = pcAuipc + 4` (`deltaLo = targetAddr - (pcAuipc + 4)`) instead of
indirectly referencing `pcAuipc`, the materialized address would miss
`targetAddr` (for `targetAddr = 0x11020`, `pcAuipc = 0x10000`, it lands at
`0x1101c = targetAddr - 4`). -/
theorem control_pcrel_lo12_direct_pc_off_by_four :
    let targetAddr : Int := 0x11020
    let pcAuipc : Int := 0x10000
    let pcLo : Int := pcAuipc + 4
    let auipcVal := pcAuipc + hi20Signed (targetAddr - pcAuipc) * 4096
    let indirectAddr := auipcVal + signExtend12 (lo12Signed (targetAddr - pcAuipc))
    let wrongDirectAddr := auipcVal + signExtend12 (lo12Signed (targetAddr - pcLo))
    indirectAddr = targetAddr ∧
    wrongDirectAddr = targetAddr - 4 ∧
    wrongDirectAddr ≠ targetAddr := by
  decide

/-- RISC-V LP64D aggregate passing/return classification by byte size:
- `0` bytes (ZST): no register transfer (`zst`).
- `1..8` bytes: single 64-bit register `a0` (`directScalar`).
- `9..16` bytes: register pair `(a0, a1)` (`scalarPair`, e.g., `&[T]`, `&str`,
  `&dyn Trait` fat pointers, `u128`/`i128`, 2-word `Result`/`Option`).
- `> 16` bytes: caller-allocated buffer pointer passed in `a0` (`indirectSret`). -/
inductive Lp64dPassingMode where
  | zst
  | directScalar
  | scalarPair
  | indirectSret
  deriving DecidableEq, Repr

def classifyLp64dSize (sizeBytes : Nat) : Lp64dPassingMode :=
  if sizeBytes == 0 then .zst
  else if sizeBytes <= 8 then .directScalar
  else if sizeBytes <= 16 then .scalarPair
  else .indirectSret

theorem lp64d_classification_boundaries :
    classifyLp64dSize 0 = .zst ∧
    classifyLp64dSize 8 = .directScalar ∧
    classifyLp64dSize 16 = .scalarPair ∧
    classifyLp64dSize 24 = .indirectSret := by
  decide

/-- 3-word trait-object vtable header layout in `.data.rel.ro`:
`[drop_in_place_fn_ptr (offset 0), size_bytes (offset 8), align_bytes (offset 16),
 method_0_fn_ptr (offset 24), method_1_fn_ptr (offset 32), ...]`. -/
def vtableDropOffset : Nat := 0
def vtableSizeOffset : Nat := 8
def vtableAlignOffset : Nat := 16
def vtableMethodOffset (methodIdx : Nat) : Nat := (3 + methodIdx) * 8

theorem vtable_three_word_header_offsets :
    vtableDropOffset = 0 ∧
    vtableSizeOffset = 8 ∧
    vtableAlignOffset = 16 ∧
    vtableMethodOffset 0 = 24 ∧
    vtableMethodOffset 1 = 32 := by
  decide

/-- Linux `riscv64` UAPI syscall numbers (`include/uapi/asm-generic/unistd.h`)
invoked via `a7` (`x17`) + `a0`..`a5` (`x10`..`x15`) + `ecall`. -/
def sysRead      : Nat := 63
def sysWrite     : Nat := 64
def sysExit      : Nat := 93
def sysExitGroup : Nat := 94
def sysBrk       : Nat := 214
def sysMmap      : Nat := 222
def sysGetrandom : Nat := 278

/-- Bump-allocator spatial disjointness: two sequential allocations of sizes
`sz1` and `sz2` starting from heap cursor `cur` within `[base, limit)` return
non-overlapping regions `[p1, p1 + sz1)` and `[p2, p2 + sz2)` with
`p1 + sz1 <= p2`. -/
def bumpAlloc (cur limit sz : Nat) : Option (Nat × Nat) :=
  if cur + sz <= limit then some (cur, cur + sz) else none

theorem bumpAlloc_disjoint (cur limit sz1 sz2 p1 cur1 p2 cur2 : Nat)
    (h1 : bumpAlloc cur limit sz1 = some (p1, cur1))
    (h2 : bumpAlloc cur1 limit sz2 = some (p2, cur2)) :
    p1 + sz1 <= p2 ∧ p2 + sz2 <= limit := by
  unfold bumpAlloc at h1 h2
  split at h1 <;> simp at h1
  split at h2 <;> simp at h2
  omega

end Rv64ElfAbiProbe
