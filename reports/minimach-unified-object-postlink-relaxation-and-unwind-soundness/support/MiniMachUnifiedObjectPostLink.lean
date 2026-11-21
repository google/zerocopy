-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Nat.Div.Basic
import Init.Data.Int.Basic

namespace VrustcFormal.F1_4

/-!
# `F1-4`: Unified `MiniMach` Object Encoding, Post-Link ELF64 Relocation &
TLS/GOT Opcode Relaxation, Dynamic `%r11` Probe-Loop CFA, and `.eh_frame_hdr`
Binary-Search Unwind Soundness

## Relation to General Foundations (`leanlib`) and Empirical Ground Truth

General span-dependent assembler branch relaxation and straight-line `sp`-based
unwind tables (`branch-relaxation-fixpoints-and-unwind-table-frame-restoration`,
`google/zerocopy@ece553a0ca`), parallel-move sequentialization and sub-register
lane framing (`parallel-move-sequentialization-and-sub-register-lane-framing`,
`google/zerocopy@a02bab389d`), and codec round-trip laws belong to the general
Lean Results Library (`leanlib`).

This module formalizes the strictly **Rust-compiler-specific** unified
assembler-free `MiniMach` -> ELF64 relocatable object -> post-link PIE machine
byte pipeline grounded in:
1. **`E3-1` Live Sysroot & `GNU ld 2.47` Post-Link Census** (ELF64 x86-64
   TLS/GOT relaxation ABI shared with `rust-lld`): All `30` `rustc`
   `x86_64-unknown-linux-gnu` sysroot `.rlib`s contain `350,943` relocations
   across exactly `10` ELF64 relocation types (`R_X86_64_PC32`, `PLT32`, `32`,
   `64`, `GOTPCREL`, `GOTTPOFF`, `TLSGD`, `REX_GOTPCRELX`, `TLSLD`,
   `DTPOFF32`), plus `R_X86_64_TPOFF32` in direct Local-Exec objects. Among
   these are **`475` opcode-mutating relaxable relocations** (`198 GOTTPOFF`,
   `178 TLSGD`, `84 REX_GOTPCRELX` in `libprofiler_builtins`, `15 TLSLD` in
   `libstd`). Live `E3-1` linking (`GNU ld 2.47`) rewrites in place:
   - **`TLSGD` -> Local-Exec (`16` B: `8B + 8B -> 9B + 7B`):**
     `66 48 8d 3d 00 00 00 00 ; 66 66 48 e8 00 00 00 00`
     ==> `64 48 8b 04 25 00 00 00 00 ; 48 8d 80 <tpoff32>`
     (`mov %fs:0, %rax; lea tpoff(%rax), %rax`), shifting the internal
     instruction boundary from `+8` to `+9`.
   - **`TLSLD` -> Local-Exec (`19` B: `7B + 5B + 7B -> 12B + 7B`):**
     `48 8d 3d 00 00 00 00 ; e8 00 00 00 00 ; 48 8b 80 00 00 00 00`
     ==> `66 66 66 64 48 8b 04 25 00 00 00 00 ; 48 8b 80 <tpoff32>`
     (`data16×3 mov %fs:0, %rax; mov tpoff(%rax), %rax`, observed verbatim in
     `E3-1` for `MY_TLS`, plus `48 8d 80` `lea` for address-of `TLSLD`).
   - **`GOTTPOFF` -> Local-Exec (`7` B):**
     `48 8b 05 00 00 00 00` (`mov gotTpOff(%rip), %rax`)
     ==> `48 c7 c0 <tpoff32>` (`mov $tpoff32, %rax`).
   - **`REX_GOTPCRELX` -> RIP-Relative `lea` (`7` B, x86-64 psABI Table B.2):**
     `48 8b 05 00 00 00 00` (`mov got(%rip), %rax`)
     ==> `48 8d 05 <pc32>` (`lea sym(%rip), %rax`).
   - **`0xCC` (`int3`) inter-function alignment padding** and signed negative
     PC-relative displacements (e.g., `E3-1` `lea -0xd9(%rip)` `27 ff ff ff`).
2. **`Crucible 3` (`google/zerocopy@b31e6312ed`, Table E1):** Mechanizes the
   two-phase `>= 9`-page **`%r11` inline probe loop** (`push` saved offset ->
   `DW_CFA_def_cfa_register: reg11` -> fixed `4096`-byte `sub` + explicit
   `movq $0, (%rsp)` guard-page touch + `cmp %r11, %rsp; jne` loop exit ->
   post-loop `sub $tailBytes, %rsp`), plus post-link `.eh_frame` FDE PC-range
   relocation and genuine `O(log n)` sorted `.eh_frame_hdr` binary search.

## Honest Scope & Explicit Non-Claims

1. **Abstract `x86-64` Machine Byte & Relocation Model:** Models genuine
   `x86-64` encodings and individual instruction decoding for the verified
   `MiniMach` subset (`movImm32`, `movImm16`, `movReg` with active `WriteMode`,
   `callSym`, `leaRipSym`, `loadGotRelaxable`, `loadGotStrict`, `tlsGdAddr`,
   `tlsLdAddr`, `tlsLdLoad`, `tlsGotTpOff`, `ret`, and trailing `0xCC` padding)
   rather than the full `x86-64` Sail ISA specification; `callSym` validates
   exact `rel32` displacement encoding while abstracting callee side effects as
   a straight-line stub.
2. **Static PIE / Local-Exec Relaxation Scope:** `validateLinkedBytes` models
   `x86-64` ELF64 PIE linking where `TLSGD` and `TLSLD` relax to Local-Exec
   while `REX_GOTPCRELX` and `GOTTPOFF` admit both relaxed and unrelaxed forms
   and `GOTPCREL` forbids relaxation; it does NOT model dynamic `ld-linux.so`
   `R_X86_64_DTPMOD64` / `__tls_get_addr` lazy TLSDESC execution, AArch64
   `ADRP`/`ADD` relaxation, PE/COFF, or Mach-O compact unwind.
3. **Anneal `TrustedBoundary.lean` Discipline:** Closed locked `Init.*` imports
   only, prefix `Nat.pow`/`Nat.div`/`Nat.mod`, `Int.negSucc` (zero unary `-`,
   `^`, `/`, `%`), inductive predicates (zero `._unsafe_rec`), `noncomputable`
   on recursive value defs, constructive axioms only (`0` `Classical.choice`,
   `0` `omega`, `0` `bv_decide`, `0` `native_decide`).
-/

/-! ## Part I: Unified `MiniMach` IR, Real `x86-64` Registers & `WriteMode` -/

/-- Architectural 64-bit GPR subset (low 7 GPRs plus `%r11` for probe loops). -/
inductive Gpr where
  | rax
  | rcx
  | rdx
  | rdi
  | rsi
  | rsp
  | rbp
  | r11

/-- Sub-register write semantics matching `Crucible 3` & `leanlib` `a02bab389d`:
`full64` overwrites all 64 bits; `zeroExt32` zeroes `[63:32]`;
`lo16PreserveUpper48` writes `[15:0]` while preserving `[63:16]`. -/
inductive WriteMode where
  | full64
  | zeroExt32
  | lo16PreserveUpper48

/-- All `10` ELF64 `x86-64` relocation kinds observed across the `30` `rustc`
sysroot `.rlib`s (`E3-1`: `350,943` relocations) plus `R_X86_64_TPOFF32`. -/
inductive Elf64RelocKind where
  | r_pc32
  | r_plt32
  | r_gotpcrel
  | r_rex_gotpcrelx
  | r_tlsgd
  | r_tlsld
  | r_dtpoff32
  | r_gottpoff
  | r_64
  | r_32
  | r_tpoff32

/-- Symbol identifier in a relocatable object or linked executable image. -/
abbrev SymId := Nat

/-- Unified `MiniMach` instruction AST (post-`RegAllocCert`, pre-byte-encoding). -/
inductive MiniMachOp where
  /-- `movq $imm32, %r64` (sign-extended if `isFull64 = true`) or
      `movl $imm32, %r32` (zero-extended `[63:32]` if `isFull64 = false`). -/
  | movImm32 (dst : Gpr) (isFull64 : Bool) (imm : BitVec 32)
  /-- `movw $imm16, %r16` (writes `[15:0]`, preserves upper 48 bits `[63:16]`). -/
  | movImm16 (dst : Gpr) (imm : BitVec 16)
  /-- Register-to-register move (`movq`, `movl`, or `movw`) with `WriteMode`. -/
  | movReg (dst src : Gpr) (mode : WriteMode)
  /-- Direct PC-relative call (`e8 00 00 00 00` + `R_X86_64_PLT32`). -/
  | callSym (sym : SymId)
  /-- RIP-relative address load (`48 8d 05 00 00 00 00` + `R_X86_64_PC32`). -/
  | leaRipSym (sym : SymId)
  /-- Relaxable GOT pointer load (`48 8b 05 00 00 00 00` + `REX_GOTPCRELX`). -/
  | loadGotRelaxable (sym : SymId)
  /-- Non-relaxable GOT pointer load (`48 8b 05 00 00 00 00` + `GOTPCREL`). -/
  | loadGotStrict (sym : SymId)
  /-- 16-byte `TLSGD` address sequence (`8B+8B` -> `9B+7B` Local-Exec). -/
  | tlsGdAddr (sym : SymId)
  /-- 19-byte `TLSLD` + `DTPOFF32` address sequence (`48 8d 80`, `lea`). -/
  | tlsLdAddr (sym : SymId)
  /-- 19-byte `TLSLD` + `DTPOFF32` load sequence (`48 8b 80`, live `E3-1` `mov`). -/
  | tlsLdLoad (sym : SymId)
  /-- 7-byte `GOTTPOFF` TLS offset load (`48 8b 05` -> `48 c7 c0` Local-Exec). -/
  | tlsGotTpOff (sym : SymId)
  /-- Return (`c3`). -/
  | ret

/-- ELF64 relocation entry attached to a pre-link `.o` byte stream. -/
structure Elf64Reloc where
  offset : Nat
  kind : Elf64RelocKind
  sym : SymId
  addend : Int

/-- Pre-link relocatable object produced directly by `MiniMach` (zero `llvm-mc`). -/
structure RelocObject where
  sym : SymId
  code : List (BitVec 8)
  relocs : List Elf64Reloc

/-! ## Part II: Little-Endian Codecs, Real `x86-64` ModRM/REX, & `encodeFn` -/

noncomputable def byteOfNat (n : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (Nat.mod n 256)

noncomputable def le16Bytes (w : BitVec 16) : List (BitVec 8) :=
  let n := w.toNat
  [ byteOfNat n, byteOfNat (Nat.div n 256) ]

noncomputable def decodeLe16 : List (BitVec 8) → Option (BitVec 16)
  | [b0, b1] => some (BitVec.ofNat 16 (b0.toNat + b1.toNat * 256))
  | _ => none

noncomputable def le32Bytes (w : BitVec 32) : List (BitVec 8) :=
  let n := w.toNat
  [ byteOfNat n,
    byteOfNat (Nat.div n 256),
    byteOfNat (Nat.div n 65536),
    byteOfNat (Nat.div n 16777216) ]

noncomputable def decodeLe32 : List (BitVec 8) → Option (BitVec 32)
  | [b0, b1, b2, b3] =>
    some (BitVec.ofNat 32
      (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216))
  | _ => none

/-- Low 3 bits of architectural `x86-64` GPR encoding (`r11 = 8 + 3`). -/
noncomputable def gprLow3 : Gpr → Nat
  | .rax => 0
  | .rcx => 1
  | .rdx => 2
  | .rsp => 4
  | .rbp => 5
  | .rsi => 6
  | .rdi => 7
  | .r11 => 3

/-- REX extension bit (`true` iff register is in `r8..r15`, here `.r11`). -/
noncomputable def gprRexBit : Gpr → Bool
  | .r11 => true
  | _ => false

/-- Inverse decoder from `(rexBit, low3)` to architectural `Gpr`. -/
noncomputable def decodeGpr (rexBit : Bool) (low3 : Nat) : Option Gpr :=
  if rexBit then
    if Nat.beq low3 3 then some .r11 else none
  else
    if Nat.beq low3 0 then some .rax
    else if Nat.beq low3 1 then some .rcx
    else if Nat.beq low3 2 then some .rdx
    else if Nat.beq low3 4 then some .rsp
    else if Nat.beq low3 5 then some .rbp
    else if Nat.beq low3 6 then some .rsi
    else if Nat.beq low3 7 then some .rdi
    else none

/-- Real `x86-64` REX prefix byte `0x40 | 8*W | 4*R | B`. -/
noncomputable def rexByte (w r b : Bool) : BitVec 8 :=
  BitVec.ofNat 8 (0x40 + (if w then 8 else 0) + (if r then 4 else 0) + (if b then 1 else 0))

/-- Real `x86-64` register-direct ModRM byte `0xC0 | (reg << 3) | rm`. -/
noncomputable def modrmRegReg (regField rmField : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (0xC0 + regField * 8 + rmField)

/-- Real `x86-64` byte-exact encoding of a single `MiniMachOp` at section
offset `pc`, returning `(bytes, relocs)`. Uses `Int.negSucc 3` for `-4` to
comply strictly with Anneal `TrustedBoundary.lean`. -/
noncomputable def encodeOneOp (pc : Nat) : MiniMachOp → List (BitVec 8) × List Elf64Reloc
  | .movImm32 dst true imm =>
    -- `movq $imm32, %r64`: `48/49 C7 C0+lo3 imm32` (7 B, sign-extends imm32)
    ([rexByte true false (gprRexBit dst), BitVec.ofNat 8 0xC7,
      modrmRegReg 0 (gprLow3 dst)] ++ le32Bytes imm, [])
  | .movImm32 dst false imm =>
    -- `movl $imm32, %r32`: `B8+lo3 imm32` (5 B) or `41 BB imm32` (6 B for r11d)
    if gprRexBit dst then
      ([BitVec.ofNat 8 0x41, BitVec.ofNat 8 (0xB8 + gprLow3 dst)] ++ le32Bytes imm, [])
    else
      ([BitVec.ofNat 8 (0xB8 + gprLow3 dst)] ++ le32Bytes imm, [])
  | .movImm16 dst imm =>
    -- `movw $imm16, %r16`: `66 B8+lo3 imm16` (4 B) or `66 41 BB imm16` (5 B)
    if gprRexBit dst then
      ([BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x41,
        BitVec.ofNat 8 (0xB8 + gprLow3 dst)] ++ le16Bytes imm, [])
    else
      ([BitVec.ofNat 8 0x66, BitVec.ofNat 8 (0xB8 + gprLow3 dst)] ++ le16Bytes imm, [])
  | .movReg dst src .full64 =>
    -- `movq %src, %dst`: `REX.W 89 ModRM(src, dst)` (3 B)
    ([rexByte true (gprRexBit src) (gprRexBit dst), BitVec.ofNat 8 0x89,
      modrmRegReg (gprLow3 src) (gprLow3 dst)], [])
  | .movReg dst src .zeroExt32 =>
    -- `movl %src32, %dst32`: `[REX] 89 ModRM(src, dst)` (2 B or 3 B)
    if gprRexBit src || gprRexBit dst then
      ([rexByte false (gprRexBit src) (gprRexBit dst), BitVec.ofNat 8 0x89,
        modrmRegReg (gprLow3 src) (gprLow3 dst)], [])
    else
      ([BitVec.ofNat 8 0x89, modrmRegReg (gprLow3 src) (gprLow3 dst)], [])
  | .movReg dst src .lo16PreserveUpper48 =>
    -- `movw %src16, %dst16`: `66 [REX] 89 ModRM(src, dst)` (3 B or 4 B)
    if gprRexBit src || gprRexBit dst then
      ([BitVec.ofNat 8 0x66, rexByte false (gprRexBit src) (gprRexBit dst),
        BitVec.ofNat 8 0x89, modrmRegReg (gprLow3 src) (gprLow3 dst)], [])
    else
      ([BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x89,
        modrmRegReg (gprLow3 src) (gprLow3 dst)], [])
  | .callSym s =>
    ([BitVec.ofNat 8 0xE8, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0],
     [{ offset := pc + 1, kind := .r_plt32, sym := s, addend := Int.negSucc 3 }])
  | .leaRipSym s =>
    ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0],
     [{ offset := pc + 3, kind := .r_pc32, sym := s, addend := Int.negSucc 3 }])
  | .loadGotRelaxable s =>
    ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0],
     [{ offset := pc + 3, kind := .r_rex_gotpcrelx, sym := s, addend := Int.negSucc 3 }])
  | .loadGotStrict s =>
    ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0],
     [{ offset := pc + 3, kind := .r_gotpcrel, sym := s, addend := Int.negSucc 3 }])
  | .tlsGdAddr s =>
    ([BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x3D,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
      BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xE8,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0],
     [{ offset := pc + 4, kind := .r_tlsgd, sym := s, addend := Int.negSucc 3 },
      { offset := pc + 12, kind := .r_plt32, sym := 0, addend := Int.negSucc 3 }])
  | .tlsLdAddr s =>
    -- `TLSLD` + `DTPOFF32` `lea` (`48 8d 80`): 7B + 5B + 7B = 19B
    ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x3D,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
      BitVec.ofNat 8 0xE8,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
      BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0],
     [{ offset := pc + 3, kind := .r_tlsld, sym := s, addend := Int.negSucc 3 },
      { offset := pc + 8, kind := .r_plt32, sym := 0, addend := Int.negSucc 3 },
      { offset := pc + 15, kind := .r_dtpoff32, sym := s, addend := Int.ofNat 0 }])
  | .tlsLdLoad s =>
    -- Live `E3-1` `TLSLD` + `DTPOFF32` `mov` (`48 8b 80`): 7B + 5B + 7B = 19B
    ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x3D,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
      BitVec.ofNat 8 0xE8,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
      BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0],
     [{ offset := pc + 3, kind := .r_tlsld, sym := s, addend := Int.negSucc 3 },
      { offset := pc + 8, kind := .r_plt32, sym := 0, addend := Int.negSucc 3 },
      { offset := pc + 15, kind := .r_dtpoff32, sym := s, addend := Int.ofNat 0 }])
  | .tlsGotTpOff s =>
    ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05,
      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0],
     [{ offset := pc + 3, kind := .r_gottpoff, sym := s, addend := Int.negSucc 3 }])
  | .ret =>
    ([BitVec.ofNat 8 0xC3], [])

/-- Multi-instruction encoder accumulating exact section offsets across `ops`. -/
noncomputable def encodeOpsLoop (pc : Nat) :
    List MiniMachOp → List (BitVec 8) × List Elf64Reloc
  | [] => ([], [])
  | op :: rest =>
    let cur := encodeOneOp pc op
    let tail := encodeOpsLoop (pc + cur.1.length) rest
    (cur.1 ++ tail.1, cur.2 ++ tail.2)

/-- Encode a complete `MiniMach` function into an ELF64 `RelocObject`. -/
noncomputable def encodeFn (fnSym : SymId) (ops : List MiniMachOp) : RelocObject :=
  let res := encodeOpsLoop 0 ops
  { sym := fnSym, code := res.1, relocs := res.2 }

/-! ## Part III: Post-Link Patching, Opcode Relaxation, & `0xCC` Padding -/

/-- Link-time address, GOT, `GOTTPOFF`, and TLS resolution environment.
`gotSlotAddr` and `gotTpOffSlotAddr` are separated so unrelaxed `GOTTPOFF`
reads `sext32To64 (tlsTpOff s)` while regular `GOTPCREL` reads `symAddr s`. -/
structure LinkEnv where
  baseAddr : Nat
  symAddr : SymId → Nat
  gotSlotAddr : SymId → Nat
  gotTpOffSlotAddr : SymId → Nat
  tlsGetAddrAddr : Nat
  tlsTpOff : SymId → BitVec 32
  tlsDtpOff : SymId → BitVec 32
  threadPtrBase : BitVec 64

/-- Exact 32-bit signed PC-relative displacement `(target - (site + 4)) mod 2^32`. -/
noncomputable def rel32Disp (siteAddr targetAddr : Nat) : BitVec 32 :=
  BitVec.ofNat 32
    (Nat.mod (targetAddr + Nat.pow 2 32 - Nat.mod (siteAddr + 4) (Nat.pow 2 32))
      (Nat.pow 2 32))

/-- Sign-extend a 32-bit two's-complement offset (`tpoff32` or `disp32`) to 64 bits. -/
noncomputable def sext32To64 (w : BitVec 32) : BitVec 64 :=
  if Nat.blt w.toNat 2147483648 then
    BitVec.ofNat 64 w.toNat
  else
    BitVec.ofNat 64 (Nat.pow 2 64 - (Nat.pow 2 32 - w.toNat))

/-- Full signed 32-bit PC-relative reachability `[-2^31, 2^31)` covering both
forward (`nextPc ≤ target`) and backward (`target < nextPc`, e.g., `lea -0xd9(%rip)`)
references! -/
def PcRel32Reachable (nextPc target : Nat) : Prop :=
  (nextPc ≤ target ∧ target - nextPc < 2147483648) ∨
  (target < nextPc ∧ nextPc - target ≤ 2147483648)

/-- Apply ELF64 x86-64 linking & in-place opcode relaxation to one `MiniMachOp`
at virtual address `vaddr`. -/
noncomputable def linkOneOpBytes (env : LinkEnv) (vaddr : Nat) (relaxEnabled : Bool) :
    MiniMachOp → List (BitVec 8)
  | .callSym s =>
    [BitVec.ofNat 8 0xE8] ++ le32Bytes (rel32Disp (vaddr + 1) (env.symAddr s))
  | .leaRipSym s =>
    [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++
      le32Bytes (rel32Disp (vaddr + 3) (env.symAddr s))
  | .loadGotRelaxable s =>
    if relaxEnabled then
      [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++
        le32Bytes (rel32Disp (vaddr + 3) (env.symAddr s))
    else
      [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++
        le32Bytes (rel32Disp (vaddr + 3) (env.gotSlotAddr s))
  | .loadGotStrict s =>
    [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++
      le32Bytes (rel32Disp (vaddr + 3) (env.gotSlotAddr s))
  | .tlsGdAddr s =>
    if relaxEnabled then
      [BitVec.ofNat 8 0x64, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04,
       BitVec.ofNat 8 0x25, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
       BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++
        le32Bytes (env.tlsTpOff s)
    else
      [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x3D] ++
        le32Bytes (rel32Disp (vaddr + 4) (env.gotSlotAddr s)) ++
        [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xE8] ++
        le32Bytes (rel32Disp (vaddr + 12) env.tlsGetAddrAddr)
  | .tlsLdAddr s =>
    if relaxEnabled then
      [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64,
       BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25,
       BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
       BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++
        le32Bytes (env.tlsTpOff s)
    else
      [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x3D] ++
        le32Bytes (rel32Disp (vaddr + 3) (env.gotSlotAddr s)) ++
        [BitVec.ofNat 8 0xE8] ++ le32Bytes (rel32Disp (vaddr + 8) env.tlsGetAddrAddr) ++
        [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++
        le32Bytes (env.tlsDtpOff s)
  | .tlsLdLoad s =>
    if relaxEnabled then
      [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64,
       BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25,
       BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
       BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80] ++
        le32Bytes (env.tlsTpOff s)
    else
      [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x3D] ++
        le32Bytes (rel32Disp (vaddr + 3) (env.gotSlotAddr s)) ++
        [BitVec.ofNat 8 0xE8] ++ le32Bytes (rel32Disp (vaddr + 8) env.tlsGetAddrAddr) ++
        [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80] ++
        le32Bytes (env.tlsDtpOff s)
  | .tlsGotTpOff s =>
    if relaxEnabled then
      [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xC7, BitVec.ofNat 8 0xC0] ++
        le32Bytes (env.tlsTpOff s)
    else
      [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++
        le32Bytes (rel32Disp (vaddr + 3) (env.gotTpOffSlotAddr s))
  | op => (encodeOneOp 0 op).1

/-- Emit `n` `0xCC` (`int3`) inter-function alignment padding bytes. -/
noncomputable def mkInt3Pad : Nat → List (BitVec 8)
  | 0 => []
  | n + 1 => BitVec.ofNat 8 0xCC :: mkInt3Pad n

/-- Link a multi-instruction `MiniMach` function starting at `vaddr` (threading
`vaddr + pc` across every instruction) and append `padBytes` `0xCC` bytes. -/
noncomputable def linkOpsLoop (env : LinkEnv) (vaddr : Nat) (relaxEnabled : Bool) :
    List MiniMachOp → List (BitVec 8)
  | [] => []
  | op :: rest =>
    let bs := linkOneOpBytes env vaddr relaxEnabled op
    bs ++ linkOpsLoop env (vaddr + bs.length) relaxEnabled rest

noncomputable def linkFn (env : LinkEnv) (vaddr : Nat) (relaxEnabled : Bool)
    (padBytes : Nat) (ops : List MiniMachOp) : List (BitVec 8) :=
  linkOpsLoop env vaddr relaxEnabled ops ++ mkInt3Pad padBytes

/-! ## Part IV: Naive vs. AST-Free Byte-Level Post-Link Validator -/

noncomputable def byteIndexInRelocHole (idx : Nat) : List Elf64Reloc → Bool
  | [] => false
  | r :: rs =>
    (Nat.ble r.offset idx && Nat.blt idx (r.offset + 4)) ||
      byteIndexInRelocHole idx rs

noncomputable def naiveDispOnlyCheckLoop (idx : Nat) (relocs : List Elf64Reloc) :
    List (BitVec 8) → List (BitVec 8) → Bool
  | [], [] => true
  | b1 :: bs1, b2 :: bs2 =>
    (Nat.beq b1.toNat b2.toNat || byteIndexInRelocHole idx relocs) &&
      naiveDispOnlyCheckLoop (idx + 1) relocs bs1 bs2
  | _, _ => false

/-- Naive displacement-only post-link checker: rejects opcode rewrites and
trailing `0xCC` padding. -/
noncomputable def naiveDispOnlyValidator (objBytes linkedBytes : List (BitVec 8))
    (relocs : List Elf64Reloc) : Bool :=
  naiveDispOnlyCheckLoop 0 relocs objBytes linkedBytes

noncomputable def byteListEq : List (BitVec 8) → List (BitVec 8) → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a.toNat b.toNat && byteListEq as bs
  | _, _ => false

noncomputable def allInt3 : List (BitVec 8) → Bool
  | [] => true
  | b :: bs => Nat.beq b.toNat 0xCC && allInt3 bs

/-- Pre-link byte templates used strictly for byte-level matching inside
`validateLinkedBytes` (NO `MiniMachOp` AST inspection!). -/
noncomputable def tmplCall : List (BitVec 8) :=
  [BitVec.ofNat 8 0xE8, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0]

noncomputable def tmplLeaRip : List (BitVec 8) :=
  [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05,
   BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0]

noncomputable def tmplMovRip : List (BitVec 8) :=
  [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05,
   BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0]

noncomputable def tmplTlsGdObj : List (BitVec 8) :=
  [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x3D,
   BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
   BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xE8,
   BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0]

noncomputable def tmplTlsLdObj (opByte : Nat) : List (BitVec 8) :=
  [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x3D,
   BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
   BitVec.ofNat 8 0xE8,
   BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
   BitVec.ofNat 8 0x48, BitVec.ofNat 8 opByte, BitVec.ofNat 8 0x80,
   BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0]

noncomputable def checkPrefixEq (expected bs : List (BitVec 8)) : Bool :=
  Nat.ble expected.length bs.length && byteListEq expected (bs.take expected.length)

/-- Helper matching an ELF64 relocation sequence anchored at section offset
`off`, returning `some (consumedObjBytes, remainingRelocs)` if the linked bytes
satisfy the exact post-link template (permitting opcode relaxation ONLY when
gated by the matching relocation kind, and forbidding `GOTPCREL` relaxation). -/
noncomputable def matchRelocAtOff (env : LinkEnv) (off : Nat)
    (obj : List (BitVec 8)) (rels : List Elf64Reloc) (lnk : List (BitVec 8)) :
    Option (Nat × List Elf64Reloc) :=
  match rels with
  | r1 :: r2 :: r3 :: rRest =>
    match r1.kind, r2.kind, r3.kind with
    | .r_tlsld, .r_plt32, .r_dtpoff32 =>
      if Nat.beq r1.offset (off + 3) && Nat.beq r2.offset (off + 8) &&
         Nat.beq r3.offset (off + 15) && Nat.beq r1.sym r3.sym then
        let lePrefix :=
          [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64,
           BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25,
           BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0]
        let expLea := lePrefix ++ [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++
          le32Bytes (env.tlsTpOff r1.sym)
        let expMov := lePrefix ++ [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80] ++
          le32Bytes (env.tlsTpOff r1.sym)
        if checkPrefixEq (tmplTlsLdObj 0x8D) obj && checkPrefixEq expLea lnk then
          some (19, rRest)
        else if checkPrefixEq (tmplTlsLdObj 0x8B) obj && checkPrefixEq expMov lnk then
          some (19, rRest)
        else none
      else none
    | .r_tlsgd, .r_plt32, _ =>
      if Nat.beq r1.offset (off + 4) && Nat.beq r2.offset (off + 12) then
        let expGd :=
          [BitVec.ofNat 8 0x64, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04,
           BitVec.ofNat 8 0x25, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
           BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++
            le32Bytes (env.tlsTpOff r1.sym)
        if checkPrefixEq tmplTlsGdObj obj && checkPrefixEq expGd lnk then
          some (16, r3 :: rRest)
        else none
      else none
    | _, _, _ => none
  | [r1, r2] =>
    match r1.kind, r2.kind with
    | .r_tlsgd, .r_plt32 =>
      if Nat.beq r1.offset (off + 4) && Nat.beq r2.offset (off + 12) then
        let expGd :=
          [BitVec.ofNat 8 0x64, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04,
           BitVec.ofNat 8 0x25, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
           BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++
            le32Bytes (env.tlsTpOff r1.sym)
        if checkPrefixEq tmplTlsGdObj obj && checkPrefixEq expGd lnk then
          some (16, [])
        else none
      else none
    | _, _ => none
  | _ => none

/-- Match a single-relocation instruction anchored at `off` (`PLT32`, `PC32`,
`GOTPCREL`, `REX_GOTPCRELX`, or `GOTTPOFF`). -/
noncomputable def matchSingleRelocAtOff (env : LinkEnv) (vaddr off : Nat)
    (obj : List (BitVec 8)) (r : Elf64Reloc) (rRest : List Elf64Reloc)
    (lnk : List (BitVec 8)) : Option (Nat × List Elf64Reloc) :=
  match r.kind with
  | .r_plt32 =>
    if Nat.beq r.offset (off + 1) then
      let exp := [BitVec.ofNat 8 0xE8] ++ le32Bytes (rel32Disp (vaddr + off + 1) (env.symAddr r.sym))
      if checkPrefixEq tmplCall obj && checkPrefixEq exp lnk then some (5, rRest) else none
    else none
  | .r_pc32 =>
    if Nat.beq r.offset (off + 3) then
      let exp := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++
        le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr r.sym))
      if checkPrefixEq tmplLeaRip obj && checkPrefixEq exp lnk then some (7, rRest) else none
    else none
  | .r_gotpcrel =>
    if Nat.beq r.offset (off + 3) then
      let exp := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++
        le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr r.sym))
      if checkPrefixEq tmplMovRip obj && checkPrefixEq exp lnk then some (7, rRest) else none
    else none
  | .r_rex_gotpcrelx =>
    if Nat.beq r.offset (off + 3) then
      let expRel := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++
        le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr r.sym))
      let expUnrel := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++
        le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr r.sym))
      if checkPrefixEq tmplMovRip obj && (checkPrefixEq expRel lnk || checkPrefixEq expUnrel lnk) then
        some (7, rRest)
      else none
    else none
  | .r_gottpoff =>
    if Nat.beq r.offset (off + 3) then
      let expRel := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xC7, BitVec.ofNat 8 0xC0] ++
        le32Bytes (env.tlsTpOff r.sym)
      let expUnrel := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++
        le32Bytes (rel32Disp (vaddr + off + 3) (env.gotTpOffSlotAddr r.sym))
      if checkPrefixEq tmplMovRip obj && (checkPrefixEq expRel lnk || checkPrefixEq expUnrel lnk) then
        some (7, rRest)
      else none
    else none
  | _ => none

/-- Check whether the head relocation requires a multi-byte relocation handler
starting at `off` (preventing byte-by-byte fallback from silently accepting an
unrelaxed or tampered relocated instruction). -/
noncomputable def isRelocAnchoredAt (off : Nat) (rels : List Elf64Reloc) : Bool :=
  match rels with
  | r :: _ =>
    match r.kind with
    | .r_plt32 => Nat.beq r.offset (off + 1)
    | .r_pc32 | .r_gotpcrel | .r_rex_gotpcrelx | .r_gottpoff | .r_tlsld =>
      Nat.beq r.offset (off + 3)
    | .r_tlsgd => Nat.beq r.offset (off + 4)
    | _ => false
  | [] => false

/-- AST-free byte-level post-link PIE validator scanning `(objBytes, relocs,
linkedBytes)` in lockstep with structural fuel. Permits opcode rewrites ONLY
when gated by the matching ELF64 relocation kind, forbids relaxation on
`R_X86_64_GOTPCREL`, requires Local-Exec relaxation on `TLSGD`/`TLSLD`, and
permits trailing `0xCC` alignment padding at EOF. -/
noncomputable def validateLinkedBytesLoop (env : LinkEnv) (vaddr : Nat) :
    Nat → Nat → List (BitVec 8) → List Elf64Reloc → List (BitVec 8) → Bool
  | _, _, [], [], lnk => allInt3 lnk
  | 0, _, _, _, _ => false
  | fuel + 1, off, obj, rels, lnk =>
    if isRelocAnchoredAt off rels then
      match matchRelocAtOff env off obj rels lnk with
      | some (stepLen, rels') =>
        validateLinkedBytesLoop env vaddr fuel (off + stepLen) (obj.drop stepLen) rels' (lnk.drop stepLen)
      | none =>
        match rels with
        | r :: rRest =>
          match matchSingleRelocAtOff env vaddr off obj r rRest lnk with
          | some (stepLen, rels') =>
            validateLinkedBytesLoop env vaddr fuel (off + stepLen) (obj.drop stepLen) rels' (lnk.drop stepLen)
          | none => false
        | [] => false
    else
      match obj, lnk with
      | b1 :: bs1, b2 :: bs2 =>
        Nat.beq b1.toNat b2.toNat &&
          validateLinkedBytesLoop env vaddr fuel (off + 1) bs1 rels bs2
      | _, _ => false

/-- Top-level AST-free byte-level post-link validator. -/
noncomputable def validateLinkedBytes (env : LinkEnv) (vaddr : Nat)
    (objBytes : List (BitVec 8)) (relocs : List Elf64Reloc)
    (linkedBytes : List (BitVec 8)) : Bool :=
  validateLinkedBytesLoop env vaddr objBytes.length 0 objBytes relocs linkedBytes

/-! ## Part V: Single-Instruction `x86-64` Byte Decoder & Multi-Op Semantics -/

/-- Abstract machine state for post-link instruction execution. -/
structure MachState where
  rax : BitVec 64
  rcx : BitVec 64
  rdx : BitVec 64
  rdi : BitVec 64
  rsi : BitVec 64
  rsp : BitVec 64
  rbp : BitVec 64
  r11 : BitVec 64
  mem : BitVec 64 → BitVec 64

noncomputable def readGpr (st : MachState) : Gpr → BitVec 64
  | .rax => st.rax
  | .rcx => st.rcx
  | .rdx => st.rdx
  | .rdi => st.rdi
  | .rsi => st.rsi
  | .rsp => st.rsp
  | .rbp => st.rbp
  | .r11 => st.r11

noncomputable def applyWriteMode (old : BitVec 64) (mode : WriteMode)
    (v : BitVec 64) : BitVec 64 :=
  match mode with
  | .full64 => v
  | .zeroExt32 => BitVec.ofNat 64 (Nat.mod v.toNat 4294967296)
  | .lo16PreserveUpper48 =>
    let hi := Nat.div old.toNat 65536
    let lo := Nat.mod v.toNat 65536
    BitVec.ofNat 64 (hi * 65536 + lo)

noncomputable def writeGpr (st : MachState) (g : Gpr) (mode : WriteMode)
    (v : BitVec 64) : MachState :=
  let nv := applyWriteMode (readGpr st g) mode v
  match g with
  | .rax => { st with rax := nv }
  | .rcx => { st with rcx := nv }
  | .rdx => { st with rdx := nv }
  | .rdi => { st with rdi := nv }
  | .rsi => { st with rsi := nv }
  | .rsp => { st with rsp := nv }
  | .rbp => { st with rbp := nv }
  | .r11 => { st with r11 := nv }

/-- Well-formedness of link-time GOT and `GOTTPOFF` tables. -/
def LinkEnvConsistent (env : LinkEnv) (st : MachState) : Prop :=
  (∀ s, st.mem (BitVec.ofNat 64 (env.gotSlotAddr s)) = BitVec.ofNat 64 (env.symAddr s)) ∧
  (∀ s, st.mem (BitVec.ofNat 64 (env.gotTpOffSlotAddr s)) = sext32To64 (env.tlsTpOff s))

/-- Source-level `MiniMachOp` denotation (purely symbolic over `env`). -/
noncomputable def execMiniMachOp (env : LinkEnv) (op : MiniMachOp)
    (st : MachState) : MachState :=
  match op with
  | .movImm32 dst true imm => writeGpr st dst .full64 (sext32To64 imm)
  | .movImm32 dst false imm => writeGpr st dst .zeroExt32 (BitVec.ofNat 64 imm.toNat)
  | .movImm16 dst imm => writeGpr st dst .lo16PreserveUpper48 (BitVec.ofNat 64 imm.toNat)
  | .movReg dst src mode => writeGpr st dst mode (readGpr st src)
  | .leaRipSym s | .loadGotRelaxable s | .loadGotStrict s =>
    writeGpr st .rax .full64 (BitVec.ofNat 64 (env.symAddr s))
  | .tlsGdAddr s | .tlsLdAddr s =>
    writeGpr st .rax .full64 (env.threadPtrBase + sext32To64 (env.tlsTpOff s))
  | .tlsLdLoad s =>
    writeGpr st .rax .full64 (st.mem (env.threadPtrBase + sext32To64 (env.tlsTpOff s)))
  | .tlsGotTpOff s =>
    writeGpr st .rax .full64 (sext32To64 (env.tlsTpOff s))
  | .callSym _ | .ret => st

/-- Multi-instruction source-level `MiniMach` function semantics. -/
noncomputable def execMiniMachFn (env : LinkEnv) :
    List MiniMachOp → MachState → MachState
  | [], st => st
  | op :: rest, st => execMiniMachFn env rest (execMiniMachOp env op st)

/-- Individual decoded `x86-64` architectural instructions (note: relaxed
`TLSGD` decodes as TWO separate instructions `movFsZeroRax` 9B + `leaDispRax`
7B across the shifted `+9` boundary; relaxed `TLSLD` decodes as TWO separate
instructions `movFsZeroRax` 12B + `leaDispRax`/`movDispRax` 7B across `+12`). -/
inductive X86Insn where
  | movImm64 (dst : Gpr) (imm : BitVec 32)
  | movImm32 (dst : Gpr) (imm : BitVec 32)
  | movImm16 (dst : Gpr) (imm : BitVec 16)
  | movReg (dst src : Gpr) (mode : WriteMode)
  | leaRipRax (disp : BitVec 32)
  | movRipRax (disp : BitVec 32)
  | callRel32 (disp : BitVec 32)
  | movFsZeroRax
  | leaDispRax (disp : BitVec 32)
  | movDispRax (disp : BitVec 32)
  | ret

/-- Decode `<= 7`-byte `x86-64` instructions (called for all non-12B/9B heads). -/
noncomputable def decodeShortInsn (bs : List (BitVec 8)) :
    Option (X86Insn × Nat × List (BitVec 8)) :=
  match bs with
  | b0 :: rest0 =>
    -- 1-byte `ret` (`0xC3`)
    if Nat.beq b0.toNat 0xC3 then
      some (.ret, 1, rest0)
    -- 5-byte `call rel32` (`0xE8`)
    else if Nat.beq b0.toNat 0xE8 then
      match rest0 with
      | d0 :: d1 :: d2 :: d3 :: tail =>
        match decodeLe32 [d0, d1, d2, d3] with
        | some d => some (.callRel32 d, 5, tail)
        | none => none
      | _ => none
    -- 5-byte `movl $imm32, %r32` (`0xB8..0xBF`)
    else if Nat.ble 0xB8 b0.toNat && Nat.ble b0.toNat 0xBF then
      match decodeGpr false (b0.toNat - 0xB8), rest0 with
      | some dst, d0 :: d1 :: d2 :: d3 :: tail =>
        match decodeLe32 [d0, d1, d2, d3] with
        | some imm => some (.movImm32 dst imm, 5, tail)
        | none => none
      | _, _ => none
    -- 2-byte `movl %src32, %dst32` (`0x89 ModRM`)
    else if Nat.beq b0.toNat 0x89 then
      match rest0 with
      | modrm :: tail =>
        if Nat.ble 0xC0 modrm.toNat then
          let srcLo := Nat.div (modrm.toNat - 0xC0) 8
          let dstLo := Nat.mod (modrm.toNat - 0xC0) 8
          match decodeGpr false dstLo, decodeGpr false srcLo with
          | some dst, some src => some (.movReg dst src .zeroExt32, 2, tail)
          | _, _ => none
        else none
      | _ => none
    -- `0x66` operand-size prefix (`movw $imm16` 4B/5B or `movw %src16, %dst16` 3B/4B)
    else if Nat.beq b0.toNat 0x66 then
      match rest0 with
      | b1 :: rest1 =>
        if Nat.ble 0xB8 b1.toNat && Nat.ble b1.toNat 0xBF then
          match decodeGpr false (b1.toNat - 0xB8), rest1 with
          | some dst, d0 :: d1 :: tail =>
            match decodeLe16 [d0, d1] with
            | some imm => some (.movImm16 dst imm, 4, tail)
            | none => none
          | _, _ => none
        else if Nat.beq b1.toNat 0x41 then
          match rest1 with
          | b2 :: d0 :: d1 :: tail =>
            if Nat.beq b2.toNat 0xBB then
              match decodeLe16 [d0, d1] with
              | some imm => some (.movImm16 .r11 imm, 5, tail)
              | none => none
            else if Nat.beq b2.toNat 0x89 then
              if Nat.ble 0xC0 d0.toNat then
                let srcLo := Nat.div (d0.toNat - 0xC0) 8
                let dstLo := Nat.mod (d0.toNat - 0xC0) 8
                match decodeGpr true dstLo, decodeGpr false srcLo with
                | some dst, some src => some (.movReg dst src .lo16PreserveUpper48, 4, d1 :: tail)
                | _, _ => none
              else none
            else none
          | b2 :: modrm :: tail =>
            if Nat.beq b2.toNat 0x89 && Nat.ble 0xC0 modrm.toNat then
              let srcLo := Nat.div (modrm.toNat - 0xC0) 8
              let dstLo := Nat.mod (modrm.toNat - 0xC0) 8
              match decodeGpr true dstLo, decodeGpr false srcLo with
              | some dst, some src => some (.movReg dst src .lo16PreserveUpper48, 4, tail)
              | _, _ => none
            else none
          | _ => none
        else if Nat.beq b1.toNat 0x89 then
          match rest1 with
          | modrm :: tail =>
            if Nat.ble 0xC0 modrm.toNat then
              let srcLo := Nat.div (modrm.toNat - 0xC0) 8
              let dstLo := Nat.mod (modrm.toNat - 0xC0) 8
              match decodeGpr false dstLo, decodeGpr false srcLo with
              | some dst, some src => some (.movReg dst src .lo16PreserveUpper48, 3, tail)
              | _, _ => none
            else none
          | _ => none
        else if Nat.beq b1.toNat 0x44 || Nat.beq b1.toNat 0x45 then
          match rest1 with
          | b2 :: modrm :: tail =>
            if Nat.beq b2.toNat 0x89 && Nat.ble 0xC0 modrm.toNat then
              let srcLo := Nat.div (modrm.toNat - 0xC0) 8
              let dstLo := Nat.mod (modrm.toNat - 0xC0) 8
              let bBit := Nat.beq b1.toNat 0x45
              match decodeGpr bBit dstLo, decodeGpr true srcLo with
              | some dst, some src => some (.movReg dst src .lo16PreserveUpper48, 4, tail)
              | _, _ => none
            else none
          | _ => none
        else none
      | _ => none
    -- REX prefix (`0x40..0x4F`)
    else if Nat.ble 0x40 b0.toNat && Nat.ble b0.toNat 0x4F then
      let rexW := Nat.beq (Nat.mod (Nat.div (b0.toNat - 0x40) 8) 2) 1
      let rexR := Nat.beq (Nat.mod (Nat.div (b0.toNat - 0x40) 4) 2) 1
      let rexB := Nat.beq (Nat.mod (b0.toNat - 0x40) 2) 1
      match rest0 with
      -- 6-byte `41 BB imm32` (`movl $imm32, %r11d`)
      | b1 :: d0 :: d1 :: d2 :: d3 :: tail =>
        if !rexW && !rexR && rexB && Nat.beq b1.toNat 0xBB then
          match decodeLe32 [d0, d1, d2, d3] with
          | some imm => some (.movImm32 .r11 imm, 6, tail)
          | none => none
        -- 7-byte `48/49 C7 C0+r imm32`, `48 8D 05`, `48 8B 05`, `48 8D 80`, `48 8B 80`
        else if Nat.beq b1.toNat 0xC7 && rexW && !rexR then
          match tail with
          | t0 :: tail7 =>
            if Nat.ble 0xC0 d0.toNat && Nat.ble d0.toNat 0xC7 then
              match decodeGpr rexB (d0.toNat - 0xC0), decodeLe32 [d1, d2, d3, t0] with
              | some dst, some imm => some (.movImm64 dst imm, 7, tail7)
              | _, _ => none
            else none
          | _ => none
        else if Nat.beq b0.toNat 0x48 && Nat.beq b1.toNat 0x8D && Nat.beq d0.toNat 0x05 then
          match tail with
          | t0 :: tail7 =>
            match decodeLe32 [d1, d2, d3, t0] with
            | some disp => some (.leaRipRax disp, 7, tail7)
            | none => none
          | _ => none
        else if Nat.beq b0.toNat 0x48 && Nat.beq b1.toNat 0x8B && Nat.beq d0.toNat 0x05 then
          match tail with
          | t0 :: tail7 =>
            match decodeLe32 [d1, d2, d3, t0] with
            | some disp => some (.movRipRax disp, 7, tail7)
            | none => none
          | _ => none
        else if Nat.beq b0.toNat 0x48 && Nat.beq b1.toNat 0x8D && Nat.beq d0.toNat 0x80 then
          match tail with
          | t0 :: tail7 =>
            match decodeLe32 [d1, d2, d3, t0] with
            | some disp => some (.leaDispRax disp, 7, tail7)
            | none => none
          | _ => none
        else if Nat.beq b0.toNat 0x48 && Nat.beq b1.toNat 0x8B && Nat.beq d0.toNat 0x80 then
          match tail with
          | t0 :: tail7 =>
            match decodeLe32 [d1, d2, d3, t0] with
            | some disp => some (.movDispRax disp, 7, tail7)
            | none => none
          | _ => none
        else if Nat.beq b1.toNat 0x89 && Nat.ble 0xC0 d0.toNat then
          let srcLo := Nat.div (d0.toNat - 0xC0) 8
          let dstLo := Nat.mod (d0.toNat - 0xC0) 8
          let mode := if rexW then WriteMode.full64 else WriteMode.zeroExt32
          match decodeGpr rexB dstLo, decodeGpr rexR srcLo with
          | some dst, some src => some (.movReg dst src mode, 3, d1 :: d2 :: d3 :: tail)
          | _, _ => none
        else none
      | b1 :: modrm :: tail =>
        if Nat.beq b1.toNat 0x89 && Nat.ble 0xC0 modrm.toNat then
          let srcLo := Nat.div (modrm.toNat - 0xC0) 8
          let dstLo := Nat.mod (modrm.toNat - 0xC0) 8
          let mode := if rexW then WriteMode.full64 else WriteMode.zeroExt32
          match decodeGpr rexB dstLo, decodeGpr rexR srcLo with
          | some dst, some src => some (.movReg dst src mode, 3, tail)
          | _, _ => none
        else none
      | _ => none
    else none
  | [] => none

/-- Unified single-instruction `x86-64` decoder checking 12B `TLSLD` -> 9B
`TLSGD` -> `<= 7B` instructions. -/
noncomputable def decodeInsn (bs : List (BitVec 8)) :
    Option (X86Insn × Nat × List (BitVec 8)) :=
  match bs with
  | p0 :: p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: p7 :: z0 :: z1 :: z2 :: z3 :: rest =>
    if Nat.beq p0.toNat 0x66 && Nat.beq p1.toNat 0x66 && Nat.beq p2.toNat 0x66 &&
       Nat.beq p3.toNat 0x64 && Nat.beq p4.toNat 0x48 && Nat.beq p5.toNat 0x8B &&
       Nat.beq p6.toNat 0x04 && Nat.beq p7.toNat 0x25 &&
       Nat.beq z0.toNat 0 && Nat.beq z1.toNat 0 && Nat.beq z2.toNat 0 && Nat.beq z3.toNat 0 then
      some (.movFsZeroRax, 12, rest)
    else if Nat.beq p0.toNat 0x64 && Nat.beq p1.toNat 0x48 && Nat.beq p2.toNat 0x8B &&
       Nat.beq p3.toNat 0x04 && Nat.beq p4.toNat 0x25 &&
       Nat.beq p5.toNat 0 && Nat.beq p6.toNat 0 && Nat.beq p7.toNat 0 && Nat.beq z0.toNat 0 then
      some (.movFsZeroRax, 9, z1 :: z2 :: z3 :: rest)
    else
      decodeShortInsn bs
  | p0 :: p1 :: p2 :: p3 :: p4 :: z0 :: z1 :: z2 :: z3 :: rest =>
    if Nat.beq p0.toNat 0x64 && Nat.beq p1.toNat 0x48 && Nat.beq p2.toNat 0x8B &&
       Nat.beq p3.toNat 0x04 && Nat.beq p4.toNat 0x25 &&
       Nat.beq z0.toNat 0 && Nat.beq z1.toNat 0 && Nat.beq z2.toNat 0 && Nat.beq z3.toNat 0 then
      some (.movFsZeroRax, 9, rest)
    else
      decodeShortInsn bs
  | _ => decodeShortInsn bs

/-- Execute ONE decoded `x86-64` instruction at `pc` with next PC `pc + len`. -/
noncomputable def execX86Insn (env : LinkEnv) (nextPc : Nat) (st : MachState) :
    X86Insn → MachState
  | .movImm64 dst imm => writeGpr st dst .full64 (sext32To64 imm)
  | .movImm32 dst imm => writeGpr st dst .zeroExt32 (BitVec.ofNat 64 imm.toNat)
  | .movImm16 dst imm => writeGpr st dst .lo16PreserveUpper48 (BitVec.ofNat 64 imm.toNat)
  | .movReg dst src mode => writeGpr st dst mode (readGpr st src)
  | .leaRipRax disp =>
    writeGpr st .rax .full64 (BitVec.ofNat 64 nextPc + sext32To64 disp)
  | .movRipRax disp =>
    writeGpr st .rax .full64 (st.mem (BitVec.ofNat 64 nextPc + sext32To64 disp))
  | .callRel32 _ => st
  | .movFsZeroRax => writeGpr st .rax .full64 env.threadPtrBase
  | .leaDispRax disp => writeGpr st .rax .full64 (st.rax + sext32To64 disp)
  | .movDispRax disp => writeGpr st .rax .full64 (st.mem (st.rax + sext32To64 disp))
  | .ret => st

/-- Execute a linked `x86-64` byte stream one instruction at a time, halting
cleanly on empty tail or trailing `0xCC` (`int3`) inter-function padding. -/
noncomputable def execByteStreamLoop (env : LinkEnv) :
    Nat → Nat → List (BitVec 8) → MachState → Option MachState
  | _, _, [], st => some st
  | 0, _, bs, st => if allInt3 bs then some st else none
  | fuel + 1, pc, bs, st =>
    if allInt3 bs then some st
    else
      match decodeInsn bs with
      | some (insn, len, rest) =>
        execByteStreamLoop env fuel (pc + len) rest (execX86Insn env (pc + len) st insn)
      | none => none

noncomputable def execByteStream (env : LinkEnv) (vaddr : Nat)
    (bs : List (BitVec 8)) (st : MachState) : Option MachState :=
  execByteStreamLoop env bs.length vaddr bs st

/-- Predicate stating every symbol/GOT/GOTTPOFF PC-relative reference in `ops`
at section base `vaddr` is within signed 32-bit reach `[-2^31, 2^31)`. -/
inductive OpsPcRelReachable (env : LinkEnv) : Nat → List MiniMachOp → Prop where
  | nil {pc} : OpsPcRelReachable env pc []
  | cons {pc op rest} :
      (match op with
       | .leaRipSym s => PcRel32Reachable (pc + 7) (env.symAddr s)
       | .loadGotRelaxable s =>
           PcRel32Reachable (pc + 7) (env.symAddr s) ∧
           PcRel32Reachable (pc + 7) (env.gotSlotAddr s)
       | .loadGotStrict s => PcRel32Reachable (pc + 7) (env.gotSlotAddr s)
       | .tlsGotTpOff s => PcRel32Reachable (pc + 7) (env.gotTpOffSlotAddr s)
       | _ => True) →
      OpsPcRelReachable env (pc + (encodeOneOp 0 op).1.length) rest →
      OpsPcRelReachable env pc (op :: rest)

/-- Predicate indicating `ops` contains no `TLSGD`/`TLSLD` when `relax = false`
(PIE Local-Exec validator scope). -/
inductive OpsValidForRelaxMode (relax : Bool) : List MiniMachOp → Prop where
  | nil : OpsValidForRelaxMode relax []
  | cons {op rest} :
      (match op with
       | .tlsGdAddr _ | .tlsLdAddr _ | .tlsLdLoad _ => relax = true
       | _ => True) →
      OpsValidForRelaxMode relax rest →
      OpsValidForRelaxMode relax (op :: rest)

/-! ## Part VI: Two-Phase `%r11` Probe Prologue & `O(log n)` `.eh_frame_hdr` Binary Search -/

/-- CFA base register supporting LLVM's `>= 9`-page `%r11` inline probe loop
(`DW_CFA_def_cfa_register: reg11`, `Crucible 3` Table E1). -/
inductive CfaBaseReg where
  | rsp
  | r11

structure CfaRule where
  base : CfaBaseReg
  offset : Nat

/-- Explicit `%r11` stack-probe machine state tracking `lastProbedRsp` (updated
ONLY on explicit `movq $0, (%rsp)` guard-page writes) and `maxUnprobedGap`. -/
structure ProbeState where
  rsp : Nat
  r11 : Nat
  lastProbedRsp : Nat
  maxUnprobedGap : Nat
  cfaRule : CfaRule

noncomputable def evalCfa (st : ProbeState) : Nat :=
  match st.cfaRule.base with
  | .rsp => st.rsp + st.cfaRule.offset
  | .r11 => st.r11 + st.cfaRule.offset

/-- Phase 1–2 setup: push callee-save registers (`pushBytes = savedCfaOff - 8`),
set `r11 := rsp1 - numPages * 4096`, and switch CFA to `r11 + (savedCfaOff + numPages * 4096)`. -/
noncomputable def initR11ProbePrologue (rsp0 savedCfaOff numPages : Nat) : ProbeState :=
  let pushBytes := savedCfaOff - 8
  let rsp1 := rsp0 - pushBytes
  {
    rsp := rsp1
    r11 := rsp1 - numPages * 4096
    lastProbedRsp := rsp1
    maxUnprobedGap := pushBytes
    cfaRule := { base := .r11, offset := savedCfaOff + numPages * 4096 }
  }

noncomputable def natMax (a b : Nat) : Nat :=
  if a < b then b else a

/-- Fixed-stride (`4096` B, zero clamping!) `%r11` probe loop:
`sub $0x1000, %rsp; movq $0x0, (%rsp); cmp %r11, %rsp; jne loop`.
Exits immediately when `rsp == r11`. -/
noncomputable def runFixedStrideR11Loop : Nat → ProbeState → ProbeState
  | 0, st => st
  | k + 1, st =>
    if st.rsp = st.r11 then st
    else
      let rsp' := st.rsp - 4096
      let gap := st.lastProbedRsp - rsp'
      let st' : ProbeState := {
        rsp := rsp'
        r11 := st.r11
        lastProbedRsp := rsp'
        maxUnprobedGap := natMax st.maxUnprobedGap gap
        cfaRule := st.cfaRule
      }
      runFixedStrideR11Loop k st'

/-- Phase 4 post-loop tail `sub $tailBytes, %rsp` (`tailBytes < 4096`),
restoring CFA to `.rsp (savedCfaOff + numPages * 4096 + tailBytes)`. -/
noncomputable def finishR11ProbeTail (savedCfaOff numPages tailBytes : Nat)
    (st : ProbeState) : ProbeState :=
  let rsp' := st.rsp - tailBytes
  let gap := st.lastProbedRsp - rsp'
  {
    rsp := rsp'
    r11 := st.r11
    lastProbedRsp := st.lastProbedRsp
    maxUnprobedGap := natMax st.maxUnprobedGap gap
    cfaRule := { base := .rsp, offset := savedCfaOff + numPages * 4096 + tailBytes }
  }

/-- Sorted `.eh_frame_hdr` FDE entry covering half-open `[startPc, endPc)`. -/
structure EhFrameEntry where
  startPc : Nat
  endPc : Nat
  cfaRule : CfaRule

/-- Relocate all `.eh_frame` FDE PC intervals by post-link `baseAddr`. -/
noncomputable def relocateEhTable (baseAddr : Nat) : List EhFrameEntry → List EhFrameEntry
  | [] => []
  | e :: rest =>
    { startPc := baseAddr + e.startPc, endPc := baseAddr + e.endPc, cfaRule := e.cfaRule } ::
      relocateEhTable baseAddr rest

/-- Predicate stating an `.eh_frame_hdr` table is strictly sorted and non-overlapping. -/
inductive EhTableSorted : Nat → List EhFrameEntry → Prop where
  | nil {lo} : EhTableSorted lo []
  | cons {lo e rest} :
      lo ≤ e.startPc → e.startPc < e.endPc →
      EhTableSorted e.endPc rest →
      EhTableSorted lo (e :: rest)

/-- Reference linear scan specification over `.eh_frame_hdr`. -/
noncomputable def lookupEhFrame (pc : Nat) : List EhFrameEntry → Option CfaRule
  | [] => none
  | e :: rest =>
    if e.startPc ≤ pc ∧ pc < e.endPc then some e.cfaRule
    else lookupEhFrame pc rest

/-- Total `List` index lookup (pure structural recursion, zero `._unsafe_rec`). -/
noncomputable def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

/-- Genuine `O(log n)` binary search over sorted `.eh_frame_hdr` table on index
interval `[lo, hi)` using structural fuel. -/
noncomputable def bsearchEhLoop (pc : Nat) (tbl : List EhFrameEntry) :
    Nat → Nat → Nat → Option CfaRule
  | 0, _, _ => none
  | fuel + 1, lo, hi =>
    if hi ≤ lo then none
    else
      let mid := lo + Nat.div (hi - lo) 2
      match listGet? tbl mid with
      | none => none
      | some e =>
        if pc < e.startPc then
          bsearchEhLoop pc tbl fuel lo mid
        else if pc < e.endPc then
          some e.cfaRule
        else
          bsearchEhLoop pc tbl fuel (mid + 1) hi

noncomputable def bsearchEhFrame (pc : Nat) (tbl : List EhFrameEntry) : Option CfaRule :=
  bsearchEhLoop pc tbl tbl.length 0 tbl.length


/-! ## Stage 4 Constructive Proof Helpers (Strictly `private`, Zero `sorry`, Zero `omega`, Zero `Classical.choice`, Anneal `TrustedBoundary.lean`-Clean) -/

section Stage4ProofHelpers

/-! ### Layer 0: Core `Nat`, `Bool`, `BitVec`, and `List` Helpers -/

private theorem nat_div_add_mod (n d : Nat) : d * Nat.div n d + Nat.mod n d = n :=
  Nat.div_add_mod n d

private theorem nat_mod_lt (n : Nat) {d : Nat} (hd : 0 < d) : Nat.mod n d < d :=
  Nat.mod_lt n hd

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_div_div (n a b : Nat) : Nat.div (Nat.div n a) b = Nat.div n (a * b) :=
  Nat.div_div_eq_div_mul n a b

private theorem nat_div_lt_iff_lt_mul {x k n : Nat} (hk : 0 < k) :
    Nat.div x k < n ↔ x < n * k :=
  Nat.div_lt_iff_lt_mul hk

private theorem nat_add_mul_mod_right (x y z : Nat) :
    Nat.mod (x + y * z) z = Nat.mod x z :=
  Nat.add_mul_mod_self_right x y z

private theorem nat_add_mul_mod_left (x y z : Nat) :
    Nat.mod (x + y * z) y = Nat.mod x y :=
  Nat.add_mul_mod_self_left x y z

private theorem nat_mod_add_mod (a b n : Nat) :
    Nat.mod (Nat.mod a n + b) n = Nat.mod (a + b) n := by
  have h1 : (n * Nat.div a n + Nat.mod a n) + b = (Nat.mod a n + b) + n * Nat.div a n := by
    rw [Nat.add_comm (n * Nat.div a n), Nat.add_assoc, Nat.add_comm (n * Nat.div a n) b, ← Nat.add_assoc]
  rw [nat_div_add_mod a n] at h1
  rw [h1, nat_add_mul_mod_left]

private theorem nat_add_mod_right (a b n : Nat) :
    Nat.mod (a + Nat.mod b n) n = Nat.mod (a + b) n := by
  rw [Nat.add_comm a (Nat.mod b n), nat_mod_add_mod, Nat.add_comm]

private theorem nat_mod_mod (x m : Nat) : Nat.mod (Nat.mod x m) m = Nat.mod x m := by
  cases m with
  | zero => exact Nat.mod_zero _
  | succ m' => exact nat_mod_eq_of_lt (nat_mod_lt x (Nat.succ_pos m'))

private theorem nat_sub_sub_self {a b : Nat} (h : b ≤ a) : a - (a - b) = b := by
  have h1 : (a - b) + b = a := Nat.sub_add_cancel h
  have h2 : ((a - b) + b) - (a - b) = b := Nat.add_sub_cancel_left (a - b) b
  rw [h1] at h2
  exact h2

private theorem nat_le_sub_of_add_le_left {a b c : Nat} (h : a + b ≤ c) : b ≤ c - a :=
  Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact h)

private theorem nat_lt_of_add_lt_add_left : ∀ {k a b : Nat}, k + a < k + b → a < b
  | 0, _, _, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | k + 1, _, _, h => by
    rw [Nat.succ_add, Nat.succ_add] at h
    exact nat_lt_of_add_lt_add_left (Nat.lt_of_succ_lt_succ h)

private theorem nat_beq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

private theorem nat_eq_of_beq {a b : Nat} (h : Nat.beq a b = true) : a = b :=
  Nat.eq_of_beq_eq_true h

private theorem nat_beq_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact nat_beq_refl a

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact False.elim (h (nat_eq_of_beq hb))

private theorem nat_le_of_ble {a b : Nat} (h : Nat.ble a b = true) : a ≤ b :=
  Nat.le_of_ble_eq_true h

private theorem nat_ble_of_le {a b : Nat} (h : a ≤ b) : Nat.ble a b = true :=
  Nat.ble_eq_true_of_le h

private theorem nat_lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

private theorem nat_blt_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

private theorem nat_blt_false_of_le {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact False.elim (Nat.not_lt_of_ge h (nat_lt_of_blt hb))

private theorem bool_and_elim {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b
  · cases h
  · cases h
  · cases h
  · exact ⟨rfl, rfl⟩

private theorem ite_prop_true {α : Type} {P : Prop} {inst : Decidable P} (h : P) {a b : α} :
    @ite α P inst a b = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn h)

private theorem ite_prop_false {α : Type} {P : Prop} {inst : Decidable P} (h : ¬P) {a b : α} :
    @ite α P inst a b = b := by
  cases inst with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

private theorem bool_and_intro {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]; rfl

private theorem bool_or_elim {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a
  · cases b
    · cases h
    · exact Or.inr rfl
  · exact Or.inl rfl

private theorem ite_bool_true {α : Type} {a b : α} : (if (true = true) then a else b) = a := rfl
private theorem ite_bool_false {α : Type} {a b : α} : (if (false = true) then a else b) = b := rfl

private theorem bv_eq_of_toNat {w : Nat} {a b : BitVec w} (h : a.toNat = b.toNat) : a = b := by
  cases a with
  | ofFin fa =>
    cases b with
    | ofFin fb =>
      cases fa with
      | mk va ha =>
        cases fb with
        | mk vb hb =>
          dsimp only [BitVec.toNat] at h
          subst h
          rfl

private theorem bv_toNat_ofNat {w : Nat} (n : Nat) :
    (BitVec.ofNat w n).toNat = Nat.mod n (Nat.pow 2 w) := by
  rfl

private theorem bv_toNat_ofNat_of_lt {w n : Nat} (h : n < Nat.pow 2 w) :
    (BitVec.ofNat w n).toNat = n := by
  rw [bv_toNat_ofNat]
  exact nat_mod_eq_of_lt h

private theorem bv_toNat_add {w : Nat} (a b : BitVec w) :
    (a + b).toNat = Nat.mod (a.toNat + b.toNat) (Nat.pow 2 w) := by
  rfl

private theorem byteOfNat_toNat (n : Nat) : (byteOfNat n).toNat = Nat.mod n 256 := by
  dsimp only [byteOfNat]
  exact bv_toNat_ofNat_of_lt (nat_mod_lt n (by decide))

private theorem list_drop_append_exact {α : Type} (xs ys : List α) :
    (xs ++ ys).drop xs.length = ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [List.cons_append, List.length_cons, List.drop_succ_cons]
    exact ih

private theorem list_take_append_exact {α : Type} (xs ys : List α) :
    (xs ++ ys).take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [List.cons_append, List.length_cons, List.take_succ_cons]
    rw [ih]

private theorem byteListEq_refl (xs : List (BitVec 8)) : byteListEq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp only [byteListEq]
    rw [nat_beq_refl, ih]; rfl

private theorem byteListEq_eq {xs ys : List (BitVec 8)} (h : byteListEq xs ys = true) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xs ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      dsimp only [byteListEq] at h
      have ⟨hxy, hrest⟩ := bool_and_elim h
      have hxe : x = y := bv_eq_of_toNat (nat_eq_of_beq hxy)
      rw [hxe, ih hrest]

private theorem checkPrefixEq_append (pre rest : List (BitVec 8)) :
    checkPrefixEq pre (pre ++ rest) = true := by
  dsimp only [checkPrefixEq]
  have hle : pre.length ≤ (pre ++ rest).length := by
    rw [List.length_append]; exact Nat.le_add_right _ _
  rw [nat_ble_of_le hle, list_take_append_exact, byteListEq_refl]; rfl

private theorem list_take_append_drop {α : Type} :
    ∀ (n : Nat) (xs : List α), xs.take n ++ xs.drop n = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: xs => congrArg (x :: ·) (list_take_append_drop n xs)

private theorem eq_append_drop_of_checkPrefixEq {pre bs : List (BitVec 8)}
    (h : checkPrefixEq pre bs = true) :
    bs = pre ++ bs.drop pre.length := by
  dsimp only [checkPrefixEq] at h
  have ⟨_, heq⟩ := bool_and_elim h
  have htake : bs.take pre.length = pre := Eq.symm (byteListEq_eq heq)
  have h2 := list_take_append_drop pre.length bs
  rw [htake] at h2
  exact Eq.symm h2

/-! ### Layer 1: `le16`/`le32` Roundtrips & Signed `rel32Disp` Arithmetic -/

private theorem decodeLe16_le16Bytes (w : BitVec 16) :
    decodeLe16 (le16Bytes w) = some w := by
  dsimp only [le16Bytes, decodeLe16]
  rw [byteOfNat_toNat, byteOfNat_toNat]
  have hlt : w.toNat < 65536 := w.isLt
  have hdivLt : Nat.div w.toNat 256 < 256 := by
    rw [nat_div_lt_iff_lt_mul (by decide : 0 < 256)]
    exact hlt
  rw [nat_mod_eq_of_lt hdivLt]
  have hsum : Nat.mod w.toNat 256 + Nat.div w.toNat 256 * 256 = w.toNat := by
    rw [Nat.mul_comm, Nat.add_comm]
    exact nat_div_add_mod w.toNat 256
  rw [hsum]
  exact congrArg some (bv_eq_of_toNat (bv_toNat_ofNat_of_lt hlt))

private theorem decodeLe32_le32Bytes (w : BitVec 32) :
    decodeLe32 (le32Bytes w) = some w := by
  dsimp only [le32Bytes, decodeLe32]
  rw [byteOfNat_toNat, byteOfNat_toNat, byteOfNat_toNat, byteOfNat_toNat]
  have hlt : w.toNat < 4294967296 := w.isLt
  let n := w.toNat
  let q1 := Nat.div n 256
  let q2 := Nat.div n 65536
  let q3 := Nat.div n 16777216
  have hq2eq : q2 = Nat.div q1 256 := Eq.symm (nat_div_div n 256 256)
  have hq3eq : q3 = Nat.div q2 256 := Eq.symm (nat_div_div n 65536 256)
  have hq3Lt : q3 < 256 := by
    rw [nat_div_lt_iff_lt_mul (by decide : 0 < 16777216)]
    exact hlt
  rw [nat_mod_eq_of_lt hq3Lt]
  have hd3 : 256 * q3 + Nat.mod q2 256 = q2 := by
    rw [hq3eq]; exact nat_div_add_mod q2 256
  have hd2 : 256 * q2 + Nat.mod q1 256 = q1 := by
    rw [hq2eq]; exact nat_div_add_mod q1 256
  have hd1 : 256 * q1 + Nat.mod n 256 = n := nat_div_add_mod n 256
  have hsum : Nat.mod n 256 + Nat.mod q1 256 * 256 + Nat.mod q2 256 * 65536 + q3 * 16777216 = n := by
    have hstep1 : Nat.mod q2 256 * 65536 + q3 * 16777216 = q2 * 65536 := by
      have h1 : q3 * 16777216 = (256 * q3) * 65536 := by
        rw [Nat.mul_assoc, Nat.mul_comm q3 16777216]
        change 16777216 * q3 = 256 * (q3 * 65536)
        rw [Nat.mul_comm q3 65536, ← Nat.mul_assoc]
      rw [h1, ← Nat.add_mul, Nat.add_comm, hd3]
    have hstep2 : Nat.mod q1 256 * 256 + q2 * 65536 = q1 * 256 := by
      have h2 : q2 * 65536 = (256 * q2) * 256 := by
        rw [Nat.mul_assoc, Nat.mul_comm q2 65536]
        change 65536 * q2 = 256 * (q2 * 256)
        rw [Nat.mul_comm q2 256, ← Nat.mul_assoc]
      rw [h2, ← Nat.add_mul, Nat.add_comm, hd2]
    rw [Nat.add_assoc (Nat.mod n 256 + Nat.mod q1 256 * 256), hstep1,
        Nat.add_assoc (Nat.mod n 256), hstep2, Nat.mul_comm q1 256, Nat.add_comm, hd1]
  rw [hsum]
  exact congrArg some (bv_eq_of_toNat (bv_toNat_ofNat_of_lt hlt))

private theorem pcRel32_add_exact (site target : Nat)
    (hReach : PcRel32Reachable (site + 4) target) :
    BitVec.ofNat 64 (site + 4) + sext32To64 (rel32Disp site target) =
      BitVec.ofNat 64 target := by
  let nextPc := site + 4
  let M32 : Nat := 4294967296
  let M64 : Nat := 18446744073709551616
  have hM32_eq : Nat.pow 2 32 = M32 := rfl
  have hM64_eq : Nat.pow 2 64 = M64 := rfl
  cases hReach with
  | inl hFwd =>
    have ⟨hle, hdLt⟩ := hFwd
    let d := target - nextPc
    have htEq : target = nextPc + d := Eq.symm (Nat.add_sub_of_le hle)
    let q := Nat.div nextPc M32
    let r := Nat.mod nextPc M32
    have hnp : nextPc = M32 * q + r := Eq.symm (nat_div_add_mod nextPc M32)
    have hdispNat : (rel32Disp site target).toNat = d := by
      dsimp only [rel32Disp]
      rw [hM32_eq]
      have h1 : target + M32 - r = d + (q + 1) * M32 := by
        rw [htEq, hnp]
        have hstep : (M32 * q + r + d) + M32 = (d + (q + 1) * M32) + r := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm q M32]
          rw [Nat.add_assoc (M32 * q) r d, Nat.add_comm r d, ← Nat.add_assoc (M32 * q) d r]
          rw [Nat.add_assoc (M32 * q + d) r M32, Nat.add_comm r M32, ← Nat.add_assoc]
          rw [Nat.add_comm (M32 * q) d, Nat.add_assoc d (M32 * q) M32]
        rw [hstep, Nat.add_sub_cancel]
      have hdM32 : d < M32 := Nat.lt_trans hdLt (by decide)
      rw [bv_toNat_ofNat, hM32_eq, nat_mod_mod]
      rw [h1, nat_add_mul_mod_right, nat_mod_eq_of_lt hdM32]
    have hsext : sext32To64 (rel32Disp site target) = BitVec.ofNat 64 d := by
      dsimp only [sext32To64]
      rw [hdispNat, nat_blt_of_lt hdLt, ite_bool_true]
    rw [hsext]
    apply bv_eq_of_toNat
    rw [bv_toNat_add, bv_toNat_ofNat, bv_toNat_ofNat, bv_toNat_ofNat,
        nat_mod_add_mod, nat_add_mod_right, ← htEq]
  | inr hBwd =>
    have ⟨hlt, hdLe⟩ := hBwd
    let d := nextPc - target
    have hnpEq : nextPc = target + d := Eq.symm (Nat.add_sub_of_le (Nat.le_of_lt hlt))
    have hdPos : 0 < d := Nat.sub_pos_of_lt hlt
    have hdLtM32 : d < M32 := Nat.lt_of_le_of_lt hdLe (by decide)
    have hdispNat : (rel32Disp site target).toNat = M32 - d := by
      dsimp only [rel32Disp]
      rw [hM32_eq]
      let qt := Nat.div target M32
      let rt := Nat.mod target M32
      have hrtLt : rt < M32 := nat_mod_lt target (by decide)
      have htDecomp : target = M32 * qt + rt := Eq.symm (nat_div_add_mod target M32)
      have hmodSub : Nat.mod (target + M32 - Nat.mod nextPc M32) M32 = M32 - d := by
        cases hcmp : Nat.blt (rt + d) M32 with
        | true =>
          have hlt2 : rt + d < M32 := nat_lt_of_blt hcmp
          have hrEq : Nat.mod nextPc M32 = rt + d := by
            rw [hnpEq, htDecomp, Nat.add_assoc, Nat.add_comm (M32 * qt),
                nat_add_mul_mod_left, nat_mod_eq_of_lt hlt2]
          rw [hrEq, htDecomp]
          have hsub : M32 * qt + rt + M32 - (rt + d) = (M32 - d) + qt * M32 := by
            have heq1 : M32 * qt + rt + M32 = ((M32 - d) + qt * M32) + (rt + d) := by
              rw [Nat.mul_comm qt M32]
              have ha : (M32 - d) + M32 * qt + (rt + d) = M32 * qt + rt + ((M32 - d) + d) := by
                rw [Nat.add_comm (M32 - d) (M32 * qt), Nat.add_assoc (M32 * qt) (M32 - d) (rt + d),
                    Nat.add_comm rt d, ← Nat.add_assoc (M32 - d) d rt, Nat.add_comm ((M32 - d) + d) rt,
                    ← Nat.add_assoc]
              rw [ha, Nat.sub_add_cancel (Nat.le_of_lt hdLtM32)]
            rw [heq1, Nat.add_sub_cancel]
          rw [hsub, nat_add_mul_mod_right, nat_mod_eq_of_lt (Nat.sub_lt (by decide) hdPos)]
        | false =>
          have hge : M32 ≤ rt + d := by
            cases Nat.lt_or_ge (rt + d) M32 with
            | inl hl => rw [nat_blt_of_lt hl] at hcmp; cases hcmp
            | inr hg => exact hg
          have hlt2 : rt + d - M32 < M32 := by
            have hsumLt : rt + d < M32 + M32 := Nat.add_lt_add hrtLt hdLtM32
            exact Nat.sub_lt_left_of_lt_add hge hsumLt
          have hrEq : Nat.mod nextPc M32 = rt + d - M32 := by
            rw [hnpEq, htDecomp, Nat.add_assoc]
            have hrew : M32 * qt + (rt + d) = (rt + d - M32) + (qt + 1) * M32 := by
              rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm qt M32, Nat.add_comm (rt + d - M32),
                  Nat.add_assoc (M32 * qt) M32 (rt + d - M32), Nat.add_comm M32 (rt + d - M32),
                  Nat.sub_add_cancel hge]
            rw [hrew, nat_add_mul_mod_right, nat_mod_eq_of_lt hlt2]
          rw [hrEq, htDecomp]
          have hsub : M32 * qt + rt + M32 - (rt + d - M32) = (M32 - d) + (qt + 1) * M32 := by
            have heq1 : M32 * qt + rt + M32 = ((M32 - d) + (qt + 1) * M32) + (rt + d - M32) := by
              rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm qt M32]
              have h1 : (M32 - d) + (M32 * qt + M32) + (rt + d - M32) =
                  M32 * qt + ((M32 - d) + (M32 + (rt + d - M32))) := by
                rw [Nat.add_assoc (M32 - d) (M32 * qt + M32),
                    Nat.add_assoc (M32 * qt) M32 (rt + d - M32),
                    ← Nat.add_assoc (M32 - d) (M32 * qt),
                    Nat.add_comm (M32 - d) (M32 * qt),
                    Nat.add_assoc (M32 * qt) (M32 - d)]
              rw [h1, Nat.add_comm M32 (rt + d - M32), Nat.sub_add_cancel hge]
              have h2 : (M32 - d) + (rt + d) = rt + M32 := by
                rw [Nat.add_comm rt d, ← Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt hdLtM32),
                    Nat.add_comm]
              rw [h2, ← Nat.add_assoc]
            rw [heq1, Nat.add_sub_cancel]
          rw [hsub, nat_add_mul_mod_right, nat_mod_eq_of_lt (Nat.sub_lt (by decide) hdPos)]
      rw [bv_toNat_ofNat, hM32_eq, nat_mod_mod, hmodSub]
    have hgeHalf : 2147483648 ≤ M32 - d := by
      have h1 : 2147483648 + d ≤ M32 := Nat.add_le_add_left hdLe 2147483648
      exact Nat.le_sub_of_add_le h1
    have hsext : sext32To64 (rel32Disp site target) = BitVec.ofNat 64 (M64 - d) := by
      dsimp only [sext32To64]
      rw [hdispNat, nat_blt_false_of_le hgeHalf, ite_bool_false, hM64_eq, hM32_eq]
      have hsubsub : M32 - (M32 - d) = d := nat_sub_sub_self (Nat.le_of_lt hdLtM32)
      rw [hsubsub]
    rw [hsext]
    apply bv_eq_of_toNat
    rw [bv_toNat_add, bv_toNat_ofNat, bv_toNat_ofNat, bv_toNat_ofNat,
        nat_mod_add_mod, nat_add_mod_right, hM64_eq]
    have hnpEq' : site + 4 = target + d := hnpEq
    rw [hnpEq']
    have hdLeM64 : d ≤ M64 := Nat.le_trans hdLe (by decide)
    have hwrap : target + d + (M64 - d) = target + 1 * M64 := by
      rw [Nat.one_mul, Nat.add_assoc, Nat.add_comm d (M64 - d), Nat.sub_add_cancel hdLeM64]
    rw [hwrap, nat_add_mul_mod_right]


/-! ### Layer 2: Multi-Op Length & Relocation-Offset Invariants -/

private theorem le16Bytes_length (w : BitVec 16) : (le16Bytes w).length = 2 := rfl
private theorem le32Bytes_length (w : BitVec 32) : (le32Bytes w).length = 4 := rfl

private theorem nat_not_add_succ_le_zero {a b : Nat} (h : (a + 1) + b ≤ 0) : False := by
  rw [Nat.add_comm] at h
  exact Nat.not_succ_le_zero _ h

private theorem nat_le_of_add_succ_le_succ {k m f : Nat} (h : (k + 1) + m ≤ f + 1) : m ≤ f := by
  rw [Nat.add_comm (k + 1) m, ← Nat.add_assoc] at h
  exact Nat.le_trans (Nat.le_add_right m k) (Nat.le_of_succ_le_succ h)

private theorem ite_bool_eq_true {α : Type} {c : Bool} {x y : α} (h : c = true) :
    (if c = true then x else y) = x := by
  rw [h]; rfl

private theorem ite_bool_eq_false {α : Type} {c : Bool} {x y : α} (h : c = false) :
    (if c = true then x else y) = y := by
  rw [h]; exact ite_bool_false

private theorem list_drop_append_of_len {α : Type} (xs ys : List α) {n : Nat}
    (hn : xs.length = n) : (xs ++ ys).drop n = ys := by
  subst hn; exact list_drop_append_exact xs ys

private theorem reloc_cons_append (r : Elf64Reloc) (rs : List Elf64Reloc) :
    [r] ++ rs = r :: rs := rfl

private theorem reloc_cons2_append (r1 r2 : Elf64Reloc) (rs : List Elf64Reloc) :
    [r1, r2] ++ rs = r1 :: r2 :: rs := rfl

private theorem reloc_cons3_append (r1 r2 r3 : Elf64Reloc) (rs : List Elf64Reloc) :
    [r1, r2, r3] ++ rs = r1 :: r2 :: r3 :: rs := rfl

private theorem linkOneOpBytes_length (env : LinkEnv) (vaddr : Nat) (relax : Bool)
    (op : MiniMachOp) :
    (linkOneOpBytes env vaddr relax op).length = (encodeOneOp 0 op).1.length := by
  cases op with
  | movImm32 dst is64 imm => rfl
  | movImm16 dst imm => rfl
  | movReg dst src mode => rfl
  | callSym s =>
    dsimp only [linkOneOpBytes, encodeOneOp]
    simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
  | leaRipSym s =>
    dsimp only [linkOneOpBytes, encodeOneOp]
    simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
  | loadGotRelaxable s =>
    cases relax
    · dsimp only [linkOneOpBytes, encodeOneOp]; rw [ite_bool_false]
      simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
    · dsimp only [linkOneOpBytes, encodeOneOp]; rw [ite_bool_true]
      simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
  | loadGotStrict s =>
    dsimp only [linkOneOpBytes, encodeOneOp]
    simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
  | tlsGdAddr s =>
    cases relax
    · dsimp only [linkOneOpBytes, encodeOneOp]; rw [ite_bool_false]
      simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
    · dsimp only [linkOneOpBytes, encodeOneOp]; rw [ite_bool_true]
      simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
  | tlsLdAddr s =>
    cases relax
    · dsimp only [linkOneOpBytes, encodeOneOp]; rw [ite_bool_false]
      simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
    · dsimp only [linkOneOpBytes, encodeOneOp]; rw [ite_bool_true]
      simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
  | tlsLdLoad s =>
    cases relax
    · dsimp only [linkOneOpBytes, encodeOneOp]; rw [ite_bool_false]
      simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
    · dsimp only [linkOneOpBytes, encodeOneOp]; rw [ite_bool_true]
      simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
  | tlsGotTpOff s =>
    cases relax
    · dsimp only [linkOneOpBytes, encodeOneOp]; rw [ite_bool_false]
      simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
    · dsimp only [linkOneOpBytes, encodeOneOp]; rw [ite_bool_true]
      simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
  | ret => rfl

private theorem encodeOneOp_movImm32_relocs (pc : Nat) (dst : Gpr) (is64 : Bool) (imm : BitVec 32) :
    (encodeOneOp pc (.movImm32 dst is64 imm)).2 = [] := by
  cases is64
  · dsimp only [encodeOneOp]
    cases gprRexBit dst <;> rfl
  · rfl

private theorem encodeOneOp_movImm16_relocs (pc : Nat) (dst : Gpr) (imm : BitVec 16) :
    (encodeOneOp pc (.movImm16 dst imm)).2 = [] := by
  dsimp only [encodeOneOp]
  cases gprRexBit dst <;> rfl

private theorem encodeOneOp_movReg_relocs (pc : Nat) (dst src : Gpr) (mode : WriteMode) :
    (encodeOneOp pc (.movReg dst src mode)).2 = [] := by
  cases mode
  · rfl
  · dsimp only [encodeOneOp]
    cases (gprRexBit src || gprRexBit dst) <;> rfl
  · dsimp only [encodeOneOp]
    cases (gprRexBit src || gprRexBit dst) <;> rfl

private theorem encodeOneOp_movImm32_len_pos (dst : Gpr) (is64 : Bool) (imm : BitVec 32) :
    1 ≤ (encodeOneOp 0 (.movImm32 dst is64 imm)).1.length := by
  cases is64
  · dsimp only [encodeOneOp]
    cases gprRexBit dst
    · rw [ite_bool_false]; simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]; decide
    · rw [ite_bool_true]; simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length]; decide
  · simp only [encodeOneOp, List.length_append, List.length_cons, List.length_nil, le32Bytes_length]; decide

private theorem encodeOneOp_movImm16_len_pos (dst : Gpr) (imm : BitVec 16) :
    1 ≤ (encodeOneOp 0 (.movImm16 dst imm)).1.length := by
  dsimp only [encodeOneOp]
  cases gprRexBit dst
  · rw [ite_bool_false]; simp only [List.length_append, List.length_cons, List.length_nil, le16Bytes_length]; decide
  · rw [ite_bool_true]; simp only [List.length_append, List.length_cons, List.length_nil, le16Bytes_length]; decide

private theorem encodeOneOp_movReg_len_pos (dst src : Gpr) (mode : WriteMode) :
    1 ≤ (encodeOneOp 0 (.movReg dst src mode)).1.length := by
  cases mode
  · simp only [encodeOneOp, List.length_cons, List.length_nil]; decide
  · dsimp only [encodeOneOp]
    cases (gprRexBit src || gprRexBit dst)
    · rw [ite_bool_false]; simp only [List.length_cons, List.length_nil]; decide
    · rw [ite_bool_true]; simp only [List.length_cons, List.length_nil]; decide
  · dsimp only [encodeOneOp]
    cases (gprRexBit src || gprRexBit dst)
    · rw [ite_bool_false]; simp only [List.length_cons, List.length_nil]; decide
    · rw [ite_bool_true]; simp only [List.length_cons, List.length_nil]; decide

private theorem encodeOneOp_code_pc_indep (pc : Nat) (op : MiniMachOp) :
    (encodeOneOp pc op).1 = (encodeOneOp 0 op).1 := by
  cases op with
  | movImm32 dst is64 imm => cases is64 <;> rfl
  | movImm16 dst imm => rfl
  | movReg dst src mode => cases mode <;> rfl
  | callSym _ | leaRipSym _ | loadGotRelaxable _ | loadGotStrict _
  | tlsGdAddr _ | tlsLdAddr _ | tlsLdLoad _ | tlsGotTpOff _ | ret => rfl

private theorem encodeOpsLoop_code_pc_indep (pc : Nat) (ops : List MiniMachOp) :
    (encodeOpsLoop pc ops).1 = (encodeOpsLoop 0 ops).1 := by
  induction ops generalizing pc with
  | nil => rfl
  | cons op rest ih =>
    dsimp only [encodeOpsLoop]
    rw [encodeOneOp_code_pc_indep pc op, ih, ih (0 + (encodeOneOp 0 op).1.length)]

private theorem linkOpsLoop_length (env : LinkEnv) (vaddr : Nat) (relax : Bool)
    (ops : List MiniMachOp) :
    (linkOpsLoop env vaddr relax ops).length = (encodeOpsLoop 0 ops).1.length := by
  induction ops generalizing vaddr with
  | nil => rfl
  | cons op rest ih =>
    dsimp only [linkOpsLoop, encodeOpsLoop]
    rw [List.length_append, List.length_append, linkOneOpBytes_length, ih,
        encodeOpsLoop_code_pc_indep (0 + (encodeOneOp 0 op).1.length)]

private theorem mkInt3Pad_length (n : Nat) : (mkInt3Pad n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => dsimp only [mkInt3Pad, List.length_cons]; rw [ih]

private theorem allInt3_mkInt3Pad (n : Nat) : allInt3 (mkInt3Pad n) = true := by
  induction n with
  | zero => rfl
  | succ k ih => dsimp only [mkInt3Pad, allInt3]; rw [ih]; rfl

/-! ### Layer 3: Relocation Anchor Separation & `validateLinkedBytes` Lemmas -/

private def relocAnchorShift : Elf64RelocKind → Nat
  | .r_plt32 => 1
  | .r_pc32 | .r_gotpcrel | .r_rex_gotpcrelx | .r_gottpoff | .r_tlsld => 3
  | .r_tlsgd => 4
  | _ => 0

private def HeadRelocGe (minPc : Nat) : List Elf64Reloc → Prop
  | [] => True
  | r :: _ => minPc + relocAnchorShift r.kind ≤ r.offset

private theorem headRelocGe_mono {a b : Nat} {rels : List Elf64Reloc}
    (hle : a ≤ b) (h : HeadRelocGe b rels) : HeadRelocGe a rels := by
  cases rels with
  | nil => exact trivial
  | cons r _ =>
    exact Nat.le_trans (Nat.add_le_add_right hle (relocAnchorShift r.kind)) h

private theorem headRelocGe_append {pc : Nat} {r1 r2 : List Elf64Reloc}
    (h1 : HeadRelocGe pc r1) (h2 : HeadRelocGe pc r2) : HeadRelocGe pc (r1 ++ r2) := by
  cases r1 with
  | nil => exact h2
  | cons _ _ => exact h1

private theorem encodeOneOp_headRelocGe (pc : Nat) (op : MiniMachOp) :
    HeadRelocGe pc (encodeOneOp pc op).2 := by
  cases op with
  | movImm32 dst is64 imm => rw [encodeOneOp_movImm32_relocs]; exact trivial
  | movImm16 dst imm => rw [encodeOneOp_movImm16_relocs]; exact trivial
  | movReg dst src mode => rw [encodeOneOp_movReg_relocs]; exact trivial
  | callSym _ => exact Nat.le_refl _
  | leaRipSym _ => exact Nat.le_refl _
  | loadGotRelaxable _ => exact Nat.le_refl _
  | loadGotStrict _ => exact Nat.le_refl _
  | tlsGdAddr _ => exact Nat.le_refl _
  | tlsLdAddr _ => exact Nat.le_refl _
  | tlsLdLoad _ => exact Nat.le_refl _
  | tlsGotTpOff _ => exact Nat.le_refl _
  | ret => exact trivial

private theorem encodeOpsLoop_headRelocGe (pc : Nat) (ops : List MiniMachOp) :
    HeadRelocGe pc (encodeOpsLoop pc ops).2 := by
  induction ops generalizing pc with
  | nil => exact trivial
  | cons op rest ih =>
    dsimp only [encodeOpsLoop]
    exact headRelocGe_append (encodeOneOp_headRelocGe pc op)
      (headRelocGe_mono (Nat.le_add_right _ _) (ih (pc + (encodeOneOp pc op).1.length)))

private theorem isRelocAnchoredAt_false_of_lt {off : Nat} {rels : List Elf64Reloc}
    (h : HeadRelocGe (off + 1) rels) : isRelocAnchoredAt off rels = false := by
  cases rels with
  | nil => rfl
  | cons r rest =>
    dsimp only [HeadRelocGe] at h
    dsimp only [isRelocAnchoredAt]
    cases hk : r.kind with
    | r_plt32 =>
      rw [hk] at h; dsimp only [relocAnchorShift] at h
      have hlt : off + 1 < r.offset := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (by rw [Nat.add_assoc] at h; exact h)
      exact nat_beq_false_of_ne (Nat.ne_of_gt hlt)
    | r_pc32 | r_gotpcrel | r_rex_gotpcrelx | r_gottpoff | r_tlsld =>
      rw [hk] at h; dsimp only [relocAnchorShift] at h
      have hlt : off + 3 < r.offset := by
        have h1 : (off + 3) + 1 = (off + 1) + 3 := by rw [Nat.add_assoc]
        rw [← h1] at h
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
      exact nat_beq_false_of_ne (Nat.ne_of_gt hlt)
    | r_tlsgd =>
      rw [hk] at h; dsimp only [relocAnchorShift] at h
      have hlt : off + 4 < r.offset := by
        have h1 : (off + 4) + 1 = (off + 1) + 4 := by rw [Nat.add_assoc]
        rw [← h1] at h
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
      exact nat_beq_false_of_ne (Nat.ne_of_gt hlt)
    | r_dtpoff32 | r_64 | r_32 | r_tpoff32 => rfl

private theorem validate_plain_bytes_step (env : LinkEnv) (vaddr : Nat)
    (bs restObj : List (BitVec 8)) (rels : List Elf64Reloc) (restLnk : List (BitVec 8)) :
    ∀ (fuel off : Nat),
      bs.length ≤ fuel →
      HeadRelocGe (off + bs.length) rels →
      validateLinkedBytesLoop env vaddr fuel off (bs ++ restObj) rels (bs ++ restLnk) =
        validateLinkedBytesLoop env vaddr (fuel - bs.length) (off + bs.length) restObj rels restLnk := by
  induction bs with
  | nil =>
    intro fuel off _ _
    simp only [List.nil_append, List.length_nil, Nat.sub_zero, Nat.add_zero]
  | cons b bs ih =>
    intro fuel off hFuel hGe
    cases fuel with
    | zero =>
      dsimp only [List.length_cons] at hFuel
      exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ f =>
      dsimp only [List.length_cons] at hFuel hGe
      have hGe1 : HeadRelocGe (off + 1) rels := by
        have hle : off + 1 ≤ off + (bs.length + 1) :=
          Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) off
        exact headRelocGe_mono hle hGe
      have hNotAnch : isRelocAnchoredAt off rels = false := isRelocAnchoredAt_false_of_lt hGe1
      dsimp only [List.cons_append]
      cases rels with
      | nil =>
        dsimp only [validateLinkedBytesLoop]
        rw [hNotAnch, ite_bool_false, nat_beq_refl]
        have hGe' : HeadRelocGe ((off + 1) + bs.length) [] := trivial
        have hFuel' : bs.length ≤ f := Nat.le_of_succ_le_succ hFuel
        rw [ih f (off + 1) hFuel' hGe']
        have hsub : f + 1 - (bs.length + 1) = f - bs.length := Nat.succ_sub_succ f bs.length
        have hadd : (off + 1) + bs.length = off + (bs.length + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 bs.length]
        simp only [Bool.true_and, List.length_cons, hsub, hadd]
      | cons r rs =>
        dsimp only [validateLinkedBytesLoop]
        rw [hNotAnch, ite_bool_false, nat_beq_refl]
        have hadd : (off + 1) + bs.length = off + (bs.length + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 bs.length]
        have hGe' : HeadRelocGe ((off + 1) + bs.length) (r :: rs) := by
          rw [hadd]; exact hGe
        have hFuel' : bs.length ≤ f := Nat.le_of_succ_le_succ hFuel
        rw [ih f (off + 1) hFuel' hGe']
        have hsub : f + 1 - (bs.length + 1) = f - bs.length := Nat.succ_sub_succ f bs.length
        simp only [Bool.true_and, List.length_cons, hsub, hadd]

private theorem validate_plain_bytes_inv (env : LinkEnv) (vaddr : Nat)
    (bs restObj : List (BitVec 8)) (rels : List Elf64Reloc) :
    ∀ (fuel off : Nat) (lnk : List (BitVec 8)),
      HeadRelocGe (off + bs.length) rels →
      validateLinkedBytesLoop env vaddr fuel off (bs ++ restObj) rels lnk = true →
      ∃ restLnk fuel',
        lnk = bs ++ restLnk ∧
        fuel = fuel' + bs.length ∧
        validateLinkedBytesLoop env vaddr fuel' (off + bs.length) restObj rels restLnk = true := by
  induction bs with
  | nil =>
    intro fuel off lnk _ hVal
    exact ⟨lnk, fuel, rfl, rfl, hVal⟩
  | cons b bs ih =>
    intro fuel off lnk hGe hVal
    cases fuel with
    | zero =>
      cases rels <;> cases hVal
    | succ f =>
      dsimp only [List.length_cons] at hGe
      have hGe1 : HeadRelocGe (off + 1) rels :=
        headRelocGe_mono (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) off) hGe
      have hNotAnch : isRelocAnchoredAt off rels = false := isRelocAnchoredAt_false_of_lt hGe1
      dsimp only [List.cons_append] at hVal
      cases lnk with
      | nil =>
        cases rels with
        | nil =>
          dsimp only [validateLinkedBytesLoop] at hVal
          rw [hNotAnch, ite_bool_false] at hVal; cases hVal
        | cons r rs =>
          dsimp only [validateLinkedBytesLoop] at hVal
          rw [hNotAnch, ite_bool_false] at hVal; cases hVal
      | cons b2 restLnk0 =>
        have hStep : Nat.beq b.toNat b2.toNat = true ∧
            validateLinkedBytesLoop env vaddr f (off + 1) (bs ++ restObj) rels restLnk0 = true := by
          cases rels with
          | nil =>
            dsimp only [validateLinkedBytesLoop] at hVal
            rw [hNotAnch, ite_bool_false] at hVal
            exact bool_and_elim hVal
          | cons r rs =>
            dsimp only [validateLinkedBytesLoop] at hVal
            rw [hNotAnch, ite_bool_false] at hVal
            exact bool_and_elim hVal
        have hbEq : b = b2 := bv_eq_of_toNat (nat_eq_of_beq hStep.1)
        have hadd : (off + 1) + bs.length = off + (bs.length + 1) := by
          rw [Nat.add_assoc, Nat.add_comm 1 bs.length]
        have hGe' : HeadRelocGe ((off + 1) + bs.length) rels := by rw [hadd]; exact hGe
        have ⟨restLnk, fuel', hLnkEq, hFuelEq, hValRest⟩ := ih f (off + 1) restLnk0 hGe' hStep.2
        rw [hadd] at hValRest
        refine ⟨restLnk, fuel', ?_, ?_, hValRest⟩
        · rw [← hbEq, hLnkEq]; rfl
        · rw [hFuelEq]; rfl

private theorem enc_callSym (off s : Nat) :
    encodeOneOp off (.callSym s) =
      (tmplCall, [{ offset := off + 1, kind := .r_plt32, sym := s, addend := Int.negSucc 3 }]) := rfl
private theorem enc_leaRipSym (off s : Nat) :
    encodeOneOp off (.leaRipSym s) =
      (tmplLeaRip, [{ offset := off + 3, kind := .r_pc32, sym := s, addend := Int.negSucc 3 }]) := rfl
private theorem enc_loadGotStrict (off s : Nat) :
    encodeOneOp off (.loadGotStrict s) =
      (tmplMovRip, [{ offset := off + 3, kind := .r_gotpcrel, sym := s, addend := Int.negSucc 3 }]) := rfl
private theorem enc_loadGotRelaxable (off s : Nat) :
    encodeOneOp off (.loadGotRelaxable s) =
      (tmplMovRip, [{ offset := off + 3, kind := .r_rex_gotpcrelx, sym := s, addend := Int.negSucc 3 }]) := rfl
private theorem enc_tlsGotTpOff (off s : Nat) :
    encodeOneOp off (.tlsGotTpOff s) =
      (tmplMovRip, [{ offset := off + 3, kind := .r_gottpoff, sym := s, addend := Int.negSucc 3 }]) := rfl
private theorem enc_tlsGdAddr (off s : Nat) :
    encodeOneOp off (.tlsGdAddr s) =
      (tmplTlsGdObj,
       [{ offset := off + 4, kind := .r_tlsgd, sym := s, addend := Int.negSucc 3 },
        { offset := off + 12, kind := .r_plt32, sym := 0, addend := Int.negSucc 3 }]) := rfl
private theorem enc_tlsLdAddr (off s : Nat) :
    encodeOneOp off (.tlsLdAddr s) =
      (tmplTlsLdObj 0x8D,
       [{ offset := off + 3, kind := .r_tlsld, sym := s, addend := Int.negSucc 3 },
        { offset := off + 8, kind := .r_plt32, sym := 0, addend := Int.negSucc 3 },
        { offset := off + 15, kind := .r_dtpoff32, sym := s, addend := Int.ofNat 0 }]) := rfl
private theorem enc_tlsLdLoad (off s : Nat) :
    encodeOneOp off (.tlsLdLoad s) =
      (tmplTlsLdObj 0x8B,
       [{ offset := off + 3, kind := .r_tlsld, sym := s, addend := Int.negSucc 3 },
        { offset := off + 8, kind := .r_plt32, sym := 0, addend := Int.negSucc 3 },
        { offset := off + 15, kind := .r_dtpoff32, sym := s, addend := Int.ofNat 0 }]) := rfl
private theorem tmplCall_len : tmplCall.length = 5 := rfl
private theorem tmplLeaRip_len : tmplLeaRip.length = 7 := rfl
private theorem tmplMovRip_len : tmplMovRip.length = 7 := rfl
private theorem tmplTlsGdObj_len : tmplTlsGdObj.length = 16 := rfl
private theorem tmplTlsLdObj_len (b : Nat) : (tmplTlsLdObj b).length = 19 := rfl

private theorem anch_plt32 (off s : Nat) (a : Int) (rs : List Elf64Reloc) :
    isRelocAnchoredAt off ({ offset := off + 1, kind := .r_plt32, sym := s, addend := a } :: rs) = true :=
  nat_beq_refl _
private theorem anch_pc32 (off s : Nat) (a : Int) (rs : List Elf64Reloc) :
    isRelocAnchoredAt off ({ offset := off + 3, kind := .r_pc32, sym := s, addend := a } :: rs) = true :=
  nat_beq_refl _
private theorem anch_gotpcrel (off s : Nat) (a : Int) (rs : List Elf64Reloc) :
    isRelocAnchoredAt off ({ offset := off + 3, kind := .r_gotpcrel, sym := s, addend := a } :: rs) = true :=
  nat_beq_refl _
private theorem anch_rex_gotpcrelx (off s : Nat) (a : Int) (rs : List Elf64Reloc) :
    isRelocAnchoredAt off ({ offset := off + 3, kind := .r_rex_gotpcrelx, sym := s, addend := a } :: rs) = true :=
  nat_beq_refl _
private theorem anch_gottpoff (off s : Nat) (a : Int) (rs : List Elf64Reloc) :
    isRelocAnchoredAt off ({ offset := off + 3, kind := .r_gottpoff, sym := s, addend := a } :: rs) = true :=
  nat_beq_refl _
private theorem anch_tlsld (off s : Nat) (a : Int) (rs : List Elf64Reloc) :
    isRelocAnchoredAt off ({ offset := off + 3, kind := .r_tlsld, sym := s, addend := a } :: rs) = true :=
  nat_beq_refl _
private theorem anch_tlsgd (off s : Nat) (a : Int) (rs : List Elf64Reloc) :
    isRelocAnchoredAt off ({ offset := off + 4, kind := .r_tlsgd, sym := s, addend := a } :: rs) = true :=
  nat_beq_refl _

private theorem validateLinkedBytesLoop_cons_reloc (env : LinkEnv) (vaddr f off : Nat)
    (obj : List (BitVec 8)) (r : Elf64Reloc) (rs : List Elf64Reloc) (lnk : List (BitVec 8)) :
    validateLinkedBytesLoop env vaddr (f + 1) off obj (r :: rs) lnk =
      if isRelocAnchoredAt off (r :: rs) then
        match matchRelocAtOff env off obj (r :: rs) lnk with
        | some (n, rem) =>
          validateLinkedBytesLoop env vaddr f (off + n) (obj.drop n) rem (lnk.drop n)
        | none =>
          match matchSingleRelocAtOff env vaddr off obj r rs lnk with
          | some (n, rem) =>
            validateLinkedBytesLoop env vaddr f (off + n) (obj.drop n) rem (lnk.drop n)
          | none => false
      else
        match obj, lnk with
        | b1 :: bs1, b2 :: bs2 =>
          Nat.beq b1.toNat b2.toNat &&
            validateLinkedBytesLoop env vaddr f (off + 1) bs1 (r :: rs) bs2
        | _, _ => false := by
  cases obj <;> rfl

private theorem checkPrefixEq_tlsLd_8D_8B (xs : List (BitVec 8)) :
    checkPrefixEq (tmplTlsLdObj 0x8D) (tmplTlsLdObj 0x8B ++ xs) = false := by
  dsimp only [checkPrefixEq]
  have h19 : (tmplTlsLdObj 0x8D).length ≤ (tmplTlsLdObj 0x8B ++ xs).length := by
    rw [List.length_append, tmplTlsLdObj_len, tmplTlsLdObj_len]; exact Nat.le_add_right 19 _
  rw [nat_ble_of_le h19]; rfl

private theorem checkPrefixEq_tlsLd_8B_8D (xs : List (BitVec 8)) :
    checkPrefixEq (tmplTlsLdObj 0x8B) (tmplTlsLdObj 0x8D ++ xs) = false := by
  dsimp only [checkPrefixEq]
  have h19 : (tmplTlsLdObj 0x8B).length ≤ (tmplTlsLdObj 0x8D ++ xs).length := by
    rw [List.length_append, tmplTlsLdObj_len, tmplTlsLdObj_len]; exact Nat.le_add_right 19 _
  rw [nat_ble_of_le h19]; rfl

private theorem validate_complete_loop (env : LinkEnv) (vaddr padBytes : Nat) (relax : Bool)
    (ops : List MiniMachOp) (hMode : OpsValidForRelaxMode relax ops) :
    ∀ (fuel off : Nat),
      (encodeOpsLoop off ops).1.length ≤ fuel →
      validateLinkedBytesLoop env vaddr fuel off (encodeOpsLoop off ops).1
        (encodeOpsLoop off ops).2 (linkOpsLoop env (vaddr + off) relax ops ++ mkInt3Pad padBytes) = true := by
  induction hMode with
  | nil =>
    intro fuel off _
    cases fuel <;> exact allInt3_mkInt3Pad padBytes
  | @cons op rest hOpMode hRestMode ih =>
    intro fuel off hFuel
    dsimp only [encodeOpsLoop, linkOpsLoop] at hFuel; dsimp only [encodeOpsLoop, linkOpsLoop]
    rw [List.append_assoc]
    have hGeRest : HeadRelocGe (off + (encodeOneOp off op).1.length)
        (encodeOpsLoop (off + (encodeOneOp off op).1.length) rest).2 :=
      encodeOpsLoop_headRelocGe _ rest
    have hLenCur : (linkOneOpBytes env (vaddr + off) relax op).length = (encodeOneOp off op).1.length := by
      rw [linkOneOpBytes_length, encodeOneOp_code_pc_indep off op]
    rw [hLenCur, Nat.add_assoc vaddr off]
    cases op with
    | movImm32 dst is64 imm =>
      have hEq : linkOneOpBytes env (vaddr + off) relax (.movImm32 dst is64 imm) =
          (encodeOneOp off (.movImm32 dst is64 imm)).1 := by
        dsimp only [linkOneOpBytes]; exact Eq.symm (encodeOneOp_code_pc_indep off _)
      rw [hEq]
      have hRelNil : (encodeOneOp off (.movImm32 dst is64 imm)).2 = [] :=
        encodeOneOp_movImm32_relocs off dst is64 imm
      rw [hRelNil, List.nil_append]
      rw [List.length_append] at hFuel
      have hLe1 : (encodeOneOp off (.movImm32 dst is64 imm)).1.length ≤ fuel :=
        Nat.le_trans (Nat.le_add_right _ _) hFuel
      rw [validate_plain_bytes_step env vaddr _ _ _ _ fuel off hLe1 hGeRest]
      exact ih (fuel - (encodeOneOp off (.movImm32 dst is64 imm)).1.length) _ (nat_le_sub_of_add_le_left hFuel)
    | movImm16 dst imm =>
      have hEq : linkOneOpBytes env (vaddr + off) relax (.movImm16 dst imm) =
          (encodeOneOp off (.movImm16 dst imm)).1 := by
        dsimp only [linkOneOpBytes]; exact Eq.symm (encodeOneOp_code_pc_indep off _)
      rw [hEq]
      have hRelNil : (encodeOneOp off (.movImm16 dst imm)).2 = [] :=
        encodeOneOp_movImm16_relocs off dst imm
      rw [hRelNil, List.nil_append]
      rw [List.length_append] at hFuel
      have hLe1 : (encodeOneOp off (.movImm16 dst imm)).1.length ≤ fuel :=
        Nat.le_trans (Nat.le_add_right _ _) hFuel
      rw [validate_plain_bytes_step env vaddr _ _ _ _ fuel off hLe1 hGeRest]
      exact ih (fuel - (encodeOneOp off (.movImm16 dst imm)).1.length) _ (nat_le_sub_of_add_le_left hFuel)
    | movReg dst src mode =>
      have hEq : linkOneOpBytes env (vaddr + off) relax (.movReg dst src mode) =
          (encodeOneOp off (.movReg dst src mode)).1 := by
        dsimp only [linkOneOpBytes]; exact Eq.symm (encodeOneOp_code_pc_indep off _)
      rw [hEq]
      have hRelNil : (encodeOneOp off (.movReg dst src mode)).2 = [] :=
        encodeOneOp_movReg_relocs off dst src mode
      rw [hRelNil, List.nil_append]
      rw [List.length_append] at hFuel
      have hLe1 : (encodeOneOp off (.movReg dst src mode)).1.length ≤ fuel :=
        Nat.le_trans (Nat.le_add_right _ _) hFuel
      rw [validate_plain_bytes_step env vaddr _ _ _ _ fuel off hLe1 hGeRest]
      exact ih (fuel - (encodeOneOp off (.movReg dst src mode)).1.length) _ (nat_le_sub_of_add_le_left hFuel)
    | ret =>
      rw [List.length_append] at hFuel
      have hLe1 : (encodeOneOp off .ret).1.length ≤ fuel :=
        Nat.le_trans (Nat.le_add_right _ _) hFuel
      dsimp only [linkOneOpBytes, encodeOneOp] at hFuel hLe1 hGeRest; dsimp only [linkOneOpBytes, encodeOneOp]
      rw [List.nil_append]
      rw [validate_plain_bytes_step env vaddr _ _ _ _ fuel off hLe1 hGeRest]
      exact ih (fuel - 1) (off + 1) (nat_le_sub_of_add_le_left hFuel)
    | callSym s =>
      cases fuel with
      | zero => dsimp only [encodeOneOp, List.length_append, List.length_cons] at hFuel; exact False.elim (Nat.not_succ_le_zero _ hFuel)
      | succ f =>
        rw [enc_callSym] at hFuel; simp only [tmplCall_len] at hFuel; rw [enc_callSym]; simp only [tmplCall_len]; dsimp only [linkOneOpBytes]
        rw [reloc_cons_append]
        have hFuelRest : (encodeOpsLoop (off + 5) rest).1.length ≤ f := by
          rw [List.length_append] at hFuel
          exact nat_le_of_add_succ_le_succ hFuel
        rw [validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_plt32 _ _ _ _)]
        have hNone : matchRelocAtOff env off (tmplCall ++ (encodeOpsLoop (off + 5) rest).1)
            ({ offset := off + 1, kind := .r_plt32, sym := s, addend := Int.negSucc 3 } ::
              (encodeOpsLoop (off + 5) rest).2)
            (([BitVec.ofNat 8 0xE8] ++ le32Bytes (rel32Disp (vaddr + off + 1) (env.symAddr s))) ++
              (linkOpsLoop env (vaddr + (off + 5)) relax rest ++ mkInt3Pad padBytes)) = none := by
          cases (encodeOpsLoop (off + 5) rest).2 with
          | nil => rfl
          | cons r2 rs2 => cases rs2 <;> rfl
        rw [hNone]
        dsimp only [matchSingleRelocAtOff]
        rw [ite_bool_eq_true (nat_beq_refl (off + 1))]
        have hChk : (checkPrefixEq tmplCall (tmplCall ++ (encodeOpsLoop (off + 5) rest).1) &&
            checkPrefixEq ([BitVec.ofNat 8 0xE8] ++ le32Bytes (rel32Disp (vaddr + off + 1) (env.symAddr s)))
              (([BitVec.ofNat 8 0xE8] ++ le32Bytes (rel32Disp (vaddr + off + 1) (env.symAddr s))) ++
                (linkOpsLoop env (vaddr + (off + 5)) relax rest ++ mkInt3Pad padBytes))) = true := by
          rw [checkPrefixEq_append, checkPrefixEq_append]; rfl
        rw [ite_bool_eq_true hChk]; dsimp only
        have hDrop1 : (tmplCall ++ (encodeOpsLoop (off + 5) rest).1).drop 5 = (encodeOpsLoop (off + 5) rest).1 :=
          list_drop_append_of_len tmplCall _ tmplCall_len
        have hDrop2 : (([BitVec.ofNat 8 0xE8] ++ le32Bytes (rel32Disp (vaddr + off + 1) (env.symAddr s))) ++
            (linkOpsLoop env (vaddr + (off + 5)) relax rest ++ mkInt3Pad padBytes)).drop 5 =
            linkOpsLoop env (vaddr + (off + 5)) relax rest ++ mkInt3Pad padBytes :=
          list_drop_append_of_len ([BitVec.ofNat 8 0xE8] ++ le32Bytes (rel32Disp (vaddr + off + 1) (env.symAddr s))) _
            (by simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length])
        rw [hDrop1, hDrop2]
        exact ih f (off + 5) hFuelRest
    | leaRipSym s =>
      cases fuel with
      | zero => dsimp only [encodeOneOp, List.length_append, List.length_cons] at hFuel; exact False.elim (Nat.not_succ_le_zero _ hFuel)
      | succ f =>
        rw [enc_leaRipSym] at hFuel; simp only [tmplLeaRip_len] at hFuel; rw [enc_leaRipSym]; simp only [tmplLeaRip_len]; dsimp only [linkOneOpBytes]
        rw [reloc_cons_append]
        have hFuelRest : (encodeOpsLoop (off + 7) rest).1.length ≤ f := by
          rw [List.length_append] at hFuel
          exact nat_le_of_add_succ_le_succ hFuel
        rw [validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_pc32 _ _ _ _)]
        have hNone : matchRelocAtOff env off (tmplLeaRip ++ (encodeOpsLoop (off + 7) rest).1)
            ({ offset := off + 3, kind := .r_pc32, sym := s, addend := Int.negSucc 3 } ::
              (encodeOpsLoop (off + 7) rest).2)
            (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr s))) ++
              (linkOpsLoop env (vaddr + (off + 7)) relax rest ++ mkInt3Pad padBytes)) = none := by
          cases (encodeOpsLoop (off + 7) rest).2 with
          | nil => rfl
          | cons r2 rs2 => cases rs2 <;> rfl
        rw [hNone]
        dsimp only [matchSingleRelocAtOff]
        rw [ite_bool_eq_true (nat_beq_refl (off + 3))]
        have hChk : (checkPrefixEq tmplLeaRip (tmplLeaRip ++ (encodeOpsLoop (off + 7) rest).1) &&
            checkPrefixEq ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr s)))
              (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr s))) ++
                (linkOpsLoop env (vaddr + (off + 7)) relax rest ++ mkInt3Pad padBytes))) = true := by
          rw [checkPrefixEq_append, checkPrefixEq_append]; rfl
        rw [ite_bool_eq_true hChk]; dsimp only
        have hDrop1 : (tmplLeaRip ++ (encodeOpsLoop (off + 7) rest).1).drop 7 = (encodeOpsLoop (off + 7) rest).1 :=
          list_drop_append_of_len tmplLeaRip _ tmplLeaRip_len
        have hDrop2 : (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr s))) ++
            (linkOpsLoop env (vaddr + (off + 7)) relax rest ++ mkInt3Pad padBytes)).drop 7 =
            linkOpsLoop env (vaddr + (off + 7)) relax rest ++ mkInt3Pad padBytes :=
          list_drop_append_of_len _ _
            (by simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length])
        rw [hDrop1, hDrop2]
        exact ih f (off + 7) hFuelRest
    | loadGotStrict s =>
      cases fuel with
      | zero => dsimp only [encodeOneOp, List.length_append, List.length_cons] at hFuel; exact False.elim (Nat.not_succ_le_zero _ hFuel)
      | succ f =>
        rw [enc_loadGotStrict] at hFuel; simp only [tmplMovRip_len] at hFuel; rw [enc_loadGotStrict]; simp only [tmplMovRip_len]; dsimp only [linkOneOpBytes]
        rw [reloc_cons_append]
        have hFuelRest : (encodeOpsLoop (off + 7) rest).1.length ≤ f := by
          rw [List.length_append] at hFuel
          exact nat_le_of_add_succ_le_succ hFuel
        rw [validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_gotpcrel _ _ _ _)]
        have hNone : matchRelocAtOff env off (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1)
            ({ offset := off + 3, kind := .r_gotpcrel, sym := s, addend := Int.negSucc 3 } ::
              (encodeOpsLoop (off + 7) rest).2)
            (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr s))) ++
              (linkOpsLoop env (vaddr + (off + 7)) relax rest ++ mkInt3Pad padBytes)) = none := by
          cases (encodeOpsLoop (off + 7) rest).2 with
          | nil => rfl
          | cons r2 rs2 => cases rs2 <;> rfl
        rw [hNone]
        dsimp only [matchSingleRelocAtOff]
        rw [ite_bool_eq_true (nat_beq_refl (off + 3))]
        have hChk : (checkPrefixEq tmplMovRip (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1) &&
            checkPrefixEq ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr s)))
              (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr s))) ++
                (linkOpsLoop env (vaddr + (off + 7)) relax rest ++ mkInt3Pad padBytes))) = true := by
          rw [checkPrefixEq_append, checkPrefixEq_append]; rfl
        rw [ite_bool_eq_true hChk]; dsimp only
        rw [list_drop_append_of_len tmplMovRip _ tmplMovRip_len, list_drop_append_of_len ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes _) _ (by simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length])]
        exact ih f (off + 7) hFuelRest
    | loadGotRelaxable s =>
      cases fuel with
      | zero => dsimp only [encodeOneOp, List.length_append, List.length_cons] at hFuel; exact False.elim (Nat.not_succ_le_zero _ hFuel)
      | succ f =>
        rw [enc_loadGotRelaxable] at hFuel; simp only [tmplMovRip_len] at hFuel; rw [enc_loadGotRelaxable]; simp only [tmplMovRip_len]; dsimp only [linkOneOpBytes]
        rw [reloc_cons_append]
        have hFuelRest : (encodeOpsLoop (off + 7) rest).1.length ≤ f := by
          rw [List.length_append] at hFuel
          exact nat_le_of_add_succ_le_succ hFuel
        cases relax with
        | true =>
          rw [ite_bool_true, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_rex_gotpcrelx _ _ _ _)]
          have hNone : matchRelocAtOff env off (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1)
              ({ offset := off + 3, kind := .r_rex_gotpcrelx, sym := s, addend := Int.negSucc 3 } ::
                (encodeOpsLoop (off + 7) rest).2)
              (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr s))) ++
                (linkOpsLoop env (vaddr + (off + 7)) true rest ++ mkInt3Pad padBytes)) = none := by
            cases (encodeOpsLoop (off + 7) rest).2 with
            | nil => rfl
            | cons r2 rs2 => cases rs2 <;> rfl
          rw [hNone]
          dsimp only [matchSingleRelocAtOff]
          rw [ite_bool_eq_true (nat_beq_refl (off + 3))]
          have hChk : (checkPrefixEq tmplMovRip (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1) &&
              (checkPrefixEq ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr s)))
                (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr s))) ++
                  (linkOpsLoop env (vaddr + (off + 7)) true rest ++ mkInt3Pad padBytes)) ||
               checkPrefixEq ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr s)))
                (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr s))) ++
                  (linkOpsLoop env (vaddr + (off + 7)) true rest ++ mkInt3Pad padBytes)))) = true := by
            rw [checkPrefixEq_append, checkPrefixEq_append]; rfl
          rw [ite_bool_eq_true hChk]; dsimp only
          rw [list_drop_append_of_len tmplMovRip _ tmplMovRip_len, list_drop_append_of_len ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++ le32Bytes _) _ (by simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length])]
          exact ih f (off + 7) hFuelRest
        | false =>
          rw [ite_bool_false, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_rex_gotpcrelx _ _ _ _)]
          have hNone : matchRelocAtOff env off (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1)
              ({ offset := off + 3, kind := .r_rex_gotpcrelx, sym := s, addend := Int.negSucc 3 } ::
                (encodeOpsLoop (off + 7) rest).2)
              (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr s))) ++
                (linkOpsLoop env (vaddr + (off + 7)) false rest ++ mkInt3Pad padBytes)) = none := by
            cases (encodeOpsLoop (off + 7) rest).2 with
            | nil => rfl
            | cons r2 rs2 => cases rs2 <;> rfl
          rw [hNone]
          dsimp only [matchSingleRelocAtOff]
          rw [ite_bool_eq_true (nat_beq_refl (off + 3))]
          have hChk : (checkPrefixEq tmplMovRip (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1) &&
              (checkPrefixEq ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr s)))
                (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr s))) ++
                  (linkOpsLoop env (vaddr + (off + 7)) false rest ++ mkInt3Pad padBytes)) ||
               checkPrefixEq ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr s)))
                (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr s))) ++
                  (linkOpsLoop env (vaddr + (off + 7)) false rest ++ mkInt3Pad padBytes)))) = true := by
            rw [checkPrefixEq_append, checkPrefixEq_append, Bool.or_true]; rfl
          rw [ite_bool_eq_true hChk]; dsimp only
          rw [list_drop_append_of_len tmplMovRip _ tmplMovRip_len, list_drop_append_of_len ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes _) _ (by simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length])]
          exact ih f (off + 7) hFuelRest
    | tlsGotTpOff s =>
      cases fuel with
      | zero => dsimp only [encodeOneOp, List.length_append, List.length_cons] at hFuel; exact False.elim (Nat.not_succ_le_zero _ hFuel)
      | succ f =>
        rw [enc_tlsGotTpOff] at hFuel; simp only [tmplMovRip_len] at hFuel; rw [enc_tlsGotTpOff]; simp only [tmplMovRip_len]; dsimp only [linkOneOpBytes]
        rw [reloc_cons_append]
        have hFuelRest : (encodeOpsLoop (off + 7) rest).1.length ≤ f := by
          rw [List.length_append] at hFuel
          exact nat_le_of_add_succ_le_succ hFuel
        cases relax with
        | true =>
          rw [ite_bool_true, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_gottpoff _ _ _ _)]
          have hNone : matchRelocAtOff env off (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1)
              ({ offset := off + 3, kind := .r_gottpoff, sym := s, addend := Int.negSucc 3 } ::
                (encodeOpsLoop (off + 7) rest).2)
              (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xC7, BitVec.ofNat 8 0xC0] ++ le32Bytes (env.tlsTpOff s)) ++
                (linkOpsLoop env (vaddr + (off + 7)) true rest ++ mkInt3Pad padBytes)) = none := by
            cases (encodeOpsLoop (off + 7) rest).2 with
            | nil => rfl
            | cons r2 rs2 => cases rs2 <;> rfl
          rw [hNone]
          dsimp only [matchSingleRelocAtOff]
          rw [ite_bool_eq_true (nat_beq_refl (off + 3))]
          have hChk : (checkPrefixEq tmplMovRip (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1) &&
              (checkPrefixEq ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xC7, BitVec.ofNat 8 0xC0] ++ le32Bytes (env.tlsTpOff s))
                (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xC7, BitVec.ofNat 8 0xC0] ++ le32Bytes (env.tlsTpOff s)) ++
                  (linkOpsLoop env (vaddr + (off + 7)) true rest ++ mkInt3Pad padBytes)) ||
               checkPrefixEq ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotTpOffSlotAddr s)))
                (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xC7, BitVec.ofNat 8 0xC0] ++ le32Bytes (env.tlsTpOff s)) ++
                  (linkOpsLoop env (vaddr + (off + 7)) true rest ++ mkInt3Pad padBytes)))) = true := by
            rw [checkPrefixEq_append, checkPrefixEq_append]; rfl
          rw [ite_bool_eq_true hChk]; dsimp only
          rw [list_drop_append_of_len tmplMovRip _ tmplMovRip_len, list_drop_append_of_len ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xC7, BitVec.ofNat 8 0xC0] ++ le32Bytes _) _ (by simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length])]
          exact ih f (off + 7) hFuelRest
        | false =>
          rw [ite_bool_false, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_gottpoff _ _ _ _)]
          have hNone : matchRelocAtOff env off (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1)
              ({ offset := off + 3, kind := .r_gottpoff, sym := s, addend := Int.negSucc 3 } ::
                (encodeOpsLoop (off + 7) rest).2)
              (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotTpOffSlotAddr s))) ++
                (linkOpsLoop env (vaddr + (off + 7)) false rest ++ mkInt3Pad padBytes)) = none := by
            cases (encodeOpsLoop (off + 7) rest).2 with
            | nil => rfl
            | cons r2 rs2 => cases rs2 <;> rfl
          rw [hNone]
          dsimp only [matchSingleRelocAtOff]
          rw [ite_bool_eq_true (nat_beq_refl (off + 3))]
          have hChk : (checkPrefixEq tmplMovRip (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1) &&
              (checkPrefixEq ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xC7, BitVec.ofNat 8 0xC0] ++ le32Bytes (env.tlsTpOff s))
                (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotTpOffSlotAddr s))) ++
                  (linkOpsLoop env (vaddr + (off + 7)) false rest ++ mkInt3Pad padBytes)) ||
               checkPrefixEq ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotTpOffSlotAddr s)))
                (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes (rel32Disp (vaddr + off + 3) (env.gotTpOffSlotAddr s))) ++
                  (linkOpsLoop env (vaddr + (off + 7)) false rest ++ mkInt3Pad padBytes)))) = true := by
            rw [checkPrefixEq_append, checkPrefixEq_append, Bool.or_true]; rfl
          rw [ite_bool_eq_true hChk]; dsimp only
          rw [list_drop_append_of_len tmplMovRip _ tmplMovRip_len, list_drop_append_of_len ([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes _) _ (by simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length])]
          exact ih f (off + 7) hFuelRest
    | tlsGdAddr s =>
      have hr : relax = true := hOpMode
      subst hr
      cases fuel with
      | zero => dsimp only [encodeOneOp, List.length_append, List.length_cons] at hFuel; exact False.elim (Nat.not_succ_le_zero _ hFuel)
      | succ f =>
        rw [enc_tlsGdAddr] at hFuel; simp only [tmplTlsGdObj_len] at hFuel; rw [enc_tlsGdAddr]; simp only [tmplTlsGdObj_len]; dsimp only [linkOneOpBytes]
        rw [ite_bool_true, reloc_cons2_append]
        have hFuelRest : (encodeOpsLoop (off + 16) rest).1.length ≤ f := by
          rw [List.length_append] at hFuel
          exact nat_le_of_add_succ_le_succ hFuel
        rw [validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_tlsgd _ _ _ _)]
        let expGd :=
          [BitVec.ofNat 8 0x64, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04,
           BitVec.ofNat 8 0x25, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
           BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
        have hOffGd : (Nat.beq (off + 4) (off + 4) && Nat.beq (off + 12) (off + 12)) = true := by
          rw [nat_beq_refl, nat_beq_refl]; rfl
        have hChkGd : (checkPrefixEq tmplTlsGdObj (tmplTlsGdObj ++ (encodeOpsLoop (off + 16) rest).1) &&
            checkPrefixEq expGd (expGd ++ (linkOpsLoop env (vaddr + (off + 16)) true rest ++ mkInt3Pad padBytes))) = true := by
          rw [checkPrefixEq_append, checkPrefixEq_append]; rfl
        have hMatch : matchRelocAtOff env off (tmplTlsGdObj ++ (encodeOpsLoop (off + 16) rest).1)
            ({ offset := off + 4, kind := .r_tlsgd, sym := s, addend := Int.negSucc 3 } ::
             { offset := off + 12, kind := .r_plt32, sym := 0, addend := Int.negSucc 3 } ::
              (encodeOpsLoop (off + 16) rest).2)
            (expGd ++ (linkOpsLoop env (vaddr + (off + 16)) true rest ++ mkInt3Pad padBytes)) =
            some (16, (encodeOpsLoop (off + 16) rest).2) := by
          cases (encodeOpsLoop (off + 16) rest).2 with
          | nil =>
            dsimp only [matchRelocAtOff]
            rw [ite_bool_eq_true hOffGd, ite_bool_eq_true hChkGd]
          | cons r3 rs3 =>
            dsimp only [matchRelocAtOff]
            rw [ite_bool_eq_true hOffGd, ite_bool_eq_true hChkGd]
        rw [hMatch]; dsimp only
        rw [list_drop_append_of_len tmplTlsGdObj _ tmplTlsGdObj_len, list_drop_append_of_len expGd _ (by simp only [expGd, List.length_append, List.length_cons, List.length_nil, le32Bytes_length])]
        exact ih f (off + 16) hFuelRest
    | tlsLdAddr s =>
      have hr : relax = true := hOpMode
      subst hr
      cases fuel with
      | zero => dsimp only [encodeOneOp, List.length_append, List.length_cons] at hFuel; exact False.elim (Nat.not_succ_le_zero _ hFuel)
      | succ f =>
        rw [enc_tlsLdAddr] at hFuel; simp only [tmplTlsLdObj_len] at hFuel; rw [enc_tlsLdAddr]; simp only [tmplTlsLdObj_len]; dsimp only [linkOneOpBytes]
        rw [ite_bool_true, reloc_cons3_append]
        have hFuelRest : (encodeOpsLoop (off + 19) rest).1.length ≤ f := by
          rw [List.length_append] at hFuel
          exact nat_le_of_add_succ_le_succ hFuel
        rw [validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_tlsld _ _ _ _)]
        let lePrefix :=
          [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64,
           BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25,
           BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0]
        let expLea := lePrefix ++ [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
        let lnkLea :=
          [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64,
           BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25,
           BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
           BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
        have hExpLeaEq : expLea = lnkLea := rfl
        have hOffLd : (Nat.beq (off + 3) (off + 3) && Nat.beq (off + 8) (off + 8) &&
            Nat.beq (off + 15) (off + 15) && Nat.beq s s) = true := by
          rw [nat_beq_refl, nat_beq_refl, nat_beq_refl, nat_beq_refl]; rfl
        have hChkLea : (checkPrefixEq (tmplTlsLdObj 0x8D) (tmplTlsLdObj 0x8D ++ (encodeOpsLoop (off + 19) rest).1) &&
            checkPrefixEq expLea (lnkLea ++ (linkOpsLoop env (vaddr + (off + 19)) true rest ++ mkInt3Pad padBytes))) = true := by
          rw [hExpLeaEq, checkPrefixEq_append, checkPrefixEq_append]; rfl
        have hMatch : matchRelocAtOff env off (tmplTlsLdObj 0x8D ++ (encodeOpsLoop (off + 19) rest).1)
            ({ offset := off + 3, kind := .r_tlsld, sym := s, addend := Int.negSucc 3 } ::
             { offset := off + 8, kind := .r_plt32, sym := 0, addend := Int.negSucc 3 } ::
             { offset := off + 15, kind := .r_dtpoff32, sym := s, addend := Int.ofNat 0 } ::
              (encodeOpsLoop (off + 19) rest).2)
            (lnkLea ++ (linkOpsLoop env (vaddr + (off + 19)) true rest ++ mkInt3Pad padBytes)) =
            some (19, (encodeOpsLoop (off + 19) rest).2) := by
          dsimp only [matchRelocAtOff]
          rw [ite_bool_eq_true hOffLd, ite_bool_eq_true hChkLea]
        rw [hMatch]; dsimp only
        rw [list_drop_append_of_len (tmplTlsLdObj 0x8D) _ (tmplTlsLdObj_len 0x8D), list_drop_append_of_len ([BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)) _ (by simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length])]
        exact ih f (off + 19) hFuelRest
    | tlsLdLoad s =>
      have hr : relax = true := hOpMode
      subst hr
      cases fuel with
      | zero => dsimp only [encodeOneOp, List.length_append, List.length_cons] at hFuel; exact False.elim (Nat.not_succ_le_zero _ hFuel)
      | succ f =>
        rw [enc_tlsLdLoad] at hFuel; simp only [tmplTlsLdObj_len] at hFuel; rw [enc_tlsLdLoad]; simp only [tmplTlsLdObj_len]; dsimp only [linkOneOpBytes]
        rw [ite_bool_true, reloc_cons3_append]
        have hFuelRest : (encodeOpsLoop (off + 19) rest).1.length ≤ f := by
          rw [List.length_append] at hFuel
          exact nat_le_of_add_succ_le_succ hFuel
        rw [validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_tlsld _ _ _ _)]
        let lePrefix :=
          [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64,
           BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25,
           BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0]
        let expLea := lePrefix ++ [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
        let expMov := lePrefix ++ [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
        let lnkMov :=
          [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64,
           BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25,
           BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
           BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
        have hExpMovEq : expMov = lnkMov := rfl
        have hOffLd : (Nat.beq (off + 3) (off + 3) && Nat.beq (off + 8) (off + 8) &&
            Nat.beq (off + 15) (off + 15) && Nat.beq s s) = true := by
          rw [nat_beq_refl, nat_beq_refl, nat_beq_refl, nat_beq_refl]; rfl
        have hNot8D : (checkPrefixEq (tmplTlsLdObj 0x8D) (tmplTlsLdObj 0x8B ++ (encodeOpsLoop (off + 19) rest).1) &&
            checkPrefixEq expLea (lnkMov ++ (linkOpsLoop env (vaddr + (off + 19)) true rest ++ mkInt3Pad padBytes))) = false := by
          rw [checkPrefixEq_tlsLd_8D_8B]; rfl
        have hChkMov : (checkPrefixEq (tmplTlsLdObj 0x8B) (tmplTlsLdObj 0x8B ++ (encodeOpsLoop (off + 19) rest).1) &&
            checkPrefixEq expMov (lnkMov ++ (linkOpsLoop env (vaddr + (off + 19)) true rest ++ mkInt3Pad padBytes))) = true := by
          rw [hExpMovEq, checkPrefixEq_append, checkPrefixEq_append]; rfl
        have hMatch : matchRelocAtOff env off (tmplTlsLdObj 0x8B ++ (encodeOpsLoop (off + 19) rest).1)
            ({ offset := off + 3, kind := .r_tlsld, sym := s, addend := Int.negSucc 3 } ::
             { offset := off + 8, kind := .r_plt32, sym := 0, addend := Int.negSucc 3 } ::
             { offset := off + 15, kind := .r_dtpoff32, sym := s, addend := Int.ofNat 0 } ::
              (encodeOpsLoop (off + 19) rest).2)
            (lnkMov ++ (linkOpsLoop env (vaddr + (off + 19)) true rest ++ mkInt3Pad padBytes)) =
            some (19, (encodeOpsLoop (off + 19) rest).2) := by
          dsimp only [matchRelocAtOff]
          rw [ite_bool_eq_true hOffLd, ite_bool_eq_false hNot8D, ite_bool_eq_true hChkMov]
        rw [hMatch]; dsimp only
        rw [list_drop_append_of_len (tmplTlsLdObj 0x8B) _ (tmplTlsLdObj_len 0x8B), list_drop_append_of_len ([BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)) _ (by simp only [List.length_append, List.length_cons, List.length_nil, le32Bytes_length])]
        exact ih f (off + 19) hFuelRest

/-! ### Layer 4: Single-Instruction `decodeInsn` Inversion & AST-Free Soundness -/

private theorem decodeInsn_of_short_head (b0 : BitVec 8) (rest : List (BitVec 8))
    (h1 : b0.toNat ≠ 0x66 ∨ match rest with | b1 :: _ => b1.toNat ≠ 0x66 | [] => True)
    (h2 : b0.toNat ≠ 0x64) :
    decodeInsn (b0 :: rest) = decodeShortInsn (b0 :: rest) := by
  cases rest with
  | nil => rfl
  | cons b1 r1 =>
    cases r1 with | nil => rfl | cons b2 r2 =>
    cases r2 with | nil => rfl | cons b3 r3 =>
    cases r3 with | nil => rfl | cons b4 r4 =>
    cases r4 with | nil => rfl | cons b5 r5 =>
    cases r5 with | nil => rfl | cons b6 r6 =>
    cases r6 with | nil => rfl | cons b7 r7 =>
    cases r7 with | nil => rfl | cons b8 r8 =>
    cases r8 with
    | nil =>
      dsimp only [decodeInsn]
      rw [nat_beq_false_of_ne h2]; rfl
    | cons b9 r9 =>
      cases r9 with
      | nil => dsimp only [decodeInsn]; rw [nat_beq_false_of_ne h2]; rfl
      | cons b10 r10 =>
        cases r10 with
        | nil => dsimp only [decodeInsn]; rw [nat_beq_false_of_ne h2]; rfl
        | cons b11 r11 =>
          dsimp only [decodeInsn]
          rw [nat_beq_false_of_ne h2]
          cases h1 with
          | inl hne66 => rw [nat_beq_false_of_ne hne66]; rfl
          | inr hne1 =>
            cases hb0 : Nat.beq b0.toNat 0x66
            · rfl
            · rw [nat_beq_false_of_ne hne1]; rfl

private theorem gprLow3_lt_8 : ∀ g : Gpr, gprLow3 g < 8
  | .rax | .rcx | .rdx | .rdi | .rsi | .rsp | .rbp | .r11 => by decide

private theorem decodeGpr_encode : ∀ g : Gpr, decodeGpr (gprRexBit g) (gprLow3 g) = some g
  | .rax | .rcx | .rdx | .rdi | .rsi | .rsp | .rbp | .r11 => rfl

private theorem modrm_ge_c0 (s d : Gpr) :
    Nat.ble 0xC0 (modrmRegReg (gprLow3 s) (gprLow3 d)).toNat = true := by
  have hs := gprLow3_lt_8 s
  have hd := gprLow3_lt_8 d
  have hlt : 0xC0 + gprLow3 s * 8 + gprLow3 d < 256 := by
    have h1 : gprLow3 s ≤ 7 := Nat.le_of_lt_succ hs
    have h2 : gprLow3 s * 8 ≤ 56 := Nat.mul_le_mul_right 8 h1
    have h3 : 0xC0 + gprLow3 s * 8 ≤ 248 := Nat.add_le_add_left h2 0xC0
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_right h3 _) (Nat.add_lt_add_left hd 248)
  dsimp only [modrmRegReg]
  rw [bv_toNat_ofNat_of_lt hlt]
  exact nat_ble_of_le (Nat.le_trans (Nat.le_add_right 0xC0 _) (Nat.le_add_right _ _))

private theorem modrm_sub_c0 (s d : Gpr) :
    (modrmRegReg (gprLow3 s) (gprLow3 d)).toNat - 0xC0 = gprLow3 s * 8 + gprLow3 d := by
  have hs := gprLow3_lt_8 s
  have hd := gprLow3_lt_8 d
  have hlt : 0xC0 + gprLow3 s * 8 + gprLow3 d < 256 := by
    have h1 : gprLow3 s ≤ 7 := Nat.le_of_lt_succ hs
    have h2 : gprLow3 s * 8 ≤ 56 := Nat.mul_le_mul_right 8 h1
    have h3 : 0xC0 + gprLow3 s * 8 ≤ 248 := Nat.add_le_add_left h2 0xC0
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_right h3 _) (Nat.add_lt_add_left hd 248)
  dsimp only [modrmRegReg]
  rw [bv_toNat_ofNat_of_lt hlt, Nat.add_assoc, Nat.add_sub_cancel_left]

private theorem modrm_div8 (s d : Gpr) :
    Nat.div ((modrmRegReg (gprLow3 s) (gprLow3 d)).toNat - 0xC0) 8 = gprLow3 s := by
  rw [modrm_sub_c0, Nat.add_comm]
  exact Eq.trans (Nat.add_mul_div_right (gprLow3 d) (gprLow3 s) (by decide : 0 < 8))
    (by rw [Nat.div_eq_of_lt (gprLow3_lt_8 d), Nat.zero_add])

private theorem modrm_mod8 (s d : Gpr) :
    Nat.mod ((modrmRegReg (gprLow3 s) (gprLow3 d)).toNat - 0xC0) 8 = gprLow3 d := by
  rw [modrm_sub_c0, Nat.add_comm, nat_add_mul_mod_right, nat_mod_eq_of_lt (gprLow3_lt_8 d)]

private theorem decodeShortInsn_rex_movReg (w r b : Bool) (dst src : Gpr)
    (hr : gprRexBit src = r) (hb : gprRexBit dst = b) (tail : List (BitVec 8)) :
    decodeShortInsn (rexByte w r b :: BitVec.ofNat 8 0x89 :: modrmRegReg (gprLow3 src) (gprLow3 dst) :: tail) =
      some (.movReg dst src (if w then .full64 else .zeroExt32), 3, tail) := by
  subst hr; subst hb
  cases w <;> cases dst <;> cases src <;> (
    cases tail with
    | nil => rfl
    | cons t0 r0 =>
      cases r0 with
      | nil => rfl
      | cons t1 r1 =>
        cases r1 with
        | nil => rfl
        | cons t2 r2 => rfl)

private theorem decodeShortInsn_movImm32_false (dst : Gpr) (imm : BitVec 32) (tail : List (BitVec 8)) :
    decodeShortInsn ((encodeOneOp 0 (.movImm32 dst false imm)).1 ++ tail) =
      some (X86Insn.movImm32 dst imm, (encodeOneOp 0 (.movImm32 dst false imm)).1.length, tail) := by
  have hDec := decodeLe32_le32Bytes imm
  dsimp only [le32Bytes] at hDec
  cases dst <;> (
    change (match decodeLe32 [byteOfNat imm.toNat, byteOfNat (Nat.div imm.toNat 256),
              byteOfNat (Nat.div imm.toNat 65536), byteOfNat (Nat.div imm.toNat 16777216)] with
      | some i => some (X86Insn.movImm32 _ i, _, tail)
      | none => none) = _
    rw [hDec]; rfl)

private theorem decodeShortInsn_movImm16 (dst : Gpr) (imm : BitVec 16) (tail : List (BitVec 8)) :
    decodeShortInsn ((encodeOneOp 0 (.movImm16 dst imm)).1 ++ tail) =
      some (X86Insn.movImm16 dst imm, (encodeOneOp 0 (.movImm16 dst imm)).1.length, tail) := by
  have hDec := decodeLe16_le16Bytes imm
  dsimp only [le16Bytes] at hDec
  cases dst <;> (
    change (match decodeLe16 [byteOfNat imm.toNat, byteOfNat (Nat.div imm.toNat 256)] with
      | some i => some (X86Insn.movImm16 _ i, _, tail)
      | none => none) = _
    rw [hDec]; rfl)

private theorem decodeShortInsn_lo16_movReg (dst src : Gpr) (tail : List (BitVec 8)) :
    decodeShortInsn ((encodeOneOp 0 (.movReg dst src .lo16PreserveUpper48)).1 ++ tail) =
      some (X86Insn.movReg dst src .lo16PreserveUpper48,
            (encodeOneOp 0 (.movReg dst src .lo16PreserveUpper48)).1.length, tail) := by
  cases dst <;> cases src <;> (
    cases tail with
    | nil => rfl
    | cons t0 r0 => rfl)

private theorem execByteStream_step_nonreloc (env : LinkEnv) (pc : Nat) (st : MachState)
    (op : MiniMachOp) (tail : List (BitVec 8)) (efuel : Nat)
    (hFuel : ((encodeOneOp 0 op).1 ++ tail).length ≤ efuel)
    (hNonRel : (encodeOneOp 0 op).2 = []) :
    execByteStreamLoop env efuel pc ((encodeOneOp 0 op).1 ++ tail) st =
      execByteStreamLoop env (efuel - 1) (pc + (encodeOneOp 0 op).1.length) tail
        (execMiniMachOp env op st) := by
  cases op with
  | callSym _ | leaRipSym _ | loadGotRelaxable _ | loadGotStrict _
  | tlsGdAddr _ | tlsLdAddr _ | tlsLdLoad _ | tlsGotTpOff _ =>
    cases hNonRel
  | ret =>
    cases efuel with
    | zero => dsimp only [encodeOneOp, List.length_append, List.length_cons] at hFuel; exact False.elim (Nat.not_succ_le_zero _ hFuel)
    | succ f =>
      dsimp only [encodeOneOp, List.cons_append, List.nil_append, execByteStreamLoop, allInt3]
      rw [decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
      rfl
  | movImm32 dst is64 imm =>
    cases efuel with
    | zero =>
      rw [List.length_append] at hFuel
      exact False.elim (nat_not_add_succ_le_zero (Nat.le_trans (Nat.add_le_add_right (encodeOneOp_movImm32_len_pos dst is64 imm) _) hFuel))
    | succ f =>
      cases is64 with
      | true =>
        cases dst <;> (
          dsimp only [encodeOneOp, rexByte, gprRexBit, modrmRegReg, gprLow3, le32Bytes, List.cons_append, List.nil_append, execByteStreamLoop, allInt3]
          rw [decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
          dsimp only [decodeShortInsn]
          have hDec := decodeLe32_le32Bytes imm
          dsimp only [le32Bytes] at hDec
          simp only [hDec, execX86Insn, execMiniMachOp]
          rfl)
      | false =>
        have hDecS := decodeShortInsn_movImm32_false dst imm tail
        have hHead : ∃ b0 r0, (encodeOneOp 0 (.movImm32 dst false imm)).1 ++ tail = b0 :: r0 ∧
            allInt3 (b0 :: r0) = false ∧ decodeInsn (b0 :: r0) = decodeShortInsn (b0 :: r0) := by
          cases dst <;> refine ⟨_, _, rfl, rfl, decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)⟩
        have ⟨b0, r0, hEqCons, hNotCC, hShort⟩ := hHead
        rw [hEqCons] at hDecS; rw [hEqCons]
        dsimp only [execByteStreamLoop]
        rw [ite_bool_eq_false hNotCC, hShort, hDecS]
        rfl
  | movImm16 dst imm =>
    cases efuel with
    | zero =>
      rw [List.length_append] at hFuel
      exact False.elim (nat_not_add_succ_le_zero (Nat.le_trans (Nat.add_le_add_right (encodeOneOp_movImm16_len_pos dst imm) _) hFuel))
    | succ f =>
      have hDecS := decodeShortInsn_movImm16 dst imm tail
      have hHead : ∃ b0 b1 r1, (encodeOneOp 0 (.movImm16 dst imm)).1 ++ tail = b0 :: b1 :: r1 ∧
          allInt3 (b0 :: b1 :: r1) = false ∧ decodeInsn (b0 :: b1 :: r1) = decodeShortInsn (b0 :: b1 :: r1) := by
        cases dst <;> refine ⟨_, _, _, rfl, rfl, decodeInsn_of_short_head _ _ (Or.inr (by dsimp only; decide)) (by decide)⟩
      have ⟨b0, b1, r1, hEqCons, hNotCC, hShort⟩ := hHead
      rw [hEqCons] at hDecS; rw [hEqCons]
      dsimp only [execByteStreamLoop]
      rw [ite_bool_eq_false hNotCC, hShort, hDecS]
      rfl
  | movReg dst src mode =>
    have hGe := modrm_ge_c0 src dst
    have hDiv := modrm_div8 src dst
    have hMod := modrm_mod8 src dst
    have hDecD := decodeGpr_encode dst
    have hDecS := decodeGpr_encode src
    cases efuel with
    | zero =>
      rw [List.length_append] at hFuel
      exact False.elim (nat_not_add_succ_le_zero (Nat.le_trans (Nat.add_le_add_right (encodeOneOp_movReg_len_pos dst src mode) _) hFuel))
    | succ f =>
      cases mode with
      | full64 =>
        dsimp only [encodeOneOp, List.cons_append, List.nil_append, execByteStreamLoop]
        have hNotCC : allInt3 (rexByte true (gprRexBit src) (gprRexBit dst) :: BitVec.ofNat 8 0x89 :: modrmRegReg (gprLow3 src) (gprLow3 dst) :: tail) = false := by
          cases gprRexBit src <;> cases gprRexBit dst <;> rfl
        have hShort : decodeInsn (rexByte true (gprRexBit src) (gprRexBit dst) :: BitVec.ofNat 8 0x89 :: modrmRegReg (gprLow3 src) (gprLow3 dst) :: tail) =
            decodeShortInsn (rexByte true (gprRexBit src) (gprRexBit dst) :: BitVec.ofNat 8 0x89 :: modrmRegReg (gprLow3 src) (gprLow3 dst) :: tail) :=
          decodeInsn_of_short_head _ _ (Or.inl (by cases gprRexBit src <;> cases gprRexBit dst <;> decide)) (by cases gprRexBit src <;> cases gprRexBit dst <;> decide)
        rw [hNotCC, ite_bool_false, hShort, decodeShortInsn_rex_movReg true (gprRexBit src) (gprRexBit dst) dst src rfl rfl tail]
        rfl
      | zeroExt32 =>
        cases hrs : gprRexBit src <;> cases hrd : gprRexBit dst
        · dsimp only [encodeOneOp]
          have hOr : (gprRexBit src || gprRexBit dst) = false := by rw [hrs, hrd]; rfl
          rw [ite_bool_eq_false hOr]
          dsimp only [List.cons_append, List.nil_append, execByteStreamLoop]
          rw [ite_bool_eq_false (rfl : allInt3 _ = false), decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
          dsimp only [decodeShortInsn]
          rw [hrs] at hDecS; rw [hrd] at hDecD
          simp only [hGe, hDiv, hMod, hDecD, hDecS, execX86Insn, execMiniMachOp]
          rfl
        · dsimp only [encodeOneOp]
          have hOr : (gprRexBit src || gprRexBit dst) = true := by rw [hrs, hrd]; rfl
          rw [ite_bool_eq_true hOr, hrs, hrd]
          dsimp only [List.cons_append, List.nil_append, execByteStreamLoop]
          rw [ite_bool_eq_false (rfl : allInt3 _ = false), decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
          rw [decodeShortInsn_rex_movReg false false true dst src hrs hrd tail]
          rfl
        · dsimp only [encodeOneOp]
          have hOr : (gprRexBit src || gprRexBit dst) = true := by rw [hrs, hrd]; rfl
          rw [ite_bool_eq_true hOr, hrs, hrd]
          dsimp only [List.cons_append, List.nil_append, execByteStreamLoop]
          rw [ite_bool_eq_false (rfl : allInt3 _ = false), decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
          rw [decodeShortInsn_rex_movReg false true false dst src hrs hrd tail]
          rfl
        · dsimp only [encodeOneOp]
          have hOr : (gprRexBit src || gprRexBit dst) = true := by rw [hrs, hrd]; rfl
          rw [ite_bool_eq_true hOr, hrs, hrd]
          dsimp only [List.cons_append, List.nil_append, execByteStreamLoop]
          rw [ite_bool_eq_false (rfl : allInt3 _ = false), decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
          rw [decodeShortInsn_rex_movReg false true true dst src hrs hrd tail]
          rfl
      | lo16PreserveUpper48 =>
        have hDecLo := decodeShortInsn_lo16_movReg dst src tail
        have hHead : ∃ b0 b1 r1, (encodeOneOp 0 (.movReg dst src .lo16PreserveUpper48)).1 ++ tail = b0 :: b1 :: r1 ∧
            allInt3 (b0 :: b1 :: r1) = false ∧ decodeInsn (b0 :: b1 :: r1) = decodeShortInsn (b0 :: b1 :: r1) := by
          cases dst <;> cases src <;> refine ⟨_, _, _, rfl, rfl, decodeInsn_of_short_head _ _ (Or.inr (by dsimp only; decide)) (by decide)⟩
        have ⟨b0, b1, r1, hEqCons, hNotCC, hShort⟩ := hHead
        rw [hEqCons] at hDecLo; rw [hEqCons]
        dsimp only [execByteStreamLoop]
        rw [ite_bool_eq_false hNotCC, hShort, hDecLo]
        rfl

private theorem execByteStream_step_9b_fs (env : LinkEnv) (pc : Nat) (st : MachState)
    (tail : List (BitVec 8)) (efuel : Nat)
    (hFuel : 9 + tail.length ≤ efuel) :
    execByteStreamLoop env efuel pc
      ([BitVec.ofNat 8 0x64, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04,
        BitVec.ofNat 8 0x25, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0] ++ tail) st =
      execByteStreamLoop env (efuel - 1) (pc + 9) tail (writeGpr st .rax .full64 env.threadPtrBase) := by
  cases efuel with
  | zero => exact False.elim (nat_not_add_succ_le_zero hFuel)
  | succ f =>
    dsimp only [List.cons_append, List.nil_append, execByteStreamLoop, allInt3]
    cases tail with
    | nil => rfl
    | cons t0 r0 =>
      cases r0 with
      | nil => rfl
      | cons t1 r1 =>
        cases r1 with
        | nil => rfl
        | cons t2 r2 => rfl

private theorem execByteStream_step_12b_fs (env : LinkEnv) (pc : Nat) (st : MachState)
    (tail : List (BitVec 8)) (efuel : Nat)
    (hFuel : 12 + tail.length ≤ efuel) :
    execByteStreamLoop env efuel pc
      ([BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64,
        BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25,
        BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0] ++ tail) st =
      execByteStreamLoop env (efuel - 1) (pc + 12) tail (writeGpr st .rax .full64 env.threadPtrBase) := by
  cases efuel with
  | zero => exact False.elim (nat_not_add_succ_le_zero hFuel)
  | succ f =>
    rfl

private theorem execByteStream_step_7b_rax (env : LinkEnv) (pc : Nat) (st : MachState)
    (w : BitVec 32) (tail : List (BitVec 8)) (efuel : Nat)
    (hFuel : 7 + tail.length ≤ efuel) :
    (execByteStreamLoop env efuel pc
      (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++ le32Bytes w) ++ tail) st =
      execByteStreamLoop env (efuel - 1) (pc + 7) tail
        (writeGpr st .rax .full64 (BitVec.ofNat 64 (pc + 7) + sext32To64 w))) ∧
    (execByteStreamLoop env efuel pc
      (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++ le32Bytes w) ++ tail) st =
      execByteStreamLoop env (efuel - 1) (pc + 7) tail
        (writeGpr st .rax .full64 (st.mem (BitVec.ofNat 64 (pc + 7) + sext32To64 w)))) ∧
    (execByteStreamLoop env efuel pc
      (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xC7, BitVec.ofNat 8 0xC0] ++ le32Bytes w) ++ tail) st =
      execByteStreamLoop env (efuel - 1) (pc + 7) tail
        (writeGpr st .rax .full64 (sext32To64 w))) ∧
    (execByteStreamLoop env efuel pc
      (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++ le32Bytes w) ++ tail) st =
      execByteStreamLoop env (efuel - 1) (pc + 7) tail
        (writeGpr st .rax .full64 (st.rax + sext32To64 w))) ∧
    (execByteStreamLoop env efuel pc
      (([BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80] ++ le32Bytes w) ++ tail) st =
      execByteStreamLoop env (efuel - 1) (pc + 7) tail
        (writeGpr st .rax .full64 (st.mem (st.rax + sext32To64 w)))) := by
  cases efuel with
  | zero => exact False.elim (nat_not_add_succ_le_zero hFuel)
  | succ f =>
    have hDec := decodeLe32_le32Bytes w
    dsimp only [le32Bytes] at hDec
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [le32Bytes, List.cons_append, List.nil_append, execByteStreamLoop, allInt3]
      rw [decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
      dsimp only [decodeShortInsn]; simp only [hDec, execX86Insn]; rfl
    · dsimp only [le32Bytes, List.cons_append, List.nil_append, execByteStreamLoop, allInt3]
      rw [decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
      dsimp only [decodeShortInsn]; simp only [hDec, execX86Insn]; rfl
    · dsimp only [le32Bytes, List.cons_append, List.nil_append, execByteStreamLoop, allInt3]
      rw [decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
      dsimp only [decodeShortInsn]; simp only [hDec, execX86Insn]; rfl
    · dsimp only [le32Bytes, List.cons_append, List.nil_append, execByteStreamLoop, allInt3]
      rw [decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
      dsimp only [decodeShortInsn]; simp only [hDec, execX86Insn]; rfl
    · dsimp only [le32Bytes, List.cons_append, List.nil_append, execByteStreamLoop, allInt3]
      rw [decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
      dsimp only [decodeShortInsn]; simp only [hDec, execX86Insn]; rfl

private theorem execByteStream_step_call (env : LinkEnv) (pc : Nat) (st : MachState)
    (w : BitVec 32) (tail : List (BitVec 8)) (efuel : Nat)
    (hFuel : 5 + tail.length ≤ efuel) :
    execByteStreamLoop env efuel pc
      (([BitVec.ofNat 8 0xE8] ++ le32Bytes w) ++ tail) st =
      execByteStreamLoop env (efuel - 1) (pc + 5) tail st := by
  cases efuel with
  | zero => exact False.elim (nat_not_add_succ_le_zero hFuel)
  | succ f =>
    have hDec := decodeLe32_le32Bytes w
    dsimp only [le32Bytes] at hDec
    dsimp only [le32Bytes, List.cons_append, List.nil_append, execByteStreamLoop, allInt3]
    rw [decodeInsn_of_short_head _ _ (Or.inl (by decide)) (by decide)]
    dsimp only [decodeShortInsn]; simp only [hDec, execX86Insn]; rfl

private theorem writeGpr_rax_full64_rax (st : MachState) (v : BitVec 64) :
    (writeGpr st .rax .full64 v).rax = v := rfl

private theorem writeGpr_rax_full64_mem (st : MachState) (v : BitVec 64) :
    (writeGpr st .rax .full64 v).mem = st.mem := rfl

private theorem writeGpr_rax_overwrite (st : MachState) (v1 v2 : BitVec 64) :
    writeGpr (writeGpr st .rax .full64 v1) .rax .full64 v2 = writeGpr st .rax .full64 v2 := rfl

private theorem linkEnvConsistent_execMiniMachOp {env : LinkEnv} {st : MachState}
    (hEnv : LinkEnvConsistent env st) (op : MiniMachOp) :
    LinkEnvConsistent env (execMiniMachOp env op st) := by
  have hMemEq : (execMiniMachOp env op st).mem = st.mem := by
    cases op with
    | movImm32 dst is64 imm => cases is64 <;> cases dst <;> rfl
    | movImm16 dst imm => cases dst <;> rfl
    | movReg dst src mode => cases mode <;> cases dst <;> rfl
    | callSym _ | leaRipSym _ | loadGotRelaxable _ | loadGotStrict _
    | tlsGdAddr _ | tlsLdAddr _ | tlsLdLoad _ | tlsGotTpOff _ | ret => rfl
  exact ⟨fun s => by rw [hMemEq]; exact hEnv.1 s, fun s => by rw [hMemEq]; exact hEnv.2 s⟩

private theorem validate_sound_loop (env : LinkEnv) (vaddr : Nat)
    (ops : List MiniMachOp) :
    ∀ (off fuel efuel : Nat) (lnk : List (BitVec 8)) (st : MachState),
      LinkEnvConsistent env st →
      OpsPcRelReachable env (vaddr + off) ops →
      lnk.length ≤ efuel →
      validateLinkedBytesLoop env vaddr fuel off (encodeOpsLoop off ops).1
        (encodeOpsLoop off ops).2 lnk = true →
      execByteStreamLoop env efuel (vaddr + off) lnk st =
        some (execMiniMachFn env ops st) := by
  induction ops with
  | nil =>
    intro off fuel efuel lnk st _ _ _ hVal
    cases fuel <;> (
      dsimp only [encodeOpsLoop, validateLinkedBytesLoop, execMiniMachFn] at hVal
      dsimp only [execMiniMachFn]
      cases efuel with
      | zero =>
        cases lnk with
        | nil => rfl
        | cons b bs => dsimp only [execByteStreamLoop]; rw [ite_bool_eq_true hVal]
      | succ f =>
        cases lnk with
        | nil => rfl
        | cons b bs => dsimp only [execByteStreamLoop]; rw [ite_bool_eq_true hVal])
  | cons op rest ih =>
    intro off fuel efuel lnk st hEnv hReach hEfuel hVal
    cases hReach with
    | cons hOpReach hRestReach =>
      dsimp only [encodeOpsLoop, execMiniMachFn] at hVal; dsimp only [encodeOpsLoop, execMiniMachFn]
      have hGeRest : HeadRelocGe (off + (encodeOneOp off op).1.length)
          (encodeOpsLoop (off + (encodeOneOp off op).1.length) rest).2 :=
        encodeOpsLoop_headRelocGe _ rest
      have hLenEq : (encodeOneOp off op).1.length = (encodeOneOp 0 op).1.length := by
        rw [encodeOneOp_code_pc_indep]
      have hRestReach' : OpsPcRelReachable env (vaddr + (off + (encodeOneOp off op).1.length)) rest := by
        rw [hLenEq, ← Nat.add_assoc]; exact hRestReach
      have hEnvNext := linkEnvConsistent_execMiniMachOp hEnv op
      cases op with
      | movImm32 dst is64 imm =>
        have hRelNil : (encodeOneOp off (.movImm32 dst is64 imm)).2 = [] :=
          encodeOneOp_movImm32_relocs off dst is64 imm
        rw [hRelNil, List.nil_append] at hVal
        have ⟨restLnk, fuel', hLnkEq, _, hValRest⟩ :=
          validate_plain_bytes_inv env vaddr _ _ _ fuel off lnk hGeRest hVal
        rw [hLnkEq, encodeOneOp_code_pc_indep] at hEfuel; rw [hLnkEq, encodeOneOp_code_pc_indep]
        rw [execByteStream_step_nonreloc env (vaddr + off) st _ restLnk efuel hEfuel (encodeOneOp_movImm32_relocs 0 dst is64 imm)]
        have hLenPos : 1 ≤ (encodeOneOp 0 (.movImm32 dst is64 imm)).1.length :=
          encodeOneOp_movImm32_len_pos dst is64 imm
        have hEfuel' : restLnk.length ≤ efuel - 1 := by
          rw [List.length_append] at hEfuel
          have h1 : 1 + restLnk.length ≤ efuel := Nat.le_trans (Nat.add_le_add_right hLenPos _) hEfuel
          exact nat_le_sub_of_add_le_left h1
        rw [Nat.add_assoc vaddr off, ← hLenEq]
        exact ih (off + (encodeOneOp off (.movImm32 dst is64 imm)).1.length) fuel' (efuel - 1)
          restLnk (execMiniMachOp env (.movImm32 dst is64 imm) st) hEnvNext hRestReach' hEfuel' hValRest
      | movImm16 dst imm =>
        have hRelNil : (encodeOneOp off (.movImm16 dst imm)).2 = [] :=
          encodeOneOp_movImm16_relocs off dst imm
        rw [hRelNil, List.nil_append] at hVal
        have ⟨restLnk, fuel', hLnkEq, _, hValRest⟩ :=
          validate_plain_bytes_inv env vaddr _ _ _ fuel off lnk hGeRest hVal
        rw [hLnkEq, encodeOneOp_code_pc_indep] at hEfuel; rw [hLnkEq, encodeOneOp_code_pc_indep]
        rw [execByteStream_step_nonreloc env (vaddr + off) st _ restLnk efuel hEfuel (encodeOneOp_movImm16_relocs 0 dst imm)]
        have hLenPos : 1 ≤ (encodeOneOp 0 (.movImm16 dst imm)).1.length :=
          encodeOneOp_movImm16_len_pos dst imm
        have hEfuel' : restLnk.length ≤ efuel - 1 := by
          rw [List.length_append] at hEfuel
          exact nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right hLenPos _) hEfuel)
        rw [Nat.add_assoc vaddr off, ← hLenEq]
        exact ih _ fuel' (efuel - 1) restLnk _ hEnvNext hRestReach' hEfuel' hValRest
      | movReg dst src mode =>
        have hRelNil : (encodeOneOp off (.movReg dst src mode)).2 = [] :=
          encodeOneOp_movReg_relocs off dst src mode
        rw [hRelNil, List.nil_append] at hVal
        have ⟨restLnk, fuel', hLnkEq, _, hValRest⟩ :=
          validate_plain_bytes_inv env vaddr _ _ _ fuel off lnk hGeRest hVal
        rw [hLnkEq, encodeOneOp_code_pc_indep] at hEfuel; rw [hLnkEq, encodeOneOp_code_pc_indep]
        rw [execByteStream_step_nonreloc env (vaddr + off) st _ restLnk efuel hEfuel (encodeOneOp_movReg_relocs 0 dst src mode)]
        have hLenPos : 1 ≤ (encodeOneOp 0 (.movReg dst src mode)).1.length :=
          encodeOneOp_movReg_len_pos dst src mode
        have hEfuel' : restLnk.length ≤ efuel - 1 := by
          rw [List.length_append] at hEfuel
          exact nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right hLenPos _) hEfuel)
        rw [Nat.add_assoc vaddr off, ← hLenEq]
        exact ih _ fuel' (efuel - 1) restLnk _ hEnvNext hRestReach' hEfuel' hValRest
      | ret =>
        have hRelNil : (encodeOneOp off .ret).2 = [] := rfl
        rw [hRelNil, List.nil_append] at hVal
        have ⟨restLnk, fuel', hLnkEq, _, hValRest⟩ :=
          validate_plain_bytes_inv env vaddr _ _ _ fuel off lnk hGeRest hVal
        rw [hLnkEq, encodeOneOp_code_pc_indep] at hEfuel; rw [hLnkEq, encodeOneOp_code_pc_indep]
        rw [execByteStream_step_nonreloc env (vaddr + off) st .ret restLnk efuel hEfuel rfl]
        have hLenPos : 1 ≤ (encodeOneOp 0 .ret).1.length := by decide
        have hEfuel' : restLnk.length ≤ efuel - 1 := by
          rw [List.length_append] at hEfuel
          exact nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right hLenPos _) hEfuel)
        rw [Nat.add_assoc vaddr off, ← hLenEq]
        exact ih _ fuel' (efuel - 1) restLnk _ hEnvNext hRestReach' hEfuel' hValRest
      | callSym s =>
        cases fuel with
        | zero => cases hVal
        | succ f =>
          rw [enc_callSym] at hVal hRestReach'; simp only [tmplCall_len] at hVal hRestReach'
          rw [reloc_cons_append, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_plt32 _ _ _ _)] at hVal
          have hNone : matchRelocAtOff env off (tmplCall ++ (encodeOpsLoop (off + 5) rest).1)
              ({ offset := off + 1, kind := .r_plt32, sym := s, addend := Int.negSucc 3 } ::
                (encodeOpsLoop (off + 5) rest).2) lnk = none := by
            cases (encodeOpsLoop (off + 5) rest).2 with | nil => rfl | cons r2 rs2 => cases rs2 <;> rfl
          rw [hNone] at hVal
          dsimp only [matchSingleRelocAtOff] at hVal
          rw [ite_bool_eq_true (nat_beq_refl (off + 1))] at hVal
          let exp := [BitVec.ofNat 8 0xE8] ++ le32Bytes (rel32Disp (vaddr + off + 1) (env.symAddr s))
          cases hChk : checkPrefixEq tmplCall (tmplCall ++ (encodeOpsLoop (off + 5) rest).1) && checkPrefixEq exp lnk
          · rw [ite_bool_eq_false hChk] at hVal; cases hVal
          · rw [ite_bool_eq_true hChk] at hVal; dsimp only at hVal
            have ⟨_, hExp⟩ := bool_and_elim hChk
            have hLnkEq : lnk = exp ++ lnk.drop 5 := eq_append_drop_of_checkPrefixEq hExp
            rw [list_drop_append_of_len tmplCall _ tmplCall_len] at hVal
            rw [hLnkEq] at hEfuel; rw [hLnkEq]
            rw [List.length_append] at hEfuel
            have hStepFuel : 5 + (lnk.drop 5).length ≤ efuel := by
              simp only [exp, List.length_append, List.length_cons, List.length_nil, le32Bytes_length] at hEfuel
              exact hEfuel
            rw [execByteStream_step_call env (vaddr + off) st _ (lnk.drop 5) efuel hStepFuel]
            have hEfuel' : (lnk.drop 5).length ≤ efuel - 1 :=
              nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 5) _) hStepFuel)
            rw [Nat.add_assoc vaddr off 5]
            exact ih (off + 5) f (efuel - 1) (lnk.drop 5) st hEnvNext hRestReach' hEfuel' hVal
      | leaRipSym s =>
        cases fuel with
        | zero => cases hVal
        | succ f =>
          rw [enc_leaRipSym] at hVal hRestReach'; simp only [tmplLeaRip_len] at hVal hRestReach'
          rw [reloc_cons_append, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_pc32 _ _ _ _)] at hVal
          have hNone : matchRelocAtOff env off (tmplLeaRip ++ (encodeOpsLoop (off + 7) rest).1)
              ({ offset := off + 3, kind := .r_pc32, sym := s, addend := Int.negSucc 3 } ::
                (encodeOpsLoop (off + 7) rest).2) lnk = none := by
            cases (encodeOpsLoop (off + 7) rest).2 with | nil => rfl | cons r2 rs2 => cases rs2 <;> rfl
          rw [hNone] at hVal
          dsimp only [matchSingleRelocAtOff] at hVal
          rw [ite_bool_eq_true (nat_beq_refl (off + 3))] at hVal
          let exp := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++
            le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr s))
          cases hChk : checkPrefixEq tmplLeaRip (tmplLeaRip ++ (encodeOpsLoop (off + 7) rest).1) && checkPrefixEq exp lnk
          · rw [ite_bool_eq_false hChk] at hVal; cases hVal
          · rw [ite_bool_eq_true hChk] at hVal; dsimp only at hVal
            have ⟨_, hExp⟩ := bool_and_elim hChk
            have hLnkEq : lnk = exp ++ lnk.drop 7 := eq_append_drop_of_checkPrefixEq hExp
            rw [list_drop_append_of_len tmplLeaRip _ tmplLeaRip_len] at hVal
            rw [hLnkEq] at hEfuel; rw [hLnkEq]
            rw [List.length_append] at hEfuel
            have hStepFuel : 7 + (lnk.drop 7).length ≤ efuel := by
              simp only [exp, List.length_append, List.length_cons, List.length_nil, le32Bytes_length] at hEfuel
              exact hEfuel
            rw [(execByteStream_step_7b_rax env (vaddr + off) st _ (lnk.drop 7) efuel hStepFuel).1]
            have hAdd := pcRel32_add_exact (vaddr + off + 3) (env.symAddr s) (by rw [Nat.add_assoc (vaddr + off) 3 4]; exact hOpReach)
            rw [Nat.add_assoc (vaddr + off) 3 4] at hAdd
            rw [hAdd, Nat.add_assoc vaddr off 7]
            have hEfuel' : (lnk.drop 7).length ≤ efuel - 1 :=
              nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 7) _) hStepFuel)
            exact ih (off + 7) f (efuel - 1) (lnk.drop 7) _ hEnvNext hRestReach' hEfuel' hVal
      | loadGotStrict s =>
        cases fuel with
        | zero => cases hVal
        | succ f =>
          rw [enc_loadGotStrict] at hVal hRestReach'; simp only [tmplMovRip_len] at hVal hRestReach'
          rw [reloc_cons_append, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_gotpcrel _ _ _ _)] at hVal
          have hNone : matchRelocAtOff env off (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1)
              ({ offset := off + 3, kind := .r_gotpcrel, sym := s, addend := Int.negSucc 3 } ::
                (encodeOpsLoop (off + 7) rest).2) lnk = none := by
            cases (encodeOpsLoop (off + 7) rest).2 with | nil => rfl | cons r2 rs2 => cases rs2 <;> rfl
          rw [hNone] at hVal
          dsimp only [matchSingleRelocAtOff] at hVal
          rw [ite_bool_eq_true (nat_beq_refl (off + 3))] at hVal
          let exp := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++
            le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr s))
          cases hChk : checkPrefixEq tmplMovRip (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1) && checkPrefixEq exp lnk
          · rw [ite_bool_eq_false hChk] at hVal; cases hVal
          · rw [ite_bool_eq_true hChk] at hVal; dsimp only at hVal
            have ⟨_, hExp⟩ := bool_and_elim hChk
            have hLnkEq : lnk = exp ++ lnk.drop 7 := eq_append_drop_of_checkPrefixEq hExp
            rw [list_drop_append_of_len tmplMovRip _ tmplMovRip_len] at hVal
            rw [hLnkEq] at hEfuel; rw [hLnkEq]
            rw [List.length_append] at hEfuel
            have hStepFuel : 7 + (lnk.drop 7).length ≤ efuel := by
              simp only [exp, List.length_append, List.length_cons, List.length_nil, le32Bytes_length] at hEfuel
              exact hEfuel
            rw [(execByteStream_step_7b_rax env (vaddr + off) st _ (lnk.drop 7) efuel hStepFuel).2.1]
            have hAdd := pcRel32_add_exact (vaddr + off + 3) (env.gotSlotAddr s) (by rw [Nat.add_assoc (vaddr + off) 3 4]; exact hOpReach)
            rw [Nat.add_assoc (vaddr + off) 3 4] at hAdd
            rw [hAdd, hEnv.1 s, Nat.add_assoc vaddr off 7]
            have hEfuel' : (lnk.drop 7).length ≤ efuel - 1 :=
              nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 7) _) hStepFuel)
            exact ih (off + 7) f (efuel - 1) (lnk.drop 7) _ hEnvNext hRestReach' hEfuel' hVal
      | loadGotRelaxable s =>
        cases fuel with
        | zero => cases hVal
        | succ f =>
          rw [enc_loadGotRelaxable] at hVal hRestReach'; simp only [tmplMovRip_len] at hVal hRestReach'
          rw [reloc_cons_append, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_rex_gotpcrelx _ _ _ _)] at hVal
          have hNone : matchRelocAtOff env off (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1)
              ({ offset := off + 3, kind := .r_rex_gotpcrelx, sym := s, addend := Int.negSucc 3 } ::
                (encodeOpsLoop (off + 7) rest).2) lnk = none := by
            cases (encodeOpsLoop (off + 7) rest).2 with | nil => rfl | cons r2 rs2 => cases rs2 <;> rfl
          rw [hNone] at hVal
          dsimp only [matchSingleRelocAtOff] at hVal
          rw [ite_bool_eq_true (nat_beq_refl (off + 3))] at hVal
          let expRel := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05] ++
            le32Bytes (rel32Disp (vaddr + off + 3) (env.symAddr s))
          let expUnrel := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++
            le32Bytes (rel32Disp (vaddr + off + 3) (env.gotSlotAddr s))
          cases hChk : checkPrefixEq tmplMovRip (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1) &&
              (checkPrefixEq expRel lnk || checkPrefixEq expUnrel lnk)
          · rw [ite_bool_eq_false hChk] at hVal; cases hVal
          · rw [ite_bool_eq_true hChk] at hVal; dsimp only at hVal
            have ⟨_, hOr⟩ := bool_and_elim hChk
            rw [list_drop_append_of_len tmplMovRip _ tmplMovRip_len] at hVal
            cases bool_or_elim hOr with
            | inl hRel =>
              have hLnkEq : lnk = expRel ++ lnk.drop 7 := eq_append_drop_of_checkPrefixEq hRel
              rw [hLnkEq] at hEfuel; rw [hLnkEq]
              rw [List.length_append] at hEfuel
              have hStepFuel : 7 + (lnk.drop 7).length ≤ efuel := by
                simp only [expRel, List.length_append, List.length_cons, List.length_nil, le32Bytes_length] at hEfuel
                exact hEfuel
              rw [(execByteStream_step_7b_rax env (vaddr + off) st _ (lnk.drop 7) efuel hStepFuel).1]
              have hAdd := pcRel32_add_exact (vaddr + off + 3) (env.symAddr s) (by rw [Nat.add_assoc (vaddr + off) 3 4]; exact hOpReach.1)
              rw [Nat.add_assoc (vaddr + off) 3 4] at hAdd
              rw [hAdd, Nat.add_assoc vaddr off 7]
              have hEfuel' : (lnk.drop 7).length ≤ efuel - 1 :=
                nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 7) _) hStepFuel)
              exact ih (off + 7) f (efuel - 1) (lnk.drop 7) _ hEnvNext hRestReach' hEfuel' hVal
            | inr hUnrel =>
              have hLnkEq : lnk = expUnrel ++ lnk.drop 7 := eq_append_drop_of_checkPrefixEq hUnrel
              rw [hLnkEq] at hEfuel; rw [hLnkEq]
              rw [List.length_append] at hEfuel
              have hStepFuel : 7 + (lnk.drop 7).length ≤ efuel := by
                simp only [expUnrel, List.length_append, List.length_cons, List.length_nil, le32Bytes_length] at hEfuel
                exact hEfuel
              rw [(execByteStream_step_7b_rax env (vaddr + off) st _ (lnk.drop 7) efuel hStepFuel).2.1]
              have hAdd := pcRel32_add_exact (vaddr + off + 3) (env.gotSlotAddr s) (by rw [Nat.add_assoc (vaddr + off) 3 4]; exact hOpReach.2)
              rw [Nat.add_assoc (vaddr + off) 3 4] at hAdd
              rw [hAdd, hEnv.1 s, Nat.add_assoc vaddr off 7]
              have hEfuel' : (lnk.drop 7).length ≤ efuel - 1 :=
                nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 7) _) hStepFuel)
              exact ih (off + 7) f (efuel - 1) (lnk.drop 7) _ hEnvNext hRestReach' hEfuel' hVal
      | tlsGotTpOff s =>
        cases fuel with
        | zero => cases hVal
        | succ f =>
          rw [enc_tlsGotTpOff] at hVal hRestReach'; simp only [tmplMovRip_len] at hVal hRestReach'
          rw [reloc_cons_append, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_gottpoff _ _ _ _)] at hVal
          have hNone : matchRelocAtOff env off (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1)
              ({ offset := off + 3, kind := .r_gottpoff, sym := s, addend := Int.negSucc 3 } ::
                (encodeOpsLoop (off + 7) rest).2) lnk = none := by
            cases (encodeOpsLoop (off + 7) rest).2 with | nil => rfl | cons r2 rs2 => cases rs2 <;> rfl
          rw [hNone] at hVal
          dsimp only [matchSingleRelocAtOff] at hVal
          rw [ite_bool_eq_true (nat_beq_refl (off + 3))] at hVal
          let expRel := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xC7, BitVec.ofNat 8 0xC0] ++
            le32Bytes (env.tlsTpOff s)
          let expUnrel := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x05] ++
            le32Bytes (rel32Disp (vaddr + off + 3) (env.gotTpOffSlotAddr s))
          cases hChk : checkPrefixEq tmplMovRip (tmplMovRip ++ (encodeOpsLoop (off + 7) rest).1) &&
              (checkPrefixEq expRel lnk || checkPrefixEq expUnrel lnk)
          · rw [ite_bool_eq_false hChk] at hVal; cases hVal
          · rw [ite_bool_eq_true hChk] at hVal; dsimp only at hVal
            have ⟨_, hOr⟩ := bool_and_elim hChk
            rw [list_drop_append_of_len tmplMovRip _ tmplMovRip_len] at hVal
            cases bool_or_elim hOr with
            | inl hRel =>
              have hLnkEq : lnk = expRel ++ lnk.drop 7 := eq_append_drop_of_checkPrefixEq hRel
              rw [hLnkEq] at hEfuel; rw [hLnkEq]
              rw [List.length_append] at hEfuel
              have hStepFuel : 7 + (lnk.drop 7).length ≤ efuel := by
                simp only [expRel, List.length_append, List.length_cons, List.length_nil, le32Bytes_length] at hEfuel
                exact hEfuel
              rw [(execByteStream_step_7b_rax env (vaddr + off) st _ (lnk.drop 7) efuel hStepFuel).2.2.1]
              rw [Nat.add_assoc vaddr off 7]
              have hEfuel' : (lnk.drop 7).length ≤ efuel - 1 :=
                nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 7) _) hStepFuel)
              exact ih (off + 7) f (efuel - 1) (lnk.drop 7) _ hEnvNext hRestReach' hEfuel' hVal
            | inr hUnrel =>
              have hLnkEq : lnk = expUnrel ++ lnk.drop 7 := eq_append_drop_of_checkPrefixEq hUnrel
              rw [hLnkEq] at hEfuel; rw [hLnkEq]
              rw [List.length_append] at hEfuel
              have hStepFuel : 7 + (lnk.drop 7).length ≤ efuel := by
                simp only [expUnrel, List.length_append, List.length_cons, List.length_nil, le32Bytes_length] at hEfuel
                exact hEfuel
              rw [(execByteStream_step_7b_rax env (vaddr + off) st _ (lnk.drop 7) efuel hStepFuel).2.1]
              have hAdd := pcRel32_add_exact (vaddr + off + 3) (env.gotTpOffSlotAddr s) (by rw [Nat.add_assoc (vaddr + off) 3 4]; exact hOpReach)
              rw [Nat.add_assoc (vaddr + off) 3 4] at hAdd
              rw [hAdd, hEnv.2 s, Nat.add_assoc vaddr off 7]
              have hEfuel' : (lnk.drop 7).length ≤ efuel - 1 :=
                nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 7) _) hStepFuel)
              exact ih (off + 7) f (efuel - 1) (lnk.drop 7) _ hEnvNext hRestReach' hEfuel' hVal
      | tlsGdAddr s =>
        cases fuel with
        | zero => cases hVal
        | succ f =>
          rw [enc_tlsGdAddr] at hVal hRestReach'; simp only [tmplTlsGdObj_len] at hVal hRestReach'
          rw [reloc_cons2_append, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_tlsgd _ _ _ _)] at hVal
          let p9 := [BitVec.ofNat 8 0x64, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04,
                     BitVec.ofNat 8 0x25, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0]
          let p7 := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
          let expGd :=
            [BitVec.ofNat 8 0x64, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04,
             BitVec.ofNat 8 0x25, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0,
             BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
          have hExpGdP : expGd = p9 ++ p7 := rfl
          have hOffGd : (Nat.beq (off + 4) (off + 4) && Nat.beq (off + 12) (off + 12)) = true := by
            rw [nat_beq_refl, nat_beq_refl]; rfl
          have hGdSplit :
              checkPrefixEq expGd lnk = true ∧
              validateLinkedBytesLoop env vaddr f (off + 16) (encodeOpsLoop (off + 16) rest).1
                (encodeOpsLoop (off + 16) rest).2 (lnk.drop 16) = true := by
            cases hrTail : (encodeOpsLoop (off + 16) rest).2 with
            | nil =>
              rw [hrTail] at hVal
              dsimp only [matchRelocAtOff] at hVal
              rw [ite_bool_eq_true hOffGd] at hVal
              cases hChk : checkPrefixEq tmplTlsGdObj (tmplTlsGdObj ++ (encodeOpsLoop (off + 16) rest).1) && checkPrefixEq expGd lnk
              · rw [ite_bool_eq_false hChk] at hVal; dsimp only [matchSingleRelocAtOff] at hVal; cases hVal
              · rw [ite_bool_eq_true hChk] at hVal; dsimp only at hVal
                rw [list_drop_append_of_len tmplTlsGdObj _ tmplTlsGdObj_len] at hVal
                exact ⟨(bool_and_elim hChk).2, hVal⟩
            | cons r3 rs3 =>
              rw [hrTail] at hVal
              dsimp only [matchRelocAtOff] at hVal
              rw [ite_bool_eq_true hOffGd] at hVal
              cases hChk : checkPrefixEq tmplTlsGdObj (tmplTlsGdObj ++ (encodeOpsLoop (off + 16) rest).1) && checkPrefixEq expGd lnk
              · rw [ite_bool_eq_false hChk] at hVal; dsimp only [matchSingleRelocAtOff] at hVal; cases hVal
              · rw [ite_bool_eq_true hChk] at hVal; dsimp only at hVal
                rw [list_drop_append_of_len tmplTlsGdObj _ tmplTlsGdObj_len] at hVal
                exact ⟨(bool_and_elim hChk).2, hVal⟩
          have hLnkEq : lnk = p9 ++ (p7 ++ lnk.drop 16) := by
            have h1 := eq_append_drop_of_checkPrefixEq hGdSplit.1
            have hLen16 : expGd.length = 16 := by
              simp only [expGd, List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
            rw [hLen16, hExpGdP, List.append_assoc] at h1; exact h1
          rw [hLnkEq] at hEfuel; rw [hLnkEq]
          rw [List.length_append, List.length_append] at hEfuel
          have hStep1Fuel : 9 + (p7 ++ lnk.drop 16).length ≤ efuel := by
            rw [List.length_append]
            simp only [p9, p7, List.length_append, List.length_cons, List.length_nil, le32Bytes_length] at hEfuel
            simp only [p7, List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
            exact hEfuel
          rw [execByteStream_step_9b_fs env (vaddr + off) st (p7 ++ lnk.drop 16) efuel hStep1Fuel]
          have hStep2Fuel : 7 + (lnk.drop 16).length ≤ efuel - 1 := by
            simp only [p9, p7, List.length_append, List.length_cons, List.length_nil, le32Bytes_length] at hEfuel
            have h1 : 1 + (7 + (lnk.drop 16).length) ≤ efuel :=
              Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 9) _) hEfuel
            exact nat_le_sub_of_add_le_left h1
          rw [(execByteStream_step_7b_rax env (vaddr + off + 9) _ (env.tlsTpOff s) (lnk.drop 16) (efuel - 1) hStep2Fuel).2.2.2.1]
          rw [writeGpr_rax_full64_rax, writeGpr_rax_overwrite]
          have hEfuel' : (lnk.drop 16).length ≤ efuel - 1 - 1 :=
            nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 7) _) hStep2Fuel)
          have hPcEq : vaddr + off + 9 + 7 = vaddr + (off + 16) := by
            rw [Nat.add_assoc (vaddr + off) 9 7, Nat.add_assoc vaddr off 16]
          rw [hPcEq]
          exact ih (off + 16) f (efuel - 1 - 1) (lnk.drop 16) _ hEnvNext hRestReach' hEfuel' hGdSplit.2
      | tlsLdAddr s =>
        cases fuel with
        | zero => cases hVal
        | succ f =>
          rw [enc_tlsLdAddr] at hVal hRestReach'; simp only [tmplTlsLdObj_len] at hVal hRestReach'
          rw [reloc_cons3_append, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_tlsld _ _ _ _)] at hVal
          let p12 := [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64,
                      BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25,
                      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0]
          let p7 := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
          let expLea := p12 ++ [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
          let expMov := p12 ++ [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
          have hExpLeaP : expLea = p12 ++ p7 := rfl
          have hOffLd : (Nat.beq (off + 3) (off + 3) && Nat.beq (off + 8) (off + 8) &&
              Nat.beq (off + 15) (off + 15) && Nat.beq s s) = true := by
            rw [nat_beq_refl, nat_beq_refl, nat_beq_refl, nat_beq_refl]; rfl
          have hNot8B : (checkPrefixEq (tmplTlsLdObj 0x8B) (tmplTlsLdObj 0x8D ++ (encodeOpsLoop (off + 19) rest).1) &&
              checkPrefixEq expMov lnk) = false := by
            rw [checkPrefixEq_tlsLd_8B_8D]; rfl
          dsimp only [matchRelocAtOff] at hVal
          rw [ite_bool_eq_true hOffLd] at hVal
          cases hChk : checkPrefixEq (tmplTlsLdObj 0x8D) (tmplTlsLdObj 0x8D ++ (encodeOpsLoop (off + 19) rest).1) && checkPrefixEq expLea lnk
          · rw [ite_bool_eq_false hChk, ite_bool_eq_false hNot8B] at hVal
            dsimp only [matchSingleRelocAtOff] at hVal; cases hVal
          · rw [ite_bool_eq_true hChk] at hVal; dsimp only at hVal
            have ⟨_, hExp⟩ := bool_and_elim hChk
            rw [list_drop_append_of_len (tmplTlsLdObj 0x8D) _ (tmplTlsLdObj_len 0x8D)] at hVal
            have hLnkEq : lnk = p12 ++ (p7 ++ lnk.drop 19) := by
              have h1 := eq_append_drop_of_checkPrefixEq hExp
              have hLen19 : expLea.length = 19 := by
                simp only [expLea, p12, List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
              rw [hLen19, hExpLeaP, List.append_assoc] at h1; exact h1
            rw [hLnkEq] at hEfuel; rw [hLnkEq]
            rw [List.length_append, List.length_append] at hEfuel
            simp only [p12, p7, List.length_append, List.length_cons, List.length_nil, le32Bytes_length] at hEfuel
            have hStep1Fuel : 12 + (p7 ++ lnk.drop 19).length ≤ efuel := by
              simp only [p7, List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
              exact hEfuel
            rw [execByteStream_step_12b_fs env (vaddr + off) st (p7 ++ lnk.drop 19) efuel hStep1Fuel]
            have hStep2Fuel : 7 + (lnk.drop 19).length ≤ efuel - 1 :=
              nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 12) _) hEfuel)
            rw [(execByteStream_step_7b_rax env (vaddr + off + 12) _ (env.tlsTpOff s) (lnk.drop 19) (efuel - 1) hStep2Fuel).2.2.2.1]
            rw [writeGpr_rax_full64_rax, writeGpr_rax_overwrite]
            have hEfuel' : (lnk.drop 19).length ≤ efuel - 1 - 1 :=
              nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 7) _) hStep2Fuel)
            have hPcEq : vaddr + off + 12 + 7 = vaddr + (off + 19) := by
              rw [Nat.add_assoc (vaddr + off) 12 7, Nat.add_assoc vaddr off 19]
            rw [hPcEq]
            exact ih (off + 19) f (efuel - 1 - 1) (lnk.drop 19) _ hEnvNext hRestReach' hEfuel' hVal
      | tlsLdLoad s =>
        cases fuel with
        | zero => cases hVal
        | succ f =>
          rw [enc_tlsLdLoad] at hVal hRestReach'; simp only [tmplTlsLdObj_len] at hVal hRestReach'
          rw [reloc_cons3_append, validateLinkedBytesLoop_cons_reloc, ite_bool_eq_true (anch_tlsld _ _ _ _)] at hVal
          let p12 := [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64,
                      BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25,
                      BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0, BitVec.ofNat 8 0]
          let p7 := [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
          let expLea := p12 ++ [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
          let expMov := p12 ++ [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80] ++ le32Bytes (env.tlsTpOff s)
          have hExpMovP : expMov = p12 ++ p7 := rfl
          have hOffLd : (Nat.beq (off + 3) (off + 3) && Nat.beq (off + 8) (off + 8) &&
              Nat.beq (off + 15) (off + 15) && Nat.beq s s) = true := by
            rw [nat_beq_refl, nat_beq_refl, nat_beq_refl, nat_beq_refl]; rfl
          have hNot8D : (checkPrefixEq (tmplTlsLdObj 0x8D) (tmplTlsLdObj 0x8B ++ (encodeOpsLoop (off + 19) rest).1) &&
              checkPrefixEq expLea lnk) = false := by
            rw [checkPrefixEq_tlsLd_8D_8B]; rfl
          dsimp only [matchRelocAtOff] at hVal
          rw [ite_bool_eq_true hOffLd, ite_bool_eq_false hNot8D] at hVal
          cases hChk : checkPrefixEq (tmplTlsLdObj 0x8B) (tmplTlsLdObj 0x8B ++ (encodeOpsLoop (off + 19) rest).1) && checkPrefixEq expMov lnk
          · rw [ite_bool_eq_false hChk] at hVal
            dsimp only [matchSingleRelocAtOff] at hVal; cases hVal
          · rw [ite_bool_eq_true hChk] at hVal; dsimp only at hVal
            have ⟨_, hExp⟩ := bool_and_elim hChk
            rw [list_drop_append_of_len (tmplTlsLdObj 0x8B) _ (tmplTlsLdObj_len 0x8B)] at hVal
            have hLnkEq : lnk = p12 ++ (p7 ++ lnk.drop 19) := by
              have h1 := eq_append_drop_of_checkPrefixEq hExp
              have hLen19 : expMov.length = 19 := by
                simp only [expMov, p12, List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
              rw [hLen19, hExpMovP, List.append_assoc] at h1; exact h1
            rw [hLnkEq] at hEfuel; rw [hLnkEq]
            rw [List.length_append, List.length_append] at hEfuel
            simp only [p12, p7, List.length_append, List.length_cons, List.length_nil, le32Bytes_length] at hEfuel
            have hStep1Fuel : 12 + (p7 ++ lnk.drop 19).length ≤ efuel := by
              simp only [p7, List.length_append, List.length_cons, List.length_nil, le32Bytes_length]
              exact hEfuel
            rw [execByteStream_step_12b_fs env (vaddr + off) st (p7 ++ lnk.drop 19) efuel hStep1Fuel]
            have hStep2Fuel : 7 + (lnk.drop 19).length ≤ efuel - 1 :=
              nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 12) _) hEfuel)
            rw [(execByteStream_step_7b_rax env (vaddr + off + 12) _ (env.tlsTpOff s) (lnk.drop 19) (efuel - 1) hStep2Fuel).2.2.2.2]
            rw [writeGpr_rax_full64_rax, writeGpr_rax_full64_mem, writeGpr_rax_overwrite]
            have hEfuel' : (lnk.drop 19).length ≤ efuel - 1 - 1 :=
              nat_le_sub_of_add_le_left (Nat.le_trans (Nat.add_le_add_right (by decide : 1 ≤ 7) _) hStep2Fuel)
            have hPcEq : vaddr + off + 12 + 7 = vaddr + (off + 19) := by
              rw [Nat.add_assoc (vaddr + off) 12 7, Nat.add_assoc vaddr off 19]
            rw [hPcEq]
            exact ih (off + 19) f (efuel - 1 - 1) (lnk.drop 19) _ hEnvNext hRestReach' hEfuel' hVal

/-! ### Layer 5: Two-Phase `%r11` Fixed-Stride Probe Loop & `O(log n)` `.eh_frame_hdr` Binary Search -/

private theorem natMax_le {a b m : Nat} (ha : a ≤ m) (hb : b ≤ m) : natMax a b ≤ m := by
  dsimp only [natMax]
  cases Nat.decLt a b with
  | isTrue h => rw [ite_prop_true h]; exact hb
  | isFalse h => rw [ite_prop_false h]; exact ha

private theorem stride_step_sub (base rem stride : Nat) :
    base + (rem + 1) * stride - stride = base + rem * stride := by
  rw [Nat.succ_mul, ← Nat.add_assoc, Nat.add_sub_cancel]

private theorem stride_step_gap (base rem stride : Nat) :
    base + (rem + 1) * stride - (base + rem * stride) = stride := by
  rw [Nat.succ_mul, ← Nat.add_assoc, Nat.add_sub_cancel_left]

private theorem runFixedStrideR11Loop_step (k : Nat) (st : ProbeState) (hne : st.rsp ≠ st.r11)
    (rsp1 gap1 : Nat) (hrsp : st.rsp - 4096 = rsp1) (hgap : st.lastProbedRsp - rsp1 = gap1) :
    runFixedStrideR11Loop (k + 1) st =
      runFixedStrideR11Loop k
        { rsp := rsp1, r11 := st.r11, lastProbedRsp := rsp1,
          maxUnprobedGap := natMax st.maxUnprobedGap gap1, cfaRule := st.cfaRule } := by
  dsimp only [runFixedStrideR11Loop]
  rw [ite_prop_false hne, hrsp, hgap]

private theorem runFixedStrideR11Loop_inv (k : Nat) :
    ∀ (rem : Nat) (st : ProbeState),
      st.rsp = st.r11 + rem * 4096 →
      st.lastProbedRsp = st.rsp →
      st.maxUnprobedGap ≤ 4096 →
      (runFixedStrideR11Loop k st).r11 = st.r11 ∧
      (runFixedStrideR11Loop k st).cfaRule = st.cfaRule ∧
      (runFixedStrideR11Loop k st).maxUnprobedGap ≤ 4096 ∧
      (runFixedStrideR11Loop k st).lastProbedRsp = (runFixedStrideR11Loop k st).rsp ∧
      (rem ≤ k → (runFixedStrideR11Loop k st).rsp = st.r11) := by
  induction k with
  | zero =>
    intro rem st hRsp hLast hGap
    dsimp only [runFixedStrideR11Loop]
    refine ⟨rfl, rfl, hGap, hLast, fun hle => ?_⟩
    have h0 : rem = 0 := Nat.eq_zero_of_le_zero hle
    subst h0; rw [hRsp]; exact Nat.add_zero _
  | succ k ih =>
    intro rem st hRsp hLast hGap
    cases rem with
    | zero =>
      have heq : st.rsp = st.r11 := by rw [hRsp]; exact Nat.add_zero _
      dsimp only [runFixedStrideR11Loop]
      rw [ite_prop_true heq]
      exact ⟨rfl, rfl, hGap, hLast, fun _ => heq⟩
    | succ rem' =>
      have hne : st.rsp ≠ st.r11 := by
        intro heq
        have hlt : st.r11 < st.r11 + (rem' + 1) * 4096 :=
          Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.succ_pos rem') (by decide))
        rw [← hRsp, heq] at hlt
        exact Nat.lt_irrefl _ hlt
      have hRsp' : st.rsp - 4096 = st.r11 + rem' * 4096 := by
        rw [hRsp]; exact stride_step_sub st.r11 rem' 4096
      have hGapStep : st.lastProbedRsp - (st.r11 + rem' * 4096) = 4096 := by
        rw [hLast, hRsp]; exact stride_step_gap st.r11 rem' 4096
      rw [runFixedStrideR11Loop_step k st hne (st.r11 + rem' * 4096) 4096 hRsp' hGapStep]
      have hMaxLe : natMax st.maxUnprobedGap 4096 ≤ 4096 :=
        natMax_le hGap (Nat.le_refl 4096)
      have hRec := ih rem'
        { rsp := st.r11 + rem' * 4096, r11 := st.r11, lastProbedRsp := st.r11 + rem' * 4096,
          maxUnprobedGap := natMax st.maxUnprobedGap 4096, cfaRule := st.cfaRule }
        rfl rfl hMaxLe
      exact ⟨hRec.1, hRec.2.1, hRec.2.2.1, hRec.2.2.2.1, fun hle => hRec.2.2.2.2 (Nat.le_of_succ_le_succ hle)⟩

private theorem relocateEhTable_sorted (baseAddr : Nat) :
    ∀ {lo : Nat} {tbl : List EhFrameEntry},
      EhTableSorted lo tbl → EhTableSorted (baseAddr + lo) (relocateEhTable baseAddr tbl)
  | _, [], .nil => .nil
  | _, _ :: _, .cons hlo hlt hrest =>
    .cons (Nat.add_le_add_left hlo baseAddr)
          (Nat.add_lt_add_left hlt baseAddr)
          (relocateEhTable_sorted baseAddr hrest)

private theorem lookupEhFrame_relocate (baseAddr pc : Nat) (tbl : List EhFrameEntry) :
    lookupEhFrame (baseAddr + pc) (relocateEhTable baseAddr tbl) = lookupEhFrame pc tbl := by
  induction tbl with
  | nil => rfl
  | cons e rest ih =>
    dsimp only [relocateEhTable, lookupEhFrame]
    cases Decidable.em (e.startPc ≤ pc ∧ pc < e.endPc) with
    | inl h =>
      have h' : baseAddr + e.startPc ≤ baseAddr + pc ∧ baseAddr + pc < baseAddr + e.endPc :=
        ⟨Nat.add_le_add_left h.1 baseAddr, Nat.add_lt_add_left h.2 baseAddr⟩
      rw [ite_prop_true h', ite_prop_true h]
    | inr h =>
      have h' : ¬(baseAddr + e.startPc ≤ baseAddr + pc ∧ baseAddr + pc < baseAddr + e.endPc) := by
        intro hc
        exact h ⟨Nat.le_of_add_le_add_left hc.1, nat_lt_of_add_lt_add_left hc.2⟩
      rw [ite_prop_false h', ite_prop_false h]
      exact ih

private theorem sorted_lo_le_all {lo : Nat} {tbl : List EhFrameEntry}
    (hS : EhTableSorted lo tbl) :
    ∀ {i : Nat} {e : EhFrameEntry}, listGet? tbl i = some e → lo ≤ e.startPc ∧ e.startPc < e.endPc := by
  induction hS with
  | nil => intro i e h; cases h
  | @cons lo0 e0 rest hlo hlt hrest ih =>
    intro i e h
    cases i with
    | zero =>
      dsimp only [listGet?] at h; injection h with heq; subst heq
      exact ⟨hlo, hlt⟩
    | succ i' =>
      have ⟨h1, h2⟩ := ih h
      exact ⟨Nat.le_trans hlo (Nat.le_trans (Nat.le_of_lt hlt) h1), h2⟩

private theorem sorted_listGet_mono {lo : Nat} {tbl : List EhFrameEntry}
    (hS : EhTableSorted lo tbl) :
    ∀ {i j : Nat} {ei ej : EhFrameEntry},
      i < j → listGet? tbl i = some ei → listGet? tbl j = some ej → ei.endPc ≤ ej.startPc := by
  induction hS with
  | nil => intro _ _ _ _ _ h _; cases h
  | @cons lo0 e0 rest hlo hlt hrest ih =>
    intro i j ei ej hij hi hj
    cases i with
    | zero =>
      dsimp only [listGet?] at hi; injection hi with heq; subst heq
      cases j with
      | zero => exact False.elim (Nat.lt_irrefl 0 hij)
      | succ j' => exact (sorted_lo_le_all hrest hj).1
    | succ i' =>
      cases j with
      | zero => exact False.elim (Nat.not_lt_zero _ hij)
      | succ j' => exact ih (Nat.lt_of_succ_lt_succ hij) hi hj

private theorem listGet_some_of_lt {α : Type} :
    ∀ (xs : List α) (i : Nat), i < xs.length → ∃ x, listGet? xs i = some x
  | [], _, h => False.elim (Nat.not_lt_zero _ h)
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: xs, i + 1, h => listGet_some_of_lt xs i (Nat.lt_of_succ_lt_succ h)

private theorem listGet_lt_length {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α}, listGet? xs i = some x → i < xs.length
  | [], _, _, h => by cases h
  | _ :: _, 0, _, _ => Nat.succ_pos _
  | _ :: xs, i + 1, _, h => Nat.succ_lt_succ (listGet_lt_length h)

private theorem listGet_mem {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α}, listGet? xs i = some x → x ∈ xs
  | [], _, _, h => by cases h
  | _ :: _, 0, _, h => by dsimp only [listGet?] at h; injection h with heq; subst heq; exact List.Mem.head _
  | _ :: xs, i + 1, _, h => List.Mem.tail _ (listGet_mem h)

private theorem mem_iff_listGet {α : Type} {xs : List α} {x : α} (h : x ∈ xs) :
    ∃ i, i < xs.length ∧ listGet? xs i = some x := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    cases h with
    | head => exact ⟨0, Nat.succ_pos _, rfl⟩
    | tail _ hm =>
      have ⟨i, hlt, hg⟩ := ih hm
      exact ⟨i + 1, Nat.succ_lt_succ hlt, hg⟩

private theorem lookupEhFrame_of_listGet {lo : Nat} {tbl : List EhFrameEntry}
    (hS : EhTableSorted lo tbl) :
    ∀ {i : Nat} {e : EhFrameEntry} {pc : Nat},
      listGet? tbl i = some e → e.startPc ≤ pc → pc < e.endPc →
      lookupEhFrame pc tbl = some e.cfaRule := by
  induction hS with
  | nil => intro _ _ _ h; cases h
  | @cons lo0 e0 rest hlo hlt hrest ih =>
    intro i e pc hGet hGe hLt
    cases i with
    | zero =>
      dsimp only [listGet?] at hGet; injection hGet with heq; subst heq
      dsimp only [lookupEhFrame]
      rw [ite_prop_true ⟨hGe, hLt⟩]
    | succ i' =>
      have hAfter : e0.endPc ≤ e.startPc := (sorted_lo_le_all hrest hGet).1
      have hNot0 : ¬(e0.startPc ≤ pc ∧ pc < e0.endPc) := fun hc =>
        Nat.not_lt_of_ge (Nat.le_trans hAfter hGe) hc.2
      dsimp only [lookupEhFrame]
      rw [ite_prop_false hNot0]
      exact ih hGet hGe hLt

private theorem lookupEhFrame_none_of_miss {tbl : List EhFrameEntry} {pc : Nat}
    (hMiss : ∀ i e, listGet? tbl i = some e → pc < e.startPc ∨ e.endPc ≤ pc) :
    lookupEhFrame pc tbl = none := by
  induction tbl with
  | nil => rfl
  | cons e0 rest ih =>
    have h0 : pc < e0.startPc ∨ e0.endPc ≤ pc := hMiss 0 e0 rfl
    have hNot0 : ¬(e0.startPc ≤ pc ∧ pc < e0.endPc) := by
      intro hc
      cases h0 with
      | inl hl => exact Nat.not_lt_of_ge hc.1 hl
      | inr hr => exact Nat.not_lt_of_ge hr hc.2
    dsimp only [lookupEhFrame]
    rw [ite_prop_false hNot0]
    exact ih (fun i e hg => hMiss (i + 1) e hg)

private theorem lookupEhFrame_some_inv {tbl : List EhFrameEntry} {pc : Nat} {r : CfaRule}
    (h : lookupEhFrame pc tbl = some r) :
    ∃ e, e ∈ tbl ∧ e.startPc ≤ pc ∧ pc < e.endPc ∧ e.cfaRule = r := by
  induction tbl with
  | nil => cases h
  | cons e0 rest ih =>
    dsimp only [lookupEhFrame] at h
    cases Decidable.em (e0.startPc ≤ pc ∧ pc < e0.endPc) with
    | inl hc =>
      rw [ite_prop_true hc] at h
      injection h with hr
      exact ⟨e0, List.Mem.head _, hc.1, hc.2, hr⟩
    | inr hc =>
      rw [ite_prop_false hc] at h
      have ⟨e, hm, h1, h2, h3⟩ := ih h
      exact ⟨e, List.Mem.tail _ hm, h1, h2, h3⟩

private theorem div2_lt_self {n : Nat} (h : 0 < n) : Nat.div n 2 < n :=
  Nat.div_lt_self h (by decide)

private theorem bsearchEhLoop_eq_lookup {minPc : Nat} {tbl : List EhFrameEntry}
    (hS : EhTableSorted minPc tbl) (pc : Nat) :
    ∀ (fuel loIdx hiIdx : Nat),
      hiIdx ≤ tbl.length →
      hiIdx - loIdx ≤ fuel →
      (∀ j e, j < loIdx → listGet? tbl j = some e → e.endPc ≤ pc) →
      (∀ j e, hiIdx ≤ j → listGet? tbl j = some e → pc < e.startPc) →
      bsearchEhLoop pc tbl fuel loIdx hiIdx = lookupEhFrame pc tbl := by
  intro fuel
  induction fuel with
  | zero =>
    intro loIdx hiIdx _ hDiff hLeft hRight
    have hLe : hiIdx ≤ loIdx := Nat.le_of_sub_eq_zero (Nat.eq_zero_of_le_zero hDiff)
    dsimp only [bsearchEhLoop]
    apply Eq.symm
    apply lookupEhFrame_none_of_miss
    intro j e hg
    cases Nat.lt_or_ge j loIdx with
    | inl hlt => exact Or.inr (hLeft j e hlt hg)
    | inr hge => exact Or.inl (hRight j e (Nat.le_trans hLe hge) hg)
  | succ fuel ih =>
    intro loIdx hiIdx hHiLe hDiff hLeft hRight
    dsimp only [bsearchEhLoop]
    cases Nat.decLe hiIdx loIdx with
    | isTrue hLe =>
      rw [ite_prop_true hLe]
      apply Eq.symm
      apply lookupEhFrame_none_of_miss
      intro j e hg
      cases Nat.lt_or_ge j loIdx with
      | inl hlt => exact Or.inr (hLeft j e hlt hg)
      | inr hge => exact Or.inl (hRight j e (Nat.le_trans hLe hge) hg)
    | isFalse hNotLe =>
      rw [ite_prop_false hNotLe]
      have hLt : loIdx < hiIdx := Nat.gt_of_not_le hNotLe
      have hSpanPos : 0 < hiIdx - loIdx := Nat.sub_pos_of_lt hLt
      let mid := loIdx + Nat.div (hiIdx - loIdx) 2
      have hMidLtHi : mid < hiIdx := by
        have h1 : Nat.div (hiIdx - loIdx) 2 < hiIdx - loIdx := div2_lt_self hSpanPos
        have h2 := Nat.add_lt_add_left h1 loIdx
        rw [Nat.add_sub_of_le (Nat.le_of_lt hLt)] at h2
        exact h2
      have hMidLtLen : mid < tbl.length := Nat.lt_of_lt_of_le hMidLtHi hHiLe
      have ⟨em, hGetMid⟩ := listGet_some_of_lt tbl mid hMidLtLen
      rw [hGetMid]
      dsimp only
      cases Nat.decLt pc em.startPc with
      | isTrue hPcLtStart =>
        rw [ite_prop_true hPcLtStart]
        have hDiffL : mid - loIdx ≤ fuel := by
          have h1 : mid - loIdx < hiIdx - loIdx := Nat.sub_lt_sub_right (Nat.le_add_right loIdx _) hMidLtHi
          exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h1 hDiff)
        have hRightL : ∀ j e, mid ≤ j → listGet? tbl j = some e → pc < e.startPc := by
          intro j ej hMidLeJ hGetJ
          cases Nat.eq_or_lt_of_le hMidLeJ with
          | inl hEq =>
            subst hEq; rw [hGetMid] at hGetJ; injection hGetJ with hE; subst hE
            exact hPcLtStart
          | inr hMidLtJ =>
            have hMono := sorted_listGet_mono hS hMidLtJ hGetMid hGetJ
            have hEmLt := (sorted_lo_le_all hS hGetMid).2
            exact Nat.lt_of_lt_of_le (Nat.lt_trans hPcLtStart hEmLt) hMono
        exact ih loIdx mid (Nat.le_of_lt hMidLtLen) hDiffL hLeft hRightL
      | isFalse hNotLtStart =>
        rw [ite_prop_false hNotLtStart]
        have hStartLePc : em.startPc ≤ pc := Nat.ge_of_not_lt hNotLtStart
        cases Nat.decLt pc em.endPc with
        | isTrue hPcLtEnd =>
          rw [ite_prop_true hPcLtEnd]
          exact Eq.symm (lookupEhFrame_of_listGet hS hGetMid hStartLePc hPcLtEnd)
        | isFalse hNotLtEnd =>
          rw [ite_prop_false hNotLtEnd]
          have hEndLePc : em.endPc ≤ pc := Nat.ge_of_not_lt hNotLtEnd
          have hDiffR : hiIdx - (mid + 1) ≤ fuel := by
            have h1 : loIdx < mid + 1 := Nat.lt_succ_of_le (Nat.le_add_right loIdx _)
            have h2 : hiIdx - (mid + 1) < hiIdx - loIdx := Nat.sub_lt_sub_left hLt h1
            exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le h2 hDiff)
          have hLeftR : ∀ j e, j < mid + 1 → listGet? tbl j = some e → e.endPc ≤ pc := by
            intro j ej hJLt hGetJ
            have hJLeMid : j ≤ mid := Nat.le_of_lt_succ hJLt
            cases Nat.eq_or_lt_of_le hJLeMid with
            | inl hEq =>
              subst hEq; rw [hGetMid] at hGetJ; injection hGetJ with hE; subst hE
              exact hEndLePc
            | inr hJLtMid =>
              have hMono := sorted_listGet_mono hS hJLtMid hGetJ hGetMid
              have hEmLt := (sorted_lo_le_all hS hGetMid).2
              exact Nat.le_trans hMono (Nat.le_trans (Nat.le_of_lt hEmLt) hEndLePc)
          exact ih (mid + 1) hiIdx hHiLe hDiffR hLeftR hRight

end Stage4ProofHelpers

/-! ## Part VII: Core Target Theorems (To Be Frozen in Stage 3 & Proved in Stage 4) -/

/-- **Theorem 1 (Codec Roundtrips & Multi-Op Post-Link Byte-Span Invariance):**
(a) `decodeLe16 (le16Bytes w16) = some w16` and `decodeLe32 (le32Bytes w32) = some w32`;
(b) For EVERY `MiniMach` function `ops`, `linkFn env vaddr true padBytes ops`
    and `linkFn env vaddr false padBytes ops` have byte length
    `(encodeFn fnSym ops).code.length + padBytes` — proving zero intra-function
    PC drift or `.eh_frame` FDE length corruption across all post-link
    relaxations! -/
theorem codecs_and_multifn_relaxation_preserve_byte_span
    (w16 : BitVec 16) (w32 : BitVec 32) (env : LinkEnv) (vaddr padBytes : Nat)
    (fnSym : SymId) (ops : List MiniMachOp) :
    decodeLe16 (le16Bytes w16) = some w16 ∧
    decodeLe32 (le32Bytes w32) = some w32 ∧
    (linkFn env vaddr true padBytes ops).length = (encodeFn fnSym ops).code.length + padBytes ∧
    (linkFn env vaddr false padBytes ops).length = (encodeFn fnSym ops).code.length + padBytes := by
  refine ⟨decodeLe16_le16Bytes w16, decodeLe32_le32Bytes w32, ?_, ?_⟩
  · dsimp only [linkFn, encodeFn]
    rw [List.length_append, linkOpsLoop_length, mkInt3Pad_length]
  · dsimp only [linkFn, encodeFn]
    rw [List.length_append, linkOpsLoop_length, mkInt3Pad_length]

/-- **Theorem 2 (AST-Free Post-Link Validator Soundness, Completeness, & Tamper Rejection):**
1. **Completeness:** For every `ops` valid for `relax` (`OpsValidForRelaxMode`),
   `padBytes`, `env`, `vaddr`, `fnSym`, `validateLinkedBytes` accepts `linkFn`.
2. **AST-Free Soundness (Full Signed `[-2^31, 2^31)` PC-Rel & Multi-Instruction
   Shifted-Boundary Decoding):** For ANY `ops` (`OpsPcRelReachable env vaddr ops`),
   ANY `LinkEnvConsistent env st`, and ANY raw candidate byte stream `linkedBytes`,
   if `validateLinkedBytes env vaddr (encodeFn fnSym ops).code (encodeFn fnSym ops).relocs linkedBytes = true`,
   then single-instruction byte-stream execution `execByteStream env vaddr linkedBytes st`
   returns `some (execMiniMachFn env ops st)`!
   *(Covers `movImm32` (`full64` sign-ext & `zeroExt32`), `movImm16` (`lo16PreserveUpper48`),
   `movReg` (all 3 `WriteMode`s), `leaRipSym`, `loadGotStrict`, relaxed & unrelaxed
   `loadGotRelaxable`, relaxed & unrelaxed `tlsGotTpOff`, shifted `9B+7B` `tlsGdAddr`,
   shifted `12B+7B` `tlsLdAddr` & live `E3-1` `tlsLdLoad`, `callSym`, `ret`, and
   trailing `0xCC` padding.)*
3. **Tamper Rejection:** For ALL `env vaddr s`, tampering `48 8b 05 -> 48 8d 05`
   on non-relaxable `R_X86_64_GOTPCREL` (`loadGotStrict s`) is rejected
   (`validateLinkedBytes ... = false`)! -/
theorem postlink_validator_sound_complete_and_tamper_rejecting
    (env : LinkEnv) (vaddr padBytes : Nat) (fnSym : SymId) (relax : Bool)
    (ops : List MiniMachOp) (st : MachState) (linkedBytes : List (BitVec 8)) :
    (OpsValidForRelaxMode relax ops →
      let obj := encodeFn fnSym ops
      validateLinkedBytes env vaddr obj.code obj.relocs
        (linkFn env vaddr relax padBytes ops) = true) ∧
    (LinkEnvConsistent env st →
      OpsPcRelReachable env vaddr ops →
      let obj := encodeFn fnSym ops
      validateLinkedBytes env vaddr obj.code obj.relocs linkedBytes = true →
      execByteStream env vaddr linkedBytes st = some (execMiniMachFn env ops st)) ∧
    (∀ s : SymId,
      let obj := encodeFn fnSym [.loadGotStrict s]
      let tampered := linkOneOpBytes env vaddr true (.loadGotRelaxable s)
      validateLinkedBytes env vaddr obj.code obj.relocs tampered = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hMode
    dsimp only [encodeFn, linkFn, validateLinkedBytes]
    have h0 := validate_complete_loop env vaddr padBytes relax ops hMode
      (encodeOpsLoop 0 ops).1.length 0 (Nat.le_refl _)
    rw [Nat.add_zero] at h0
    exact h0
  · intro hEnv hReach
    dsimp only [encodeFn, validateLinkedBytes, execByteStream]
    intro hVal
    have h0 := validate_sound_loop env vaddr ops 0 (encodeOpsLoop 0 ops).1.length
      linkedBytes.length linkedBytes st hEnv (by rw [Nat.add_zero]; exact hReach) (Nat.le_refl _) hVal
    rw [Nat.add_zero] at h0
    exact h0
  · intro s
    dsimp only [encodeFn, encodeOpsLoop, encodeOneOp, linkOneOpBytes, validateLinkedBytes,
                validateLinkedBytesLoop, isRelocAnchoredAt, List.append_nil, List.nil_append]
    dsimp only [matchRelocAtOff, matchSingleRelocAtOff, checkPrefixEq, tmplMovRip,
                List.length_cons, List.length_nil, List.cons_append, List.take_succ_cons,
                List.take_zero, byteListEq]
    rfl

/-- **Theorem 3 (Two-Phase `%r11` Fixed-Stride Probe Loop CFA & `O(log n)`
Relocated `.eh_frame_hdr` Binary Search Soundness):**
(a) For ANY `(rsp0 savedCfaOff numPages tailBytes)` with `8 ≤ savedCfaOff`,
    `savedCfaOff - 8 ≤ 4096`, `tailBytes < 4096`, and
    `savedCfaOff - 8 + numPages * 4096 + tailBytes ≤ rsp0`:
    - At EVERY iteration `k`, `evalCfa = rsp0 + 8` and `maxUnprobedGap ≤ 4096`;
    - At `k ≥ numPages`, the fixed-stride loop exits at `rsp = r11` with
      `lastProbedRsp = rsp`;
    - After Phase 4 `finishR11ProbeTail`, `evalCfa = rsp0 + 8` and
      `maxUnprobedGap ≤ 4096`!
(b) For ANY strictly sorted `.eh_frame_hdr` table `EhTableSorted lo tbl` and
    post-link `baseAddr`:
    - `bsearchEhFrame pc tbl = lookupEhFrame pc tbl` for EVERY `pc`;
    - Hit completeness (`e ∈ tbl ∧ e.startPc ≤ pc < e.endPc → bsearch = some e.cfaRule`);
    - Converse soundness (`bsearch = some r → ∃ e ∈ tbl, e.startPc ≤ pc ∧ pc < e.endPc ∧ e.cfaRule = r`);
    - Gap / `0xCC`-padding rejection (`(∀ e ∈ tbl, pc < e.startPc ∨ e.endPc ≤ pc) → bsearch = none`);
    - Post-link FDE relocation invariance: `EhTableSorted (baseAddr + lo) (relocateEhTable baseAddr tbl)`
      and `bsearchEhFrame (baseAddr + pc) (relocateEhTable baseAddr tbl) = bsearchEhFrame pc tbl`! -/
theorem r11_two_phase_probe_and_eh_frame_bsearch_sound
    (rsp0 savedCfaOff numPages tailBytes k : Nat)
    (hSavedGe : 8 ≤ savedCfaOff)
    (hPushBound : savedCfaOff - 8 ≤ 4096)
    (hTailBound : tailBytes < 4096)
    (hFit : (savedCfaOff - 8) + numPages * 4096 + tailBytes ≤ rsp0)
    (lo baseAddr : Nat) (tbl : List EhFrameEntry) (hSorted : EhTableSorted lo tbl) :
    let st0 := initR11ProbePrologue rsp0 savedCfaOff numPages
    let stK := runFixedStrideR11Loop k st0
    (evalCfa stK = rsp0 + 8 ∧ stK.maxUnprobedGap ≤ 4096 ∧
     (numPages ≤ k →
       stK.rsp = st0.r11 ∧ stK.lastProbedRsp = st0.r11 ∧
       let stDone := finishR11ProbeTail savedCfaOff numPages tailBytes stK
       evalCfa stDone = rsp0 + 8 ∧ stDone.maxUnprobedGap ≤ 4096)) ∧
    EhTableSorted (baseAddr + lo) (relocateEhTable baseAddr tbl) ∧
    (∀ pc, bsearchEhFrame pc tbl = lookupEhFrame pc tbl) ∧
    (∀ e pc, e ∈ tbl → e.startPc ≤ pc → pc < e.endPc →
      bsearchEhFrame pc tbl = some e.cfaRule) ∧
    (∀ pc r, bsearchEhFrame pc tbl = some r →
      ∃ e, e ∈ tbl ∧ e.startPc ≤ pc ∧ pc < e.endPc ∧ e.cfaRule = r) ∧
    (∀ pc, (∀ e, e ∈ tbl → pc < e.startPc ∨ e.endPc ≤ pc) →
      bsearchEhFrame pc tbl = none) ∧
    (∀ pc, bsearchEhFrame (baseAddr + pc) (relocateEhTable baseAddr tbl) =
      bsearchEhFrame pc tbl) := by
  let st0 := initR11ProbePrologue rsp0 savedCfaOff numPages
  have hPushLeRsp0 : savedCfaOff - 8 ≤ rsp0 :=
    Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) hFit)
  have hPagesLeRsp1 : numPages * 4096 ≤ rsp0 - (savedCfaOff - 8) := by
    have h1 : (savedCfaOff - 8) + numPages * 4096 ≤ rsp0 := Nat.le_trans (Nat.le_add_right _ _) hFit
    exact nat_le_sub_of_add_le_left h1
  have hTailLeR11 : tailBytes ≤ (rsp0 - (savedCfaOff - 8)) - numPages * 4096 := by
    have h1 : (savedCfaOff - 8) + numPages * 4096 + tailBytes ≤ rsp0 := hFit
    have h2 : numPages * 4096 + tailBytes ≤ rsp0 - (savedCfaOff - 8) := by
      rw [Nat.add_assoc] at h1; exact nat_le_sub_of_add_le_left h1
    exact nat_le_sub_of_add_le_left h2
  have hRspInit : st0.rsp = st0.r11 + numPages * 4096 :=
    Eq.symm (Nat.sub_add_cancel hPagesLeRsp1)
  have hInv := runFixedStrideR11Loop_inv k numPages st0 hRspInit rfl hPushBound
  have hCfa0 : evalCfa st0 = rsp0 + 8 := by
    dsimp only [evalCfa, st0, initR11ProbePrologue]
    rw [Nat.add_comm (rsp0 - (savedCfaOff - 8) - numPages * 4096) (savedCfaOff + numPages * 4096),
        Nat.add_assoc savedCfaOff (numPages * 4096), Nat.add_comm (numPages * 4096),
        Nat.sub_add_cancel hPagesLeRsp1]
    have h8 : savedCfaOff = (savedCfaOff - 8) + 8 := Eq.symm (Nat.sub_add_cancel hSavedGe)
    rw [Nat.add_comm savedCfaOff, h8, Nat.add_sub_cancel, ← Nat.add_assoc, Nat.sub_add_cancel hPushLeRsp0]
  have hBsearchAll : ∀ pc, bsearchEhFrame pc tbl = lookupEhFrame pc tbl := fun pc =>
    bsearchEhLoop_eq_lookup hSorted pc tbl.length 0 tbl.length (Nat.le_refl _)
      (by rw [Nat.sub_zero]; exact Nat.le_refl _)
      (fun _ _ hlt _ => False.elim (Nat.not_lt_zero _ hlt))
      (fun j _ hge hg => False.elim (Nat.not_lt_of_ge hge (listGet_lt_length hg)))
  have hRelSorted : EhTableSorted (baseAddr + lo) (relocateEhTable baseAddr tbl) :=
    relocateEhTable_sorted baseAddr hSorted
  refine ⟨⟨?_, hInv.2.2.1, fun hge => ?_⟩, hRelSorted, hBsearchAll, ?_, ?_, ?_, ?_⟩
  · dsimp only [evalCfa]
    rw [hInv.2.1, hInv.1]
    exact hCfa0
  · have hRspDone : (runFixedStrideR11Loop k st0).rsp = st0.r11 := hInv.2.2.2.2 hge
    have hLastDone : (runFixedStrideR11Loop k st0).lastProbedRsp = st0.r11 := by
      rw [hInv.2.2.2.1, hRspDone]
    refine ⟨hRspDone, hLastDone, ?_, ?_⟩
    · dsimp only [evalCfa, finishR11ProbeTail]
      rw [hRspDone]
      dsimp only [st0, initR11ProbePrologue]
      rw [Nat.add_comm _ (savedCfaOff + numPages * 4096 + tailBytes), Nat.add_assoc (savedCfaOff + numPages * 4096) tailBytes,
          Nat.add_comm tailBytes, Nat.sub_add_cancel hTailLeR11, Nat.add_comm (savedCfaOff + numPages * 4096)]
      exact hCfa0
    · dsimp only [finishR11ProbeTail]
      rw [hLastDone, hRspDone]
      have hTailGap : st0.r11 - (st0.r11 - tailBytes) = tailBytes :=
        nat_sub_sub_self hTailLeR11
      rw [hTailGap]
      exact natMax_le hInv.2.2.1 (Nat.le_of_lt hTailBound)
  · intro e pc hMem hGe hLt
    rw [hBsearchAll pc]
    have ⟨i, _, hGet⟩ := mem_iff_listGet hMem
    exact lookupEhFrame_of_listGet hSorted hGet hGe hLt
  · intro pc r hB
    rw [hBsearchAll pc] at hB
    exact lookupEhFrame_some_inv hB
  · intro pc hMiss
    rw [hBsearchAll pc]
    exact lookupEhFrame_none_of_miss (fun i e hg => hMiss e (listGet_mem hg))
  · intro pc
    dsimp only [bsearchEhFrame]
    rw [bsearchEhLoop_eq_lookup hRelSorted (baseAddr + pc) (relocateEhTable baseAddr tbl).length 0
        (relocateEhTable baseAddr tbl).length (Nat.le_refl _) (by rw [Nat.sub_zero]; exact Nat.le_refl _)
        (fun _ _ hlt _ => False.elim (Nat.not_lt_zero _ hlt))
        (fun j _ hge hg => False.elim (Nat.not_lt_of_ge hge (listGet_lt_length hg)))]
    rw [lookupEhFrame_relocate]
    exact Eq.symm (hBsearchAll pc)

/-- **Theorem 4 (Universal Sharpness Across All 4 Relaxations & `0xCC` Padding):**
For EVERY `env`, `vaddr`, `fnSym`, `s`, and `padBytes` (`padBytes ≥ 1`), our
AST-free `validateLinkedBytes` accepts (`= true`) while `naiveDispOnlyValidator`
falsely rejects (`= false`) ALL FIVE real post-link patterns:
(1) `TLSGD -> Local-Exec`, (2) `TLSLD` (`48 8b 80` `mov`) `-> Local-Exec`,
(3) `GOTTPOFF -> Local-Exec`, (4) `REX_GOTPCRELX` (`mov -> lea`), and
(5) `ret` followed by `padBytes` `0xCC` alignment padding bytes! -/
theorem naive_disp_only_rejects_all_relaxations_and_int3_padding
    (env : LinkEnv) (vaddr fnSym s padBytes : Nat) (hPad : 1 ≤ padBytes) :
    (let obj := encodeFn fnSym [.tlsGdAddr s]
     let lnk := linkFn env vaddr true 0 [.tlsGdAddr s]
     validateLinkedBytes env vaddr obj.code obj.relocs lnk = true ∧
     naiveDispOnlyValidator obj.code lnk obj.relocs = false) ∧
    (let obj := encodeFn fnSym [.tlsLdLoad s]
     let lnk := linkFn env vaddr true 0 [.tlsLdLoad s]
     validateLinkedBytes env vaddr obj.code obj.relocs lnk = true ∧
     naiveDispOnlyValidator obj.code lnk obj.relocs = false) ∧
    (let obj := encodeFn fnSym [.tlsGotTpOff s]
     let lnk := linkFn env vaddr true 0 [.tlsGotTpOff s]
     validateLinkedBytes env vaddr obj.code obj.relocs lnk = true ∧
     naiveDispOnlyValidator obj.code lnk obj.relocs = false) ∧
    (let obj := encodeFn fnSym [.loadGotRelaxable s]
     let lnk := linkFn env vaddr true 0 [.loadGotRelaxable s]
     validateLinkedBytes env vaddr obj.code obj.relocs lnk = true ∧
     naiveDispOnlyValidator obj.code lnk obj.relocs = false) ∧
    (let obj := encodeFn fnSym [.ret]
     let lnk := linkFn env vaddr true padBytes [.ret]
     validateLinkedBytes env vaddr obj.code obj.relocs lnk = true ∧
     naiveDispOnlyValidator obj.code lnk obj.relocs = false) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (postlink_validator_sound_complete_and_tamper_rejecting env vaddr 0 fnSym true [.tlsGdAddr s]
      { rax := BitVec.ofNat 64 0, rcx := BitVec.ofNat 64 0, rdx := BitVec.ofNat 64 0,
        rdi := BitVec.ofNat 64 0, rsi := BitVec.ofNat 64 0, rsp := BitVec.ofNat 64 0,
        rbp := BitVec.ofNat 64 0, r11 := BitVec.ofNat 64 0, mem := fun _ => BitVec.ofNat 64 0 } []).1
      (.cons rfl .nil)
  · dsimp only [encodeFn, encodeOpsLoop, encodeOneOp, linkFn, linkOpsLoop, linkOneOpBytes,
                mkInt3Pad, naiveDispOnlyValidator, naiveDispOnlyCheckLoop, byteIndexInRelocHole,
                List.append_nil, List.nil_append]
    rfl
  · exact (postlink_validator_sound_complete_and_tamper_rejecting env vaddr 0 fnSym true [.tlsLdLoad s]
      { rax := BitVec.ofNat 64 0, rcx := BitVec.ofNat 64 0, rdx := BitVec.ofNat 64 0,
        rdi := BitVec.ofNat 64 0, rsi := BitVec.ofNat 64 0, rsp := BitVec.ofNat 64 0,
        rbp := BitVec.ofNat 64 0, r11 := BitVec.ofNat 64 0, mem := fun _ => BitVec.ofNat 64 0 } []).1
      (.cons rfl .nil)
  · dsimp only [encodeFn, encodeOpsLoop, encodeOneOp, linkFn, linkOpsLoop, linkOneOpBytes,
                mkInt3Pad, naiveDispOnlyValidator, naiveDispOnlyCheckLoop, byteIndexInRelocHole,
                List.append_nil, List.nil_append]
    rfl
  · exact (postlink_validator_sound_complete_and_tamper_rejecting env vaddr 0 fnSym true [.tlsGotTpOff s]
      { rax := BitVec.ofNat 64 0, rcx := BitVec.ofNat 64 0, rdx := BitVec.ofNat 64 0,
        rdi := BitVec.ofNat 64 0, rsi := BitVec.ofNat 64 0, rsp := BitVec.ofNat 64 0,
        rbp := BitVec.ofNat 64 0, r11 := BitVec.ofNat 64 0, mem := fun _ => BitVec.ofNat 64 0 } []).1
      (.cons trivial .nil)
  · dsimp only [encodeFn, encodeOpsLoop, encodeOneOp, linkFn, linkOpsLoop, linkOneOpBytes,
                mkInt3Pad, naiveDispOnlyValidator, naiveDispOnlyCheckLoop, byteIndexInRelocHole,
                List.append_nil, List.nil_append]
    rfl
  · exact (postlink_validator_sound_complete_and_tamper_rejecting env vaddr 0 fnSym true [.loadGotRelaxable s]
      { rax := BitVec.ofNat 64 0, rcx := BitVec.ofNat 64 0, rdx := BitVec.ofNat 64 0,
        rdi := BitVec.ofNat 64 0, rsi := BitVec.ofNat 64 0, rsp := BitVec.ofNat 64 0,
        rbp := BitVec.ofNat 64 0, r11 := BitVec.ofNat 64 0, mem := fun _ => BitVec.ofNat 64 0 } []).1
      (.cons trivial .nil)
  · dsimp only [encodeFn, encodeOpsLoop, encodeOneOp, linkFn, linkOpsLoop, linkOneOpBytes,
                mkInt3Pad, naiveDispOnlyValidator, naiveDispOnlyCheckLoop, byteIndexInRelocHole,
                List.append_nil, List.nil_append]
    rfl
  · exact (postlink_validator_sound_complete_and_tamper_rejecting env vaddr padBytes fnSym true [.ret]
      { rax := BitVec.ofNat 64 0, rcx := BitVec.ofNat 64 0, rdx := BitVec.ofNat 64 0,
        rdi := BitVec.ofNat 64 0, rsi := BitVec.ofNat 64 0, rsp := BitVec.ofNat 64 0,
        rbp := BitVec.ofNat 64 0, r11 := BitVec.ofNat 64 0, mem := fun _ => BitVec.ofNat 64 0 } []).1
      (.cons trivial .nil)
  · cases padBytes with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hPad)
    | succ p =>
      dsimp only [encodeFn, encodeOpsLoop, encodeOneOp, linkFn, linkOpsLoop, linkOneOpBytes,
                  mkInt3Pad, naiveDispOnlyValidator, naiveDispOnlyCheckLoop, byteIndexInRelocHole,
                  List.append_nil, List.nil_append]
      rfl

/-! ## Part VIII: Concrete Live `E3-1` & `Crucible 3` Witnesses (0 `sorry`) -/

/-- Sample `LinkEnv` matching live `E3-1` `GNU ld 2.47` PIE addresses:
real `.got` `[0x51948, 0x52240)` (`gotSlotAddr = 0x519b0`, `gotTpOffSlotAddr = 0x519c8`),
`MY_TLS` `tpoff = 0xffffffa8` (`-0x58`), and backward `leaf_callee = 0x14860`. -/
noncomputable def e31SampleEnv : LinkEnv := {
  baseAddr := 0x14700
  symAddr := fun s => if Nat.beq s 2 then 0x14860 else 0x53270
  gotSlotAddr := fun _ => 0x519b0
  gotTpOffSlotAddr := fun _ => 0x519c8
  tlsGetAddrAddr := 0x14100
  tlsTpOff := fun _ => BitVec.ofNat 32 0xffffffa8
  tlsDtpOff := fun _ => BitVec.ofNat 32 0x00000010
  threadPtrBase := BitVec.ofNat 64 0x7ffff7fc0000
}

noncomputable def e31SampleState : MachState := {
  rax := BitVec.ofNat 64 0x1122334455667788
  rcx := BitVec.ofNat 64 0xAABBCCDDEEFF0011
  rdx := BitVec.ofNat 64 0
  rdi := BitVec.ofNat 64 0
  rsi := BitVec.ofNat 64 0
  rsp := BitVec.ofNat 64 0x100000
  rbp := BitVec.ofNat 64 0x100040
  r11 := BitVec.ofNat 64 0
  mem := fun a =>
    if a == BitVec.ofNat 64 0x519b0 then BitVec.ofNat 64 0x53270
    else if a == BitVec.ofNat 64 0x519c8 then sext32To64 (BitVec.ofNat 32 0xffffffa8)
    else if a == (BitVec.ofNat 64 0x7ffff7fc0000 + sext32To64 (BitVec.ofNat 32 0xffffffa8)) then
      BitVec.ofNat 64 0xCAFEBABE12345678
    else BitVec.ofNat 64 0
}

/-- Witness `W1`: Live `E3-1` `TLSGD -> Local-Exec` (`9B + 7B` = `16B`) passes
AST-free `validateLinkedBytes`, fails `naiveDispOnlyValidator`, and executes
across the shifted `+9` boundary to `0x7ffff7fbffa8`! -/
theorem witness_e31_tlsgd_shifted_boundary_and_naive_rejection :
    let obj := encodeFn 1 [.tlsGdAddr 1]
    let lnk := linkFn e31SampleEnv 0x14701 true 0 [.tlsGdAddr 1]
    lnk = [BitVec.ofNat 8 0x64, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04,
           BitVec.ofNat 8 0x25, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00,
           BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x80,
           BitVec.ofNat 8 0xA8, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0xFF] ∧
    validateLinkedBytes e31SampleEnv 0x14701 obj.code obj.relocs lnk = true ∧
    naiveDispOnlyValidator obj.code lnk obj.relocs = false ∧
    (execByteStream e31SampleEnv 0x14701 lnk e31SampleState).map MachState.rax =
      some (BitVec.ofNat 64 0x7ffff7fbffa8) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Witness `W2`: Live `E3-1` `TLSLD` + `DTPOFF32` `mov` (`48 8b 80 a8 ff ff ff`,
`12B + 7B` = `19B`) and `GOTTPOFF` (`48 c7 c0 a8 ff ff ff`) match `E3-1`
disassembly verbatim, pass `validateLinkedBytes`, fail `naiveDispOnlyValidator`,
and load `0xCAFEBABE12345678` from `%fs:-0x58`! -/
theorem witness_e31_tlsld_mov_and_gottpoff_exact_bytes :
    let objLd := encodeFn 1 [.tlsLdLoad 1]
    let lnkLd := linkFn e31SampleEnv 0x14700 true 0 [.tlsLdLoad 1]
    let objGot := encodeFn 1 [.tlsGotTpOff 1]
    let lnkGot := linkFn e31SampleEnv 0x14700 true 0 [.tlsGotTpOff 1]
    lnkLd = [BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x66, BitVec.ofNat 8 0x64,
             BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x04, BitVec.ofNat 8 0x25,
             BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00, BitVec.ofNat 8 0x00,
             BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8B, BitVec.ofNat 8 0x80,
             BitVec.ofNat 8 0xA8, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0xFF] ∧
    validateLinkedBytes e31SampleEnv 0x14700 objLd.code objLd.relocs lnkLd = true ∧
    naiveDispOnlyValidator objLd.code lnkLd objLd.relocs = false ∧
    (execByteStream e31SampleEnv 0x14700 lnkLd e31SampleState).map MachState.rax =
      some (BitVec.ofNat 64 0xCAFEBABE12345678) ∧
    lnkGot = [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0xC7, BitVec.ofNat 8 0xC0,
              BitVec.ofNat 8 0xA8, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0xFF] ∧
    validateLinkedBytes e31SampleEnv 0x14700 objGot.code objGot.relocs lnkGot = true ∧
    naiveDispOnlyValidator objGot.code lnkGot objGot.relocs = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Witness `W3`: Live `E3-1` backward PC-relative `lea -0xd9(%rip)` (`27 ff ff ff`
at `vaddr = 0x14932`, `target = 0x14860`), `REX_GOTPCRELX` relaxation vs.
non-relaxable `R_X86_64_GOTPCREL` tamper rejection, and active `WriteMode`
(`zeroExt32` + `lo16PreserveUpper48`) multi-op function with `0xCC` padding! -/
theorem witness_e31_neg_pcrel_tamper_rejection_and_writemode :
    let objNeg := encodeFn 2 [.leaRipSym 2]
    let lnkNeg := linkFn e31SampleEnv 0x14932 true 0 [.leaRipSym 2]
    let objStrict := encodeFn 3 [.loadGotStrict 1]
    let tampered := linkOneOpBytes e31SampleEnv 0x14700 true (.loadGotRelaxable 1)
    let opsWm : List MiniMachOp :=
      [.movImm32 .rax false (BitVec.ofNat 32 0x12345678),
       .movImm16 .rax (BitVec.ofNat 16 0xABCD),
       .ret]
    let objWm := encodeFn 4 opsWm
    let lnkWm := linkFn e31SampleEnv 0x14700 true 3 opsWm
    lnkNeg = [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8D, BitVec.ofNat 8 0x05,
              BitVec.ofNat 8 0x27, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0xFF, BitVec.ofNat 8 0xFF] ∧
    validateLinkedBytes e31SampleEnv 0x14932 objNeg.code objNeg.relocs lnkNeg = true ∧
    (execByteStream e31SampleEnv 0x14932 lnkNeg e31SampleState).map MachState.rax =
      some (BitVec.ofNat 64 0x14860) ∧
    validateLinkedBytes e31SampleEnv 0x14700 objStrict.code objStrict.relocs tampered = false ∧
    validateLinkedBytes e31SampleEnv 0x14700 objWm.code objWm.relocs lnkWm = true ∧
    (execByteStream e31SampleEnv 0x14700 lnkWm e31SampleState).map MachState.rax =
      some (BitVec.ofNat 64 0x000000001234ABCD) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Witness `W4`: Exact `Crucible 3` Table E1 (`frame_loop_probe_36864`,
`savedCfaOff = 16`, `numPages = 9`, `tailBytes = 32` / `0x20`):
loop CFA `r11 + 36880` (`= 0x100008`), final CFA `rsp + 36912` (`= 0x100008`),
`maxUnprobedGap = 4096`, plus relocated `.eh_frame_hdr` binary search hit and
`0xCC`-gap miss! -/
theorem witness_crucible3_exact_r11_probe_and_bsearch :
    let st0 := initR11ProbePrologue 0x100000 16 9
    let st9 := runFixedStrideR11Loop 9 st0
    let stDone := finishR11ProbeTail 16 9 32 st9
    let tbl : List EhFrameEntry :=
      [{ startPc := 0x0, endPc := 0x10, cfaRule := { base := .rsp, offset := 16 } },
       { startPc := 0x10, endPc := 0x1F, cfaRule := { base := .r11, offset := 36880 } },
       { startPc := 0x24, endPc := 0x74, cfaRule := { base := .rsp, offset := 36912 } }]
    let relTbl := relocateEhTable 0x14700 tbl
    st0.cfaRule = { base := .r11, offset := 36880 } ∧
    evalCfa st9 = 0x100008 ∧ st9.rsp = st0.r11 ∧ st9.maxUnprobedGap = 4096 ∧
    stDone.cfaRule = { base := .rsp, offset := 36912 } ∧
    evalCfa stDone = 0x100008 ∧ stDone.maxUnprobedGap = 4096 ∧
    bsearchEhFrame 0x14712 relTbl = some { base := .r11, offset := 36880 } ∧
    bsearchEhFrame 0x14720 relTbl = none := by
  exact ⟨rfl, rfl, rfl, by decide, rfl, rfl, by decide, rfl, rfl⟩

end VrustcFormal.F1_4
