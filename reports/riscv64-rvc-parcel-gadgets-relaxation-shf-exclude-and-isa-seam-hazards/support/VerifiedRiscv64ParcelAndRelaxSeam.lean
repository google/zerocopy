/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

/-!
# Verified RISC-V Mixed `16/32`-Bit (`RVC`) Parcel SFI and Byte-Shrinking Relaxation Seam

Standalone `Init.*`-only Lean `v4.34.1` mechanization accompanying the
`riscv64-rvc-parcel-gadgets-relaxation-shf-exclude-and-isa-seam-hazards`
reference report.
-/

namespace VerifiedRiscv64ParcelAndRelaxSeam

/-! ## Part I: Mixed `16/32`-Bit `RVC` (`IALIGN = 16`) Parcel Decoding -/

/-- Decoded `RV64GC` (`Zca` + `RV64I`) instruction subset covering compressed
    and 32-bit ALU, memory, branch, jump, and privileged/trap encodings. -/
inductive RvInsn where
  | addi   (rd rs1 : Nat) (immSigned : Int)
  | andi   (rd rs1 : Nat) (immRaw12 : Nat)
  | add    (rd rs1 rs2 : Nat)
  | lui    (rd : Nat) (imm20 : Nat)
  | ld     (rd rs1 : Nat) (immRaw12 : Nat)
  | sd     (rs2 rs1 : Nat) (immRaw12 : Nat)
  | rvcLd  (rd rs1 : Nat) (uimm : Nat)
  | rvcSd  (rs2 rs1 : Nat) (uimm : Nat)
  | branch (isNe : Bool) (rs1 rs2 : Nat) (offSigned : Int)
  | jal    (rd : Nat) (offSigned : Int)
  | jalr   (rd rs1 : Nat) (immSigned : Int)
  | ebreak
  | system (raw : Nat)
  | illegal
  deriving DecidableEq, Repr

/-- Hardware parcel fetch outcome at byte offset `pc` (`IALIGN = 16`). -/
inductive DecodeOutcome where
  | misalignedFetch
  | pcOutOfBounds
  | truncated32AtEnd
  | parcel (byteLen : Nat) (insn : RvInsn)
  deriving DecidableEq, Repr

/-- Convert a little-endian byte list into 16-bit halfword parcels.
    Rejects odd-length byte lists (such as inline `.byte 0x01`). -/
def bytesToHalfwords : List Nat → Option (List Nat)
  | [] => some []
  | b0 :: b1 :: rest =>
      match bytesToHalfwords rest with
      | some hws => some (((b0 % 256) + (b1 % 256) * 256) :: hws)
      | none => none
  | [_] => none

/-- Two's-complement sign extension of a `b`-bit unsigned field (`b > 0`). -/
def sextBits (u : Nat) (b : Nat) : Int :=
  let m := 2 ^ b
  let half := 2 ^ (b - 1)
  let v := u % m
  if v >= half then (v : Int) - (m : Int) else (v : Int)

/-- True iff the 16-bit halfword carries the 32-bit instruction prefix `bits[1:0] == 0b11`. -/
def is32BitPrefix (hw : Nat) : Bool :=
  (hw % 4) == 3

/-- Bit-accurate decoder for 16-bit `RVC` (`Zca`) halfwords (`hw % 4 != 3`). -/
def decodeRvc16 (hw : Nat) : RvInsn :=
  let h := hw % 65536
  let op := h % 4
  let funct3 := (h / 8192) % 8
  if h == 0 then
    .illegal
  else if op == 0 then
    let rs1p := 8 + ((h / 128) % 8)
    let rdp  := 8 + ((h / 4) % 8)
    let uimm5_3 := (h / 1024) % 8
    let uimm7_6 := (h / 32) % 4
    let uimm := uimm5_3 * 8 + uimm7_6 * 64
    if funct3 == 3 then .rvcLd rdp rs1p uimm
    else if funct3 == 7 then .rvcSd rdp rs1p uimm
    else .illegal
  else if op == 1 then
    if funct3 == 0 then
      let rd := (h / 128) % 32
      let imm5 := (h / 4096) % 2
      let imm4_0 := (h / 4) % 32
      let imm6 := imm5 * 32 + imm4_0
      .addi rd rd (sextBits imm6 6)
    else if funct3 == 5 then
      let raw11 := (h / 4) % 2048
      .jal 0 (sextBits (raw11 * 2) 12)
    else if funct3 == 6 || funct3 == 7 then
      let rs1p := 8 + ((h / 128) % 8)
      let raw8 := ((h / 4) % 32) + ((h / 1024) % 8) * 32
      .branch (funct3 == 7) rs1p 0 (sextBits (raw8 * 2) 9)
    else
      .illegal
  else if op == 2 then
    if funct3 == 4 then
      let bit12 := (h / 4096) % 2
      let rd_rs1 := (h / 128) % 32
      let rs2 := (h / 4) % 32
      if bit12 == 0 then
        if rs2 == 0 then
          if rd_rs1 == 0 then .illegal
          else .jalr 0 rd_rs1 0
        else
          .add rd_rs1 0 rs2
      else
        if rs2 == 0 then
          if rd_rs1 == 0 then .ebreak
          else .jalr 1 rd_rs1 0
        else
          .add rd_rs1 rd_rs1 rs2
    else
      .illegal
  else
    .illegal

/-- Bit-accurate decoder for 32-bit `RV64I` words (`w % 4 == 3`). -/
def decodeRv32Word (w : Nat) : RvInsn :=
  let u := w % 4294967296
  let opcode := u % 128
  let rd     := (u / 128) % 32
  let funct3 := (u / 4096) % 8
  let rs1    := (u / 32768) % 32
  let rs2    := (u / 1048576) % 32
  let funct7 := (u / 33554432) % 128
  let imm12  := (u / 1048576) % 4096
  if opcode == 0x37 then
    .lui rd (u / 4096)
  else if opcode == 0x13 then
    if funct3 == 0 then .addi rd rs1 (sextBits imm12 12)
    else if funct3 == 7 then .andi rd rs1 imm12
    else .illegal
  else if opcode == 0x33 then
    if funct3 == 0 && funct7 == 0 then .add rd rs1 rs2
    else .illegal
  else if opcode == 0x03 then
    if funct3 == 3 then .ld rd rs1 imm12 else .illegal
  else if opcode == 0x23 then
    let simm12 := funct7 * 32 + rd
    if funct3 == 3 then .sd rs2 rs1 simm12 else .illegal
  else if opcode == 0x63 then
    let b12   := (u / 2147483648) % 2
    let b10_5 := (u / 33554432) % 64
    let b4_1  := (u / 256) % 16
    let b11   := (u / 128) % 2
    let imm13 := b12 * 4096 + b11 * 2048 + b10_5 * 32 + b4_1 * 2
    if funct3 == 0 || funct3 == 1 then
      .branch (funct3 == 1) rs1 rs2 (sextBits imm13 13)
    else .illegal
  else if opcode == 0x6f then
    let j20    := (u / 2147483648) % 2
    let j10_1  := (u / 2097152) % 1024
    let j11    := (u / 1048576) % 2
    let j19_12 := (u / 4096) % 256
    let imm21  := j20 * 1048576 + j19_12 * 4096 + j11 * 2048 + j10_1 * 2
    .jal rd (sextBits imm21 21)
  else if opcode == 0x67 then
    if funct3 == 0 then .jalr rd rs1 (sextBits imm12 12) else .illegal
  else if opcode == 0x73 then
    .system u
  else
    .illegal

/-- Fetch and decode one `16`- or `32`-bit RISC-V parcel at byte offset `pc`. -/
def decodeRvParcel (halfwords : List Nat) (pc : Nat) : DecodeOutcome :=
  if pc % 2 != 0 then
    .misalignedFetch
  else
    match halfwords[pc / 2]? with
    | none => .pcOutOfBounds
    | some lo =>
        if is32BitPrefix lo then
          match halfwords[pc / 2 + 1]? with
          | none => .truncated32AtEnd
          | some hi =>
              .parcel 4 (decodeRv32Word ((lo % 65536) + (hi % 65536) * 65536))
        else
          .parcel 2 (decodeRvc16 lo)

/-- Complete sequential slice decoder for an attested `[start_pc, end_pc)` halfword slice. -/
def decodeCompleteParcelSlice : List Nat → Option (List RvInsn)
  | [] => some []
  | [lo] =>
      if is32BitPrefix lo then none
      else some [decodeRvc16 lo]
  | lo :: hi :: rest =>
      if is32BitPrefix lo then
        let w32 := (lo % 65536) + (hi % 65536) * 65536
        match decodeCompleteParcelSlice rest with
        | some tail => some (decodeRv32Word w32 :: tail)
        | none => none
      else
        match decodeCompleteParcelSlice (hi :: rest) with
        | some tail => some (decodeRvc16 lo :: tail)
        | none => none

/-! ## Operational Machine Semantics Over Mixed `16/32`-Bit Parcels -/

def modulus64 : Nat := 18446744073709551616

structure RvState where
  pc   : Nat
  regs : Nat → Nat
  mem  : Nat → Nat

inductive TrapKind where
  | misalignedFetch
  | pcOutOfBounds
  | truncated32
  | misalignedMem
  | illegalInsn
  | privilegedInsn
  | ebreakTrap
  deriving DecidableEq, Repr

inductive StepOut where
  | running  (next : RvState)
  | returned (targetPc : Nat) (final : RvState)
  | trapped  (kind : TrapKind)

def rdReg (s : RvState) (r : Nat) : Nat :=
  if r == 0 then 0 else s.regs r

def wrReg (s : RvState) (r : Nat) (v : Nat) : RvState :=
  if r == 0 then s
  else { s with regs := fun k => if k == r then v % modulus64 else s.regs k }

def addSigned64 (base : Nat) (delta : Int) : Nat :=
  ((((base % modulus64 : Nat) : Int) + delta) % (modulus64 : Int)).toNat

def readMem64 (m : Nat → Nat) (addr : Nat) : Nat :=
  (m addr % 256)
  + (m (addr + 1) % 256) * 256
  + (m (addr + 2) % 256) * 65536
  + (m (addr + 3) % 256) * 16777216
  + (m (addr + 4) % 256) * 4294967296
  + (m (addr + 5) % 256) * 1099511627776
  + (m (addr + 6) % 256) * 281474976710656
  + (m (addr + 7) % 256) * 72057594037927936

def writeByte (m : Nat → Nat) (a b : Nat) : Nat → Nat :=
  fun x => if x == a then b % 256 else m x

def writeMem64 (m : Nat → Nat) (addr val : Nat) : Nat → Nat :=
  let m0 := writeByte m addr (val % 256)
  let m1 := writeByte m0 (addr + 1) ((val / 256) % 256)
  let m2 := writeByte m1 (addr + 2) ((val / 65536) % 256)
  let m3 := writeByte m2 (addr + 3) ((val / 16777216) % 256)
  let m4 := writeByte m3 (addr + 4) ((val / 4294967296) % 256)
  let m5 := writeByte m4 (addr + 5) ((val / 1099511627776) % 256)
  let m6 := writeByte m5 (addr + 6) ((val / 281474976710656) % 256)
  writeByte m6 (addr + 7) ((val / 72057594037927936) % 256)

def luiVal64 (imm20 : Nat) : Nat :=
  let raw32 := (imm20 % 1048576) * 4096
  addSigned64 0 (sextBits raw32 32)

/-- Execute one architectural step from `s.pc` over 16-bit `halfwords`. -/
def stepParcel (halfwords : List Nat) (s : RvState) : StepOut :=
  match decodeRvParcel halfwords s.pc with
  | .misalignedFetch => .trapped .misalignedFetch
  | .pcOutOfBounds   => .trapped .pcOutOfBounds
  | .truncated32AtEnd => .trapped .truncated32
  | .parcel len insn =>
      match insn with
      | .addi rd rs1 imm =>
          let v := addSigned64 (rdReg s rs1) imm
          .running { (wrReg s rd v) with pc := s.pc + len }
      | .andi rd rs1 imm12 =>
          let mask :=
            if imm12 % 4096 < 2048 then imm12 % 4096
            else (modulus64 - 4096) + (imm12 % 4096)
          let v := (rdReg s rs1) &&& mask
          .running { (wrReg s rd v) with pc := s.pc + len }
      | .add rd rs1 rs2 =>
          let v := ((rdReg s rs1) + (rdReg s rs2)) % modulus64
          .running { (wrReg s rd v) with pc := s.pc + len }
      | .lui rd imm20 =>
          .running { (wrReg s rd (luiVal64 imm20)) with pc := s.pc + len }
      | .ld rd rs1 imm12 =>
          let addr := addSigned64 (rdReg s rs1) (sextBits imm12 12)
          if addr % 8 != 0 then .trapped .misalignedMem
          else .running { (wrReg s rd (readMem64 s.mem addr)) with pc := s.pc + len }
      | .sd rs2 rs1 imm12 =>
          let addr := addSigned64 (rdReg s rs1) (sextBits imm12 12)
          if addr % 8 != 0 then .trapped .misalignedMem
          else .running { s with pc := s.pc + len, mem := writeMem64 s.mem addr (rdReg s rs2) }
      | .rvcLd rd rs1 uimm =>
          let addr := ((rdReg s rs1) + uimm) % modulus64
          if addr % 8 != 0 then .trapped .misalignedMem
          else .running { (wrReg s rd (readMem64 s.mem addr)) with pc := s.pc + len }
      | .rvcSd rs2 rs1 uimm =>
          let addr := ((rdReg s rs1) + uimm) % modulus64
          if addr % 8 != 0 then .trapped .misalignedMem
          else .running { s with pc := s.pc + len, mem := writeMem64 s.mem addr (rdReg s rs2) }
      | .branch isNe rs1 rs2 off =>
          let cond := if isNe then (rdReg s rs1 != rdReg s rs2) else (rdReg s rs1 == rdReg s rs2)
          let signedTgt := (s.pc : Int) + off
          let tgt := signedTgt.toNat
          if cond then
            if decide (signedTgt < 0) || (tgt % 2 != 0) then .trapped .misalignedFetch
            else .running { s with pc := tgt }
          else
            .running { s with pc := s.pc + len }
      | .jal rd off =>
          let signedTgt := (s.pc : Int) + off
          let tgt := signedTgt.toNat
          if decide (signedTgt < 0) || (tgt % 2 != 0) then .trapped .misalignedFetch
          else .running { (wrReg s rd (s.pc + len)) with pc := tgt }
      | .jalr rd rs1 imm =>
          let rawTgt := addSigned64 (rdReg s rs1) imm
          let tgt := rawTgt - (rawTgt % 2)
          let s' := wrReg s rd (s.pc + len)
          .returned tgt s'
      | .ebreak => .trapped .ebreakTrap
      | .system _ => .trapped .privilegedInsn
      | .illegal => .trapped .illegalInsn

/-- Run up to `fuel` parcel steps. -/
def runParcels (halfwords : List Nat) : Nat → RvState → StepOut
  | 0, s => .running s
  | k + 1, s =>
      match stepParcel halfwords s with
      | .running s' => runParcels halfwords k s'
      | other => other

/-! ### Theorem 1: Odd-Byte & Trailing `.half` (`bits[1:0] == 0b11`) Bleed Rejection -/

private theorem bytesToHalfwords_odd_len_none :
    ∀ (bs : List Nat), bs.length % 2 = 1 → bytesToHalfwords bs = none
  | [], h => by simp at h
  | [_], _ => rfl
  | _ :: _ :: rest, h => by
      have hrest : rest.length % 2 = 1 := by
        simp [List.length] at h
        omega
      simp [bytesToHalfwords, bytesToHalfwords_odd_len_none rest hrest]

private theorem decodeComplete_snoc_half11_len :
    ∀ (n : Nat) (xs : List Nat) (insns : List RvInsn) (hw : Nat),
      xs.length <= n →
      decodeCompleteParcelSlice xs = some insns →
      is32BitPrefix hw = true →
      decodeCompleteParcelSlice (xs ++ [hw]) = none := by
  intro n
  induction n with
  | zero =>
      intro xs insns hw hlen _ hhw
      cases xs with
      | nil => simp [decodeCompleteParcelSlice, hhw]
      | cons _ _ => simp at hlen
  | succ m ih =>
      intro xs insns hw hlen hxs hhw
      cases xs with
      | nil => simp [decodeCompleteParcelSlice, hhw]
      | cons a rest =>
          cases rest with
          | nil =>
              simp only [decodeCompleteParcelSlice] at hxs
              cases ha : is32BitPrefix a
              · simp [decodeCompleteParcelSlice, ha, hhw]
              · simp [ha] at hxs
          | cons b tail =>
              simp only [decodeCompleteParcelSlice] at hxs
              cases ha : is32BitPrefix a
              · simp only [ha, Bool.false_eq_true, ↓reduceIte] at hxs
                cases hsub : decodeCompleteParcelSlice (b :: tail) with
                | none => simp [hsub] at hxs
                | some subInsns =>
                    have hrec := ih (b :: tail) subInsns hw (by simp at hlen ⊢; omega) hsub hhw
                    change (if is32BitPrefix a = true then _ else _) = none
                    rw [ha]
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    change (match decodeCompleteParcelSlice ((b :: tail) ++ [hw]) with | some t => _ | none => none) = none
                    rw [hrec]
              · simp only [ha, ↓reduceIte] at hxs
                cases hsub : decodeCompleteParcelSlice tail with
                | none => simp [hsub] at hxs
                | some subInsns =>
                    have hrec := ih tail subInsns hw (by simp at hlen ⊢; omega) hsub hhw
                    change (if is32BitPrefix a = true then _ else _) = none
                    rw [ha]
                    simp only [↓reduceIte]
                    change (match decodeCompleteParcelSlice (tail ++ [hw]) with | some t => _ | none => none) = none
                    rw [hrec]

private theorem decodeComplete_snoc_half11 (xs : List Nat) (insns : List RvInsn) (hw : Nat)
    (hxs : decodeCompleteParcelSlice xs = some insns) (hhw : is32BitPrefix hw = true) :
    decodeCompleteParcelSlice (xs ++ [hw]) = none :=
  decodeComplete_snoc_half11_len xs.length xs insns hw (Nat.le_refl _) hxs hhw

/-- Live CGU witness from `caller_corrupted_by_half11`:
    `0x0505` (`c.addi a0, 1`), rogue `.2byte 0x0537` (`bits[1:0] == 0b11`, `lui a0, ...`),
    followed by pure-Rust epilogue `0x8082` (`ret` = `c.jr ra`). -/
def corruptedHalf11Prog : List Nat := [0x0505, 0x0537, 0x8082]

def checkHalf11SwallowWitness : Bool :=
  let s0 : RvState :=
    { pc := 0
    , regs := fun r => if r == 10 then 41 else if r == 1 then 0x10000 else 0
    , mem := fun _ => 0 }
  match runParcels corruptedHalf11Prog 2 s0 with
  | .running s2 =>
      (s2.pc == 6) &&
      (rdReg s2 10 == luiVal64 0x80820) &&
      (match stepParcel corruptedHalf11Prog s2 with
       | .trapped .pcOutOfBounds => true
       | _ => false)
  | _ => false

theorem odd_byte_and_trailing_half11_bleed_rejected :
    bytesToHalfwords [0x05, 0x15, 0x01] = none ∧
    (∀ bs, bs.length % 2 = 1 → bytesToHalfwords bs = none) ∧
    (∀ xs insns hw,
      decodeCompleteParcelSlice xs = some insns →
      is32BitPrefix hw = true →
      decodeCompleteParcelSlice (xs ++ [hw]) = none) ∧
    decodeCompleteParcelSlice [0x0505, 0x0537] = none ∧
    checkHalf11SwallowWitness = true :=
  ⟨rfl, bytesToHalfwords_odd_len_none, decodeComplete_snoc_half11, rfl, rfl⟩

/-! ## Part II: `pc + 2` Mid-Instruction `RVC` Gadgets vs. Parcel-Bitmap SFI -/

structure SfiCfg where
  ctxBytes : Nat
  scrBytes : Nat
  idxMask  : Nat
  deriving DecidableEq, Repr

def isTempReg (r : Nat) : Bool :=
  r == 5 || (12 <= r && r <= 17) || (28 <= r && r <= 31)

def canReadReg (r : Nat) : Bool :=
  r == 0 || r == 6 || isTempReg r

def addrOk8 (cfg : SfiCfg) (rs1 off : Nat) : Bool :=
  off < 2048 && off % 8 == 0 &&
  ((rs1 == 10 && off + 8 <= cfg.ctxBytes) ||
   (rs1 == 7 && cfg.idxMask + off + 8 <= cfg.scrBytes))

/-- Naive 4-byte-word-only SFI checker (`IALIGN = 32` assumption) checking 32-bit words
    without a 2-byte parcel-start bitmap. -/
def okWordOnlyInsn (cfg : SfiCfg) (numWords idx : Nat) (insn : RvInsn) : Bool :=
  match insn with
  | .lui rd _ => (idx + 1 < numWords) && isTempReg rd
  | .addi rd rs1 _ => (idx + 1 < numWords) && isTempReg rd && canReadReg rs1
  | .andi rd rs1 imm12 =>
      (idx + 1 < numWords) && canReadReg rs1 &&
      (isTempReg rd || (rd == 6 && imm12 < 2048 && imm12 <= cfg.idxMask && imm12 % 8 == 0))
  | .add rd rs1 rs2 =>
      (idx + 1 < numWords) &&
      ((isTempReg rd && canReadReg rs1 && canReadReg rs2) || (rd == 7 && rs1 == 11 && rs2 == 6))
  | .ld rd rs1 imm12 => (idx + 1 < numWords) && isTempReg rd && addrOk8 cfg rs1 imm12
  | .sd rs2 rs1 imm12 => (idx + 1 < numWords) && canReadReg rs2 && addrOk8 cfg rs1 imm12
  | .jalr rd rs1 imm => rd == 0 && rs1 == 1 && imm == 0
  | _ => false

def checkWordsOnlyAux (cfg : SfiCfg) (numWords idx : Nat) : List Nat → Bool
  | [] => true
  | w :: rest =>
      (w % 4 == 3) &&
      okWordOnlyInsn cfg numWords idx (decodeRv32Word w) &&
      checkWordsOnlyAux cfg numWords (idx + 1) rest

def checkWordsOnlySfi (cfg : SfiCfg) (words32 : List Nat) : Bool :=
  !words32.isEmpty && (cfg.idxMask + 8 <= cfg.scrBytes) &&
  checkWordsOnlyAux cfg words32.length 0 words32

/-- Expand 32-bit words into little-endian 16-bit halfword parcels in `.text`. -/
def words32ToHalfwords : List Nat → List Nat
  | [] => []
  | w :: rest => (w % 65536) :: ((w / 65536) % 65536) :: words32ToHalfwords rest

def demoSfiCfg : SfiCfg := { ctxBytes := 64, scrBytes := 4096, idxMask := 2040 }

/-- Benign 4-byte-word module #1: `lui t0, 0xe10c0; jalr x0, 0(ra)`.
    At `pc = 2`, upper halfword `0xe10c` decodes as `c.sd a1, 0(a0)`. -/
def benignStoreGadgetWords : List Nat := [0xe10c02b7, 0x00008067]

/-- Benign 4-byte-word module #2: `lui t0, 0x86020; addi t0, zero, 1; jalr x0, 0(ra)`.
    At `pc = 2`, upper halfword `0x8602` decodes as `c.jr a2`. -/
def benignJrGadgetWords : List Nat := [0x860202b7, 0x00100293, 0x00008067]

def checkMidInsnStoreGadget : Bool :=
  let hws := words32ToHalfwords benignStoreGadgetWords
  let initRegs := fun r =>
    if r == 1 then 0x8000
    else if r == 10 then 0x9000
    else if r == 11 then 0xdeadbeef
    else 0
  let initMem := fun a => if a == 0x9000 then 0x11 else 0
  let okAt0 :=
    match runParcels hws 2 { pc := 0, regs := initRegs, mem := initMem } with
    | .returned tgt s => (tgt == 0x8000) && (s.mem 0x9000 == 0x11)
    | _ => false
  let hijackedAt2 :=
    match runParcels hws 2 { pc := 2, regs := initRegs, mem := initMem } with
    | .returned tgt s => (tgt == 0x8000) && (s.mem 0x9000 == 0xef)
    | _ => false
  okAt0 && hijackedAt2

def checkMidInsnJrGadget : Bool :=
  let hwsJr := words32ToHalfwords benignJrGadgetWords
  let regsJr := fun r => if r == 1 then 0x8000 else if r == 12 then 0x77770000 else 0
  match runParcels hwsJr 1 { pc := 2, regs := regsJr, mem := fun _ => 0 } with
  | .returned tgt _ => tgt == 0x77770000
  | _ => false

/-! ### Theorem 2: Unsoundness of 4-Byte-Word Checkers Under `RVC` (`IALIGN = 16`) -/

theorem rvc_mid_insn_gadget_unsound :
    checkWordsOnlySfi demoSfiCfg benignStoreGadgetWords = true ∧
    checkWordsOnlySfi demoSfiCfg benignJrGadgetWords = true ∧
    decodeRvParcel (words32ToHalfwords benignStoreGadgetWords) 2 = .parcel 2 (.rvcSd 11 10 0) ∧
    decodeRvParcel (words32ToHalfwords benignJrGadgetWords) 2 = .parcel 2 (.jalr 0 12 0) ∧
    checkMidInsnStoreGadget = true ∧
    checkMidInsnJrGadget = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### Parcel-Start Bitmap Construction & Soundness (`checkRvParcelBitmapSfi_sound`) -/

/-- Forward sequential parcel-start bitmap builder:
    - 16-bit `RVC` parcel (`hw % 4 != 3`): emits `[true]`.
    - 32-bit `RV64I` parcel (`hw % 4 == 3`): emits `[true, false]`, marking the
      interior `pc + 2` halfword `false`. -/
def buildParcelBitmap : List Nat → Option (List Bool)
  | [] => some []
  | [lo] =>
      if is32BitPrefix lo then none
      else some [true]
  | lo :: hi :: rest =>
      if is32BitPrefix lo then
        match buildParcelBitmap rest with
        | some bRest => some (true :: false :: bRest)
        | none => none
      else
        match buildParcelBitmap (hi :: rest) with
        | some bRest => some (true :: bRest)
        | none => none

def bitmapAllows (bmap : List Bool) (pc : Nat) : Bool :=
  (pc % 2 == 0) && (bmap[pc / 2]? == some true)

/-- Per-parcel SFI admission rule over mixed `16/32`-bit parcels using `bmap`. -/
def okParcelInsn (cfg : SfiCfg) (bmap : List Bool) (pc byteLen : Nat) (insn : RvInsn) : Bool :=
  let nextPc := pc + byteLen
  match insn with
  | .lui rd _ => bitmapAllows bmap nextPc && isTempReg rd
  | .addi rd rs1 _ => bitmapAllows bmap nextPc && isTempReg rd && canReadReg rs1
  | .andi rd rs1 imm12 =>
      bitmapAllows bmap nextPc && canReadReg rs1 &&
      (isTempReg rd || (rd == 6 && imm12 < 2048 && imm12 <= cfg.idxMask && imm12 % 8 == 0))
  | .add rd rs1 rs2 =>
      bitmapAllows bmap nextPc &&
      ((isTempReg rd && canReadReg rs1 && canReadReg rs2) || (rd == 7 && rs1 == 11 && rs2 == 6))
  | .ld rd rs1 imm12 => bitmapAllows bmap nextPc && isTempReg rd && addrOk8 cfg rs1 imm12
  | .sd rs2 rs1 imm12 => bitmapAllows bmap nextPc && canReadReg rs2 && addrOk8 cfg rs1 imm12
  | .rvcLd rd rs1 uimm => bitmapAllows bmap nextPc && isTempReg rd && addrOk8 cfg rs1 uimm
  | .rvcSd rs2 rs1 uimm => bitmapAllows bmap nextPc && canReadReg rs2 && addrOk8 cfg rs1 uimm
  | .branch _ rs1 rs2 off =>
      canReadReg rs1 && canReadReg rs2 &&
      decide (0 < off) &&
      (let tgt := pc + off.toNat
       bitmapAllows bmap nextPc && bitmapAllows bmap tgt)
  | .jal rd off =>
      rd == 0 && decide (0 < off) &&
      bitmapAllows bmap (pc + off.toNat)
  | .jalr rd rs1 imm =>
      rd == 0 && rs1 == 1 && imm == 0
  | .ebreak | .system _ | .illegal => false

def checkParcelPositions (cfg : SfiCfg) (halfwords : List Nat) (bmap : List Bool) : Nat → Bool
  | 0 => true
  | rem + 1 =>
      let idx := bmap.length - (rem + 1)
      let okHere :=
        if bmap[idx]? == some true then
          match decodeRvParcel halfwords (2 * idx) with
          | .parcel len insn => okParcelInsn cfg bmap (2 * idx) len insn
          | _ => false
        else
          true
      okHere && checkParcelPositions cfg halfwords bmap rem

/-- Top-level mixed `16/32`-bit `RVC` parcel-bitmap SFI checker. -/
def checkRvParcelBitmapSfi (cfg : SfiCfg) (halfwords : List Nat) : Bool :=
  match buildParcelBitmap halfwords with
  | none => false
  | some bmap =>
      !halfwords.isEmpty &&
      (cfg.idxMask + 8 <= cfg.scrBytes) &&
      bitmapAllows bmap 0 &&
      checkParcelPositions cfg halfwords bmap bmap.length

def inSandbox (cfg : SfiCfg) (s0 : RvState) (addr : Nat) : Prop :=
  (s0.regs 10 <= addr ∧ addr < s0.regs 10 + cfg.ctxBytes) ∨
  (s0.regs 11 <= addr ∧ addr < s0.regs 11 + cfg.scrBytes)

structure ParcelEntry (cfg : SfiCfg) (s0 : RvState) : Prop where
  pcZero   : s0.pc = 0
  raEven   : s0.regs 1 % 2 = 0
  raBound  : s0.regs 1 < modulus64
  ctxAlign : s0.regs 10 % 8 = 0
  ctxBound : s0.regs 10 + cfg.ctxBytes <= modulus64
  scrAlign : s0.regs 11 % 8 = 0
  scrBound : s0.regs 11 + cfg.scrBytes <= modulus64
  x6Init   : s0.regs 6 <= cfg.idxMask ∧ s0.regs 6 % 8 = 0
  x7Init   : ∃ k, k <= cfg.idxMask ∧ k % 8 = 0 ∧ s0.regs 7 = s0.regs 11 + k

structure ParcelSfiInv (cfg : SfiCfg) (s0 s : RvState) : Prop where
  regsPreserved : ∀ r, isTempReg r = false → r ≠ 6 → r ≠ 7 → s.regs r = s0.regs r
  x6Bounded     : s.regs 6 <= cfg.idxMask ∧ s.regs 6 % 8 = 0
  x7Confined    : ∃ k, k <= cfg.idxMask ∧ k % 8 = 0 ∧ s.regs 7 = s0.regs 11 + k
  memConfined   : ∀ a, ¬inSandbox cfg s0 a → s.mem a = s0.mem a

private theorem invWithPc {cfg : SfiCfg} {s0 s : RvState} (pc' : Nat)
    (hinv : ParcelSfiInv cfg s0 s) : ParcelSfiInv cfg s0 { s with pc := pc' } :=
  ⟨hinv.regsPreserved, hinv.x6Bounded, hinv.x7Confined, hinv.memConfined⟩

private theorem buildParcelBitmap_len :
    ∀ (n : Nat) (hws : List Nat) (bmap : List Bool),
      hws.length <= n →
      buildParcelBitmap hws = some bmap →
      bmap.length = hws.length := by
  intro n
  induction n with
  | zero =>
      intro hws bmap hlen hbm
      cases hws with
      | nil => simp [buildParcelBitmap] at hbm; subst hbm; rfl
      | cons _ _ => simp at hlen
  | succ m ih =>
      intro hws bmap hlen hbm
      cases hws with
      | nil => simp [buildParcelBitmap] at hbm; subst hbm; rfl
      | cons lo rest =>
          cases rest with
          | nil =>
              simp only [buildParcelBitmap] at hbm
              split at hbm
              · contradiction
              · injection hbm with h'; subst h'; rfl
          | cons hi tail =>
              simp only [buildParcelBitmap] at hbm
              split at hbm
              · cases hsub : buildParcelBitmap tail with
                | none => simp [hsub] at hbm
                | some bRest =>
                    simp [hsub] at hbm; subst hbm
                    have hrec := ih tail bRest (by simp at hlen ⊢; omega) hsub
                    simp [hrec]
              · cases hsub : buildParcelBitmap (hi :: tail) with
                | none => simp [hsub] at hbm
                | some bRest =>
                    simp [hsub] at hbm; subst hbm
                    have hrec := ih (hi :: tail) bRest (by simp at hlen ⊢; omega) hsub
                    simp at hrec ⊢
                    exact hrec

private theorem checkParcelPositions_at (cfg : SfiCfg) (hws : List Nat) (bmap : List Bool) :
    ∀ (rem idx : Nat),
      rem <= bmap.length →
      bmap.length - rem <= idx →
      idx < bmap.length →
      checkParcelPositions cfg hws bmap rem = true →
      bmap[idx]? = some true →
      ∃ len insn,
        decodeRvParcel hws (2 * idx) = .parcel len insn ∧
        okParcelInsn cfg bmap (2 * idx) len insn = true := by
  intro rem
  induction rem with
  | zero =>
      intro idx _ hlo hhi
      omega
  | succ r ih =>
      intro idx hrem hlo hhi hchk hb
      simp only [checkParcelPositions, Bool.and_eq_true] at hchk
      by_cases heq : idx = bmap.length - (r + 1)
      · subst heq
        have hleft := hchk.1
        simp only [hb] at hleft
        cases hdec : decodeRvParcel hws (2 * (bmap.length - (r + 1))) with
        | misalignedFetch | pcOutOfBounds | truncated32AtEnd =>
            simp [hdec] at hleft
        | parcel len insn =>
            simp only [hdec] at hleft
            exact ⟨len, insn, rfl, hleft⟩
      · exact ih idx (by omega) (by omega) hhi hchk.2 hb

private theorem decodeRvParcel_pos_len (hws : List Nat) (pc len : Nat) (insn : RvInsn)
    (h : decodeRvParcel hws pc = .parcel len insn) : len = 2 ∨ len = 4 := by
  unfold decodeRvParcel at h
  split at h
  · contradiction
  · cases hlo : hws[pc / 2]? with
    | none => simp [hlo] at h
    | some lo =>
        simp only [hlo] at h
        cases h32 : is32BitPrefix lo
        · simp [h32] at h
          exact Or.inl h.1.symm
        · simp only [h32, ↓reduceIte] at h
          cases hhi : hws[pc / 2 + 1]? with
          | none => simp [hhi] at h
          | some hi =>
              simp [hhi] at h
              exact Or.inr h.1.symm

private theorem wrReg_preserves_inv_temp (cfg : SfiCfg) (s0 s : RvState) (rd val pc' : Nat)
    (hinv : ParcelSfiInv cfg s0 s) (htemp : isTempReg rd = true) :
    ParcelSfiInv cfg s0 { (wrReg s rd val) with pc := pc' } := by
  have hrd0 : rd ≠ 0 := by intro h0; subst h0; simp [isTempReg] at htemp
  have hrd6 : rd ≠ 6 := by intro h6; subst h6; simp [isTempReg] at htemp
  have hrd7 : rd ≠ 7 := by intro h7; subst h7; simp [isTempReg] at htemp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r hrnt hr6 hr7
    have hne : r ≠ rd := by intro he; subst he; simp [htemp] at hrnt
    simp [wrReg, hrd0, hne, hinv.regsPreserved r hrnt hr6 hr7]
  · simp [wrReg, hrd0, hrd6.symm]
    exact hinv.x6Bounded
  · simp [wrReg, hrd0, hrd7.symm]
    exact hinv.x7Confined
  · intro a hns
    simp [wrReg, hrd0, hinv.memConfined a hns]

private theorem and_bound_align (a m : Nat) (hm8 : m % 8 = 0) :
    (a &&& m) <= m ∧ (a &&& m) % 8 = 0 := by
  refine ⟨Nat.and_le_right, ?_⟩
  change (a &&& m) % (2 ^ 3) = 0
  rw [Nat.and_mod_two_pow]
  have hm0 : m % (2 ^ 3) = 0 := hm8
  simp [hm0]

private theorem sextBits_nonneg12 (u : Nat) (hu : u < 2048) :
    sextBits u 12 = (u : Int) := by
  unfold sextBits
  have h1 : u % 4096 = u := Nat.mod_eq_of_lt (by omega)
  have h2 : ¬(u >= 2048) := by omega
  simp [h1, h2]

private theorem addSigned64_lt (base off : Nat) (hlt : base + off < modulus64) :
    addSigned64 base (off : Int) = base + off := by
  unfold addSigned64
  have hb : base % modulus64 = base := Nat.mod_eq_of_lt (by omega)
  rw [hb]
  have hcast : ((base : Int) + (off : Int)) = ((base + off : Nat) : Int) := by omega
  rw [hcast]
  have hmod : (((base + off : Nat) : Int) % (modulus64 : Int)) = ((base + off : Nat) : Int) :=
    Int.emod_eq_of_lt (by omega) (by omega)
  rw [hmod]
  omega

private theorem writeMem64_outside (m : Nat → Nat) (addr val x : Nat)
    (hout : x < addr ∨ addr + 8 <= x) :
    writeMem64 m addr val x = m x := by
  unfold writeMem64 writeByte
  have h0 : (x == addr) = false := beq_false_of_ne (by omega)
  have h1 : (x == addr + 1) = false := beq_false_of_ne (by omega)
  have h2 : (x == addr + 2) = false := beq_false_of_ne (by omega)
  have h3 : (x == addr + 3) = false := beq_false_of_ne (by omega)
  have h4 : (x == addr + 4) = false := beq_false_of_ne (by omega)
  have h5 : (x == addr + 5) = false := beq_false_of_ne (by omega)
  have h6 : (x == addr + 6) = false := beq_false_of_ne (by omega)
  have h7 : (x == addr + 7) = false := beq_false_of_ne (by omega)
  simp [h0, h1, h2, h3, h4, h5, h6, h7]

private theorem addrOk8_safe (cfg : SfiCfg) (s0 s : RvState) (rs1 off : Nat)
    (hent : ParcelEntry cfg s0) (hinv : ParcelSfiInv cfg s0 s)
    (hok : addrOk8 cfg rs1 off = true) :
    off < 2048 ∧
    ((rdReg s rs1 + off) % modulus64 = rdReg s rs1 + off) ∧
    (addSigned64 (rdReg s rs1) (sextBits off 12) = rdReg s rs1 + off) ∧
    ((rdReg s rs1 + off) % 8 = 0) ∧
    (∀ a, ¬inSandbox cfg s0 a → a < rdReg s rs1 + off ∨ rdReg s rs1 + off + 8 <= a) := by
  unfold addrOk8 at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨hoff2048, hoff8⟩, hregion⟩
  cases hregion with
  | inl hctx =>
      rcases hctx with ⟨hrs1, hctxB⟩
      subst hrs1
      have hr10 : rdReg s 10 = s0.regs 10 := by
        simp [rdReg]
        exact hinv.regsPreserved 10 (by decide) (by decide) (by decide)
      rw [hr10]
      have hlt : s0.regs 10 + off < modulus64 := by
        have := hent.ctxBound; omega
      refine ⟨hoff2048, Nat.mod_eq_of_lt hlt, ?_, ?_, ?_⟩
      · rw [sextBits_nonneg12 off hoff2048]
        exact addSigned64_lt (s0.regs 10) off hlt
      · have := hent.ctxAlign; omega
      · intro a hns
        by_cases hlo : a < s0.regs 10 + off
        · exact Or.inl hlo
        · by_cases hhi : s0.regs 10 + off + 8 <= a
          · exact Or.inr hhi
          · exfalso
            apply hns
            exact Or.inl ⟨by omega, by omega⟩
  | inr hscr =>
      rcases hscr with ⟨hrs1, hscrB⟩
      subst hrs1
      rcases hinv.x7Confined with ⟨k, hkM, hk8, hx7⟩
      have hr7 : rdReg s 7 = s0.regs 11 + k := by simp [rdReg, hx7]
      rw [hr7]
      have hlt : (s0.regs 11 + k) + off < modulus64 := by
        have := hent.scrBound; omega
      refine ⟨hoff2048, Nat.mod_eq_of_lt hlt, ?_, ?_, ?_⟩
      · rw [sextBits_nonneg12 off hoff2048]
        exact addSigned64_lt (s0.regs 11 + k) off hlt
      · have := hent.scrAlign; omega
      · intro a hns
        by_cases hlo : a < (s0.regs 11 + k) + off
        · exact Or.inl hlo
        · by_cases hhi : (s0.regs 11 + k) + off + 8 <= a
          · exact Or.inr hhi
          · exfalso
            apply hns
            exact Or.inr ⟨by omega, by omega⟩

private theorem bitmapAllows_bounds (bmap : List Bool) (pc : Nat)
    (hb : bitmapAllows bmap pc = true) :
    pc % 2 = 0 ∧ pc / 2 < bmap.length ∧ bmap[pc / 2]? = some true := by
  unfold bitmapAllows at hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  rcases hb with ⟨heven, hsome⟩
  by_cases hlt : pc / 2 < bmap.length
  · exact ⟨heven, hlt, hsome⟩
  · exfalso
    have hnone : bmap[pc / 2]? = none := List.getElem?_eq_none (by omega)
    rw [hnone] at hsome
    contradiction

private theorem step_sound_and_advances
    (cfg : SfiCfg) (hws : List Nat) (bmap : List Bool) (s0 s : RvState) (idx : Nat)
    (hscrCfg : cfg.idxMask + 8 <= cfg.scrBytes)
    (hent : ParcelEntry cfg s0)
    (hinv : ParcelSfiInv cfg s0 s)
    (hpc : s.pc = 2 * idx)
    (hdec : ∃ len insn,
      decodeRvParcel hws (2 * idx) = .parcel len insn ∧
      okParcelInsn cfg bmap (2 * idx) len insn = true) :
    (∃ s', stepParcel hws s = .returned (s0.regs 1) s' ∧ ParcelSfiInv cfg s0 s') ∨
    (∃ s' idx',
      stepParcel hws s = .running s' ∧
      s'.pc = 2 * idx' ∧
      idx < idx' ∧
      idx' < bmap.length ∧
      bmap[idx']? = some true ∧
      ParcelSfiInv cfg s0 s') := by
  rcases hdec with ⟨len, insn, hfetch, hok⟩
  have hlen24 : len = 2 ∨ len = 4 := decodeRvParcel_pos_len hws (2 * idx) len insn hfetch
  unfold stepParcel
  rw [hpc, hfetch]
  cases insn with
  | lui rd imm20 =>
      simp only [okParcelInsn, Bool.and_eq_true] at hok
      rcases bitmapAllows_bounds bmap (2 * idx + len) hok.1 with ⟨heven, hlt, hb'⟩
      refine Or.inr ⟨_, (2 * idx + len) / 2, rfl, ?_, ?_, hlt, hb', ?_⟩
      · simp; omega
      · omega
      · rw [← hpc]
        exact wrReg_preserves_inv_temp cfg s0 s rd (luiVal64 imm20) (s.pc + len) hinv hok.2
  | addi rd rs1 imm =>
      simp only [okParcelInsn, Bool.and_eq_true] at hok
      rcases bitmapAllows_bounds bmap (2 * idx + len) hok.1.1 with ⟨heven, hlt, hb'⟩
      refine Or.inr ⟨_, (2 * idx + len) / 2, rfl, ?_, ?_, hlt, hb', ?_⟩
      · simp; omega
      · omega
      · rw [← hpc]
        exact wrReg_preserves_inv_temp cfg s0 s rd (addSigned64 (rdReg s rs1) imm) (s.pc + len) hinv hok.1.2
  | andi rd rs1 imm12 =>
      simp only [okParcelInsn, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
      rcases hok with ⟨⟨hbNext, _⟩, hrdCase⟩
      rcases bitmapAllows_bounds bmap (2 * idx + len) hbNext with ⟨heven, hlt, hb'⟩
      cases hrdCase with
      | inl htemp =>
          refine Or.inr ⟨_, (2 * idx + len) / 2, rfl, ?_, ?_, hlt, hb', ?_⟩
          · simp; omega
          · omega
          · rw [← hpc]
            exact wrReg_preserves_inv_temp cfg s0 s rd _ (s.pc + len) hinv htemp
      | inr hx6 =>
          rcases hx6 with ⟨⟨⟨hrd6, himm2048⟩, himmMask⟩, himm8⟩
          subst hrd6
          have hmMod : imm12 % 4096 = imm12 := Nat.mod_eq_of_lt (by omega)
          refine Or.inr ⟨_, (2 * idx + len) / 2, rfl, ?_, ?_, hlt, hb', ?_⟩
          · simp; omega
          · omega
          · refine ⟨?_, ?_, ?_, ?_⟩
            · intro r hrnt hr6 hr7
              simp [wrReg, hr6, hinv.regsPreserved r hrnt hr6 hr7]
            · simp only [wrReg, beq_iff_eq, Nat.reduceBeqDiff, Bool.false_eq_true, ↓reduceIte, hmMod, himm2048]
              have hba := and_bound_align (rdReg s rs1) imm12 himm8
              have hmod64 : (rdReg s rs1 &&& imm12) % modulus64 = (rdReg s rs1 &&& imm12) := by
                apply Nat.mod_eq_of_lt
                have := hba.1; unfold modulus64; omega
              rw [hmod64]
              exact ⟨Nat.le_trans hba.1 himmMask, hba.2⟩
            · simp [wrReg]
              exact hinv.x7Confined
            · intro a hns
              simp [wrReg, hinv.memConfined a hns]
  | add rd rs1 rs2 =>
      simp only [okParcelInsn, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
      rcases hok with ⟨hbNext, hrdCase⟩
      rcases bitmapAllows_bounds bmap (2 * idx + len) hbNext with ⟨heven, hlt, hb'⟩
      cases hrdCase with
      | inl htemp =>
          refine Or.inr ⟨_, (2 * idx + len) / 2, rfl, ?_, ?_, hlt, hb', ?_⟩
          · simp; omega
          · omega
          · rw [← hpc]
            exact wrReg_preserves_inv_temp cfg s0 s rd _ (s.pc + len) hinv htemp.1.1
      | inr hx7 =>
          rcases hx7 with ⟨⟨hrd7, hrs1_11⟩, hrs2_6⟩
          subst hrd7; subst hrs1_11; subst hrs2_6
          refine Or.inr ⟨_, (2 * idx + len) / 2, rfl, ?_, ?_, hlt, hb', ?_⟩
          · simp; omega
          · omega
          · refine ⟨?_, ?_, ?_, ?_⟩
            · intro r hrnt hr6 hr7
              simp [wrReg, hr7, hinv.regsPreserved r hrnt hr6 hr7]
            · simp [wrReg]
              exact hinv.x6Bounded
            · have hr11 : rdReg s 11 = s0.regs 11 := by
                simp [rdReg]
                exact hinv.regsPreserved 11 (by decide) (by decide) (by decide)
              have hr6 : rdReg s 6 = s.regs 6 := by simp [rdReg]
              have hsumLt : s0.regs 11 + s.regs 6 < modulus64 := by
                have := hent.scrBound
                have := hinv.x6Bounded.1
                omega
              refine ⟨s.regs 6, hinv.x6Bounded.1, hinv.x6Bounded.2, ?_⟩
              simp [wrReg, hr11, hr6, Nat.mod_eq_of_lt hsumLt]
            · intro a hns
              simp [wrReg, hinv.memConfined a hns]
  | ld rd rs1 imm12 =>
      simp only [okParcelInsn, Bool.and_eq_true] at hok
      rcases addrOk8_safe cfg s0 s rs1 imm12 hent hinv hok.2 with ⟨_, _, hadd, hal8, _⟩
      rcases bitmapAllows_bounds bmap (2 * idx + len) hok.1.1 with ⟨heven, hlt, hb'⟩
      have hmis : (addSigned64 (rdReg s rs1) (sextBits imm12 12) % 8 != 0) = false := by
        rw [hadd]; simp [hal8]
      simp only [hmis, Bool.false_eq_true, ↓reduceIte]
      refine Or.inr ⟨_, (2 * idx + len) / 2, rfl, ?_, ?_, hlt, hb', ?_⟩
      · simp; omega
      · omega
      · rw [← hpc]
        exact wrReg_preserves_inv_temp cfg s0 s rd _ (s.pc + len) hinv hok.1.2
  | sd rs2 rs1 imm12 =>
      simp only [okParcelInsn, Bool.and_eq_true] at hok
      rcases addrOk8_safe cfg s0 s rs1 imm12 hent hinv hok.2 with ⟨_, _, hadd, hal8, hout⟩
      rcases bitmapAllows_bounds bmap (2 * idx + len) hok.1.1 with ⟨heven, hlt, hb'⟩
      have hmis : (addSigned64 (rdReg s rs1) (sextBits imm12 12) % 8 != 0) = false := by
        rw [hadd]; simp [hal8]
      simp only [hmis, Bool.false_eq_true, ↓reduceIte]
      refine Or.inr ⟨_, (2 * idx + len) / 2, rfl, ?_, ?_, hlt, hb', ?_⟩
      · simp; omega
      · omega
      · refine ⟨hinv.regsPreserved, hinv.x6Bounded, hinv.x7Confined, ?_⟩
        intro a hns
        change writeMem64 s.mem (addSigned64 (rdReg s rs1) (sextBits imm12 12)) (rdReg s rs2) a = s0.mem a
        rw [hadd, writeMem64_outside s.mem (rdReg s rs1 + imm12) (rdReg s rs2) a (hout a hns)]
        exact hinv.memConfined a hns
  | rvcLd rd rs1 uimm =>
      simp only [okParcelInsn, Bool.and_eq_true] at hok
      rcases addrOk8_safe cfg s0 s rs1 uimm hent hinv hok.2 with ⟨_, hmod, _, hal8, _⟩
      rcases bitmapAllows_bounds bmap (2 * idx + len) hok.1.1 with ⟨heven, hlt, hb'⟩
      have hmis : (((rdReg s rs1 + uimm) % modulus64) % 8 != 0) = false := by
        rw [hmod]; simp [hal8]
      simp only [hmis, Bool.false_eq_true, ↓reduceIte]
      refine Or.inr ⟨_, (2 * idx + len) / 2, rfl, ?_, ?_, hlt, hb', ?_⟩
      · simp; omega
      · omega
      · rw [← hpc]
        exact wrReg_preserves_inv_temp cfg s0 s rd _ (s.pc + len) hinv hok.1.2
  | rvcSd rs2 rs1 uimm =>
      simp only [okParcelInsn, Bool.and_eq_true] at hok
      rcases addrOk8_safe cfg s0 s rs1 uimm hent hinv hok.2 with ⟨_, hmod, _, hal8, hout⟩
      rcases bitmapAllows_bounds bmap (2 * idx + len) hok.1.1 with ⟨heven, hlt, hb'⟩
      have hmis : (((rdReg s rs1 + uimm) % modulus64) % 8 != 0) = false := by
        rw [hmod]; simp [hal8]
      simp only [hmis, Bool.false_eq_true, ↓reduceIte]
      refine Or.inr ⟨_, (2 * idx + len) / 2, rfl, ?_, ?_, hlt, hb', ?_⟩
      · simp; omega
      · omega
      · refine ⟨hinv.regsPreserved, hinv.x6Bounded, hinv.x7Confined, ?_⟩
        intro a hns
        change writeMem64 s.mem ((rdReg s rs1 + uimm) % modulus64) (rdReg s rs2) a = s0.mem a
        rw [hmod, writeMem64_outside s.mem (rdReg s rs1 + uimm) (rdReg s rs2) a (hout a hns)]
        exact hinv.memConfined a hns
  | branch isNe rs1 rs2 off =>
      simp only [okParcelInsn, Bool.and_eq_true, decide_eq_true_eq] at hok
      rcases hok with ⟨⟨⟨_, _⟩, hoffPos⟩, hbNext, hbTgt⟩
      by_cases hcond : (if isNe then rdReg s rs1 != rdReg s rs2 else rdReg s rs1 == rdReg s rs2) = true
      · simp only [hcond, ↓reduceIte]
        have hsumEq : (((2 * idx : Nat) : Int) + off).toNat = 2 * idx + off.toNat := by omega
        have hltFalse : decide (((2 * idx : Nat) : Int) + off < 0) = false :=
          decide_eq_false (by omega)
        rcases bitmapAllows_bounds bmap (2 * idx + off.toNat) hbTgt with ⟨heven, hlt, hb'⟩
        have hmodFalse : ((((2 * idx : Nat) : Int) + off).toNat % 2 != 0) = false := by
          rw [hsumEq]; simp [heven]
        simp only [hltFalse, hmodFalse, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
        refine Or.inr ⟨_, (2 * idx + off.toNat) / 2, rfl, ?_, ?_, hlt, hb', invWithPc _ hinv⟩
        · change (((2 * idx : Nat) : Int) + off).toNat = 2 * ((2 * idx + off.toNat) / 2)
          rw [hsumEq]; omega
        · omega
      · simp only [Bool.not_eq_true] at hcond
        simp only [hcond, Bool.false_eq_true, ↓reduceIte]
        rcases bitmapAllows_bounds bmap (2 * idx + len) hbNext with ⟨heven, hlt, hb'⟩
        refine Or.inr ⟨_, (2 * idx + len) / 2, rfl, ?_, ?_, hlt, hb', invWithPc _ hinv⟩
        · simp; omega
        · omega
  | jal rd off =>
      simp only [okParcelInsn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
      rcases hok with ⟨⟨hrd0, hoffPos⟩, hbTgt⟩
      subst hrd0
      have hsumEq : (((2 * idx : Nat) : Int) + off).toNat = 2 * idx + off.toNat := by omega
      have hltFalse : decide (((2 * idx : Nat) : Int) + off < 0) = false :=
        decide_eq_false (by omega)
      rcases bitmapAllows_bounds bmap (2 * idx + off.toNat) hbTgt with ⟨heven, hlt, hb'⟩
      have hmodFalse : ((((2 * idx : Nat) : Int) + off).toNat % 2 != 0) = false := by
        rw [hsumEq]; simp [heven]
      simp only [hltFalse, hmodFalse, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      refine Or.inr ⟨_, (2 * idx + off.toNat) / 2, rfl, ?_, ?_, hlt, hb', ?_⟩
      · change (((2 * idx : Nat) : Int) + off).toNat = 2 * ((2 * idx + off.toNat) / 2)
        rw [hsumEq]; omega
      · omega
      · simp only [wrReg, beq_self_eq_true, ↓reduceIte]
        exact invWithPc _ hinv
  | jalr rd rs1 imm =>
      simp only [okParcelInsn, Bool.and_eq_true, beq_iff_eq] at hok
      rcases hok with ⟨⟨hrd0, hrs1_1⟩, himm0⟩
      subst hrd0; subst hrs1_1; subst himm0
      have hr1 : rdReg s 1 = s0.regs 1 := by
        simp [rdReg]
        exact hinv.regsPreserved 1 (by decide) (by decide) (by decide)
      have hraw : addSigned64 (rdReg s 1) 0 = s0.regs 1 := by
        rw [hr1]
        exact addSigned64_lt (s0.regs 1) 0 hent.raBound
      have heven : s0.regs 1 % 2 = 0 := hent.raEven
      refine Or.inl ⟨s, ?_, hinv⟩
      simp [wrReg, hraw, heven]
  | ebreak | system _ | illegal =>
      simp [okParcelInsn] at hok

private theorem run_from_idx_terminates_safely
    (cfg : SfiCfg) (hws : List Nat) (bmap : List Bool) (s0 : RvState)
    (hscrCfg : cfg.idxMask + 8 <= cfg.scrBytes)
    (hchkAll : checkParcelPositions cfg hws bmap bmap.length = true)
    (hent : ParcelEntry cfg s0) :
    ∀ (rem idx : Nat) (s : RvState),
      bmap.length - idx <= rem →
      idx < bmap.length →
      bmap[idx]? = some true →
      s.pc = 2 * idx →
      ParcelSfiInv cfg s0 s →
      (∃ k s', k <= rem ∧ runParcels hws k s = .returned (s0.regs 1) s' ∧ ParcelSfiInv cfg s0 s') ∧
      (∀ n, match runParcels hws n s with
            | .running sn => bitmapAllows bmap sn.pc = true ∧ ParcelSfiInv cfg s0 sn
            | .returned tgt sn => tgt = s0.regs 1 ∧ ParcelSfiInv cfg s0 sn
            | .trapped _ => False) := by
  intro rem
  induction rem with
  | zero =>
      intro idx _ hrem hlt
      omega
  | succ r ih =>
      intro idx s hrem hlt hb hpc hinv
      have hdec := checkParcelPositions_at cfg hws bmap bmap.length idx (Nat.le_refl _) (by omega) hlt hchkAll hb
      have hstep := step_sound_and_advances cfg hws bmap s0 s idx hscrCfg hent hinv hpc hdec
      cases hstep with
      | inl hret =>
          rcases hret with ⟨s', hst, hinv'⟩
          refine ⟨⟨1, s', by omega, ?_, hinv'⟩, ?_⟩
          · simp [runParcels, hst]
          · intro n
            cases n with
            | zero =>
                simp [runParcels, bitmapAllows, hpc, hb, hinv]
            | succ m =>
                simp [runParcels, hst, hinv']
      | inr hrun =>
          rcases hrun with ⟨s', idx', hst, hpc', hgt, hlt', hb', hinv'⟩
          have hsub := ih idx' s' (by omega) hlt' hb' hpc' hinv'
          rcases hsub with ⟨⟨k, sFinal, hk, hrunK, hinvF⟩, hall⟩
          refine ⟨⟨k + 1, sFinal, by omega, ?_, hinvF⟩, ?_⟩
          · simp [runParcels, hst, hrunK]
          · intro n
            cases n with
            | zero =>
                simp [runParcels, bitmapAllows, hpc, hb, hinv]
            | succ m =>
                simpa [runParcels, hst] using hall m

/-- Theorem 3: Parcel-start bitmap SFI soundness over mixed `16/32`-bit `RVC` + `RV64I` streams. -/
theorem checkRvParcelBitmapSfi_sound
    (cfg : SfiCfg) (halfwords : List Nat) (s0 : RvState)
    (hcheck : checkRvParcelBitmapSfi cfg halfwords = true)
    (hent : ParcelEntry cfg s0) :
    ∃ bmap,
      buildParcelBitmap halfwords = some bmap ∧
      (∃ k s',
        k <= halfwords.length ∧
        runParcels halfwords k s0 = .returned (s0.regs 1) s' ∧
        ParcelSfiInv cfg s0 s') ∧
      (∀ n,
        match runParcels halfwords n s0 with
        | .running sn => bitmapAllows bmap sn.pc = true ∧ ParcelSfiInv cfg s0 sn
        | .returned tgt sn => tgt = s0.regs 1 ∧ ParcelSfiInv cfg s0 sn
        | .trapped _ => False) := by
  unfold checkRvParcelBitmapSfi at hcheck
  cases hbm : buildParcelBitmap halfwords with
  | none => simp [hbm] at hcheck
  | some bmap =>
      simp only [hbm, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨_, hscrCfg⟩, hb0⟩, hchkAll⟩
      have hlenEq : bmap.length = halfwords.length :=
        buildParcelBitmap_len halfwords.length halfwords bmap (Nat.le_refl _) hbm
      rcases bitmapAllows_bounds bmap 0 hb0 with ⟨_, hlt0, htrue0⟩
      have hinv0 : ParcelSfiInv cfg s0 s0 :=
        ⟨fun _ _ _ _ => rfl, hent.x6Init, hent.x7Init, fun _ _ => rfl⟩
      have hmain :=
        run_from_idx_terminates_safely cfg halfwords bmap s0 hscrCfg hchkAll hent
          bmap.length 0 s0 (by omega) hlt0 htrue0 hent.pcZero hinv0
      refine ⟨bmap, rfl, ?_, hmain.2⟩
      rcases hmain.1 with ⟨k, s', hk, hret, hinv'⟩
      exact ⟨k, s', hlenEq ▸ hk, hret, hinv'⟩

/-- Non-vacuity & mid-parcel jump rejection witness for `checkRvParcelBitmapSfi`:
    1. Mixed `16/32`-bit module `[0x029d, 0x02b7, 0xe10c, 0xe110, 0x8082]`
       (`c.addi t0, 7` [2 B]; `lui t0, 0xe10c0` [4 B, interior `0xe10c` marked `false`];
        `c.sd a2, 0(a0)` [2 B]; `c.jr ra` [2 B]) is ADMITTED (`= true`) with bitmap
       `[true, true, false, true, true]`.
    2. Prepending `c.j +4` (`0xa011`, raw11=4 -> +8? Wait: `0xa009` raw11=2 -> `off = +4`,
       jumping from `pc = 0` directly onto the interior `pc = 4` upper halfword `0xe10c`!)
       is REJECTED (`= false`) because `bmap[2] == false`! -/
def validMixedRvcModule : List Nat := [0x029d, 0x02b7, 0xe10c, 0xe110, 0x8082]
def rogueJumpIntoMidInsnModule : List Nat := [0xa009, 0x02b7, 0xe10c, 0x8082]

theorem parcel_bitmap_admits_mixed_and_rejects_mid_jump :
    buildParcelBitmap validMixedRvcModule = some [true, true, false, true, true] ∧
    checkRvParcelBitmapSfi demoSfiCfg validMixedRvcModule = true ∧
    buildParcelBitmap rogueJumpIntoMidInsnModule = some [true, true, false, true] ∧
    decodeRvParcel rogueJumpIntoMidInsnModule 0 = .parcel 2 (.jal 0 4) ∧
    checkRvParcelBitmapSfi demoSfiCfg rogueJumpIntoMidInsnModule = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Part III: Byte-Shrinking `RelocRelaxMap` Span & `.eh_frame` `ADD`/`SUB` Preservation -/

inductive SectionAtom where
  | fixed     (bytes : List UInt8)
  | relaxable (preBytes postBytes : List UInt8)
  deriving DecidableEq, Repr

def atomPreBytes : SectionAtom → List UInt8
  | .fixed bs => bs
  | .relaxable pre _ => pre

def atomPostBytes : SectionAtom → List UInt8
  | .fixed bs => bs
  | .relaxable _ post => post

def atomWellFormed : SectionAtom → Bool
  | .fixed _ => true
  | .relaxable pre post => decide (post.length <= pre.length)

def atomsWellFormed : List SectionAtom → Bool
  | [] => true
  | a :: rest => atomWellFormed a && atomsWellFormed rest

def preSectionBytes : List SectionAtom → List UInt8
  | [] => []
  | a :: rest => atomPreBytes a ++ preSectionBytes rest

def postSectionBytes : List SectionAtom → List UInt8
  | [] => []
  | a :: rest => atomPostBytes a ++ postSectionBytes rest

def preAtomOffset (atoms : List SectionAtom) (idx : Nat) : Nat :=
  (preSectionBytes (atoms.take idx)).length

def postAtomOffset (atoms : List SectionAtom) (idx : Nat) : Nat :=
  (postSectionBytes (atoms.take idx)).length

def cumBytesDeleted (atoms : List SectionAtom) (idx : Nat) : Nat :=
  preAtomOffset atoms idx - postAtomOffset atoms idx

def evalAddSubPair (baseVA : Nat) (atoms : List SectionAtom) (startIdx endIdx : Nat) : Nat :=
  (baseVA + postAtomOffset atoms endIdx) - (baseVA + postAtomOffset atoms startIdx)

def extractByteSlice (bytes : List UInt8) (off len : Nat) : List UInt8 :=
  (bytes.drop off).take len

def sumCfaAdvanceDeltas (baseVA : Nat) (atoms : List SectionAtom) : List Nat → Nat
  | [] | [_] => 0
  | i :: j :: rest =>
      evalAddSubPair baseVA atoms i j + sumCfaAdvanceDeltas baseVA atoms (j :: rest)

def isMonotoneChain : List Nat → Bool
  | [] | [_] => true
  | i :: j :: rest => decide (i <= j) && isMonotoneChain (j :: rest)

def victimAtomsDefaultRelax : List SectionAtom :=
  [ .fixed [0x41, 0x11, 0x06, 0xe4]
  , .relaxable (List.replicate 8 0x97) (List.replicate 4 0xef)
  , .fixed [0x05, 0x05]
  , .relaxable (List.replicate 16 0x13) (List.replicate 8 0x13)
  , .relaxable (List.replicate 8 0x17) [0x01, 0xa0]
  , .fixed [0x13, 0x05, 0x35, 0x06]
  , .fixed [0x06, 0x05, 0x15, 0x05, 0xa2, 0x60, 0x41, 0x01, 0x82, 0x80]
  ]

def victimAtomsLinkerNoRelax : List SectionAtom :=
  [ .fixed [0x41, 0x11, 0x06, 0xe4]
  , .relaxable (List.replicate 8 0x97) (List.replicate 8 0x97)
  , .fixed [0x05, 0x05]
  , .relaxable (List.replicate 16 0x13) (List.replicate 4 0x13)
  , .relaxable (List.replicate 8 0x17) (List.replicate 8 0x17)
  , .fixed [0x13, 0x05, 0x35, 0x06]
  , .fixed [0x06, 0x05, 0x15, 0x05, 0xa2, 0x60, 0x41, 0x01, 0x82, 0x80]
  ]

/-- Theorem 4: Constructive refutation of pre-link `SHF_EXCLUDE` spans under both
    default `--relax` (`52 B -> 34 B`) and `--no-relax` with `R_RISCV_ALIGN` (`52 B -> 40 B`). -/
theorem shf_exclude_prelink_span_unsound_under_relax :
    (preSectionBytes victimAtomsDefaultRelax).length = 52 ∧
    preAtomOffset victimAtomsDefaultRelax 4 = 30 ∧
    preAtomOffset victimAtomsDefaultRelax 5 = 38 ∧
    (postSectionBytes victimAtomsDefaultRelax).length = 34 ∧
    preAtomOffset victimAtomsDefaultRelax 5 > (postSectionBytes victimAtomsDefaultRelax).length ∧
    (postSectionBytes victimAtomsLinkerNoRelax).length = 40 ∧
    postAtomOffset victimAtomsLinkerNoRelax 4 = 18 ∧
    extractByteSlice (postSectionBytes victimAtomsLinkerNoRelax) 30 8 ≠ List.replicate 8 0x17 := by
  decide

private theorem postSectionBytes_append (xs ys : List SectionAtom) :
    postSectionBytes (xs ++ ys) = postSectionBytes xs ++ postSectionBytes ys := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
      simp [postSectionBytes, ih, List.append_assoc]

private theorem postAtomOffset_mono (atoms : List SectionAtom) :
    ∀ {i j : Nat}, i <= j → postAtomOffset atoms i <= postAtomOffset atoms j := by
  intro i j hij
  unfold postAtomOffset
  have hsplit : atoms.take j = atoms.take i ++ (atoms.drop i).take (j - i) := by
    rw [← List.take_add, Nat.add_sub_of_le hij]
  rw [hsplit, postSectionBytes_append, List.length_append]
  omega

private theorem pre_ge_post_len :
    ∀ (atoms : List SectionAtom),
      atomsWellFormed atoms = true →
      (postSectionBytes atoms).length <= (preSectionBytes atoms).length
  | [], _ => Nat.le_refl 0
  | a :: rest, hwf => by
      simp only [atomsWellFormed, Bool.and_eq_true] at hwf
      have ih := pre_ge_post_len rest hwf.2
      cases a with
      | fixed bs =>
          simp only [preSectionBytes, postSectionBytes, atomPreBytes, atomPostBytes, List.length_append]
          omega
      | relaxable pre post =>
          simp only [atomWellFormed, decide_eq_true_eq] at hwf
          have ha := hwf.1
          simp only [preSectionBytes, postSectionBytes, atomPreBytes, atomPostBytes, List.length_append]
          omega

private theorem take_succ_eq_snoc (atoms : List SectionAtom) (idx : Nat) (a : SectionAtom)
    (hget : atoms[idx]? = some a) :
    atoms.take (idx + 1) = atoms.take idx ++ [a] := by
  induction atoms generalizing idx with
  | nil => simp at hget
  | cons x xs ih =>
      cases idx with
      | zero =>
          simp at hget
          subst hget
          rfl
      | succ k =>
          simp only [List.getElem?_cons_succ] at hget
          simp [List.take_succ_cons, ih k hget]

private theorem postSectionBytes_split_at (atoms : List SectionAtom) (idx : Nat) (a : SectionAtom)
    (hget : atoms[idx]? = some a) :
    postSectionBytes atoms =
      postSectionBytes (atoms.take idx) ++ atomPostBytes a ++ postSectionBytes (atoms.drop (idx + 1)) := by
  have hlist : atoms = atoms.take (idx + 1) ++ atoms.drop (idx + 1) := (List.take_append_drop (idx + 1) atoms).symm
  conv => lhs; rw [hlist]
  rw [take_succ_eq_snoc atoms idx a hget, postSectionBytes_append, postSectionBytes_append]
  simp [postSectionBytes, List.append_assoc]

private theorem extractByteSlice_mid (prefixBs midBs suffixBs : List UInt8) :
    extractByteSlice (prefixBs ++ midBs ++ suffixBs) prefixBs.length midBs.length = midBs := by
  unfold extractByteSlice
  rw [List.append_assoc, List.drop_left, List.take_left]

private theorem monotoneChain_head_le_last :
    ∀ (rest : List Nat) (start finish : Nat),
      isMonotoneChain (start :: rest ++ [finish]) = true →
      start <= finish
  | [], start, finish, h => by
      simp [isMonotoneChain] at h
      exact h
  | nxt :: tl, start, finish, h => by
      simp only [List.cons_append, isMonotoneChain, Bool.and_eq_true, decide_eq_true_eq] at h
      exact Nat.le_trans h.1 (monotoneChain_head_le_last tl nxt finish h.2)

private theorem sumCfaAdvanceDeltas_telescopes (baseVA : Nat) (atoms : List SectionAtom) :
    ∀ (chain : List Nat) (first last : Nat),
      isMonotoneChain (first :: chain ++ [last]) = true →
      sumCfaAdvanceDeltas baseVA atoms (first :: chain ++ [last]) =
        evalAddSubPair baseVA atoms first last := by
  intro chain
  induction chain with
  | nil =>
      intro first last _
      simp [sumCfaAdvanceDeltas]
  | cons mid rest ih =>
      intro first last hmono
      simp only [List.cons_append, isMonotoneChain, Bool.and_eq_true, decide_eq_true_eq] at hmono
      have h12 : postAtomOffset atoms first <= postAtomOffset atoms mid :=
        postAtomOffset_mono atoms hmono.1
      have h2last : mid <= last := monotoneChain_head_le_last rest mid last hmono.2
      have h23 : postAtomOffset atoms mid <= postAtomOffset atoms last :=
        postAtomOffset_mono atoms h2last
      have hrec := ih mid last hmono.2
      change evalAddSubPair baseVA atoms first mid +
        sumCfaAdvanceDeltas baseVA atoms (mid :: rest ++ [last]) =
        evalAddSubPair baseVA atoms first last
      rw [hrec]
      unfold evalAddSubPair
      omega

private theorem atomsWellFormed_take :
    ∀ (atoms : List SectionAtom) (idx : Nat),
      atomsWellFormed atoms = true →
      atomsWellFormed (atoms.take idx) = true
  | [], _, _ => by simp [atomsWellFormed]
  | _ :: _, 0, _ => by simp [atomsWellFormed]
  | _ :: xs, k + 1, hwf => by
      simp only [atomsWellFormed, Bool.and_eq_true] at hwf
      simp [List.take_succ_cons, atomsWellFormed, hwf.1, atomsWellFormed_take xs k hwf.2]

/-- Theorem 5: Retained `ADD`/`SUB` (`SET6`/`SUB6`) relocations preserve exact post-link
    span boundaries, recover every post-link atom byte slice (`extractByteSlice`) verbatim,
    satisfy cumulative shrinkage monotonicity (`postAtomOffset + cumBytesDeleted = preAtomOffset`),
    and telescope `.eh_frame` `DW_CFA_advance_loc` chains to the exact FDE `address_range`. -/
theorem reloc_relax_preserves_fde_and_spans
    (baseVA : Nat) (atoms : List SectionAtom)
    (hwf : atomsWellFormed atoms = true) :
    (∀ idx, postAtomOffset atoms idx + cumBytesDeleted atoms idx = preAtomOffset atoms idx) ∧
    (∀ idx a,
      atoms[idx]? = some a →
      evalAddSubPair baseVA atoms idx (idx + 1) = (atomPostBytes a).length ∧
      extractByteSlice
        (postSectionBytes atoms)
        (postAtomOffset atoms idx)
        (evalAddSubPair baseVA atoms idx (idx + 1)) = atomPostBytes a) ∧
    (∀ chain first last,
      isMonotoneChain (first :: chain ++ [last]) = true →
      sumCfaAdvanceDeltas baseVA atoms (first :: chain ++ [last]) =
        evalAddSubPair baseVA atoms first last) := by
  refine ⟨?_, ?_, ?_⟩
  · intro idx
    unfold cumBytesDeleted preAtomOffset postAtomOffset
    have hle := pre_ge_post_len (atoms.take idx) (atomsWellFormed_take atoms idx hwf)
    omega
  · intro idx a hget
    have hlen : postAtomOffset atoms (idx + 1) = postAtomOffset atoms idx + (atomPostBytes a).length := by
      unfold postAtomOffset
      rw [take_succ_eq_snoc atoms idx a hget, postSectionBytes_append]
      simp [postSectionBytes]
    have hpair : evalAddSubPair baseVA atoms idx (idx + 1) = (atomPostBytes a).length := by
      unfold evalAddSubPair
      rw [hlen]
      omega
    refine ⟨hpair, ?_⟩
    rw [hpair, postSectionBytes_split_at atoms idx a hget]
    exact extractByteSlice_mid
      (postSectionBytes (atoms.take idx))
      (atomPostBytes a)
      (postSectionBytes (atoms.drop (idx + 1)))
  · intro chain first last hmono
    exact sumCfaAdvanceDeltas_telescopes baseVA atoms chain first last hmono

end VerifiedRiscv64ParcelAndRelaxSeam
