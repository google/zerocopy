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

public section
namespace Anneal.ElfX86

/-!
# Total x86-64 Prefix, ModR/M, SIB, VEX, and Stream Decoder
(`Anneal.ElfX86.PrefixDecode`)

Pure Pass-1 (`0` `._unsafe_rec`, `0` `partial`, `0` `noncomputable`, `[]`
axioms) variable-length x86-64 instruction decoder over `List UInt8` and
`List PcRelReloc`:

1. **Repaired prefix scanner (`scanPrefixes`):** Tracks `segOverride`
   (`0x64 -> some .fs`, `0x65 -> some .gs`; 64-bit null prefixes `0x26`,
   `0x2E`, `0x36`, `0x3E` preserve `segOverride` while nullifying prior REX),
   `has67`, `has66`, `rep`, `hasLock`, `rex`, and `count` via `@Nat.rec`.
2. **Architectural decode-fault enforcement (`decodeOne`):**
   - Enforces the 15-byte x86-64 `#GP(0)` instruction-length limit;
   - Rejects legacy-prefixed VEX (`C4`/`C5` preceded by `0x66`, `0xF2`, `0xF3`,
     `0xF0`, or `REX`) as `#UD`;
   - Enforces `LOCK` (`0xF0`) and `REP` (`0xF2`/`0xF3`) legality across legacy
     and `0x0F` opcodes (decoding `41 90`/`49 90` as `xchgAx`, `F3 0F BC` as
     `tzcnt`, `F3 0F 1E FA` as `endbr64`, rejecting `F3 90` `PAUSE` and
     `66 E8`/`66 E9` vendor-divergent `rel16` forms);
   - Separates `opSizeOf` (`d32`) and `opSizeD64` (`d64`, `PUSH`/`POP`) with
     exact `REX.W`-over-`0x66` precedence;
   - Requires exact matching `R_X86_64_PC32` relocations for 64-bit RIP-relative
     operands, decodes `0x67` + `mod=00, r/m=101` as EIP-relative `.ripRel`
     with `addr32 = true` (rejected fail-closed in relocatable mode and SFI),
     and rejects un-relocated base-less SIB `[disp32]` in relocatable object
     mode.
3. **Structural guarantees:** `decodeOne_deterministic`, `decodeOne_len_bounds`
   (`1 ≤ len ∧ len ≤ 15`), `decodeOne_window_local`, 1-to-1 relocation
   accounting in `localDecodeCoverageOk`, and `dirtyYmmClearedBeforeRet`.
-/

/-! ## 1. Total List & Integer Helpers (`0` `._unsafe_rec`) -/

/-- Structural `List.take` via `@Nat.rec`. -/
@[expose] def listTake {α : Type} (n : Nat) (xs : List α) : List α :=
  @Nat.rec (fun _ => List α → List α)
    (fun _ => [])
    (fun _ ih ys =>
      match ys with
      | [] => []
      | y :: rest => y :: ih rest)
    n xs

/-- Structural `List.drop` via `@Nat.rec`. -/
@[expose] def listDrop {α : Type} (n : Nat) (xs : List α) : List α :=
  @Nat.rec (fun _ => List α → List α)
    (fun ys => ys)
    (fun _ ih ys =>
      match ys with
      | [] => []
      | _ :: rest => ih rest)
    n xs

/-- Structural `List` indexing via `@Nat.rec`. -/
@[expose] def listGet? {α : Type} (xs : List α) (n : Nat) : Option α :=
  @Nat.rec (fun _ => List α → Option α)
    (fun ys =>
      match ys with
      | [] => none
      | y :: _ => some y)
    (fun _ ih ys =>
      match ys with
      | [] => none
      | _ :: rest => ih rest)
    n xs

/-- Structural `List.find?` via `List.foldr`. -/
@[expose] def listFind? {α : Type} (p : α → Bool) (xs : List α) : Option α :=
  List.foldr (fun x acc => if p x then some x else acc) none xs

/-- Structural `List.all` via `List.foldr`. -/
@[expose] def listAll {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  List.foldr (fun x acc => p x && acc) true xs

/-- Structural `List.any` via `List.foldr`. -/
@[expose] def listAny {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  List.foldr (fun x acc => p x || acc) false xs

/-- Structural `List.getLast?` via `List.foldl`. -/
@[expose] def listGetLast? {α : Type} (xs : List α) : Option α :=
  List.foldl (fun _ x => some x) none xs

/-- Structural `List.countP` via `List.foldl`. -/
@[expose] def listCountP {α : Type} (p : α → Bool) (xs : List α) : Nat :=
  List.foldl (fun acc x => if p x then acc + 1 else acc) 0 xs

/-- Membership test on `List Nat`. -/
@[expose] def natListContains (xs : List Nat) (v : Nat) : Bool :=
  listAny (fun x => Nat.beq x v) xs

/-- True iff all elements of `xs : List Nat` are pairwise distinct. -/
@[expose] def natListAllDistinct (xs : List Nat) : Bool :=
  let st := List.foldr
    (fun x acc =>
      let seen := acc.1
      let ok := acc.2
      (x :: seen, ok && !natListContains seen x))
    ([], true) xs
  st.2

/-- True iff `a` and `b` represent the same finite set of distinct `Nat`s
(exact 1-to-1 bijection with zero duplicates or extras). -/
@[expose] def natListBijection (a b : List Nat) : Bool :=
  natListAllDistinct a &&
  natListAllDistinct b &&
  Nat.beq a.length b.length &&
  listAll (fun x => natListContains b x) a &&
  listAll (fun x => natListContains a x) b

/-- Sign-extend an 8-bit unsigned byte to `Int`. -/
@[expose] def sext8 (b : UInt8) : Int :=
  if Nat.blt b.toNat 128 then Int.ofNat b.toNat
  else Int.ofNat b.toNat - Int.ofNat 256

/-- Assemble 2 little-endian bytes into an unsigned `Nat`. -/
@[expose] def le16Nat (b0 b1 : UInt8) : Nat :=
  b0.toNat + 256 * b1.toNat

/-- Assemble 4 little-endian bytes into an unsigned `Nat`. -/
@[expose] def le32Nat (b0 b1 b2 b3 : UInt8) : Nat :=
  b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))

/-- Assemble 8 little-endian bytes into an unsigned `Nat`. -/
@[expose] def le64Nat (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : Nat :=
  le32Nat b0 b1 b2 b3 + 4294967296 * le32Nat b4 b5 b6 b7

/-- Sign-extend a 32-bit unsigned value to `Int`. -/
@[expose] def sext32 (n : Nat) : Int :=
  if Nat.blt n 2147483648 then Int.ofNat n
  else Int.ofNat n - Int.ofNat 4294967296

/-- Sign-extend a 64-bit unsigned value to `Int`. -/
@[expose] def sext64 (n : Nat) : Int :=
  if Nat.blt n 9223372036854775808 then Int.ofNat n
  else Int.ofNat n - Int.ofNat 18446744073709551616

/-- Exact `Int` equality test (`0` axioms). -/
@[expose] def intBeq (a b : Int) : Bool :=
  match a, b with
  | Int.ofNat x, Int.ofNat y => Nat.beq x y
  | Int.negSucc x, Int.negSucc y => Nat.beq x y
  | _, _ => false

/-! ## 2. Architectural Registers, Prefixes, and Operands -/

/-- Non-null 64-bit segment override prefixes (`0x64` FS, `0x65` GS). -/
inductive SegReg where
  | fs
  | gs

@[expose] def SegReg.beq (a b : SegReg) : Bool :=
  match a, b with
  | .fs, .fs => true
  | .gs, .gs => true
  | _, _ => false

/-- Legacy repeat prefixes (`0xF3` REPZ, `0xF2` REPNZ). -/
inductive RepPrefix where
  | none
  | repz
  | repnz

@[expose] def RepPrefix.beq (a b : RepPrefix) : Bool :=
  match a, b with
  | .none, .none => true
  | .repz, .repz => true
  | .repnz, .repnz => true
  | _, _ => false

/-- Effective scalar operand size in 64-bit mode. -/
inductive OpSize where
  | s16
  | s32
  | s64

@[expose] def OpSize.beq (a b : OpSize) : Bool :=
  match a, b with
  | .s16, .s16 => true
  | .s32, .s32 => true
  | .s64, .s64 => true
  | _, _ => false

/-- Byte width of a scalar `OpSize`. -/
@[expose] def OpSize.byteWidth (sz : OpSize) : Nat :=
  match sz with
  | .s16 => 2
  | .s32 => 4
  | .s64 => 8

/-- The 16 architectural x86-64 general-purpose registers. -/
inductive Gpr where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15

@[expose] def gprToNat (r : Gpr) : Nat :=
  match r with
  | .rax => 0  | .rcx => 1  | .rdx => 2  | .rbx => 3
  | .rsp => 4  | .rbp => 5  | .rsi => 6  | .rdi => 7
  | .r8  => 8  | .r9  => 9  | .r10 => 10 | .r11 => 11
  | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

@[expose] def gprOfNat (n : Nat) : Gpr :=
  match Nat.mod n 16 with
  | 0  => .rax | 1  => .rcx | 2  => .rdx | 3  => .rbx
  | 4  => .rsp | 5  => .rbp | 6  => .rsi | 7  => .rdi
  | 8  => .r8  | 9  => .r9  | 10 => .r10 | 11 => .r11
  | 12 => .r12 | 13 => .r13 | 14 => .r14 | _  => .r15

@[expose] def Gpr.beq (a b : Gpr) : Bool :=
  Nat.beq (gprToNat a) (gprToNat b)

/-- System V AMD64 ABI callee-saved GPRs (`rbx, rbp, r12..r15`). -/
@[expose] def Gpr.isCalleeSaved (r : Gpr) : Bool :=
  match r with
  | .rbx | .rbp | .r12 | .r13 | .r14 | .r15 => true
  | _ => false

/-- True iff `r` is the stack pointer `rsp`. -/
@[expose] def Gpr.isStackPtr (r : Gpr) : Bool :=
  match r with
  | .rsp => true
  | _ => false

/-- True iff `r` is the stack pointer `rsp` or frame pointer `rbp`. -/
@[expose] def Gpr.isStackOrFramePtr (r : Gpr) : Bool :=
  match r with
  | .rsp | .rbp => true
  | _ => false

/-- Host-protected GPRs (`rsp` plus all System V callee-saved registers). -/
@[expose] def Gpr.isHostProtected (r : Gpr) : Bool :=
  r.isStackPtr || r.isCalleeSaved

/-- Prefix state accumulated by `scanPrefixes`. -/
structure PrefixState where
  segOverride : Option SegReg := none
  has67 : Bool := false
  has66 : Bool := false
  rep : RepPrefix := .none
  hasRepConflict : Bool := false
  hasLock : Bool := false
  hasLockRepHle : Bool := false
  rex : Option UInt8 := none
  seenRex : Bool := false
  count : Nat := 0

/-- Empty initial `PrefixState`. -/
@[expose] def PrefixState.empty : PrefixState :=
  ⟨none, false, false, .none, false, false, false, none, false, 0⟩

/-- True iff `pfx` is the exact canonical single-`0xF3` mandatory-prefix set
(exactly one `0xF3` byte, no `0xF2` or duplicate `0xF3`, no `LOCK`, no `0x66`,
no `0x67`, no segment override or null segment prefix, and no `REX`). -/
@[expose] def PrefixState.isCanonicalSingleF3 (pfx : PrefixState) : Bool :=
  Nat.beq pfx.count 1 &&
  RepPrefix.beq pfx.rep .repz &&
  !pfx.hasRepConflict &&
  !pfx.hasLock &&
  !pfx.hasLockRepHle &&
  !pfx.has66 &&
  !pfx.has67 &&
  pfx.segOverride.isNone &&
  !pfx.seenRex

@[expose] def rexBit (rex : Option UInt8) (bitVal : Nat) : Bool :=
  match rex with
  | none => false
  | some b => Nat.beq (Nat.mod (Nat.div b.toNat bitVal) 2) 1

@[expose] def rexB (rex : Option UInt8) : Bool := rexBit rex 1
@[expose] def rexX (rex : Option UInt8) : Bool := rexBit rex 2
@[expose] def rexR (rex : Option UInt8) : Bool := rexBit rex 4
@[expose] def rexW (rex : Option UInt8) : Bool := rexBit rex 8

/-- Default-32-bit (`d32`) operand size: `REX.W` overrides `0x66`. -/
@[expose] def opSizeOf (pfx : PrefixState) : OpSize :=
  if rexW pfx.rex then .s64 else if pfx.has66 then .s16 else .s32

/-- Default-64-bit (`d64`) stack operand size (`PUSH`/`POP`): an active
`REX.W` immediately before the opcode overrides `0x66` to `.s64`; a `0x66`
after `REX` nullifies `REX` and selects `.s16`. -/
@[expose] def opSizeD64 (pfx : PrefixState) : OpSize :=
  if rexW pfx.rex then .s64 else if pfx.has66 then .s16 else .s64

/-- Bounded `@Nat.rec` x86-64 prefix scanner preserving `segOverride` across
64-bit null segment prefixes (`0x26`/`0x2E`/`0x36`/`0x3E`), tracking sticky
`seenRex` across subsequent legacy prefixes, flagging multiple/conflicting
Group-1 repeat prefixes (`0xF2`/`0xF3` in any combination) in `hasRepConflict`,
conservatively flagging combined `LOCK` (`0xF0`) + `F2`/`F3` (HLE
`XACQUIRE`/`XRELEASE` hints, unmodeled in this AST) for fail-closed rejection,
and resetting active `rex := none` on every legacy prefix. -/
@[expose] def scanPrefixes (fuel : Nat) (st : PrefixState)
    (bs : List UInt8) : PrefixState × List UInt8 :=
  @Nat.rec (fun _ => PrefixState → List UInt8 → PrefixState × List UInt8)
    (fun s rem => (s, rem))
    (fun _ ih s rem =>
      match rem with
      | [] => (s, [])
      | b :: rest =>
        let n := b.toNat
        if Nat.beq n 0x66 then
          ih { s with has66 := true, rex := none, count := s.count + 1 } rest
        else if Nat.beq n 0x67 then
          ih { s with has67 := true, rex := none, count := s.count + 1 } rest
        else if Nat.beq n 0xF2 then
          ih { s with rep := .repnz,
                      hasRepConflict :=
                        s.hasRepConflict || !RepPrefix.beq s.rep .none,
                      hasLockRepHle := s.hasLockRepHle || s.hasLock,
                      rex := none, count := s.count + 1 } rest
        else if Nat.beq n 0xF3 then
          ih { s with rep := .repz,
                      hasRepConflict :=
                        s.hasRepConflict || !RepPrefix.beq s.rep .none,
                      hasLockRepHle := s.hasLockRepHle || s.hasLock,
                      rex := none, count := s.count + 1 } rest
        else if Nat.beq n 0xF0 then
          ih { s with hasLock := true,
                      hasLockRepHle :=
                        s.hasLockRepHle || !RepPrefix.beq s.rep .none,
                      rex := none, count := s.count + 1 } rest
        else if Nat.beq n 0x64 then
          ih { s with segOverride := some .fs, rex := none,
                      count := s.count + 1 } rest
        else if Nat.beq n 0x65 then
          ih { s with segOverride := some .gs, rex := none,
                      count := s.count + 1 } rest
        else if Nat.beq n 0x26 || Nat.beq n 0x2E ||
                Nat.beq n 0x36 || Nat.beq n 0x3E then
          ih { s with rex := none, count := s.count + 1 } rest
        else if Nat.beq (Nat.div n 16) 4 then
          ih { s with rex := some b, seenRex := true,
                      count := s.count + 1 } rest
        else
          (s, b :: rest))
    fuel st bs

/-- Decoder mode configuration. When `requireRelocForRip = true` (relocatable
object mode), RIP-relative operands must match an `R_X86_64_PC32` relocation
with zero placeholder bytes and un-relocated base-less `[disp32]` addressing is
rejected fail-closed. `F3 0F BC` decodes as `.tzcnt` only when `bmi1 = true`
(failing closed otherwise, since non-BMI1 hardware executes it as `BSF`). -/
structure DecodeConfig where
  requireRelocForRip : Bool := true
  bmi1 : Bool := false

/-- An `R_X86_64_PC32` relocation on a `disp32` field at `.text` offset
`offset`, targeting read-only section `secIdx` with
`symValue + addend = target`. -/
structure PcRelReloc where
  offset : Nat
  secIdx : Nat
  target : Int

/-- Memory addressing operand preserving segment override, `0x67` flag, and
optional consumed relocation offset for `.ripRel`. -/
inductive MemAddr where
  | gpr (seg : Option SegReg) (addr32 : Bool) (base : Option Gpr)
      (index : Option (Gpr × Nat)) (disp : Int)
  | ripRel (seg : Option SegReg) (addr32 : Bool)
      (secIdx : Option Nat) (relocOff : Option Nat) (effOff : Int)

@[expose] def optBeq {α : Type} (eq : α → α → Bool)
    (a b : Option α) : Bool :=
  match a, b with
  | none, none => true
  | some x, some y => eq x y
  | _, _ => false

@[expose] def indexBeq (a b : Gpr × Nat) : Bool :=
  Gpr.beq a.1 b.1 && Nat.beq a.2 b.2

@[expose] def MemAddr.beq (a b : MemAddr) : Bool :=
  match a, b with
  | .gpr s1 a1 b1 i1 d1, .gpr s2 a2 b2 i2 d2 =>
    optBeq SegReg.beq s1 s2 && (a1 == a2) &&
    optBeq Gpr.beq b1 b2 && optBeq indexBeq i1 i2 && intBeq d1 d2
  | .ripRel s1 a1 sec1 ro1 o1, .ripRel s2 a2 sec2 ro2 o2 =>
    optBeq SegReg.beq s1 s2 && (a1 == a2) &&
    optBeq Nat.beq sec1 sec2 && optBeq Nat.beq ro1 ro2 && intBeq o1 o2
  | _, _ => false

/-- Vector operand (`xmm`/`ymm` register index `0..15`, or memory). -/
inductive VecOpnd where
  | reg (r : Nat)
  | mem (m : MemAddr)

@[expose] def VecOpnd.beq (a b : VecOpnd) : Bool :=
  match a, b with
  | .reg x, .reg y => Nat.beq x y
  | .mem m1, .mem m2 => MemAddr.beq m1 m2
  | _, _ => false

/-- General-purpose register or memory operand. -/
inductive GpOpnd where
  | reg (r : Gpr)
  | mem (m : MemAddr)

@[expose] def GpOpnd.beq (a b : GpOpnd) : Bool :=
  match a, b with
  | .reg x, .reg y => Gpr.beq x y
  | .mem m1, .mem m2 => MemAddr.beq m1 m2
  | _, _ => false

/-! ## 3. Decoded x86-64 & AVX/AVX2 Instruction AST -/

/-- Three-operand integer AVX/AVX2 lane operations. -/
inductive VBinOp where
  | paddd | psubd | pxor | pand | por
  | punpckldq | punpckhdq | punpcklqdq | punpckhqdq
  | psravd | psrlvd | psllvd
  | pmaxsd | pminsd
  | packusdw | packssdw
  | pmaxsw | pminsw | pminuw | paddsw

@[expose] def vbinToNat (op : VBinOp) : Nat :=
  match op with
  | .paddd => 0      | .psubd => 1      | .pxor => 2       | .pand => 3
  | .por => 4        | .punpckldq => 5  | .punpckhdq => 6  | .punpcklqdq => 7
  | .punpckhqdq => 8 | .psravd => 9     | .psrlvd => 10    | .psllvd => 11
  | .pmaxsd => 12    | .pminsd => 13    | .packusdw => 14  | .packssdw => 15
  | .pmaxsw => 16    | .pminsw => 17    | .pminuw => 18    | .paddsw => 19

@[expose] def VBinOp.beq (a b : VBinOp) : Bool :=
  Nat.beq (vbinToNat a) (vbinToNat b)

/-- Immediate-count integer AVX/AVX2 dword shifts. -/
inductive VShiftOp where
  | psrad | psrld | pslld

@[expose] def VShiftOp.beq (a b : VShiftOp) : Bool :=
  match a, b with
  | .psrad, .psrad => true
  | .psrld, .psrld => true
  | .pslld, .pslld => true
  | _, _ => false

/-- Vector memory load forms. -/
inductive VLoadKind where
  | ymm | xmm | q | sd | bcastd | bcastq | bcast128

@[expose] def vloadToNat (k : VLoadKind) : Nat :=
  match k with
  | .ymm => 0 | .xmm => 1 | .q => 2 | .sd => 3
  | .bcastd => 4 | .bcastq => 5 | .bcast128 => 6

@[expose] def VLoadKind.beq (a b : VLoadKind) : Bool :=
  Nat.beq (vloadToNat a) (vloadToNat b)

/-- Vector memory store forms. -/
inductive VStoreKind where
  | ymm | xmm | lo64 | hi64

@[expose] def vstoreToNat (k : VStoreKind) : Nat :=
  match k with
  | .ymm => 0 | .xmm => 1 | .lo64 => 2 | .hi64 => 3

@[expose] def VStoreKind.beq (a b : VStoreKind) : Bool :=
  Nat.beq (vstoreToNat a) (vstoreToNat b)

/-- Scalar GP ALU operations. -/
inductive GpAluOp where
  | add | or | adc | sbb | and | sub | xor | cmp | test

@[expose] def gpAluToNat (op : GpAluOp) : Nat :=
  match op with
  | .add => 0 | .or => 1  | .adc => 2 | .sbb => 3 | .and => 4
  | .sub => 5 | .xor => 6 | .cmp => 7 | .test => 8

@[expose] def GpAluOp.beq (a b : GpAluOp) : Bool :=
  Nat.beq (gpAluToNat a) (gpAluToNat b)

@[expose] def gpAluOfExt (ext : Nat) : Option GpAluOp :=
  match ext with
  | 0 => some .add | 1 => some .or  | 2 => some .adc | 3 => some .sbb
  | 4 => some .and | 5 => some .sub | 6 => some .xor | 7 => some .cmp
  | _ => none

/-- Scalar GP shift operations. -/
inductive GpShiftOp where
  | shl | shr | sar

@[expose] def GpShiftOp.beq (a b : GpShiftOp) : Bool :=
  match a, b with
  | .shl, .shl => true
  | .shr, .shr => true
  | .sar, .sar => true
  | _, _ => false

/-- Decoded x86-64 instruction AST spanning AVX/AVX2 DSP kernels, scalar GP
ALU/stack/prefix instructions, CET `endbr64`, and explicit trap/control-flow
markers for SFI rejection. -/
inductive DecodedInsn where
  | vbin (op : VBinOp) (is256 : Bool) (dst src1 : Nat) (src2 : VecOpnd)
  | vshift (op : VShiftOp) (is256 : Bool) (dst src : Nat) (imm : Nat)
  | vload (kind : VLoadKind) (aligned : Bool) (dst : Nat) (m : MemAddr)
  | vmovhps (dst src1 : Nat) (m : MemAddr)
  | vstore (kind : VStoreKind) (aligned : Bool) (m : MemAddr) (src : Nat)
  | vpmovzxwd (is256 : Bool) (dst : Nat) (src : VecOpnd)
  | vperm2i128 (dst src1 : Nat) (src2 : VecOpnd) (imm : Nat)
  | vinserti128 (dst src1 : Nat) (src2 : VecOpnd) (imm : Nat)
  | vextracti128 (dst src : Nat) (imm : Nat)
  | vpermq (dst : Nat) (src : VecOpnd) (imm : Nat)
  | vpshufd (is256 : Bool) (dst : Nat) (src : VecOpnd) (imm : Nat)
  | vpblendd (is256 : Bool) (dst src1 : Nat) (src2 : VecOpnd) (imm : Nat)
  | vzeroupper
  | lea (sz : OpSize) (dst : Gpr) (m : MemAddr)
  | movsxd (dst : Gpr) (src : GpOpnd)
  | movRegRm (sz : OpSize) (dst : Gpr) (src : GpOpnd)
  | movRmReg (sz : OpSize) (dst : GpOpnd) (src : Gpr)
  | movImm (sz : OpSize) (dst : Gpr) (imm : Nat)
  | aluRmReg (sz : OpSize) (locked : Bool) (op : GpAluOp)
      (dst : GpOpnd) (src : Gpr)
  | aluRegRm (sz : OpSize) (op : GpAluOp) (dst : Gpr) (src : GpOpnd)
  | aluRmImm (sz : OpSize) (locked : Bool) (op : GpAluOp)
      (dst : GpOpnd) (imm : Int)
  | shiftRmImm (sz : OpSize) (op : GpShiftOp) (dst : GpOpnd) (cnt : Nat)
  | imulRegRm (sz : OpSize) (dst : Gpr) (src : GpOpnd)
  | bsf (sz : OpSize) (dst : Gpr) (src : GpOpnd)
  | tzcnt (sz : OpSize) (dst : Gpr) (src : GpOpnd)
  | xchgAx (sz : OpSize) (dst : Gpr)
  | pushReg (sz : OpSize) (src : Gpr)
  | popReg (sz : OpSize) (dst : Gpr)
  | endbr64
  | nop
  | ret
  | syscall
  | sysenter
  | intImm (vec : Nat)
  | int3
  | ud2
  | jmpRel (disp : Int)
  | callRel (disp : Int)
  | jmpInd (target : GpOpnd)
  | callInd (target : GpOpnd)

@[expose] def DecodedInsn.beq (a b : DecodedInsn) : Bool :=
  match a, b with
  | .vbin o1 l1 d1 s1 x1, .vbin o2 l2 d2 s2 x2 =>
    VBinOp.beq o1 o2 && (l1 == l2) && Nat.beq d1 d2 &&
    Nat.beq s1 s2 && VecOpnd.beq x1 x2
  | .vshift o1 l1 d1 s1 i1, .vshift o2 l2 d2 s2 i2 =>
    VShiftOp.beq o1 o2 && (l1 == l2) && Nat.beq d1 d2 &&
    Nat.beq s1 s2 && Nat.beq i1 i2
  | .vload k1 a1 d1 m1, .vload k2 a2 d2 m2 =>
    VLoadKind.beq k1 k2 && (a1 == a2) && Nat.beq d1 d2 && MemAddr.beq m1 m2
  | .vmovhps d1 s1 m1, .vmovhps d2 s2 m2 =>
    Nat.beq d1 d2 && Nat.beq s1 s2 && MemAddr.beq m1 m2
  | .vstore k1 a1 m1 s1, .vstore k2 a2 m2 s2 =>
    VStoreKind.beq k1 k2 && (a1 == a2) && MemAddr.beq m1 m2 && Nat.beq s1 s2
  | .vpmovzxwd l1 d1 x1, .vpmovzxwd l2 d2 x2 =>
    (l1 == l2) && Nat.beq d1 d2 && VecOpnd.beq x1 x2
  | .vperm2i128 d1 s1 x1 i1, .vperm2i128 d2 s2 x2 i2 =>
    Nat.beq d1 d2 && Nat.beq s1 s2 && VecOpnd.beq x1 x2 && Nat.beq i1 i2
  | .vinserti128 d1 s1 x1 i1, .vinserti128 d2 s2 x2 i2 =>
    Nat.beq d1 d2 && Nat.beq s1 s2 && VecOpnd.beq x1 x2 && Nat.beq i1 i2
  | .vextracti128 d1 s1 i1, .vextracti128 d2 s2 i2 =>
    Nat.beq d1 d2 && Nat.beq s1 s2 && Nat.beq i1 i2
  | .vpermq d1 x1 i1, .vpermq d2 x2 i2 =>
    Nat.beq d1 d2 && VecOpnd.beq x1 x2 && Nat.beq i1 i2
  | .vpshufd l1 d1 x1 i1, .vpshufd l2 d2 x2 i2 =>
    (l1 == l2) && Nat.beq d1 d2 && VecOpnd.beq x1 x2 && Nat.beq i1 i2
  | .vpblendd l1 d1 s1 x1 i1, .vpblendd l2 d2 s2 x2 i2 =>
    (l1 == l2) && Nat.beq d1 d2 && Nat.beq s1 s2 &&
    VecOpnd.beq x1 x2 && Nat.beq i1 i2
  | .vzeroupper, .vzeroupper => true
  | .lea z1 d1 m1, .lea z2 d2 m2 =>
    OpSize.beq z1 z2 && Gpr.beq d1 d2 && MemAddr.beq m1 m2
  | .movsxd d1 s1, .movsxd d2 s2 => Gpr.beq d1 d2 && GpOpnd.beq s1 s2
  | .movRegRm z1 d1 s1, .movRegRm z2 d2 s2 =>
    OpSize.beq z1 z2 && Gpr.beq d1 d2 && GpOpnd.beq s1 s2
  | .movRmReg z1 d1 s1, .movRmReg z2 d2 s2 =>
    OpSize.beq z1 z2 && GpOpnd.beq d1 d2 && Gpr.beq s1 s2
  | .movImm z1 d1 i1, .movImm z2 d2 i2 =>
    OpSize.beq z1 z2 && Gpr.beq d1 d2 && Nat.beq i1 i2
  | .aluRmReg z1 lk1 o1 d1 s1, .aluRmReg z2 lk2 o2 d2 s2 =>
    OpSize.beq z1 z2 && (lk1 == lk2) && GpAluOp.beq o1 o2 &&
    GpOpnd.beq d1 d2 && Gpr.beq s1 s2
  | .aluRegRm z1 o1 d1 s1, .aluRegRm z2 o2 d2 s2 =>
    OpSize.beq z1 z2 && GpAluOp.beq o1 o2 && Gpr.beq d1 d2 && GpOpnd.beq s1 s2
  | .aluRmImm z1 lk1 o1 d1 i1, .aluRmImm z2 lk2 o2 d2 i2 =>
    OpSize.beq z1 z2 && (lk1 == lk2) && GpAluOp.beq o1 o2 &&
    GpOpnd.beq d1 d2 && intBeq i1 i2
  | .shiftRmImm z1 o1 d1 c1, .shiftRmImm z2 o2 d2 c2 =>
    OpSize.beq z1 z2 && GpShiftOp.beq o1 o2 && GpOpnd.beq d1 d2 && Nat.beq c1 c2
  | .imulRegRm z1 d1 s1, .imulRegRm z2 d2 s2 =>
    OpSize.beq z1 z2 && Gpr.beq d1 d2 && GpOpnd.beq s1 s2
  | .bsf z1 d1 s1, .bsf z2 d2 s2 =>
    OpSize.beq z1 z2 && Gpr.beq d1 d2 && GpOpnd.beq s1 s2
  | .tzcnt z1 d1 s1, .tzcnt z2 d2 s2 =>
    OpSize.beq z1 z2 && Gpr.beq d1 d2 && GpOpnd.beq s1 s2
  | .xchgAx z1 d1, .xchgAx z2 d2 => OpSize.beq z1 z2 && Gpr.beq d1 d2
  | .pushReg z1 s1, .pushReg z2 s2 => OpSize.beq z1 z2 && Gpr.beq s1 s2
  | .popReg z1 d1, .popReg z2 d2 => OpSize.beq z1 z2 && Gpr.beq d1 d2
  | .endbr64, .endbr64 => true
  | .nop, .nop => true
  | .ret, .ret => true
  | .syscall, .syscall => true
  | .sysenter, .sysenter => true
  | .intImm v1, .intImm v2 => Nat.beq v1 v2
  | .int3, .int3 => true
  | .ud2, .ud2 => true
  | .jmpRel d1, .jmpRel d2 => intBeq d1 d2
  | .callRel d1, .callRel d2 => intBeq d1 d2
  | .jmpInd t1, .jmpInd t2 => GpOpnd.beq t1 t2
  | .callInd t1, .callInd t2 => GpOpnd.beq t1 t2
  | _, _ => false

/-- Optional memory operand and exact byte access width of `ins`. -/
@[expose] def insnMemOperandWithSize? (ins : DecodedInsn) :
    Option (MemAddr × Nat) :=
  match ins with
  | .vbin _ is256 _ _ (.mem m) => some (m, if is256 then 32 else 16)
  | .vload k _ _ m =>
    let w := match k with
      | .ymm => 32 | .xmm => 16 | .q => 8 | .sd => 8
      | .bcastd => 4 | .bcastq => 8 | .bcast128 => 16
    some (m, w)
  | .vmovhps _ _ m => some (m, 8)
  | .vstore k _ m _ =>
    let w := match k with
      | .ymm => 32 | .xmm => 16 | .lo64 => 8 | .hi64 => 8
    some (m, w)
  | .vpmovzxwd is256 _ (.mem m) => some (m, if is256 then 16 else 8)
  | .vperm2i128 _ _ (.mem m) _ => some (m, 32)
  | .vinserti128 _ _ (.mem m) _ => some (m, 16)
  | .vpermq _ (.mem m) _ => some (m, 32)
  | .vpshufd is256 _ (.mem m) _ => some (m, if is256 then 32 else 16)
  | .vpblendd is256 _ _ (.mem m) _ => some (m, if is256 then 32 else 16)
  | .lea sz _ m => some (m, sz.byteWidth)
  | .movsxd _ (.mem m) => some (m, 4)
  | .movRegRm sz _ (.mem m) => some (m, sz.byteWidth)
  | .movRmReg sz (.mem m) _ => some (m, sz.byteWidth)
  | .aluRmReg sz _ _ (.mem m) _ => some (m, sz.byteWidth)
  | .aluRegRm sz _ _ (.mem m) => some (m, sz.byteWidth)
  | .aluRmImm sz _ _ (.mem m) _ => some (m, sz.byteWidth)
  | .shiftRmImm sz _ (.mem m) _ => some (m, sz.byteWidth)
  | .imulRegRm sz _ (.mem m) => some (m, sz.byteWidth)
  | .bsf sz _ (.mem m) => some (m, sz.byteWidth)
  | .tzcnt sz _ (.mem m) => some (m, sz.byteWidth)
  | .jmpInd (.mem m) => some (m, 8)
  | .callInd (.mem m) => some (m, 8)
  | _ => none

/-- Relocation offset consumed by `ins`, if `ins` has a relocated `.ripRel`
operand. -/
@[expose] def insnConsumedRelocOff? (ins : DecodedInsn) : Option Nat :=
  match insnMemOperandWithSize? ins with
  | some (.ripRel _ _ _ relocOff _, _) => relocOff
  | _ => none

/-- Collect all relocation offsets consumed by a decoded trace. -/
@[expose] def consumedRelocOffsets
    (trace : List (Nat × Nat × DecodedInsn)) : List Nat :=
  List.foldr
    (fun entry acc =>
      match insnConsumedRelocOff? entry.2.2 with
      | some off => off :: acc
      | none => acc)
    [] trace

/-! ## 4. ModR/M + SIB + Displacement & Relocation Resolution -/

/-- Raw ModR/M decoded result before RIP relocation resolution. -/
inductive RawRm where
  | reg (idx : Nat)
  | mem (m : MemAddr)
  | rip (seg : Option SegReg) (addr32 : Bool)
      (dispPos : Nat) (dispRaw : Nat) (dispVal : Int)

/-- Parse ModR/M (+ optional SIB + disp8/disp32) at `.text` byte offset
`modrmPos`, attaching `seg` and `addr32` to every memory operand. Returns
`(regIdx, rawRm, bytesConsumed, remainingBytes)`. -/
@[expose] def parseModRm (modrmPos : Nat) (seg : Option SegReg)
    (addr32 rBit xBit bBit : Bool) (bs : List UInt8) :
    Option (Nat × RawRm × Nat × List UInt8) :=
  match bs with
  | [] => none
  | m :: rest =>
    let mn := m.toNat
    let md := Nat.div mn 64
    let reg3 := Nat.mod (Nat.div mn 8) 8
    let rm3 := Nat.mod mn 8
    let regIdx := reg3 + (if rBit then 8 else 0)
    let rmIdx := rm3 + (if bBit then 8 else 0)
    if Nat.beq md 3 then
      some (regIdx, .reg rmIdx, 1, rest)
    else if Nat.beq rm3 4 then
      match rest with
      | [] => none
      | s :: restSib =>
        let sn := s.toNat
        let sc := Nat.div sn 64
        let ix3 := Nat.mod (Nat.div sn 8) 8
        let bs3 := Nat.mod sn 8
        let ixFull := ix3 + (if xBit then 8 else 0)
        let bsFull := bs3 + (if bBit then 8 else 0)
        let idxOpt : Option (Gpr × Nat) :=
          if Nat.beq ixFull 4 then none
          else some (gprOfNat ixFull, Nat.pow 2 sc)
        if Nat.beq md 0 && Nat.beq bs3 5 then
          match restSib with
          | d0 :: d1 :: d2 :: d3 :: restD =>
            let disp := sext32 (le32Nat d0 d1 d2 d3)
            some (regIdx, .mem (.gpr seg addr32 none idxOpt disp), 6, restD)
          | _ => none
        else if Nat.beq md 0 then
          some (regIdx,
            .mem (.gpr seg addr32 (some (gprOfNat bsFull)) idxOpt 0),
            2, restSib)
        else if Nat.beq md 1 then
          match restSib with
          | d8 :: restD =>
            some (regIdx,
              .mem (.gpr seg addr32 (some (gprOfNat bsFull)) idxOpt (sext8 d8)),
              3, restD)
          | [] => none
        else
          match restSib with
          | d0 :: d1 :: d2 :: d3 :: restD =>
            let disp := sext32 (le32Nat d0 d1 d2 d3)
            some (regIdx,
              .mem (.gpr seg addr32 (some (gprOfNat bsFull)) idxOpt disp),
              6, restD)
          | _ => none
    else if Nat.beq md 0 && Nat.beq rm3 5 then
      match rest with
      | d0 :: d1 :: d2 :: d3 :: restD =>
        let raw := le32Nat d0 d1 d2 d3
        some (regIdx, .rip seg addr32 (modrmPos + 1) raw (sext32 raw),
          5, restD)
      | _ => none
    else if Nat.beq md 0 then
      some (regIdx,
        .mem (.gpr seg addr32 (some (gprOfNat rmIdx)) none 0), 1, rest)
    else if Nat.beq md 1 then
      match rest with
      | d8 :: restD =>
        some (regIdx,
          .mem (.gpr seg addr32 (some (gprOfNat rmIdx)) none (sext8 d8)),
          2, restD)
      | [] => none
    else
      match rest with
      | d0 :: d1 :: d2 :: d3 :: restD =>
        let disp := sext32 (le32Nat d0 d1 d2 d3)
        some (regIdx,
          .mem (.gpr seg addr32 (some (gprOfNat rmIdx)) none disp), 5, restD)
      | _ => none

/-- Resolve a `RawRm` memory operand. When `cfg.requireRelocForRip = true`,
64-bit RIP-relative addressing requires `seg = none` (rejecting active
`FS:`/`GS:` segment overrides), `addr32 = false` (rejecting `0x67`
EIP-relative), an exact matching `R_X86_64_PC32` relocation with zero
placeholder `disp32`, and rejects un-relocated base-less SIB `[disp32]`
addressing fail-closed. -/
@[expose] def resolveMemAddr (cfg : DecodeConfig) (relocs : List PcRelReloc)
    (insnEnd : Nat) (rm : RawRm) : Option MemAddr :=
  match rm with
  | .reg _ => none
  | .mem m =>
    if cfg.requireRelocForRip then
      match m with
      | .gpr _ _ none _ _ => none
      | _ => some m
    else some m
  | .rip seg addr32 dispPos dispRaw dispVal =>
    if cfg.requireRelocForRip then
      if seg.isSome || addr32 || !Nat.beq dispRaw 0 then none
      else
        match listFind? (fun r => Nat.beq r.offset dispPos) relocs with
        | none => none
        | some r =>
          let eff := r.target + (Int.ofNat insnEnd - Int.ofNat dispPos)
          some (.ripRel none false (some r.secIdx) (some dispPos) eff)
    else
      match listFind? (fun r => Nat.beq r.offset dispPos) relocs with
      | some r =>
        let eff := r.target + (Int.ofNat insnEnd - Int.ofNat dispPos)
        some (.ripRel seg addr32 (some r.secIdx) (some dispPos) eff)
      | none => some (.ripRel seg addr32 none none dispVal)

@[expose] def resolveVecOpnd (cfg : DecodeConfig) (relocs : List PcRelReloc)
    (insnEnd : Nat) (rm : RawRm) : Option VecOpnd :=
  match rm with
  | .reg r => some (.reg r)
  | _ =>
    match resolveMemAddr cfg relocs insnEnd rm with
    | some m => some (.mem m)
    | none => none

@[expose] def resolveGpOpnd (cfg : DecodeConfig) (relocs : List PcRelReloc)
    (insnEnd : Nat) (rm : RawRm) : Option GpOpnd :=
  match rm with
  | .reg r => some (.reg (gprOfNat r))
  | _ =>
    match resolveMemAddr cfg relocs insnEnd rm with
    | some m => some (.mem m)
    | none => none

/-! ## 5. VEX (`C4`/`C5`) and Legacy/REX Instruction Decoding -/

/-- Decoded VEX prefix fields (extension bits R/X/B and vvvv un-inverted). -/
structure VexFields where
  mapSel : Nat
  pp : Nat
  is256 : Bool
  wBit : Bool
  vvvv : Nat
  rBit : Bool
  xBit : Bool
  bBit : Bool

/-- Decode a VEX-prefixed instruction body starting at the opcode byte. -/
@[expose] def decodeVexBody (cfg : DecodeConfig) (relocs : List PcRelReloc)
    (seg : Option SegReg) (addr32 : Bool) (v : VexFields)
    (insnPos baseLen : Nat) (rest : List UInt8) :
    Option (DecodedInsn × Nat) :=
  match rest with
  | [] => none
  | opc :: afterOpc =>
    let o := opc.toNat
    if Nat.beq v.mapSel 1 && Nat.beq o 0x77 then
      if Nat.beq v.pp 0 && !v.is256 && Nat.beq v.vvvv 0 && !v.wBit &&
         seg.isNone && !addr32 then
        some (.vzeroupper, baseLen + 1)
      else none
    else
      match parseModRm (insnPos + baseLen + 1) seg addr32
          v.rBit v.xBit v.bBit afterOpc with
      | none => none
      | some (regIdx, rm, mlen, postMrm) =>
        let len0 := baseLen + 1 + mlen
        let len1 := len0 + 1
        let reg3 := Nat.mod regIdx 8
        let mkVBin (op : VBinOp) : Option (DecodedInsn × Nat) :=
          match resolveVecOpnd cfg relocs (insnPos + len0) rm with
          | some s => some (.vbin op v.is256 regIdx v.vvvv s, len0)
          | none => none
        if Nat.beq v.mapSel 1 then
          if Nat.beq v.pp 1 then
            if Nat.beq o 0xFE then mkVBin .paddd
            else if Nat.beq o 0xFA then mkVBin .psubd
            else if Nat.beq o 0xEF then mkVBin .pxor
            else if Nat.beq o 0xDB then mkVBin .pand
            else if Nat.beq o 0xEB then mkVBin .por
            else if Nat.beq o 0x62 then mkVBin .punpckldq
            else if Nat.beq o 0x6A then mkVBin .punpckhdq
            else if Nat.beq o 0x6C then mkVBin .punpcklqdq
            else if Nat.beq o 0x6D then mkVBin .punpckhqdq
            else if Nat.beq o 0x6B then mkVBin .packssdw
            else if Nat.beq o 0xEE then mkVBin .pmaxsw
            else if Nat.beq o 0xEA then mkVBin .pminsw
            else if Nat.beq o 0xED then mkVBin .paddsw
            else if Nat.beq o 0x72 then
              if seg.isSome || addr32 then none
              else match rm, postMrm with
              | .reg r, immB :: _ =>
                if Nat.beq reg3 4 then
                  some (.vshift .psrad v.is256 v.vvvv r immB.toNat, len1)
                else if Nat.beq reg3 2 then
                  some (.vshift .psrld v.is256 v.vvvv r immB.toNat, len1)
                else if Nat.beq reg3 6 then
                  some (.vshift .pslld v.is256 v.vvvv r immB.toNat, len1)
                else none
              | _, _ => none
            else if Nat.beq o 0x70 then
              if !Nat.beq v.vvvv 0 then none
              else match postMrm with
                | immB :: _ =>
                  match resolveVecOpnd cfg relocs (insnPos + len1) rm with
                  | some s => some (.vpshufd v.is256 regIdx s immB.toNat, len1)
                  | none => none
                | [] => none
            else if Nat.beq o 0x6F then
              if !Nat.beq v.vvvv 0 then none
              else match resolveMemAddr cfg relocs (insnPos + len0) rm with
                | some m =>
                  some (.vload (if v.is256 then .ymm else .xmm) true regIdx m,
                        len0)
                | none => none
            else if Nat.beq o 0x7F then
              if !Nat.beq v.vvvv 0 then none
              else match resolveMemAddr cfg relocs (insnPos + len0) rm with
                | some m =>
                  some (.vstore (if v.is256 then .ymm else .xmm) true m regIdx,
                        len0)
                | none => none
            else if Nat.beq o 0xD6 then
              if !Nat.beq v.vvvv 0 || v.is256 then none
              else match resolveMemAddr cfg relocs (insnPos + len0) rm with
                | some m => some (.vstore .lo64 false m regIdx, len0)
                | none => none
            else none
          else if Nat.beq v.pp 2 then
            if Nat.beq o 0x6F then
              if !Nat.beq v.vvvv 0 then none
              else match resolveMemAddr cfg relocs (insnPos + len0) rm with
                | some m =>
                  some (.vload (if v.is256 then .ymm else .xmm) false regIdx m,
                        len0)
                | none => none
            else if Nat.beq o 0x7F then
              if !Nat.beq v.vvvv 0 then none
              else match resolveMemAddr cfg relocs (insnPos + len0) rm with
                | some m =>
                  some (.vstore (if v.is256 then .ymm else .xmm) false m regIdx,
                        len0)
                | none => none
            else if Nat.beq o 0x7E then
              if !Nat.beq v.vvvv 0 || v.is256 then none
              else match resolveMemAddr cfg relocs (insnPos + len0) rm with
                | some m => some (.vload .q false regIdx m, len0)
                | none => none
            else none
          else if Nat.beq v.pp 3 then
            if Nat.beq o 0x10 then
              if !Nat.beq v.vvvv 0 || v.is256 then none
              else match resolveMemAddr cfg relocs (insnPos + len0) rm with
                | some m => some (.vload .sd false regIdx m, len0)
                | none => none
            else none
          else if Nat.beq v.pp 0 then
            if Nat.beq o 0x16 then
              if v.is256 then none
              else match resolveMemAddr cfg relocs (insnPos + len0) rm with
                | some m => some (.vmovhps regIdx v.vvvv m, len0)
                | none => none
            else if Nat.beq o 0x17 then
              if v.is256 || !Nat.beq v.vvvv 0 then none
              else match resolveMemAddr cfg relocs (insnPos + len0) rm with
                | some m => some (.vstore .hi64 false m regIdx, len0)
                | none => none
            else none
          else none
        else if Nat.beq v.mapSel 2 && Nat.beq v.pp 1 then
          if Nat.beq o 0x46 && !v.wBit then mkVBin .psravd
          else if Nat.beq o 0x45 && !v.wBit then mkVBin .psrlvd
          else if Nat.beq o 0x47 && !v.wBit then mkVBin .psllvd
          else if Nat.beq o 0x3D then mkVBin .pmaxsd
          else if Nat.beq o 0x39 then mkVBin .pminsd
          else if Nat.beq o 0x2B then mkVBin .packusdw
          else if Nat.beq o 0x3A then mkVBin .pminuw
          else if Nat.beq o 0x33 then
            if !Nat.beq v.vvvv 0 then none
            else match resolveVecOpnd cfg relocs (insnPos + len0) rm with
              | some s => some (.vpmovzxwd v.is256 regIdx s, len0)
              | none => none
          else if Nat.beq o 0x58 && !v.wBit && v.is256 then
            if !Nat.beq v.vvvv 0 then none
            else match resolveMemAddr cfg relocs (insnPos + len0) rm with
              | some m => some (.vload .bcastd false regIdx m, len0)
              | none => none
          else if Nat.beq o 0x59 && !v.wBit && v.is256 then
            if !Nat.beq v.vvvv 0 then none
            else match resolveMemAddr cfg relocs (insnPos + len0) rm with
              | some m => some (.vload .bcastq false regIdx m, len0)
              | none => none
          else if Nat.beq o 0x5A && !v.wBit && v.is256 then
            if !Nat.beq v.vvvv 0 then none
            else match resolveMemAddr cfg relocs (insnPos + len0) rm with
              | some m => some (.vload .bcast128 false regIdx m, len0)
              | none => none
          else none
        else if Nat.beq v.mapSel 3 && Nat.beq v.pp 1 then
          match postMrm with
          | [] => none
          | immB :: _ =>
            let imm := immB.toNat
            if Nat.beq o 0x46 && v.is256 && !v.wBit then
              match resolveVecOpnd cfg relocs (insnPos + len1) rm with
              | some s => some (.vperm2i128 regIdx v.vvvv s imm, len1)
              | none => none
            else if Nat.beq o 0x38 && v.is256 && !v.wBit then
              match resolveVecOpnd cfg relocs (insnPos + len1) rm with
              | some s => some (.vinserti128 regIdx v.vvvv s imm, len1)
              | none => none
            else if Nat.beq o 0x39 && v.is256 && !v.wBit then
              if !Nat.beq v.vvvv 0 || seg.isSome || addr32 then none
              else match rm with
                | .reg r => some (.vextracti128 r regIdx imm, len1)
                | _ => none
            else if Nat.beq o 0x00 && v.is256 && v.wBit then
              if !Nat.beq v.vvvv 0 then none
              else match resolveVecOpnd cfg relocs (insnPos + len1) rm with
                | some s => some (.vpermq regIdx s imm, len1)
                | none => none
            else if Nat.beq o 0x02 && !v.wBit then
              match resolveVecOpnd cfg relocs (insnPos + len1) rm with
              | some s => some (.vpblendd v.is256 regIdx v.vvvv s imm, len1)
              | none => none
            else none
        else none

/-- Decode a two-byte `0x0F` escape instruction, enforcing `LOCK` and `REP`
prefix legality on every opcode, and requiring the exact canonical single-`F3`
prefix set (`isCanonicalSingleF3`) on mandatory-prefix encodings (`F3 0F 1E FA`
`endbr64` and `bmi1`-gated `F3 0F BC` `tzcnt`). -/
@[expose] def decodeEsc0F (cfg : DecodeConfig) (relocs : List PcRelReloc)
    (pfx : PrefixState) (insnPos : Nat) (after0F : List UInt8) :
    Option (DecodedInsn × Nat) :=
  match after0F with
  | [] => none
  | opc2 :: rest2 =>
    let o2 := opc2.toNat
    if pfx.hasLock || pfx.hasRepConflict then none
    else if Nat.beq o2 0x1E then
      match rest2 with
      | b3 :: _ =>
        if Nat.beq b3.toNat 0xFA && pfx.isCanonicalSingleF3 then
          some (.endbr64, pfx.count + 3)
        else none
      | [] => none
    else if Nat.beq o2 0x05 then
      if RepPrefix.beq pfx.rep .none && pfx.segOverride.isNone && !pfx.has67
      then some (.syscall, pfx.count + 2)
      else none
    else if Nat.beq o2 0x34 then
      if RepPrefix.beq pfx.rep .none && pfx.segOverride.isNone && !pfx.has67
      then some (.sysenter, pfx.count + 2)
      else none
    else if Nat.beq o2 0x0B then
      if RepPrefix.beq pfx.rep .none && pfx.segOverride.isNone && !pfx.has67
      then some (.ud2, pfx.count + 2)
      else none
    else
      let rBit := rexR pfx.rex
      let xBit := rexX pfx.rex
      let bBit := rexB pfx.rex
      let sz := opSizeOf pfx
      match parseModRm (insnPos + pfx.count + 2) pfx.segOverride pfx.has67
          rBit xBit bBit rest2 with
      | none => none
      | some (regIdx, rm, mlen, _) =>
        let len2 := pfx.count + 2 + mlen
        let dstG := gprOfNat regIdx
        if Nat.beq o2 0x1F && Nat.beq (Nat.mod regIdx 8) 0 then
          if RepPrefix.beq pfx.rep .none && pfx.segOverride.isNone &&
             !pfx.has67 then
            some (.nop, len2)
          else none
        else if Nat.beq o2 0xAF then
          if !RepPrefix.beq pfx.rep .none then none
          else match resolveGpOpnd cfg relocs (insnPos + len2) rm with
            | some s => some (.imulRegRm sz dstG s, len2)
            | none => none
        else if Nat.beq o2 0xBC then
          if RepPrefix.beq pfx.rep .none then
            match resolveGpOpnd cfg relocs (insnPos + len2) rm with
            | some s => some (.bsf sz dstG s, len2)
            | none => none
          else if pfx.isCanonicalSingleF3 && cfg.bmi1 then
            match resolveGpOpnd cfg relocs (insnPos + len2) rm with
            | some s => some (.tzcnt sz dstG s, len2)
            | none => none
          else none
        else none

/-- Decode one legacy/REX or VEX instruction before applying the 15-byte
`#GP(0)` cap. Rejects conflicting Group-1 prefixes (`LOCK`+`F2`/`F3` and
multiple `F2`/`F3`), non-mandatory `F2`/`F3` prefixes on all 1-byte opcodes,
and ignored `FS:`/`GS:`/`0x67` prefixes on non-memory control/NOP opcodes. -/
@[expose] def decodeOneRaw (cfg : DecodeConfig) (relocs : List PcRelReloc)
    (insnPos : Nat) (window : List UInt8) : Option (DecodedInsn × Nat) :=
  let (pfx, rem) := scanPrefixes 16 PrefixState.empty window
  if Nat.ble 16 pfx.count || pfx.hasLockRepHle || pfx.hasRepConflict then none
  else
    match rem with
    | [] => none
    | opc :: afterOpc =>
      let o := opc.toNat
      if Nat.beq o 0xC5 then
        if pfx.hasLock || pfx.has66 || !RepPrefix.beq pfx.rep .none ||
           pfx.seenRex then none
        else match afterOpc with
          | b1 :: rest =>
            let x := b1.toNat
            let v : VexFields := {
              mapSel := 1
              pp := Nat.mod x 4
              is256 := Nat.beq (Nat.mod (Nat.div x 4) 2) 1
              wBit := false
              vvvv := 15 - Nat.mod (Nat.div x 8) 16
              rBit := Nat.beq (Nat.div x 128) 0
              xBit := false
              bBit := false
            }
            decodeVexBody cfg relocs pfx.segOverride pfx.has67 v
              insnPos (pfx.count + 2) rest
          | [] => none
      else if Nat.beq o 0xC4 then
        if pfx.hasLock || pfx.has66 || !RepPrefix.beq pfx.rep .none ||
           pfx.seenRex then none
        else match afterOpc with
          | b1 :: b2 :: rest =>
            let x := b1.toNat
            let y := b2.toNat
            let v : VexFields := {
              mapSel := Nat.mod x 32
              pp := Nat.mod y 4
              is256 := Nat.beq (Nat.mod (Nat.div y 4) 2) 1
              wBit := Nat.beq (Nat.div y 128) 1
              vvvv := 15 - Nat.mod (Nat.div y 8) 16
              rBit := Nat.beq (Nat.div x 128) 0
              xBit := Nat.beq (Nat.mod (Nat.div x 64) 2) 0
              bBit := Nat.beq (Nat.mod (Nat.div x 32) 2) 0
            }
            decodeVexBody cfg relocs pfx.segOverride pfx.has67 v
              insnPos (pfx.count + 3) rest
          | _ => none
      else if Nat.beq o 0x0F then
        decodeEsc0F cfg relocs pfx insnPos afterOpc
      else if !RepPrefix.beq pfx.rep .none then none
      else
        let rBit := rexR pfx.rex
        let xBit := rexX pfx.rex
        let bBit := rexB pfx.rex
        let sz := opSizeOf pfx
        let szD64 := opSizeD64 pfx
        let noSegA32 := pfx.segOverride.isNone && !pfx.has67
        if Nat.beq o 0xC3 then
          if pfx.hasLock || pfx.has66 || !noSegA32 then none
          else some (.ret, pfx.count + 1)
        else if Nat.beq o 0x90 then
          if pfx.hasLock || !noSegA32 then none
          else if bBit then some (.xchgAx sz (gprOfNat 8), pfx.count + 1)
          else some (.nop, pfx.count + 1)
        else if Nat.beq o 0xCC then
          if pfx.hasLock || !noSegA32 then none
          else some (.int3, pfx.count + 1)
        else if Nat.beq o 0xCD then
          if pfx.hasLock || !noSegA32 then none
          else match afterOpc with
            | immB :: _ => some (.intImm immB.toNat, pfx.count + 2)
            | [] => none
        else if Nat.ble 0x50 o && Nat.ble o 0x57 then
          if pfx.hasLock then none
          else
            let reg := gprOfNat ((o - 0x50) + (if bBit then 8 else 0))
            some (.pushReg szD64 reg, pfx.count + 1)
        else if Nat.ble 0x58 o && Nat.ble o 0x5F then
          if pfx.hasLock then none
          else
            let reg := gprOfNat ((o - 0x58) + (if bBit then 8 else 0))
            some (.popReg szD64 reg, pfx.count + 1)
        else if Nat.ble 0xB8 o && Nat.ble o 0xBF then
          if pfx.hasLock || !noSegA32 then none
          else
            let dst := gprOfNat ((o - 0xB8) + (if bBit then 8 else 0))
            if rexW pfx.rex then
              match afterOpc with
              | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ =>
                some (.movImm .s64 dst (le64Nat b0 b1 b2 b3 b4 b5 b6 b7),
                      pfx.count + 9)
              | _ => none
            else if pfx.has66 then
              match afterOpc with
              | b0 :: b1 :: _ =>
                some (.movImm .s16 dst (le16Nat b0 b1), pfx.count + 3)
              | _ => none
            else
              match afterOpc with
              | b0 :: b1 :: b2 :: b3 :: _ =>
                some (.movImm .s32 dst (le32Nat b0 b1 b2 b3), pfx.count + 5)
              | _ => none
        else if Nat.beq o 0xEB then
          if pfx.hasLock || pfx.has66 || !noSegA32 then none
          else match afterOpc with
            | d8 :: _ => some (.jmpRel (sext8 d8), pfx.count + 2)
            | [] => none
        else if Nat.beq o 0xE9 then
          if pfx.hasLock || pfx.has66 || !noSegA32 then none
          else match afterOpc with
            | b0 :: b1 :: b2 :: b3 :: _ =>
              some (.jmpRel (sext32 (le32Nat b0 b1 b2 b3)), pfx.count + 5)
            | _ => none
        else if Nat.beq o 0xE8 then
          if pfx.hasLock || pfx.has66 || !noSegA32 then none
          else match afterOpc with
            | b0 :: b1 :: b2 :: b3 :: _ =>
              some (.callRel (sext32 (le32Nat b0 b1 b2 b3)), pfx.count + 5)
            | _ => none
        else
          match parseModRm (insnPos + pfx.count + 1) pfx.segOverride pfx.has67
              rBit xBit bBit afterOpc with
          | none => none
          | some (regIdx, rm, mlen, postMrm) =>
            let len1 := pfx.count + 1 + mlen
            let reg3 := Nat.mod regIdx 8
            let regG := gprOfNat regIdx
            if Nat.beq o 0x8D then
              if pfx.hasLock then none
              else match resolveMemAddr cfg relocs (insnPos + len1) rm with
                | some m => some (.lea sz regG m, len1)
                | none => none
            else if Nat.beq o 0x63 && rexW pfx.rex then
              if pfx.hasLock then none
              else match resolveGpOpnd cfg relocs (insnPos + len1) rm with
                | some s => some (.movsxd regG s, len1)
                | none => none
            else if Nat.beq o 0x8B then
              if pfx.hasLock then none
              else match resolveGpOpnd cfg relocs (insnPos + len1) rm with
                | some s => some (.movRegRm sz regG s, len1)
                | none => none
            else if Nat.beq o 0x89 then
              if pfx.hasLock then none
              else match resolveGpOpnd cfg relocs (insnPos + len1) rm with
                | some d => some (.movRmReg sz d regG, len1)
                | none => none
            else if Nat.beq o 0x85 then
              if pfx.hasLock then none
              else match resolveGpOpnd cfg relocs (insnPos + len1) rm with
                | some d => some (.aluRmReg sz false .test d regG, len1)
                | none => none
            else if Nat.beq (Nat.mod o 8) 1 && Nat.blt o 0x40 then
              match gpAluOfExt (Nat.div o 8) with
              | none => none
              | some aop =>
                if pfx.hasLock then
                  if GpAluOp.beq aop .cmp then none
                  else match resolveMemAddr cfg relocs (insnPos + len1) rm with
                    | some m => some (.aluRmReg sz true aop (.mem m) regG, len1)
                    | none => none
                else match resolveGpOpnd cfg relocs (insnPos + len1) rm with
                  | some d => some (.aluRmReg sz false aop d regG, len1)
                  | none => none
            else if Nat.beq (Nat.mod o 8) 3 && Nat.blt o 0x40 then
              if pfx.hasLock then none
              else match gpAluOfExt (Nat.div o 8) with
                | none => none
                | some aop =>
                  match resolveGpOpnd cfg relocs (insnPos + len1) rm with
                  | some s => some (.aluRegRm sz aop regG s, len1)
                  | none => none
            else if Nat.beq o 0x83 then
              match gpAluOfExt reg3, postMrm with
              | some aop, immB :: _ =>
                let lenImm := len1 + 1
                if pfx.hasLock then
                  if GpAluOp.beq aop .cmp then none
                  else match resolveMemAddr cfg relocs
                      (insnPos + lenImm) rm with
                    | some m =>
                      some (.aluRmImm sz true aop (.mem m) (sext8 immB), lenImm)
                    | none => none
                else match resolveGpOpnd cfg relocs (insnPos + lenImm) rm with
                  | some d =>
                    some (.aluRmImm sz false aop d (sext8 immB), lenImm)
                  | none => none
              | _, _ => none
            else if Nat.beq o 0xC1 then
              if pfx.hasLock then none
              else match postMrm with
                | immB :: _ =>
                  let lenImm := len1 + 1
                  let sop? : Option GpShiftOp :=
                    if Nat.beq reg3 4 then some .shl
                    else if Nat.beq reg3 5 then some .shr
                    else if Nat.beq reg3 7 then some .sar
                    else none
                  match sop?,
                      resolveGpOpnd cfg relocs (insnPos + lenImm) rm with
                  | some sop, some d =>
                    some (.shiftRmImm sz sop d immB.toNat, lenImm)
                  | _, _ => none
                | [] => none
            else if Nat.beq o 0xFF then
              if pfx.hasLock || pfx.has66 then none
              else if Nat.beq reg3 2 then
                match resolveGpOpnd cfg relocs (insnPos + len1) rm with
                | some t => some (.callInd t, len1)
                | none => none
              else if Nat.beq reg3 4 then
                match resolveGpOpnd cfg relocs (insnPos + len1) rm with
                | some t => some (.jmpInd t, len1)
                | none => none
              else none
            else none

/-- Total x86-64 single-instruction decoder enforcing the 16-byte fetch window
and the architectural 15-byte (`#GP(0)`) instruction-length cap. -/
@[expose] def decodeOne (cfg : DecodeConfig) (relocs : List PcRelReloc)
    (pos : Nat) (bs : List UInt8) : Option (DecodedInsn × Nat) :=
  let win := listTake 16 bs
  match decodeOneRaw cfg relocs pos win with
  | none => none
  | some (ins, len) =>
    if Nat.ble 1 len && Nat.ble len 15 && Nat.ble len win.length then
      some (ins, len)
    else none

/-- Total `@Nat.rec` byte-stream decoder producing `(offset, len, insn)`. -/
@[expose] def decodeStreamFuel (cfg : DecodeConfig) (relocs : List PcRelReloc)
    (fuel pos : Nat) (bs : List UInt8) :
    Option (List (Nat × Nat × DecodedInsn)) :=
  @Nat.rec (fun _ => Nat → List UInt8 → Option (List (Nat × Nat × DecodedInsn)))
    (fun _ rem =>
      match rem with
      | [] => some []
      | _ :: _ => none)
    (fun _ ih curPos rem =>
      match rem with
      | [] => some []
      | _ :: _ =>
        match decodeOne cfg relocs curPos rem with
        | none => none
        | some (ins, len) =>
          if Nat.beq len 0 then none
          else
            match ih (curPos + len) (listDrop len rem) with
            | none => none
            | some tl => some ((curPos, len, ins) :: tl))
    fuel pos bs

/-- Decode an entire `.text` buffer starting at offset `0`. -/
@[expose] def decodeStream (cfg : DecodeConfig) (relocs : List PcRelReloc)
    (bs : List UInt8) : Option (List (Nat × Nat × DecodedInsn)) :=
  decodeStreamFuel cfg relocs bs.length 0 bs

/-- True iff `ins` is a `ret` instruction. -/
@[expose] def isRetInsn (ins : DecodedInsn) : Bool :=
  match ins with
  | .ret => true
  | _ => false

/-- True iff `insns` ends with `.ret` and contains exactly one `.ret`. -/
@[expose] def hasSingleTerminalRet (insns : List DecodedInsn) : Bool :=
  match listGetLast? insns with
  | some .ret => Nat.beq (listCountP isRetInsn insns) 1
  | _ => false

/-- Contiguous, prefix-local full-buffer coverage ending in a single `ret`
with zero trailing bare prefix bytes and exact 1-to-1 relocation consumption
(every relocation in `relocs` is consumed exactly once with no duplicates or
unconsumed relocations). -/
@[expose] def localDecodeCoverageOk (cfg : DecodeConfig)
    (relocs : List PcRelReloc) (bs : List UInt8) : Bool :=
  match decodeStream cfg relocs bs with
  | none => false
  | some trace =>
    let allLocal := listAll (fun entry =>
      let off := entry.1
      let len := entry.2.1
      let ins := entry.2.2
      match decodeOne cfg relocs off (listTake len (listDrop off bs)) with
      | some (ins', len') => DecodedInsn.beq ins ins' && Nat.beq len len'
      | none => false) trace
    let contigEnd := List.foldl (fun acc entry =>
      match acc with
      | none => none
      | some cur =>
        if Nat.beq cur entry.1 then some (cur + entry.2.1) else none)
      (some 0) trace
    let coversAll := match contigEnd with
      | some n => Nat.beq n bs.length
      | none => false
    let relocsOk :=
      natListBijection (consumedRelocOffsets trace)
        (relocs.map (fun r => r.offset))
    let insns := trace.map (fun e => e.2.2)
    allLocal && coversAll && relocsOk && hasSingleTerminalRet insns

/-- True iff `ins` writes or touches upper 128-bit `YMM` state (VEX.256). -/
@[expose] def insnTouchesUpperYmm (ins : DecodedInsn) : Bool :=
  match ins with
  | .vbin _ is256 _ _ _ => is256
  | .vshift _ is256 _ _ _ => is256
  | .vload k _ _ _ =>
    match k with
    | .ymm | .bcastd | .bcastq | .bcast128 => true
    | .xmm | .q | .sd => false
  | .vstore k _ _ _ =>
    match k with
    | .ymm => true
    | .xmm | .lo64 | .hi64 => false
  | .vpmovzxwd is256 _ _ => is256
  | .vperm2i128 _ _ _ _ => true
  | .vinserti128 _ _ _ _ => true
  | .vextracti128 _ _ _ => true
  | .vpermq _ _ _ => true
  | .vpshufd is256 _ _ _ => is256
  | .vpblendd is256 _ _ _ _ => is256
  | _ => false

/-- Check that every VEX.256 upper-`YMM` write is cleared by `vzeroupper`
before any `ret` and before stream exit (preventing AVX/SSE transition
penalties across ABI boundaries). -/
@[expose] def dirtyYmmClearedBeforeRet (insns : List DecodedInsn) : Bool :=
  let finalState := List.foldl (fun st ins =>
    let dirty := st.1
    let ok := st.2
    match ins with
    | .vzeroupper => (false, ok)
    | .ret => (dirty, ok && !dirty)
    | _ => (dirty || insnTouchesUpperYmm ins, ok)) (false, true) insns
  finalState.2 && !finalState.1

/-! ## 6. Structural Decoder Theorems (`[]` Axioms) -/

private theorem bandLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => rfl

private theorem bandRight {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact Bool.noConfusion h
  | true => exact h

private theorem iteBoolTrue {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b then t else e) = t := by
  subst hb
  rfl

private theorem iteBoolFalse {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

/-- `decodeOne` is functional and unique (`[]` axioms). -/
theorem decodeOne_deterministic (cfg : DecodeConfig)
    (relocs : List PcRelReloc) (pos : Nat) (bs : List UInt8)
    (a b : DecodedInsn × Nat)
    (ha : decodeOne cfg relocs pos bs = some a)
    (hb : decodeOne cfg relocs pos bs = some b) : a = b := by
  rw [ha] at hb
  exact Option.some.inj hb

/-- Every successful `decodeOne` result obeys `1 ≤ len ∧ len ≤ 15`
(`#GP(0)` architectural instruction-length bound, `[]` axioms). -/
theorem decodeOne_len_bounds (cfg : DecodeConfig)
    (relocs : List PcRelReloc) (pos : Nat) (bs : List UInt8)
    (insn : DecodedInsn) (len : Nat)
    (h : decodeOne cfg relocs pos bs = some (insn, len)) :
    1 ≤ len ∧ len ≤ 15 := by
  dsimp only [decodeOne] at h
  cases hRaw : decodeOneRaw cfg relocs pos (listTake 16 bs) with
  | none =>
    rw [hRaw] at h
    nomatch h
  | some p =>
    rw [hRaw] at h
    cases p with
    | mk ins' len' =>
      dsimp only at h
      cases hCond :
          (Nat.ble 1 len' && Nat.ble len' 15 &&
            Nat.ble len' (listTake 16 bs).length) with
      | false =>
        rw [iteBoolFalse hCond] at h
        nomatch h
      | true =>
        rw [iteBoolTrue hCond] at h
        injection h with hPair
        have hLenEq : len' = len := congrArg Prod.snd hPair
        subst hLenEq
        have h12 : (Nat.ble 1 len' && Nat.ble len' 15) = true := bandLeft hCond
        exact ⟨Nat.le_of_ble_eq_true (bandLeft h12),
               Nat.le_of_ble_eq_true (bandRight h12)⟩

private theorem listTake_idemp {α : Type} (n : Nat) :
    ∀ (xs : List α), listTake n (listTake n xs) = listTake n xs := by
  induction n with
  | zero =>
    intro xs
    rfl
  | succ k ih =>
    intro xs
    cases xs with
    | nil => rfl
    | cons x rest =>
      exact congrArg (List.cons x) (ih rest)

/-- `decodeOne` depends strictly on the 16-byte architectural fetch window
(`listTake 16 bs`), so bytes at offset `≥ 16` never alter decoding. -/
theorem decodeOne_window_local (cfg : DecodeConfig)
    (relocs : List PcRelReloc) (pos : Nat) (bs : List UInt8) :
    decodeOne cfg relocs pos (listTake 16 bs) =
      decodeOne cfg relocs pos bs := by
  dsimp only [decodeOne]
  rw [listTake_idemp 16 bs]

end Anneal.ElfX86
end
