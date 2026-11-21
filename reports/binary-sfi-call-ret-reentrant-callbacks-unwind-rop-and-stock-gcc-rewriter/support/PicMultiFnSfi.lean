-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.List.TakeDrop
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Lemmas

/-!
# Repaired PIC Multi-Function Binary SFI Verifier (`checkSfiPicMultiFn`) in Lean 4

Closes the two soundness and executability fractures in single-function `code_base = 0`
surrogate-`ret` SFI models:
1. **Real `[%rsp]`-popping `0xC3` (`ret`) semantics & `raw_ret_0xc3_rop_escape` canary:**
   Models `rip : BitVec 64` as a real 64-bit virtual address and `0xC3` (`ret`) as popping
   `readMem64 s.mem (s.regs .rsp)` into `rip` and advancing `rsp` by `8`. Proves constructively
   that admitting `0xC3` inside an untrusted SFI bundle (`checkLegacySurrogateRetBundle = true`)
   permits a sandboxed store on a guest stack to redirect `rip` to an arbitrary 64-bit host
   address outside `[codeBase, codeBase + totalBytes)`.
2. **Linux `mmap_min_addr` / PIE ASLR `code_base = 0` trap & PIC `%r15` + `%r14` + `%r13`
   multi-function architecture (`checkSfiPicMultiFn_sound`):**
   Proves that without adding `%r15` (`codeBase`), `and eax, mask32; jmp rax` jumps into the
   unmapped null guard region `[0, 0x10000)` whenever `codeBase ≥ 0x10000`. Formulates and
   proves sound across all `steps : Nat` and demonic `nd : Nat → UndefFlags` the PIC
   multi-function verifier enforcing:
   - Read-only host registers `%rsp, %rbp, %rbx, %r12, %r14, %r15`;
   - Inductive 32-bit zero-extended guest stack pointer `(s.regs .r13).toNat < 2^32`,
     enabling 1-instruction guest-stack loads/stores `[r14 + r13*1 + disp]`;
   - Symmetric `±64 KiB` guard envelope `[arenaBase - 64 KiB, arenaBase + 4 GiB + 64 KiB)`
     admitting signed displacements `disp ∈ [-65536, +65528]`;
   - 2-instruction general arena macro `mov idx32, src32` + `load/store [r14 + idx*1 + disp]`;
   - 3-instruction PIC indirect branch/return macro `and r11d, mask32` +
     `lea r11, [r15 + r11*1]` + `jmp r11`;
   - Dedicated loader-synthesized Portal Bundles 0 (`portalReturn`) and 1 (`portalHostcall`),
     rejecting `0xC3` (`ret`), `push`, `pop`, and `leave` across all untrusted bundles `≥ 64`.
-/

namespace PicMultiFnSfi

/-! ## Section 1: Registers, Byte Memory, Symmetric `±64 KiB` Arena, and Demonic `RFLAGS` -/

inductive Reg where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

def regOfNat (n : Nat) : Reg :=
  match n % 16 with
  | 0  => .rax | 1  => .rcx | 2  => .rdx | 3  => .rbx
  | 4  => .rsp | 5  => .rbp | 6  => .rsi | 7  => .rdi
  | 8  => .r8  | 9  => .r9  | 10 => .r10 | 11 => .r11
  | 12 => .r12 | 13 => .r13 | 14 => .r14 | _  => .r15

def regUpd (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 64) : Reg → BitVec 64 :=
  fun r' => if r' = r then v else regs r'

theorem regUpd_eq (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 64) :
    regUpd regs r v r = v := by
  dsimp [regUpd]; simp

theorem regUpd_ne (regs : Reg → BitVec 64) {r r' : Reg} (h : r' ≠ r) (v : BitVec 64) :
    regUpd regs r v r' = regs r' := by
  dsimp [regUpd]; simp [h]

structure RFlags where
  cf : Bool := false
  pf : Bool := false
  af : Bool := false
  zf : Bool := false
  sf : Bool := false
  of : Bool := false
  deriving DecidableEq, Repr

abbrev UndefFlags := RFlags

def parity8 (lo : BitVec 8) : Bool :=
  !(lo.getLsbD 0 ^^ lo.getLsbD 1 ^^ lo.getLsbD 2 ^^ lo.getLsbD 3 ^^
    lo.getLsbD 4 ^^ lo.getLsbD 5 ^^ lo.getLsbD 6 ^^ lo.getLsbD 7)

abbrev ByteMem := BitVec 64 → BitVec 8

def memUpd8 (m : ByteMem) (a : BitVec 64) (b : BitVec 8) : ByteMem :=
  fun a' => if a' = a then b else m a'

theorem memUpd8_ne (m : ByteMem) {a a' : BitVec 64} (h : a' ≠ a) (b : BitVec 8) :
    memUpd8 m a b a' = m a' := by
  dsimp [memUpd8]; simp [h]

def byteOf64 (v : BitVec 64) (k : Nat) : BitVec 8 :=
  BitVec.extractLsb' (k * 8) 8 v

def pack8Bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ (b6 ++ (b5 ++ (b4 ++ (b3 ++ (b2 ++ (b1 ++ b0))))))

def readMem64 (m : ByteMem) (a : BitVec 64) : BitVec 64 :=
  pack8Bytes (m (a + 0#64)) (m (a + 1#64)) (m (a + 2#64)) (m (a + 3#64))
             (m (a + 4#64)) (m (a + 5#64)) (m (a + 6#64)) (m (a + 7#64))

def writeMem64 (m : ByteMem) (a : BitVec 64) (v : BitVec 64) : ByteMem :=
  let m0 := memUpd8 m  (a + 0#64) (byteOf64 v 0)
  let m1 := memUpd8 m0 (a + 1#64) (byteOf64 v 1)
  let m2 := memUpd8 m1 (a + 2#64) (byteOf64 v 2)
  let m3 := memUpd8 m2 (a + 3#64) (byteOf64 v 3)
  let m4 := memUpd8 m3 (a + 4#64) (byteOf64 v 4)
  let m5 := memUpd8 m4 (a + 5#64) (byteOf64 v 5)
  let m6 := memUpd8 m5 (a + 6#64) (byteOf64 v 6)
  memUpd8 m6 (a + 7#64) (byteOf64 v 7)

def writeMem32 (m : ByteMem) (a : BitVec 64) (v : BitVec 64) : ByteMem :=
  let m0 := memUpd8 m  (a + 0#64) (byteOf64 v 0)
  let m1 := memUpd8 m0 (a + 1#64) (byteOf64 v 1)
  let m2 := memUpd8 m1 (a + 2#64) (byteOf64 v 2)
  memUpd8 m2 (a + 3#64) (byteOf64 v 3)

def readMem32Sext64 (m : ByteMem) (a : BitVec 64) : BitVec 64 :=
  let w32 : BitVec 32 := m (a + 3#64) ++ (m (a + 2#64) ++ (m (a + 1#64) ++ m (a + 0#64)))
  (if (w32 &&& 0x80000000#32) != 0#32 then 0xFFFFFFFF#32 else 0#32) ++ w32

def readMem32Zext64 (m : ByteMem) (a : BitVec 64) : BitVec 64 :=
  let w32 : BitVec 32 := m (a + 3#64) ++ (m (a + 2#64) ++ (m (a + 1#64) ++ m (a + 0#64)))
  w32.zeroExtend 64

theorem writeMem64_byte_ne (m : ByteMem) (a b : BitVec 64) (v : BitVec 64)
    (h : ∀ k, k < 8 → b ≠ a + BitVec.ofNat 64 k) :
    writeMem64 m a v b = m b := by
  dsimp [writeMem64]
  rw [memUpd8_ne _ (h 7 (by decide)),
      memUpd8_ne _ (h 6 (by decide)),
      memUpd8_ne _ (h 5 (by decide)),
      memUpd8_ne _ (h 4 (by decide)),
      memUpd8_ne _ (h 3 (by decide)),
      memUpd8_ne _ (h 2 (by decide)),
      memUpd8_ne _ (h 1 (by decide)),
      memUpd8_ne _ (h 0 (by decide))]

theorem writeMem32_byte_ne (m : ByteMem) (a b : BitVec 64) (v : BitVec 64)
    (h : ∀ k, k < 8 → b ≠ a + BitVec.ofNat 64 k) :
    writeMem32 m a v b = m b := by
  dsimp [writeMem32]
  rw [memUpd8_ne _ (h 3 (by decide)),
      memUpd8_ne _ (h 2 (by decide)),
      memUpd8_ne _ (h 1 (by decide)),
      memUpd8_ne _ (h 0 (by decide))]

/-- C++ GMP `Nat.ble` boolean comparators (`O(1)` kernel reduction at arbitrary offsets). -/
def natLeB (a b : Nat) : Bool := Nat.ble a b
def natLtB (a b : Nat) : Bool := Nat.ble (a + 1) b
def natEqB (a b : Nat) : Bool := Nat.ble a b && Nat.ble b a

theorem natLeB_true {a b : Nat} (h : natLeB a b = true) : a ≤ b := Nat.le_of_ble_eq_true h
theorem natLtB_true {a b : Nat} (h : natLtB a b = true) : a < b := Nat.le_of_ble_eq_true h
theorem natEqB_true {a b : Nat} (h : natEqB a b = true) : a = b := by
  have hc := Bool.and_eq_true_iff.mp h
  exact Nat.le_antisymm (Nat.le_of_ble_eq_true hc.1) (Nat.le_of_ble_eq_true hc.2)

/-! ## Section 2: Variable-Length (`1..15`B) x86-64 Byte Decoder & Prefix-Invariance -/

inductive AluOp where
  | add | sub | xor | and | or | cmp | test
  deriving DecidableEq, Repr

inductive ShiftOp where
  | shl | shr
  deriving DecidableEq, Repr

inductive CondCode where
  | e | ne | b | ae | be | a
  deriving DecidableEq, Repr

inductive MemAddr where
  | baseDisp (base : Reg) (index : Option (Reg × Nat)) (disp : BitVec 64)
  | ripRel   (disp : BitVec 64)
  deriving DecidableEq, Repr

inductive X64Instr where
  | nop
  | endbr64
  | movRR64    (dst src : Reg)
  | movRR32    (dst src : Reg)
  | movImm64   (dst : Reg) (imm : BitVec 64)
  | movImm32   (dst : Reg) (imm : BitVec 32)
  | load64     (dst : Reg) (addr : MemAddr)
  | store64    (addr : MemAddr) (src : Reg)
  | store32    (addr : MemAddr) (src : Reg)
  | load32Zext (dst : Reg) (addr : MemAddr)
  | load32Sext (dst : Reg) (addr : MemAddr)
  | lea64      (dst : Reg) (addr : MemAddr)
  | aluRR64    (op : AluOp) (dst src : Reg)
  | aluImm64   (op : AluOp) (dst : Reg) (imm : BitVec 64)
  | aluRR32    (op : AluOp) (dst src : Reg)
  | aluImm32   (op : AluOp) (dst : Reg) (imm : BitVec 32)
  | shiftImm64 (op : ShiftOp) (dst : Reg) (cnt : Nat)
  | imulRR64   (dst src : Reg)
  | push64     (src : Reg)
  | pop64      (dst : Reg)
  | leave64
  | jmpRel     (rel : BitVec 64)
  | jccRel     (cc : CondCode) (rel : BitVec 64)
  | jmpReg     (target : Reg)
  | ret
  | int3
  deriving DecidableEq, Repr

inductive DecodeFault where
  | truncated | gpLenExceeded | udIllegalLock | unsupported
  deriving DecidableEq, Repr

inductive DecodeOutcome where
  | ok    (ins : X64Instr) (len : Nat)
  | fault (f : DecodeFault)
  deriving DecidableEq, Repr

inductive RepPfx where
  | none | f2 | f3
  deriving DecidableEq, Repr

structure PrefixState where
  hasLock : Bool := false
  rep     : RepPfx := .none
  has66   : Bool := false
  has67   : Bool := false
  rex     : Option UInt8 := none
  deriving DecidableEq, Repr

def isLegacyPrefix (b : UInt8) : Bool :=
  b == 0xF0 || b == 0xF2 || b == 0xF3 || b == 0x66 || b == 0x67 ||
  b == 0x2E || b == 0x3E || b == 0x64 || b == 0x65

def isRexPrefix (b : UInt8) : Bool := (b &&& 0xF0) == 0x40
def rexW (r : Option UInt8) : Bool := match r with | some b => (b &&& 0x08) != 0 | none => false
def rexR (r : Option UInt8) : Nat  := match r with | some b => if (b &&& 0x04) != 0 then 8 else 0 | none => 0
def rexX (r : Option UInt8) : Nat  := match r with | some b => if (b &&& 0x02) != 0 then 8 else 0 | none => 0
def rexB (r : Option UInt8) : Nat  := match r with | some b => if (b &&& 0x01) != 0 then 8 else 0 | none => 0

def stepPrefix (ps : PrefixState) (b : UInt8) : PrefixState :=
  if b == 0xF0 then { ps with hasLock := true, rex := none }
  else if b == 0xF2 then { ps with rep := .f2, rex := none }
  else if b == 0xF3 then { ps with rep := .f3, rex := none }
  else if b == 0x66 then { ps with has66 := true, rex := none }
  else if b == 0x67 then { ps with has67 := true, rex := none }
  else { ps with rex := none }

def scanPrefixes : Nat → PrefixState → Nat → List UInt8 → Option (PrefixState × Nat × List UInt8)
  | 0, _, _, _ => none
  | _ + 1, ps, consumed, [] => some (ps, consumed, [])
  | fuel + 1, ps, consumed, b :: rest =>
      if isLegacyPrefix b then scanPrefixes fuel (stepPrefix ps b) (consumed + 1) rest
      else if isRexPrefix b then scanPrefixes fuel { ps with rex := some b } (consumed + 1) rest
      else some (ps, consumed, b :: rest)

theorem scanPrefixes_append_nonempty :
    ∀ (fuel : Nat) (ps ps' : PrefixState) (c c' : Nat) (bs body sfx : List UInt8),
      scanPrefixes fuel ps c bs = some (ps', c', body) →
      body ≠ [] →
      c' + body.length = c + bs.length ∧
      scanPrefixes fuel ps c (bs ++ sfx) = some (ps', c', body ++ sfx)
  | 0, _, _, _, _, _, _, _, h, _ => nomatch h
  | _ + 1, _, _, _, _, [], _, _, h, hne => by
    dsimp [scanPrefixes] at h
    injection h with h1; injection h1 with _ h2; injection h2 with _ hbody
    exact False.elim (hne hbody.symm)
  | fuel + 1, ps, ps', c, c', b :: rest, body, sfx, h, hne => by
    dsimp [scanPrefixes] at h ⊢
    revert h
    cases isLegacyPrefix b with
    | true =>
      intro h; dsimp at h ⊢
      have ih := scanPrefixes_append_nonempty fuel (stepPrefix ps b) ps' (c + 1) c' rest body sfx h hne
      refine ⟨?_, ih.2⟩
      rw [ih.1]; show c + 1 + rest.length = c + (rest.length + 1)
      rw [Nat.add_assoc c 1 rest.length, Nat.add_comm 1 rest.length, ← Nat.add_assoc]
    | false =>
      dsimp
      cases isRexPrefix b with
      | true =>
        intro h; dsimp at h ⊢
        have ih := scanPrefixes_append_nonempty fuel { ps with rex := some b } ps' (c + 1) c' rest body sfx h hne
        refine ⟨?_, ih.2⟩
        rw [ih.1]; show c + 1 + rest.length = c + (rest.length + 1)
        rw [Nat.add_assoc c 1 rest.length, Nat.add_comm 1 rest.length, ← Nat.add_assoc]
      | false =>
        intro h; dsimp at h ⊢
        injection h with h1; injection h1 with hps h2; injection h2 with hc hbody
        subst hps hc hbody
        exact ⟨rfl, rfl⟩

def listGet? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => listGet? xs n

def lenTR {α : Type} : List α → Nat
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => 8 + lenTR rest
  | _ :: rest => 1 + lenTR rest
  | [] => 0

theorem lenTR_eq_length {α : Type} : ∀ (xs : List α), lenTR xs = xs.length
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: rest => by
    show 8 + lenTR rest = rest.length + 8
    rw [lenTR_eq_length rest, Nat.add_comm]
  | [_, _, _, _, _, _, _] | [_, _, _, _, _, _] | [_, _, _, _, _]
  | [_, _, _, _] | [_, _, _] | [_, _] | [_] | [] => rfl

theorem listGet?_append_left {α : Type} :
    ∀ (xs ys : List α) (i : Nat), i < xs.length → listGet? (xs ++ ys) i = listGet? xs i
  | [], _, _, h => nomatch h
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, h => listGet?_append_left xs ys i (Nat.lt_of_succ_lt_succ h)

def modrmLenAt (body : List UInt8) (modrmIdx : Nat) : Option Nat :=
  match listGet? body modrmIdx with
  | none => none
  | some modrm =>
    let modBits := (modrm >>> 6) &&& 0x03
    let rmBits  := modrm &&& 0x07
    if modBits == 3 then some 1
    else if rmBits == 4 then
      match listGet? body (modrmIdx + 1) with
      | none => none
      | some sib =>
        let baseBits := sib &&& 0x07
        if modBits == 0 then
          if baseBits == 5 then some 6 else some 2
        else if modBits == 1 then some 3
        else some 6
    else
      if modBits == 0 then
        if rmBits == 5 then some 5 else some 1
      else if modBits == 1 then some 2
      else some 5

theorem modrmLenAt_ge (body : List UInt8) (idx n : Nat)
    (h : modrmLenAt body idx = some n) : 1 ≤ n := by
  dsimp [modrmLenAt] at h
  cases h0 : listGet? body idx with
  | none => rw [h0] at h; nomatch h
  | some modrm =>
    rw [h0] at h; dsimp at h
    split at h
    · injection h with h'; subst h'; decide
    · split at h
      · cases h1 : listGet? body (idx + 1) with
        | none => rw [h1] at h; nomatch h
        | some sib =>
          rw [h1] at h; dsimp at h
          repeat (first | split at h | (injection h with h'; subst h'; decide))
      · repeat (first | split at h | (injection h with h'; subst h'; decide))

theorem modrmLenAt_append (body sfx : List UInt8) (idx n : Nat)
    (h : modrmLenAt body idx = some n) (hle : idx + n ≤ body.length) :
    modrmLenAt (body ++ sfx) idx = some n := by
  have hge1 : 1 ≤ n := modrmLenAt_ge body idx n h
  have hlt0 : idx < body.length := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hge1) hle
  dsimp [modrmLenAt] at h ⊢
  rw [listGet?_append_left body sfx idx hlt0]
  revert h
  cases listGet? body idx with
  | none => intro h; nomatch h
  | some modrm =>
    dsimp
    cases (((modrm >>> 6) &&& 3) == 3) with
    | true => intro h; exact h
    | false =>
      dsimp
      cases ((modrm &&& 7) == 4) with
      | false => intro h; exact h
      | true =>
        dsimp
        cases h1 : listGet? body (idx + 1) with
        | none => intro h; nomatch h
        | some _ =>
          intro h; dsimp at h
          have hge2 : 2 ≤ n := by
            repeat (first | split at h | (injection h with h'; subst h'; decide))
          have hlt1 : idx + 1 < body.length :=
            Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 1 < 2) idx)
              (Nat.le_trans (Nat.add_le_add_left hge2 idx) hle)
          rw [listGet?_append_left body sfx (idx + 1) hlt1, h1]
          exact h

inductive IldKind where
  | fixed1 | fixed2 | fixed5 | fixed9 | modrm1 (immBytes : Nat) | esc0F
  deriving DecidableEq, Repr

def classifyOpc (hasRexW : Bool) (opc : UInt8) : IldKind :=
  if opc == 0x90 || opc == 0xC3 || opc == 0xC9 || opc == 0xCC ||
     (opc >= 0x50 && opc <= 0x5F) then .fixed1
  else if opc == 0xEB || (opc >= 0x70 && opc <= 0x7F) then .fixed2
  else if opc == 0x05 || opc == 0x25 || opc == 0xE9 then .fixed5
  else if opc >= 0xB8 && opc <= 0xBF then
    if hasRexW then .fixed9 else .fixed5
  else if opc == 0x01 || opc == 0x03 || opc == 0x09 || opc == 0x0B ||
          opc == 0x21 || opc == 0x23 || opc == 0x29 || opc == 0x2B ||
          opc == 0x31 || opc == 0x33 || opc == 0x39 || opc == 0x3B ||
          opc == 0x63 || opc == 0x85 || opc == 0x89 || opc == 0x8B ||
          opc == 0x8D || opc == 0xD1 || opc == 0xFF then .modrm1 0
  else if opc == 0x83 || opc == 0xC1 then .modrm1 1
  else if opc == 0x81 || opc == 0xC7 then .modrm1 4
  else if opc == 0x0F then .esc0F
  else .fixed1

inductive Esc0FKind where
  | fixed2 | fixed6 | modrm2
  deriving DecidableEq, Repr

def classifyEsc0F (opc2 : UInt8) : Esc0FKind :=
  if opc2 >= 0x80 && opc2 <= 0x8F then .fixed6
  else if opc2 == 0x1E || opc2 == 0x1F || opc2 == 0xAF then .modrm2
  else .fixed2

def ildBodyLen (ps : PrefixState) (body : List UInt8) : Option Nat :=
  match listGet? body 0 with
  | none => none
  | some opc =>
    match classifyOpc (rexW ps.rex) opc with
    | .fixed1 => some 1
    | .fixed2 => some 2
    | .fixed5 => some 5
    | .fixed9 => some 9
    | .modrm1 immB =>
      match modrmLenAt body 1 with
      | some m => some ((1 + m) + immB)
      | none   => none
    | .esc0F =>
      match listGet? body 1 with
      | none => none
      | some opc2 =>
        match classifyEsc0F opc2 with
        | .fixed2 => some 2
        | .fixed6 => some 6
        | .modrm2 =>
          match modrmLenAt body 2 with
          | some m => some (2 + m)
          | none   => none

theorem ildBodyLen_pos (ps : PrefixState) (body : List UInt8) (n : Nat)
    (h : ildBodyLen ps body = some n) : 1 ≤ n := by
  dsimp [ildBodyLen] at h; revert h
  cases listGet? body 0 with
  | none => intro h; nomatch h
  | some opc =>
    dsimp; cases classifyOpc (rexW ps.rex) opc with
    | fixed1 | fixed2 | fixed5 | fixed9 =>
      intro h; injection h with hn; subst hn; decide
    | modrm1 immB =>
      dsimp; cases modrmLenAt body 1 with
      | none => intro h; nomatch h
      | some m =>
        intro h; injection h with hn; subst hn
        exact Nat.le_trans (Nat.le_add_right 1 m) (Nat.le_add_right (1 + m) immB)
    | esc0F =>
      dsimp; cases listGet? body 1 with
      | none => intro h; nomatch h
      | some opc2 =>
        dsimp; cases classifyEsc0F opc2 with
        | fixed2 | fixed6 => intro h; injection h with hn; subst hn; decide
        | modrm2 =>
          dsimp; cases modrmLenAt body 2 with
          | none => intro h; nomatch h
          | some m =>
            intro h; injection h with hn; subst hn
            exact Nat.le_trans (by decide : 1 ≤ 2) (Nat.le_add_right 2 m)

theorem ildBodyLen_append (ps : PrefixState) (body sfx : List UInt8) (n : Nat)
    (h : ildBodyLen ps body = some n) (hle : n ≤ body.length) :
    ildBodyLen ps (body ++ sfx) = some n := by
  have hpos : 1 ≤ n := ildBodyLen_pos ps body n h
  have hlt0 : 0 < body.length := Nat.lt_of_lt_of_le hpos hle
  dsimp [ildBodyLen] at h ⊢
  rw [listGet?_append_left body sfx 0 hlt0]; revert h
  cases listGet? body 0 with
  | none => intro h; nomatch h
  | some opc =>
    dsimp; cases classifyOpc (rexW ps.rex) opc with
    | fixed1 | fixed2 | fixed5 | fixed9 => intro h; exact h
    | modrm1 immB =>
      dsimp; cases hm : modrmLenAt body 1 with
      | none => intro h; nomatch h
      | some m =>
        intro h; injection h with hn; subst hn
        have hmle : 1 + m ≤ body.length := Nat.le_trans (Nat.le_add_right (1 + m) immB) hle
        rw [modrmLenAt_append body sfx 1 m hm hmle]
    | esc0F =>
      dsimp; cases hb1 : listGet? body 1 with
      | none => intro h; nomatch h
      | some opc2 =>
        dsimp; cases he : classifyEsc0F opc2 with
        | fixed2 =>
          intro h; injection h with hn; subst hn
          rw [listGet?_append_left body sfx 1 (Nat.lt_of_lt_of_le (by decide : 1 < 2) hle), hb1]
          dsimp; rw [he]
        | fixed6 =>
          intro h; injection h with hn; subst hn
          have h2 : 2 ≤ body.length := Nat.le_trans (by decide : 2 ≤ 6) hle
          rw [listGet?_append_left body sfx 1 (Nat.lt_of_lt_of_le (by decide : 1 < 2) h2), hb1]
          dsimp; rw [he]
        | modrm2 =>
          dsimp; cases hm : modrmLenAt body 2 with
          | none => intro h; nomatch h
          | some m =>
            intro h; injection h with hn; subst hn
            have h2 : 2 ≤ body.length := Nat.le_trans (Nat.le_add_right 2 m) hle
            rw [listGet?_append_left body sfx 1 (Nat.lt_of_lt_of_le (by decide : 1 < 2) h2), hb1]
            dsimp; rw [he]; dsimp
            rw [modrmLenAt_append body sfx 2 m hm hle]

def u8ToBV8 (b : UInt8) : BitVec 8 := BitVec.ofNat 8 b.toNat
def readBV32LE (b0 b1 b2 b3 : UInt8) : BitVec 32 :=
  u8ToBV8 b3 ++ (u8ToBV8 b2 ++ (u8ToBV8 b1 ++ u8ToBV8 b0))
def readBV64LE (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : BitVec 64 :=
  pack8Bytes (u8ToBV8 b0) (u8ToBV8 b1) (u8ToBV8 b2) (u8ToBV8 b3)
             (u8ToBV8 b4) (u8ToBV8 b5) (u8ToBV8 b6) (u8ToBV8 b7)
def sext8To64 (b : UInt8) : BitVec 64 :=
  let v := u8ToBV8 b
  (if (v &&& 0x80#8) != 0#8 then 0xFFFFFFFFFFFFFF#56 else 0#56) ++ v
def sext8To32 (b : UInt8) : BitVec 32 :=
  let v := u8ToBV8 b
  (if (v &&& 0x80#8) != 0#8 then 0xFFFFFF#24 else 0#24) ++ v
def sext32To64 (b0 b1 b2 b3 : UInt8) : BitVec 64 :=
  let w := readBV32LE b0 b1 b2 b3
  (if (w &&& 0x80000000#32) != 0#32 then 0xFFFFFFFF#32 else 0#32) ++ w

def parseModRM (ps : PrefixState) (bs : List UInt8) :
    Option (Reg × (Reg ⊕ MemAddr) × List UInt8) :=
  match bs with
  | [] => none
  | modrm :: rest =>
    let modBits := (modrm >>> 6) &&& 0x03
    let regIdx  := rexR ps.rex + ((modrm >>> 3) &&& 0x07).toNat
    let rmBits  := modrm &&& 0x07
    let reg     := regOfNat regIdx
    let rmReg   := regOfNat (rexB ps.rex + rmBits.toNat)
    if modBits == 3 then some (reg, .inl rmReg, rest)
    else if rmBits == 4 then
      match rest with
      | [] => none
      | sib :: rest1 =>
        let scaleBits := (sib >>> 6) &&& 0x03
        let idxNum    := rexX ps.rex + ((sib >>> 3) &&& 0x07).toNat
        let idxOpt    := if idxNum == 4 then none else some (regOfNat idxNum, 1 <<< scaleBits.toNat)
        let baseBits  := sib &&& 0x07
        let baseReg   := regOfNat (rexB ps.rex + baseBits.toNat)
        if modBits == 0 then
          if baseBits == 5 then none
          else some (reg, .inr (.baseDisp baseReg idxOpt 0#64), rest1)
        else if modBits == 1 then
          match rest1 with
          | d8 :: rest2 => some (reg, .inr (.baseDisp baseReg idxOpt (sext8To64 d8)), rest2)
          | [] => none
        else
          match rest1 with
          | b0 :: b1 :: b2 :: b3 :: rest2 =>
            some (reg, .inr (.baseDisp baseReg idxOpt (sext32To64 b0 b1 b2 b3)), rest2)
          | _ => none
    else
      if modBits == 0 then
        if rmBits == 5 then
          match rest with
          | b0 :: b1 :: b2 :: b3 :: rest1 =>
            some (reg, .inr (.ripRel (sext32To64 b0 b1 b2 b3)), rest1)
          | _ => none
        else some (reg, .inr (.baseDisp rmReg none 0#64), rest)
      else if modBits == 1 then
        match rest with
        | d8 :: rest1 => some (reg, .inr (.baseDisp rmReg none (sext8To64 d8)), rest1)
        | [] => none
      else
        match rest with
        | b0 :: b1 :: b2 :: b3 :: rest1 =>
          some (reg, .inr (.baseDisp rmReg none (sext32To64 b0 b1 b2 b3)), rest1)
        | _ => none

def aluOpOfExt (ext : UInt8) : Option AluOp :=
  match ext with
  | 0 => some .add | 1 => some .or | 4 => some .and
  | 5 => some .sub | 6 => some .xor | 7 => some .cmp | _ => none

def ccOfLowNibble (n : UInt8) : Option CondCode :=
  match n with
  | 0x2 => some .b | 0x3 => some .ae | 0x4 => some .e
  | 0x5 => some .ne | 0x6 => some .be | 0x7 => some .a | _ => none

inductive BodyParseResult where
  | okIns (ins : X64Instr)
  | err   (f : DecodeFault)
  deriving DecidableEq, Repr

def parseAluMR (ps : PrefixState) (op : AluOp) (rest : List UInt8) : BodyParseResult :=
  if ps.hasLock then .err .udIllegalLock
  else if ps.rep != .none then .err .unsupported
  else match parseModRM ps rest with
  | some (reg, .inl rm, []) =>
    if rexW ps.rex then .okIns (.aluRR64 op rm reg)
    else if !ps.has66 then .okIns (.aluRR32 op rm reg)
    else .err .unsupported
  | _ => .err .unsupported

def parseAluRM (ps : PrefixState) (op : AluOp) (rest : List UInt8) : BodyParseResult :=
  if ps.hasLock then .err .udIllegalLock
  else if ps.rep != .none then .err .unsupported
  else match parseModRM ps rest with
  | some (reg, .inl rm, []) =>
    if rexW ps.rex then .okIns (.aluRR64 op reg rm)
    else if !ps.has66 then .okIns (.aluRR32 op reg rm)
    else .err .unsupported
  | _ => .err .unsupported

def parseExactBody (ps : PrefixState) (exactBody : List UInt8) : BodyParseResult :=
  match exactBody with
  | [] => .err .truncated
  | opc :: rest =>
    if opc == 0x90 then
      if ps.hasLock then .err .udIllegalLock
      else if ps.rep != .none then .err .unsupported
      else if rexB ps.rex == 0 then .okIns .nop
      else .err .unsupported
    else if opc == 0xC3 then
      if ps.hasLock then .err .udIllegalLock else .okIns .ret
    else if opc == 0xC9 then
      if ps.hasLock then .err .udIllegalLock else .okIns .leave64
    else if opc == 0xCC then
      if ps.hasLock then .err .udIllegalLock else .okIns .int3
    else if opc >= 0x50 && opc <= 0x57 then
      if ps.hasLock then .err .udIllegalLock
      else .okIns (.push64 (regOfNat (rexB ps.rex + (opc - 0x50).toNat)))
    else if opc >= 0x58 && opc <= 0x5F then
      if ps.hasLock then .err .udIllegalLock
      else .okIns (.pop64 (regOfNat (rexB ps.rex + (opc - 0x58).toNat)))
    else if opc >= 0xB8 && opc <= 0xBF then
      if ps.hasLock then .err .udIllegalLock
      else
        let dst := regOfNat (rexB ps.rex + (opc - 0xB8).toNat)
        if rexW ps.rex then
          match rest with
          | [b0, b1, b2, b3, b4, b5, b6, b7] =>
            .okIns (.movImm64 dst (readBV64LE b0 b1 b2 b3 b4 b5 b6 b7))
          | _ => .err .unsupported
        else if !ps.has66 then
          match rest with
          | [b0, b1, b2, b3] => .okIns (.movImm32 dst (readBV32LE b0 b1 b2 b3))
          | _ => .err .unsupported
        else .err .unsupported
    else if opc == 0xEB then
      if ps.hasLock then .err .udIllegalLock
      else match rest with
      | [d8] => .okIns (.jmpRel (sext8To64 d8))
      | _ => .err .unsupported
    else if opc == 0xE9 then
      if ps.hasLock then .err .udIllegalLock
      else match rest with
      | [b0, b1, b2, b3] => .okIns (.jmpRel (sext32To64 b0 b1 b2 b3))
      | _ => .err .unsupported
    else if opc >= 0x70 && opc <= 0x7F then
      if ps.hasLock then .err .udIllegalLock
      else match ccOfLowNibble (opc - 0x70), rest with
      | some cc, [d8] => .okIns (.jccRel cc (sext8To64 d8))
      | _, _ => .err .unsupported
    else if opc == 0x05 then
      if ps.hasLock then .err .udIllegalLock
      else match rest with
      | [b0, b1, b2, b3] =>
        if rexW ps.rex then .okIns (.aluImm64 .add .rax (sext32To64 b0 b1 b2 b3))
        else if !ps.has66 then .okIns (.aluImm32 .add .rax (readBV32LE b0 b1 b2 b3))
        else .err .unsupported
      | _ => .err .unsupported
    else if opc == 0x25 then
      if ps.hasLock then .err .udIllegalLock
      else match rest with
      | [b0, b1, b2, b3] =>
        if rexW ps.rex then .okIns (.aluImm64 .and .rax (sext32To64 b0 b1 b2 b3))
        else if !ps.has66 then .okIns (.aluImm32 .and .rax (readBV32LE b0 b1 b2 b3))
        else .err .unsupported
      | _ => .err .unsupported
    else if opc == 0x89 then
      if ps.hasLock then .err .udIllegalLock
      else if ps.rep != .none || ps.has67 then .err .unsupported
      else match parseModRM ps rest with
      | some (src, .inl dst, []) =>
        if rexW ps.rex then .okIns (.movRR64 dst src)
        else if !ps.has66 then .okIns (.movRR32 dst src)
        else .err .unsupported
      | some (src, .inr addr, []) =>
        if rexW ps.rex then .okIns (.store64 addr src)
        else if !ps.has66 then .okIns (.store32 addr src)
        else .err .unsupported
      | _ => .err .unsupported
    else if opc == 0x8B then
      if ps.hasLock then .err .udIllegalLock
      else if ps.rep != .none || ps.has67 then .err .unsupported
      else match parseModRM ps rest with
      | some (dst, .inl src, []) =>
        if rexW ps.rex then .okIns (.movRR64 dst src)
        else if !ps.has66 then .okIns (.movRR32 dst src)
        else .err .unsupported
      | some (dst, .inr addr, []) =>
        if rexW ps.rex then .okIns (.load64 dst addr)
        else if !ps.has66 then .okIns (.load32Zext dst addr)
        else .err .unsupported
      | _ => .err .unsupported
    else if opc == 0x63 then
      if ps.hasLock then .err .udIllegalLock
      else if !rexW ps.rex || ps.rep != .none || ps.has67 then .err .unsupported
      else match parseModRM ps rest with
      | some (dst, .inr addr, []) => .okIns (.load32Sext dst addr)
      | _ => .err .unsupported
    else if opc == 0x8D then
      if ps.hasLock then .err .udIllegalLock
      else if !rexW ps.rex || ps.rep != .none || ps.has67 then .err .unsupported
      else match parseModRM ps rest with
      | some (dst, .inr addr, []) => .okIns (.lea64 dst addr)
      | _ => .err .unsupported
    else if opc == 0x01 then parseAluMR ps .add rest
    else if opc == 0x03 then parseAluRM ps .add rest
    else if opc == 0x09 then parseAluMR ps .or  rest
    else if opc == 0x0B then parseAluRM ps .or  rest
    else if opc == 0x21 then parseAluMR ps .and rest
    else if opc == 0x23 then parseAluRM ps .and rest
    else if opc == 0x29 then parseAluMR ps .sub rest
    else if opc == 0x2B then parseAluRM ps .sub rest
    else if opc == 0x31 then parseAluMR ps .xor rest
    else if opc == 0x33 then parseAluRM ps .xor rest
    else if opc == 0x39 then parseAluMR ps .cmp rest
    else if opc == 0x3B then parseAluRM ps .cmp rest
    else if opc == 0x85 then parseAluMR ps .test rest
    else if opc == 0x83 then
      if ps.hasLock then .err .udIllegalLock
      else match parseModRM ps rest, listGet? rest 0 with
      | some (_, .inl rm, [imm8]), some modrm =>
        match aluOpOfExt ((modrm >>> 3) &&& 0x07) with
        | some op =>
          if rexW ps.rex then .okIns (.aluImm64 op rm (sext8To64 imm8))
          else if !ps.has66 then .okIns (.aluImm32 op rm (sext8To32 imm8))
          else .err .unsupported
        | none => .err .unsupported
      | _, _ => .err .unsupported
    else if opc == 0x81 then
      if ps.hasLock then .err .udIllegalLock
      else match parseModRM ps rest, listGet? rest 0 with
      | some (_, .inl rm, [b0, b1, b2, b3]), some modrm =>
        match aluOpOfExt ((modrm >>> 3) &&& 0x07) with
        | some op =>
          if rexW ps.rex then .okIns (.aluImm64 op rm (sext32To64 b0 b1 b2 b3))
          else if !ps.has66 then .okIns (.aluImm32 op rm (readBV32LE b0 b1 b2 b3))
          else .err .unsupported
        | none => .err .unsupported
      | _, _ => .err .unsupported
    else if opc == 0xC1 then
      if ps.hasLock then .err .udIllegalLock
      else if !rexW ps.rex then .err .unsupported
      else match parseModRM ps rest, listGet? rest 0 with
      | some (_, .inl rm, [cnt8]), some modrm =>
        let ext := (modrm >>> 3) &&& 0x07
        if ext == 4 then .okIns (.shiftImm64 .shl rm (cnt8 &&& 0x3F).toNat)
        else if ext == 5 then .okIns (.shiftImm64 .shr rm (cnt8 &&& 0x3F).toNat)
        else .err .unsupported
      | _, _ => .err .unsupported
    else if opc == 0xD1 then
      if ps.hasLock then .err .udIllegalLock
      else if !rexW ps.rex then .err .unsupported
      else match parseModRM ps rest, listGet? rest 0 with
      | some (_, .inl rm, []), some modrm =>
        let ext := (modrm >>> 3) &&& 0x07
        if ext == 4 then .okIns (.shiftImm64 .shl rm 1)
        else if ext == 5 then .okIns (.shiftImm64 .shr rm 1)
        else .err .unsupported
      | _, _ => .err .unsupported
    else if opc == 0xFF then
      if ps.hasLock then .err .udIllegalLock
      else match parseModRM ps rest, listGet? rest 0 with
      | some (_, .inl rm, []), some modrm =>
        if ((modrm >>> 3) &&& 0x07) == 4 then .okIns (.jmpReg rm)
        else .err .unsupported
      | _, _ => .err .unsupported
    else if opc == 0x0F then
      match rest with
      | [] => .err .truncated
      | opc2 :: rest2 =>
        if opc2 == 0x1E then
          if ps.hasLock then .err .udIllegalLock
          else match rest2 with
          | [0xFA] =>
            if ps.rep == .f3 && ps.rex.isNone then .okIns .endbr64
            else if ps.rep == .none then .okIns .nop
            else .err .unsupported
          | _ => .err .unsupported
        else if opc2 == 0x1F then
          if ps.hasLock then .err .udIllegalLock
          else if ps.rep != .none then .err .unsupported
          else match parseModRM ps rest2, listGet? rest2 0 with
          | some (_, _, []), some modrm =>
            if ((modrm >>> 3) &&& 0x07) == 0 then .okIns .nop else .err .unsupported
          | _, _ => .err .unsupported
        else if opc2 >= 0x80 && opc2 <= 0x8F then
          if ps.hasLock then .err .udIllegalLock
          else match ccOfLowNibble (opc2 - 0x80), rest2 with
          | some cc, [b0, b1, b2, b3] => .okIns (.jccRel cc (sext32To64 b0 b1 b2 b3))
          | _, _ => .err .unsupported
        else if opc2 == 0xAF then
          if ps.hasLock then .err .udIllegalLock
          else if !rexW ps.rex || ps.rep != .none then .err .unsupported
          else match parseModRM ps rest2 with
          | some (dst, .inl src, []) => .okIns (.imulRR64 dst src)
          | _ => .err .unsupported
        else .err .unsupported
    else .err .unsupported

def decodeX64 (bs : List UInt8) : DecodeOutcome :=
  match scanPrefixes 16 {} 0 bs with
  | none => .fault .gpLenExceeded
  | some (ps, pfxLen, body) =>
    match ildBodyLen ps body with
    | none => .fault .truncated
    | some bLen =>
      let exactBody := body.take bLen
      if exactBody.length < bLen then .fault .truncated
      else if pfxLen + bLen > 15 then .fault .gpLenExceeded
      else match parseExactBody ps exactBody with
      | .okIns ins => .ok ins (pfxLen + bLen)
      | .err flt   => .fault flt

theorem decodeX64_len_bounds {bs : List UInt8} {ins : X64Instr} {len : Nat}
    (hok : decodeX64 bs = .ok ins len) :
    1 ≤ len ∧ len ≤ 15 ∧ len ≤ bs.length := by
  dsimp [decodeX64] at hok; revert hok
  cases hs : scanPrefixes 16 {} 0 bs with
  | none => intro h; nomatch h
  | some triple =>
    rcases triple with ⟨ps, pfxLen, body⟩; dsimp
    cases hi : ildBodyLen ps body with
    | none => intro h; nomatch h
    | some bLen =>
      dsimp
      cases hlt : decide ((body.take bLen).length < bLen) with
      | true => intro h; simp only [of_decide_eq_true hlt, ite_true] at h; nomatch h
      | false =>
        have hge : bLen ≤ (body.take bLen).length := Nat.not_lt.mp (of_decide_eq_false hlt)
        have hbody_ge : bLen ≤ body.length := Nat.le_trans hge (List.length_take_le' bLen body)
        have hbpos : 1 ≤ bLen := ildBodyLen_pos ps body bLen hi
        have hne : body ≠ [] := by
          intro heq; subst heq; have : 1 ≤ 0 := Nat.le_trans hbpos hbody_ge; nomatch this
        have hscan := scanPrefixes_append_nonempty 16 {} ps 0 pfxLen bs body [] hs hne
        cases hgt15 : decide (pfxLen + bLen > 15) with
        | true =>
          intro h; simp only [of_decide_eq_false hlt, of_decide_eq_true hgt15, ite_false, ite_true] at h
          nomatch h
        | false =>
          intro h
          have ht1 := of_decide_eq_false hlt; have ht2 := of_decide_eq_false hgt15
          simp only [ht1, ht2, ite_false] at h; revert h
          cases parseExactBody ps (body.take bLen) with
          | err _ => intro h; nomatch h
          | okIns _ =>
            intro h; injection h with _ hlen_eq; subst hlen_eq
            refine ⟨Nat.le_trans hbpos (Nat.le_add_left bLen pfxLen), Nat.not_lt.mp ht2, ?_⟩
            have hbs : pfxLen + body.length = bs.length := by
              have t := hscan.1; rw [Nat.zero_add] at t; exact t
            rw [← hbs]; exact Nat.add_le_add_left hbody_ge pfxLen

theorem decodeX64_prefix_invariant {pfx : List UInt8} {ins : X64Instr} {len : Nat}
    (hok : decodeX64 pfx = .ok ins len) (sfx : List UInt8) :
    decodeX64 (pfx ++ sfx) = .ok ins len := by
  dsimp [decodeX64] at hok ⊢; revert hok
  cases hs : scanPrefixes 16 {} 0 pfx with
  | none => intro h; nomatch h
  | some triple =>
    rcases triple with ⟨ps, pfxLen, body⟩; dsimp
    cases hi : ildBodyLen ps body with
    | none => intro h; nomatch h
    | some bLen =>
      dsimp
      cases hlt : decide ((body.take bLen).length < bLen) with
      | true => intro h; simp only [of_decide_eq_true hlt, ite_true] at h; nomatch h
      | false =>
        have ht1 := of_decide_eq_false hlt
        have hge : bLen ≤ (body.take bLen).length := Nat.not_lt.mp ht1
        have hbody_ge : bLen ≤ body.length := Nat.le_trans hge (List.length_take_le' bLen body)
        have hbpos : 1 ≤ bLen := ildBodyLen_pos ps body bLen hi
        have hne : body ≠ [] := by
          intro heq; subst heq; have : 1 ≤ 0 := Nat.le_trans hbpos hbody_ge; nomatch this
        have hscan := scanPrefixes_append_nonempty 16 {} ps 0 pfxLen pfx body sfx hs hne
        rw [hscan.2]; dsimp
        rw [ildBodyLen_append ps body sfx bLen hi hbody_ge]; dsimp
        rw [List.take_append_of_le_length hbody_ge]
        intro h; exact h

/-! ## Section 3: Real 64-Bit Virtual-Address & `[%rsp]`-Popping x86-64 Machine -/

inductive ByteCodeTree where
  | leaf (bytes : List UInt8)
  | node (leftBytes : Nat) (l r : ByteCodeTree)

def ByteCodeTree.getByte? : ByteCodeTree → Nat → Option UInt8
  | .leaf bs, off => listGet? bs off
  | .node lsz l r, off => if off < lsz then l.getByte? off else r.getByte? (off - lsz)

def fetchBytes (t : ByteCodeTree) : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, off =>
    match t.getByte? off with
    | none => []
    | some b => b :: fetchBytes t k (off + 1)

def fetchWindow16 (t : ByteCodeTree) (off : Nat) : List UInt8 := fetchBytes t 16 off

theorem fetchBytes_prefix :
    ∀ (pfx : List UInt8) (t : ByteCodeTree) (k off : Nat),
      pfx.length ≤ k →
      (∀ i, i < pfx.length → t.getByte? (off + i) = listGet? pfx i) →
      ∃ sfx, fetchBytes t k off = pfx ++ sfx
  | [], t, k, off, _, _ => ⟨fetchBytes t k off, rfl⟩
  | _ :: _, _, 0, _, hle, _ => nomatch hle
  | b :: bs, t, k + 1, off, hle, hget => by
    have h0 : t.getByte? off = some b := by
      have t0 := hget 0 (Nat.zero_lt_succ bs.length); rw [Nat.add_zero] at t0; exact t0
    have hle' : bs.length ≤ k := Nat.le_of_succ_le_succ hle
    have hget' : ∀ i, i < bs.length → t.getByte? ((off + 1) + i) = listGet? bs i := by
      intro i hi
      have ti := hget (i + 1) (Nat.succ_lt_succ hi)
      rw [Nat.add_assoc off 1 i, Nat.add_comm 1 i]; exact ti
    rcases fetchBytes_prefix bs t k (off + 1) hle' hget' with ⟨sfx, hsfx⟩
    refine ⟨sfx, ?_⟩; dsimp [fetchBytes]; rw [h0]; dsimp; rw [hsfx]

inductive SfiExitKind where
  | running
  | portalReturn
  | portalHostcall
  deriving DecidableEq, Repr

/-- Machine state with full 64-bit virtual `rip : BitVec 64` (never zero-based!). -/
structure RealX64State where
  rip      : BitVec 64
  regs     : Reg → BitVec 64
  flags    : RFlags
  mem      : ByteMem
  exitKind : SfiExitKind := .running
  fault    : Bool := false

structure X64ObjImage where
  code : ByteCodeTree

def evalAddr (s : RealX64State) (nextRip : BitVec 64) : MemAddr → BitVec 64
  | .baseDisp base none disp => s.regs base + disp
  | .baseDisp base (some (idx, scale)) disp =>
    s.regs base + s.regs idx * BitVec.ofNat 64 scale + disp
  | .ripRel disp => nextRip + disp

def aluVal64 (op : AluOp) (a b : BitVec 64) : BitVec 64 :=
  match op with
  | .add => a + b | .sub | .cmp => a - b | .xor => a ^^^ b
  | .and | .test => a &&& b | .or => a ||| b

def evalAluFlags64 (op : AluOp) (a b : BitVec 64) (nd : UndefFlags) : BitVec 64 × RFlags :=
  let res := aluVal64 op a b
  let pf := parity8 (byteOf64 res 0)
  let zf := res == 0#64
  let sf := res.msb
  match op with
  | .add =>
    (res, { cf := decide (a.toNat + b.toNat ≥ 2 ^ 64),
            pf, af := decide ((a &&& 0xF#64).toNat + (b &&& 0xF#64).toNat ≥ 16),
            zf, sf, of := (a.msb == b.msb) && (res.msb != a.msb) })
  | .sub | .cmp =>
    (res, { cf := decide (a.toNat < b.toNat),
            pf, af := decide ((a &&& 0xF#64).toNat < (b &&& 0xF#64).toNat),
            zf, sf, of := (a.msb != b.msb) && (res.msb != a.msb) })
  | .xor | .and | .or | .test =>
    (res, { cf := false, pf, af := nd.af, zf, sf, of := false })

def evalAluFlags32 (op : AluOp) (a32 b32 : BitVec 32) (nd : UndefFlags) : BitVec 64 × RFlags :=
  let res32 : BitVec 32 :=
    match op with
    | .add => a32 + b32 | .sub | .cmp => a32 - b32 | .xor => a32 ^^^ b32
    | .and | .test => a32 &&& b32 | .or => a32 ||| b32
  let res64 := res32.zeroExtend 64
  let pf := parity8 (BitVec.extractLsb' 0 8 res32)
  let zf := res32 == 0#32
  let sf := res32.msb
  match op with
  | .add =>
    (res64, { cf := decide (a32.toNat + b32.toNat ≥ 2 ^ 32),
              pf, af := decide ((a32 &&& 0xF#32).toNat + (b32 &&& 0xF#32).toNat ≥ 16),
              zf, sf, of := (a32.msb == b32.msb) && (res32.msb != a32.msb) })
  | .sub | .cmp =>
    (res64, { cf := decide (a32.toNat < b32.toNat),
              pf, af := decide ((a32 &&& 0xF#32).toNat < (b32 &&& 0xF#32).toNat),
              zf, sf, of := (a32.msb != b32.msb) && (res32.msb != a32.msb) })
  | .xor | .and | .or | .test =>
    (res64, { cf := false, pf, af := nd.af, zf, sf, of := false })

theorem evalAluFlags32_fst (op : AluOp) (a32 b32 : BitVec 32) (nd : UndefFlags) :
    ∃ r32 : BitVec 32, (evalAluFlags32 op a32 b32 nd).1 = r32.zeroExtend 64 := by
  cases op <;> exact ⟨_, rfl⟩

def evalShift64 (op : ShiftOp) (a : BitVec 64) (cnt : Nat) (oldF : RFlags) (nd : UndefFlags) :
    BitVec 64 × RFlags :=
  let c := cnt % 64
  if c == 0 then (a, oldF)
  else
    let res := match op with | .shl => a <<< c | .shr => a >>> c
    let cfBit := match op with | .shl => a.getLsbD (64 - c) | .shr => a.getLsbD (c - 1)
    let ofBit := if c == 1 then (match op with | .shl => res.msb != cfBit | .shr => a.msb) else nd.of
    (res, { cf := cfBit, pf := parity8 (byteOf64 res 0), af := nd.af,
            zf := res == 0#64, sf := res.msb, of := ofBit })

def sext64ValTo128 (v : BitVec 64) : BitVec 128 :=
  (if (v &&& 0x8000000000000000#64) != 0#64 then 0xFFFFFFFFFFFFFFFF#64 else 0#64) ++ v

def evalImul64 (a b : BitVec 64) (nd : UndefFlags) : BitVec 64 × RFlags :=
  let res := a * b
  let p128 : BitVec 128 := sext64ValTo128 a * sext64ValTo128 b
  let ovf : Bool := p128 != sext64ValTo128 res
  (res, { cf := ovf, pf := nd.pf, af := nd.af, zf := nd.zf, sf := nd.sf, of := ovf })

def evalCond (cc : CondCode) (f : RFlags) : Bool :=
  match cc with
  | .e => f.zf | .ne => !f.zf | .b => f.cf
  | .ae => !f.cf | .be => f.cf || f.zf | .a => !f.cf && !f.zf

def aluWritesDst : AluOp → Bool
  | .cmp | .test => false
  | _ => true

/-- Execute one decoded instruction under REAL x86-64 `[%rsp]`-popping semantics:
    `0xC3` (`ret`) reads `readMem64 s.mem (s.regs .rsp)` into `s.rip` and adds `8` to `%rsp`! -/
def execDecodedRealX64 (ins : X64Instr) (len : Nat) (nd : UndefFlags) (s : RealX64State) :
    RealX64State :=
  let nextRip := s.rip + BitVec.ofNat 64 len
  match ins with
  | .nop | .endbr64 => { s with rip := nextRip }
  | .movRR64 dst src => { s with rip := nextRip, regs := regUpd s.regs dst (s.regs src) }
  | .movRR32 dst src =>
    let zext := (BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64
    { s with rip := nextRip, regs := regUpd s.regs dst zext }
  | .movImm64 dst imm => { s with rip := nextRip, regs := regUpd s.regs dst imm }
  | .movImm32 dst imm32 => { s with rip := nextRip, regs := regUpd s.regs dst (imm32.zeroExtend 64) }
  | .load64 dst addr =>
    let ea := evalAddr s nextRip addr
    { s with rip := nextRip, regs := regUpd s.regs dst (readMem64 s.mem ea) }
  | .store64 addr src =>
    let ea := evalAddr s nextRip addr
    { s with rip := nextRip, mem := writeMem64 s.mem ea (s.regs src) }
  | .store32 addr src =>
    let ea := evalAddr s nextRip addr
    { s with rip := nextRip, mem := writeMem32 s.mem ea (s.regs src) }
  | .load32Zext dst addr =>
    let ea := evalAddr s nextRip addr
    { s with rip := nextRip, regs := regUpd s.regs dst (readMem32Zext64 s.mem ea) }
  | .load32Sext dst addr =>
    let ea := evalAddr s nextRip addr
    { s with rip := nextRip, regs := regUpd s.regs dst (readMem32Sext64 s.mem ea) }
  | .lea64 dst addr =>
    let ea := evalAddr s nextRip addr
    { s with rip := nextRip, regs := regUpd s.regs dst ea }
  | .aluRR64 op dst src =>
    let (res, fl) := evalAluFlags64 op (s.regs dst) (s.regs src) nd
    { s with rip := nextRip, regs := if aluWritesDst op then regUpd s.regs dst res else s.regs, flags := fl }
  | .aluImm64 op dst imm =>
    let (res, fl) := evalAluFlags64 op (s.regs dst) imm nd
    { s with rip := nextRip, regs := if aluWritesDst op then regUpd s.regs dst res else s.regs, flags := fl }
  | .aluRR32 op dst src =>
    let a32 := BitVec.extractLsb' 0 32 (s.regs dst)
    let b32 := BitVec.extractLsb' 0 32 (s.regs src)
    let (res64, fl) := evalAluFlags32 op a32 b32 nd
    { s with rip := nextRip, regs := if aluWritesDst op then regUpd s.regs dst res64 else s.regs, flags := fl }
  | .aluImm32 op dst imm32 =>
    let a32 := BitVec.extractLsb' 0 32 (s.regs dst)
    let (res64, fl) := evalAluFlags32 op a32 imm32 nd
    { s with rip := nextRip, regs := if aluWritesDst op then regUpd s.regs dst res64 else s.regs, flags := fl }
  | .shiftImm64 op dst cnt =>
    let (res, fl) := evalShift64 op (s.regs dst) cnt s.flags nd
    { s with rip := nextRip, regs := regUpd s.regs dst res, flags := fl }
  | .imulRR64 dst src =>
    let (res, fl) := evalImul64 (s.regs dst) (s.regs src) nd
    { s with rip := nextRip, regs := regUpd s.regs dst res, flags := fl }
  | .push64 src =>
    let rsp' := s.regs .rsp - 8#64
    { s with rip := nextRip, regs := regUpd s.regs .rsp rsp', mem := writeMem64 s.mem rsp' (s.regs src) }
  | .pop64 dst =>
    let rsp0 := s.regs .rsp
    let v := readMem64 s.mem rsp0
    { s with rip := nextRip, regs := regUpd (regUpd s.regs .rsp (rsp0 + 8#64)) dst v }
  | .leave64 =>
    let rbp0 := s.regs .rbp
    let saved := readMem64 s.mem rbp0
    { s with rip := nextRip, regs := regUpd (regUpd s.regs .rsp (rbp0 + 8#64)) .rbp saved }
  | .jmpRel rel => { s with rip := nextRip + rel }
  | .jccRel cc rel => if evalCond cc s.flags then { s with rip := nextRip + rel } else { s with rip := nextRip }
  | .jmpReg tgt => { s with rip := s.regs tgt }
  | .ret =>
    -- REAL x86-64 `0xC3` (`ret`): pops 64-bit QWORD `[%rsp]` directly into `rip`!
    let rsp0 := s.regs .rsp
    let retRip := readMem64 s.mem rsp0
    { s with rip := retRip, regs := regUpd s.regs .rsp (rsp0 + 8#64) }
  | .int3 => { s with fault := true }

/-- Raw unportaled real-x86 step at `[codeBase, codeBase + totalBytes)` (used for Fracture 1
    negative canaries showing what happens without Portal separation / PIC `%r15`). -/
def stepRawRealX64 (codeBase : BitVec 64) (totalBytes : Nat) (img : X64ObjImage)
    (nd : UndefFlags) (s : RealX64State) : RealX64State :=
  if s.exitKind != .running || s.fault then s
  else if !(natLeB codeBase.toNat s.rip.toNat && natLtB s.rip.toNat (codeBase.toNat + totalBytes)) then
    { s with fault := true }
  else
    let off := s.rip.toNat - codeBase.toNat
    match decodeX64 (fetchWindow16 img.code off) with
    | .fault _ => { s with fault := true }
    | .ok ins len => execDecodedRealX64 ins len nd s

def runRawRealX64 (codeBase : BitVec 64) (totalBytes : Nat) (img : X64ObjImage) :
    Nat → (Nat → UndefFlags) → RealX64State → RealX64State
  | 0, _, s => s
  | n + 1, nd, s =>
    runRawRealX64 codeBase totalBytes img n (fun k => nd (k + 1))
      (stepRawRealX64 codeBase totalBytes img (nd 0) s)

/-- PIC Portal-Separated Real x86-64 Small-Step Machine:
    - Landing on `codeBase + 0` (Portal Bundle 0) executes the loader-owned `ret` back to
      the host trampoline (`rip := [rsp]; rsp := rsp + 8; exitKind := .portalReturn`);
    - Landing on `codeBase + 32` (Portal Bundle 1) transitions to `sfi_hostcall_trampoline`
      (`exitKind := .portalHostcall` with unmodified host `rsp`);
    - All untrusted code offsets `64 ≤ off < totalBytes` execute `execDecodedRealX64`! -/
def stepPicPortalX64 (codeBase : BitVec 64) (totalBytes : Nat) (img : X64ObjImage)
    (nd : UndefFlags) (s : RealX64State) : RealX64State :=
  if s.exitKind != .running || s.fault then s
  else if s.rip == codeBase then
    let rsp0 := s.regs .rsp
    { s with rip := readMem64 s.mem rsp0,
             regs := regUpd s.regs .rsp (rsp0 + 8#64),
             exitKind := .portalReturn }
  else if s.rip == codeBase + 32#64 then
    { s with exitKind := .portalHostcall }
  else if !(natLeB (codeBase.toNat + 64) s.rip.toNat && natLtB s.rip.toNat (codeBase.toNat + totalBytes)) then
    { s with fault := true }
  else
    let off := s.rip.toNat - codeBase.toNat
    match decodeX64 (fetchWindow16 img.code off) with
    | .fault _ => { s with fault := true }
    | .ok ins len => execDecodedRealX64 ins len nd s

def runPicPortalX64 (codeBase : BitVec 64) (totalBytes : Nat) (img : X64ObjImage) :
    Nat → (Nat → UndefFlags) → RealX64State → RealX64State
  | 0, _, s => s
  | n + 1, nd, s =>
    runPicPortalX64 codeBase totalBytes img n (fun k => nd (k + 1))
      (stepPicPortalX64 codeBase totalBytes img (nd 0) s)

/-! ## Section 4: Fracture 1 Negative Canaries (`raw_ret_0xc3_rop_escape` & Null-Page Fault) -/

/-- Legacy single-bundle checker matching `ByteX86Sfi.checkSfiMacroStream`'s unsound `| .ret =>`
    clause (`mov eax, ecx; mov [r14 + rax*1], rdx; ret; nop...`). -/
def legacyAdmitsRawRet : X64Instr → Bool
  | .ret | .nop => true
  | _ => false

/-- Concrete 32-byte bundle admitted by the legacy surrogate-`ret` model:
    `89 c8` (`mov eax, ecx`), `49 89 14 06` (`mov [r14 + rax*1], rdx`), `c3` (`ret`),
    padded with 25 `0x90` NOPs to 32 bytes. -/
def legacyRopBundleBytes : List UInt8 :=
  [0x89, 0xC8, 0x49, 0x89, 0x14, 0x06, 0xC3] ++ List.replicate 25 0x90

def legacyRopImg : X64ObjImage := { code := .leaf legacyRopBundleBytes }

/-- Negative Canary 1A (`raw_ret_0xc3_rop_escape`):
    Under real `[%rsp]`-popping x86-64 semantics, executing the 3-instruction bundle
    `mov eax, ecx; mov [r14 + rax*1], rdx; ret` when `%rsp` resides in the writable
    sandbox stack (`arenaBase + 0x1000`) overwrites `[%rsp]` via an SFI-confined store
    and pops `sf.rip = 0x00007FFFDEAD0000` — escaping `[codeBase, codeBase + 32)`! -/
theorem raw_ret_0xc3_rop_escape :
    let codeBase  := 0x0000555555554000#64
    let arenaBase := 0x0000700000000000#64
    let guestRsp  := arenaBase + 0x1000#64
    let hostGadget := 0x00007FFFDEAD0000#64
    let regs0 : Reg → BitVec 64 := fun r =>
      if r == .r14 then arenaBase
      else if r == .rsp then guestRsp
      else if r == .rcx then 0x1000#64
      else if r == .rdx then hostGadget
      else 0#64
    let s0 : RealX64State := { rip := codeBase, regs := regs0, flags := {}, mem := fun _ => 0#8 }
    let sf := runRawRealX64 codeBase 32 legacyRopImg 3 (fun _ => {}) s0
    sf.fault = false ∧
    sf.rip = hostGadget ∧
    !(codeBase.toNat ≤ sf.rip.toNat ∧ sf.rip.toNat < codeBase.toNat + 32) := by
  decide

/-- Negative Canary 1B (`legacy_abs32_indirect_jmp_null_page_fault`):
    At any realistic Linux PIE/ASLR `codeBase ≥ mmap_min_addr` (`0x10000`), the unrelocated
    macro `25 e0 00 00 00; ff e0` (`and eax, 0xE0; jmp rax`) sets `rip = 0x0000000000000000`
    inside the unmapped null guard page `[0, 0x10000)`, faulting immediately on fetch! -/
def legacyAbsJmpImg : X64ObjImage :=
  { code := .leaf ([0x25, 0xE0, 0x00, 0x00, 0x00, 0xFF, 0xE0] ++ List.replicate 25 0x90) }

theorem legacy_abs32_indirect_jmp_null_page_fault :
    let codeBase := 0x0000555555554000#64
    let s0 : RealX64State := {
      rip := codeBase,
      regs := fun r => if r == .rax then 0x0000555555554000#64 else 0#64,
      flags := {},
      mem := fun _ => 0#8
    }
    let s2 := runRawRealX64 codeBase 256 legacyAbsJmpImg 2 (fun _ => {}) s0
    let s3 := runRawRealX64 codeBase 256 legacyAbsJmpImg 3 (fun _ => {}) s0
    s2.rip.toNat < 65536 ∧ s3.fault = true := by
  decide

/-! ## Section 5: Repaired PIC Multi-Function SFI Verifier (`checkSfiPicMultiFn`) -/

/-- Host-protected registers strictly read-only across all untrusted SFI bundles:
    `%rsp` (host stack), `%rbp, %rbx, %r12` (host CSRs / `SfiContext`),
    `%r14` (`arenaBase`), and `%r15` (`codeBase`). -/
def isPicHostProtectedReg : Reg → Bool
  | .rsp | .rbp | .rbx | .r12 | .r14 | .r15 => true
  | _ => false

/-- General SFI scratch registers (`rax, rcx, rdx, rsi, rdi, r8, r9, r10, r11`),
    excluding both host-protected registers and `%r13` (`guest_sp`, which may ONLY
    be written by 32-bit zero-extending operations!). -/
def isPicScratchReg : Reg → Bool
  | .rax | .rcx | .rdx | .rsi | .rdi | .r8 | .r9 | .r10 | .r11 => true
  | _ => false

/-- Registers permitted as 32-bit zero-extending destinations (`isPicScratchReg` OR `.r13`!). -/
def isPicZext32DstReg (r : Reg) : Bool :=
  isPicScratchReg r || (r == .r13)

theorem zext32Dst_ne_protected {dst r : Reg}
    (hdst : isPicZext32DstReg dst = true) (hprot : isPicHostProtectedReg r = true) :
    r ≠ dst := by
  intro heq; subst heq
  cases r <;> revert hdst hprot <;> decide

theorem scratch_ne_protected {dst r : Reg}
    (hscr : isPicScratchReg dst = true) (hprot : isPicHostProtectedReg r = true) :
    r ≠ dst := by
  intro heq; subst heq
  cases r <;> revert hscr hprot <;> decide

theorem scratch_ne_r13 {dst : Reg} (hscr : isPicScratchReg dst = true) : .r13 ≠ dst := by
  intro heq; subst heq; nomatch hscr

/-- Symmetric `±64 KiB` guard envelope around `[arenaBase, arenaBase + 4 GiB)`:
    total guarded span `[arenaBase - 65536, arenaBase + 4294967296 + 65536)`. -/
def SymmetricEnvBound : Nat := 65536 + 4294967296 + 65536

def OutsideSymmetricArena (arenaBase a : BitVec 64) : Prop :=
  SymmetricEnvBound ≤ (a - (arenaBase - 65536#64)).toNat

/-- Decidable check for signed displacement `disp ∈ [-65536, +65528]`:
    `0 ≤ (disp + 65536#64).toNat ≤ 131064`. -/
def dispSymOk (disp : BitVec 64) : Bool :=
  natLeB (disp + 65536#64).toNat 131064

theorem sfi_sym_mem_byte_inside
    (arenaBase idxVal disp : BitVec 64) (k : Nat)
    (hidx : idxVal.toNat < 4294967296)
    (hdisp : dispSymOk disp = true)
    (hk : k < 8) :
    ((arenaBase + idxVal * 1#64 + disp + BitVec.ofNat 64 k) - (arenaBase - 65536#64)).toNat <
      SymmetricEnvBound := by
  have hd : (disp + 65536#64).toNat ≤ 131064 := natLeB_true hdisp
  have hm1 : idxVal * 1#64 = idxVal := BitVec.mul_one idxVal
  let envBase := arenaBase - 65536#64
  have hbase : arenaBase = envBase + 65536#64 := (BitVec.sub_add_cancel (x := arenaBase) (y := 65536#64)).symm
  have halg : (arenaBase + idxVal * 1#64 + disp + BitVec.ofNat 64 k) - envBase =
      (idxVal + (disp + 65536#64)) + BitVec.ofNat 64 k := by
    rw [hm1, hbase]
    have hreord : envBase + 65536#64 + idxVal + disp + BitVec.ofNat 64 k =
        envBase + ((idxVal + (disp + 65536#64)) + BitVec.ofNat 64 k) := by
      rw [BitVec.add_assoc envBase 65536#64 idxVal,
          BitVec.add_comm 65536#64 idxVal,
          BitVec.add_assoc envBase (idxVal + 65536#64) disp,
          BitVec.add_assoc idxVal 65536#64 disp,
          BitVec.add_comm 65536#64 disp,
          BitVec.add_assoc envBase (idxVal + (disp + 65536#64)) (BitVec.ofNat 64 k)]
    rw [hreord, BitVec.add_comm envBase _, BitVec.add_sub_cancel]
  rw [halg]
  have hsum1 : idxVal.toNat + (disp + 65536#64).toNat < 4294967296 + 131064 :=
    Nat.add_lt_add_of_lt_of_le hidx hd
  have hsum1_64 : idxVal.toNat + (disp + 65536#64).toNat < 2 ^ 64 :=
    Nat.lt_trans hsum1 (by decide)
  have hsum2 : idxVal.toNat + (disp + 65536#64).toNat + k < (4294967296 + 131064) + 8 :=
    Nat.add_lt_add hsum1 hk
  have hsum2_bound : idxVal.toNat + (disp + 65536#64).toNat + k < SymmetricEnvBound := hsum2
  have hsum2_64 : idxVal.toNat + (disp + 65536#64).toNat + k < 2 ^ 64 :=
    Nat.lt_trans hsum2_bound (by decide)
  have hk64 : k < 2 ^ 64 := Nat.lt_trans hk (by decide)
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hsum1_64, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hsum2_64]
  exact hsum2_bound

theorem sfi_store64_preserves_outside_sym_arena
    (m : ByteMem) (arenaBase idxVal disp val a : BitVec 64)
    (hidx : idxVal.toNat < 4294967296)
    (hdisp : dispSymOk disp = true)
    (hout : OutsideSymmetricArena arenaBase a) :
    writeMem64 m (arenaBase + idxVal * 1#64 + disp) val a = m a := by
  apply writeMem64_byte_ne
  intro k hk heq
  subst heq
  exact Nat.not_lt_of_ge hout (sfi_sym_mem_byte_inside arenaBase idxVal disp k hidx hdisp hk)

theorem sfi_store32_preserves_outside_sym_arena
    (m : ByteMem) (arenaBase idxVal disp val a : BitVec 64)
    (hidx : idxVal.toNat < 4294967296)
    (hdisp : dispSymOk disp = true)
    (hout : OutsideSymmetricArena arenaBase a) :
    writeMem32 m (arenaBase + idxVal * 1#64 + disp) val a = m a := by
  apply writeMem32_byte_ne
  intro k hk heq
  subst heq
  exact Nat.not_lt_of_ge hout (sfi_sym_mem_byte_inside arenaBase idxVal disp k hidx hdisp hk)

/-- Standalone 1-instruction operations admitted in PIC multi-function SFI:
    - Pure ALU/move/shift/lea/imul operations writing ONLY `isPicScratchReg` (64-bit)
      or `isPicZext32DstReg` (32-bit zero-extending, which includes `%r13`!);
    - Direct guest-stack loads and stores `[r14 + r13*1 + disp]` (`dispSymOk disp`),
      sound as single instructions because `(s.regs .r13).toNat < 2^32` holds at every step! -/
def isStandalonePicSfiOp : X64Instr → Bool
  | .nop | .endbr64 => true
  | .movRR64 dst _ | .movImm64 dst _ | .lea64 dst _
  | .shiftImm64 _ dst _ | .imulRR64 dst _ => isPicScratchReg dst
  | .movRR32 dst _ | .movImm32 dst _ => isPicZext32DstReg dst
  | .aluRR64 op dst _ | .aluImm64 op dst _ =>
    if aluWritesDst op then isPicScratchReg dst else true
  | .aluRR32 op dst _ | .aluImm32 op dst _ =>
    if aluWritesDst op then isPicZext32DstReg dst else true
  | .store64 (.baseDisp .r14 (some (.r13, 1)) disp) _
  | .store32 (.baseDisp .r14 (some (.r13, 1)) disp) _ => dispSymOk disp
  | .load64 dst (.baseDisp .r14 (some (.r13, 1)) disp)
  | .load32Sext dst (.baseDisp .r14 (some (.r13, 1)) disp) =>
    isPicScratchReg dst && dispSymOk disp
  | .load32Zext dst (.baseDisp .r14 (some (.r13, 1)) disp) =>
    isPicZext32DstReg dst && dispSymOk disp
  | _ => false

/-- Second instruction of a 2-instruction general arena memory macro `mov idx32, src32` + `mem`. -/
def isSandboxedPicMem2nd (idx : Reg) : X64Instr → Bool
  | .store64 (.baseDisp .r14 (some (idx', 1)) disp) _
  | .store32 (.baseDisp .r14 (some (idx', 1)) disp) _ =>
    (idx' == idx) && dispSymOk disp
  | .load64 dst (.baseDisp .r14 (some (idx', 1)) disp)
  | .load32Sext dst (.baseDisp .r14 (some (idx', 1)) disp) =>
    isPicScratchReg dst && (idx' == idx) && dispSymOk disp
  | .load32Zext dst (.baseDisp .r14 (some (idx', 1)) disp) =>
    isPicZext32DstReg dst && (idx' == idx) && dispSymOk disp
  | _ => false

def peekPicMem2nd (idx : Reg) (rem1 : List UInt8) : Option (X64Instr × Nat) :=
  match decodeX64 rem1 with
  | .ok ins2 len2 =>
    let pfx2 := rem1.take len2
    if isSandboxedPicMem2nd idx ins2 && !(len2 == 0) && !decide (lenTR rem1 < len2) &&
       (decodeX64 pfx2 == .ok ins2 pfx2.length) then some (ins2, len2)
    else none
  | .fault _ => none

/-- Peek instructions 2 and 3 of the 3-instruction PIC indirect jump/return macro:
    `and r11d, mask32` + `lea r11, [r15 + r11*1 + 0]` + `jmp r11`. -/
def isPicLeaR15R11 : X64Instr → Bool
  | .lea64 .r11 (.baseDisp .r15 (some (.r11, 1)) 0#64) => true
  | _ => false

def isPicJmpR11 : X64Instr → Bool
  | .jmpReg .r11 => true
  | _ => false

def peekPicJmp2nd3rd (rem1 : List UInt8) : Option (Nat × Nat) :=
  match decodeX64 rem1 with
  | .ok ins2 len2 =>
    let pfx2 := rem1.take len2
    let rem2 := rem1.drop len2
    if isPicLeaR15R11 ins2 && !(len2 == 0) && !decide (lenTR rem1 < len2) &&
       (decodeX64 pfx2 == .ok ins2 pfx2.length) then
      match decodeX64 rem2 with
      | .ok ins3 len3 =>
        let pfx3 := rem2.take len3
        if isPicJmpR11 ins3 && !(len3 == 0) && !decide (lenTR rem2 < len3) &&
           (decodeX64 pfx3 == .ok ins3 pfx3.length) then some (len2, len3)
        else none
      | .fault _ => none
    else none
  | .fault _ => none

def sfiPicJmpTarget (bBase off len1 : Nat) (rel : BitVec 64) : Nat :=
  (BitVec.ofNat 64 (bBase + off + len1) + rel).toNat

def sfiPicJmpTargetOk (totalBytes bBase off len1 : Nat) (rel : BitVec 64) : Bool :=
  natLtB (sfiPicJmpTarget bBase off len1 rel) totalBytes &&
  natEqB (sfiPicJmpTarget bBase off len1 rel % 32) 0

/-- Verifies a single 32-byte untrusted bundle (`bBase ≥ 64`):
    Note that `.ret` (`0xC3`), `push`, `pop`, and `leave` are UNCONDITIONALLY REJECTED! -/
def checkSfiPicMacroStream (totalBytes bBase : Nat) (isLast : Bool) :
    Nat → Nat → List UInt8 → Bool
  | _, off, [] => decide (off = 32)
  | 0, _, _ :: _ => false
  | fuel + 1, off, bs =>
    match decodeX64 bs with
    | .fault _ => false
    | .ok ins1 len1 =>
      let pfx1 := bs.take len1
      let rem1 := bs.drop len1
      if len1 == 0 || decide (lenTR bs < len1) || decide (32 < off + len1) ||
         (decodeX64 pfx1 != .ok ins1 pfx1.length) then false
      else
        match ins1 with
        | .jmpRel rel =>
          if sfiPicJmpTargetOk totalBytes bBase off len1 rel then
            checkSfiPicMacroStream totalBytes bBase isLast fuel (off + len1) rem1
          else false
        | .jccRel _ rel =>
          if sfiPicJmpTargetOk totalBytes bBase off len1 rel &&
             !(isLast && decide (off + len1 = 32)) then
            checkSfiPicMacroStream totalBytes bBase isLast fuel (off + len1) rem1
          else false
        | .movRR32 idx dstSrc =>
          if isPicScratchReg idx then
            match peekPicMem2nd idx rem1 with
            | some (_, len2) =>
              if decide (32 < off + len1 + len2) || (isLast && decide (off + len1 + len2 = 32)) then
                false
              else
                checkSfiPicMacroStream totalBytes bBase isLast fuel (off + len1 + len2) (rem1.drop len2)
            | none =>
              if isStandalonePicSfiOp (.movRR32 idx dstSrc) && !(isLast && decide (off + len1 = 32)) then
                checkSfiPicMacroStream totalBytes bBase isLast fuel (off + len1) rem1
              else false
          else if isStandalonePicSfiOp (.movRR32 idx dstSrc) && !(isLast && decide (off + len1 = 32)) then
            checkSfiPicMacroStream totalBytes bBase isLast fuel (off + len1) rem1
          else false
        | .aluImm32 op dst mask =>
          if op == .and && dst == .r11 then
            match peekPicJmp2nd3rd rem1 with
            | some (len2, len3) =>
              if (mask &&& 31#32) == 0#32 && natLtB mask.toNat totalBytes &&
                 !decide (32 < off + len1 + len2 + len3) then
                checkSfiPicMacroStream totalBytes bBase isLast fuel
                  (off + len1 + len2 + len3) ((rem1.drop len2).drop len3)
              else false
            | none =>
              if isStandalonePicSfiOp (.aluImm32 op dst mask) && !(isLast && decide (off + len1 = 32)) then
                checkSfiPicMacroStream totalBytes bBase isLast fuel (off + len1) rem1
              else false
          else if isStandalonePicSfiOp (.aluImm32 op dst mask) && !(isLast && decide (off + len1 = 32)) then
            checkSfiPicMacroStream totalBytes bBase isLast fuel (off + len1) rem1
          else false
        | other =>
          if isStandalonePicSfiOp other && !(isLast && decide (off + len1 = 32)) then
            checkSfiPicMacroStream totalBytes bBase isLast fuel (off + len1) rem1
          else false

/-- Checks loader-owned Portal Bundle 0 (`0x00`: `ret` + NOPs) and Portal Bundle 1 (`0x20`: `jmpRel` + NOPs),
    and enforces `checkSfiPicMacroStream` on every untrusted bundle `bBase ≥ 64`! -/
def checkPortal0Bundle (bs : List UInt8) : Bool :=
  decide (lenTR bs = 32) && (listGet? bs 0 == some 0xC3)

def checkPortal1Bundle (bs : List UInt8) : Bool :=
  decide (lenTR bs = 32) &&
  (listGet? bs 0 == some 0xE9 || listGet? bs 0 == some 0xEB)

def checkOnePicBundle (totalBytes base : Nat) (bundle : List UInt8) : Bool :=
  if base == 0 then checkPortal0Bundle bundle
  else if base == 32 then checkPortal1Bundle bundle
  else checkSfiPicMacroStream totalBytes base (base + 32 == totalBytes) 32 0 bundle

def checkSfiPicLeafBundles (totalBytes : Nat) : Nat → Nat → List UInt8 → Bool
  | _, base, [] => natEqB (base % 32) 0
  | 0, _, _ :: _ => false
  | fuel + 1, base, bs =>
    natEqB (base % 32) 0 &&
    natLeB 32 (lenTR bs) &&
    natLeB (base + 32) totalBytes &&
    checkOnePicBundle totalBytes base (bs.take 32) &&
    checkSfiPicLeafBundles totalBytes fuel (base + 32) (bs.drop 32)

def checkSfiPicSubtree (totalBytes base endOff : Nat) : ByteCodeTree → Bool
  | .leaf bs =>
    let sz := lenTR bs
    natLtB base endOff &&
    natLeB endOff totalBytes &&
    natEqB (base + sz) endOff &&
    natEqB (sz % 32) 0 &&
    checkSfiPicLeafBundles totalBytes (sz / 32) base bs
  | .node lsz l r =>
    natEqB (lsz % 32) 0 &&
    natLeB (base + lsz) endOff &&
    checkSfiPicSubtree totalBytes base (base + lsz) l &&
    checkSfiPicSubtree totalBytes (base + lsz) endOff r

def checkSfiPicMultiFn (totalBytes : Nat) (img : X64ObjImage) : Bool :=
  natLeB 96 totalBytes &&
  natEqB (totalBytes % 32) 0 &&
  checkSfiPicSubtree totalBytes 0 totalBytes img.code

/-- Confirm `checkSfiPicMultiFn` REJECTS an untrusted bundle containing raw `0xC3` (`ret`)! -/
def rejectedUntrustedRetImg : X64ObjImage :=
  { code := .leaf (
      ([0xC3] ++ List.replicate 31 0x90) ++
      ([0xE9, 0x00, 0x00, 0x00, 0x00] ++ List.replicate 27 0x90) ++
      legacyRopBundleBytes) }

theorem checkSfiPicMultiFn_rejects_untrusted_ret :
    checkSfiPicMultiFn 96 rejectedUntrustedRetImg = false := rfl

/-! ## Section 6: Inductive Multi-Phase Soundness Proof (`checkSfiPicMultiFn_sound`) -/

def AllUntrustedBundlesValid (totalBytes : Nat) (code : ByteCodeTree) : Prop :=
  96 ≤ totalBytes ∧ totalBytes % 32 = 0 ∧
  ∀ bBase, 64 ≤ bBase → bBase < totalBytes → bBase % 32 = 0 →
    ∃ bundle : List UInt8,
      bundle.length = 32 ∧
      (∀ i, i < 32 → code.getByte? (bBase + i) = listGet? bundle i) ∧
      checkSfiPicMacroStream totalBytes bBase (bBase + 32 == totalBytes) 32 0 bundle = true

theorem mod32_step_le {x y : Nat} (hx : x % 32 = 0) (hy : y % 32 = 0) (hlt : x < y) :
    x + 32 ≤ y := by
  have hdx : x = (x / 32) * 32 := ((Nat.dvd_iff_div_mul_eq x 32).mp (Nat.dvd_of_mod_eq_zero hx)).symm
  have hdy : y = (y / 32) * 32 := ((Nat.dvd_iff_div_mul_eq y 32).mp (Nat.dvd_of_mod_eq_zero hy)).symm
  have hq_lt : x / 32 < y / 32 := by
    cases hle : decide (y / 32 ≤ x / 32) with
    | false => exact Nat.not_le.mp (of_decide_eq_false hle)
    | true =>
      have hm := Nat.mul_le_mul_right 32 (of_decide_eq_true hle)
      rw [← hdx, ← hdy] at hm
      exact False.elim (Nat.not_lt_of_ge hm hlt)
  have hq_succ : (x / 32 + 1) * 32 ≤ (y / 32) * 32 := Nat.mul_le_mul_right 32 hq_lt
  rw [Nat.add_mul, Nat.one_mul, ← hdx, ← hdy] at hq_succ
  exact hq_succ

theorem add_mod32_zero {a b : Nat} (ha : a % 32 = 0) (hb : b % 32 = 0) : (a + b) % 32 = 0 := by
  rw [Nat.add_mod, ha, hb]

theorem bnot_eq_true_imp_false {b : Bool} (h : (!b) = true) : b = false := by
  cases b with | false => rfl | true => nomatch h

theorem listGet?_take {α : Type} :
    ∀ (n : Nat) (xs : List α) (i : Nat), i < n → listGet? (xs.take n) i = listGet? xs i
  | 0, _, _, hi => nomatch hi
  | _ + 1, [], _, _ => rfl
  | _ + 1, _ :: _, 0, _ => rfl
  | n + 1, _ :: xs, i + 1, hi => listGet?_take n xs i (Nat.lt_of_succ_lt_succ hi)

theorem listGet?_drop {α : Type} :
    ∀ (n : Nat) (xs : List α) (i : Nat), listGet? (xs.drop n) i = listGet? xs (n + i)
  | 0, xs, i => by rw [List.drop_zero, Nat.zero_add]
  | n + 1, [], i => by
    have hnone : ∀ k, listGet? ([] : List α) k = none := fun k => by cases k <;> rfl
    rw [List.drop_nil, hnone, hnone]
  | n + 1, x :: xs, i => by
    show listGet? (xs.drop n) i = listGet? (x :: xs) ((n + 1) + i)
    rw [Nat.add_assoc, Nat.add_comm 1 i, ← Nat.add_assoc]
    exact listGet?_drop n xs i

theorem checkSfiPicLeafBundles_spec (totalBytes : Nat) :
    ∀ (fuel base : Nat) (bs : List UInt8) (b : Nat),
      checkSfiPicLeafBundles totalBytes fuel base bs = true →
      64 ≤ b → base ≤ b → b < base + bs.length → b % 32 = 0 →
      ∃ bundle : List UInt8,
        bundle.length = 32 ∧
        (∀ i, i < 32 → listGet? bs ((b - base) + i) = listGet? bundle i) ∧
        checkSfiPicMacroStream totalBytes b (b + 32 == totalBytes) 32 0 bundle = true
  | _, base, [], b, _, _, hge, hlt, _ => by
    rw [List.length_nil, Nat.add_zero] at hlt
    exact False.elim (Nat.lt_irrefl b (Nat.lt_of_lt_of_le hlt hge))
  | 0, _, _ :: _, _, hchk, _, _, _, _ => nomatch hchk
  | fuel + 1, base, c :: cs, b, hchk, hb64, hge, hlt, hmod => by
    dsimp [checkSfiPicLeafBundles] at hchk
    have c1 := Bool.and_eq_true_iff.mp hchk
    have c2 := Bool.and_eq_true_iff.mp c1.1
    have c3 := Bool.and_eq_true_iff.mp c2.1
    have c4 := Bool.and_eq_true_iff.mp c3.1
    have hbase_mod : base % 32 = 0 := natEqB_true c4.1
    have hlen32 : 32 ≤ (c :: cs).length := by
      have ht := natLeB_true c4.2; rw [lenTR_eq_length] at ht; exact ht
    cases h_eq : decide (b = base) with
    | true =>
      have hb : b = base := of_decide_eq_true h_eq; subst hb
      have hne0 : (b == 0) = false := by
        cases h0 : (b == 0) with
        | false => rfl
        | true => have := of_decide_eq_true h0; subst this; nomatch hb64
      have hne32 : (b == 32) = false := by
        cases h32 : (b == 32) with
        | false => rfl
        | true => have := of_decide_eq_true h32; subst this; nomatch hb64
      have hmacro : checkSfiPicMacroStream totalBytes b (b + 32 == totalBytes) 32 0 ((c :: cs).take 32) = true := by
        have ho := c2.2; dsimp [checkOnePicBundle] at ho; rw [hne0, hne32] at ho; exact ho
      refine ⟨(c :: cs).take 32, List.length_take_of_le hlen32, ?_, hmacro⟩
      intro i hi; rw [Nat.sub_self, Nat.zero_add, listGet?_take 32 (c :: cs) i hi]
    | false =>
      have hne : b ≠ base := of_decide_eq_false h_eq
      have hgt : base < b := Nat.lt_of_le_of_ne hge hne.symm
      have hb32 : base + 32 ≤ b := mod32_step_le hbase_mod hmod hgt
      have hlt_drop : b < (base + 32) + ((c :: cs).drop 32).length := by
        rw [List.length_drop, Nat.add_assoc, Nat.add_sub_of_le hlen32]; exact hlt
      rcases checkSfiPicLeafBundles_spec totalBytes fuel (base + 32) ((c :: cs).drop 32) b
        c1.2 hb64 hb32 hlt_drop hmod with ⟨bundle, hblen, hbget, hbchk⟩
      refine ⟨bundle, hblen, ?_, hbchk⟩
      intro i hi
      rw [← hbget i hi, listGet?_drop 32 (c :: cs) ((b - (base + 32)) + i)]
      have hd : 32 + (b - (base + 32)) = b - base := by
        have h1 : (base + 32) + (b - (base + 32)) = b := Nat.add_sub_of_le hb32
        have h2 : base + (32 + (b - (base + 32))) = b := by rw [← Nat.add_assoc, h1]
        have h3 := congrArg (fun x => x - base) h2
        rw [Nat.add_sub_cancel_left] at h3; exact h3
      rw [← Nat.add_assoc, hd]

theorem checkSfiPicSubtree_spec (totalBytes : Nat) :
    ∀ (t : ByteCodeTree) (base endOff b : Nat),
      base % 32 = 0 →
      checkSfiPicSubtree totalBytes base endOff t = true →
      64 ≤ b → base ≤ b → b < endOff → b % 32 = 0 →
      ∃ bundle : List UInt8,
        bundle.length = 32 ∧
        (∀ i, i < 32 → t.getByte? ((b - base) + i) = listGet? bundle i) ∧
        checkSfiPicMacroStream totalBytes b (b + 32 == totalBytes) 32 0 bundle = true
  | .leaf bs, base, endOff, b, _, hchk, hb64, hge, hlt, hmod => by
    dsimp [checkSfiPicSubtree] at hchk
    have c1 := Bool.and_eq_true_iff.mp hchk
    have c2 := Bool.and_eq_true_iff.mp c1.1
    have c3 := Bool.and_eq_true_iff.mp c2.1
    have hend : base + bs.length = endOff := by
      have ht := natEqB_true c3.2; rw [lenTR_eq_length] at ht; exact ht
    rw [← hend] at hlt
    have hchk_l : checkSfiPicLeafBundles totalBytes (bs.length / 32) base bs = true := by
      have ht := c1.2; rw [lenTR_eq_length] at ht; exact ht
    exact checkSfiPicLeafBundles_spec totalBytes (bs.length / 32) base bs b hchk_l hb64 hge hlt hmod
  | .node lsz l r, base, endOff, b, hbase_mod, hchk, hb64, hge, hlt, hmod => by
    dsimp [checkSfiPicSubtree] at hchk
    have c1 := Bool.and_eq_true_iff.mp hchk
    have c2 := Bool.and_eq_true_iff.mp c1.1
    have c3 := Bool.and_eq_true_iff.mp c2.1
    have hlsz_mod : lsz % 32 = 0 := natEqB_true c3.1
    have hsplit_mod : (base + lsz) % 32 = 0 := add_mod32_zero hbase_mod hlsz_mod
    cases hleft : decide (b < base + lsz) with
    | true =>
      have hbl : b < base + lsz := of_decide_eq_true hleft
      have hb32 : b + 32 ≤ base + lsz := mod32_step_le hmod hsplit_mod hbl
      rcases checkSfiPicSubtree_spec totalBytes l base (base + lsz) b hbase_mod c2.2 hb64 hge hbl hmod with
        ⟨bundle, hblen, hbget, hbchk⟩
      refine ⟨bundle, hblen, ?_, hbchk⟩
      intro i hi
      have hidx_lt : (b - base) + i < lsz := by
        have hb_eq : base + (b - base) = b := Nat.add_sub_of_le hge
        have hsum_lt : base + ((b - base) + i) < base + lsz := by
          rw [← Nat.add_assoc, hb_eq]
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi b) hb32
        exact Nat.lt_of_add_lt_add_left hsum_lt
      dsimp [ByteCodeTree.getByte?]; simp only [hidx_lt, ite_true]; exact hbget i hi
    | false =>
      have hbge : base + lsz ≤ b := Nat.not_lt.mp (of_decide_eq_false hleft)
      rcases checkSfiPicSubtree_spec totalBytes r (base + lsz) endOff b hsplit_mod c1.2 hb64 hbge hlt hmod with
        ⟨bundle, hblen, hbget, hbchk⟩
      refine ⟨bundle, hblen, ?_, hbchk⟩
      intro i hi
      have hidx_ge : lsz ≤ (b - base) + i :=
        Nat.le_trans (Nat.le_sub_of_add_le' hbge) (Nat.le_add_right _ i)
      have hnlt : ¬ ((b - base) + i < lsz) := Nat.not_lt_of_ge hidx_ge
      dsimp [ByteCodeTree.getByte?]; simp only [hnlt, ite_false]
      have hsub_eq : ((b - base) + i) - lsz = (b - (base + lsz)) + i := by
        rw [Nat.sub_add_comm (Nat.le_sub_of_add_le' hbge), Nat.sub_sub]
      rw [hsub_eq]; exact hbget i hi

theorem checkSfiPicMultiFn_bundlesValid {totalBytes : Nat} {img : X64ObjImage}
    (hok : checkSfiPicMultiFn totalBytes img = true) :
    AllUntrustedBundlesValid totalBytes img.code := by
  dsimp [checkSfiPicMultiFn] at hok
  have c1 := Bool.and_eq_true_iff.mp hok
  have c2 := Bool.and_eq_true_iff.mp c1.1
  refine ⟨natLeB_true c2.1, natEqB_true c2.2, ?_⟩
  intro b hb64 hblt hbmod
  rcases checkSfiPicSubtree_spec totalBytes img.code 0 totalBytes b rfl c1.2 hb64 (Nat.zero_le b) hblt hbmod with
    ⟨bundle, hblen, hbget, hbchk⟩
  refine ⟨bundle, hblen, ?_, hbchk⟩
  intro i hi; have h0 : b - 0 = b := Nat.sub_zero b; rw [← h0]; exact hbget i hi

/-- Core PIC host-safety state invariant:
    - Zero faults (`fault = false`);
    - `%r15 = codeBase`, `%r14 = arenaBase`, and inductive 32-bit guest-stack bound `(regs .r13).toNat < 2^32`;
    - Every byte outside `[arenaBase - 64 KiB, arenaBase + 4 GiB + 64 KiB)` equals `initMem`;
    - While `.running` or `.portalHostcall`: all host-protected registers (`%rsp, %rbp, %rbx, %r12, %r14, %r15`)
      equal `initRegs`;
    - Upon `.portalReturn` (Portal Bundle 0 `ret`): `rip = readMem64 initMem (initRegs .rsp)`,
      `regs .rsp = initRegs .rsp + 8#64`, and all non-`rsp` host-protected registers equal `initRegs`! -/
def SfiPicCoreSafe (codeBase arenaBase : BitVec 64)
    (initRegs : Reg → BitVec 64) (initMem : ByteMem) (s : RealX64State) : Prop :=
  s.fault = false ∧
  s.regs .r15 = codeBase ∧
  s.regs .r14 = arenaBase ∧
  (s.regs .r13).toNat < 4294967296 ∧
  (∀ a, OutsideSymmetricArena arenaBase a → s.mem a = initMem a) ∧
  match s.exitKind with
  | .running | .portalHostcall =>
    s.regs .rsp = initRegs .rsp ∧
    (∀ r, isPicHostProtectedReg r = true → s.regs r = initRegs r)
  | .portalReturn =>
    s.rip = readMem64 initMem (initRegs .rsp) ∧
    s.regs .rsp = initRegs .rsp + 8#64 ∧
    (∀ r, isPicHostProtectedReg r = true → r ≠ .rsp → s.regs r = initRegs r)

/-- Multi-phase small-step control invariant for PIC multi-function SFI when `exitKind == .running`. -/
inductive SfiPicPhase (codeBase : BitVec 64) (totalBytes : Nat) (img : X64ObjImage) (s : RealX64State) : Prop where
  | atPortal0 (hrip0 : s.rip = codeBase)
  | atPortal1 (hrip1 : s.rip = codeBase + 32#64)
  | atMacro (bBase fuel off : Nat) (rem : List UInt8)
      (hb64 : 64 ≤ bBase)
      (hb_lt : bBase < totalBytes)
      (hb_mod : bBase % 32 = 0)
      (hb_le : bBase + 32 ≤ totalBytes)
      (hoff_lt : off < 32)
      (hrip : s.rip = codeBase + BitVec.ofNat 64 (bBase + off))
      (hlen : off + rem.length = 32)
      (hbytes : ∀ i, i < rem.length → img.code.getByte? ((bBase + off) + i) = listGet? rem i)
      (hchk : checkSfiPicMacroStream totalBytes bBase (bBase + 32 == totalBytes) fuel off rem = true)
  | pendingMem (bBase fuel nextOff curOff : Nat) (idx : Reg) (ins2 : X64Instr) (pfx2 rem2 : List UInt8)
      (hidx_lt : (s.regs idx).toNat < 4294967296)
      (hb64 : 64 ≤ bBase)
      (hb_lt : bBase < totalBytes)
      (hb_mod : bBase % 32 = 0)
      (hb_le : bBase + 32 ≤ totalBytes)
      (hcur64 : 64 ≤ curOff)
      (hcur_lt : curOff < totalBytes)
      (hrip : s.rip = codeBase + BitVec.ofNat 64 curOff)
      (hmem2 : isSandboxedPicMem2nd idx ins2 = true)
      (hdec2 : decodeX64 pfx2 = .ok ins2 pfx2.length)
      (hwin2 : ∀ i, i < pfx2.length → img.code.getByte? (curOff + i) = listGet? pfx2 i)
      (hnrip : curOff + pfx2.length = bBase + nextOff)
      (hnlen : nextOff + rem2.length = 32)
      (hnlast : ((bBase + 32 == totalBytes) && decide (nextOff = 32)) = false)
      (hnbytes : ∀ i, i < rem2.length → img.code.getByte? ((bBase + nextOff) + i) = listGet? rem2 i)
      (hnchk : checkSfiPicMacroStream totalBytes bBase (bBase + 32 == totalBytes) fuel nextOff rem2 = true)
  | pendingPicLea (curOff leaLen tgtOff : Nat) (pfx2 pfx3 : List UInt8)
      (hr11_eq : s.regs .r11 = BitVec.ofNat 64 tgtOff)
      (htgt_lt : tgtOff < totalBytes)
      (htgt_mod : tgtOff % 32 = 0)
      (hcur64 : 64 ≤ curOff)
      (hcur_lt : curOff < totalBytes)
      (hnext64 : 64 ≤ curOff + leaLen)
      (hnext_lt : curOff + leaLen < totalBytes)
      (hrip : s.rip = codeBase + BitVec.ofNat 64 curOff)
      (hdec2 : decodeX64 pfx2 = .ok (.lea64 .r11 (.baseDisp .r15 (some (.r11, 1)) 0#64)) leaLen)
      (hpfx2_len : pfx2.length = leaLen)
      (hwin2 : ∀ i, i < pfx2.length → img.code.getByte? (curOff + i) = listGet? pfx2 i)
      (hdec3 : decodeX64 pfx3 = .ok (.jmpReg .r11) pfx3.length)
      (hwin3 : ∀ i, i < pfx3.length → img.code.getByte? ((curOff + leaLen) + i) = listGet? pfx3 i)
  | pendingPicJmp (curOff tgtOff : Nat) (pfx3 : List UInt8)
      (hr11_eq : s.regs .r11 = codeBase + BitVec.ofNat 64 tgtOff)
      (htgt_lt : tgtOff < totalBytes)
      (htgt_mod : tgtOff % 32 = 0)
      (hcur64 : 64 ≤ curOff)
      (hcur_lt : curOff < totalBytes)
      (hrip : s.rip = codeBase + BitVec.ofNat 64 curOff)
      (hdec3 : decodeX64 pfx3 = .ok (.jmpReg .r11) pfx3.length)
      (hwin3 : ∀ i, i < pfx3.length → img.code.getByte? (curOff + i) = listGet? pfx3 i)

def SfiPicMachineInv (codeBase arenaBase : BitVec 64) (totalBytes : Nat) (img : X64ObjImage)
    (initRegs : Reg → BitVec 64) (initMem : ByteMem) (s : RealX64State) : Prop :=
  SfiPicCoreSafe codeBase arenaBase initRegs initMem s ∧
  (s.exitKind = .running → SfiPicPhase codeBase totalBytes img s)

theorem codeBase_add_off_toNat {codeBase : BitVec 64} {totalBytes off : Nat}
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (hoff : off < totalBytes) :
    (codeBase + BitVec.ofNat 64 off).toNat = codeBase.toNat + off := by
  have hoff64 : off < 2 ^ 64 := Nat.lt_trans hoff (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hfit)
  have hsum64 : codeBase.toNat + off < 2 ^ 64 := Nat.lt_trans (Nat.add_lt_add_left hoff _) hfit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64, Nat.mod_eq_of_lt hsum64]

theorem untrusted_off_portal_flags {codeBase : BitVec 64} {totalBytes off : Nat}
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (h64 : 64 ≤ off) (hlt : off < totalBytes) :
    let rip := codeBase + BitVec.ofNat 64 off
    (rip == codeBase) = false ∧
    (rip == codeBase + 32#64) = false ∧
    (natLeB (codeBase.toNat + 64) rip.toNat && natLtB rip.toNat (codeBase.toNat + totalBytes)) = true ∧
    rip.toNat - codeBase.toNat = off := by
  have htn := codeBase_add_off_toNat hfit hlt
  have hpos96 : 32 < totalBytes :=
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide : 32 < 64) h64) (Nat.le_of_lt hlt)
  have htn0 : (codeBase + BitVec.ofNat 64 0).toNat = codeBase.toNat := by
    have h := codeBase_add_off_toNat hfit (Nat.lt_trans (by decide : 0 < 32) hpos96)
    rw [Nat.add_zero] at h; exact h
  have htn32 : (codeBase + 32#64).toNat = codeBase.toNat + 32 :=
    codeBase_add_off_toNat hfit hpos96
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases heq : (codeBase + BitVec.ofNat 64 off == codeBase) with
    | false => rfl
    | true =>
      have hv := congrArg BitVec.toNat (eq_of_beq heq)
      rw [htn] at hv
      have hoff0 : off = 0 := Nat.add_left_cancel (by rw [hv, Nat.add_zero])
      subst hoff0; nomatch h64
  · cases heq : (codeBase + BitVec.ofNat 64 off == codeBase + 32#64) with
    | false => rfl
    | true =>
      have hv := congrArg BitVec.toNat (eq_of_beq heq)
      rw [htn, htn32] at hv
      have hoff32 : off = 32 := Nat.add_left_cancel hv
      subst hoff32; nomatch h64
  · apply Bool.and_eq_true_iff.mpr
    rw [htn]
    exact ⟨Nat.ble_eq_true_of_le (Nat.add_le_add_left h64 _),
           Nat.ble_eq_true_of_le (Nat.succ_le_of_lt (Nat.add_lt_add_left hlt _))⟩
  · rw [htn, Nat.add_sub_cancel_left]

theorem enterPicTarget {codeBase : BitVec 64} {totalBytes : Nat} {img : X64ObjImage}
    {s' : RealX64State} {tgt : Nat}
    (hall : AllUntrustedBundlesValid totalBytes img.code)
    (htgt_lt : tgt < totalBytes) (htgt_mod : tgt % 32 = 0)
    (hrip : s'.rip = codeBase + BitVec.ofNat 64 tgt) :
    SfiPicPhase codeBase totalBytes img s' := by
  cases h0 : decide (tgt = 0) with
  | true =>
    have ht0 : tgt = 0 := of_decide_eq_true h0; subst ht0
    apply SfiPicPhase.atPortal0
    rw [hrip]; exact BitVec.add_zero codeBase
  | false =>
    cases h32 : decide (tgt = 32) with
    | true =>
      have ht32 : tgt = 32 := of_decide_eq_true h32; subst ht32
      exact SfiPicPhase.atPortal1 hrip
    | false =>
      have hne0 : tgt ≠ 0 := of_decide_eq_false h0
      have hne32 : tgt ≠ 32 := of_decide_eq_false h32
      have hge32 : 32 ≤ tgt := by
        have hpos : 0 < tgt := Nat.pos_of_ne_zero hne0
        exact mod32_step_le rfl htgt_mod hpos
      have hgt32 : 32 < tgt := Nat.lt_of_le_of_ne hge32 hne32.symm
      have hge64 : 64 ≤ tgt := mod32_step_le rfl htgt_mod hgt32
      rcases hall with ⟨_, htot_mod, hget_b⟩
      rcases hget_b tgt hge64 htgt_lt htgt_mod with ⟨bundle, hblen, hbget, hbchk⟩
      have hb32 : tgt + 32 ≤ totalBytes := mod32_step_le htgt_mod htot_mod htgt_lt
      apply SfiPicPhase.atMacro tgt 32 0 bundle hge64 htgt_lt htgt_mod hb32 (by decide)
      · rw [Nat.add_zero]; exact hrip
      · rw [Nat.zero_add]; exact hblen
      · intro i hi; rw [Nat.add_zero]; exact hbget i (by rw [hblen] at hi; exact hi)
      · exact hbchk

theorem enterNextPicMacro {codeBase : BitVec 64} {totalBytes : Nat} {img : X64ObjImage}
    {s' : RealX64State} {bBase fuel nextOff : Nat} {rem2 : List UInt8}
    (hall : AllUntrustedBundlesValid totalBytes img.code)
    (hb64 : 64 ≤ bBase) (hb_lt : bBase < totalBytes) (hb_mod : bBase % 32 = 0)
    (hb_le : bBase + 32 ≤ totalBytes)
    (hrip : s'.rip = codeBase + BitVec.ofNat 64 (bBase + nextOff))
    (hnlen : nextOff + rem2.length = 32)
    (hnlast : ((bBase + 32 == totalBytes) && decide (nextOff = 32)) = false)
    (hnbytes : ∀ i, i < rem2.length → img.code.getByte? ((bBase + nextOff) + i) = listGet? rem2 i)
    (hnchk : checkSfiPicMacroStream totalBytes bBase (bBase + 32 == totalBytes) fuel nextOff rem2 = true) :
    SfiPicPhase codeBase totalBytes img s' := by
  cases rem2 with
  | cons r0 rs =>
    have hoff_lt : nextOff < 32 := by
      rw [← hnlen]; exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ rs.length)
    exact SfiPicPhase.atMacro bBase fuel nextOff (r0 :: rs) hb64 hb_lt hb_mod hb_le hoff_lt hrip hnlen hnbytes hnchk
  | nil =>
    rw [List.length_nil, Nat.add_zero] at hnlen; subst hnlen
    have hnot_eq : bBase + 32 ≠ totalBytes := by
      intro heq
      have hbe : (bBase + 32 == totalBytes) = true := beq_iff_eq.mpr heq
      rw [decide_eq_true (rfl : 32 = 32), Bool.and_true, hbe] at hnlast
      nomatch hnlast
    have hnext_lt : bBase + 32 < totalBytes := Nat.lt_of_le_of_ne hb_le hnot_eq
    have hnext_mod : (bBase + 32) % 32 = 0 := add_mod32_zero hb_mod rfl
    exact enterPicTarget hall hnext_lt hnext_mod hrip

theorem coreSafe_upd_scratch64 {codeBase arenaBase : BitVec 64}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    {s : RealX64State} {dst : Reg} {v : BitVec 64} {fl' : RFlags} {rip' : BitVec 64}
    (hrun : s.exitKind = .running)
    (hcore : SfiPicCoreSafe codeBase arenaBase initRegs initMem s)
    (hscr : isPicScratchReg dst = true) :
    SfiPicCoreSafe codeBase arenaBase initRegs initMem
      { s with rip := rip', regs := regUpd s.regs dst v, flags := fl' } := by
  rcases hcore with ⟨hf, hr15, hr14, hr13, hmem, hexit⟩
  rw [hrun] at hexit
  dsimp [SfiPicCoreSafe]; rw [hrun]
  refine ⟨hf, ?_, ?_, ?_, hmem, ?_, ?_⟩
  · rw [regUpd_ne s.regs (scratch_ne_protected hscr rfl) v]; exact hr15
  · rw [regUpd_ne s.regs (scratch_ne_protected hscr rfl) v]; exact hr14
  · rw [regUpd_ne s.regs (scratch_ne_r13 hscr) v]; exact hr13
  · rw [regUpd_ne s.regs (scratch_ne_protected hscr rfl) v]; exact hexit.1
  · intro r hp; rw [regUpd_ne s.regs (scratch_ne_protected hscr hp) v]; exact hexit.2 r hp

theorem coreSafe_upd_zext32 {codeBase arenaBase : BitVec 64}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    {s : RealX64State} {dst : Reg} {v32 : BitVec 32} {fl' : RFlags} {rip' : BitVec 64}
    (hrun : s.exitKind = .running)
    (hcore : SfiPicCoreSafe codeBase arenaBase initRegs initMem s)
    (hdst : isPicZext32DstReg dst = true) :
    SfiPicCoreSafe codeBase arenaBase initRegs initMem
      { s with rip := rip', regs := regUpd s.regs dst (v32.zeroExtend 64), flags := fl' } := by
  rcases hcore with ⟨hf, hr15, hr14, hr13, hmem, hexit⟩
  rw [hrun] at hexit
  dsimp [SfiPicCoreSafe]; rw [hrun]
  refine ⟨hf, ?_, ?_, ?_, hmem, ?_, ?_⟩
  · rw [regUpd_ne s.regs (zext32Dst_ne_protected hdst rfl) _]; exact hr15
  · rw [regUpd_ne s.regs (zext32Dst_ne_protected hdst rfl) _]; exact hr14
  · cases hr_eq : decide (.r13 = dst) with
    | true =>
      have he : .r13 = dst := of_decide_eq_true hr_eq; subst he
      rw [regUpd_eq, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
      exact v32.isLt
    | false =>
      rw [regUpd_ne s.regs (of_decide_eq_false hr_eq) _]; exact hr13
  · rw [regUpd_ne s.regs (zext32Dst_ne_protected hdst rfl) _]; exact hexit.1
  · intro r hp; rw [regUpd_ne s.regs (zext32Dst_ne_protected hdst hp) _]; exact hexit.2 r hp

theorem zext64_lt_2pow32 (m : ByteMem) (ea : BitVec 64) :
    ∃ v32 : BitVec 32, readMem32Zext64 m ea = v32.zeroExtend 64 :=
  ⟨m (ea + 3#64) ++ (m (ea + 2#64) ++ (m (ea + 1#64) ++ m (ea + 0#64))), rfl⟩

theorem add_ofNat_assoc (codeBase : BitVec 64) (a b : Nat) :
    (codeBase + BitVec.ofNat 64 a) + BitVec.ofNat 64 b = codeBase + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem step_standalonePicOp_safe {codeBase arenaBase : BitVec 64}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    {s : RealX64State} {ins : X64Instr} {len : Nat} (nd0 : UndefFlags)
    (hrun : s.exitKind = .running)
    (hcore : SfiPicCoreSafe codeBase arenaBase initRegs initMem s)
    (hop : isStandalonePicSfiOp ins = true) :
    let s' := execDecodedRealX64 ins len nd0 s
    s'.exitKind = .running ∧
    s'.rip = s.rip + BitVec.ofNat 64 len ∧
    SfiPicCoreSafe codeBase arenaBase initRegs initMem s' := by
  cases ins with
  | nop | endbr64 =>
    refine ⟨hrun, rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1, ?_⟩
    have hx := hcore.2.2.2.2.2; dsimp [execDecodedRealX64]; rw [hrun] at hx ⊢; exact hx
  | movRR64 dst src => exact ⟨hrun, rfl, coreSafe_upd_scratch64 hrun hcore hop⟩
  | movImm64 dst imm => exact ⟨hrun, rfl, coreSafe_upd_scratch64 hrun hcore hop⟩
  | lea64 dst addr => exact ⟨hrun, rfl, coreSafe_upd_scratch64 hrun hcore hop⟩
  | shiftImm64 op dst cnt => exact ⟨hrun, rfl, coreSafe_upd_scratch64 hrun hcore hop⟩
  | imulRR64 dst src => exact ⟨hrun, rfl, coreSafe_upd_scratch64 hrun hcore hop⟩
  | movRR32 dst src => exact ⟨hrun, rfl, coreSafe_upd_zext32 hrun hcore hop⟩
  | movImm32 dst imm32 => exact ⟨hrun, rfl, coreSafe_upd_zext32 hrun hcore hop⟩
  | aluRR64 op dst src =>
    dsimp [isStandalonePicSfiOp] at hop; revert hop
    cases hw : aluWritesDst op with
    | false =>
      intro _; dsimp [execDecodedRealX64]; rw [hw]; dsimp
      have hx := hcore.2.2.2.2.2; rw [hrun] at hx
      refine ⟨hrun, rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1, ?_⟩
      rw [hrun]; exact hx
    | true =>
      intro hs; dsimp [execDecodedRealX64]; rw [hw]; dsimp
      exact ⟨hrun, rfl, coreSafe_upd_scratch64 hrun hcore hs⟩
  | aluImm64 op dst imm =>
    dsimp [isStandalonePicSfiOp] at hop; revert hop
    cases hw : aluWritesDst op with
    | false =>
      intro _; dsimp [execDecodedRealX64]; rw [hw]; dsimp
      have hx := hcore.2.2.2.2.2; rw [hrun] at hx
      refine ⟨hrun, rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1, ?_⟩
      rw [hrun]; exact hx
    | true =>
      intro hs; dsimp [execDecodedRealX64]; rw [hw]; dsimp
      exact ⟨hrun, rfl, coreSafe_upd_scratch64 hrun hcore hs⟩
  | aluRR32 op dst src =>
    dsimp [isStandalonePicSfiOp] at hop; revert hop
    cases hw : aluWritesDst op with
    | false =>
      intro _; dsimp [execDecodedRealX64]; rw [hw]; dsimp
      have hx := hcore.2.2.2.2.2; rw [hrun] at hx
      refine ⟨hrun, rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1, ?_⟩
      rw [hrun]; exact hx
    | true =>
      intro hd; dsimp [execDecodedRealX64]; rw [hw]; dsimp
      rcases evalAluFlags32_fst op (BitVec.extractLsb' 0 32 (s.regs dst))
        (BitVec.extractLsb' 0 32 (s.regs src)) nd0 with ⟨r32, hr32⟩
      rw [hr32]
      exact ⟨hrun, rfl, coreSafe_upd_zext32 hrun hcore hd⟩
  | aluImm32 op dst imm32 =>
    dsimp [isStandalonePicSfiOp] at hop; revert hop
    cases hw : aluWritesDst op with
    | false =>
      intro _; dsimp [execDecodedRealX64]; rw [hw]; dsimp
      have hx := hcore.2.2.2.2.2; rw [hrun] at hx
      refine ⟨hrun, rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2.1, ?_⟩
      rw [hrun]; exact hx
    | true =>
      intro hd; dsimp [execDecodedRealX64]; rw [hw]; dsimp
      rcases evalAluFlags32_fst op (BitVec.extractLsb' 0 32 (s.regs dst)) imm32 nd0 with ⟨r32, hr32⟩
      rw [hr32]
      exact ⟨hrun, rfl, coreSafe_upd_zext32 hrun hcore hd⟩
  | store64 addr src =>
    cases addr with
    | ripRel _ => nomatch hop
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch hop
        | some p =>
          rcases p with ⟨ir, sc⟩
          cases ir with
          | r13 =>
            cases sc with | zero => nomatch hop | succ s1 =>
              cases s1 with | succ _ => nomatch hop | zero =>
                dsimp [isStandalonePicSfiOp] at hop
                rcases hcore with ⟨hf, hr15, hr14, hr13, hmem, hexit⟩
                rw [hrun] at hexit
                refine ⟨hrun, rfl, hf, hr15, hr14, hr13, ?_, ?_⟩
                · intro a hout; dsimp [execDecodedRealX64, evalAddr]
                  rw [hr14, sfi_store64_preserves_outside_sym_arena s.mem arenaBase (s.regs .r13) disp (s.regs src) a hr13 hop hout]
                  exact hmem a hout
                · dsimp [execDecodedRealX64]; rw [hrun]; exact hexit
          | _ => nomatch hop
      | _ => nomatch hop
  | store32 addr src =>
    cases addr with
    | ripRel _ => nomatch hop
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch hop
        | some p =>
          rcases p with ⟨ir, sc⟩
          cases ir with
          | r13 =>
            cases sc with | zero => nomatch hop | succ s1 =>
              cases s1 with | succ _ => nomatch hop | zero =>
                dsimp [isStandalonePicSfiOp] at hop
                rcases hcore with ⟨hf, hr15, hr14, hr13, hmem, hexit⟩
                rw [hrun] at hexit
                refine ⟨hrun, rfl, hf, hr15, hr14, hr13, ?_, ?_⟩
                · intro a hout; dsimp [execDecodedRealX64, evalAddr]
                  rw [hr14, sfi_store32_preserves_outside_sym_arena s.mem arenaBase (s.regs .r13) disp (s.regs src) a hr13 hop hout]
                  exact hmem a hout
                · dsimp [execDecodedRealX64]; rw [hrun]; exact hexit
          | _ => nomatch hop
      | _ => nomatch hop
  | load64 dst addr =>
    cases addr with
    | ripRel _ => nomatch hop
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch hop
        | some p =>
          rcases p with ⟨ir, sc⟩
          cases ir with
          | r13 =>
            cases sc with | zero => nomatch hop | succ s1 =>
              cases s1 with | succ _ => nomatch hop | zero =>
                dsimp [isStandalonePicSfiOp] at hop
                have hc := Bool.and_eq_true_iff.mp hop
                exact ⟨hrun, rfl, coreSafe_upd_scratch64 hrun hcore hc.1⟩
          | _ => nomatch hop
      | _ => nomatch hop
  | load32Sext dst addr =>
    cases addr with
    | ripRel _ => nomatch hop
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch hop
        | some p =>
          rcases p with ⟨ir, sc⟩
          cases ir with
          | r13 =>
            cases sc with | zero => nomatch hop | succ s1 =>
              cases s1 with | succ _ => nomatch hop | zero =>
                dsimp [isStandalonePicSfiOp] at hop
                have hc := Bool.and_eq_true_iff.mp hop
                exact ⟨hrun, rfl, coreSafe_upd_scratch64 hrun hcore hc.1⟩
          | _ => nomatch hop
      | _ => nomatch hop
  | load32Zext dst addr =>
    cases addr with
    | ripRel _ => nomatch hop
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch hop
        | some p =>
          rcases p with ⟨ir, sc⟩
          cases ir with
          | r13 =>
            cases sc with | zero => nomatch hop | succ s1 =>
              cases s1 with | succ _ => nomatch hop | zero =>
                dsimp [isStandalonePicSfiOp] at hop
                have hc := Bool.and_eq_true_iff.mp hop
                rcases zext64_lt_2pow32 s.mem (evalAddr s (s.rip + BitVec.ofNat 64 len) _) with ⟨v32, hv32⟩
                dsimp [execDecodedRealX64]; rw [hv32]
                exact ⟨hrun, rfl, coreSafe_upd_zext32 hrun hcore hc.1⟩
          | _ => nomatch hop
      | _ => nomatch hop
  | push64 _ | pop64 _ | leave64 | jmpRel _ | jccRel _ _ | jmpReg _ | ret | int3 =>
    nomatch hop

theorem peekPicMem2nd_spec {idx : Reg} {rem1 : List UInt8} {ins2 : X64Instr} {len2 : Nat}
    (h : peekPicMem2nd idx rem1 = some (ins2, len2)) :
    isSandboxedPicMem2nd idx ins2 = true ∧
    0 < len2 ∧ len2 ≤ rem1.length ∧
    decodeX64 (rem1.take len2) = .ok ins2 (rem1.take len2).length ∧
    (rem1.take len2).length = len2 := by
  dsimp [peekPicMem2nd] at h; revert h
  cases decodeX64 rem1 with
  | fault _ => intro h; nomatch h
  | ok i2 l2 =>
    dsimp
    let pfx2 := rem1.take l2
    cases hc : (((isSandboxedPicMem2nd idx i2 && !(l2 == 0)) && !decide (lenTR rem1 < l2)) &&
                (decodeX64 pfx2 == .ok i2 pfx2.length)) with
    | false => intro h; nomatch h
    | true =>
      intro h; injection h with hp; injection hp with hi hl; subst hi hl
      have c1 := Bool.and_eq_true_iff.mp hc
      have c2 := Bool.and_eq_true_iff.mp c1.1
      have c3 := Bool.and_eq_true_iff.mp c2.1
      have hl_pos : 0 < l2 := by cases l2 with | zero => nomatch c3.2 | succ k => exact Nat.zero_lt_succ k
      have hl_le : l2 ≤ rem1.length := by
        cases hlt : decide (lenTR rem1 < l2) with
        | false => have hn := Nat.not_lt.mp (of_decide_eq_false hlt); rw [lenTR_eq_length] at hn; exact hn
        | true => rw [hlt] at c2; nomatch c2.2
      exact ⟨c3.1, hl_pos, hl_le, of_decide_eq_true c1.2, List.length_take_of_le hl_le⟩

theorem isPicLeaR15R11_eq {ins : X64Instr} (h : isPicLeaR15R11 ins = true) :
    ins = .lea64 .r11 (.baseDisp .r15 (some (.r11, 1)) 0#64) := by
  dsimp [isPicLeaR15R11] at h
  split at h <;> first | rfl | nomatch h

theorem isPicJmpR11_eq {ins : X64Instr} (h : isPicJmpR11 ins = true) :
    ins = .jmpReg .r11 := by
  dsimp [isPicJmpR11] at h
  split at h <;> first | rfl | nomatch h

theorem peekPicJmp2nd3rd_spec {rem1 : List UInt8} {len2 len3 : Nat}
    (h : peekPicJmp2nd3rd rem1 = some (len2, len3)) :
    0 < len2 ∧ len2 ≤ rem1.length ∧
    decodeX64 (rem1.take len2) =
      .ok (.lea64 .r11 (.baseDisp .r15 (some (.r11, 1)) 0#64)) len2 ∧
    (rem1.take len2).length = len2 ∧
    0 < len3 ∧ len3 ≤ (rem1.drop len2).length ∧
    decodeX64 ((rem1.drop len2).take len3) =
      .ok (.jmpReg .r11) ((rem1.drop len2).take len3).length ∧
    ((rem1.drop len2).take len3).length = len3 := by
  dsimp [peekPicJmp2nd3rd] at h; revert h
  cases decodeX64 rem1 with
  | fault _ => intro h; nomatch h
  | ok i2 l2 =>
    dsimp
    let pfx2 := rem1.take l2
    let rem2 := rem1.drop l2
    cases hc2 : (((isPicLeaR15R11 i2 && !(l2 == 0)) && !decide (lenTR rem1 < l2)) &&
                 (decodeX64 pfx2 == .ok i2 pfx2.length)) with
    | false => intro h; nomatch h
    | true =>
      dsimp
      cases decodeX64 rem2 with
      | fault _ => intro h; nomatch h
      | ok i3 l3 =>
        dsimp
        let pfx3 := rem2.take l3
        cases hc3 : (((isPicJmpR11 i3 && !(l3 == 0)) && !decide (lenTR rem2 < l3)) &&
                     (decodeX64 pfx3 == .ok i3 pfx3.length)) with
        | false => intro h; nomatch h
        | true =>
          intro h; injection h with hp; injection hp with hl2 hl3; subst hl2 hl3
          have d1 := Bool.and_eq_true_iff.mp hc2
          have d2 := Bool.and_eq_true_iff.mp d1.1
          have d3 := Bool.and_eq_true_iff.mp d2.1
          have e1 := Bool.and_eq_true_iff.mp hc3
          have e2 := Bool.and_eq_true_iff.mp e1.1
          have e3 := Bool.and_eq_true_iff.mp e2.1
          have hl2_pos : 0 < l2 := by cases l2 with | zero => nomatch d3.2 | succ k => exact Nat.zero_lt_succ k
          have hl2_le : l2 ≤ rem1.length := by
            cases hlt : decide (lenTR rem1 < l2) with
            | false => have hn := Nat.not_lt.mp (of_decide_eq_false hlt); rw [lenTR_eq_length] at hn; exact hn
            | true => rw [hlt] at d2; nomatch d2.2
          have hl3_pos : 0 < l3 := by cases l3 with | zero => nomatch e3.2 | succ k => exact Nat.zero_lt_succ k
          have hl3_le : l3 ≤ rem2.length := by
            cases hlt : decide (lenTR rem2 < l3) with
            | false => have hn := Nat.not_lt.mp (of_decide_eq_false hlt); rw [lenTR_eq_length] at hn; exact hn
            | true => rw [hlt] at e2; nomatch e2.2
          have hi2 := isPicLeaR15R11_eq d3.1
          have hi3 := isPicJmpR11_eq e3.1
          have hp2_len : pfx2.length = l2 := List.length_take_of_le hl2_le
          have hp3_len : pfx3.length = l3 := List.length_take_of_le hl3_le
          have hdec2 := of_decide_eq_true d1.2
          rw [hi2, hp2_len] at hdec2
          have hdec3 := of_decide_eq_true e1.2
          rw [hi3] at hdec3
          exact ⟨hl2_pos, hl2_le, hdec2, hp2_len, hl3_pos, hl3_le, hdec3, hp3_len⟩

theorem masked32_target_valid {a32 mask : BitVec 32} {totalBytes : Nat}
    (halign : (mask &&& 31#32) == 0#32)
    (hbound : mask.toNat < totalBytes) :
    ((a32 &&& mask).zeroExtend 64).toNat < totalBytes ∧
    ((a32 &&& mask).zeroExtend 64).toNat % 32 = 0 := by
  have htn : ((a32 &&& mask).zeroExtend 64).toNat = (a32 &&& mask).toNat :=
    BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)
  rw [htn, BitVec.toNat_and]
  refine ⟨Nat.lt_of_le_of_lt Nat.and_le_right hbound, ?_⟩
  rw [← Nat.and_two_pow_sub_one_eq_mod _ 5]
  change (a32.toNat &&& mask.toNat) &&& 31 = 0
  rw [Nat.and_assoc]
  have hm0 : mask.toNat &&& 31 = 0 := by
    have heq : mask &&& 31#32 = 0#32 := of_decide_eq_true halign
    have ht := congrArg BitVec.toNat heq; rw [BitVec.toNat_and] at ht; exact ht
  rw [hm0, Nat.and_zero]

theorem isSandboxedPicMem2nd_exec_safe {codeBase arenaBase : BitVec 64}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    {s : RealX64State} {idx : Reg} {ins2 : X64Instr} {len2 : Nat} (nd0 : UndefFlags)
    (hrun : s.exitKind = .running)
    (hcore : SfiPicCoreSafe codeBase arenaBase initRegs initMem s)
    (hidx_lt : (s.regs idx).toNat < 4294967296)
    (hmem2 : isSandboxedPicMem2nd idx ins2 = true) :
    let s' := execDecodedRealX64 ins2 len2 nd0 s
    s'.exitKind = .running ∧
    s'.rip = s.rip + BitVec.ofNat 64 len2 ∧
    SfiPicCoreSafe codeBase arenaBase initRegs initMem s' := by
  cases ins2 with
  | store64 addr src =>
    cases addr with
    | ripRel _ => nomatch hmem2
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch hmem2
        | some p =>
          rcases p with ⟨idx', sc⟩
          cases sc with | zero => nomatch hmem2 | succ s1 =>
            cases s1 with | succ _ => nomatch hmem2 | zero =>
              dsimp [isSandboxedPicMem2nd] at hmem2
              have hc := Bool.and_eq_true_iff.mp hmem2
              have hi_eq : idx' = idx := eq_of_beq hc.1; subst idx'
              rcases hcore with ⟨hf, hr15, hr14, hr13, hmem, hexit⟩
              rw [hrun] at hexit
              refine ⟨hrun, rfl, hf, hr15, hr14, hr13, ?_, ?_⟩
              · intro a hout; dsimp [execDecodedRealX64, evalAddr]
                rw [hr14, sfi_store64_preserves_outside_sym_arena s.mem arenaBase (s.regs idx) disp (s.regs src) a hidx_lt hc.2 hout]
                exact hmem a hout
              · dsimp [execDecodedRealX64]; rw [hrun]; exact hexit
      | _ => nomatch hmem2
  | store32 addr src =>
    cases addr with
    | ripRel _ => nomatch hmem2
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch hmem2
        | some p =>
          rcases p with ⟨idx', sc⟩
          cases sc with | zero => nomatch hmem2 | succ s1 =>
            cases s1 with | succ _ => nomatch hmem2 | zero =>
              dsimp [isSandboxedPicMem2nd] at hmem2
              have hc := Bool.and_eq_true_iff.mp hmem2
              have hi_eq : idx' = idx := eq_of_beq hc.1; subst idx'
              rcases hcore with ⟨hf, hr15, hr14, hr13, hmem, hexit⟩
              rw [hrun] at hexit
              refine ⟨hrun, rfl, hf, hr15, hr14, hr13, ?_, ?_⟩
              · intro a hout; dsimp [execDecodedRealX64, evalAddr]
                rw [hr14, sfi_store32_preserves_outside_sym_arena s.mem arenaBase (s.regs idx) disp (s.regs src) a hidx_lt hc.2 hout]
                exact hmem a hout
              · dsimp [execDecodedRealX64]; rw [hrun]; exact hexit
      | _ => nomatch hmem2
  | load64 dst addr =>
    cases addr with
    | ripRel _ => nomatch hmem2
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch hmem2
        | some p =>
          rcases p with ⟨idx', sc⟩
          cases sc with | zero => nomatch hmem2 | succ s1 =>
            cases s1 with | succ _ => nomatch hmem2 | zero =>
              dsimp [isSandboxedPicMem2nd] at hmem2
              have hc1 := Bool.and_eq_true_iff.mp hmem2
              have hc2 := Bool.and_eq_true_iff.mp hc1.1
              exact ⟨hrun, rfl, coreSafe_upd_scratch64 hrun hcore hc2.1⟩
      | _ => nomatch hmem2
  | load32Sext dst addr =>
    cases addr with
    | ripRel _ => nomatch hmem2
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch hmem2
        | some p =>
          rcases p with ⟨idx', sc⟩
          cases sc with | zero => nomatch hmem2 | succ s1 =>
            cases s1 with | succ _ => nomatch hmem2 | zero =>
              dsimp [isSandboxedPicMem2nd] at hmem2
              have hc1 := Bool.and_eq_true_iff.mp hmem2
              have hc2 := Bool.and_eq_true_iff.mp hc1.1
              exact ⟨hrun, rfl, coreSafe_upd_scratch64 hrun hcore hc2.1⟩
      | _ => nomatch hmem2
  | load32Zext dst addr =>
    cases addr with
    | ripRel _ => nomatch hmem2
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch hmem2
        | some p =>
          rcases p with ⟨idx', sc⟩
          cases sc with | zero => nomatch hmem2 | succ s1 =>
            cases s1 with | succ _ => nomatch hmem2 | zero =>
              dsimp [isSandboxedPicMem2nd] at hmem2
              have hc1 := Bool.and_eq_true_iff.mp hmem2
              have hc2 := Bool.and_eq_true_iff.mp hc1.1
              rcases zext64_lt_2pow32 s.mem (evalAddr s (s.rip + BitVec.ofNat 64 len2) _) with ⟨v32, hv32⟩
              dsimp [execDecodedRealX64]; rw [hv32]
              exact ⟨hrun, rfl, coreSafe_upd_zext32 hrun hcore hc2.1⟩
      | _ => nomatch hmem2
  | _ => nomatch hmem2

theorem stepPicPortalX64_untrusted {codeBase : BitVec 64} {totalBytes off len : Nat}
    {img : X64ObjImage} {ins : X64Instr} (nd0 : UndefFlags) {s : RealX64State}
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (hkx : s.exitKind = .running) (hnf : s.fault = false)
    (h64 : 64 ≤ off) (hlt : off < totalBytes)
    (hrip : s.rip = codeBase + BitVec.ofNat 64 off)
    (hwin : decodeX64 (fetchWindow16 img.code off) = .ok ins len) :
    stepPicPortalX64 codeBase totalBytes img nd0 s = execDecodedRealX64 ins len nd0 s := by
  rcases untrusted_off_portal_flags hfit h64 hlt with ⟨hp0, hp1, hrng, hsub⟩
  simp only [stepPicPortalX64, hkx, hnf, hrip, hp0, hp1, hrng, hsub, hwin,
             bne_self_eq_false, Bool.false_or, Bool.not_true, Bool.false_eq_true, ite_false]

/-- Single-step inductive preservation of `SfiPicMachineInv` across ALL instructions & phases. -/
theorem step_preserves_sfiPicInv {codeBase arenaBase : BitVec 64} {totalBytes : Nat} {img : X64ObjImage}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    (hall : AllUntrustedBundlesValid totalBytes img.code)
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (hhost_rsp : ∀ k, k < 8 → OutsideSymmetricArena arenaBase (initRegs .rsp + BitVec.ofNat 64 k))
    (nd0 : UndefFlags) {s : RealX64State}
    (hinv : SfiPicMachineInv codeBase arenaBase totalBytes img initRegs initMem s) :
    SfiPicMachineInv codeBase arenaBase totalBytes img initRegs initMem
      (stepPicPortalX64 codeBase totalBytes img nd0 s) := by
  rcases hinv with ⟨hcore, hphase_fn⟩
  have hnf : s.fault = false := hcore.1
  cases hkx : s.exitKind with
  | portalReturn =>
    have hst : stepPicPortalX64 codeBase totalBytes img nd0 s = s := by
      dsimp [stepPicPortalX64]; rw [hkx]; rfl
    rw [hst]; exact ⟨hcore, fun hr => by rw [hkx] at hr; nomatch hr⟩
  | portalHostcall =>
    have hst : stepPicPortalX64 codeBase totalBytes img nd0 s = s := by
      dsimp [stepPicPortalX64]; rw [hkx]; rfl
    rw [hst]; exact ⟨hcore, fun hr => by rw [hkx] at hr; nomatch hr⟩
  | running =>
    have hphase := hphase_fn hkx
    cases hphase with
    | atPortal0 hrip0 =>
      have hst : stepPicPortalX64 codeBase totalBytes img nd0 s =
          { s with rip := readMem64 s.mem (s.regs .rsp),
                   regs := regUpd s.regs .rsp (s.regs .rsp + 8#64),
                   exitKind := .portalReturn } := by
        have hbeq0 : (codeBase == codeBase) = true := beq_self_eq_true codeBase
        simp only [stepPicPortalX64, hkx, hnf, hrip0, hbeq0,
                   bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ite_false, ite_true]
      rw [hst]
      rcases hcore with ⟨_, hr15, hr14, hr13, hmem, hexit⟩
      rw [hkx] at hexit
      refine ⟨⟨hnf, ?_, ?_, ?_, hmem, ?_, ?_, ?_⟩, fun hr => nomatch hr⟩
      · dsimp only; rw [regUpd_ne s.regs (by decide : .r15 ≠ .rsp) _]; exact hr15
      · dsimp only; rw [regUpd_ne s.regs (by decide : .r14 ≠ .rsp) _]; exact hr14
      · dsimp only; rw [regUpd_ne s.regs (by decide : .r13 ≠ .rsp) _]; exact hr13
      · dsimp only; rw [hexit.1]
        dsimp [readMem64]
        rw [hmem _ (hhost_rsp 0 (by decide)), hmem _ (hhost_rsp 1 (by decide)),
            hmem _ (hhost_rsp 2 (by decide)), hmem _ (hhost_rsp 3 (by decide)),
            hmem _ (hhost_rsp 4 (by decide)), hmem _ (hhost_rsp 5 (by decide)),
            hmem _ (hhost_rsp 6 (by decide)), hmem _ (hhost_rsp 7 (by decide))]
      · dsimp only; rw [regUpd_eq, hexit.1]
      · intro r hp hne; dsimp only; rw [regUpd_ne s.regs hne _]; exact hexit.2 r hp
    | atPortal1 hrip1 =>
      have hne0 : (codeBase + 32#64 == codeBase) = false := by
        have hpos96 : 32 < totalBytes := Nat.lt_of_lt_of_le (by decide : 32 < 96) hall.1
        have htn32 := codeBase_add_off_toNat hfit hpos96
        cases heq : (codeBase + 32#64 == codeBase) with
        | false => rfl
        | true =>
          have hv := congrArg BitVec.toNat (eq_of_beq heq)
          rw [htn32] at hv
          have : 32 = 0 := Nat.add_left_cancel (by rw [hv, Nat.add_zero])
          nomatch this
      have hst : stepPicPortalX64 codeBase totalBytes img nd0 s = { s with exitKind := .portalHostcall } := by
        have hbeq32 : (codeBase + 32#64 == codeBase + 32#64) = true := beq_self_eq_true _
        simp only [stepPicPortalX64, hkx, hnf, hrip1, hne0, hbeq32,
                   bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ite_false, ite_true]
      rw [hst]
      rcases hcore with ⟨_, hr15, hr14, hr13, hmem, hexit⟩
      rw [hkx] at hexit
      exact ⟨⟨hnf, hr15, hr14, hr13, hmem, hexit⟩, fun hr => nomatch hr⟩
    | pendingPicJmp curOff tgtOff pfx3 hr11_eq htgt_lt htgt_mod hcur64 hcur_lt hrip hdec3 hwin3 =>
      have hlen_le16 : pfx3.length ≤ 16 := Nat.le_trans (decodeX64_len_bounds hdec3).2.1 (by decide)
      rcases fetchBytes_prefix pfx3 img.code 16 curOff hlen_le16 hwin3 with ⟨sfx, hsfx⟩
      have hwin_dec : decodeX64 (fetchWindow16 img.code curOff) = .ok (.jmpReg .r11) pfx3.length := by
        dsimp [fetchWindow16]; rw [hsfx]; exact decodeX64_prefix_invariant hdec3 sfx
      have hst : stepPicPortalX64 codeBase totalBytes img nd0 s = { s with rip := s.regs .r11 } :=
        stepPicPortalX64_untrusted nd0 hfit hkx hnf hcur64 hcur_lt hrip hwin_dec
      rw [hst]
      rcases hcore with ⟨_, hr15, hr14, hr13, hmem, hexit⟩
      rw [hkx] at hexit
      refine ⟨⟨hnf, hr15, hr14, hr13, hmem, ?_⟩, fun _ => ?_⟩
      · dsimp; rw [hkx]; exact hexit
      · exact enterPicTarget hall htgt_lt htgt_mod hr11_eq
    | pendingPicLea curOff leaLen tgtOff pfx2 pfx3 hr11_eq htgt_lt htgt_mod
        hcur64 hcur_lt hnext64 hnext_lt hrip hdec2 hpfx2_len hwin2 hdec3 hwin3 =>
      have hlen_le16 : pfx2.length ≤ 16 := by
        rw [hpfx2_len]
        exact Nat.le_trans (decodeX64_len_bounds hdec2).2.1 (by decide)
      rcases fetchBytes_prefix pfx2 img.code 16 curOff hlen_le16 hwin2 with ⟨sfx, hsfx⟩
      have hwin_dec : decodeX64 (fetchWindow16 img.code curOff) =
          .ok (.lea64 .r11 (.baseDisp .r15 (some (.r11, 1)) 0#64)) leaLen := by
        dsimp [fetchWindow16]; rw [hsfx]; exact decodeX64_prefix_invariant hdec2 sfx
      have hst : stepPicPortalX64 codeBase totalBytes img nd0 s =
          { s with rip := s.rip + BitVec.ofNat 64 leaLen,
                   regs := regUpd s.regs .r11 (s.regs .r15 + s.regs .r11 * 1#64 + 0#64) } :=
        stepPicPortalX64_untrusted nd0 hfit hkx hnf hcur64 hcur_lt hrip hwin_dec
      rw [hst]
      refine ⟨coreSafe_upd_scratch64 hkx hcore rfl, fun _ => ?_⟩
      have hr11_new : (regUpd s.regs .r11 (s.regs .r15 + s.regs .r11 * 1#64 + 0#64)) .r11 =
          codeBase + BitVec.ofNat 64 tgtOff := by
        rw [regUpd_eq, hcore.2.1, hr11_eq, BitVec.mul_one, BitVec.add_zero]
      have hrip_new : s.rip + BitVec.ofNat 64 leaLen = codeBase + BitVec.ofNat 64 (curOff + leaLen) := by
        rw [hrip, add_ofNat_assoc]
      exact SfiPicPhase.pendingPicJmp (curOff + leaLen) tgtOff pfx3 hr11_new htgt_lt htgt_mod
        hnext64 hnext_lt hrip_new hdec3 hwin3
    | pendingMem bBase fuel nextOff curOff idx ins2 pfx2 rem2 hidx_lt hb64 hb_lt hb_mod hb_le
        hcur64 hcur_lt hrip hmem2 hdec2 hwin2 hnrip hnlen hnlast hnbytes hnchk =>
      have hlen_le16 : pfx2.length ≤ 16 := Nat.le_trans (decodeX64_len_bounds hdec2).2.1 (by decide)
      rcases fetchBytes_prefix pfx2 img.code 16 curOff hlen_le16 hwin2 with ⟨sfx, hsfx⟩
      have hwin_dec : decodeX64 (fetchWindow16 img.code curOff) = .ok ins2 pfx2.length := by
        dsimp [fetchWindow16]; rw [hsfx]; exact decodeX64_prefix_invariant hdec2 sfx
      have hst : stepPicPortalX64 codeBase totalBytes img nd0 s = execDecodedRealX64 ins2 pfx2.length nd0 s :=
        stepPicPortalX64_untrusted nd0 hfit hkx hnf hcur64 hcur_lt hrip hwin_dec
      rw [hst]
      rcases isSandboxedPicMem2nd_exec_safe nd0 hkx hcore hidx_lt hmem2 (len2 := pfx2.length) with
        ⟨_, hrip2, hcore2⟩
      refine ⟨hcore2, fun _ => ?_⟩
      have hrip_n : (execDecodedRealX64 ins2 pfx2.length nd0 s).rip =
          codeBase + BitVec.ofNat 64 (bBase + nextOff) := by
        rw [hrip2, hrip, add_ofNat_assoc, hnrip]
      exact enterNextPicMacro hall hb64 hb_lt hb_mod hb_le hrip_n hnlen hnlast hnbytes hnchk
    | atMacro bBase fuel off rem hb64 hb_lt hb_mod hb_le hoff_lt hrip hlen hbytes hchk =>
      cases rem with
      | nil =>
        rw [List.length_nil, Nat.add_zero] at hlen; subst hlen
        exact False.elim (Nat.lt_irrefl 32 hoff_lt)
      | cons b0 bs =>
        cases fuel with
        | zero => nomatch hchk
        | succ fuel' =>
          have hcur64 : 64 ≤ bBase + off := Nat.le_trans hb64 (Nat.le_add_right bBase off)
          have hcur_lt : bBase + off < totalBytes :=
            Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff_lt bBase) hb_le
          dsimp [checkSfiPicMacroStream] at hchk; revert hchk
          cases hdec1 : decodeX64 (b0 :: bs) with
          | fault _ => intro h; nomatch h
          | ok ins1 len1 =>
            dsimp
            let pfx1 := (b0 :: bs).take len1
            let rem1 := (b0 :: bs).drop len1
            cases hbad1 : (((len1 == 0 || decide (lenTR (b0 :: bs) < len1)) || decide (32 < off + len1)) ||
                           (decodeX64 pfx1 != .ok ins1 pfx1.length)) with
            | true => intro h; nomatch h
            | false =>
              have hb1 := Bool.or_eq_false_iff.mp hbad1
              have hb2 := Bool.or_eq_false_iff.mp hb1.1
              have hb3 := Bool.or_eq_false_iff.mp hb2.1
              have hlen1_le_rem : len1 ≤ (b0 :: bs).length := by
                cases hd : decide (lenTR (b0 :: bs) < len1) with
                | false => have hn := Nat.not_lt.mp (of_decide_eq_false hd); rw [lenTR_eq_length] at hn; exact hn
                | true => rw [hd] at hb3; nomatch hb3.2
              have hpfx1_len : pfx1.length = len1 := List.length_take_of_le hlen1_le_rem
              have hpfx1_dec : decodeX64 pfx1 = .ok ins1 pfx1.length := by
                cases heq : (decodeX64 pfx1 == .ok ins1 pfx1.length) with
                | true => exact eq_of_beq heq
                | false => have hf := hb1.2; dsimp [bne] at hf; rw [heq] at hf; nomatch hf
              have hpfx1_win : ∀ i, i < pfx1.length → img.code.getByte? ((bBase + off) + i) = listGet? pfx1 i := by
                intro i hi
                have hi_len1 : i < len1 := by rw [← hpfx1_len]; exact hi
                have hi_rem : i < (b0 :: bs).length := Nat.lt_of_lt_of_le hi_len1 hlen1_le_rem
                rw [hbytes i hi_rem, ← listGet?_take len1 (b0 :: bs) i hi_len1]
              have hlen1_le16 : pfx1.length ≤ 16 := Nat.le_trans (decodeX64_len_bounds hpfx1_dec).2.1 (by decide)
              rcases fetchBytes_prefix pfx1 img.code 16 (bBase + off) hlen1_le16 hpfx1_win with ⟨sfx1, hsfx1⟩
              have hwin1_dec : decodeX64 (fetchWindow16 img.code (bBase + off)) = .ok ins1 len1 := by
                dsimp [fetchWindow16]; rw [hsfx1, ← hpfx1_len]
                exact decodeX64_prefix_invariant hpfx1_dec sfx1
              have hst1 : stepPicPortalX64 codeBase totalBytes img nd0 s = execDecodedRealX64 ins1 len1 nd0 s :=
                stepPicPortalX64_untrusted nd0 hfit hkx hnf hcur64 hcur_lt hrip hwin1_dec
              have hrem1_len : (off + len1) + rem1.length = 32 := by
                dsimp [rem1]; rw [List.length_drop, Nat.add_assoc, Nat.add_sub_of_le hlen1_le_rem]; exact hlen
              have hrem1_bytes : ∀ i, i < rem1.length →
                  img.code.getByte? ((bBase + (off + len1)) + i) = listGet? rem1 i := by
                intro i hi; dsimp [rem1] at hi ⊢; rw [listGet?_drop len1 (b0 :: bs) i]
                rw [List.length_drop] at hi
                rw [← Nat.add_assoc bBase off len1, Nat.add_assoc (bBase + off) len1 i]
                exact hbytes (len1 + i) (Nat.add_lt_of_lt_sub' hi)
              have finishStandalone :
                  isStandalonePicSfiOp ins1 = true →
                  ((bBase + 32 == totalBytes) && decide (off + len1 = 32)) = false →
                  checkSfiPicMacroStream totalBytes bBase (bBase + 32 == totalBytes) fuel' (off + len1) rem1 = true →
                  SfiPicMachineInv codeBase arenaBase totalBytes img initRegs initMem
                    (stepPicPortalX64 codeBase totalBytes img nd0 s) := by
                intro hop1 hnlast1 hchk1
                rw [hst1]
                rcases step_standalonePicOp_safe nd0 hkx hcore hop1 (len := len1) with ⟨_, hrip1, hcore1⟩
                refine ⟨hcore1, fun _ => ?_⟩
                have hrip1' : (execDecodedRealX64 ins1 len1 nd0 s).rip =
                    codeBase + BitVec.ofNat 64 (bBase + (off + len1)) := by
                  rw [hrip1, hrip, add_ofNat_assoc, Nat.add_assoc]
                exact enterNextPicMacro hall hb64 hb_lt hb_mod hb_le hrip1' hrem1_len hnlast1 hrem1_bytes hchk1
              cases ins1 with
              | jmpRel rel =>
                dsimp
                cases hok_j : sfiPicJmpTargetOk totalBytes bBase off len1 rel with
                | false => intro h; nomatch h
                | true =>
                  intro _; rw [hst1]
                  dsimp [sfiPicJmpTargetOk] at hok_j
                  have cj := Bool.and_eq_true_iff.mp hok_j
                  rcases hcore with ⟨_, hr15, hr14, hr13, hmem, hexit⟩; rw [hkx] at hexit
                  refine ⟨⟨hnf, hr15, hr14, hr13, hmem, ?_⟩, fun _ => ?_⟩
                  · dsimp [execDecodedRealX64]; rw [hkx]; exact hexit
                  · have hrip_j : (execDecodedRealX64 (.jmpRel rel) len1 nd0 s).rip =
                        codeBase + BitVec.ofNat 64 (sfiPicJmpTarget bBase off len1 rel) := by
                      dsimp [execDecodedRealX64]; unfold sfiPicJmpTarget
                      rw [hrip, add_ofNat_assoc, BitVec.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
                    exact enterPicTarget hall (natLtB_true cj.1) (natEqB_true cj.2) hrip_j
              | jccRel cc rel =>
                dsimp
                cases hok_jc : (sfiPicJmpTargetOk totalBytes bBase off len1 rel &&
                                !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                | false => intro h; nomatch h
                | true =>
                  dsimp; intro hchk_next; rw [hst1]
                  have cj1 := Bool.and_eq_true_iff.mp hok_jc
                  have cj2 := Bool.and_eq_true_iff.mp (by dsimp [sfiPicJmpTargetOk] at cj1; exact cj1.1)
                  have hnlast1 := bnot_eq_true_imp_false cj1.2
                  rcases hcore with ⟨_, hr15, hr14, hr13, hmem, hexit⟩; rw [hkx] at hexit
                  cases hcond : evalCond cc s.flags with
                  | true =>
                    dsimp [execDecodedRealX64]; rw [hcond]; dsimp
                    refine ⟨⟨hnf, hr15, hr14, hr13, hmem, ?_⟩, fun _ => ?_⟩
                    · rw [hkx]; exact hexit
                    · have hrip_j : s.rip + BitVec.ofNat 64 len1 + rel =
                          codeBase + BitVec.ofNat 64 (sfiPicJmpTarget bBase off len1 rel) := by
                        unfold sfiPicJmpTarget
                        rw [hrip, add_ofNat_assoc, BitVec.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
                      exact enterPicTarget hall (natLtB_true cj2.1) (natEqB_true cj2.2) hrip_j
                  | false =>
                    dsimp [execDecodedRealX64]; rw [hcond]; dsimp
                    refine ⟨⟨hnf, hr15, hr14, hr13, hmem, ?_⟩, fun _ => ?_⟩
                    · rw [hkx]; exact hexit
                    · have hrip_f : s.rip + BitVec.ofNat 64 len1 =
                          codeBase + BitVec.ofNat 64 (bBase + (off + len1)) := by
                        rw [hrip, add_ofNat_assoc, Nat.add_assoc]
                      exact enterNextPicMacro hall hb64 hb_lt hb_mod hb_le hrip_f hrem1_len hnlast1 hrem1_bytes hchk_next
              | movRR32 idx dstSrc =>
                dsimp
                cases hscr : isPicScratchReg idx with
                | false =>
                  dsimp
                  cases hp_ok : (isStandalonePicSfiOp (.movRR32 idx dstSrc) &&
                                 !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                  | false => intro h; nomatch h
                  | true =>
                    dsimp; intro hchk_next
                    have cp := Bool.and_eq_true_iff.mp hp_ok
                    exact finishStandalone cp.1 (bnot_eq_true_imp_false cp.2) hchk_next
                | true =>
                  dsimp
                  cases hp2 : peekPicMem2nd idx rem1 with
                  | none =>
                    dsimp
                    cases hp_ok : (isStandalonePicSfiOp (.movRR32 idx dstSrc) &&
                                   !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                    | false => intro h; nomatch h
                    | true =>
                      dsimp; intro hchk_next
                      have cp := Bool.and_eq_true_iff.mp hp_ok
                      exact finishStandalone cp.1 (bnot_eq_true_imp_false cp.2) hchk_next
                  | some pair2 =>
                    rcases pair2 with ⟨ins2, len2⟩; dsimp
                    cases hbad2 : (decide (32 < off + len1 + len2) ||
                                   ((bBase + 32 == totalBytes) && decide (off + len1 + len2 = 32))) with
                    | true => intro h; nomatch h
                    | false =>
                      intro hchk2; rw [hst1]
                      rcases peekPicMem2nd_spec hp2 with ⟨hmem2, hlen2_pos, hlen2_le, hdec2, hpfx2_len⟩
                      have hb2_pair := Bool.or_eq_false_iff.mp hbad2
                      have hdst_ok : isPicZext32DstReg idx = true := by
                        dsimp [isPicZext32DstReg]; rw [hscr]; rfl
                      refine ⟨coreSafe_upd_zext32 hkx hcore hdst_ok, fun _ => ?_⟩
                      have hidx_val : (regUpd s.regs idx ((BitVec.extractLsb' 0 32 (s.regs dstSrc)).zeroExtend 64) idx).toNat < 4294967296 := by
                        rw [regUpd_eq, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
                        exact (BitVec.extractLsb' 0 32 (s.regs dstSrc)).isLt
                      have hoff1_lt32 : off + len1 < 32 :=
                        Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hlen2_pos)
                          (Nat.not_lt.mp (of_decide_eq_false hb2_pair.1))
                      have hcur1_64 : 64 ≤ bBase + (off + len1) :=
                        Nat.le_trans hb64 (Nat.le_add_right bBase _)
                      have hcur1_lt : bBase + (off + len1) < totalBytes :=
                        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff1_lt32 bBase) hb_le
                      have hrip1 : s.rip + BitVec.ofNat 64 len1 = codeBase + BitVec.ofNat 64 (bBase + (off + len1)) := by
                        rw [hrip, add_ofNat_assoc, Nat.add_assoc]
                      have hwin2 : ∀ i, i < (rem1.take len2).length →
                          img.code.getByte? ((bBase + (off + len1)) + i) = listGet? (rem1.take len2) i := by
                        intro i hi; rw [hpfx2_len] at hi
                        rw [hrem1_bytes i (Nat.lt_of_lt_of_le hi hlen2_le), ← listGet?_take len2 rem1 i hi]
                      have hnrip : (bBase + (off + len1)) + (rem1.take len2).length = bBase + (off + len1 + len2) := by
                        rw [hpfx2_len, Nat.add_assoc bBase (off + len1) len2]
                      have hnlen2 : (off + len1 + len2) + (rem1.drop len2).length = 32 := by
                        rw [List.length_drop, Nat.add_assoc (off + len1) len2 _, Nat.add_sub_of_le hlen2_le]
                        exact hrem1_len
                      have hnbytes2 : ∀ i, i < (rem1.drop len2).length →
                          img.code.getByte? ((bBase + (off + len1 + len2)) + i) = listGet? (rem1.drop len2) i := by
                        intro i hi; rw [listGet?_drop len2 rem1 i]; rw [List.length_drop] at hi
                        rw [← Nat.add_assoc bBase (off + len1) len2, Nat.add_assoc (bBase + (off + len1)) len2 i]
                        exact hrem1_bytes (len2 + i) (Nat.add_lt_of_lt_sub' hi)
                      exact SfiPicPhase.pendingMem bBase fuel' (off + len1 + len2) (bBase + (off + len1))
                        idx ins2 (rem1.take len2) (rem1.drop len2) hidx_val hb64 hb_lt hb_mod hb_le
                        hcur1_64 hcur1_lt hrip1 hmem2 hdec2 hwin2 hnrip hnlen2 hb2_pair.2 hnbytes2 hchk2
              | aluImm32 op dst mask =>
                dsimp
                cases hand_r11 : (op == .and && dst == .r11) with
                | false =>
                  dsimp
                  cases hp_ok : (isStandalonePicSfiOp (.aluImm32 op dst mask) &&
                                 !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                  | false => intro h; nomatch h
                  | true =>
                    dsimp; intro hchk_next
                    have cp := Bool.and_eq_true_iff.mp hp_ok
                    exact finishStandalone cp.1 (bnot_eq_true_imp_false cp.2) hchk_next
                | true =>
                  dsimp
                  have h_ar := Bool.and_eq_true_iff.mp hand_r11
                  have hop : op = .and := of_decide_eq_true h_ar.1
                  have hdst : dst = .r11 := of_decide_eq_true h_ar.2
                  subst hop hdst
                  cases hpj : peekPicJmp2nd3rd rem1 with
                  | none =>
                    dsimp
                    cases hp_ok : (isStandalonePicSfiOp (.aluImm32 .and .r11 mask) &&
                                   !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                    | false => intro h; nomatch h
                    | true =>
                      dsimp; intro hchk_next
                      have cp := Bool.and_eq_true_iff.mp hp_ok
                      exact finishStandalone cp.1 (bnot_eq_true_imp_false cp.2) hchk_next
                  | some pair23 =>
                    rcases pair23 with ⟨len2, len3⟩; dsimp
                    cases hok_m : (((mask &&& 31#32) == 0#32 && natLtB mask.toNat totalBytes) &&
                                   !decide (32 < off + len1 + len2 + len3)) with
                    | false => intro h; nomatch h
                    | true =>
                      intro _; rw [hst1]
                      rcases peekPicJmp2nd3rd_spec hpj with
                        ⟨hlen2_pos, hlen2_le, hdec2, hpfx2_len, hlen3_pos, hlen3_le, hdec3, hpfx3_len⟩
                      have cm1 := Bool.and_eq_true_iff.mp hok_m
                      have cm2 := Bool.and_eq_true_iff.mp cm1.1
                      have hle32 : off + len1 + len2 + len3 ≤ 32 := by
                        cases hd : decide (32 < off + len1 + len2 + len3) with
                        | false => exact Nat.not_lt.mp (of_decide_eq_false hd)
                        | true => rw [hd] at cm1; nomatch cm1.2
                      let a32 := BitVec.extractLsb' 0 32 (s.regs .r11)
                      refine ⟨coreSafe_upd_zext32 hkx hcore rfl, fun _ => ?_⟩
                      rcases masked32_target_valid cm2.1 (natLtB_true cm2.2) (a32 := a32) with ⟨ht_lt, ht_mod⟩
                      let tgtOff := ((a32 &&& mask).zeroExtend 64).toNat
                      have hr11_eq : (regUpd s.regs .r11 ((a32 &&& mask).zeroExtend 64)) .r11 =
                          BitVec.ofNat 64 tgtOff := by
                        rw [regUpd_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
                      have hoff12_lt32 : off + len1 + len2 < 32 :=
                        Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hlen3_pos) hle32
                      have hoff1_lt32 : off + len1 < 32 :=
                        Nat.lt_trans (Nat.lt_add_of_pos_right hlen2_pos) hoff12_lt32
                      have hcur1_64 : 64 ≤ bBase + (off + len1) := Nat.le_trans hb64 (Nat.le_add_right _ _)
                      have hcur1_lt : bBase + (off + len1) < totalBytes :=
                        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff1_lt32 bBase) hb_le
                      have hnext64 : 64 ≤ (bBase + (off + len1)) + len2 := Nat.le_trans hcur1_64 (Nat.le_add_right _ _)
                      have hnext_lt : (bBase + (off + len1)) + len2 < totalBytes := by
                        rw [Nat.add_assoc bBase (off + len1) len2]
                        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff12_lt32 bBase) hb_le
                      have hrip1 : s.rip + BitVec.ofNat 64 len1 = codeBase + BitVec.ofNat 64 (bBase + (off + len1)) := by
                        rw [hrip, add_ofNat_assoc, Nat.add_assoc]
                      have hwin2 : ∀ i, i < (rem1.take len2).length →
                          img.code.getByte? ((bBase + (off + len1)) + i) = listGet? (rem1.take len2) i := by
                        intro i hi; rw [hpfx2_len] at hi
                        rw [hrem1_bytes i (Nat.lt_of_lt_of_le hi hlen2_le), ← listGet?_take len2 rem1 i hi]
                      have hwin3 : ∀ i, i < ((rem1.drop len2).take len3).length →
                          img.code.getByte? (((bBase + (off + len1)) + len2) + i) =
                            listGet? ((rem1.drop len2).take len3) i := by
                        intro i hi
                        have hi_len3 : i < len3 := by rw [← hpfx3_len]; exact hi
                        have hi_drop : i < (rem1.drop len2).length := Nat.lt_of_lt_of_le hi_len3 hlen3_le
                        rw [listGet?_take len3 (rem1.drop len2) i hi_len3, listGet?_drop len2 rem1 i]
                        rw [List.length_drop] at hi_drop
                        rw [Nat.add_assoc (bBase + (off + len1)) len2 i]
                        exact hrem1_bytes (len2 + i) (Nat.add_lt_of_lt_sub' hi_drop)
                      exact SfiPicPhase.pendingPicLea (bBase + (off + len1)) len2 tgtOff
                        (rem1.take len2) ((rem1.drop len2).take len3) hr11_eq ht_lt ht_mod
                        hcur1_64 hcur1_lt hnext64 hnext_lt hrip1 hdec2 hpfx2_len hwin2 hdec3 hwin3
              | nop | endbr64 | movRR64 _ _ | movImm64 _ _ | movImm32 _ _
              | load64 _ _ | store64 _ _ | store32 _ _ | load32Zext _ _ | load32Sext _ _ | lea64 _ _
              | aluRR64 _ _ _ | aluImm64 _ _ _ | aluRR32 _ _ _ | shiftImm64 _ _ _ | imulRR64 _ _
              | push64 _ | pop64 _ | leave64 | jmpReg _ | ret | int3 =>
                dsimp
                cases hp_ok : (isStandalonePicSfiOp _ &&
                               !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                | false => intro h; nomatch h
                | true =>
                  dsimp; intro hchk_next
                  have cp := Bool.and_eq_true_iff.mp hp_ok
                  exact finishStandalone cp.1 (bnot_eq_true_imp_false cp.2) hchk_next

theorem runPicPortalX64_preserves_inv {codeBase arenaBase : BitVec 64} {totalBytes : Nat} {img : X64ObjImage}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    (hall : AllUntrustedBundlesValid totalBytes img.code)
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (hhost_rsp : ∀ k, k < 8 → OutsideSymmetricArena arenaBase (initRegs .rsp + BitVec.ofNat 64 k)) :
    ∀ (steps : Nat) (nd : Nat → UndefFlags) (s : RealX64State),
      SfiPicMachineInv codeBase arenaBase totalBytes img initRegs initMem s →
      SfiPicMachineInv codeBase arenaBase totalBytes img initRegs initMem
        (runPicPortalX64 codeBase totalBytes img steps nd s)
  | 0, _, _, hinv => hinv
  | steps + 1, nd, s, hinv =>
    runPicPortalX64_preserves_inv hall hfit hhost_rsp steps (fun k => nd (k + 1))
      (stepPicPortalX64 codeBase totalBytes img (nd 0) s)
      (step_preserves_sfiPicInv hall hfit hhost_rsp (nd 0) hinv)

theorem sfiPicPhase_rip_in_range {codeBase : BitVec 64} {totalBytes : Nat} {img : X64ObjImage}
    {s : RealX64State} (hall : AllUntrustedBundlesValid totalBytes img.code)
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (hp : SfiPicPhase codeBase totalBytes img s) :
    codeBase.toNat ≤ s.rip.toNat ∧ s.rip.toNat < codeBase.toNat + totalBytes := by
  have hpos96 : 32 < totalBytes := Nat.lt_of_lt_of_le (by decide : 32 < 96) hall.1
  cases hp with
  | atPortal0 h0 =>
    rw [h0]; exact ⟨Nat.le_refl _, Nat.lt_add_of_pos_right (Nat.lt_trans (by decide : 0 < 32) hpos96)⟩
  | atPortal1 h1 =>
    rw [h1, codeBase_add_off_toNat hfit hpos96]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hpos96 _⟩
  | atMacro bBase _ off _ _ _ _ hb_le hoff_lt hrip _ _ _ =>
    have hlt : bBase + off < totalBytes := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff_lt bBase) hb_le
    rw [hrip, codeBase_add_off_toNat hfit hlt]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hlt _⟩
  | pendingMem _ _ _ curOff _ _ _ _ _ _ _ _ _ _ hcur_lt hrip _ _ _ _ _ _ _ _ =>
    rw [hrip, codeBase_add_off_toNat hfit hcur_lt]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hcur_lt _⟩
  | pendingPicLea curOff _ _ _ _ _ _ _ _ hcur_lt _ _ hrip _ _ _ _ _ =>
    rw [hrip, codeBase_add_off_toNat hfit hcur_lt]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hcur_lt _⟩
  | pendingPicJmp curOff _ _ _ _ _ _ hcur_lt hrip _ _ =>
    rw [hrip, codeBase_add_off_toNat hfit hcur_lt]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hcur_lt _⟩

/-- Top-level Repaired PIC Multi-Function SFI Soundness Theorem (`checkSfiPicMultiFn_sound`):
    For ANY 64-bit PIC `codeBase` (`codeBase + totalBytes < 2^64`), ANY `arenaBase`, and ANY
    multi-function C `.o` passing `checkSfiPicMultiFn totalBytes img = true`, across ALL step
    counts `steps : Nat` and ALL hardware demonic flag streams `nd : Nat → UndefFlags`:
    1. Execution never faults (`sf.fault = false`);
    2. `%r15 = codeBase`, `%r14 = arenaBase`, and `(sf.regs .r13).toNat < 2^32` (32-bit `guest_sp`);
    3. Every host byte outside `[arenaBase - 64 KiB, arenaBase + 4 GiB + 64 KiB)` (including the
       entire host stack around `%rsp`) is preserved byte-for-byte;
    4. While `.running`, `sf.rip ∈ [codeBase, codeBase + totalBytes)` and all host-protected
       registers (`%rsp, %rbp, %rbx, %r12, %r14, %r15`) equal `s0.regs`;
    5. Upon `.portalReturn` (Portal 0 `ret`), `sf.rip = readMem64 s0.mem (s0.regs .rsp)` (exact
       return to the host caller's `.Lsfi_after_guest`!) and `sf.regs .rsp = s0.regs .rsp + 8#64`! -/
theorem checkSfiPicMultiFn_sound
    {codeBase arenaBase : BitVec 64} {totalBytes : Nat} {img : X64ObjImage}
    (hok : checkSfiPicMultiFn totalBytes img = true)
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (s0 : RealX64State)
    (entryOff : Nat)
    (hentry_lt : entryOff < totalBytes) (hentry_mod : entryOff % 32 = 0)
    (hrip0 : s0.rip = codeBase + BitVec.ofNat 64 entryOff)
    (hr15_0 : s0.regs .r15 = codeBase)
    (hr14_0 : s0.regs .r14 = arenaBase)
    (hr13_0 : (s0.regs .r13).toNat < 4294967296)
    (hhost_rsp : ∀ k, k < 8 → OutsideSymmetricArena arenaBase (s0.regs .rsp + BitVec.ofNat 64 k))
    (hrun0 : s0.exitKind = .running)
    (hnf0 : s0.fault = false) :
    ∀ (steps : Nat) (nd : Nat → UndefFlags),
      let sf := runPicPortalX64 codeBase totalBytes img steps nd s0
      sf.fault = false ∧
      sf.regs .r15 = codeBase ∧
      sf.regs .r14 = arenaBase ∧
      (sf.regs .r13).toNat < 4294967296 ∧
      (∀ a, OutsideSymmetricArena arenaBase a → sf.mem a = s0.mem a) ∧
      (sf.exitKind = .running →
        codeBase.toNat ≤ sf.rip.toNat ∧ sf.rip.toNat < codeBase.toNat + totalBytes ∧
        sf.regs .rsp = s0.regs .rsp ∧
        (∀ r, isPicHostProtectedReg r = true → sf.regs r = s0.regs r)) ∧
      (sf.exitKind = .portalReturn →
        sf.rip = readMem64 s0.mem (s0.regs .rsp) ∧
        sf.regs .rsp = s0.regs .rsp + 8#64 ∧
        (∀ r, isPicHostProtectedReg r = true → r ≠ .rsp → sf.regs r = s0.regs r)) ∧
      (sf.exitKind = .portalHostcall →
        sf.regs .rsp = s0.regs .rsp ∧
        (∀ r, isPicHostProtectedReg r = true → sf.regs r = s0.regs r)) := by
  intro steps nd
  have hall := checkSfiPicMultiFn_bundlesValid hok
  have hinv0 : SfiPicMachineInv codeBase arenaBase totalBytes img s0.regs s0.mem s0 := by
    refine ⟨⟨hnf0, hr15_0, hr14_0, hr13_0, fun _ _ => rfl, ?_⟩, ?_⟩
    · rw [hrun0]; exact ⟨rfl, fun _ _ => rfl⟩
    · intro _; exact enterPicTarget hall hentry_lt hentry_mod hrip0
  rcases runPicPortalX64_preserves_inv hall hfit hhost_rsp steps nd s0 hinv0 with ⟨hcore_f, hphase_f⟩
  let sf := runPicPortalX64 codeBase totalBytes img steps nd s0
  rcases hcore_f with ⟨hf, hr15, hr14, hr13, hmem, hexit⟩
  refine ⟨hf, hr15, hr14, hr13, hmem, ?_, ?_, ?_⟩
  · intro hrun_f
    have hph := hphase_f hrun_f
    rcases sfiPicPhase_rip_in_range hall hfit hph with ⟨hlo, hhi⟩
    rw [hrun_f] at hexit
    exact ⟨hlo, hhi, hexit.1, hexit.2⟩
  · intro hret_f; rw [hret_f] at hexit; exact hexit
  · intro hhc_f; rw [hhc_f] at hexit; exact hexit

theorem checkSfiPicSubtree_node {totalBytes base lsz endOff : Nat} {l r : ByteCodeTree}
    (hmod : natEqB (lsz % 32) 0 = true) (hle : natLeB (base + lsz) endOff = true)
    (hl : checkSfiPicSubtree totalBytes base (base + lsz) l = true)
    (hr : checkSfiPicSubtree totalBytes (base + lsz) endOff r = true) :
    checkSfiPicSubtree totalBytes base endOff (.node lsz l r) = true := by
  dsimp [checkSfiPicSubtree]; rw [hmod, hle, hl, hr]; rfl

end PicMultiFnSfi

