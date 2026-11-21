-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import RealX64PrefixSem

/-!
# `StackCanaryLiftV2` — Sound `%fs:0x28` Lifting for Stock GCC & Rustc `.o` Code

Mechanizes `PrivateStackCanarySep` and proves end-to-end functional correctness,
caller/TCB memory preservation, and deadness of `__stack_chk_fail` directly from
compiler-emitted `.o` machine bytes (`0` `sorry`, `0` `*._unsafe_rec`):
1. `unpatched_fs28_flat_mismodel_counterexample`: refutes flat `[0x28]` mismodeling
   of `64 48 8B 04 25 28 00 00 00` (`mov %fs:0x28, %rax`).
2. `gcc_hash2_canary_verified`: exact `83`-byte `gcc 15.2.0 -O2 -fstack-protector-strong`
   `.o` specimen (`sub %fs:0x28, %rdx; jne __stack_chk_fail`).
3. `rust_unexposed_canary_verified`: exact `88`-byte `rustc 1.102.0-nightly
   -C opt-level=2 -Z stack-protector=all` `.o` specimen (`mov %fs:0x28, %rcx;
   cmp 0x10(%rsp), %rcx; jne __stack_chk_fail`).
4. `xor_fs28_canary_verified`: classic `xor %fs:0x28, %rdx; jne __stack_chk_fail`
   epilogue idiom.
5. `gcc_hash2_canary_corrupted_traps_to_stack_chk_fail`: two-sided sensitivity
   theorem proving corrupted stack-slot canaries branch to `__stack_chk_fail`.
-/

namespace StackCanaryLiftV2

open RealX64PrefixSem

/-! ## Section 1: Flat-`[0x28]` Mismodel Counterexample & 64-Bit Byte-Memory Algebra -/

theorem unpatched_fs28_flat_mismodel_counterexample :
    let fs28LoadBytes : List UInt8 := [0x64, 0x48, 0x8B, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]
    let fsVal := 0x00007F8FE4E08740#64
    let m0 := writeMem64 (writeMem64 (fun _ => 0#8) 0x28#64 0xDEAD0028DEAD0028#64)
                         (fsVal + 0x28#64) 0xCA028000CA028000#64
    let s0 : RealX64PrefixState := { rip := 0x100#64, fsBase := fsVal, regs := fun _ => 0#64, mem := m0 }
    decodeX64Unpatched fs28LoadBytes =
      .ok (.load64 .rax { seg := none, addr32 := false, kind := .baseDisp none none 0x28#64 }) 9 ∧
    decodeX64V2 fs28LoadBytes =
      .ok (.load64 .rax { seg := some .fs, addr32 := false, kind := .baseDisp none none 0x28#64 }) 9 ∧
    (execDecodedRealX64V2
      (.load64 .rax { seg := none, addr32 := false, kind := .baseDisp none none 0x28#64 }) 9 {} s0).regs .rax =
      0xDEAD0028DEAD0028#64 ∧
    (stepRawRealX64V2 0x100#64 32 { code := .leaf fs28LoadBytes } {} s0).regs .rax =
      0xCA028000CA028000#64 := by
  decide

theorem memUpd8_eq (m : ByteMem) (a : BitVec 64) (b : BitVec 8) :
    memUpd8 m a b a = b := by
  dsimp [memUpd8]; simp

theorem add_left_cancel_bv64 {a x y : BitVec 64} (h : a + x = a + y) : x = y := by
  have h1 := congrArg (fun z => z - a) h
  simpa [BitVec.add_comm a x, BitVec.add_comm a y, BitVec.add_sub_cancel] using h1

theorem pack8Bytes_byteOf64 (v : BitVec 64) :
    pack8Bytes (byteOf64 v 0) (byteOf64 v 1) (byteOf64 v 2) (byteOf64 v 3)
               (byteOf64 v 4) (byteOf64 v 5) (byteOf64 v 6) (byteOf64 v 7) = v := by
  dsimp [pack8Bytes, byteOf64]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem addr_off_ne (a : BitVec 64) {i j : Nat} (hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 j) :
    a + BitVec.ofNat 64 i ≠ a + BitVec.ofNat 64 j := by
  intro heq; exact hne (add_left_cancel_bv64 heq)

theorem readMem64_writeMem64_same (m : ByteMem) (a v : BitVec 64) :
    readMem64 (writeMem64 m a v) a = v := by
  dsimp [readMem64, writeMem64]
  have ne01 : a + 0#64 ≠ a + 1#64 := addr_off_ne a (by decide)
  have ne02 : a + 0#64 ≠ a + 2#64 := addr_off_ne a (by decide)
  have ne03 : a + 0#64 ≠ a + 3#64 := addr_off_ne a (by decide)
  have ne04 : a + 0#64 ≠ a + 4#64 := addr_off_ne a (by decide)
  have ne05 : a + 0#64 ≠ a + 5#64 := addr_off_ne a (by decide)
  have ne06 : a + 0#64 ≠ a + 6#64 := addr_off_ne a (by decide)
  have ne07 : a + 0#64 ≠ a + 7#64 := addr_off_ne a (by decide)
  have ne12 : a + 1#64 ≠ a + 2#64 := addr_off_ne a (by decide)
  have ne13 : a + 1#64 ≠ a + 3#64 := addr_off_ne a (by decide)
  have ne14 : a + 1#64 ≠ a + 4#64 := addr_off_ne a (by decide)
  have ne15 : a + 1#64 ≠ a + 5#64 := addr_off_ne a (by decide)
  have ne16 : a + 1#64 ≠ a + 6#64 := addr_off_ne a (by decide)
  have ne17 : a + 1#64 ≠ a + 7#64 := addr_off_ne a (by decide)
  have ne23 : a + 2#64 ≠ a + 3#64 := addr_off_ne a (by decide)
  have ne24 : a + 2#64 ≠ a + 4#64 := addr_off_ne a (by decide)
  have ne25 : a + 2#64 ≠ a + 5#64 := addr_off_ne a (by decide)
  have ne26 : a + 2#64 ≠ a + 6#64 := addr_off_ne a (by decide)
  have ne27 : a + 2#64 ≠ a + 7#64 := addr_off_ne a (by decide)
  have ne34 : a + 3#64 ≠ a + 4#64 := addr_off_ne a (by decide)
  have ne35 : a + 3#64 ≠ a + 5#64 := addr_off_ne a (by decide)
  have ne36 : a + 3#64 ≠ a + 6#64 := addr_off_ne a (by decide)
  have ne37 : a + 3#64 ≠ a + 7#64 := addr_off_ne a (by decide)
  have ne45 : a + 4#64 ≠ a + 5#64 := addr_off_ne a (by decide)
  have ne46 : a + 4#64 ≠ a + 6#64 := addr_off_ne a (by decide)
  have ne47 : a + 4#64 ≠ a + 7#64 := addr_off_ne a (by decide)
  have ne56 : a + 5#64 ≠ a + 6#64 := addr_off_ne a (by decide)
  have ne57 : a + 5#64 ≠ a + 7#64 := addr_off_ne a (by decide)
  have ne67 : a + 6#64 ≠ a + 7#64 := addr_off_ne a (by decide)
  rw [memUpd8_eq]
  rw [memUpd8_ne _ ne67, memUpd8_eq]
  rw [memUpd8_ne _ ne57, memUpd8_ne _ ne56, memUpd8_eq]
  rw [memUpd8_ne _ ne47, memUpd8_ne _ ne46, memUpd8_ne _ ne45, memUpd8_eq]
  rw [memUpd8_ne _ ne37, memUpd8_ne _ ne36, memUpd8_ne _ ne35, memUpd8_ne _ ne34, memUpd8_eq]
  rw [memUpd8_ne _ ne27, memUpd8_ne _ ne26, memUpd8_ne _ ne25, memUpd8_ne _ ne24, memUpd8_ne _ ne23, memUpd8_eq]
  rw [memUpd8_ne _ ne17, memUpd8_ne _ ne16, memUpd8_ne _ ne15, memUpd8_ne _ ne14, memUpd8_ne _ ne13, memUpd8_ne _ ne12, memUpd8_eq]
  rw [memUpd8_ne _ ne07, memUpd8_ne _ ne06, memUpd8_ne _ ne05, memUpd8_ne _ ne04, memUpd8_ne _ ne03, memUpd8_ne _ ne02, memUpd8_ne _ ne01, memUpd8_eq]
  exact pack8Bytes_byteOf64 v

def Disjoint8 (a b : BitVec 64) : Prop :=
  ∀ (i j : Nat), i < 8 → j < 8 → b + BitVec.ofNat 64 j ≠ a + BitVec.ofNat 64 i

theorem readMem64_writeMem64_disjoint (m : ByteMem) {a b : BitVec 64} (v : BitVec 64)
    (hd : Disjoint8 a b) :
    readMem64 (writeMem64 m a v) b = readMem64 m b := by
  dsimp [readMem64]
  rw [writeMem64_byte_ne m a (b + 0#64) v (fun k hk => hd k 0 hk (by decide)),
      writeMem64_byte_ne m a (b + 1#64) v (fun k hk => hd k 1 hk (by decide)),
      writeMem64_byte_ne m a (b + 2#64) v (fun k hk => hd k 2 hk (by decide)),
      writeMem64_byte_ne m a (b + 3#64) v (fun k hk => hd k 3 hk (by decide)),
      writeMem64_byte_ne m a (b + 4#64) v (fun k hk => hd k 4 hk (by decide)),
      writeMem64_byte_ne m a (b + 5#64) v (fun k hk => hd k 5 hk (by decide)),
      writeMem64_byte_ne m a (b + 6#64) v (fun k hk => hd k 6 hk (by decide)),
      writeMem64_byte_ne m a (b + 7#64) v (fun k hk => hd k 7 hk (by decide))]

theorem disjoint8_base_offsets (base : BitVec 64) (o1 o2 : Nat)
    (hoff : ∀ i j : Nat, i < 8 → j < 8 → BitVec.ofNat 64 (o2 + j) ≠ BitVec.ofNat 64 (o1 + i)) :
    Disjoint8 (base + BitVec.ofNat 64 o1) (base + BitVec.ofNat 64 o2) := by
  intro i j hi hj heq
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add] at heq
  exact hoff i j hi hj (add_left_cancel_bv64 heq)

theorem disjoint8_small_offsets (base : BitVec 64) {o1 o2 : Nat}
    (hb1 : o1 + 8 ≤ 64) (hb2 : o2 + 8 ≤ 64) (hsep : o1 + 8 ≤ o2 ∨ o2 + 8 ≤ o1) :
    Disjoint8 (base + BitVec.ofNat 64 o1) (base + BitVec.ofNat 64 o2) := by
  apply disjoint8_base_offsets
  intro i j hi hj heq
  have hi64 : o1 + i < 2 ^ 64 := Nat.lt_trans (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi o1) hb1) (by decide)
  have hj64 : o2 + j < 2 ^ 64 := Nat.lt_trans (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj o2) hb2) (by decide)
  have htn := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt hi64] at htn
  rcases hsep with h12 | h21
  · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi o1) (Nat.le_trans h12 (Nat.le_add_right o2 j))) htn
  · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj o2) (Nat.le_trans h21 (Nat.le_add_right o1 i))) htn

def PrivateStackCanarySep (frameBase : BitVec 64) (frameBytes : Nat) (fsBase : BitVec 64) : Prop :=
  ∀ (off j : Nat), off < frameBytes → j < 8 →
    (fsBase + 0x28#64) + BitVec.ofNat 64 j ≠ frameBase + BitVec.ofNat 64 off

theorem privateStackCanarySep_disjoint8 {frameBase fsBase : BitVec 64} {frameBytes slotOff : Nat}
    (hsep : PrivateStackCanarySep frameBase frameBytes fsBase)
    (hslot : slotOff + 8 ≤ frameBytes) :
    Disjoint8 (frameBase + BitVec.ofNat 64 slotOff) (fsBase + 0x28#64) := by
  intro i j hi hj
  rw [BitVec.add_assoc frameBase, ← BitVec.ofNat_add]
  exact hsep (slotOff + i) j (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi slotOff) hslot) hj

theorem writeMem64_slot_outside_frame (m : ByteMem) {frameBase a : BitVec 64} {frameBytes slotOff : Nat}
    (v : BitVec 64) (hslot : slotOff + 8 ≤ frameBytes)
    (hout : ∀ off, off < frameBytes → a ≠ frameBase + BitVec.ofNat 64 off) :
    writeMem64 m (frameBase + BitVec.ofNat 64 slotOff) v a = m a := by
  apply writeMem64_byte_ne
  intro k hk
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hout (slotOff + k) (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk slotOff) hslot)

def mkSt (rip : BitVec 64) (regs : Reg → BitVec 64) (fs gs : BitVec 64) (fl : RFlags) (m : ByteMem) :
    RealX64PrefixState :=
  { rip := rip, regs := regs, fsBase := fs, gsBase := gs, flags := fl, mem := m,
    exitKind := .running, fault := false }

theorem stepRaw_mkSt (codeBase ripVal : BitVec 64) (totalBytes off : Nat)
    (img : X64ObjImage) (ins : X64InstrV2) (len : Nat) (nd0 : UndefFlags)
    (regs : Reg → BitVec 64) (fs gs : BitVec 64) (fl : RFlags) (m : ByteMem)
    (hrng : (natLeB codeBase.toNat ripVal.toNat && natLtB ripVal.toNat (codeBase.toNat + totalBytes)) = true)
    (hsub : ripVal.toNat - codeBase.toNat = off)
    (hdec : decodeX64V2 (fetchWindow16 img.code off) = .ok ins len) :
    stepRawRealX64V2 codeBase totalBytes img nd0 (mkSt ripVal regs fs gs fl m) =
      execDecodedRealX64V2 ins len nd0 (mkSt ripVal regs fs gs fl m) := by
  dsimp only [stepRawRealX64V2, mkSt]
  rw [hrng, hsub, hdec]
  rfl

theorem evalLinear_rspDisp (s : RealX64PrefixState) (nr disp : BitVec 64) :
    evalLinearAddr s nr { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none disp } =
      s.regs .rsp + disp := by
  dsimp [evalLinearAddr, segBaseOf, evalEffectiveAddr]
  rw [BitVec.zero_add, BitVec.add_zero]

theorem evalLinear_fs28 (s : RealX64PrefixState) (nr : BitVec 64) :
    evalLinearAddr s nr { seg := some .fs, addr32 := false, kind := .baseDisp none none 0x28#64 } =
      s.fsBase + 0x28#64 := by
  dsimp [evalLinearAddr, segBaseOf, evalEffectiveAddr]

theorem runRaw_step {cb : BitVec 64} {tb n : Nat} {img : X64ObjImage}
    {nd : Nat → UndefFlags} {s s' sf : RealX64PrefixState}
    (hst : stepRawRealX64V2 cb tb img (nd 0) s = s')
    (hrest : runRawRealX64V2 cb tb img n (fun k => nd (k + 1)) s' = sf) :
    runRawRealX64V2 cb tb img (n + 1) nd s = sf :=
  (congrArg (runRawRealX64V2 cb tb img n (fun k => nd (k + 1))) hst).trans hrest

theorem zf_sub_self64 (c : BitVec 64) (nd : UndefFlags) :
    (evalAluFlags64 .sub c c nd).2.zf = true := by
  dsimp [evalAluFlags64, aluVal64]; rw [BitVec.sub_self]; rfl

theorem zf_cmp_self64 (c : BitVec 64) (nd : UndefFlags) :
    (evalAluFlags64 .cmp c c nd).2.zf = true := by
  dsimp [evalAluFlags64, aluVal64]; rw [BitVec.sub_self]; rfl

theorem zf_xor_self64 (c : BitVec 64) (nd : UndefFlags) :
    (evalAluFlags64 .xor c c nd).2.zf = true := by
  dsimp [evalAluFlags64, aluVal64]; rw [BitVec.xor_self]; rfl

theorem zf_sub_ne64 {a b : BitVec 64} (hne : a ≠ b) (nd : UndefFlags) :
    (evalAluFlags64 .sub a b nd).2.zf = false := by
  dsimp [evalAluFlags64, aluVal64]
  cases h : (a - b == 0#64) with
  | false => rfl
  | true =>
    have heq0 : a - b = 0#64 := eq_of_beq h
    have hab : a = b := by
      have h1 := congrArg (fun z => z + b) heq0
      simpa [BitVec.sub_add_cancel, BitVec.zero_add] using h1
    exact False.elim (hne hab)

theorem exec_jne_not_taken (ripVal rel : BitVec 64) (len : Nat) (nd0 : UndefFlags)
    (r : Reg → BitVec 64) (fs gs : BitVec 64) (fl : RFlags) (m : ByteMem)
    (hzf : fl.zf = true) :
    execDecodedRealX64V2 (.jccRel false .ne rel) len nd0 (mkSt ripVal r fs gs fl m) =
      mkSt (ripVal + BitVec.ofNat 64 len) r fs gs fl m := by
  dsimp only [execDecodedRealX64V2]
  have hc : evalCond .ne (mkSt ripVal r fs gs fl m).flags = false := by
    dsimp [evalCond, mkSt]; rw [hzf]; rfl
  rw [hc]; rfl

theorem exec_jne_taken (ripVal rel : BitVec 64) (len : Nat) (nd0 : UndefFlags)
    (r : Reg → BitVec 64) (fs gs : BitVec 64) (fl : RFlags) (m : ByteMem)
    (hzf : fl.zf = false) :
    execDecodedRealX64V2 (.jccRel false .ne rel) len nd0 (mkSt ripVal r fs gs fl m) =
      mkSt (ripVal + BitVec.ofNat 64 len + rel) r fs gs fl m := by
  dsimp only [execDecodedRealX64V2]
  have hc : evalCond .ne (mkSt ripVal r fs gs fl m).flags = true := by
    dsimp [evalCond, mkSt]; rw [hzf]; rfl
  rw [hc]; rfl

/-! ## Section 2: Compiler-Emitted `.o` Byte Arrays & Universal Lifting Proofs -/

def gccHash2CanaryBytes : List UInt8 := [
  0x48, 0x83, 0xEC, 0x28,
  0x48, 0x81, 0xC7, 0x78, 0x56, 0x34, 0x12,
  0x64, 0x48, 0x8B, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00,
  0x48, 0x89, 0x44, 0x24, 0x18,
  0x31, 0xC0,
  0xB8, 0x21, 0x43, 0x65, 0x87,
  0x48, 0x89, 0x3C, 0x24,
  0x48, 0x31, 0xC6,
  0x48, 0x89, 0x74, 0x24, 0x08,
  0x48, 0x8B, 0x04, 0x24,
  0x48, 0x8D, 0x04, 0x80,
  0x48, 0x33, 0x44, 0x24, 0x08,
  0x48, 0x8B, 0x54, 0x24, 0x18,
  0x64, 0x48, 0x2B, 0x14, 0x25, 0x28, 0x00, 0x00, 0x00,
  0x75, 0x05,
  0x48, 0x83, 0xC4, 0x28,
  0xC3,
  0xE8, 0x00, 0x00, 0x00, 0x00
]

def gccHash2CanaryImg : X64ObjImage := { code := .leaf gccHash2CanaryBytes }

def xorFs28CanaryBytes : List UInt8 := [
  0x48, 0x83, 0xEC, 0x28,
  0x48, 0x81, 0xC7, 0x78, 0x56, 0x34, 0x12,
  0x64, 0x48, 0x8B, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00,
  0x48, 0x89, 0x44, 0x24, 0x18,
  0x31, 0xC0,
  0xB8, 0x21, 0x43, 0x65, 0x87,
  0x48, 0x89, 0x3C, 0x24,
  0x48, 0x31, 0xC6,
  0x48, 0x89, 0x74, 0x24, 0x08,
  0x48, 0x8B, 0x04, 0x24,
  0x48, 0x8D, 0x04, 0x80,
  0x48, 0x33, 0x44, 0x24, 0x08,
  0x48, 0x8B, 0x54, 0x24, 0x18,
  0x64, 0x48, 0x33, 0x14, 0x25, 0x28, 0x00, 0x00, 0x00,
  0x75, 0x05,
  0x48, 0x83, 0xC4, 0x28,
  0xC3,
  0xE8, 0x00, 0x00, 0x00, 0x00
]

def xorFs28CanaryImg : X64ObjImage := { code := .leaf xorFs28CanaryBytes }

def rustUnexposedCanaryBytes : List UInt8 := [
  0x48, 0x83, 0xEC, 0x18,
  0x64, 0x48, 0x8B, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00,
  0x48, 0x89, 0x44, 0x24, 0x10,
  0x48, 0x81, 0xC7, 0x78, 0x56, 0x34, 0x12,
  0x48, 0x89, 0x3C, 0x24,
  0xB8, 0x21, 0x43, 0x65, 0x87,
  0x48, 0x31, 0xF0,
  0x48, 0x89, 0x44, 0x24, 0x08,
  0x48, 0xB8, 0x15, 0x7C, 0x4A, 0x7F, 0xB9, 0x79, 0x37, 0x9E,
  0x48, 0x0F, 0xAF, 0x04, 0x24,
  0x48, 0x33, 0x44, 0x24, 0x08,
  0x64, 0x48, 0x8B, 0x0C, 0x25, 0x28, 0x00, 0x00, 0x00,
  0x48, 0x3B, 0x4C, 0x24, 0x10,
  0x75, 0x05,
  0x48, 0x83, 0xC4, 0x18,
  0xC3,
  0xE8, 0x00, 0x00, 0x00, 0x00
]

def rustUnexposedCanaryImg : X64ObjImage := { code := .leaf rustUnexposedCanaryBytes }

def gccHash2Spec (x y : BitVec 64) : BitVec 64 :=
  let x1 := x + 0x12345678#64
  (x1 + x1 * 4#64) ^^^ (y ^^^ 0x0000000087654321#64)

def rustUnexposedSpec (x y : BitVec 64) : BitVec 64 :=
  (0x9E3779B97F4A7C15#64 * (x + 0x12345678#64)) ^^^ (0x0000000087654321#64 ^^^ y)

/-- Universal `PrivateStackCanarySep` lifting proof for stock `gcc 15.2.0 -O2 -fstack-protector-strong` (`83`B): -/
theorem gcc_hash2_canary_verified
    (x y rsp0 fsBase : BitVec 64) (mem0 : ByteMem) (nd : Nat → UndefFlags)
    (s0 : RealX64PrefixState)
    (hrip0 : s0.rip = 0x100#64) (hfs0 : s0.fsBase = fsBase)
    (hrsp0 : s0.regs .rsp = rsp0) (hrdi0 : s0.regs .rdi = x) (hrsi0 : s0.regs .rsi = y)
    (hmem0 : s0.mem = mem0) (hrun0 : s0.exitKind = .running) (hnf0 : s0.fault = false)
    (hsep : PrivateStackCanarySep (rsp0 - 0x28#64) 0x28 fsBase) :
    let sf := runRawRealX64V2 0x100#64 83 gccHash2CanaryImg 17 nd s0
    sf.fault = false ∧
    sf.rip = readMem64 mem0 rsp0 ∧
    sf.regs .rsp = rsp0 + 8#64 ∧
    sf.regs .rax = gccHash2Spec x y ∧
    (∀ a, (∀ off, off < 0x28 → a ≠ (rsp0 - 0x28#64) + BitVec.ofNat 64 off) → sf.mem a = mem0 a) := by
  cases s0 with | mk rip regs0 fs0 gs0 fl0 m0 ex0 flt0 =>
  dsimp only at hrip0 hfs0 hrsp0 hrdi0 hrsi0 hmem0 hrun0 hnf0
  subst rip fs0 m0 ex0 flt0
  let fb := rsp0 - 0x28#64
  let x1 := x + 0x12345678#64
  let y1 := y ^^^ 0x0000000087654321#64
  have hread_0_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fb + 0#64) = x1 := by
    rw [readMem64_writeMem64_disjoint _ y1 (disjoint8_small_offsets fb (o1 := 8) (o2 := 0) (by decide) (by decide) (.inr (by decide))),
        readMem64_writeMem64_same]
  have hread_8_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fb + 8#64) = y1 :=
    readMem64_writeMem64_same _ (fb + 8#64) y1
  have hread_18_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fb + 0x18#64) = readMem64 mem0 (fsBase + 0x28#64) := by
    rw [readMem64_writeMem64_disjoint _ y1 (disjoint8_small_offsets fb (o1 := 8) (o2 := 0x18) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_disjoint _ x1 (disjoint8_small_offsets fb (o1 := 0) (o2 := 0x18) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_same]
  have hread_fs_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fsBase + 0x28#64) = readMem64 mem0 (fsBase + 0x28#64) := by
    rw [readMem64_writeMem64_disjoint _ y1 (privateStackCanarySep_disjoint8 hsep (slotOff := 8) (by decide)),
        readMem64_writeMem64_disjoint _ x1 (privateStackCanarySep_disjoint8 hsep (slotOff := 0) (by decide)),
        readMem64_writeMem64_disjoint mem0 _ (privateStackCanarySep_disjoint8 hsep (slotOff := 0x18) (by decide))]
  have hret_mem_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) rsp0 = readMem64 mem0 rsp0 := by
    have hrsp_fb : rsp0 = fb + 0x28#64 := (BitVec.sub_add_cancel (x := rsp0) (y := 0x28#64)).symm
    rw [hrsp_fb,
        readMem64_writeMem64_disjoint _ y1 (disjoint8_small_offsets fb (o1 := 8) (o2 := 0x28) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_disjoint _ x1 (disjoint8_small_offsets fb (o1 := 0) (o2 := 0x28) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_disjoint mem0 _ (disjoint8_small_offsets fb (o1 := 0x18) (o2 := 0x28) (by decide) (by decide) (.inl (by decide)))]
  have hout_raw : ∀ a, (∀ off, off < 0x28 → a ≠ fb + BitVec.ofNat 64 off) →
      writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1 a = mem0 a := by
    intro a hout
    rw [writeMem64_slot_outside_frame _ y1 (slotOff := 8) (by decide) hout,
        writeMem64_slot_outside_frame _ x1 (slotOff := 0) (by decide) hout,
        writeMem64_slot_outside_frame mem0 _ (slotOff := 0x18) (by decide) hout]
  generalize hm4 : writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64)) = m4 at hread_0_raw hread_8_raw hread_18_raw hread_fs_raw hret_mem_raw hout_raw
  generalize hm7 : writeMem64 m4 (fb + 0#64) x1 = m7 at hread_0_raw hread_8_raw hread_18_raw hread_fs_raw hret_mem_raw hout_raw
  generalize hm9 : writeMem64 m7 (fb + 8#64) y1 = m9 at hread_0_raw hread_8_raw hread_18_raw hread_fs_raw hret_mem_raw hout_raw
  generalize hc : readMem64 mem0 (fsBase + 0x28#64) = c0 at hm4 hread_18_raw hread_fs_raw
  change (let sf := runRawRealX64V2 0x100#64 83 gccHash2CanaryImg 17 nd (mkSt 0x100#64 regs0 fsBase gs0 fl0 mem0); _)
  let r1 := regUpd regs0 .rsp fb; let f1 := (evalAluFlags64 .sub rsp0 0x28#64 (nd 0)).2
  have st1 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 0) (mkSt 0x100#64 regs0 fsBase gs0 fl0 mem0) =
      mkSt 0x104#64 r1 fsBase gs0 f1 mem0 := by
    refine (stepRaw_mkSt 0x100#64 0x100#64 83 0 gccHash2CanaryImg (.aluImm64 .sub .rsp 0x28#64) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]; rw [hrsp0]; rfl
  let r2 := regUpd r1 .rdi x1; let f2 := (evalAluFlags64 .add x 0x12345678#64 (nd 1)).2
  have st2 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 1) (mkSt 0x104#64 r1 fsBase gs0 f1 mem0) =
      mkSt 0x10B#64 r2 fsBase gs0 f2 mem0 := by
    refine (stepRaw_mkSt 0x100#64 0x104#64 83 4 gccHash2CanaryImg (.aluImm64 .add .rdi 0x12345678#64) 7 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]
    have : r1 .rdi = x := by dsimp only [r1, regUpd]; exact hrdi0
    rw [this]; rfl
  let r3 := regUpd r2 .rax c0
  have st3 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 2) (mkSt 0x10B#64 r2 fsBase gs0 f2 mem0) =
      mkSt 0x114#64 r3 fsBase gs0 f2 mem0 := by
    refine (stepRaw_mkSt 0x100#64 0x10B#64 83 0x0B gccHash2CanaryImg (.load64 .rax { seg := some .fs, addr32 := false, kind := .baseDisp none none 0x28#64 }) 9 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_fs28]; dsimp only [mkSt]; rw [hc]; rfl
  have st4 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 3) (mkSt 0x114#64 r3 fsBase gs0 f2 mem0) =
      mkSt 0x119#64 r3 fsBase gs0 f2 m4 := by
    refine (stepRaw_mkSt 0x100#64 0x114#64 83 0x14 gccHash2CanaryImg (.store64 { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0x18#64 } .rax) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x114#64 r3 fsBase gs0 f2 mem0).regs .rsp = fb := rfl
    have ha : (mkSt 0x114#64 r3 fsBase gs0 f2 mem0).regs .rax = c0 := rfl
    rw [hr, ha]; dsimp only [mkSt]; rw [hm4]; rfl
  let r5 := regUpd r3 .rax ((c0.extractLsb' 0 32 ^^^ c0.extractLsb' 0 32).zeroExtend 64)
  let f5 := (evalAluFlags32 .xor (c0.extractLsb' 0 32) (c0.extractLsb' 0 32) (nd 4)).2
  have st5 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 4) (mkSt 0x119#64 r3 fsBase gs0 f2 m4) =
      mkSt 0x11B#64 r5 fsBase gs0 f5 m4 :=
    (stepRaw_mkSt 0x100#64 0x119#64 83 0x19 gccHash2CanaryImg (.aluRR32 .xor .rax .rax) 2 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans rfl
  let r6 := regUpd r5 .rax 0x0000000087654321#64
  have st6 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 5) (mkSt 0x11B#64 r5 fsBase gs0 f5 m4) =
      mkSt 0x120#64 r6 fsBase gs0 f5 m4 :=
    (stepRaw_mkSt 0x100#64 0x11B#64 83 0x1B gccHash2CanaryImg (.movImm32 .rax 0x87654321#32) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans rfl
  have st7 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 6) (mkSt 0x120#64 r6 fsBase gs0 f5 m4) =
      mkSt 0x124#64 r6 fsBase gs0 f5 m7 := by
    refine (stepRaw_mkSt 0x100#64 0x120#64 83 0x20 gccHash2CanaryImg (.store64 { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0#64 } .rdi) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x120#64 r6 fsBase gs0 f5 m4).regs .rsp = fb := rfl
    have hd : (mkSt 0x120#64 r6 fsBase gs0 f5 m4).regs .rdi = x1 := rfl
    rw [hr, hd]; dsimp only [mkSt]; rw [hm7]; rfl
  let r8 := regUpd r6 .rsi y1; let f8 := (evalAluFlags64 .xor y 0x0000000087654321#64 (nd 7)).2
  have st8 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 7) (mkSt 0x124#64 r6 fsBase gs0 f5 m7) =
      mkSt 0x127#64 r8 fsBase gs0 f8 m7 := by
    refine (stepRaw_mkSt 0x100#64 0x124#64 83 0x24 gccHash2CanaryImg (.aluRR64 .xor .rsi .rax) 3 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]
    have hs : r6 .rsi = y := by dsimp only [r6, r5, r3, r2, r1, regUpd]; exact hrsi0
    have ha : r6 .rax = 0x0000000087654321#64 := rfl
    rw [hs, ha]; rfl
  have st9 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 8) (mkSt 0x127#64 r8 fsBase gs0 f8 m7) =
      mkSt 0x12C#64 r8 fsBase gs0 f8 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x127#64 83 0x27 gccHash2CanaryImg (.store64 { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 8#64 } .rsi) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x127#64 r8 fsBase gs0 f8 m7).regs .rsp = fb := rfl
    have hs : (mkSt 0x127#64 r8 fsBase gs0 f8 m7).regs .rsi = y1 := rfl
    rw [hr, hs]; dsimp only [mkSt]; rw [hm9]; rfl
  let r10 := regUpd r8 .rax x1
  have st10 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 9) (mkSt 0x12C#64 r8 fsBase gs0 f8 m9) =
      mkSt 0x130#64 r10 fsBase gs0 f8 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x12C#64 83 0x2C gccHash2CanaryImg (.load64 .rax { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0#64 }) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x12C#64 r8 fsBase gs0 f8 m9).regs .rsp = fb := rfl
    rw [hr]; dsimp only [mkSt]; rw [hread_0_raw]; rfl
  let r11 := regUpd r10 .rax (x1 + x1 * 4#64)
  have st11 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 10) (mkSt 0x130#64 r10 fsBase gs0 f8 m9) =
      mkSt 0x134#64 r11 fsBase gs0 f8 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x130#64 83 0x30 gccHash2CanaryImg (.lea64 .rax { seg := none, addr32 := false, kind := .baseDisp (some .rax) (some (.rax, 4)) 0#64 }) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, evalEffectiveAddr, mkSt]
    have ha : r10 .rax = x1 := rfl
    rw [ha, BitVec.add_zero]; rfl
  let r12 := regUpd r11 .rax (gccHash2Spec x y)
  let f12 := (evalAluFlags64 .xor (x1 + x1 * 4#64) y1 (nd 11)).2
  have st12 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 11) (mkSt 0x134#64 r11 fsBase gs0 f8 m9) =
      mkSt 0x139#64 r12 fsBase gs0 f12 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x134#64 83 0x34 gccHash2CanaryImg (.aluRM64 .xor .rax { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 8#64 }) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x134#64 r11 fsBase gs0 f8 m9).regs .rsp = fb := rfl
    have ha : (mkSt 0x134#64 r11 fsBase gs0 f8 m9).regs .rax = x1 + x1 * 4#64 := rfl
    rw [hr, ha]; dsimp only [mkSt]; rw [hread_8_raw]; rfl
  let r13 := regUpd r12 .rdx c0
  have st13 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 12) (mkSt 0x139#64 r12 fsBase gs0 f12 m9) =
      mkSt 0x13E#64 r13 fsBase gs0 f12 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x139#64 83 0x39 gccHash2CanaryImg (.load64 .rdx { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0x18#64 }) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x139#64 r12 fsBase gs0 f12 m9).regs .rsp = fb := rfl
    rw [hr]; dsimp only [mkSt]; rw [hread_18_raw]; rfl
  let r14 := regUpd r13 .rdx (c0 - c0)
  let f14 := (evalAluFlags64 .sub c0 c0 (nd 13)).2
  have st14 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 13) (mkSt 0x13E#64 r13 fsBase gs0 f12 m9) =
      mkSt 0x147#64 r14 fsBase gs0 f14 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x13E#64 83 0x3E gccHash2CanaryImg (.aluRM64 .sub .rdx { seg := some .fs, addr32 := false, kind := .baseDisp none none 0x28#64 }) 9 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_fs28]
    have hd : (mkSt 0x13E#64 r13 fsBase gs0 f12 m9).regs .rdx = c0 := rfl
    rw [hd]; dsimp only [mkSt]; rw [hread_fs_raw]; rfl
  have st15 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 14) (mkSt 0x147#64 r14 fsBase gs0 f14 m9) =
      mkSt 0x149#64 r14 fsBase gs0 f14 m9 :=
    (stepRaw_mkSt 0x100#64 0x147#64 83 0x47 gccHash2CanaryImg (.jccRel false .ne 5#64) 2 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans
      (exec_jne_not_taken 0x147#64 5#64 2 (nd 14) r14 fsBase gs0 f14 m9 (zf_sub_self64 c0 (nd 13)))
  let r16 := regUpd r14 .rsp rsp0
  let f16 := (evalAluFlags64 .add fb 0x28#64 (nd 15)).2
  have st16 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 15) (mkSt 0x149#64 r14 fsBase gs0 f14 m9) =
      mkSt 0x14D#64 r16 fsBase gs0 f16 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x149#64 83 0x49 gccHash2CanaryImg (.aluImm64 .add .rsp 0x28#64) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    have hfb : fb + 0x28#64 = rsp0 := BitVec.sub_add_cancel rsp0 0x28#64
    have hr : (mkSt 0x149#64 r14 fsBase gs0 f14 m9).regs .rsp = fb := rfl
    dsimp only [execDecodedRealX64V2]; rw [hr]
    change mkSt 0x14D#64 (regUpd r14 .rsp (fb + 0x28#64)) fsBase gs0 f16 m9 = mkSt 0x14D#64 r16 fsBase gs0 f16 m9
    rw [hfb]
  have st17 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 16) (mkSt 0x14D#64 r16 fsBase gs0 f16 m9) =
      mkSt (readMem64 mem0 rsp0) (regUpd r16 .rsp (rsp0 + 8#64)) fsBase gs0 f16 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x14D#64 83 0x4D gccHash2CanaryImg (.ret false) 1 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]
    have hr : r16 .rsp = rsp0 := rfl
    rw [hr, hret_mem_raw]
  have hrun17 : runRawRealX64V2 0x100#64 83 gccHash2CanaryImg 17 nd (mkSt 0x100#64 regs0 fsBase gs0 fl0 mem0) =
      mkSt (readMem64 mem0 rsp0) (regUpd r16 .rsp (rsp0 + 8#64)) fsBase gs0 f16 m9 := by
    refine runRaw_step st1 ?_; refine runRaw_step st2 ?_; refine runRaw_step st3 ?_
    refine runRaw_step st4 ?_; refine runRaw_step st5 ?_; refine runRaw_step st6 ?_
    refine runRaw_step st7 ?_; refine runRaw_step st8 ?_; refine runRaw_step st9 ?_
    refine runRaw_step st10 ?_; refine runRaw_step st11 ?_; refine runRaw_step st12 ?_
    refine runRaw_step st13 ?_; refine runRaw_step st14 ?_; refine runRaw_step st15 ?_
    refine runRaw_step st16 ?_; refine runRaw_step st17 ?_; rfl
  dsimp only [mkSt] at hrun17 ⊢
  rw [hrun17]
  exact ⟨rfl, rfl, regUpd_eq r16 .rsp (rsp0 + 8#64), rfl, hout_raw⟩

/-- Universal `PrivateStackCanarySep` lifting proof for `rustc 1.102.0-nightly -C opt-level=2
    -Z stack-protector=all` (`88`B, `mov %fs:0x28, %rcx; cmp 0x10(%rsp), %rcx; jne __stack_chk_fail`): -/
theorem rust_unexposed_canary_verified
    (x y rsp0 fsBase : BitVec 64) (mem0 : ByteMem) (nd : Nat → UndefFlags)
    (s0 : RealX64PrefixState)
    (hrip0 : s0.rip = 0x100#64) (hfs0 : s0.fsBase = fsBase)
    (hrsp0 : s0.regs .rsp = rsp0) (hrdi0 : s0.regs .rdi = x) (hrsi0 : s0.regs .rsi = y)
    (hmem0 : s0.mem = mem0) (hrun0 : s0.exitKind = .running) (hnf0 : s0.fault = false)
    (hsep : PrivateStackCanarySep (rsp0 - 0x18#64) 0x18 fsBase) :
    let sf := runRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg 16 nd s0
    sf.fault = false ∧
    sf.rip = readMem64 mem0 rsp0 ∧
    sf.regs .rsp = rsp0 + 8#64 ∧
    sf.regs .rax = rustUnexposedSpec x y ∧
    (∀ a, (∀ off, off < 0x18 → a ≠ (rsp0 - 0x18#64) + BitVec.ofNat 64 off) → sf.mem a = mem0 a) := by
  cases s0 with | mk rip regs0 fs0 gs0 fl0 m0 ex0 flt0 =>
  dsimp only at hrip0 hfs0 hrsp0 hrdi0 hrsi0 hmem0 hrun0 hnf0
  subst rip fs0 m0 ex0 flt0
  let fb := rsp0 - 0x18#64
  let x1 := x + 0x12345678#64
  let y1 := 0x0000000087654321#64 ^^^ y
  have hread_0_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x10#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fb + 0#64) = x1 := by
    rw [readMem64_writeMem64_disjoint _ y1 (disjoint8_small_offsets fb (o1 := 8) (o2 := 0) (by decide) (by decide) (.inr (by decide))),
        readMem64_writeMem64_same]
  have hread_8_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x10#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fb + 8#64) = y1 :=
    readMem64_writeMem64_same _ (fb + 8#64) y1
  have hread_10_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x10#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fb + 0x10#64) = readMem64 mem0 (fsBase + 0x28#64) := by
    rw [readMem64_writeMem64_disjoint _ y1 (disjoint8_small_offsets fb (o1 := 8) (o2 := 0x10) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_disjoint _ x1 (disjoint8_small_offsets fb (o1 := 0) (o2 := 0x10) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_same]
  have hread_fs_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x10#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fsBase + 0x28#64) = readMem64 mem0 (fsBase + 0x28#64) := by
    rw [readMem64_writeMem64_disjoint _ y1 (privateStackCanarySep_disjoint8 hsep (slotOff := 8) (by decide)),
        readMem64_writeMem64_disjoint _ x1 (privateStackCanarySep_disjoint8 hsep (slotOff := 0) (by decide)),
        readMem64_writeMem64_disjoint mem0 _ (privateStackCanarySep_disjoint8 hsep (slotOff := 0x10) (by decide))]
  have hret_mem_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x10#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) rsp0 = readMem64 mem0 rsp0 := by
    have hrsp_fb : rsp0 = fb + 0x18#64 := (BitVec.sub_add_cancel (x := rsp0) (y := 0x18#64)).symm
    rw [hrsp_fb,
        readMem64_writeMem64_disjoint _ y1 (disjoint8_small_offsets fb (o1 := 8) (o2 := 0x18) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_disjoint _ x1 (disjoint8_small_offsets fb (o1 := 0) (o2 := 0x18) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_disjoint mem0 _ (disjoint8_small_offsets fb (o1 := 0x10) (o2 := 0x18) (by decide) (by decide) (.inl (by decide)))]
  have hout_raw : ∀ a, (∀ off, off < 0x18 → a ≠ fb + BitVec.ofNat 64 off) →
      writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x10#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1 a = mem0 a := by
    intro a hout
    rw [writeMem64_slot_outside_frame _ y1 (slotOff := 8) (by decide) hout,
        writeMem64_slot_outside_frame _ x1 (slotOff := 0) (by decide) hout,
        writeMem64_slot_outside_frame mem0 _ (slotOff := 0x10) (by decide) hout]
  generalize hm3 : writeMem64 mem0 (fb + 0x10#64) (readMem64 mem0 (fsBase + 0x28#64)) = m3 at hread_0_raw hread_8_raw hread_10_raw hread_fs_raw hret_mem_raw hout_raw
  generalize hm5 : writeMem64 m3 (fb + 0#64) x1 = m5 at hread_0_raw hread_8_raw hread_10_raw hread_fs_raw hret_mem_raw hout_raw
  generalize hm8 : writeMem64 m5 (fb + 8#64) y1 = m8 at hread_0_raw hread_8_raw hread_10_raw hread_fs_raw hret_mem_raw hout_raw
  generalize hc : readMem64 mem0 (fsBase + 0x28#64) = c0 at hm3 hread_10_raw hread_fs_raw
  change (let sf := runRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg 16 nd (mkSt 0x100#64 regs0 fsBase gs0 fl0 mem0); _)
  let r1 := regUpd regs0 .rsp fb; let f1 := (evalAluFlags64 .sub rsp0 0x18#64 (nd 0)).2
  have st1 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 0) (mkSt 0x100#64 regs0 fsBase gs0 fl0 mem0) =
      mkSt 0x104#64 r1 fsBase gs0 f1 mem0 := by
    refine (stepRaw_mkSt 0x100#64 0x100#64 88 0 rustUnexposedCanaryImg (.aluImm64 .sub .rsp 0x18#64) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]; rw [hrsp0]; rfl
  let r2 := regUpd r1 .rax c0
  have st2 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 1) (mkSt 0x104#64 r1 fsBase gs0 f1 mem0) =
      mkSt 0x10D#64 r2 fsBase gs0 f1 mem0 := by
    refine (stepRaw_mkSt 0x100#64 0x104#64 88 4 rustUnexposedCanaryImg (.load64 .rax { seg := some .fs, addr32 := false, kind := .baseDisp none none 0x28#64 }) 9 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_fs28]; dsimp only [mkSt]; rw [hc]; rfl
  have st3 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 2) (mkSt 0x10D#64 r2 fsBase gs0 f1 mem0) =
      mkSt 0x112#64 r2 fsBase gs0 f1 m3 := by
    refine (stepRaw_mkSt 0x100#64 0x10D#64 88 0x0D rustUnexposedCanaryImg (.store64 { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0x10#64 } .rax) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x10D#64 r2 fsBase gs0 f1 mem0).regs .rsp = fb := rfl
    have ha : (mkSt 0x10D#64 r2 fsBase gs0 f1 mem0).regs .rax = c0 := rfl
    rw [hr, ha]; dsimp only [mkSt]; rw [hm3]; rfl
  let r4 := regUpd r2 .rdi x1; let f4 := (evalAluFlags64 .add x 0x12345678#64 (nd 3)).2
  have st4 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 3) (mkSt 0x112#64 r2 fsBase gs0 f1 m3) =
      mkSt 0x119#64 r4 fsBase gs0 f4 m3 := by
    refine (stepRaw_mkSt 0x100#64 0x112#64 88 0x12 rustUnexposedCanaryImg (.aluImm64 .add .rdi 0x12345678#64) 7 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]
    have : r2 .rdi = x := by dsimp only [r2, r1, regUpd]; exact hrdi0
    rw [this]; rfl
  have st5 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 4) (mkSt 0x119#64 r4 fsBase gs0 f4 m3) =
      mkSt 0x11D#64 r4 fsBase gs0 f4 m5 := by
    refine (stepRaw_mkSt 0x100#64 0x119#64 88 0x19 rustUnexposedCanaryImg (.store64 { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0#64 } .rdi) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x119#64 r4 fsBase gs0 f4 m3).regs .rsp = fb := rfl
    have hd : (mkSt 0x119#64 r4 fsBase gs0 f4 m3).regs .rdi = x1 := rfl
    rw [hr, hd]; dsimp only [mkSt]; rw [hm5]; rfl
  let r6 := regUpd r4 .rax 0x0000000087654321#64
  have st6 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 5) (mkSt 0x11D#64 r4 fsBase gs0 f4 m5) =
      mkSt 0x122#64 r6 fsBase gs0 f4 m5 :=
    (stepRaw_mkSt 0x100#64 0x11D#64 88 0x1D rustUnexposedCanaryImg (.movImm32 .rax 0x87654321#32) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans rfl
  let r7 := regUpd r6 .rax y1; let f7 := (evalAluFlags64 .xor 0x0000000087654321#64 y (nd 6)).2
  have st7 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 6) (mkSt 0x122#64 r6 fsBase gs0 f4 m5) =
      mkSt 0x125#64 r7 fsBase gs0 f7 m5 := by
    refine (stepRaw_mkSt 0x100#64 0x122#64 88 0x22 rustUnexposedCanaryImg (.aluRR64 .xor .rax .rsi) 3 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]
    have hs : r6 .rsi = y := by dsimp only [r6, r4, r2, r1, regUpd]; exact hrsi0
    have ha : r6 .rax = 0x0000000087654321#64 := rfl
    rw [hs, ha]; rfl
  have st8 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 7) (mkSt 0x125#64 r7 fsBase gs0 f7 m5) =
      mkSt 0x12A#64 r7 fsBase gs0 f7 m8 := by
    refine (stepRaw_mkSt 0x100#64 0x125#64 88 0x25 rustUnexposedCanaryImg (.store64 { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 8#64 } .rax) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x125#64 r7 fsBase gs0 f7 m5).regs .rsp = fb := rfl
    have ha : (mkSt 0x125#64 r7 fsBase gs0 f7 m5).regs .rax = y1 := rfl
    rw [hr, ha]; dsimp only [mkSt]; rw [hm8]; rfl
  let r9 := regUpd r7 .rax 0x9E3779B97F4A7C15#64
  have st9 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 8) (mkSt 0x12A#64 r7 fsBase gs0 f7 m8) =
      mkSt 0x134#64 r9 fsBase gs0 f7 m8 :=
    (stepRaw_mkSt 0x100#64 0x12A#64 88 0x2A rustUnexposedCanaryImg (.movImm64 .rax 0x9E3779B97F4A7C15#64) 10 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans rfl
  let r10 := regUpd r9 .rax (0x9E3779B97F4A7C15#64 * x1)
  let f10 := (evalImul64 0x9E3779B97F4A7C15#64 x1 (nd 9)).2
  have st10 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 9) (mkSt 0x134#64 r9 fsBase gs0 f7 m8) =
      mkSt 0x139#64 r10 fsBase gs0 f10 m8 := by
    refine (stepRaw_mkSt 0x100#64 0x134#64 88 0x34 rustUnexposedCanaryImg (.imulRM64 .rax { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0#64 }) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x134#64 r9 fsBase gs0 f7 m8).regs .rsp = fb := rfl
    have ha : (mkSt 0x134#64 r9 fsBase gs0 f7 m8).regs .rax = 0x9E3779B97F4A7C15#64 := rfl
    rw [hr, ha]; dsimp only [mkSt]; rw [hread_0_raw]; rfl
  let r11 := regUpd r10 .rax (rustUnexposedSpec x y)
  let f11 := (evalAluFlags64 .xor (0x9E3779B97F4A7C15#64 * x1) y1 (nd 10)).2
  have st11 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 10) (mkSt 0x139#64 r10 fsBase gs0 f10 m8) =
      mkSt 0x13E#64 r11 fsBase gs0 f11 m8 := by
    refine (stepRaw_mkSt 0x100#64 0x139#64 88 0x39 rustUnexposedCanaryImg (.aluRM64 .xor .rax { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 8#64 }) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x139#64 r10 fsBase gs0 f10 m8).regs .rsp = fb := rfl
    have ha : (mkSt 0x139#64 r10 fsBase gs0 f10 m8).regs .rax = 0x9E3779B97F4A7C15#64 * x1 := rfl
    rw [hr, ha]; dsimp only [mkSt]; rw [hread_8_raw]; rfl
  let r12 := regUpd r11 .rcx c0
  have st12 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 11) (mkSt 0x13E#64 r11 fsBase gs0 f11 m8) =
      mkSt 0x147#64 r12 fsBase gs0 f11 m8 := by
    refine (stepRaw_mkSt 0x100#64 0x13E#64 88 0x3E rustUnexposedCanaryImg (.load64 .rcx { seg := some .fs, addr32 := false, kind := .baseDisp none none 0x28#64 }) 9 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_fs28]; dsimp only [mkSt]; rw [hread_fs_raw]; rfl
  let f13 := (evalAluFlags64 .cmp c0 c0 (nd 12)).2
  have st13 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 12) (mkSt 0x147#64 r12 fsBase gs0 f11 m8) =
      mkSt 0x14C#64 r12 fsBase gs0 f13 m8 := by
    refine (stepRaw_mkSt 0x100#64 0x147#64 88 0x47 rustUnexposedCanaryImg (.aluRM64 .cmp .rcx { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0x10#64 }) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x147#64 r12 fsBase gs0 f11 m8).regs .rsp = fb := rfl
    have hcx : (mkSt 0x147#64 r12 fsBase gs0 f11 m8).regs .rcx = c0 := rfl
    rw [hr, hcx]; dsimp only [mkSt]; rw [hread_10_raw]; rfl
  have st14 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 13) (mkSt 0x14C#64 r12 fsBase gs0 f13 m8) =
      mkSt 0x14E#64 r12 fsBase gs0 f13 m8 :=
    (stepRaw_mkSt 0x100#64 0x14C#64 88 0x4C rustUnexposedCanaryImg (.jccRel false .ne 5#64) 2 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans
      (exec_jne_not_taken 0x14C#64 5#64 2 (nd 13) r12 fsBase gs0 f13 m8 (zf_cmp_self64 c0 (nd 12)))
  let r15 := regUpd r12 .rsp rsp0
  let f15 := (evalAluFlags64 .add fb 0x18#64 (nd 14)).2
  have st15 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 14) (mkSt 0x14E#64 r12 fsBase gs0 f13 m8) =
      mkSt 0x152#64 r15 fsBase gs0 f15 m8 := by
    refine (stepRaw_mkSt 0x100#64 0x14E#64 88 0x4E rustUnexposedCanaryImg (.aluImm64 .add .rsp 0x18#64) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    have hfb : fb + 0x18#64 = rsp0 := BitVec.sub_add_cancel rsp0 0x18#64
    have hr : (mkSt 0x14E#64 r12 fsBase gs0 f13 m8).regs .rsp = fb := rfl
    dsimp only [execDecodedRealX64V2]; rw [hr]
    change mkSt 0x152#64 (regUpd r12 .rsp (fb + 0x18#64)) fsBase gs0 f15 m8 = mkSt 0x152#64 r15 fsBase gs0 f15 m8
    rw [hfb]
  have st16 : stepRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg (nd 15) (mkSt 0x152#64 r15 fsBase gs0 f15 m8) =
      mkSt (readMem64 mem0 rsp0) (regUpd r15 .rsp (rsp0 + 8#64)) fsBase gs0 f15 m8 := by
    refine (stepRaw_mkSt 0x100#64 0x152#64 88 0x52 rustUnexposedCanaryImg (.ret false) 1 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]
    have hr : r15 .rsp = rsp0 := rfl
    rw [hr, hret_mem_raw]
  have hrun16 : runRawRealX64V2 0x100#64 88 rustUnexposedCanaryImg 16 nd (mkSt 0x100#64 regs0 fsBase gs0 fl0 mem0) =
      mkSt (readMem64 mem0 rsp0) (regUpd r15 .rsp (rsp0 + 8#64)) fsBase gs0 f15 m8 := by
    refine runRaw_step st1 ?_; refine runRaw_step st2 ?_; refine runRaw_step st3 ?_
    refine runRaw_step st4 ?_; refine runRaw_step st5 ?_; refine runRaw_step st6 ?_
    refine runRaw_step st7 ?_; refine runRaw_step st8 ?_; refine runRaw_step st9 ?_
    refine runRaw_step st10 ?_; refine runRaw_step st11 ?_; refine runRaw_step st12 ?_
    refine runRaw_step st13 ?_; refine runRaw_step st14 ?_; refine runRaw_step st15 ?_
    refine runRaw_step st16 ?_; rfl
  dsimp only [mkSt] at hrun16 ⊢
  rw [hrun16]
  exact ⟨rfl, rfl, regUpd_eq r15 .rsp (rsp0 + 8#64), rfl, hout_raw⟩

/-- Universal `PrivateStackCanarySep` lifting proof for the classic `xor %fs:0x28, %rdx` (`0x33`) epilogue idiom: -/
theorem xor_fs28_canary_verified
    (x y rsp0 fsBase : BitVec 64) (mem0 : ByteMem) (nd : Nat → UndefFlags)
    (s0 : RealX64PrefixState)
    (hrip0 : s0.rip = 0x100#64) (hfs0 : s0.fsBase = fsBase)
    (hrsp0 : s0.regs .rsp = rsp0) (hrdi0 : s0.regs .rdi = x) (hrsi0 : s0.regs .rsi = y)
    (hmem0 : s0.mem = mem0) (hrun0 : s0.exitKind = .running) (hnf0 : s0.fault = false)
    (hsep : PrivateStackCanarySep (rsp0 - 0x28#64) 0x28 fsBase) :
    let sf := runRawRealX64V2 0x100#64 83 xorFs28CanaryImg 17 nd s0
    sf.fault = false ∧
    sf.rip = readMem64 mem0 rsp0 ∧
    sf.regs .rsp = rsp0 + 8#64 ∧
    sf.regs .rax = gccHash2Spec x y := by
  cases s0 with | mk rip regs0 fs0 gs0 fl0 m0 ex0 flt0 =>
  dsimp only at hrip0 hfs0 hrsp0 hrdi0 hrsi0 hmem0 hrun0 hnf0
  subst rip fs0 m0 ex0 flt0
  let fb := rsp0 - 0x28#64
  let x1 := x + 0x12345678#64
  let y1 := y ^^^ 0x0000000087654321#64
  have hread_0_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fb + 0#64) = x1 := by
    rw [readMem64_writeMem64_disjoint _ y1 (disjoint8_small_offsets fb (o1 := 8) (o2 := 0) (by decide) (by decide) (.inr (by decide))),
        readMem64_writeMem64_same]
  have hread_8_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fb + 8#64) = y1 :=
    readMem64_writeMem64_same _ (fb + 8#64) y1
  have hread_18_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fb + 0x18#64) = readMem64 mem0 (fsBase + 0x28#64) := by
    rw [readMem64_writeMem64_disjoint _ y1 (disjoint8_small_offsets fb (o1 := 8) (o2 := 0x18) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_disjoint _ x1 (disjoint8_small_offsets fb (o1 := 0) (o2 := 0x18) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_same]
  have hread_fs_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) (fsBase + 0x28#64) = readMem64 mem0 (fsBase + 0x28#64) := by
    rw [readMem64_writeMem64_disjoint _ y1 (privateStackCanarySep_disjoint8 hsep (slotOff := 8) (by decide)),
        readMem64_writeMem64_disjoint _ x1 (privateStackCanarySep_disjoint8 hsep (slotOff := 0) (by decide)),
        readMem64_writeMem64_disjoint mem0 _ (privateStackCanarySep_disjoint8 hsep (slotOff := 0x18) (by decide))]
  have hret_mem_raw : readMem64 (writeMem64 (writeMem64 (writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64))) (fb + 0#64) x1) (fb + 8#64) y1) rsp0 = readMem64 mem0 rsp0 := by
    have hrsp_fb : rsp0 = fb + 0x28#64 := (BitVec.sub_add_cancel (x := rsp0) (y := 0x28#64)).symm
    rw [hrsp_fb,
        readMem64_writeMem64_disjoint _ y1 (disjoint8_small_offsets fb (o1 := 8) (o2 := 0x28) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_disjoint _ x1 (disjoint8_small_offsets fb (o1 := 0) (o2 := 0x28) (by decide) (by decide) (.inl (by decide))),
        readMem64_writeMem64_disjoint mem0 _ (disjoint8_small_offsets fb (o1 := 0x18) (o2 := 0x28) (by decide) (by decide) (.inl (by decide)))]
  generalize hm4 : writeMem64 mem0 (fb + 0x18#64) (readMem64 mem0 (fsBase + 0x28#64)) = m4 at hread_0_raw hread_8_raw hread_18_raw hread_fs_raw hret_mem_raw
  generalize hm7 : writeMem64 m4 (fb + 0#64) x1 = m7 at hread_0_raw hread_8_raw hread_18_raw hread_fs_raw hret_mem_raw
  generalize hm9 : writeMem64 m7 (fb + 8#64) y1 = m9 at hread_0_raw hread_8_raw hread_18_raw hread_fs_raw hret_mem_raw
  generalize hc : readMem64 mem0 (fsBase + 0x28#64) = c0 at hm4 hread_18_raw hread_fs_raw
  change (let sf := runRawRealX64V2 0x100#64 83 xorFs28CanaryImg 17 nd (mkSt 0x100#64 regs0 fsBase gs0 fl0 mem0); _)
  let r1 := regUpd regs0 .rsp fb; let f1 := (evalAluFlags64 .sub rsp0 0x28#64 (nd 0)).2
  have st1 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 0) (mkSt 0x100#64 regs0 fsBase gs0 fl0 mem0) =
      mkSt 0x104#64 r1 fsBase gs0 f1 mem0 := by
    refine (stepRaw_mkSt 0x100#64 0x100#64 83 0 xorFs28CanaryImg (.aluImm64 .sub .rsp 0x28#64) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]; rw [hrsp0]; rfl
  let r2 := regUpd r1 .rdi x1; let f2 := (evalAluFlags64 .add x 0x12345678#64 (nd 1)).2
  have st2 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 1) (mkSt 0x104#64 r1 fsBase gs0 f1 mem0) =
      mkSt 0x10B#64 r2 fsBase gs0 f2 mem0 := by
    refine (stepRaw_mkSt 0x100#64 0x104#64 83 4 xorFs28CanaryImg (.aluImm64 .add .rdi 0x12345678#64) 7 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]
    have : r1 .rdi = x := by dsimp only [r1, regUpd]; exact hrdi0
    rw [this]; rfl
  let r3 := regUpd r2 .rax c0
  have st3 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 2) (mkSt 0x10B#64 r2 fsBase gs0 f2 mem0) =
      mkSt 0x114#64 r3 fsBase gs0 f2 mem0 := by
    refine (stepRaw_mkSt 0x100#64 0x10B#64 83 0x0B xorFs28CanaryImg (.load64 .rax { seg := some .fs, addr32 := false, kind := .baseDisp none none 0x28#64 }) 9 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_fs28]; dsimp only [mkSt]; rw [hc]; rfl
  have st4 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 3) (mkSt 0x114#64 r3 fsBase gs0 f2 mem0) =
      mkSt 0x119#64 r3 fsBase gs0 f2 m4 := by
    refine (stepRaw_mkSt 0x100#64 0x114#64 83 0x14 xorFs28CanaryImg (.store64 { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0x18#64 } .rax) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x114#64 r3 fsBase gs0 f2 mem0).regs .rsp = fb := rfl
    have ha : (mkSt 0x114#64 r3 fsBase gs0 f2 mem0).regs .rax = c0 := rfl
    rw [hr, ha]; dsimp only [mkSt]; rw [hm4]; rfl
  let r5 := regUpd r3 .rax ((c0.extractLsb' 0 32 ^^^ c0.extractLsb' 0 32).zeroExtend 64)
  let f5 := (evalAluFlags32 .xor (c0.extractLsb' 0 32) (c0.extractLsb' 0 32) (nd 4)).2
  have st5 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 4) (mkSt 0x119#64 r3 fsBase gs0 f2 m4) =
      mkSt 0x11B#64 r5 fsBase gs0 f5 m4 :=
    (stepRaw_mkSt 0x100#64 0x119#64 83 0x19 xorFs28CanaryImg (.aluRR32 .xor .rax .rax) 2 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans rfl
  let r6 := regUpd r5 .rax 0x0000000087654321#64
  have st6 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 5) (mkSt 0x11B#64 r5 fsBase gs0 f5 m4) =
      mkSt 0x120#64 r6 fsBase gs0 f5 m4 :=
    (stepRaw_mkSt 0x100#64 0x11B#64 83 0x1B xorFs28CanaryImg (.movImm32 .rax 0x87654321#32) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans rfl
  have st7 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 6) (mkSt 0x120#64 r6 fsBase gs0 f5 m4) =
      mkSt 0x124#64 r6 fsBase gs0 f5 m7 := by
    refine (stepRaw_mkSt 0x100#64 0x120#64 83 0x20 xorFs28CanaryImg (.store64 { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0#64 } .rdi) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x120#64 r6 fsBase gs0 f5 m4).regs .rsp = fb := rfl
    have hd : (mkSt 0x120#64 r6 fsBase gs0 f5 m4).regs .rdi = x1 := rfl
    rw [hr, hd]; dsimp only [mkSt]; rw [hm7]; rfl
  let r8 := regUpd r6 .rsi y1; let f8 := (evalAluFlags64 .xor y 0x0000000087654321#64 (nd 7)).2
  have st8 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 7) (mkSt 0x124#64 r6 fsBase gs0 f5 m7) =
      mkSt 0x127#64 r8 fsBase gs0 f8 m7 := by
    refine (stepRaw_mkSt 0x100#64 0x124#64 83 0x24 xorFs28CanaryImg (.aluRR64 .xor .rsi .rax) 3 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]
    have hs : r6 .rsi = y := by dsimp only [r6, r5, r3, r2, r1, regUpd]; exact hrsi0
    have ha : r6 .rax = 0x0000000087654321#64 := rfl
    rw [hs, ha]; rfl
  have st9 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 8) (mkSt 0x127#64 r8 fsBase gs0 f8 m7) =
      mkSt 0x12C#64 r8 fsBase gs0 f8 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x127#64 83 0x27 xorFs28CanaryImg (.store64 { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 8#64 } .rsi) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x127#64 r8 fsBase gs0 f8 m7).regs .rsp = fb := rfl
    have hs : (mkSt 0x127#64 r8 fsBase gs0 f8 m7).regs .rsi = y1 := rfl
    rw [hr, hs]; dsimp only [mkSt]; rw [hm9]; rfl
  let r10 := regUpd r8 .rax x1
  have st10 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 9) (mkSt 0x12C#64 r8 fsBase gs0 f8 m9) =
      mkSt 0x130#64 r10 fsBase gs0 f8 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x12C#64 83 0x2C xorFs28CanaryImg (.load64 .rax { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0#64 }) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x12C#64 r8 fsBase gs0 f8 m9).regs .rsp = fb := rfl
    rw [hr]; dsimp only [mkSt]; rw [hread_0_raw]; rfl
  let r11 := regUpd r10 .rax (x1 + x1 * 4#64)
  have st11 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 10) (mkSt 0x130#64 r10 fsBase gs0 f8 m9) =
      mkSt 0x134#64 r11 fsBase gs0 f8 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x130#64 83 0x30 xorFs28CanaryImg (.lea64 .rax { seg := none, addr32 := false, kind := .baseDisp (some .rax) (some (.rax, 4)) 0#64 }) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, evalEffectiveAddr, mkSt]
    have ha : r10 .rax = x1 := rfl
    rw [ha, BitVec.add_zero]; rfl
  let r12 := regUpd r11 .rax (gccHash2Spec x y)
  let f12 := (evalAluFlags64 .xor (x1 + x1 * 4#64) y1 (nd 11)).2
  have st12 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 11) (mkSt 0x134#64 r11 fsBase gs0 f8 m9) =
      mkSt 0x139#64 r12 fsBase gs0 f12 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x134#64 83 0x34 xorFs28CanaryImg (.aluRM64 .xor .rax { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 8#64 }) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x134#64 r11 fsBase gs0 f8 m9).regs .rsp = fb := rfl
    have ha : (mkSt 0x134#64 r11 fsBase gs0 f8 m9).regs .rax = x1 + x1 * 4#64 := rfl
    rw [hr, ha]; dsimp only [mkSt]; rw [hread_8_raw]; rfl
  let r13 := regUpd r12 .rdx c0
  have st13 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 12) (mkSt 0x139#64 r12 fsBase gs0 f12 m9) =
      mkSt 0x13E#64 r13 fsBase gs0 f12 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x139#64 83 0x39 xorFs28CanaryImg (.load64 .rdx { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0x18#64 }) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x139#64 r12 fsBase gs0 f12 m9).regs .rsp = fb := rfl
    rw [hr]; dsimp only [mkSt]; rw [hread_18_raw]; rfl
  let r14 := regUpd r13 .rdx (c0 ^^^ c0)
  let f14 := (evalAluFlags64 .xor c0 c0 (nd 13)).2
  have st14 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 13) (mkSt 0x13E#64 r13 fsBase gs0 f12 m9) =
      mkSt 0x147#64 r14 fsBase gs0 f14 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x13E#64 83 0x3E xorFs28CanaryImg (.aluRM64 .xor .rdx { seg := some .fs, addr32 := false, kind := .baseDisp none none 0x28#64 }) 9 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_fs28]
    have hd : (mkSt 0x13E#64 r13 fsBase gs0 f12 m9).regs .rdx = c0 := rfl
    rw [hd]; dsimp only [mkSt]; rw [hread_fs_raw]; rfl
  have st15 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 14) (mkSt 0x147#64 r14 fsBase gs0 f14 m9) =
      mkSt 0x149#64 r14 fsBase gs0 f14 m9 :=
    (stepRaw_mkSt 0x100#64 0x147#64 83 0x47 xorFs28CanaryImg (.jccRel false .ne 5#64) 2 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans
      (exec_jne_not_taken 0x147#64 5#64 2 (nd 14) r14 fsBase gs0 f14 m9 (zf_xor_self64 c0 (nd 13)))
  let r16 := regUpd r14 .rsp rsp0
  let f16 := (evalAluFlags64 .add fb 0x28#64 (nd 15)).2
  have st16 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 15) (mkSt 0x149#64 r14 fsBase gs0 f14 m9) =
      mkSt 0x14D#64 r16 fsBase gs0 f16 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x149#64 83 0x49 xorFs28CanaryImg (.aluImm64 .add .rsp 0x28#64) 4 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    have hfb : fb + 0x28#64 = rsp0 := BitVec.sub_add_cancel rsp0 0x28#64
    have hr : (mkSt 0x149#64 r14 fsBase gs0 f14 m9).regs .rsp = fb := rfl
    dsimp only [execDecodedRealX64V2]; rw [hr]
    change mkSt 0x14D#64 (regUpd r14 .rsp (fb + 0x28#64)) fsBase gs0 f16 m9 = mkSt 0x14D#64 r16 fsBase gs0 f16 m9
    rw [hfb]
  have st17 : stepRawRealX64V2 0x100#64 83 xorFs28CanaryImg (nd 16) (mkSt 0x14D#64 r16 fsBase gs0 f16 m9) =
      mkSt (readMem64 mem0 rsp0) (regUpd r16 .rsp (rsp0 + 8#64)) fsBase gs0 f16 m9 := by
    refine (stepRaw_mkSt 0x100#64 0x14D#64 83 0x4D xorFs28CanaryImg (.ret false) 1 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2, mkSt]
    have hr : r16 .rsp = rsp0 := rfl
    rw [hr, hret_mem_raw]
  have hrun17 : runRawRealX64V2 0x100#64 83 xorFs28CanaryImg 17 nd (mkSt 0x100#64 regs0 fsBase gs0 fl0 mem0) =
      mkSt (readMem64 mem0 rsp0) (regUpd r16 .rsp (rsp0 + 8#64)) fsBase gs0 f16 m9 := by
    refine runRaw_step st1 ?_; refine runRaw_step st2 ?_; refine runRaw_step st3 ?_
    refine runRaw_step st4 ?_; refine runRaw_step st5 ?_; refine runRaw_step st6 ?_
    refine runRaw_step st7 ?_; refine runRaw_step st8 ?_; refine runRaw_step st9 ?_
    refine runRaw_step st10 ?_; refine runRaw_step st11 ?_; refine runRaw_step st12 ?_
    refine runRaw_step st13 ?_; refine runRaw_step st14 ?_; refine runRaw_step st15 ?_
    refine runRaw_step st16 ?_; refine runRaw_step st17 ?_; rfl
  dsimp only [mkSt] at hrun17 ⊢
  rw [hrun17]
  exact ⟨rfl, rfl, regUpd_eq r16 .rsp (rsp0 + 8#64), rfl⟩

/-- Two-sided sensitivity theorem (`gcc_hash2_canary_corrupted_traps_to_stack_chk_fail`):
    Entering the epilogue (`0x139`: `mov 0x18(%rsp), %rdx; sub %fs:0x28, %rdx; jne 0x14E`)
    when `[fb + 0x18]` has been corrupted to ANY `badCanary ≠ readMem64 m (fsBase + 0x28#64)`
    sets `ZF = false` and branches directly to `0x14E#64` (`call __stack_chk_fail`), never reaching `ret`! -/
theorem gcc_hash2_canary_corrupted_traps_to_stack_chk_fail
    (fb fsBase : BitVec 64) (m : ByteMem) (nd : Nat → UndefFlags)
    (s : RealX64PrefixState)
    (hrip : s.rip = 0x139#64) (hfs : s.fsBase = fsBase)
    (hrsp : s.regs .rsp = fb) (hmem : s.mem = m)
    (hrun : s.exitKind = .running) (hnf : s.fault = false)
    (hcorrupt : readMem64 m (fb + 0x18#64) ≠ readMem64 m (fsBase + 0x28#64)) :
    let sf := runRawRealX64V2 0x100#64 83 gccHash2CanaryImg 3 nd s
    sf.fault = false ∧ sf.rip = 0x14E#64 := by
  cases s with | mk rip regs0 fs0 gs0 fl0 m0 ex0 flt0 =>
  dsimp only at hrip hfs hrsp hmem hrun hnf
  subst rip fs0 m0 ex0 flt0
  generalize hb : readMem64 m (fb + 0x18#64) = bad at hcorrupt
  generalize hc : readMem64 m (fsBase + 0x28#64) = ref at hcorrupt
  change (let sf := runRawRealX64V2 0x100#64 83 gccHash2CanaryImg 3 nd (mkSt 0x139#64 regs0 fsBase gs0 fl0 m); _)
  let r1 := regUpd regs0 .rdx bad
  have st1 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 0) (mkSt 0x139#64 regs0 fsBase gs0 fl0 m) =
      mkSt 0x13E#64 r1 fsBase gs0 fl0 m := by
    refine (stepRaw_mkSt 0x100#64 0x139#64 83 0x39 gccHash2CanaryImg (.load64 .rdx { seg := none, addr32 := false, kind := .baseDisp (some .rsp) none 0x18#64 }) 5 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_rspDisp]
    have hr : (mkSt 0x139#64 regs0 fsBase gs0 fl0 m).regs .rsp = fb := hrsp
    rw [hr]; dsimp only [mkSt]; rw [hb]; rfl
  let r2 := regUpd r1 .rdx (bad - ref)
  let f2 := (evalAluFlags64 .sub bad ref (nd 1)).2
  have st2 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 1) (mkSt 0x13E#64 r1 fsBase gs0 fl0 m) =
      mkSt 0x147#64 r2 fsBase gs0 f2 m := by
    refine (stepRaw_mkSt 0x100#64 0x13E#64 83 0x3E gccHash2CanaryImg (.aluRM64 .sub .rdx { seg := some .fs, addr32 := false, kind := .baseDisp none none 0x28#64 }) 9 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ?_
    dsimp only [execDecodedRealX64V2]; rw [evalLinear_fs28]
    have hd : (mkSt 0x13E#64 r1 fsBase gs0 fl0 m).regs .rdx = bad := rfl
    rw [hd]; dsimp only [mkSt]; rw [hc]; rfl
  have st3 : stepRawRealX64V2 0x100#64 83 gccHash2CanaryImg (nd 2) (mkSt 0x147#64 r2 fsBase gs0 f2 m) =
      mkSt 0x14E#64 r2 fsBase gs0 f2 m :=
    (stepRaw_mkSt 0x100#64 0x147#64 83 0x47 gccHash2CanaryImg (.jccRel false .ne 5#64) 2 _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans
      (exec_jne_taken 0x147#64 5#64 2 (nd 2) r2 fsBase gs0 f2 m (zf_sub_ne64 hcorrupt (nd 1)))
  have hrun3 : runRawRealX64V2 0x100#64 83 gccHash2CanaryImg 3 nd (mkSt 0x139#64 regs0 fsBase gs0 fl0 m) =
      mkSt 0x14E#64 r2 fsBase gs0 f2 m := by
    refine runRaw_step st1 ?_; refine runRaw_step st2 ?_; refine runRaw_step st3 ?_; rfl
  dsimp only [mkSt] at hrun3 ⊢
  rw [hrun3]; exact ⟨rfl, rfl⟩

end StackCanaryLiftV2
