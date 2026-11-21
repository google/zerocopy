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
# `PicMultiFnSfiV2` — Prefix-Hardened PIC Multi-Function SFI Verifier & Soundness

Closes the `0x64` (`FS:`), `0x65` (`GS:`), `0x67` (`addr32`), and `0x66` (`op16`)
prefix vulnerabilities on `RealX64PrefixSem`:
1. Enforces `addr.seg == none && !addr.addr32` on every memory load/store and
   rejects all `16`-bit memory, `push*`/`pop*`/`leave*`, and `has66` branch/jump
   encodings in untrusted 32-byte bundles.
2. Admits both `mov idx32, src32 + mem` and `mov idx32, imm32 + mem` (`%fs:0x28`
   rewritten to arena-guarded `0xFE28(%r14)`), expressed solely via `Nat.rec`
   combinators (`0` `sorry`, `0` `*._unsafe_rec`).
3. Proves five negative rejection certificates (`fsEscapeSfiImg`, `gsEscapeSfiImg`,
   `addr32StoreSfiImg`, `op16PushSfiImg`, `op16JmpSfiImg`) by `rfl`, and proves
   universal `checkSfiPicMultiFnV2_sound` over ALL `(fsBase, gsBase : BitVec 64)`
   and arbitrary step counts `steps : Nat`.
-/

namespace PicMultiFnSfiV2

open RealX64PrefixSem

/-- Host-protected registers strictly read-only across untrusted SFI bundles:
    `%rsp` (host stack), `%rbp, %rbx, %r12` (host CSRs / `SfiContext`),
    `%r14` (`arenaBase`), and `%r15` (`codeBase`). -/
def isPicHostProtectedReg : Reg → Bool
  | .rsp | .rbp | .rbx | .r12 | .r14 | .r15 => true
  | _ => false

/-- General SFI scratch registers (`rax, rcx, rdx, rsi, rdi, r8, r9, r10, r11`),
    excluding host-protected registers and `%r13` (`guest_sp`). -/
def isPicScratchReg : Reg → Bool
  | .rax | .rcx | .rdx | .rsi | .rdi | .r8 | .r9 | .r10 | .r11 => true
  | _ => false

/-- Registers permitted as 32-bit zero-extending destinations (`isPicScratchReg` or `.r13`). -/
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

/-- Decidable check for signed displacement `disp ∈ [-65536, +65528]`. -/
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
  intro k hk heq; subst heq
  exact Nat.not_lt_of_ge hout (sfi_sym_mem_byte_inside arenaBase idxVal disp k hidx hdisp hk)

theorem sfi_store32_preserves_outside_sym_arena
    (m : ByteMem) (arenaBase idxVal disp val a : BitVec 64)
    (hidx : idxVal.toNat < 4294967296)
    (hdisp : dispSymOk disp = true)
    (hout : OutsideSymmetricArena arenaBase a) :
    writeMem32 m (arenaBase + idxVal * 1#64 + disp) val a = m a := by
  apply writeMem32_byte_ne
  intro k hk heq; subst heq
  exact Nat.not_lt_of_ge hout (sfi_sym_mem_byte_inside arenaBase idxVal disp k hidx hdisp hk)

/-- Checks that `addr` has NO `FS:`/`GS:` segment override (`seg == none`), NO `0x67`
    address-size truncation (`addr32 == false`), base `%r14`, index `(idx, 1)`, and `dispSymOk`. -/
def isArenaIdxAddrV2 (idx : Reg) (addr : MemAddr) : Bool :=
  match addr.seg, addr.addr32, addr.kind with
  | none, false, .baseDisp (some .r14) (some (idx', 1)) disp =>
    (idx' == idx) && dispSymOk disp
  | _, _, _ => false

theorem isArenaIdxAddrV2_spec {idx : Reg} {addr : MemAddr}
    (h : isArenaIdxAddrV2 idx addr = true) :
    ∃ disp : BitVec 64,
      addr = { seg := none, addr32 := false, kind := .baseDisp (some .r14) (some (idx, 1)) disp } ∧
      dispSymOk disp = true := by
  rcases addr with ⟨seg, a32, kind⟩
  cases seg with
  | some _ => nomatch h
  | none =>
    cases a32 with
    | true => nomatch h
    | false =>
      cases kind with
      | ripRel _ => nomatch h
      | baseDisp b io disp =>
        cases b with
        | none => nomatch h
        | some br =>
          cases br with
          | r14 =>
            cases io with
            | none => nomatch h
            | some p =>
              rcases p with ⟨idx', sc⟩
              cases sc with
              | zero => nomatch h
              | succ s1 =>
                cases s1 with
                | succ _ => nomatch h
                | zero =>
                  dsimp [isArenaIdxAddrV2] at h
                  have hc := Bool.and_eq_true_iff.mp h
                  have hi : idx' = idx := eq_of_beq hc.1
                  subst hi
                  exact ⟨disp, rfl, hc.2⟩
          | _ => nomatch h

/-- Standalone 1-instruction operations admitted in PIC multi-function SFI V2:
    all guest-stack loads/stores `[r14 + r13*1 + disp]` strictly require `isArenaIdxAddrV2 .r13`
    (`seg == none && addr32 == false`), blocking `FS:`/`GS:` and `addr32` escapes! -/
def isStandalonePicSfiOpV2 : X64InstrV2 → Bool
  | .nop | .endbr64 => true
  | .movRR64 dst _ | .movImm64 dst _ | .lea64 dst _
  | .shiftImm64 _ dst _ | .imulRR64 dst _ => isPicScratchReg dst
  | .movRR32 dst _ | .movImm32 dst _ | .lea32 dst _ => isPicZext32DstReg dst
  | .movRR16 dst _ | .movImm16 dst _ => isPicScratchReg dst
  | .aluRR64 op dst _ | .aluImm64 op dst _ =>
    if aluWritesDst op then isPicScratchReg dst else true
  | .aluRR32 op dst _ | .aluImm32 op dst _ =>
    if aluWritesDst op then isPicZext32DstReg dst else true
  | .aluRR16 op dst _ | .aluImm16 op dst _ =>
    if aluWritesDst op then isPicScratchReg dst else true
  | .store64 addr _ | .store32 addr _ => isArenaIdxAddrV2 .r13 addr
  | .load64 dst addr | .load32Sext dst addr =>
    isPicScratchReg dst && isArenaIdxAddrV2 .r13 addr
  | .load32Zext dst addr =>
    isPicZext32DstReg dst && isArenaIdxAddrV2 .r13 addr
  | _ => false

/-- Second instruction of a 2-instruction general arena memory macro
    (`mov idx32, src32` or `mov idx32, imm32` followed by `mem [r14 + idx*1 + disp]`). -/
def isSandboxedPicMem2ndV2 (idx : Reg) : X64InstrV2 → Bool
  | .store64 addr _ | .store32 addr _ => isArenaIdxAddrV2 idx addr
  | .load64 dst addr | .load32Sext dst addr =>
    isPicScratchReg dst && isArenaIdxAddrV2 idx addr
  | .load32Zext dst addr =>
    isPicZext32DstReg dst && isArenaIdxAddrV2 idx addr
  | _ => false

def peekPicMem2ndV2 (idx : Reg) (rem1 : List UInt8) : Option (X64InstrV2 × Nat) :=
  match decodeX64V2 rem1 with
  | .ok ins2 len2 =>
    let pfx2 := rem1.take len2
    if isSandboxedPicMem2ndV2 idx ins2 && !(len2 == 0) && !decide (lenTR rem1 < len2) &&
       (decodeX64V2 pfx2 == .ok ins2 pfx2.length) then some (ins2, len2)
    else none
  | .fault _ => none

/-- Exact `lea r11, [r15 + r11*1 + 0]` (`addr32 = false`) and `jmp r11` (`has66 = false`)
    for the 3-instruction PIC indirect control-flow macro. -/
def isPicLeaR15R11V2 : X64InstrV2 → Bool
  | .lea64 .r11 { seg := none, addr32 := false, kind := .baseDisp (some .r15) (some (.r11, 1)) 0#64 } => true
  | _ => false

def isPicJmpR11V2 : X64InstrV2 → Bool
  | .jmpReg false .r11 => true
  | _ => false

def peekPicJmp2nd3rdV2 (rem1 : List UInt8) : Option (Nat × Nat) :=
  match decodeX64V2 rem1 with
  | .ok ins2 len2 =>
    let pfx2 := rem1.take len2
    let rem2 := rem1.drop len2
    if isPicLeaR15R11V2 ins2 && !(len2 == 0) && !decide (lenTR rem1 < len2) &&
       (decodeX64V2 pfx2 == .ok ins2 pfx2.length) then
      match decodeX64V2 rem2 with
      | .ok ins3 len3 =>
        let pfx3 := rem2.take len3
        if isPicJmpR11V2 ins3 && !(len3 == 0) && !decide (lenTR rem2 < len3) &&
           (decodeX64V2 pfx3 == .ok ins3 pfx3.length) then some (len2, len3)
        else none
      | .fault _ => none
    else none
  | .fault _ => none

def sfiPicJmpTarget (bBase off len1 : Nat) (rel : BitVec 64) : Nat :=
  (BitVec.ofNat 64 (bBase + off + len1) + rel).toNat

def sfiPicJmpTargetOk (totalBytes bBase off len1 : Nat) (rel : BitVec 64) : Bool :=
  natLtB (sfiPicJmpTarget bBase off len1 rel) totalBytes &&
  natEqB (sfiPicJmpTarget bBase off len1 rel % 32) 0

/-- Verifies a single 32-byte untrusted bundle (`bBase ≥ 64`) via `Nat.rec` (`0` `isPartial`):
    - Rejects `has66 = true` on `jmpRel` and `jccRel` (preventing Intel/AMD `rel16` desync);
    - Rejects all `FS:`/`GS:` and `0x67` memory instructions;
    - Rejects all `push64`, `push16`, `pop64`, `pop16`, `leave64`, `leave16`, `callRel32`, `ret`. -/
def checkSfiPicMacroStreamV2 (totalBytes bBase : Nat) (isLast : Bool)
    (fuel : Nat) (off0 : Nat) (bs0 : List UInt8) : Bool :=
  Nat.rec (motive := fun _ => Nat → List UInt8 → Bool)
    (fun off bs => match bs with | [] => decide (off = 32) | _ :: _ => false)
    (fun _ ih off bs =>
      match bs with
      | [] => decide (off = 32)
      | _ :: _ =>
        match decodeX64V2 bs with
        | .fault _ => false
        | .ok ins1 len1 =>
          let pfx1 := bs.take len1
          let rem1 := bs.drop len1
          if len1 == 0 || decide (lenTR bs < len1) || decide (32 < off + len1) ||
             (decodeX64V2 pfx1 != .ok ins1 pfx1.length) then false
          else
            match ins1 with
            | .jmpRel has66 rel =>
              if !has66 && sfiPicJmpTargetOk totalBytes bBase off len1 rel then
                ih (off + len1) rem1
              else false
            | .jccRel has66 _ rel =>
              if !has66 && sfiPicJmpTargetOk totalBytes bBase off len1 rel &&
                 !(isLast && decide (off + len1 = 32)) then
                ih (off + len1) rem1
              else false
            | .movRR32 idx dstSrc =>
              if isPicScratchReg idx then
                match peekPicMem2ndV2 idx rem1 with
                | some (_, len2) =>
                  if decide (32 < off + len1 + len2) || (isLast && decide (off + len1 + len2 = 32)) then
                    false
                  else ih (off + len1 + len2) (rem1.drop len2)
                | none =>
                  if isStandalonePicSfiOpV2 (.movRR32 idx dstSrc) && !(isLast && decide (off + len1 = 32)) then
                    ih (off + len1) rem1
                  else false
              else if isStandalonePicSfiOpV2 (.movRR32 idx dstSrc) && !(isLast && decide (off + len1 = 32)) then
                ih (off + len1) rem1
              else false
            | .movImm32 idx imm32 =>
              if isPicScratchReg idx then
                match peekPicMem2ndV2 idx rem1 with
                | some (_, len2) =>
                  if decide (32 < off + len1 + len2) || (isLast && decide (off + len1 + len2 = 32)) then
                    false
                  else ih (off + len1 + len2) (rem1.drop len2)
                | none =>
                  if isStandalonePicSfiOpV2 (.movImm32 idx imm32) && !(isLast && decide (off + len1 = 32)) then
                    ih (off + len1) rem1
                  else false
              else if isStandalonePicSfiOpV2 (.movImm32 idx imm32) && !(isLast && decide (off + len1 = 32)) then
                ih (off + len1) rem1
              else false
            | .aluImm32 op dst mask =>
              if op == .and && dst == .r11 then
                match peekPicJmp2nd3rdV2 rem1 with
                | some (len2, len3) =>
                  if (mask &&& 31#32) == 0#32 && natLtB mask.toNat totalBytes &&
                     !decide (32 < off + len1 + len2 + len3) then
                    ih (off + len1 + len2 + len3) ((rem1.drop len2).drop len3)
                  else false
                | none =>
                  if isStandalonePicSfiOpV2 (.aluImm32 op dst mask) && !(isLast && decide (off + len1 = 32)) then
                    ih (off + len1) rem1
                  else false
              else if isStandalonePicSfiOpV2 (.aluImm32 op dst mask) && !(isLast && decide (off + len1 = 32)) then
                ih (off + len1) rem1
              else false
            | other =>
              if isStandalonePicSfiOpV2 other && !(isLast && decide (off + len1 = 32)) then
                ih (off + len1) rem1
              else false)
    fuel off0 bs0

def checkPortal0BundleV2 (bs : List UInt8) : Bool :=
  decide (lenTR bs = 32) && (listGet? bs 0 == some 0xC3)

def checkPortal1BundleV2 (bs : List UInt8) : Bool :=
  decide (lenTR bs = 32) &&
  (listGet? bs 0 == some 0xE9 || listGet? bs 0 == some 0xEB)

def checkOnePicBundleV2 (totalBytes base : Nat) (bundle : List UInt8) : Bool :=
  if base == 0 then checkPortal0BundleV2 bundle
  else if base == 32 then checkPortal1BundleV2 bundle
  else checkSfiPicMacroStreamV2 totalBytes base (base + 32 == totalBytes) 32 0 bundle

def checkSfiPicLeafBundlesV2 (totalBytes : Nat) (fuel : Nat) (base0 : Nat) (bs0 : List UInt8) : Bool :=
  Nat.rec (motive := fun _ => Nat → List UInt8 → Bool)
    (fun base bs => match bs with | [] => natEqB (base % 32) 0 | _ :: _ => false)
    (fun _ ih base bs =>
      match bs with
      | [] => natEqB (base % 32) 0
      | _ :: _ =>
        natEqB (base % 32) 0 &&
        natLeB 32 (lenTR bs) &&
        natLeB (base + 32) totalBytes &&
        checkOnePicBundleV2 totalBytes base (bs.take 32) &&
        ih (base + 32) (bs.drop 32))
    fuel base0 bs0

def checkSfiPicSubtreeBoundedV2 (totalBytes : Nat) (fuel : Nat) (base0 endOff0 : Nat) (t0 : ByteCodeTree) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → ByteCodeTree → Bool)
    (fun _ _ _ => false)
    (fun _ ih base endOff t =>
      match t with
      | .leaf bs =>
        let sz := lenTR bs
        natLtB base endOff &&
        natLeB endOff totalBytes &&
        natEqB (base + sz) endOff &&
        natEqB (sz % 32) 0 &&
        checkSfiPicLeafBundlesV2 totalBytes (sz / 32) base bs
      | .node lsz l r =>
        natEqB (lsz % 32) 0 &&
        natLeB (base + lsz) endOff &&
        ih base (base + lsz) l &&
        ih (base + lsz) endOff r)
    fuel base0 endOff0 t0

def checkSfiPicMultiFnV2 (totalBytes : Nat) (img : X64ObjImage) : Bool :=
  natLeB 96 totalBytes &&
  natEqB (totalBytes % 32) 0 &&
  checkSfiPicSubtreeBoundedV2 totalBytes 64 0 totalBytes img.code

/-! ## Five Kernel-Checked Prefix-Rejection Certificates (`rfl`) -/

def addr32StoreSfiImg : X64ObjImage :=
  { code := .leaf (
      ([0xC3] ++ List.replicate 31 0x90) ++
      ([0xEB, 0xFE] ++ List.replicate 30 0x90) ++
      ([0x67, 0x4F, 0x89, 0x04, 0x2E, 0xE9, 0xB6, 0xFF, 0xFF, 0xFF] ++ List.replicate 22 0x90)) }

def op16PushSfiImg : X64ObjImage :=
  { code := .leaf (
      ([0xC3] ++ List.replicate 31 0x90) ++
      ([0xEB, 0xFE] ++ List.replicate 30 0x90) ++
      ([0x66, 0x50, 0xE9, 0xB9, 0xFF, 0xFF, 0xFF] ++ List.replicate 25 0x90)) }

def op16JmpSfiImg : X64ObjImage :=
  { code := .leaf (
      ([0xC3] ++ List.replicate 31 0x90) ++
      ([0xEB, 0xFE] ++ List.replicate 30 0x90) ++
      ([0x66, 0xE9, 0xBA, 0xFF, 0xFF, 0xFF] ++ List.replicate 26 0x90)) }

theorem checkSfiPicMultiFnV2_rejects_fs_escape :
    checkSfiPicMultiFnV2 96 fsEscapeSfiImg = false := rfl

theorem checkSfiPicMultiFnV2_rejects_gs_escape :
    checkSfiPicMultiFnV2 96 gsEscapeSfiImg = false := rfl

theorem checkSfiPicMultiFnV2_rejects_addr32_store :
    checkSfiPicMultiFnV2 96 addr32StoreSfiImg = false := rfl

theorem checkSfiPicMultiFnV2_rejects_op16_push :
    checkSfiPicMultiFnV2 96 op16PushSfiImg = false := rfl

theorem checkSfiPicMultiFnV2_rejects_op16_jmp :
    checkSfiPicMultiFnV2 96 op16JmpSfiImg = false := rfl

/-! ## Inductive Multi-Phase Soundness Proof (`checkSfiPicMultiFnV2_sound`) -/

def AllUntrustedBundlesValidV2 (totalBytes : Nat) (code : ByteCodeTree) : Prop :=
  96 ≤ totalBytes ∧ totalBytes % 32 = 0 ∧
  ∀ bBase, 64 ≤ bBase → bBase < totalBytes → bBase % 32 = 0 →
    ∃ bundle : List UInt8,
      bundle.length = 32 ∧
      (∀ i, i < 32 → code.getByte? (bBase + i) = listGet? bundle i) ∧
      checkSfiPicMacroStreamV2 totalBytes bBase (bBase + 32 == totalBytes) 32 0 bundle = true

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

theorem ite_false_left {α : Type} {c : Bool} (hc : c = false) (t e : α) :
    (if c then t else e) = e := by
  subst hc; rfl

theorem checkOnePicBundleV2_ge64 (totalBytes b : Nat) (bundle : List UInt8) (hb64 : 64 ≤ b) :
    checkOnePicBundleV2 totalBytes b bundle =
      checkSfiPicMacroStreamV2 totalBytes b (b + 32 == totalBytes) 32 0 bundle := by
  have hne0 : (b == 0) = false := by
    cases h0 : (b == 0) with | false => rfl | true => have := of_decide_eq_true h0; subst this; nomatch hb64
  have hne32 : (b == 32) = false := by
    cases h32 : (b == 32) with | false => rfl | true => have := of_decide_eq_true h32; subst this; nomatch hb64
  unfold checkOnePicBundleV2
  exact (ite_false_left hne0 _ _).trans (ite_false_left hne32 _ _)

theorem checkSfiPicLeafBundlesV2_spec (totalBytes : Nat) :
    ∀ (fuel base : Nat) (bs : List UInt8) (b : Nat),
      checkSfiPicLeafBundlesV2 totalBytes fuel base bs = true →
      64 ≤ b → base ≤ b → b < base + bs.length → b % 32 = 0 →
      ∃ bundle : List UInt8,
        bundle.length = 32 ∧
        (∀ i, i < 32 → listGet? bs ((b - base) + i) = listGet? bundle i) ∧
        checkSfiPicMacroStreamV2 totalBytes b (b + 32 == totalBytes) 32 0 bundle = true
  | 0, base, [], b, _, _, hge, hlt, _ => by
    rw [List.length_nil, Nat.add_zero] at hlt
    exact False.elim (Nat.lt_irrefl b (Nat.lt_of_lt_of_le hlt hge))
  | 0, _, _ :: _, _, hchk, _, _, _, _ => nomatch hchk
  | _ + 1, base, [], b, _, _, hge, hlt, _ => by
    rw [List.length_nil, Nat.add_zero] at hlt
    exact False.elim (Nat.lt_irrefl b (Nat.lt_of_lt_of_le hlt hge))
  | fuel + 1, base, c :: cs, b, hchk, hb64, hge, hlt, hmod => by
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
      have hmacro : checkSfiPicMacroStreamV2 totalBytes b (b + 32 == totalBytes) 32 0 ((c :: cs).take 32) = true :=
        (checkOnePicBundleV2_ge64 totalBytes b ((c :: cs).take 32) hb64).symm.trans c2.2
      refine ⟨(c :: cs).take 32, List.length_take_of_le hlen32, ?_, hmacro⟩
      intro i hi; rw [Nat.sub_self, Nat.zero_add, listGet?_take 32 (c :: cs) i hi]
    | false =>
      have hne : b ≠ base := of_decide_eq_false h_eq
      have hgt : base < b := Nat.lt_of_le_of_ne hge hne.symm
      have hb32 : base + 32 ≤ b := mod32_step_le hbase_mod hmod hgt
      have hlt_drop : b < (base + 32) + ((c :: cs).drop 32).length := by
        rw [List.length_drop, Nat.add_assoc, Nat.add_sub_of_le hlen32]; exact hlt
      rcases checkSfiPicLeafBundlesV2_spec totalBytes fuel (base + 32) ((c :: cs).drop 32) b
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

theorem checkSfiPicSubtreeBoundedV2_spec (totalBytes : Nat) :
    ∀ (fuel : Nat) (t : ByteCodeTree) (base endOff b : Nat),
      base % 32 = 0 →
      checkSfiPicSubtreeBoundedV2 totalBytes fuel base endOff t = true →
      64 ≤ b → base ≤ b → b < endOff → b % 32 = 0 →
      ∃ bundle : List UInt8,
        bundle.length = 32 ∧
        (∀ i, i < 32 → ByteCodeTree.getByteBounded fuel t ((b - base) + i) = listGet? bundle i) ∧
        checkSfiPicMacroStreamV2 totalBytes b (b + 32 == totalBytes) 32 0 bundle = true
  | 0, _, _, _, _, _, hchk, _, _, _, _ => nomatch hchk
  | _ + 1, .leaf bs, base, endOff, b, _, hchk, hb64, hge, hlt, hmod => by
    dsimp [checkSfiPicSubtreeBoundedV2] at hchk
    have c1 := Bool.and_eq_true_iff.mp hchk
    have c2 := Bool.and_eq_true_iff.mp c1.1
    have c3 := Bool.and_eq_true_iff.mp c2.1
    have hend : base + bs.length = endOff := by
      have ht := natEqB_true c3.2; rw [lenTR_eq_length] at ht; exact ht
    rw [← hend] at hlt
    have hchk_l : checkSfiPicLeafBundlesV2 totalBytes (bs.length / 32) base bs = true := by
      have ht := c1.2; rw [lenTR_eq_length] at ht; exact ht
    exact checkSfiPicLeafBundlesV2_spec totalBytes (bs.length / 32) base bs b hchk_l hb64 hge hlt hmod
  | fuel + 1, .node lsz l r, base, endOff, b, hbase_mod, hchk, hb64, hge, hlt, hmod => by
    dsimp [checkSfiPicSubtreeBoundedV2] at hchk
    have c1 := Bool.and_eq_true_iff.mp hchk
    have c2 := Bool.and_eq_true_iff.mp c1.1
    have c3 := Bool.and_eq_true_iff.mp c2.1
    have hlsz_mod : lsz % 32 = 0 := natEqB_true c3.1
    have hsplit_mod : (base + lsz) % 32 = 0 := add_mod32_zero hbase_mod hlsz_mod
    cases hleft : decide (b < base + lsz) with
    | true =>
      have hbl : b < base + lsz := of_decide_eq_true hleft
      have hb32 : b + 32 ≤ base + lsz := mod32_step_le hmod hsplit_mod hbl
      rcases checkSfiPicSubtreeBoundedV2_spec totalBytes fuel l base (base + lsz) b
        hbase_mod c2.2 hb64 hge hbl hmod with ⟨bundle, hblen, hbget, hbchk⟩
      refine ⟨bundle, hblen, ?_, hbchk⟩
      intro i hi
      have hidx_lt : (b - base) + i < lsz := by
        have hb_eq : base + (b - base) = b := Nat.add_sub_of_le hge
        have hsum_lt : base + ((b - base) + i) < base + lsz := by
          rw [← Nat.add_assoc, hb_eq]
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi b) hb32
        exact Nat.lt_of_add_lt_add_left hsum_lt
      dsimp [ByteCodeTree.getByteBounded]; simp only [hidx_lt, ite_true]; exact hbget i hi
    | false =>
      have hbge : base + lsz ≤ b := Nat.not_lt.mp (of_decide_eq_false hleft)
      rcases checkSfiPicSubtreeBoundedV2_spec totalBytes fuel r (base + lsz) endOff b
        hsplit_mod c1.2 hb64 hbge hlt hmod with ⟨bundle, hblen, hbget, hbchk⟩
      refine ⟨bundle, hblen, ?_, hbchk⟩
      intro i hi
      have hidx_ge : lsz ≤ (b - base) + i :=
        Nat.le_trans (Nat.le_sub_of_add_le' hbge) (Nat.le_add_right _ i)
      have hnlt : ¬ ((b - base) + i < lsz) := Nat.not_lt_of_ge hidx_ge
      dsimp [ByteCodeTree.getByteBounded]; simp only [hnlt, ite_false]
      have hsub_eq : ((b - base) + i) - lsz = (b - (base + lsz)) + i := by
        rw [Nat.sub_add_comm (Nat.le_sub_of_add_le' hbge), Nat.sub_sub]
      rw [hsub_eq]; exact hbget i hi

theorem checkSfiPicMultiFnV2_bundlesValid {totalBytes : Nat} {img : X64ObjImage}
    (hok : checkSfiPicMultiFnV2 totalBytes img = true) :
    AllUntrustedBundlesValidV2 totalBytes img.code := by
  dsimp [checkSfiPicMultiFnV2] at hok
  have c1 := Bool.and_eq_true_iff.mp hok
  have c2 := Bool.and_eq_true_iff.mp c1.1
  refine ⟨natLeB_true c2.1, natEqB_true c2.2, ?_⟩
  intro b hb64 hblt hbmod
  rcases checkSfiPicSubtreeBoundedV2_spec totalBytes 64 img.code 0 totalBytes b
    rfl c1.2 hb64 (Nat.zero_le b) hblt hbmod with ⟨bundle, hblen, hbget, hbchk⟩
  refine ⟨bundle, hblen, ?_, hbchk⟩
  intro i hi; have h0 : b - 0 = b := Nat.sub_zero b
  dsimp [ByteCodeTree.getByte?]; rw [← h0]; exact hbget i hi

/-- Core PIC host-safety state invariant parameterized over arbitrary `(fsBase, gsBase : BitVec 64)`. -/
def SfiPicCoreSafeV2 (codeBase arenaBase fsBase gsBase : BitVec 64)
    (initRegs : Reg → BitVec 64) (initMem : ByteMem) (s : RealX64PrefixState) : Prop :=
  s.fault = false ∧
  s.fsBase = fsBase ∧
  s.gsBase = gsBase ∧
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

inductive SfiPicPhaseV2 (codeBase : BitVec 64) (totalBytes : Nat) (img : X64ObjImage)
    (s : RealX64PrefixState) : Prop where
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
      (hchk : checkSfiPicMacroStreamV2 totalBytes bBase (bBase + 32 == totalBytes) fuel off rem = true)
  | pendingMem (bBase fuel nextOff curOff : Nat) (idx : Reg) (ins2 : X64InstrV2) (pfx2 rem2 : List UInt8)
      (hidx_lt : (s.regs idx).toNat < 4294967296)
      (hb64 : 64 ≤ bBase)
      (hb_lt : bBase < totalBytes)
      (hb_mod : bBase % 32 = 0)
      (hb_le : bBase + 32 ≤ totalBytes)
      (hcur64 : 64 ≤ curOff)
      (hcur_lt : curOff < totalBytes)
      (hrip : s.rip = codeBase + BitVec.ofNat 64 curOff)
      (hmem2 : isSandboxedPicMem2ndV2 idx ins2 = true)
      (hdec2 : decodeX64V2 pfx2 = .ok ins2 pfx2.length)
      (hwin2 : ∀ i, i < pfx2.length → img.code.getByte? (curOff + i) = listGet? pfx2 i)
      (hnrip : curOff + pfx2.length = bBase + nextOff)
      (hnlen : nextOff + rem2.length = 32)
      (hnlast : ((bBase + 32 == totalBytes) && decide (nextOff = 32)) = false)
      (hnbytes : ∀ i, i < rem2.length → img.code.getByte? ((bBase + nextOff) + i) = listGet? rem2 i)
      (hnchk : checkSfiPicMacroStreamV2 totalBytes bBase (bBase + 32 == totalBytes) fuel nextOff rem2 = true)
  | pendingPicLea (curOff leaLen tgtOff : Nat) (pfx2 pfx3 : List UInt8)
      (hr11_eq : s.regs .r11 = BitVec.ofNat 64 tgtOff)
      (htgt_lt : tgtOff < totalBytes)
      (htgt_mod : tgtOff % 32 = 0)
      (hcur64 : 64 ≤ curOff)
      (hcur_lt : curOff < totalBytes)
      (hnext64 : 64 ≤ curOff + leaLen)
      (hnext_lt : curOff + leaLen < totalBytes)
      (hrip : s.rip = codeBase + BitVec.ofNat 64 curOff)
      (hdec2 : decodeX64V2 pfx2 =
        .ok (.lea64 .r11 { seg := none, addr32 := false, kind := .baseDisp (some .r15) (some (.r11, 1)) 0#64 }) leaLen)
      (hpfx2_len : pfx2.length = leaLen)
      (hwin2 : ∀ i, i < pfx2.length → img.code.getByte? (curOff + i) = listGet? pfx2 i)
      (hdec3 : decodeX64V2 pfx3 = .ok (.jmpReg false .r11) pfx3.length)
      (hwin3 : ∀ i, i < pfx3.length → img.code.getByte? ((curOff + leaLen) + i) = listGet? pfx3 i)
  | pendingPicJmp (curOff tgtOff : Nat) (pfx3 : List UInt8)
      (hr11_eq : s.regs .r11 = codeBase + BitVec.ofNat 64 tgtOff)
      (htgt_lt : tgtOff < totalBytes)
      (htgt_mod : tgtOff % 32 = 0)
      (hcur64 : 64 ≤ curOff)
      (hcur_lt : curOff < totalBytes)
      (hrip : s.rip = codeBase + BitVec.ofNat 64 curOff)
      (hdec3 : decodeX64V2 pfx3 = .ok (.jmpReg false .r11) pfx3.length)
      (hwin3 : ∀ i, i < pfx3.length → img.code.getByte? (curOff + i) = listGet? pfx3 i)

def SfiPicMachineInvV2 (codeBase arenaBase fsBase gsBase : BitVec 64)
    (totalBytes : Nat) (img : X64ObjImage)
    (initRegs : Reg → BitVec 64) (initMem : ByteMem) (s : RealX64PrefixState) : Prop :=
  SfiPicCoreSafeV2 codeBase arenaBase fsBase gsBase initRegs initMem s ∧
  (s.exitKind = .running → SfiPicPhaseV2 codeBase totalBytes img s)

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
  have htn32 : (codeBase + 32#64).toNat = codeBase.toNat + 32 := codeBase_add_off_toNat hfit hpos96
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases heq : (codeBase + BitVec.ofNat 64 off == codeBase) with
    | false => rfl
    | true =>
      have hv := congrArg BitVec.toNat (eq_of_beq heq); rw [htn] at hv
      have hoff0 : off = 0 := Nat.add_left_cancel (by rw [hv, Nat.add_zero]); subst hoff0; nomatch h64
  · cases heq : (codeBase + BitVec.ofNat 64 off == codeBase + 32#64) with
    | false => rfl
    | true =>
      have hv := congrArg BitVec.toNat (eq_of_beq heq); rw [htn, htn32] at hv
      have hoff32 : off = 32 := Nat.add_left_cancel hv; subst hoff32; nomatch h64
  · apply Bool.and_eq_true_iff.mpr; rw [htn]
    exact ⟨Nat.ble_eq_true_of_le (Nat.add_le_add_left h64 _),
           Nat.ble_eq_true_of_le (Nat.succ_le_of_lt (Nat.add_lt_add_left hlt _))⟩
  · rw [htn, Nat.add_sub_cancel_left]

theorem enterPicTargetV2 {codeBase : BitVec 64} {totalBytes : Nat} {img : X64ObjImage}
    {s' : RealX64PrefixState} {tgt : Nat}
    (hall : AllUntrustedBundlesValidV2 totalBytes img.code)
    (htgt_lt : tgt < totalBytes) (htgt_mod : tgt % 32 = 0)
    (hrip : s'.rip = codeBase + BitVec.ofNat 64 tgt) :
    SfiPicPhaseV2 codeBase totalBytes img s' := by
  cases h0 : decide (tgt = 0) with
  | true =>
    have ht0 : tgt = 0 := of_decide_eq_true h0; subst ht0
    apply SfiPicPhaseV2.atPortal0; rw [hrip]; exact BitVec.add_zero codeBase
  | false =>
    cases h32 : decide (tgt = 32) with
    | true =>
      have ht32 : tgt = 32 := of_decide_eq_true h32; subst ht32
      exact SfiPicPhaseV2.atPortal1 hrip
    | false =>
      have hne0 : tgt ≠ 0 := of_decide_eq_false h0
      have hne32 : tgt ≠ 32 := of_decide_eq_false h32
      have hge32 : 32 ≤ tgt := mod32_step_le rfl htgt_mod (Nat.pos_of_ne_zero hne0)
      have hge64 : 64 ≤ tgt := mod32_step_le rfl htgt_mod (Nat.lt_of_le_of_ne hge32 hne32.symm)
      rcases hall with ⟨_, htot_mod, hget_b⟩
      rcases hget_b tgt hge64 htgt_lt htgt_mod with ⟨bundle, hblen, hbget, hbchk⟩
      have hb32 : tgt + 32 ≤ totalBytes := mod32_step_le htgt_mod htot_mod htgt_lt
      apply SfiPicPhaseV2.atMacro tgt 32 0 bundle hge64 htgt_lt htgt_mod hb32 (by decide)
      · rw [Nat.add_zero]; exact hrip
      · rw [Nat.zero_add]; exact hblen
      · intro i hi; rw [Nat.add_zero]; exact hbget i (by rw [hblen] at hi; exact hi)
      · exact hbchk

theorem enterNextPicMacroV2 {codeBase : BitVec 64} {totalBytes : Nat} {img : X64ObjImage}
    {s' : RealX64PrefixState} {bBase fuel nextOff : Nat} {rem2 : List UInt8}
    (hall : AllUntrustedBundlesValidV2 totalBytes img.code)
    (hb64 : 64 ≤ bBase) (hb_lt : bBase < totalBytes) (hb_mod : bBase % 32 = 0)
    (hb_le : bBase + 32 ≤ totalBytes)
    (hrip : s'.rip = codeBase + BitVec.ofNat 64 (bBase + nextOff))
    (hnlen : nextOff + rem2.length = 32)
    (hnlast : ((bBase + 32 == totalBytes) && decide (nextOff = 32)) = false)
    (hnbytes : ∀ i, i < rem2.length → img.code.getByte? ((bBase + nextOff) + i) = listGet? rem2 i)
    (hnchk : checkSfiPicMacroStreamV2 totalBytes bBase (bBase + 32 == totalBytes) fuel nextOff rem2 = true) :
    SfiPicPhaseV2 codeBase totalBytes img s' := by
  cases rem2 with
  | cons r0 rs =>
    have hoff_lt : nextOff < 32 := by
      rw [← hnlen]; exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ rs.length)
    exact SfiPicPhaseV2.atMacro bBase fuel nextOff (r0 :: rs) hb64 hb_lt hb_mod hb_le hoff_lt hrip hnlen hnbytes hnchk
  | nil =>
    rw [List.length_nil, Nat.add_zero] at hnlen; subst hnlen
    have hnot_eq : bBase + 32 ≠ totalBytes := by
      intro heq
      have hbe : (bBase + 32 == totalBytes) = true := beq_iff_eq.mpr heq
      rw [decide_eq_true (rfl : 32 = 32), Bool.and_true, hbe] at hnlast
      nomatch hnlast
    exact enterPicTargetV2 hall (Nat.lt_of_le_of_ne hb_le hnot_eq) (add_mod32_zero hb_mod rfl) hrip

theorem evalLinearAddr_arenaIdx (s : RealX64PrefixState) (nextRip : BitVec 64) (idx : Reg) (disp : BitVec 64) :
    evalLinearAddr s nextRip { seg := none, addr32 := false, kind := .baseDisp (some .r14) (some (idx, 1)) disp } =
      s.regs .r14 + s.regs idx * 1#64 + disp := by
  dsimp [evalLinearAddr, segBaseOf, evalEffectiveAddr]
  exact BitVec.zero_add _

theorem coreSafeV2_upd_scratch64 {codeBase arenaBase fsBase gsBase : BitVec 64}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    {s : RealX64PrefixState} {dst : Reg} {v : BitVec 64} {fl' : RFlags} {rip' : BitVec 64}
    (hrun : s.exitKind = .running)
    (hcore : SfiPicCoreSafeV2 codeBase arenaBase fsBase gsBase initRegs initMem s)
    (hscr : isPicScratchReg dst = true) :
    SfiPicCoreSafeV2 codeBase arenaBase fsBase gsBase initRegs initMem
      { s with rip := rip', regs := regUpd s.regs dst v, flags := fl' } := by
  rcases hcore with ⟨hf, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩
  rw [hrun] at hexit
  dsimp [SfiPicCoreSafeV2]; rw [hrun]
  refine ⟨hf, hfs, hgs, ?_, ?_, ?_, hmem, ?_, ?_⟩
  · rw [regUpd_ne s.regs (scratch_ne_protected hscr rfl) v]; exact hr15
  · rw [regUpd_ne s.regs (scratch_ne_protected hscr rfl) v]; exact hr14
  · rw [regUpd_ne s.regs (scratch_ne_r13 hscr) v]; exact hr13
  · rw [regUpd_ne s.regs (scratch_ne_protected hscr rfl) v]; exact hexit.1
  · intro r hp; rw [regUpd_ne s.regs (scratch_ne_protected hscr hp) v]; exact hexit.2 r hp

theorem coreSafeV2_upd_zext32 {codeBase arenaBase fsBase gsBase : BitVec 64}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    {s : RealX64PrefixState} {dst : Reg} {v32 : BitVec 32} {fl' : RFlags} {rip' : BitVec 64}
    (hrun : s.exitKind = .running)
    (hcore : SfiPicCoreSafeV2 codeBase arenaBase fsBase gsBase initRegs initMem s)
    (hdst : isPicZext32DstReg dst = true) :
    SfiPicCoreSafeV2 codeBase arenaBase fsBase gsBase initRegs initMem
      { s with rip := rip', regs := regUpd s.regs dst (v32.zeroExtend 64), flags := fl' } := by
  rcases hcore with ⟨hf, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩
  rw [hrun] at hexit
  dsimp [SfiPicCoreSafeV2]; rw [hrun]
  refine ⟨hf, hfs, hgs, ?_, ?_, ?_, hmem, ?_, ?_⟩
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

theorem coreSafeV2_flags_only {codeBase arenaBase fsBase gsBase : BitVec 64}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    {s : RealX64PrefixState} {fl' : RFlags} {rip' : BitVec 64}
    (hrun : s.exitKind = .running)
    (hcore : SfiPicCoreSafeV2 codeBase arenaBase fsBase gsBase initRegs initMem s) :
    SfiPicCoreSafeV2 codeBase arenaBase fsBase gsBase initRegs initMem
      { s with rip := rip', flags := fl' } := by
  rcases hcore with ⟨hf, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩
  rw [hrun] at hexit
  dsimp [SfiPicCoreSafeV2]; rw [hrun]
  exact ⟨hf, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩

theorem zext64_lt_2pow32 (m : ByteMem) (la : BitVec 64) :
    ∃ v32 : BitVec 32, readMem32Zext64 m la = v32.zeroExtend 64 :=
  ⟨m (la + 3#64) ++ (m (la + 2#64) ++ (m (la + 1#64) ++ m (la + 0#64))), rfl⟩

theorem add_ofNat_assoc (codeBase : BitVec 64) (a b : Nat) :
    (codeBase + BitVec.ofNat 64 a) + BitVec.ofNat 64 b = codeBase + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem step_standalonePicOpV2_safe {codeBase arenaBase fsBase gsBase : BitVec 64}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    {s : RealX64PrefixState} {ins : X64InstrV2} {len : Nat} (nd0 : UndefFlags)
    (hrun : s.exitKind = .running)
    (hcore : SfiPicCoreSafeV2 codeBase arenaBase fsBase gsBase initRegs initMem s)
    (hop : isStandalonePicSfiOpV2 ins = true) :
    let s' := execDecodedRealX64V2 ins len nd0 s
    s'.exitKind = .running ∧
    s'.rip = s.rip + BitVec.ofNat 64 len ∧
    SfiPicCoreSafeV2 codeBase arenaBase fsBase gsBase initRegs initMem s' := by
  cases ins with
  | nop | endbr64 => exact ⟨hrun, rfl, coreSafeV2_flags_only hrun hcore⟩
  | movRR64 dst _ | movImm64 dst _ | lea64 dst _ | shiftImm64 _ dst _ | imulRR64 dst _
  | movRR16 dst _ | movImm16 dst _ =>
    exact ⟨hrun, rfl, coreSafeV2_upd_scratch64 hrun hcore hop⟩
  | movRR32 dst _ | movImm32 dst _ | lea32 dst _ =>
    exact ⟨hrun, rfl, coreSafeV2_upd_zext32 hrun hcore hop⟩
  | aluRR64 op dst src =>
    dsimp [isStandalonePicSfiOpV2] at hop; revert hop
    cases hw : aluWritesDst op with
    | false => intro _; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp; exact ⟨hrun, rfl, coreSafeV2_flags_only hrun hcore⟩
    | true => intro hs; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp; exact ⟨hrun, rfl, coreSafeV2_upd_scratch64 hrun hcore hs⟩
  | aluImm64 op dst imm =>
    dsimp [isStandalonePicSfiOpV2] at hop; revert hop
    cases hw : aluWritesDst op with
    | false => intro _; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp; exact ⟨hrun, rfl, coreSafeV2_flags_only hrun hcore⟩
    | true => intro hs; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp; exact ⟨hrun, rfl, coreSafeV2_upd_scratch64 hrun hcore hs⟩
  | aluRR16 op dst src =>
    dsimp [isStandalonePicSfiOpV2] at hop; revert hop
    cases hw : aluWritesDst op with
    | false => intro _; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp; exact ⟨hrun, rfl, coreSafeV2_flags_only hrun hcore⟩
    | true => intro hs; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp; exact ⟨hrun, rfl, coreSafeV2_upd_scratch64 hrun hcore hs⟩
  | aluImm16 op dst imm16 =>
    dsimp [isStandalonePicSfiOpV2] at hop; revert hop
    cases hw : aluWritesDst op with
    | false => intro _; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp; exact ⟨hrun, rfl, coreSafeV2_flags_only hrun hcore⟩
    | true => intro hs; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp; exact ⟨hrun, rfl, coreSafeV2_upd_scratch64 hrun hcore hs⟩
  | aluRR32 op dst src =>
    dsimp [isStandalonePicSfiOpV2] at hop; revert hop
    cases hw : aluWritesDst op with
    | false => intro _; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp; exact ⟨hrun, rfl, coreSafeV2_flags_only hrun hcore⟩
    | true =>
      intro hd; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp
      rcases evalAluFlags32_fst op (BitVec.extractLsb' 0 32 (s.regs dst))
        (BitVec.extractLsb' 0 32 (s.regs src)) nd0 with ⟨r32, hr32⟩
      rw [hr32]; exact ⟨hrun, rfl, coreSafeV2_upd_zext32 hrun hcore hd⟩
  | aluImm32 op dst imm32 =>
    dsimp [isStandalonePicSfiOpV2] at hop; revert hop
    cases hw : aluWritesDst op with
    | false => intro _; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp; exact ⟨hrun, rfl, coreSafeV2_flags_only hrun hcore⟩
    | true =>
      intro hd; dsimp [execDecodedRealX64V2]; rw [hw]; dsimp
      rcases evalAluFlags32_fst op (BitVec.extractLsb' 0 32 (s.regs dst)) imm32 nd0 with ⟨r32, hr32⟩
      rw [hr32]; exact ⟨hrun, rfl, coreSafeV2_upd_zext32 hrun hcore hd⟩
  | store64 addr src =>
    rcases isArenaIdxAddrV2_spec hop with ⟨disp, rfl, hdisp⟩
    rcases hcore with ⟨hf, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩; rw [hrun] at hexit
    refine ⟨hrun, rfl, hf, hfs, hgs, hr15, hr14, hr13, ?_, ?_⟩
    · intro a hout; dsimp [execDecodedRealX64V2]
      rw [evalLinearAddr_arenaIdx, hr14,
          sfi_store64_preserves_outside_sym_arena s.mem arenaBase (s.regs .r13) disp (s.regs src) a hr13 hdisp hout]
      exact hmem a hout
    · dsimp [execDecodedRealX64V2]; rw [hrun]; exact hexit
  | store32 addr src =>
    rcases isArenaIdxAddrV2_spec hop with ⟨disp, rfl, hdisp⟩
    rcases hcore with ⟨hf, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩; rw [hrun] at hexit
    refine ⟨hrun, rfl, hf, hfs, hgs, hr15, hr14, hr13, ?_, ?_⟩
    · intro a hout; dsimp [execDecodedRealX64V2]
      rw [evalLinearAddr_arenaIdx, hr14,
          sfi_store32_preserves_outside_sym_arena s.mem arenaBase (s.regs .r13) disp (s.regs src) a hr13 hdisp hout]
      exact hmem a hout
    · dsimp [execDecodedRealX64V2]; rw [hrun]; exact hexit
  | load64 dst addr | load32Sext dst addr =>
    have hc := Bool.and_eq_true_iff.mp hop
    exact ⟨hrun, rfl, coreSafeV2_upd_scratch64 hrun hcore hc.1⟩
  | load32Zext dst addr =>
    have hc := Bool.and_eq_true_iff.mp hop
    rcases zext64_lt_2pow32 s.mem (evalLinearAddr s (s.rip + BitVec.ofNat 64 len) addr) with ⟨v32, hv32⟩
    dsimp [execDecodedRealX64V2]; rw [hv32]
    exact ⟨hrun, rfl, coreSafeV2_upd_zext32 hrun hcore hc.1⟩
  | load16 _ _ | store16 _ _ | aluRM64 _ _ _ | imulRM64 _ _ | lockCmpxchg64 _ _
  | push64 _ | push16 _ | pop64 _ | pop16 _ | leave64 | leave16
  | callRel32 _ _ | jmpRel _ _ | jccRel _ _ _ | jmpReg _ _ | ret _ | int3 =>
    nomatch hop

theorem peekPicMem2ndV2_spec {idx : Reg} {rem1 : List UInt8} {ins2 : X64InstrV2} {len2 : Nat}
    (h : peekPicMem2ndV2 idx rem1 = some (ins2, len2)) :
    isSandboxedPicMem2ndV2 idx ins2 = true ∧
    0 < len2 ∧ len2 ≤ rem1.length ∧
    decodeX64V2 (rem1.take len2) = .ok ins2 (rem1.take len2).length ∧
    (rem1.take len2).length = len2 := by
  dsimp [peekPicMem2ndV2] at h; revert h
  cases decodeX64V2 rem1 with
  | fault _ => intro h; nomatch h
  | ok i2 l2 =>
    dsimp
    let pfx2 := rem1.take l2
    cases hc : (((isSandboxedPicMem2ndV2 idx i2 && !(l2 == 0)) && !decide (lenTR rem1 < l2)) &&
                (decodeX64V2 pfx2 == .ok i2 pfx2.length)) with
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

theorem isPicLeaR15R11V2_eq {ins : X64InstrV2} (h : isPicLeaR15R11V2 ins = true) :
    ins = .lea64 .r11 { seg := none, addr32 := false, kind := .baseDisp (some .r15) (some (.r11, 1)) 0#64 } := by
  dsimp [isPicLeaR15R11V2] at h
  split at h <;> first | rfl | nomatch h

theorem isPicJmpR11V2_eq {ins : X64InstrV2} (h : isPicJmpR11V2 ins = true) :
    ins = .jmpReg false .r11 := by
  dsimp [isPicJmpR11V2] at h
  split at h <;> first | rfl | nomatch h

theorem peekPicJmp2nd3rdV2_spec {rem1 : List UInt8} {len2 len3 : Nat}
    (h : peekPicJmp2nd3rdV2 rem1 = some (len2, len3)) :
    0 < len2 ∧ len2 ≤ rem1.length ∧
    decodeX64V2 (rem1.take len2) =
      .ok (.lea64 .r11 { seg := none, addr32 := false, kind := .baseDisp (some .r15) (some (.r11, 1)) 0#64 }) len2 ∧
    (rem1.take len2).length = len2 ∧
    0 < len3 ∧ len3 ≤ (rem1.drop len2).length ∧
    decodeX64V2 ((rem1.drop len2).take len3) =
      .ok (.jmpReg false .r11) ((rem1.drop len2).take len3).length ∧
    ((rem1.drop len2).take len3).length = len3 := by
  dsimp [peekPicJmp2nd3rdV2] at h; revert h
  cases decodeX64V2 rem1 with
  | fault _ => intro h; nomatch h
  | ok i2 l2 =>
    dsimp
    let pfx2 := rem1.take l2
    let rem2 := rem1.drop l2
    cases hc2 : (((isPicLeaR15R11V2 i2 && !(l2 == 0)) && !decide (lenTR rem1 < l2)) &&
                 (decodeX64V2 pfx2 == .ok i2 pfx2.length)) with
    | false => intro h; nomatch h
    | true =>
      dsimp
      cases decodeX64V2 rem2 with
      | fault _ => intro h; nomatch h
      | ok i3 l3 =>
        dsimp
        let pfx3 := rem2.take l3
        cases hc3 : (((isPicJmpR11V2 i3 && !(l3 == 0)) && !decide (lenTR rem2 < l3)) &&
                     (decodeX64V2 pfx3 == .ok i3 pfx3.length)) with
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
          have hi2 := isPicLeaR15R11V2_eq d3.1
          have hi3 := isPicJmpR11V2_eq e3.1
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

theorem isSandboxedPicMem2ndV2_exec_safe {codeBase arenaBase fsBase gsBase : BitVec 64}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    {s : RealX64PrefixState} {idx : Reg} {ins2 : X64InstrV2} {len2 : Nat} (nd0 : UndefFlags)
    (hrun : s.exitKind = .running)
    (hcore : SfiPicCoreSafeV2 codeBase arenaBase fsBase gsBase initRegs initMem s)
    (hidx_lt : (s.regs idx).toNat < 4294967296)
    (hmem2 : isSandboxedPicMem2ndV2 idx ins2 = true) :
    let s' := execDecodedRealX64V2 ins2 len2 nd0 s
    s'.exitKind = .running ∧
    s'.rip = s.rip + BitVec.ofNat 64 len2 ∧
    SfiPicCoreSafeV2 codeBase arenaBase fsBase gsBase initRegs initMem s' := by
  cases ins2 with
  | store64 addr src =>
    rcases isArenaIdxAddrV2_spec hmem2 with ⟨disp, rfl, hdisp⟩
    rcases hcore with ⟨hf, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩; rw [hrun] at hexit
    refine ⟨hrun, rfl, hf, hfs, hgs, hr15, hr14, hr13, ?_, ?_⟩
    · intro a hout; dsimp [execDecodedRealX64V2]
      rw [evalLinearAddr_arenaIdx, hr14,
          sfi_store64_preserves_outside_sym_arena s.mem arenaBase (s.regs idx) disp (s.regs src) a hidx_lt hdisp hout]
      exact hmem a hout
    · dsimp [execDecodedRealX64V2]; rw [hrun]; exact hexit
  | store32 addr src =>
    rcases isArenaIdxAddrV2_spec hmem2 with ⟨disp, rfl, hdisp⟩
    rcases hcore with ⟨hf, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩; rw [hrun] at hexit
    refine ⟨hrun, rfl, hf, hfs, hgs, hr15, hr14, hr13, ?_, ?_⟩
    · intro a hout; dsimp [execDecodedRealX64V2]
      rw [evalLinearAddr_arenaIdx, hr14,
          sfi_store32_preserves_outside_sym_arena s.mem arenaBase (s.regs idx) disp (s.regs src) a hidx_lt hdisp hout]
      exact hmem a hout
    · dsimp [execDecodedRealX64V2]; rw [hrun]; exact hexit
  | load64 dst addr | load32Sext dst addr =>
    have hc := Bool.and_eq_true_iff.mp hmem2
    exact ⟨hrun, rfl, coreSafeV2_upd_scratch64 hrun hcore hc.1⟩
  | load32Zext dst addr =>
    have hc := Bool.and_eq_true_iff.mp hmem2
    rcases zext64_lt_2pow32 s.mem (evalLinearAddr s (s.rip + BitVec.ofNat 64 len2) addr) with ⟨v32, hv32⟩
    dsimp [execDecodedRealX64V2]; rw [hv32]
    exact ⟨hrun, rfl, coreSafeV2_upd_zext32 hrun hcore hc.1⟩
  | _ => nomatch hmem2

theorem stepPicPortalX64V2_untrusted {codeBase : BitVec 64} {totalBytes off len : Nat}
    {img : X64ObjImage} {ins : X64InstrV2} (nd0 : UndefFlags) {s : RealX64PrefixState}
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (hkx : s.exitKind = .running) (hnf : s.fault = false)
    (h64 : 64 ≤ off) (hlt : off < totalBytes)
    (hrip : s.rip = codeBase + BitVec.ofNat 64 off)
    (hwin : decodeX64V2 (fetchWindow16 img.code off) = .ok ins len) :
    stepPicPortalX64V2 codeBase totalBytes img nd0 s = execDecodedRealX64V2 ins len nd0 s := by
  rcases untrusted_off_portal_flags hfit h64 hlt with ⟨hp0, hp1, hrng, hsub⟩
  simp only [stepPicPortalX64V2, hkx, hnf, hrip, hp0, hp1, hrng, hsub, hwin,
             bne_self_eq_false, Bool.false_or, Bool.not_true, Bool.false_eq_true, ite_false]

theorem step_preserves_sfiPicInvV2 {codeBase arenaBase fsBase gsBase : BitVec 64}
    {totalBytes : Nat} {img : X64ObjImage}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    (hall : AllUntrustedBundlesValidV2 totalBytes img.code)
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (hhost_rsp : ∀ k, k < 8 → OutsideSymmetricArena arenaBase (initRegs .rsp + BitVec.ofNat 64 k))
    (nd0 : UndefFlags) {s : RealX64PrefixState}
    (hinv : SfiPicMachineInvV2 codeBase arenaBase fsBase gsBase totalBytes img initRegs initMem s) :
    SfiPicMachineInvV2 codeBase arenaBase fsBase gsBase totalBytes img initRegs initMem
      (stepPicPortalX64V2 codeBase totalBytes img nd0 s) := by
  rcases hinv with ⟨hcore, hphase_fn⟩
  have hnf : s.fault = false := hcore.1
  cases hkx : s.exitKind with
  | portalReturn =>
    have hst : stepPicPortalX64V2 codeBase totalBytes img nd0 s = s := by
      dsimp [stepPicPortalX64V2]; rw [hkx]; rfl
    rw [hst]; exact ⟨hcore, fun hr => by rw [hkx] at hr; nomatch hr⟩
  | portalHostcall =>
    have hst : stepPicPortalX64V2 codeBase totalBytes img nd0 s = s := by
      dsimp [stepPicPortalX64V2]; rw [hkx]; rfl
    rw [hst]; exact ⟨hcore, fun hr => by rw [hkx] at hr; nomatch hr⟩
  | running =>
    have hphase := hphase_fn hkx
    cases hphase with
    | atPortal0 hrip0 =>
      have hst : stepPicPortalX64V2 codeBase totalBytes img nd0 s =
          { s with rip := readMem64 s.mem (s.regs .rsp),
                   regs := regUpd s.regs .rsp (s.regs .rsp + 8#64),
                   exitKind := .portalReturn } := by
        have hbeq0 : (codeBase == codeBase) = true := beq_self_eq_true codeBase
        simp only [stepPicPortalX64V2, hkx, hnf, hrip0, hbeq0,
                   bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ite_false, ite_true]
      rw [hst]
      rcases hcore with ⟨_, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩; rw [hkx] at hexit
      refine ⟨⟨hnf, hfs, hgs, ?_, ?_, ?_, hmem, ?_, ?_, ?_⟩, fun hr => nomatch hr⟩
      · dsimp only; rw [regUpd_ne s.regs (by decide : .r15 ≠ .rsp) _]; exact hr15
      · dsimp only; rw [regUpd_ne s.regs (by decide : .r14 ≠ .rsp) _]; exact hr14
      · dsimp only; rw [regUpd_ne s.regs (by decide : .r13 ≠ .rsp) _]; exact hr13
      · dsimp only; rw [hexit.1]; dsimp [readMem64]
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
          have hv := congrArg BitVec.toNat (eq_of_beq heq); rw [htn32] at hv
          have : 32 = 0 := Nat.add_left_cancel (by rw [hv, Nat.add_zero]); nomatch this
      have hst : stepPicPortalX64V2 codeBase totalBytes img nd0 s = { s with exitKind := .portalHostcall } := by
        have hbeq32 : (codeBase + 32#64 == codeBase + 32#64) = true := beq_self_eq_true _
        simp only [stepPicPortalX64V2, hkx, hnf, hrip1, hne0, hbeq32,
                   bne_self_eq_false, Bool.false_or, Bool.false_eq_true, ite_false, ite_true]
      rw [hst]
      rcases hcore with ⟨_, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩; rw [hkx] at hexit
      exact ⟨⟨hnf, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩, fun hr => nomatch hr⟩
    | pendingPicJmp curOff tgtOff pfx3 hr11_eq htgt_lt htgt_mod hcur64 hcur_lt hrip hdec3 hwin3 =>
      have hlen_le16 : pfx3.length ≤ 16 := Nat.le_trans (decodeX64V2_len_bounds hdec3).2.1 (by decide)
      rcases fetchBytes_prefix pfx3 img.code 16 curOff hlen_le16 hwin3 with ⟨sfx, hsfx⟩
      have hwin_dec : decodeX64V2 (fetchWindow16 img.code curOff) = .ok (.jmpReg false .r11) pfx3.length := by
        dsimp [fetchWindow16]; rw [hsfx]; exact decodeX64V2_prefix_invariant hdec3 sfx
      have hst : stepPicPortalX64V2 codeBase totalBytes img nd0 s = { s with rip := s.regs .r11 } :=
        stepPicPortalX64V2_untrusted nd0 hfit hkx hnf hcur64 hcur_lt hrip hwin_dec
      rw [hst]
      rcases hcore with ⟨_, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩; rw [hkx] at hexit
      refine ⟨⟨hnf, hfs, hgs, hr15, hr14, hr13, hmem, ?_⟩, fun _ => ?_⟩
      · dsimp; rw [hkx]; exact hexit
      · exact enterPicTargetV2 hall htgt_lt htgt_mod hr11_eq
    | pendingPicLea curOff leaLen tgtOff pfx2 pfx3 hr11_eq htgt_lt htgt_mod
        hcur64 hcur_lt hnext64 hnext_lt hrip hdec2 hpfx2_len hwin2 hdec3 hwin3 =>
      have hlen_le16 : pfx2.length ≤ 16 := by
        rw [hpfx2_len]; exact Nat.le_trans (decodeX64V2_len_bounds hdec2).2.1 (by decide)
      rcases fetchBytes_prefix pfx2 img.code 16 curOff hlen_le16 hwin2 with ⟨sfx, hsfx⟩
      have hwin_dec : decodeX64V2 (fetchWindow16 img.code curOff) =
          .ok (.lea64 .r11 { seg := none, addr32 := false, kind := .baseDisp (some .r15) (some (.r11, 1)) 0#64 }) leaLen := by
        dsimp [fetchWindow16]; rw [hsfx]; exact decodeX64V2_prefix_invariant hdec2 sfx
      have hst : stepPicPortalX64V2 codeBase totalBytes img nd0 s =
          { s with rip := s.rip + BitVec.ofNat 64 leaLen,
                   regs := regUpd s.regs .r11 (s.regs .r15 + s.regs .r11 * 1#64 + 0#64) } :=
        stepPicPortalX64V2_untrusted nd0 hfit hkx hnf hcur64 hcur_lt hrip hwin_dec
      rw [hst]
      refine ⟨coreSafeV2_upd_scratch64 hkx hcore rfl, fun _ => ?_⟩
      have hr11_new : (regUpd s.regs .r11 (s.regs .r15 + s.regs .r11 * 1#64 + 0#64)) .r11 =
          codeBase + BitVec.ofNat 64 tgtOff := by
        rw [regUpd_eq, hcore.2.2.2.1, hr11_eq, BitVec.mul_one, BitVec.add_zero]
      have hrip_new : s.rip + BitVec.ofNat 64 leaLen = codeBase + BitVec.ofNat 64 (curOff + leaLen) := by
        rw [hrip, add_ofNat_assoc]
      exact SfiPicPhaseV2.pendingPicJmp (curOff + leaLen) tgtOff pfx3 hr11_new htgt_lt htgt_mod
        hnext64 hnext_lt hrip_new hdec3 hwin3
    | pendingMem bBase fuel nextOff curOff idx ins2 pfx2 rem2 hidx_lt hb64 hb_lt hb_mod hb_le
        hcur64 hcur_lt hrip hmem2 hdec2 hwin2 hnrip hnlen hnlast hnbytes hnchk =>
      have hlen_le16 : pfx2.length ≤ 16 := Nat.le_trans (decodeX64V2_len_bounds hdec2).2.1 (by decide)
      rcases fetchBytes_prefix pfx2 img.code 16 curOff hlen_le16 hwin2 with ⟨sfx, hsfx⟩
      have hwin_dec : decodeX64V2 (fetchWindow16 img.code curOff) = .ok ins2 pfx2.length := by
        dsimp [fetchWindow16]; rw [hsfx]; exact decodeX64V2_prefix_invariant hdec2 sfx
      have hst : stepPicPortalX64V2 codeBase totalBytes img nd0 s = execDecodedRealX64V2 ins2 pfx2.length nd0 s :=
        stepPicPortalX64V2_untrusted nd0 hfit hkx hnf hcur64 hcur_lt hrip hwin_dec
      rw [hst]
      rcases isSandboxedPicMem2ndV2_exec_safe nd0 hkx hcore hidx_lt hmem2 (len2 := pfx2.length) with
        ⟨_, hrip2, hcore2⟩
      refine ⟨hcore2, fun _ => ?_⟩
      have hrip_n : (execDecodedRealX64V2 ins2 pfx2.length nd0 s).rip =
          codeBase + BitVec.ofNat 64 (bBase + nextOff) := by
        rw [hrip2, hrip, add_ofNat_assoc, hnrip]
      exact enterNextPicMacroV2 hall hb64 hb_lt hb_mod hb_le hrip_n hnlen hnlast hnbytes hnchk
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
          dsimp [checkSfiPicMacroStreamV2] at hchk; revert hchk
          cases hdec1 : decodeX64V2 (b0 :: bs) with
          | fault _ => intro h; nomatch h
          | ok ins1 len1 =>
            dsimp
            let pfx1 := (b0 :: bs).take len1
            let rem1 := (b0 :: bs).drop len1
            cases hbad1 : (((len1 == 0 || decide (lenTR (b0 :: bs) < len1)) || decide (32 < off + len1)) ||
                           (decodeX64V2 pfx1 != .ok ins1 pfx1.length)) with
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
              have hpfx1_dec : decodeX64V2 pfx1 = .ok ins1 pfx1.length := by
                cases heq : (decodeX64V2 pfx1 == .ok ins1 pfx1.length) with
                | true => exact eq_of_beq heq
                | false => have hf := hb1.2; dsimp [bne] at hf; rw [heq] at hf; nomatch hf
              have hpfx1_win : ∀ i, i < pfx1.length → img.code.getByte? ((bBase + off) + i) = listGet? pfx1 i := by
                intro i hi
                have hi_len1 : i < len1 := by rw [← hpfx1_len]; exact hi
                rw [hbytes i (Nat.lt_of_lt_of_le hi_len1 hlen1_le_rem), ← listGet?_take len1 (b0 :: bs) i hi_len1]
              have hlen1_le16 : pfx1.length ≤ 16 := Nat.le_trans (decodeX64V2_len_bounds hpfx1_dec).2.1 (by decide)
              rcases fetchBytes_prefix pfx1 img.code 16 (bBase + off) hlen1_le16 hpfx1_win with ⟨sfx1, hsfx1⟩
              have hwin1_dec : decodeX64V2 (fetchWindow16 img.code (bBase + off)) = .ok ins1 len1 := by
                dsimp [fetchWindow16]; rw [hsfx1, ← hpfx1_len]
                exact decodeX64V2_prefix_invariant hpfx1_dec sfx1
              have hst1 : stepPicPortalX64V2 codeBase totalBytes img nd0 s = execDecodedRealX64V2 ins1 len1 nd0 s :=
                stepPicPortalX64V2_untrusted nd0 hfit hkx hnf hcur64 hcur_lt hrip hwin1_dec
              have hrem1_len : (off + len1) + rem1.length = 32 := by
                dsimp [rem1]; rw [List.length_drop, Nat.add_assoc, Nat.add_sub_of_le hlen1_le_rem]; exact hlen
              have hrem1_bytes : ∀ i, i < rem1.length →
                  img.code.getByte? ((bBase + (off + len1)) + i) = listGet? rem1 i := by
                intro i hi; dsimp [rem1] at hi ⊢; rw [listGet?_drop len1 (b0 :: bs) i]
                rw [List.length_drop] at hi
                rw [← Nat.add_assoc bBase off len1, Nat.add_assoc (bBase + off) len1 i]
                exact hbytes (len1 + i) (Nat.add_lt_of_lt_sub' hi)
              have finishStandalone :
                  isStandalonePicSfiOpV2 ins1 = true →
                  ((bBase + 32 == totalBytes) && decide (off + len1 = 32)) = false →
                  checkSfiPicMacroStreamV2 totalBytes bBase (bBase + 32 == totalBytes) fuel' (off + len1) rem1 = true →
                  SfiPicMachineInvV2 codeBase arenaBase fsBase gsBase totalBytes img initRegs initMem
                    (stepPicPortalX64V2 codeBase totalBytes img nd0 s) := by
                intro hop1 hnlast1 hchk1; rw [hst1]
                rcases step_standalonePicOpV2_safe nd0 hkx hcore hop1 (len := len1) with ⟨_, hrip1, hcore1⟩
                refine ⟨hcore1, fun _ => ?_⟩
                have hrip1' : (execDecodedRealX64V2 ins1 len1 nd0 s).rip =
                    codeBase + BitVec.ofNat 64 (bBase + (off + len1)) := by
                  rw [hrip1, hrip, add_ofNat_assoc, Nat.add_assoc]
                exact enterNextPicMacroV2 hall hb64 hb_lt hb_mod hb_le hrip1' hrem1_len hnlast1 hrem1_bytes hchk1
              have finishMem1st (idx : Reg) (v32 : BitVec 32)
                  (hscr : isPicScratchReg idx = true)
                  (hexec : execDecodedRealX64V2 ins1 len1 nd0 s =
                    { s with rip := s.rip + BitVec.ofNat 64 len1, regs := regUpd s.regs idx (v32.zeroExtend 64) })
                  (ins2 : X64InstrV2) (len2 : Nat)
                  (hp2 : peekPicMem2ndV2 idx rem1 = some (ins2, len2))
                  (hbad2 : (decide (32 < off + len1 + len2) ||
                           ((bBase + 32 == totalBytes) && decide (off + len1 + len2 = 32))) = false)
                  (hchk2 : checkSfiPicMacroStreamV2 totalBytes bBase (bBase + 32 == totalBytes)
                             fuel' (off + len1 + len2) (rem1.drop len2) = true) :
                  SfiPicMachineInvV2 codeBase arenaBase fsBase gsBase totalBytes img initRegs initMem
                    (stepPicPortalX64V2 codeBase totalBytes img nd0 s) := by
                rw [hst1, hexec]
                rcases peekPicMem2ndV2_spec hp2 with ⟨hmem2, hlen2_pos, hlen2_le, hdec2, hpfx2_len⟩
                have hb2_pair := Bool.or_eq_false_iff.mp hbad2
                have hdst_ok : isPicZext32DstReg idx = true := by dsimp [isPicZext32DstReg]; rw [hscr]; rfl
                refine ⟨coreSafeV2_upd_zext32 hkx hcore hdst_ok, fun _ => ?_⟩
                have hidx_val : (regUpd s.regs idx (v32.zeroExtend 64) idx).toNat < 4294967296 := by
                  rw [regUpd_eq, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]; exact v32.isLt
                have hoff1_lt32 : off + len1 < 32 :=
                  Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hlen2_pos)
                    (Nat.not_lt.mp (of_decide_eq_false hb2_pair.1))
                have hcur1_64 : 64 ≤ bBase + (off + len1) := Nat.le_trans hb64 (Nat.le_add_right bBase _)
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
                  rw [List.length_drop, Nat.add_assoc (off + len1) len2 _, Nat.add_sub_of_le hlen2_le]; exact hrem1_len
                have hnbytes2 : ∀ i, i < (rem1.drop len2).length →
                    img.code.getByte? ((bBase + (off + len1 + len2)) + i) = listGet? (rem1.drop len2) i := by
                  intro i hi; rw [listGet?_drop len2 rem1 i]; rw [List.length_drop] at hi
                  rw [← Nat.add_assoc bBase (off + len1) len2, Nat.add_assoc (bBase + (off + len1)) len2 i]
                  exact hrem1_bytes (len2 + i) (Nat.add_lt_of_lt_sub' hi)
                exact SfiPicPhaseV2.pendingMem bBase fuel' (off + len1 + len2) (bBase + (off + len1))
                  idx ins2 (rem1.take len2) (rem1.drop len2) hidx_val hb64 hb_lt hb_mod hb_le
                  hcur1_64 hcur1_lt hrip1 hmem2 hdec2 hwin2 hnrip hnlen2 hb2_pair.2 hnbytes2 hchk2
              cases ins1 with
              | jmpRel has66 rel =>
                dsimp
                cases hok_j : (!has66 && sfiPicJmpTargetOk totalBytes bBase off len1 rel) with
                | false => intro h; nomatch h
                | true =>
                  intro _; rw [hst1]
                  have cj0 := Bool.and_eq_true_iff.mp hok_j
                  have cj := Bool.and_eq_true_iff.mp (by dsimp [sfiPicJmpTargetOk] at cj0; exact cj0.2)
                  rcases hcore with ⟨_, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩; rw [hkx] at hexit
                  refine ⟨⟨hnf, hfs, hgs, hr15, hr14, hr13, hmem, ?_⟩, fun _ => ?_⟩
                  · dsimp [execDecodedRealX64V2]; rw [hkx]; exact hexit
                  · have hrip_j : (execDecodedRealX64V2 (.jmpRel has66 rel) len1 nd0 s).rip =
                        codeBase + BitVec.ofNat 64 (sfiPicJmpTarget bBase off len1 rel) := by
                      dsimp [execDecodedRealX64V2]; unfold sfiPicJmpTarget
                      rw [hrip, add_ofNat_assoc, BitVec.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
                    exact enterPicTargetV2 hall (natLtB_true cj.1) (natEqB_true cj.2) hrip_j
              | jccRel has66 cc rel =>
                dsimp
                cases hok_jc : ((!has66 && sfiPicJmpTargetOk totalBytes bBase off len1 rel) &&
                                !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                | false => intro h; nomatch h
                | true =>
                  dsimp; intro hchk_next; rw [hst1]
                  have cj1 := Bool.and_eq_true_iff.mp hok_jc
                  have cj1b := Bool.and_eq_true_iff.mp cj1.1
                  have cj2 := Bool.and_eq_true_iff.mp (by dsimp [sfiPicJmpTargetOk] at cj1b; exact cj1b.2)
                  have hnlast1 := bnot_eq_true_imp_false cj1.2
                  rcases hcore with ⟨_, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩; rw [hkx] at hexit
                  cases hcond : evalCond cc s.flags with
                  | true =>
                    dsimp [execDecodedRealX64V2]; rw [hcond]; dsimp
                    refine ⟨⟨hnf, hfs, hgs, hr15, hr14, hr13, hmem, ?_⟩, fun _ => ?_⟩
                    · rw [hkx]; exact hexit
                    · have hrip_j : s.rip + BitVec.ofNat 64 len1 + rel =
                          codeBase + BitVec.ofNat 64 (sfiPicJmpTarget bBase off len1 rel) := by
                        unfold sfiPicJmpTarget
                        rw [hrip, add_ofNat_assoc, BitVec.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
                      exact enterPicTargetV2 hall (natLtB_true cj2.1) (natEqB_true cj2.2) hrip_j
                  | false =>
                    dsimp [execDecodedRealX64V2]; rw [hcond]; dsimp
                    refine ⟨⟨hnf, hfs, hgs, hr15, hr14, hr13, hmem, ?_⟩, fun _ => ?_⟩
                    · rw [hkx]; exact hexit
                    · have hrip_f : s.rip + BitVec.ofNat 64 len1 =
                          codeBase + BitVec.ofNat 64 (bBase + (off + len1)) := by
                        rw [hrip, add_ofNat_assoc, Nat.add_assoc]
                      exact enterNextPicMacroV2 hall hb64 hb_lt hb_mod hb_le hrip_f hrem1_len hnlast1 hrem1_bytes hchk_next
              | movRR32 idx dstSrc =>
                dsimp
                cases hscr : isPicScratchReg idx with
                | false =>
                  dsimp
                  cases hp_ok : (isStandalonePicSfiOpV2 (.movRR32 idx dstSrc) &&
                                 !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                  | false => intro h; nomatch h
                  | true =>
                    dsimp; intro hchk_next
                    have cp := Bool.and_eq_true_iff.mp hp_ok
                    exact finishStandalone cp.1 (bnot_eq_true_imp_false cp.2) hchk_next
                | true =>
                  dsimp
                  cases hp2 : peekPicMem2ndV2 idx rem1 with
                  | none =>
                    dsimp
                    cases hp_ok : (isStandalonePicSfiOpV2 (.movRR32 idx dstSrc) &&
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
                      intro hchk2
                      exact finishMem1st idx (BitVec.extractLsb' 0 32 (s.regs dstSrc)) hscr rfl ins2 len2 hp2 hbad2 hchk2
              | movImm32 idx imm32 =>
                dsimp
                cases hscr : isPicScratchReg idx with
                | false =>
                  dsimp
                  cases hp_ok : (isStandalonePicSfiOpV2 (.movImm32 idx imm32) &&
                                 !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                  | false => intro h; nomatch h
                  | true =>
                    dsimp; intro hchk_next
                    have cp := Bool.and_eq_true_iff.mp hp_ok
                    exact finishStandalone cp.1 (bnot_eq_true_imp_false cp.2) hchk_next
                | true =>
                  dsimp
                  cases hp2 : peekPicMem2ndV2 idx rem1 with
                  | none =>
                    dsimp
                    cases hp_ok : (isStandalonePicSfiOpV2 (.movImm32 idx imm32) &&
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
                      intro hchk2
                      exact finishMem1st idx imm32 hscr rfl ins2 len2 hp2 hbad2 hchk2
              | aluImm32 op dst mask =>
                dsimp
                cases hand_r11 : (op == .and && dst == .r11) with
                | false =>
                  dsimp
                  cases hp_ok : (isStandalonePicSfiOpV2 (.aluImm32 op dst mask) &&
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
                  cases hpj : peekPicJmp2nd3rdV2 rem1 with
                  | none =>
                    dsimp
                    cases hp_ok : (isStandalonePicSfiOpV2 (.aluImm32 .and .r11 mask) &&
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
                      rcases peekPicJmp2nd3rdV2_spec hpj with
                        ⟨hlen2_pos, hlen2_le, hdec2, hpfx2_len, hlen3_pos, hlen3_le, hdec3, hpfx3_len⟩
                      have cm1 := Bool.and_eq_true_iff.mp hok_m
                      have cm2 := Bool.and_eq_true_iff.mp cm1.1
                      have hle32 : off + len1 + len2 + len3 ≤ 32 := by
                        cases hd : decide (32 < off + len1 + len2 + len3) with
                        | false => exact Nat.not_lt.mp (of_decide_eq_false hd)
                        | true => rw [hd] at cm1; nomatch cm1.2
                      let a32 := BitVec.extractLsb' 0 32 (s.regs .r11)
                      refine ⟨coreSafeV2_upd_zext32 hkx hcore rfl, fun _ => ?_⟩
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
                      exact SfiPicPhaseV2.pendingPicLea (bBase + (off + len1)) len2 tgtOff
                        (rem1.take len2) ((rem1.drop len2).take len3) hr11_eq ht_lt ht_mod
                        hcur1_64 hcur1_lt hnext64 hnext_lt hrip1 hdec2 hpfx2_len hwin2 hdec3 hwin3
              | nop | endbr64 | movRR64 _ _ | movRR16 _ _ | movImm64 _ _ | movImm16 _ _
              | load64 _ _ | load32Zext _ _ | load32Sext _ _ | load16 _ _
              | store64 _ _ | store32 _ _ | store16 _ _ | lea64 _ _ | lea32 _ _
              | aluRR64 _ _ _ | aluImm64 _ _ _ | aluRR32 _ _ _ | aluRR16 _ _ _ | aluImm16 _ _ _ | aluRM64 _ _ _
              | shiftImm64 _ _ _ | imulRR64 _ _ | imulRM64 _ _ | lockCmpxchg64 _ _
              | push64 _ | push16 _ | pop64 _ | pop16 _ | leave64 | leave16
              | callRel32 _ _ | jmpReg _ _ | ret _ | int3 =>
                dsimp
                cases hp_ok : (isStandalonePicSfiOpV2 _ &&
                               !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                | false => intro h; nomatch h
                | true =>
                  dsimp; intro hchk_next
                  have cp := Bool.and_eq_true_iff.mp hp_ok
                  exact finishStandalone cp.1 (bnot_eq_true_imp_false cp.2) hchk_next

theorem runPicPortalX64V2_preserves_inv {codeBase arenaBase fsBase gsBase : BitVec 64}
    {totalBytes : Nat} {img : X64ObjImage}
    {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    (hall : AllUntrustedBundlesValidV2 totalBytes img.code)
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (hhost_rsp : ∀ k, k < 8 → OutsideSymmetricArena arenaBase (initRegs .rsp + BitVec.ofNat 64 k)) :
    ∀ (steps : Nat) (nd : Nat → UndefFlags) (s : RealX64PrefixState),
      SfiPicMachineInvV2 codeBase arenaBase fsBase gsBase totalBytes img initRegs initMem s →
      SfiPicMachineInvV2 codeBase arenaBase fsBase gsBase totalBytes img initRegs initMem
        (runPicPortalX64V2 codeBase totalBytes img steps nd s)
  | 0, _, _, hinv => hinv
  | steps + 1, nd, s, hinv =>
    runPicPortalX64V2_preserves_inv hall hfit hhost_rsp steps (fun k => nd (k + 1))
      (stepPicPortalX64V2 codeBase totalBytes img (nd 0) s)
      (step_preserves_sfiPicInvV2 hall hfit hhost_rsp (nd 0) hinv)

theorem sfiPicPhaseV2_rip_in_range {codeBase : BitVec 64} {totalBytes : Nat} {img : X64ObjImage}
    {s : RealX64PrefixState} (hall : AllUntrustedBundlesValidV2 totalBytes img.code)
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (hp : SfiPicPhaseV2 codeBase totalBytes img s) :
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

/-- Universal Prefix-Hardened PIC Multi-Function SFI Soundness Theorem (`checkSfiPicMultiFnV2_sound`):
    Holds universally over ALL 64-bit `codeBase`, `arenaBase`, AND arbitrary Ring-3 segment bases
    `fsBase, gsBase : BitVec 64` (including non-zero glibc TLS `%fs` and arbitrary `wrfsbase`/`wrgsbase` values)! -/
theorem checkSfiPicMultiFnV2_sound
    {codeBase arenaBase fsBase gsBase : BitVec 64} {totalBytes : Nat} {img : X64ObjImage}
    (hok : checkSfiPicMultiFnV2 totalBytes img = true)
    (hfit : codeBase.toNat + totalBytes < 2 ^ 64)
    (s0 : RealX64PrefixState)
    (entryOff : Nat)
    (hentry_lt : entryOff < totalBytes) (hentry_mod : entryOff % 32 = 0)
    (hrip0 : s0.rip = codeBase + BitVec.ofNat 64 entryOff)
    (hfs0 : s0.fsBase = fsBase)
    (hgs0 : s0.gsBase = gsBase)
    (hr15_0 : s0.regs .r15 = codeBase)
    (hr14_0 : s0.regs .r14 = arenaBase)
    (hr13_0 : (s0.regs .r13).toNat < 4294967296)
    (hhost_rsp : ∀ k, k < 8 → OutsideSymmetricArena arenaBase (s0.regs .rsp + BitVec.ofNat 64 k))
    (hrun0 : s0.exitKind = .running)
    (hnf0 : s0.fault = false) :
    ∀ (steps : Nat) (nd : Nat → UndefFlags),
      let sf := runPicPortalX64V2 codeBase totalBytes img steps nd s0
      sf.fault = false ∧
      sf.fsBase = fsBase ∧
      sf.gsBase = gsBase ∧
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
  have hall := checkSfiPicMultiFnV2_bundlesValid hok
  have hinv0 : SfiPicMachineInvV2 codeBase arenaBase fsBase gsBase totalBytes img s0.regs s0.mem s0 := by
    refine ⟨⟨hnf0, hfs0, hgs0, hr15_0, hr14_0, hr13_0, fun _ _ => rfl, ?_⟩, ?_⟩
    · rw [hrun0]; exact ⟨rfl, fun _ _ => rfl⟩
    · intro _; exact enterPicTargetV2 hall hentry_lt hentry_mod hrip0
  rcases runPicPortalX64V2_preserves_inv hall hfit hhost_rsp steps nd s0 hinv0 with ⟨hcore_f, hphase_f⟩
  let sf := runPicPortalX64V2 codeBase totalBytes img steps nd s0
  rcases hcore_f with ⟨hf, hfs, hgs, hr15, hr14, hr13, hmem, hexit⟩
  refine ⟨hf, hfs, hgs, hr15, hr14, hr13, hmem, ?_, ?_, ?_⟩
  · intro hrun_f
    have hph := hphase_f hrun_f
    rcases sfiPicPhaseV2_rip_in_range hall hfit hph with ⟨hlo, hhi⟩
    rw [hrun_f] at hexit
    exact ⟨hlo, hhi, hexit.1, hexit.2⟩
  · intro hret_f; rw [hret_f] at hexit; exact hexit
  · intro hhc_f; rw [hhc_f] at hexit; exact hexit

end PicMultiFnSfiV2
