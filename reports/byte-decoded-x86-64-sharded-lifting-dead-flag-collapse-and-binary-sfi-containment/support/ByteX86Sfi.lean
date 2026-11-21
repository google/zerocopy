prelude
import Init.Core
import Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.List.Basic
import Init.Data.List.TakeDrop
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Lemmas
import ByteX86Base

/-!
Decidable, Loop-Invariant-Free Binary SFI Containment Checker (`checkSfiObject`)
over the Unified Variable-Length x86-64 Byte Decoder & `ByteCodeTree` Semantics.

Proves `checkSfiObject_preserves_rust_host_safety`: any arbitrarily large cyclic
C `.o` object passing `checkSfiObject` executes with zero faults, preserves
`%r14`, `%rsp`, and all System V AMD64 callee-saved registers (`%rbx`, `%rbp`,
`%r12`–`%r15`), confines `rip` to `[0, totalBytes)`, and never modifies a single
byte of Rust host memory outside its 4 GiB + 64 KiB guard arena across ALL step
counts `steps : Nat` and ALL hardware demonic flag streams `nd : Nat → UndefFlags`
— eliminating `#[anneal::trusted]` waivers for sandboxed C archives with ZERO
manual loop invariants!
-/

namespace ByteX86

/-! ## Section 4A: Host Protection Surfaces, Sandbox Arena, & Negative Control -/

def isHostProtectedReg : Reg → Bool
  | .rsp | .rbp | .rbx | .r12 | .r13 | .r14 | .r15 => true
  | _ => false

def isSfiScratchReg (r : Reg) : Bool := !isHostProtectedReg r

theorem sfiScratch_ne_protected {dst r : Reg}
    (hscr : isSfiScratchReg dst = true) (hprot : isHostProtectedReg r = true) :
    r ≠ dst := by
  intro heq; subst heq
  dsimp [isSfiScratchReg] at hscr
  rw [hprot] at hscr
  nomatch hscr

theorem sfiScratch_ne_r14 {dst : Reg} (hscr : isSfiScratchReg dst = true) : .r14 ≠ dst :=
  sfiScratch_ne_protected hscr rfl

theorem sfiScratch_ne_rsp {dst : Reg} (hscr : isSfiScratchReg dst = true) : .rsp ≠ dst :=
  sfiScratch_ne_protected hscr rfl

/-- 4 GiB mapped sandbox arena + 64 KiB upper guard page (`2^32 + 65536` bytes). -/
def SandboxBound : Nat := 4294967296 + 65536

def OutsideSandboxArena (r14Base a : BitVec 64) : Prop :=
  SandboxBound ≤ (a - r14Base).toNat

/-- Any 8-byte store to `[r14Base + idx*1 + disp]` with 32-bit zero-extended `idx < 2^32`
    and `disp ≤ 65528` leaves every Rust host byte `OutsideSandboxArena r14Base` untouched! -/
theorem sfi_store_preserves_outside_arena
    (m : ByteMem) (r14Base idxVal disp val a : BitVec 64)
    (hidx : idxVal.toNat < 4294967296)
    (hdisp : disp.toNat ≤ 65528)
    (hout : OutsideSandboxArena r14Base a) :
    writeMem64 m (r14Base + idxVal * BitVec.ofNat 64 1 + disp) val a = m a := by
  apply writeMem64_byte_ne
  intro k hk heq
  subst heq
  unfold OutsideSandboxArena SandboxBound at hout
  have hm1 : idxVal * BitVec.ofNat 64 1 = idxVal := BitVec.mul_one idxVal
  rw [hm1, BitVec.add_assoc r14Base idxVal disp,
      BitVec.add_assoc r14Base (idxVal + disp) (BitVec.ofNat 64 k),
      BitVec.add_comm r14Base _, BitVec.add_sub_cancel] at hout
  have hsum_id : idxVal.toNat + disp.toNat < 4294967296 + 65528 :=
    Nat.add_lt_add_of_lt_of_le hidx hdisp
  have hsum_id64 : idxVal.toNat + disp.toNat < 2 ^ 64 :=
    Nat.lt_trans hsum_id (by decide)
  have hsum_all' : idxVal.toNat + disp.toNat + k < (4294967296 + 65528) + 8 :=
    Nat.add_lt_add hsum_id hk
  have hsum_all : idxVal.toNat + disp.toNat + k < 4294967296 + 65536 := hsum_all'
  have hsum_all64 : idxVal.toNat + disp.toNat + k < 2 ^ 64 :=
    Nat.lt_trans hsum_all (by decide)
  have hk64 : k < 2 ^ 64 := Nat.lt_trans hk (by decide)
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hsum_id64, Nat.mod_eq_of_lt hk64, Nat.mod_eq_of_lt hsum_all64] at hout
  exact Nat.not_lt_of_ge hout hsum_all

/-- Negative-Control Theorem (`guest_stack_callee_save_unsound_under_sfi`):
    If a sandboxed `.o` were permitted to save/restore host callee-saved registers (`%rbx`)
    inside its own `[%r14, %r14 + 2^32)` arena, a memory-confined in-sandbox store overwrites
    the saved `%rbx` slot and corrupts the Rust caller's `%rbx` upon `ret`! -/
def guestClobberRbxImg : X64ObjImage :=
  { code := .leaf [0x49, 0x89, 0x1E, 0x89, 0xC0, 0x49, 0x89, 0x0C, 0x06, 0x49, 0x8B, 0x1E, 0xC3] }

theorem guest_stack_callee_save_unsound_under_sfi :
    let r14Base := 0x0000000100000000#64
    let regs0 : Reg → BitVec 64 := fun r =>
      if r == .r14 then r14Base
      else if r == .rbx then 0x12345678#64
      else if r == .rcx then 0xBADC0FFEE#64
      else 0#64
    let s0 : X64State := { rip := 0, regs := regs0, flags := {}, mem := fun _ => 0#8 }
    let sf := runX64 guestClobberRbxImg 5 (fun _ => {}) s0
    sf.halted = true ∧ sf.fault = false ∧ sf.regs .rbx = 0xBADC0FFEE#64 ∧ sf.regs .rbx ≠ s0.regs .rbx := by
  decide

/-! ## Section 4B: Decidable 32-Byte Bundle & `ByteCodeTree` SFI Verifier -/

def isPureSfiOp : X64Instr → Bool
  | .nop | .endbr64 | .vzeroupper => true
  | .movRR64 dst _ | .movRR32 dst _ | .movImm64 dst _ | .movImm32 dst _
  | .lea64 dst _ | .shiftImm64 _ dst _ | .imulRR64 dst _
  | .bsf64 dst _ | .tzcnt64 dst _ => isSfiScratchReg dst
  | .aluRR64 op dst _ | .aluImm64 op dst _
  | .aluRR32 op dst _ | .aluImm32 op dst _ =>
    if aluWritesDst op then isSfiScratchReg dst else true
  | _ => false

def isSandboxedMem2nd (idx : Reg) : X64Instr → Bool
  | .store64 (.baseDisp .r14 (some (idx', 1)) disp) _ =>
    (idx' == idx) && natLeB disp.toNat 65528
  | .load64 dst (.baseDisp .r14 (some (idx', 1)) disp) =>
    isSfiScratchReg dst && (idx' == idx) && natLeB disp.toNat 65528
  | _ => false

def peekMem2nd (idx : Reg) (rem1 : List UInt8) : Option (X64Instr × Nat) :=
  match decodeX64 rem1 with
  | .ok ins2 len2 =>
    let pfx2 := rem1.take len2
    if isSandboxedMem2nd idx ins2 && !(len2 == 0) && !decide (lenTR rem1 < len2) &&
       (decodeX64 pfx2 == .ok ins2 pfx2.length) then some (ins2, len2)
    else none
  | .fault _ => none

def peekMaskedJmp2nd (rem1 : List UInt8) : Option Nat :=
  match decodeX64 rem1 with
  | .ok (.jmpReg .rax) len2 =>
    let pfx2 := rem1.take len2
    if !(len2 == 0) && !decide (lenTR rem1 < len2) &&
       (decodeX64 pfx2 == .ok (.jmpReg .rax) pfx2.length) then some len2
    else none
  | _ => none

def sfiJmpTarget (bBase off len1 : Nat) (rel : BitVec 64) : Nat :=
  (BitVec.ofNat 64 (bBase + off + len1) + rel).toNat

def sfiJmpTargetOk (totalBytes bBase off len1 : Nat) (rel : BitVec 64) : Bool :=
  natLtB (sfiJmpTarget bBase off len1 rel) totalBytes &&
  natEqB (sfiJmpTarget bBase off len1 rel % 32) 0

def checkSfiMacroStream (totalBytes bBase : Nat) (isLast : Bool) : Nat → Nat → List UInt8 → Bool
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
        | .ret =>
          checkSfiMacroStream totalBytes bBase isLast fuel (off + len1) rem1
        | .jmpRel rel =>
          if sfiJmpTargetOk totalBytes bBase off len1 rel then
            checkSfiMacroStream totalBytes bBase isLast fuel (off + len1) rem1
          else false
        | .jccRel _ rel =>
          if sfiJmpTargetOk totalBytes bBase off len1 rel &&
             !(isLast && decide (off + len1 = 32)) then
            checkSfiMacroStream totalBytes bBase isLast fuel (off + len1) rem1
          else false
        | .movRR32 idx _ =>
          if !isSfiScratchReg idx then false
          else
            match peekMem2nd idx rem1 with
            | some (_, len2) =>
              if decide (32 < off + len1 + len2) || (isLast && decide (off + len1 + len2 = 32)) then false
              else checkSfiMacroStream totalBytes bBase isLast fuel (off + len1 + len2) (rem1.drop len2)
            | none =>
              if isLast && decide (off + len1 = 32) then false
              else checkSfiMacroStream totalBytes bBase isLast fuel (off + len1) rem1
        | .aluImm32 op dst mask =>
          if op == .and && dst == .rax then
            match peekMaskedJmp2nd rem1 with
            | some len2 =>
              if (mask &&& 31#32) == 0#32 && natLtB mask.toNat totalBytes &&
                 !decide (32 < off + len1 + len2) then
                checkSfiMacroStream totalBytes bBase isLast fuel (off + len1 + len2) (rem1.drop len2)
              else false
            | none =>
              if isLast && decide (off + len1 = 32) then false
              else checkSfiMacroStream totalBytes bBase isLast fuel (off + len1) rem1
          else
            if isPureSfiOp (.aluImm32 op dst mask) && !(isLast && decide (off + len1 = 32)) then
              checkSfiMacroStream totalBytes bBase isLast fuel (off + len1) rem1
            else false
        | other =>
          if isPureSfiOp other && !(isLast && decide (off + len1 = 32)) then
            checkSfiMacroStream totalBytes bBase isLast fuel (off + len1) rem1
          else false

def checkSfiLeafBundles (totalBytes : Nat) : Nat → Nat → List UInt8 → Bool
  | _, base, [] => natEqB (base % 32) 0
  | 0, _, _ :: _ => false
  | fuel + 1, base, bs =>
    natEqB (base % 32) 0 &&
    natLeB 32 (lenTR bs) &&
    natLeB (base + 32) totalBytes &&
    checkSfiMacroStream totalBytes base (base + 32 == totalBytes) 32 0 (bs.take 32) &&
    checkSfiLeafBundles totalBytes fuel (base + 32) (bs.drop 32)

def checkSfiSubtree (totalBytes base endOff : Nat) : ByteCodeTree → Bool
  | .leaf bs =>
    let sz := lenTR bs
    natLtB base endOff &&
    natLeB endOff totalBytes &&
    natEqB (base + sz) endOff &&
    natEqB (sz % 32) 0 &&
    checkSfiLeafBundles totalBytes (sz / 32) base bs
  | .node lsz l r =>
    natEqB (lsz % 32) 0 &&
    natLeB (base + lsz) endOff &&
    checkSfiSubtree totalBytes base (base + lsz) l &&
    checkSfiSubtree totalBytes (base + lsz) endOff r

theorem checkSfiSubtree_node {totalBytes base lsz endOff : Nat} {l r : ByteCodeTree}
    (hmod : natEqB (lsz % 32) 0 = true) (hle : natLeB (base + lsz) endOff = true)
    (hl : checkSfiSubtree totalBytes base (base + lsz) l = true)
    (hr : checkSfiSubtree totalBytes (base + lsz) endOff r = true) :
    checkSfiSubtree totalBytes base endOff (.node lsz l r) = true := by
  dsimp [checkSfiSubtree]
  rw [hmod, hle, hl, hr]
  rfl

def checkSfiObject (totalBytes : Nat) (img : X64ObjImage) : Bool :=
  natLtB 0 totalBytes && natEqB (totalBytes % 32) 0 &&
  checkSfiSubtree totalBytes 0 totalBytes img.code

/-! ## Section 4C: Bundle-Coverage & Multi-Step Inductive Soundness Proof -/

def BundleValidAt (totalBytes : Nat) (code : ByteCodeTree) (bBase : Nat) : Prop :=
  ∃ bundle : List UInt8,
    bundle.length = 32 ∧
    (∀ i, i < 32 → code.getByte? (bBase + i) = listGet? bundle i) ∧
    checkSfiMacroStream totalBytes bBase (bBase + 32 == totalBytes) 32 0 bundle = true

def AllBundlesValid (totalBytes : Nat) (code : ByteCodeTree) : Prop :=
  0 < totalBytes ∧ totalBytes % 32 = 0 ∧
  ∀ bBase, bBase < totalBytes → bBase % 32 = 0 → BundleValidAt totalBytes code bBase

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

theorem checkSfiLeafBundles_spec (totalBytes : Nat) :
    ∀ (fuel base : Nat) (bs : List UInt8) (b : Nat),
      checkSfiLeafBundles totalBytes fuel base bs = true →
      base ≤ b → b < base + bs.length → b % 32 = 0 →
      ∃ bundle : List UInt8,
        bundle.length = 32 ∧
        (∀ i, i < 32 → listGet? bs ((b - base) + i) = listGet? bundle i) ∧
        checkSfiMacroStream totalBytes b (b + 32 == totalBytes) 32 0 bundle = true
  | _, base, [], b, _, hge, hlt, _ => by
    rw [List.length_nil, Nat.add_zero] at hlt
    exact False.elim (Nat.lt_irrefl b (Nat.lt_of_lt_of_le hlt hge))
  | 0, _, _ :: _, _, hchk, _, _, _ => nomatch hchk
  | fuel + 1, base, c :: cs, b, hchk, hge, hlt, hmod => by
    dsimp [checkSfiLeafBundles] at hchk
    have c1 := Bool.and_eq_true_iff.mp hchk
    have c2 := Bool.and_eq_true_iff.mp c1.1
    have c3 := Bool.and_eq_true_iff.mp c2.1
    have c4 := Bool.and_eq_true_iff.mp c3.1
    have hbase_mod : base % 32 = 0 := natEqB_true c4.1
    have hlen32 : 32 ≤ (c :: cs).length := by
      have ht := natLeB_true c4.2
      rw [lenTR_eq_length] at ht
      exact ht
    cases h_eq : decide (b = base) with
    | true =>
      have hb : b = base := of_decide_eq_true h_eq
      subst hb
      refine ⟨(c :: cs).take 32, List.length_take_of_le hlen32, ?_, c2.2⟩
      intro i hi
      rw [Nat.sub_self, Nat.zero_add, listGet?_take 32 (c :: cs) i hi]
    | false =>
      have hne : b ≠ base := of_decide_eq_false h_eq
      have hgt : base < b := Nat.lt_of_le_of_ne hge hne.symm
      have hb32 : base + 32 ≤ b := mod32_step_le hbase_mod hmod hgt
      have hlt_drop : b < (base + 32) + ((c :: cs).drop 32).length := by
        rw [List.length_drop, Nat.add_assoc, Nat.add_sub_of_le hlen32]
        exact hlt
      rcases checkSfiLeafBundles_spec totalBytes fuel (base + 32) ((c :: cs).drop 32) b
        c1.2 hb32 hlt_drop hmod with ⟨bundle, hblen, hbget, hbchk⟩
      refine ⟨bundle, hblen, ?_, hbchk⟩
      intro i hi
      rw [← hbget i hi, listGet?_drop 32 (c :: cs) ((b - (base + 32)) + i)]
      have hd : 32 + (b - (base + 32)) = b - base := by
        have h1 : (base + 32) + (b - (base + 32)) = b := Nat.add_sub_of_le hb32
        have h2 : base + (32 + (b - (base + 32))) = b := by rw [← Nat.add_assoc, h1]
        have h3 := congrArg (fun x => x - base) h2
        rw [Nat.add_sub_cancel_left] at h3
        exact h3
      rw [← Nat.add_assoc, hd]

theorem add_mod32_zero {a b : Nat} (ha : a % 32 = 0) (hb : b % 32 = 0) : (a + b) % 32 = 0 := by
  rw [Nat.add_mod, ha, hb]

theorem bnot_eq_true_imp_false {b : Bool} (h : (!b) = true) : b = false := by
  cases b with
  | false => rfl
  | true => nomatch h

theorem checkSfiSubtree_spec (totalBytes : Nat) :
    ∀ (t : ByteCodeTree) (base endOff b : Nat),
      base % 32 = 0 →
      checkSfiSubtree totalBytes base endOff t = true →
      base ≤ b → b < endOff → b % 32 = 0 →
      ∃ bundle : List UInt8,
        bundle.length = 32 ∧
        (∀ i, i < 32 → t.getByte? ((b - base) + i) = listGet? bundle i) ∧
        checkSfiMacroStream totalBytes b (b + 32 == totalBytes) 32 0 bundle = true
  | .leaf bs, base, endOff, b, _, hchk, hge, hlt, hmod => by
    dsimp [checkSfiSubtree] at hchk
    have c1 := Bool.and_eq_true_iff.mp hchk
    have c2 := Bool.and_eq_true_iff.mp c1.1
    have c3 := Bool.and_eq_true_iff.mp c2.1
    have hend : base + bs.length = endOff := by
      have ht := natEqB_true c3.2
      rw [lenTR_eq_length] at ht
      exact ht
    rw [← hend] at hlt
    have hchk_l : checkSfiLeafBundles totalBytes (bs.length / 32) base bs = true := by
      have ht := c1.2
      rw [lenTR_eq_length] at ht
      exact ht
    exact checkSfiLeafBundles_spec totalBytes (bs.length / 32) base bs b hchk_l hge hlt hmod
  | .node lsz l r, base, endOff, b, hbase_mod, hchk, hge, hlt, hmod => by
    dsimp [checkSfiSubtree] at hchk
    have c1 := Bool.and_eq_true_iff.mp hchk
    have c2 := Bool.and_eq_true_iff.mp c1.1
    have c3 := Bool.and_eq_true_iff.mp c2.1
    have hlsz_mod : lsz % 32 = 0 := natEqB_true c3.1
    have hsplit_mod : (base + lsz) % 32 = 0 := add_mod32_zero hbase_mod hlsz_mod
    cases hleft : decide (b < base + lsz) with
    | true =>
      have hbl : b < base + lsz := of_decide_eq_true hleft
      have hb32 : b + 32 ≤ base + lsz := mod32_step_le hmod hsplit_mod hbl
      rcases checkSfiSubtree_spec totalBytes l base (base + lsz) b hbase_mod c2.2 hge hbl hmod with
        ⟨bundle, hblen, hbget, hbchk⟩
      refine ⟨bundle, hblen, ?_, hbchk⟩
      intro i hi
      have hidx_lt : (b - base) + i < lsz := by
        have hb_eq : base + (b - base) = b := Nat.add_sub_of_le hge
        have hsum_lt : base + ((b - base) + i) < base + lsz := by
          rw [← Nat.add_assoc, hb_eq]
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi b) hb32
        exact Nat.lt_of_add_lt_add_left hsum_lt
      dsimp [ByteCodeTree.getByte?]
      simp only [hidx_lt, ite_true]
      exact hbget i hi
    | false =>
      have hbge : base + lsz ≤ b := Nat.not_lt.mp (of_decide_eq_false hleft)
      rcases checkSfiSubtree_spec totalBytes r (base + lsz) endOff b hsplit_mod c1.2 hbge hlt hmod with
        ⟨bundle, hblen, hbget, hbchk⟩
      refine ⟨bundle, hblen, ?_, hbchk⟩
      intro i hi
      have hidx_ge : lsz ≤ (b - base) + i := by
        have h1 : lsz ≤ b - base := Nat.le_sub_of_add_le' hbge
        exact Nat.le_trans h1 (Nat.le_add_right _ i)
      have hnlt : ¬ ((b - base) + i < lsz) := Nat.not_lt_of_ge hidx_ge
      dsimp [ByteCodeTree.getByte?]
      simp only [hnlt, ite_false]
      have hsub_eq : ((b - base) + i) - lsz = (b - (base + lsz)) + i := by
        have h1 : lsz ≤ b - base := Nat.le_sub_of_add_le' hbge
        rw [Nat.sub_add_comm h1, Nat.sub_sub]
      rw [hsub_eq]
      exact hbget i hi

theorem checkSfiObject_bundlesValid {totalBytes : Nat} {img : X64ObjImage}
    (hok : checkSfiObject totalBytes img = true) :
    AllBundlesValid totalBytes img.code := by
  dsimp [checkSfiObject] at hok
  have c1 := Bool.and_eq_true_iff.mp hok
  have c2 := Bool.and_eq_true_iff.mp c1.1
  have hpos : 0 < totalBytes := natLtB_true c2.1
  have hmod : totalBytes % 32 = 0 := natEqB_true c2.2
  refine ⟨hpos, hmod, ?_⟩
  intro b hb hbmod
  rcases checkSfiSubtree_spec totalBytes img.code 0 totalBytes b rfl c1.2 (Nat.zero_le b) hb hbmod with
    ⟨bundle, hblen, hbget, hbchk⟩
  refine ⟨bundle, hblen, ?_, hbchk⟩
  intro i hi
  have h0 : b - 0 = b := Nat.sub_zero b
  rw [← h0]
  exact hbget i hi

def SfiCoreSafe (r14Base : BitVec 64) (initRegs : Reg → BitVec 64) (initMem : ByteMem)
    (s : X64State) : Prop :=
  s.fault = false ∧
  s.regs .r14 = r14Base ∧
  s.regs .rsp = initRegs .rsp ∧
  (∀ r, isHostProtectedReg r = true → s.regs r = initRegs r) ∧
  (∀ a, OutsideSandboxArena r14Base a → s.mem a = initMem a)

inductive SfiPhase (totalBytes : Nat) (img : X64ObjImage) (s : X64State) : Prop where
  | atMacro (bBase fuel off : Nat) (rem : List UInt8)
      (hb_lt : bBase < totalBytes)
      (hb_mod : bBase % 32 = 0)
      (hb_le : bBase + 32 ≤ totalBytes)
      (hoff_lt : off < 32)
      (hrip : s.rip = bBase + off)
      (hlen : off + rem.length = 32)
      (hbytes : ∀ i, i < rem.length → img.code.getByte? ((bBase + off) + i) = listGet? rem i)
      (hchk : checkSfiMacroStream totalBytes bBase (bBase + 32 == totalBytes) fuel off rem = true)
  | pendingMem (bBase fuel nextOff : Nat) (idx : Reg) (ins2 : X64Instr) (pfx2 rem2 : List UInt8)
      (hidx_lt : (s.regs idx).toNat < 4294967296)
      (hb_lt : bBase < totalBytes)
      (hb_mod : bBase % 32 = 0)
      (hb_le : bBase + 32 ≤ totalBytes)
      (hrip_lt : s.rip < totalBytes)
      (hmem2 : isSandboxedMem2nd idx ins2 = true)
      (hdec2 : decodeX64 pfx2 = .ok ins2 pfx2.length)
      (hwin2 : ∀ i, i < pfx2.length → img.code.getByte? (s.rip + i) = listGet? pfx2 i)
      (hnrip : s.rip + pfx2.length = bBase + nextOff)
      (hnlen : nextOff + rem2.length = 32)
      (hnlast : ((bBase + 32 == totalBytes) && decide (nextOff = 32)) = false)
      (hnbytes : ∀ i, i < rem2.length → img.code.getByte? ((bBase + nextOff) + i) = listGet? rem2 i)
      (hnchk : checkSfiMacroStream totalBytes bBase (bBase + 32 == totalBytes) fuel nextOff rem2 = true)
  | pendingJmp (pfx2 : List UInt8)
      (htgt_lt : (s.regs .rax).toNat < totalBytes)
      (htgt_mod : (s.regs .rax).toNat % 32 = 0)
      (hrip_lt : s.rip < totalBytes)
      (hdec2 : decodeX64 pfx2 = .ok (.jmpReg .rax) pfx2.length)
      (hwin2 : ∀ i, i < pfx2.length → img.code.getByte? (s.rip + i) = listGet? pfx2 i)

def SfiMachineInv (totalBytes : Nat) (img : X64ObjImage)
    (r14Base : BitVec 64) (initRegs : Reg → BitVec 64) (initMem : ByteMem)
    (s : X64State) : Prop :=
  SfiCoreSafe r14Base initRegs initMem s ∧
  (s.halted = false → SfiPhase totalBytes img s)

theorem sfiPhase_rip_lt {totalBytes : Nat} {img : X64ObjImage} {s : X64State}
    (hp : SfiPhase totalBytes img s) : s.rip < totalBytes := by
  cases hp with
  | atMacro bBase _ off _ _ _ hb_le hoff_lt hrip _ _ _ =>
    rw [hrip]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff_lt bBase) hb_le
  | pendingMem _ _ _ _ _ _ _ _ _ _ _ hrip_lt _ _ _ _ _ _ _ _ => exact hrip_lt
  | pendingJmp _ _ _ hrip_lt _ _ => exact hrip_lt

theorem enterBundleStart {totalBytes : Nat} {img : X64ObjImage} {s' : X64State} {tgt : Nat}
    (hall : AllBundlesValid totalBytes img.code)
    (htgt_lt : tgt < totalBytes) (htgt_mod : tgt % 32 = 0)
    (hrip : s'.rip = tgt) :
    SfiPhase totalBytes img s' := by
  rcases hall with ⟨_, htot_mod, hget_b⟩
  rcases hget_b tgt htgt_lt htgt_mod with ⟨bundle, hblen, hbget, hbchk⟩
  have hb32 : tgt + 32 ≤ totalBytes := mod32_step_le htgt_mod htot_mod htgt_lt
  apply SfiPhase.atMacro tgt 32 0 bundle htgt_lt htgt_mod hb32 (by decide)
  · rw [Nat.add_zero]; exact hrip
  · rw [Nat.zero_add]; exact hblen
  · intro i hi; rw [Nat.add_zero]; exact hbget i (by rw [hblen] at hi; exact hi)
  · exact hbchk

theorem enterNextMacro {totalBytes : Nat} {img : X64ObjImage} {s' : X64State}
    {bBase fuel nextOff : Nat} {rem2 : List UInt8}
    (hall : AllBundlesValid totalBytes img.code)
    (hb_lt : bBase < totalBytes) (hb_mod : bBase % 32 = 0) (hb_le : bBase + 32 ≤ totalBytes)
    (hrip : s'.rip = bBase + nextOff)
    (hnlen : nextOff + rem2.length = 32)
    (hnlast : ((bBase + 32 == totalBytes) && decide (nextOff = 32)) = false)
    (hnbytes : ∀ i, i < rem2.length → img.code.getByte? ((bBase + nextOff) + i) = listGet? rem2 i)
    (hnchk : checkSfiMacroStream totalBytes bBase (bBase + 32 == totalBytes) fuel nextOff rem2 = true) :
    SfiPhase totalBytes img s' := by
  cases rem2 with
  | cons r0 rs =>
    have hpos : 0 < (r0 :: rs).length := Nat.zero_lt_succ rs.length
    have hoff_lt : nextOff < 32 := by
      rw [← hnlen]
      exact Nat.lt_add_of_pos_right hpos
    exact SfiPhase.atMacro bBase fuel nextOff (r0 :: rs) hb_lt hb_mod hb_le hoff_lt hrip hnlen hnbytes hnchk
  | nil =>
    rw [List.length_nil, Nat.add_zero] at hnlen
    subst hnlen
    have hnot_eq : bBase + 32 ≠ totalBytes := by
      intro heq
      rw [decide_eq_true (rfl : 32 = 32), Bool.and_true] at hnlast
      have ht : (bBase + 32 == totalBytes) = true := decide_eq_true heq
      rw [ht] at hnlast; nomatch hnlast
    have hnext_lt : bBase + 32 < totalBytes := Nat.lt_of_le_of_ne hb_le hnot_eq
    have hnext_mod : (bBase + 32) % 32 = 0 := add_mod32_zero hb_mod rfl
    exact enterBundleStart hall hnext_lt hnext_mod hrip

theorem coreSafe_upd_scratch {r14Base : BitVec 64} {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    {s : X64State} {dst : Reg} {v : BitVec 64} {fl' : RFlags} {rip' : Nat}
    (hcore : SfiCoreSafe r14Base initRegs initMem s)
    (hscr : isSfiScratchReg dst = true) :
    SfiCoreSafe r14Base initRegs initMem { s with rip := rip', regs := regUpd s.regs dst v, flags := fl' } := by
  rcases hcore with ⟨hf, hr14, hrsp, hprot, hmem⟩
  dsimp [SfiCoreSafe]
  refine ⟨hf, ?_, ?_, ?_, hmem⟩
  · rw [regUpd_ne s.regs (sfiScratch_ne_r14 hscr) v]; exact hr14
  · rw [regUpd_ne s.regs (sfiScratch_ne_rsp hscr) v]; exact hrsp
  · intro r hp
    rw [regUpd_ne s.regs (sfiScratch_ne_protected hscr hp) v]
    exact hprot r hp

theorem step_pureSfiOp_safe {r14Base : BitVec 64} {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    {img : X64ObjImage} {s : X64State} {ins : X64Instr} {len : Nat} (nd0 : UndefFlags)
    (hnh : s.halted = false)
    (hcore : SfiCoreSafe r14Base initRegs initMem s)
    (hdec : decodeX64 (fetchWindow16 img.code s.rip) = .ok ins len)
    (hpure : isPureSfiOp ins = true) :
    let s' := stepX64 img nd0 s
    s'.halted = false ∧ s'.rip = s.rip + len ∧
    SfiCoreSafe r14Base initRegs initMem s' := by
  have hnf := hcore.1
  cases ins with
  | nop | endbr64 | vzeroupper =>
    have hst : stepX64 img nd0 s = { s with rip := s.rip + len } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]
    exact ⟨hnh, rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2⟩
  | movRR64 dst src =>
    have hst : stepX64 img nd0 s = { s with rip := s.rip + len, regs := regUpd s.regs dst (s.regs src) } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]
    exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hpure⟩
  | movRR32 dst src =>
    have hst : stepX64 img nd0 s =
        { s with rip := s.rip + len, regs := regUpd s.regs dst ((BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64) } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]
    exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hpure⟩
  | movImm64 dst imm =>
    have hst : stepX64 img nd0 s = { s with rip := s.rip + len, regs := regUpd s.regs dst imm } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]
    exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hpure⟩
  | movImm32 dst imm32 =>
    have hst : stepX64 img nd0 s = { s with rip := s.rip + len, regs := regUpd s.regs dst (imm32.zeroExtend 64) } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]
    exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hpure⟩
  | lea64 dst addr =>
    have hst : stepX64 img nd0 s = { s with rip := s.rip + len, regs := regUpd s.regs dst (evalAddr s (s.rip + len) addr) } := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]
    exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hpure⟩
  | shiftImm64 op dst cnt =>
    have hst : stepX64 img nd0 s =
        (let (res, fl) := evalShift64 op (s.regs dst) cnt s.flags nd0
         { s with rip := s.rip + len, regs := regUpd s.regs dst res, flags := fl }) := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]; dsimp only
    exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hpure⟩
  | imulRR64 dst src =>
    have hst : stepX64 img nd0 s =
        (let (res, fl) := evalImul64 (s.regs dst) (s.regs src) nd0
         { s with rip := s.rip + len, regs := regUpd s.regs dst res, flags := fl }) := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]; dsimp only
    exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hpure⟩
  | bsf64 dst src =>
    have hst : stepX64 img nd0 s =
        (let (res, fl) := evalBsf64 (s.regs dst) (s.regs src) nd0
         { s with rip := s.rip + len, regs := regUpd s.regs dst res, flags := fl }) := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]; dsimp only
    exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hpure⟩
  | tzcnt64 dst src =>
    have hst : stepX64 img nd0 s =
        (let (res, fl) := evalTzcnt64 (s.regs src) nd0
         { s with rip := s.rip + len, regs := regUpd s.regs dst res, flags := fl }) := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]; dsimp only
    exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hpure⟩
  | aluRR64 op dst src =>
    have hst : stepX64 img nd0 s =
        (let (res, fl) := evalAluFlags64 op (s.regs dst) (s.regs src) nd0
         { s with rip := s.rip + len, regs := if aluWritesDst op then regUpd s.regs dst res else s.regs, flags := fl }) := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]; dsimp only
    dsimp [isPureSfiOp] at hpure
    revert hpure
    cases aluWritesDst op with
    | false => intro _; exact ⟨hnh, rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2⟩
    | true => intro hp; exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hp⟩
  | aluImm64 op dst imm =>
    have hst : stepX64 img nd0 s =
        (let (res, fl) := evalAluFlags64 op (s.regs dst) imm nd0
         { s with rip := s.rip + len, regs := if aluWritesDst op then regUpd s.regs dst res else s.regs, flags := fl }) := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]; dsimp only
    dsimp [isPureSfiOp] at hpure
    revert hpure
    cases aluWritesDst op with
    | false => intro _; exact ⟨hnh, rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2⟩
    | true => intro hp; exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hp⟩
  | aluRR32 op dst src =>
    have hst : stepX64 img nd0 s =
        (let a32 := BitVec.extractLsb' 0 32 (s.regs dst)
         let b32 := BitVec.extractLsb' 0 32 (s.regs src)
         let (res, fl) := evalAluFlags32 op a32 b32 nd0
         { s with rip := s.rip + len, regs := if aluWritesDst op then regUpd s.regs dst res else s.regs, flags := fl }) := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]; dsimp only
    dsimp [isPureSfiOp] at hpure
    revert hpure
    cases aluWritesDst op with
    | false => intro _; exact ⟨hnh, rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2⟩
    | true => intro hp; exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hp⟩
  | aluImm32 op dst imm32 =>
    have hst : stepX64 img nd0 s =
        (let a32 := BitVec.extractLsb' 0 32 (s.regs dst)
         let (res, fl) := evalAluFlags32 op a32 imm32 nd0
         { s with rip := s.rip + len, regs := if aluWritesDst op then regUpd s.regs dst res else s.regs, flags := fl }) := by
      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hdec]
    dsimp only; rw [hst]; dsimp only
    dsimp [isPureSfiOp] at hpure
    revert hpure
    cases aluWritesDst op with
    | false => intro _; exact ⟨hnh, rfl, hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2⟩
    | true => intro hp; exact ⟨hnh, rfl, coreSafe_upd_scratch hcore hp⟩
  | load64 _ _ | store64 _ _ | load32Zext _ _ | load32Sext _ _
  | xchg64 _ _ | xchg32 _ _ | xchg16 _ _
  | lockAdd64 _ _ | lockAddImm64 _ _ | lockCmpxchg64 _ _
  | push64 _ | pop64 _ | leave64
  | jmpRel _ | jccRel _ _ | jmpReg _ | ret | int3 | ud2 =>
    dsimp [isPureSfiOp] at hpure; nomatch hpure

theorem peekMem2nd_spec {idx : Reg} {rem1 : List UInt8} {ins2 : X64Instr} {len2 : Nat}
    (h : peekMem2nd idx rem1 = some (ins2, len2)) :
    isSandboxedMem2nd idx ins2 = true ∧
    0 < len2 ∧ len2 ≤ rem1.length ∧
    decodeX64 (rem1.take len2) = .ok ins2 (rem1.take len2).length ∧
    (rem1.take len2).length = len2 := by
  dsimp [peekMem2nd] at h
  revert h
  cases decodeX64 rem1 with
  | fault _ => intro h; nomatch h
  | ok i2 l2 =>
    dsimp
    let pfx2 := rem1.take l2
    cases hc : (((isSandboxedMem2nd idx i2 && !(l2 == 0)) && !decide (lenTR rem1 < l2)) &&
                (decodeX64 pfx2 == .ok i2 pfx2.length)) with
    | false => intro h; nomatch h
    | true =>
      intro h; injection h with hp; injection hp with hi hl; subst hi hl
      have c1 := Bool.and_eq_true_iff.mp hc
      have c2 := Bool.and_eq_true_iff.mp c1.1
      have c3 := Bool.and_eq_true_iff.mp c2.1
      have hl_pos : 0 < l2 := by
        cases l2 with
        | zero => nomatch c3.2
        | succ k => exact Nat.zero_lt_succ k
      have hl_le : l2 ≤ rem1.length := by
        cases hlt : decide (lenTR rem1 < l2) with
        | false =>
          have hn := Nat.not_lt.mp (of_decide_eq_false hlt)
          rw [lenTR_eq_length] at hn
          exact hn
        | true => rw [hlt] at c2; nomatch c2.2
      exact ⟨c3.1, hl_pos, hl_le, of_decide_eq_true c1.2, List.length_take_of_le hl_le⟩

theorem peekMaskedJmp2nd_spec {rem1 : List UInt8} {len2 : Nat}
    (h : peekMaskedJmp2nd rem1 = some len2) :
    0 < len2 ∧ len2 ≤ rem1.length ∧
    decodeX64 (rem1.take len2) = .ok (.jmpReg .rax) (rem1.take len2).length ∧
    (rem1.take len2).length = len2 := by
  dsimp [peekMaskedJmp2nd] at h
  revert h
  cases hdec : decodeX64 rem1 with
  | fault _ => intro h; nomatch h
  | ok i2 l2 =>
    cases i2 with
    | jmpReg r =>
      cases r with
      | rax =>
        dsimp
        let pfx2 := rem1.take l2
        cases hc : ((!(l2 == 0) && !decide (lenTR rem1 < l2)) &&
                    (decodeX64 pfx2 == .ok (.jmpReg .rax) pfx2.length)) with
        | false => intro h; nomatch h
        | true =>
          intro h; injection h with hl; subst hl
          have c1 := Bool.and_eq_true_iff.mp hc
          have c2 := Bool.and_eq_true_iff.mp c1.1
          have hl_pos : 0 < l2 := by
            cases l2 with
            | zero => nomatch c2.1
            | succ k => exact Nat.zero_lt_succ k
          have hl_le : l2 ≤ rem1.length := by
            cases hlt : decide (lenTR rem1 < l2) with
            | false =>
              have hn := Nat.not_lt.mp (of_decide_eq_false hlt)
              rw [lenTR_eq_length] at hn
              exact hn
            | true => rw [hlt] at c2; nomatch c2.2
          exact ⟨hl_pos, hl_le, of_decide_eq_true c1.2, List.length_take_of_le hl_le⟩
      | _ => intro h; nomatch h
    | _ => intro h; nomatch h

theorem isSandboxedMem2nd_spec {idx : Reg} {ins2 : X64Instr}
    (h : isSandboxedMem2nd idx ins2 = true) :
    (∃ disp src, disp.toNat ≤ 65528 ∧ ins2 = .store64 (.baseDisp .r14 (some (idx, 1)) disp) src) ∨
    (∃ dst disp, isSfiScratchReg dst = true ∧ disp.toNat ≤ 65528 ∧
       ins2 = .load64 dst (.baseDisp .r14 (some (idx, 1)) disp)) := by
  cases ins2 with
  | store64 addr src =>
    cases addr with
    | ripRel _ => nomatch h
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch h
        | some pair =>
          rcases pair with ⟨idx', sc⟩
          cases sc with
          | zero => nomatch h
          | succ sc1 =>
            cases sc1 with
            | succ _ => nomatch h
            | zero =>
              dsimp [isSandboxedMem2nd] at h
              have hc := Bool.and_eq_true_iff.mp h
              have heq : idx' = idx := of_decide_eq_true hc.1
              subst heq
              exact Or.inl ⟨disp, src, natLeB_true hc.2, rfl⟩
      | _ => nomatch h
  | load64 dst addr =>
    cases addr with
    | ripRel _ => nomatch h
    | baseDisp b io disp =>
      cases b with
      | r14 =>
        cases io with
        | none => nomatch h
        | some pair =>
          rcases pair with ⟨idx', sc⟩
          cases sc with
          | zero => nomatch h
          | succ sc1 =>
            cases sc1 with
            | succ _ => nomatch h
            | zero =>
              dsimp [isSandboxedMem2nd] at h
              have hc1 := Bool.and_eq_true_iff.mp h
              have hc2 := Bool.and_eq_true_iff.mp hc1.1
              have heq : idx' = idx := of_decide_eq_true hc2.2
              subst heq
              exact Or.inr ⟨dst, disp, hc2.1, natLeB_true hc1.2, rfl⟩
      | _ => nomatch h
  | _ => nomatch h

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
    have ht := congrArg BitVec.toNat heq
    rw [BitVec.toNat_and] at ht
    exact ht
  rw [hm0, Nat.and_zero]

/-- Single-step inductive preservation of `SfiMachineInv` across ALL instructions & phases. -/
theorem step_preserves_sfiInv {totalBytes : Nat} {img : X64ObjImage}
    {r14Base : BitVec 64} {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    (hall : AllBundlesValid totalBytes img.code)
    (nd0 : UndefFlags) {s : X64State}
    (hinv : SfiMachineInv totalBytes img r14Base initRegs initMem s) :
    SfiMachineInv totalBytes img r14Base initRegs initMem (stepX64 img nd0 s) := by
  rcases hinv with ⟨hcore, hphase_fn⟩
  have hnf : s.fault = false := hcore.1
  cases hnh : s.halted with
  | true =>
    have hst : stepX64 img nd0 s = s := by dsimp [stepX64]; rw [hnh]; rfl
    rw [hst]
    exact ⟨hcore, fun hh => by rw [hnh] at hh; nomatch hh⟩
  | false =>
    have hphase := hphase_fn hnh
    cases hphase with
    | pendingJmp pfx2 htgt_lt htgt_mod _ hdec2 hwin2 =>
      have hlen_le16 : pfx2.length ≤ 16 :=
        Nat.le_trans (decodeX64_len_bounds hdec2).2.1 (by decide)
      rcases fetchBytes_prefix pfx2 img.code 16 s.rip hlen_le16 hwin2 with ⟨sfx, hsfx⟩
      have hwin_dec : decodeX64 (fetchWindow16 img.code s.rip) = .ok (.jmpReg .rax) pfx2.length := by
        dsimp [fetchWindow16]; rw [hsfx]; exact decodeX64_prefix_invariant hdec2 sfx
      have hst : stepX64 img nd0 s = { s with rip := (s.regs .rax).toNat } := by
        dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hwin_dec]
      rw [hst]
      refine ⟨⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2⟩, ?_⟩
      intro _
      exact enterBundleStart hall htgt_lt htgt_mod rfl
    | pendingMem bBase fuel nextOff idx ins2 pfx2 rem2 hidx_lt hb_lt hb_mod hb_le _
        hmem2 hdec2 hwin2 hnrip hnlen hnlast hnbytes hnchk =>
      have hlen_le16 : pfx2.length ≤ 16 :=
        Nat.le_trans (decodeX64_len_bounds hdec2).2.1 (by decide)
      rcases fetchBytes_prefix pfx2 img.code 16 s.rip hlen_le16 hwin2 with ⟨sfx, hsfx⟩
      have hwin_dec : decodeX64 (fetchWindow16 img.code s.rip) = .ok ins2 pfx2.length := by
        dsimp [fetchWindow16]; rw [hsfx]; exact decodeX64_prefix_invariant hdec2 sfx
      rcases isSandboxedMem2nd_spec hmem2 with ⟨disp, src, hdisp, hins_eq⟩ | ⟨dst, disp, hscr, hdisp, hins_eq⟩
      · subst hins_eq
        have hst : stepX64 img nd0 s =
            { s with rip := s.rip + pfx2.length,
                     mem := writeMem64 s.mem (s.regs .r14 + s.regs idx * BitVec.ofNat 64 1 + disp) (s.regs src) } := by
          dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hwin_dec]; rfl
        rw [hst]
        refine ⟨⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, ?_⟩, ?_⟩
        · intro a hout
          dsimp only
          rw [hcore.2.1, sfi_store_preserves_outside_arena s.mem r14Base (s.regs idx) disp (s.regs src) a hidx_lt hdisp hout]
          exact hcore.2.2.2.2 a hout
        · intro _
          exact enterNextMacro hall hb_lt hb_mod hb_le hnrip hnlen hnlast hnbytes hnchk
      · subst hins_eq
        have hst : stepX64 img nd0 s =
            { s with rip := s.rip + pfx2.length,
                     regs := regUpd s.regs dst (readMem64 s.mem (s.regs .r14 + s.regs idx * BitVec.ofNat 64 1 + disp)) } := by
          dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hwin_dec]; rfl
        rw [hst]
        refine ⟨coreSafe_upd_scratch hcore hscr, ?_⟩
        intro _
        exact enterNextMacro hall hb_lt hb_mod hb_le hnrip hnlen hnlast hnbytes hnchk
    | atMacro bBase fuel off rem hb_lt hb_mod hb_le hoff_lt hrip hlen hbytes hchk =>
      cases rem with
      | nil =>
        rw [List.length_nil, Nat.add_zero] at hlen
        subst hlen
        exact False.elim (Nat.lt_irrefl 32 hoff_lt)
      | cons b0 bs =>
        cases fuel with
        | zero => nomatch hchk
        | succ fuel' =>
          dsimp [checkSfiMacroStream] at hchk
          revert hchk
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
                | false =>
                  have hn := Nat.not_lt.mp (of_decide_eq_false hd)
                  rw [lenTR_eq_length] at hn
                  exact hn
                | true => rw [hd] at hb3; nomatch hb3.2
              have hpfx1_len : pfx1.length = len1 := List.length_take_of_le hlen1_le_rem
              have hpfx1_dec : decodeX64 pfx1 = .ok ins1 pfx1.length := by
                cases heq : (decodeX64 pfx1 == .ok ins1 pfx1.length) with
                | true => exact of_decide_eq_true heq
                | false =>
                  have hf := hb1.2; dsimp [bne] at hf; rw [heq] at hf; nomatch hf
              have hpfx1_win : ∀ i, i < pfx1.length → img.code.getByte? (s.rip + i) = listGet? pfx1 i := by
                intro i hi
                have hi_len1 : i < len1 := by rw [← hpfx1_len]; exact hi
                have hi_rem : i < (b0 :: bs).length := Nat.lt_of_lt_of_le hi_len1 hlen1_le_rem
                rw [hrip, hbytes i hi_rem, ← listGet?_take len1 (b0 :: bs) i hi_len1]
              have hlen1_le16 : pfx1.length ≤ 16 :=
                Nat.le_trans (decodeX64_len_bounds hpfx1_dec).2.1 (by decide)
              rcases fetchBytes_prefix pfx1 img.code 16 s.rip hlen1_le16 hpfx1_win with ⟨sfx1, hsfx1⟩
              have hwin1_dec : decodeX64 (fetchWindow16 img.code s.rip) = .ok ins1 len1 := by
                dsimp [fetchWindow16]; rw [hsfx1, ← hpfx1_len]
                exact decodeX64_prefix_invariant hpfx1_dec sfx1
              have hrem1_len : (off + len1) + rem1.length = 32 := by
                dsimp [rem1]
                rw [List.length_drop, Nat.add_assoc, Nat.add_sub_of_le hlen1_le_rem]
                exact hlen
              have hrem1_bytes : ∀ i, i < rem1.length →
                  img.code.getByte? ((bBase + (off + len1)) + i) = listGet? rem1 i := by
                intro i hi
                dsimp [rem1] at hi ⊢
                rw [listGet?_drop len1 (b0 :: bs) i]
                have hi_tot : len1 + i < (b0 :: bs).length := by
                  rw [List.length_drop] at hi
                  exact Nat.add_lt_of_lt_sub' hi
                rw [← Nat.add_assoc bBase off len1, Nat.add_assoc (bBase + off) len1 i]
                exact hbytes (len1 + i) hi_tot
              -- Helper for any 1-insn pure fallthrough arm:
              have finishPure :
                  isPureSfiOp ins1 = true →
                  ((bBase + 32 == totalBytes) && decide (off + len1 = 32)) = false →
                  checkSfiMacroStream totalBytes bBase (bBase + 32 == totalBytes) fuel' (off + len1) rem1 = true →
                  SfiMachineInv totalBytes img r14Base initRegs initMem (stepX64 img nd0 s) := by
                intro hpure hnlast1 hchk1
                rcases step_pureSfiOp_safe nd0 hnh hcore hwin1_dec hpure with ⟨_, hrip1, hcore1⟩
                refine ⟨hcore1, fun _ => ?_⟩
                have hrip1' : (stepX64 img nd0 s).rip = bBase + (off + len1) := by
                  rw [hrip1, hrip, Nat.add_assoc]
                exact enterNextMacro hall hb_lt hb_mod hb_le hrip1' hrem1_len hnlast1 hrem1_bytes hchk1
              -- Dispatch over the 6 macro-instruction cases of `ins1`!
              cases ins1 with
              | ret =>
                intro _
                have hst : stepX64 img nd0 s = { s with halted := true } := by
                  dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hwin1_dec]
                rw [hst]
                exact ⟨⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2⟩, fun hh => nomatch hh⟩
              | jmpRel rel =>
                dsimp
                cases hok_j : sfiJmpTargetOk totalBytes bBase off len1 rel with
                | false => intro h; nomatch h
                | true =>
                  intro _
                  dsimp [sfiJmpTargetOk] at hok_j
                  have cj := Bool.and_eq_true_iff.mp hok_j
                  have hst : stepX64 img nd0 s = { s with rip := (BitVec.ofNat 64 (s.rip + len1) + rel).toNat } := by
                    dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hwin1_dec]
                  rw [hst]
                  refine ⟨⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2⟩, fun _ => ?_⟩
                  have hrip_j : (BitVec.ofNat 64 (s.rip + len1) + rel).toNat =
                      sfiJmpTarget bBase off len1 rel := by
                    dsimp [sfiJmpTarget]; rw [hrip]
                  exact enterBundleStart hall (natLtB_true cj.1) (natEqB_true cj.2) hrip_j
              | jccRel cc rel =>
                dsimp
                cases hok_jc : (sfiJmpTargetOk totalBytes bBase off len1 rel &&
                                !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                | false => intro h; nomatch h
                | true =>
                  dsimp
                  intro hchk_next
                  have cj1 := Bool.and_eq_true_iff.mp hok_jc
                  have cj2 := Bool.and_eq_true_iff.mp (by dsimp [sfiJmpTargetOk] at cj1; exact cj1.1)
                  have hnlast1 : ((bBase + 32 == totalBytes) && decide (off + len1 = 32)) = false :=
                    bnot_eq_true_imp_false cj1.2
                  cases hcond : evalCond cc s.flags with
                  | true =>
                    have hst : stepX64 img nd0 s = { s with rip := (BitVec.ofNat 64 (s.rip + len1) + rel).toNat } := by
                      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hwin1_dec]; dsimp; rw [hcond]; rfl
                    rw [hst]
                    refine ⟨⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2⟩, fun _ => ?_⟩
                    have hrip_j : (BitVec.ofNat 64 (s.rip + len1) + rel).toNat =
                        sfiJmpTarget bBase off len1 rel := by
                      dsimp [sfiJmpTarget]; rw [hrip]
                    exact enterBundleStart hall (natLtB_true cj2.1) (natEqB_true cj2.2) hrip_j
                  | false =>
                    have hst : stepX64 img nd0 s = { s with rip := s.rip + len1 } := by
                      dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hwin1_dec]; dsimp; rw [hcond]; rfl
                    rw [hst]
                    refine ⟨⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2.1, hcore.2.2.2.2⟩, fun _ => ?_⟩
                    have hrip_f : s.rip + len1 = bBase + (off + len1) := by rw [hrip, Nat.add_assoc]
                    exact enterNextMacro hall hb_lt hb_mod hb_le hrip_f hrem1_len hnlast1 hrem1_bytes hchk_next
              | movRR32 idx src =>
                dsimp
                cases hscr : isSfiScratchReg idx with
                | false => intro h; nomatch h
                | true =>
                  dsimp
                  cases hp2 : peekMem2nd idx rem1 with
                  | none =>
                    dsimp
                    cases hlast1 : ((bBase + 32 == totalBytes) && decide (off + len1 = 32)) with
                    | true => intro h; nomatch h
                    | false =>
                      intro hchk_next
                      exact finishPure hscr hlast1 hchk_next
                  | some pair2 =>
                    rcases pair2 with ⟨ins2, len2⟩
                    dsimp
                    cases hbad2 : (decide (32 < off + len1 + len2) ||
                                   ((bBase + 32 == totalBytes) && decide (off + len1 + len2 = 32))) with
                    | true => intro h; nomatch h
                    | false =>
                      intro hchk2
                      rcases peekMem2nd_spec hp2 with ⟨hmem2, hlen2_pos, hlen2_le, hdec2, hpfx2_len⟩
                      have hb2_pair := Bool.or_eq_false_iff.mp hbad2
                      have hst : stepX64 img nd0 s =
                          { s with rip := s.rip + len1,
                                   regs := regUpd s.regs idx ((BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64) } := by
                        dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hwin1_dec]
                      rw [hst]
                      refine ⟨coreSafe_upd_scratch hcore hscr, fun _ => ?_⟩
                      have hidx_val : (regUpd s.regs idx ((BitVec.extractLsb' 0 32 (s.regs src)).zeroExtend 64) idx).toNat < 4294967296 := by
                        rw [regUpd_eq, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
                        exact (BitVec.extractLsb' 0 32 (s.regs src)).isLt
                      have hoff1_lt32 : off + len1 < 32 := by
                        have hle32 : off + len1 + len2 ≤ 32 := Nat.not_lt.mp (of_decide_eq_false hb2_pair.1)
                        exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hlen2_pos) hle32
                      have hrip1_lt : s.rip + len1 < totalBytes := by
                        rw [hrip, Nat.add_assoc]
                        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff1_lt32 bBase) hb_le
                      have hwin2 : ∀ i, i < (rem1.take len2).length →
                          img.code.getByte? ((s.rip + len1) + i) = listGet? (rem1.take len2) i := by
                        intro i hi
                        rw [hpfx2_len] at hi
                        have hi_rem1 : i < rem1.length := Nat.lt_of_lt_of_le hi hlen2_le
                        rw [hrip, Nat.add_assoc bBase off len1, hrem1_bytes i hi_rem1,
                            ← listGet?_take len2 rem1 i hi]
                      have hnrip : (s.rip + len1) + (rem1.take len2).length = bBase + (off + len1 + len2) := by
                        rw [hpfx2_len, hrip, Nat.add_assoc bBase off len1, Nat.add_assoc bBase (off + len1) len2]
                      have hnlen2 : (off + len1 + len2) + (rem1.drop len2).length = 32 := by
                        rw [List.length_drop, Nat.add_assoc (off + len1) len2 _, Nat.add_sub_of_le hlen2_le]
                        exact hrem1_len
                      have hnbytes2 : ∀ i, i < (rem1.drop len2).length →
                          img.code.getByte? ((bBase + (off + len1 + len2)) + i) = listGet? (rem1.drop len2) i := by
                        intro i hi
                        rw [listGet?_drop len2 rem1 i]
                        rw [List.length_drop] at hi
                        have hi_r1 : len2 + i < rem1.length := Nat.add_lt_of_lt_sub' hi
                        rw [← Nat.add_assoc bBase (off + len1) len2, Nat.add_assoc (bBase + (off + len1)) len2 i]
                        exact hrem1_bytes (len2 + i) hi_r1
                      exact SfiPhase.pendingMem bBase fuel' (off + len1 + len2) idx ins2
                        (rem1.take len2) (rem1.drop len2) hidx_val hb_lt hb_mod hb_le hrip1_lt
                        hmem2 hdec2 hwin2 hnrip hnlen2 hb2_pair.2 hnbytes2 hchk2
              | aluImm32 op dst mask =>
                dsimp
                cases hand_rax : (op == .and && dst == .rax) with
                | true =>
                  dsimp
                  have h_ar := Bool.and_eq_true_iff.mp hand_rax
                  have hop : op = .and := of_decide_eq_true h_ar.1
                  have hdst : dst = .rax := of_decide_eq_true h_ar.2
                  subst hop hdst
                  cases hpj : peekMaskedJmp2nd rem1 with
                  | none =>
                    dsimp
                    cases hlast1 : ((bBase + 32 == totalBytes) && decide (off + len1 = 32)) with
                    | true => intro h; nomatch h
                    | false =>
                      intro hchk_next
                      exact finishPure rfl hlast1 hchk_next
                  | some len2 =>
                    dsimp
                    cases hok_m : (((mask &&& 31#32) == 0#32 && natLtB mask.toNat totalBytes) &&
                                   !decide (32 < off + len1 + len2)) with
                    | false => intro h; nomatch h
                    | true =>
                      intro _
                      rcases peekMaskedJmp2nd_spec hpj with ⟨hlen2_pos, hlen2_le, hdec2, hpfx2_len⟩
                      have cm1 := Bool.and_eq_true_iff.mp hok_m
                      have cm2 := Bool.and_eq_true_iff.mp cm1.1
                      have hle32 : off + len1 + len2 ≤ 32 := by
                        cases hd : decide (32 < off + len1 + len2) with
                        | false => exact Nat.not_lt.mp (of_decide_eq_false hd)
                        | true => rw [hd] at cm1; nomatch cm1.2
                      let a32 := BitVec.extractLsb' 0 32 (s.regs .rax)
                      have hst : stepX64 img nd0 s =
                          { s with rip := s.rip + len1,
                                   regs := regUpd s.regs .rax ((a32 &&& mask).zeroExtend 64),
                                   flags := (evalAluFlags32 .and a32 mask nd0).2 } := by
                        dsimp [stepX64]; rw [hnh, hnf]; dsimp; rw [hwin1_dec]; rfl
                      rw [hst]
                      refine ⟨coreSafe_upd_scratch hcore rfl, fun _ => ?_⟩
                      rcases masked32_target_valid cm2.1 (natLtB_true cm2.2) (a32 := a32) with ⟨ht_lt, ht_mod⟩
                      have hrax_lt : (regUpd s.regs .rax ((a32 &&& mask).zeroExtend 64) .rax).toNat < totalBytes := by
                        rw [regUpd_eq]; exact ht_lt
                      have hrax_mod : (regUpd s.regs .rax ((a32 &&& mask).zeroExtend 64) .rax).toNat % 32 = 0 := by
                        rw [regUpd_eq]; exact ht_mod
                      have hoff1_lt32 : off + len1 < 32 :=
                        Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hlen2_pos) hle32
                      have hrip1_lt : s.rip + len1 < totalBytes := by
                        rw [hrip, Nat.add_assoc]
                        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hoff1_lt32 bBase) hb_le
                      have hwin2 : ∀ i, i < (rem1.take len2).length →
                          img.code.getByte? ((s.rip + len1) + i) = listGet? (rem1.take len2) i := by
                        intro i hi
                        rw [hpfx2_len] at hi
                        have hi_rem1 : i < rem1.length := Nat.lt_of_lt_of_le hi hlen2_le
                        rw [hrip, Nat.add_assoc bBase off len1, hrem1_bytes i hi_rem1,
                            ← listGet?_take len2 rem1 i hi]
                      exact SfiPhase.pendingJmp (rem1.take len2) hrax_lt hrax_mod hrip1_lt hdec2 hwin2
                | false =>
                  dsimp
                  cases hp_ok : (isPureSfiOp (.aluImm32 op dst mask) &&
                                 !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                  | false => intro h; nomatch h
                  | true =>
                    dsimp
                    intro hchk_next
                    have cp := Bool.and_eq_true_iff.mp hp_ok
                    exact finishPure cp.1 (bnot_eq_true_imp_false cp.2) hchk_next
              | nop | endbr64 | vzeroupper | movRR64 _ _ | movImm64 _ _ | movImm32 _ _
              | load64 _ _ | store64 _ _ | load32Zext _ _ | load32Sext _ _ | lea64 _ _
              | aluRR64 _ _ _ | aluImm64 _ _ _ | aluRR32 _ _ _ | shiftImm64 _ _ _
              | imulRR64 _ _ | bsf64 _ _ | tzcnt64 _ _ | xchg64 _ _ | xchg32 _ _ | xchg16 _ _
              | lockAdd64 _ _ | lockAddImm64 _ _ | lockCmpxchg64 _ _
              | push64 _ | pop64 _ | leave64 | jmpReg _ | int3 | ud2 =>
                dsimp
                cases hp_ok : (isPureSfiOp _ &&
                               !((bBase + 32 == totalBytes) && decide (off + len1 = 32))) with
                | false => intro h; nomatch h
                | true =>
                  dsimp
                  intro hchk_next
                  have cp := Bool.and_eq_true_iff.mp hp_ok
                  exact finishPure cp.1 (bnot_eq_true_imp_false cp.2) hchk_next

theorem runX64_preserves_sfiInv {totalBytes : Nat} {img : X64ObjImage}
    {r14Base : BitVec 64} {initRegs : Reg → BitVec 64} {initMem : ByteMem}
    (hall : AllBundlesValid totalBytes img.code) :
    ∀ (steps : Nat) (nd : Nat → UndefFlags) (s : X64State),
      SfiMachineInv totalBytes img r14Base initRegs initMem s →
      SfiMachineInv totalBytes img r14Base initRegs initMem (runX64 img steps nd s)
  | 0, _, _, hinv => hinv
  | steps + 1, nd, s, hinv =>
    runX64_preserves_sfiInv hall steps (fun k => nd (k + 1)) (stepX64 img (nd 0) s)
      (step_preserves_sfiInv hall (nd 0) hinv)

/-- Top-level Decidable Binary SFI Containment Theorem (`checkSfiObject_preserves_rust_host_safety`):
    Any arbitrarily large cyclic C `.o` passing `checkSfiObject totalBytes img = true` (zero manual
    loop invariants!) is guaranteed across ALL execution lengths `steps : Nat` and ALL demonic
    hardware flag streams `nd : Nat → UndefFlags` to never fault, never modify `%r14`, `%rsp`, or
    any SysV callee-saved register (`%rbx`, `%rbp`, `%r12`–`%r15`), never escape `[0, totalBytes)`,
    and never overwrite a single byte of Rust host memory outside `[r14, r14 + 2^32 + 64 KiB)`. -/
theorem checkSfiObject_preserves_rust_host_safety
    {totalBytes : Nat} {img : X64ObjImage}
    (hok : checkSfiObject totalBytes img = true)
    (s0 : X64State)
    (hrip0 : s0.rip < totalBytes) (hmod0 : s0.rip % 32 = 0)
    (hnf0 : s0.fault = false) :
    ∀ (steps : Nat) (nd : Nat → UndefFlags),
      let sf := runX64 img steps nd s0
      sf.fault = false ∧
      sf.regs .r14 = s0.regs .r14 ∧
      sf.regs .rsp = s0.regs .rsp ∧
      (∀ r, isHostProtectedReg r = true → sf.regs r = s0.regs r) ∧
      (∀ a, OutsideSandboxArena (s0.regs .r14) a → sf.mem a = s0.mem a) ∧
      (sf.halted = false → sf.rip < totalBytes) := by
  intro steps nd
  have hall := checkSfiObject_bundlesValid hok
  have hinv0 : SfiMachineInv totalBytes img (s0.regs .r14) s0.regs s0.mem s0 := by
    refine ⟨⟨hnf0, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩, ?_⟩
    intro _
    exact enterBundleStart hall hrip0 hmod0 rfl
  rcases runX64_preserves_sfiInv hall steps nd s0 hinv0 with ⟨hcore_f, hphase_f⟩
  refine ⟨hcore_f.1, hcore_f.2.1, hcore_f.2.2.1, hcore_f.2.2.2.1, hcore_f.2.2.2.2, ?_⟩
  intro hnh_f
  exact sfiPhase_rip_lt (hphase_f hnh_f)

end ByteX86
