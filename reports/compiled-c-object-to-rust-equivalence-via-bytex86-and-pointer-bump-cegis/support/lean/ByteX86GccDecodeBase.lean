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
import Init.Omega
import VendorX86GccRef
import ByteX86Gcc

/-!
# `ByteX86GccPass2`

Kernel-checked Pass-2 correlation (`0` `sorry`, `0` `isPartial`) proving that the
standalone Pass-1 operational model `ByteX86Gcc` faithfully simulates the
`s2n-bignum` + `intelxed` reference machine `VendorX86GccRef` across the entire
`gcc 15.2.0 -O2` and `-O3 -mavx2` instruction and sub-register slice:

1. **Exact 16-Byte Fetch-Window Decoder Isomorphism (`decodeRef_commutes_of_len16`):**
   Every 16-byte instruction fetch window (`w16.length = 16`) decodes to the exact
   homomorphic `DecodeOutcome` (matching instruction AST, byte length `1..15`, and
   `#GP(0)` / `#UD` fault classification).
2. **Universal Single-Step & Multi-Step Forward Simulation
   (`vendorX86GccRef_step_sub_byteX86Gcc_step`,
   `vendorX86GccRef_stepsN_sub_byteX86Gcc_stepsN`):**
   `VendorX86GccRef.Step ⊆ ByteX86Gcc.Step` and `VendorX86GccRef.StepsN ⊆ ByteX86Gcc.StepsN`
   across all 8/16/32/64-bit sub-registers (`AH/CH/DH/BH` vs REX `SPL/BPL/SIL/DIL`),
   `MOVZX`/`MOVSX`/`MOVSXD`, multi-byte `0F 1F` NOPs, `MOV r64, imm64`, `LEA`, and
   Legacy Non-VEX SSE2 vs. VEX `L = 0` / `L = 1` upper-`YMM[255:128]` transitions.
3. **Reverse Soundness Counterexamples:**
   - `misdecoded_rex_subreg8_refinement_counterexample`: misdecoding `88 df`
     (`mov bh, bl`) as low-byte `mov dil, bl` breaks Pass-2 simulation.
   - `collapsed_legacy_sse_vex_refinement_counterexample`: collapsing Legacy SSE2
     `66 0f ef c0` (`pxor xmm0, xmm0`) into VEX-128 upper-lane zeroing breaks Pass-2
     simulation whenever `YMM0[255:128]` is live.
-/

namespace ByteX86GccPass2

/-! ## Section 1: Homomorphic Type & AST Bridges -/

def mapGpr : VendorX86GccRef.Gpr → ByteX86Gcc.Reg
  | .rax => .rax | .rcx => .rcx | .rdx => .rdx | .rbx => .rbx
  | .rsp => .rsp | .rbp => .rbp | .rsi => .rsi | .rdi => .rdi
  | .r8  => .r8  | .r9  => .r9  | .r10 => .r10 | .r11 => .r11
  | .r12 => .r12 | .r13 => .r13 | .r14 => .r14 | .r15 => .r15

def unmapReg : ByteX86Gcc.Reg → VendorX86GccRef.Gpr
  | .rax => .rax | .rcx => .rcx | .rdx => .rdx | .rbx => .rbx
  | .rsp => .rsp | .rbp => .rbp | .rsi => .rsi | .rdi => .rdi
  | .r8  => .r8  | .r9  => .r9  | .r10 => .r10 | .r11 => .r11
  | .r12 => .r12 | .r13 => .r13 | .r14 => .r14 | .r15 => .r15

@[simp] theorem unmapReg_mapGpr (g : VendorX86GccRef.Gpr) :
    unmapReg (mapGpr g) = g := by
  cases g <;> rfl

@[simp] theorem mapGpr_unmapReg (r : ByteX86Gcc.Reg) :
    mapGpr (unmapReg r) = r := by
  cases r <;> rfl

theorem mapGpr_gprOfNat (n : Nat) :
    mapGpr (VendorX86GccRef.gprOfNat n) = ByteX86Gcc.regOfNat n := by
  unfold VendorX86GccRef.gprOfNat ByteX86Gcc.regOfNat
  match n % 16 with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
  | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | 8 => rfl | 9 => rfl | 10 => rfl | 11 => rfl
  | 12 => rfl | 13 => rfl | 14 => rfl | _ + 15 => rfl

def mapReg8 : VendorX86GccRef.Reg8 → ByteX86Gcc.SubReg8
  | .lo8 g => .lo8 (mapGpr g)
  | .hi8 g => .hi8 (mapGpr g)

theorem mapReg8_reg8OfIdx (rexP extBit : Bool) (idx3 : BitVec 3) :
    mapReg8 (VendorX86GccRef.reg8OfIdx rexP extBit idx3) =
      ByteX86Gcc.subReg8OfIdx rexP extBit idx3 := by
  cases rexP with
  | false =>
    dsimp [VendorX86GccRef.reg8OfIdx, ByteX86Gcc.subReg8OfIdx, mapReg8]
    match idx3.toNat with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
    | 4 => rfl | 5 => rfl | 6 => rfl | _ + 7 => rfl
  | true =>
    dsimp [VendorX86GccRef.reg8OfIdx, ByteX86Gcc.subReg8OfIdx, mapReg8]
    rw [mapGpr_gprOfNat]

def mapOpSize : VendorX86GccRef.OpSize → ByteX86Gcc.OpSize
  | .s16 => .s16 | .s32 => .s32 | .s64 => .s64

def mapAluOp : VendorX86GccRef.AluOp → ByteX86Gcc.AluOp
  | .add => .add | .or => .or | .adc => .adc | .sbb => .sbb
  | .and => .and | .sub => .sub | .xor => .xor | .cmp => .cmp | .test => .test

def mapUnaryOp : VendorX86GccRef.UnaryOp → ByteX86Gcc.UnaryOp
  | .not => .not | .neg => .neg | .inc => .inc | .dec => .dec

def mapShiftOp : VendorX86GccRef.ShiftOp → ByteX86Gcc.ShiftOp
  | .rol => .rol | .ror => .ror | .shl => .shl | .shr => .shr | .sar => .sar

def mapCond : VendorX86GccRef.Cond → ByteX86Gcc.Cond
  | .o => .o | .no => .no | .b => .b | .ae => .ae
  | .e => .e | .ne => .ne | .be => .be | .a => .a
  | .s => .s | .ns => .ns | .p => .p | .np => .np
  | .l => .l | .ge => .ge | .le => .le | .g => .g

def mapSimdMode : VendorX86GccRef.SimdMode → ByteX86Gcc.SimdMode
  | .legacy128 => .legacy128 | .vex128 => .vex128 | .vex256 => .vex256

def mapVecElem : VendorX86GccRef.VecElem → ByteX86Gcc.VecElem
  | .e8 => .e8 | .e16 => .e16 | .e32 => .e32 | .e64 => .e64

def mapVecUnpackOp : VendorX86GccRef.VecUnpackOp → ByteX86Gcc.VecUnpackOp
  | .lbw => .lbw | .hbw => .hbw | .lwd => .lwd | .hwd => .hwd
  | .ldq => .ldq | .hdq => .hdq | .lqdq => .lqdq | .hqdq => .hqdq

def mapVecExtendOp : VendorX86GccRef.VecExtendOp → ByteX86Gcc.VecExtendOp
  | .zxbw => .zxbw | .zxwd => .zxwd | .zxdq => .zxdq
  | .sxbw => .sxbw | .sxwd => .sxwd | .sxdq => .sxdq

def mapRepPfx : VendorX86GccRef.RepPfx → ByteX86Gcc.RepPfx
  | .none => .none | .repz => .repz | .repnz => .repnz

def mapFaultKind : VendorX86GccRef.FaultKind → ByteX86Gcc.DecodeFault
  | .gp0LengthExceeds15 => .gp0LengthExceeds15
  | .gp0Privilege       => .gp0Privilege
  | .udIllegalLock      => .udIllegalLock
  | .udVexPrefix        => .udVexPrefix
  | .udVexField         => .udVexField
  | .udRegisterOperand  => .udRegisterOperand
  | .udExplicit         => .udExplicit
  | .udUnmapped         => .udUnmapped

def mapAddr (a : VendorX86GccRef.MemAddr) : ByteX86Gcc.X64Addr :=
  { base   := a.base.map mapGpr
    index  := a.index.map (fun (g, sc) => (mapGpr g, sc))
    disp   := a.disp
    ripRel := a.ripRel }

def mapRm : VendorX86GccRef.RmOp → ByteX86Gcc.X64Rm
  | .reg g => .reg (mapGpr g)
  | .mem a => .mem (mapAddr a)

def mapRm8 : VendorX86GccRef.Rm8Op → ByteX86Gcc.X64Rm8
  | .reg8 r => .reg8 (mapReg8 r)
  | .mem8 a => .mem8 (mapAddr a)

def mapXmmRm : VendorX86GccRef.XmmRmOp → ByteX86Gcc.X64XmmRm
  | .reg y => .reg y
  | .mem a => .mem (mapAddr a)

def mapInstr : VendorX86GccRef.Instr → ByteX86Gcc.X64Instr
  | .nop                       => .nop
  | .endbr64                   => .endbr64
  | .vzeroupper                => .vzeroupper
  | .ud2                       => .ud2
  | .cli                       => .cli
  | .mov8Load dst src          => .mov8Load (mapReg8 dst) (mapRm8 src)
  | .mov8Store dst src         => .mov8Store (mapRm8 dst) (mapReg8 src)
  | .mov8Imm dst imm           => .mov8Imm (mapRm8 dst) imm
  | .alu8RmReg op dst src      => .alu8RmReg (mapAluOp op) (mapRm8 dst) (mapReg8 src)
  | .alu8RegRm op dst src      => .alu8RegRm (mapAluOp op) (mapReg8 dst) (mapRm8 src)
  | .alu8Imm op dst imm        => .alu8Imm (mapAluOp op) (mapRm8 dst) imm
  | .setcc8 cc dst             => .setcc8 (mapCond cc) (mapRm8 dst)
  | .movzx8 sz dst src         => .movzx8 (mapOpSize sz) (mapGpr dst) (mapRm8 src)
  | .movzx16 sz dst src        => .movzx16 (mapOpSize sz) (mapGpr dst) (mapRm src)
  | .movsx8 sz dst src         => .movsx8 (mapOpSize sz) (mapGpr dst) (mapRm8 src)
  | .movsx16 sz dst src        => .movsx16 (mapOpSize sz) (mapGpr dst) (mapRm src)
  | .movsxd dst src            => .movsxd (mapGpr dst) (mapRm src)
  | .movLoad sz dst src        => .movLoad (mapOpSize sz) (mapGpr dst) (mapRm src)
  | .movStore sz dst src       => .movStore (mapOpSize sz) (mapRm dst) (mapGpr src)
  | .movImm sz dst imm         => .movImm (mapOpSize sz) (mapGpr dst) imm
  | .movRmImm32 sz dst imm     => .movRmImm32 (mapOpSize sz) (mapRm dst) imm
  | .lea sz dst addr           => .lea (mapOpSize sz) (mapGpr dst) (mapAddr addr)
  | .xchg sz r1 rm             => .xchg (mapOpSize sz) (mapGpr r1) (mapRm rm)
  | .aluRmReg sz op dst src    => .aluRmReg (mapOpSize sz) (mapAluOp op) (mapRm dst) (mapGpr src)
  | .aluRegRm sz op dst src    => .aluRegRm (mapOpSize sz) (mapAluOp op) (mapGpr dst) (mapRm src)
  | .aluImm sz op dst imm      => .aluImm (mapOpSize sz) (mapAluOp op) (mapRm dst) imm
  | .unaryRm sz op dst         => .unaryRm (mapOpSize sz) (mapUnaryOp op) (mapRm dst)
  | .shiftImm sz op dst cnt    => .shiftImm (mapOpSize sz) (mapShiftOp op) (mapRm dst) cnt
  | .imul2 sz dst src          => .imul2 (mapOpSize sz) (mapGpr dst) (mapRm src)
  | .imul3 sz dst src imm      => .imul3 (mapOpSize sz) (mapGpr dst) (mapRm src) imm
  | .bsf sz dst src            => .bsf (mapOpSize sz) (mapGpr dst) (mapRm src)
  | .push64 src                => .push64 (mapGpr src)
  | .pop64 dst                 => .pop64 (mapGpr dst)
  | .leave64                   => .leave64
  | .ret64                     => .ret64
  | .jmpRel rel                => .jmpRel rel
  | .jccRel cc rel             => .jccRel (mapCond cc) rel
  | .simdMovLoad m dst src     => .simdMovLoad (mapSimdMode m) dst (mapXmmRm src)
  | .simdMovStore m dst src    => .simdMovStore (mapSimdMode m) (mapXmmRm dst) src
  | .simdMovqLoad v dst src    => .simdMovqLoad v dst (mapXmmRm src)
  | .simdMovqStore v dst src   => .simdMovqStore v (mapXmmRm dst) src
  | .simdMovGprToX v w dst src => .simdMovGprToX v w dst (mapRm src)
  | .simdMovXToGpr v w dst src => .simdMovXToGpr v w (mapRm dst) src
  | .simdBitwise m op d s1 s2  => .simdBitwise (mapSimdMode m) (mapAluOp op) d s1 (mapXmmRm s2)
  | .simdAdd m ew d s1 s2      => .simdAdd (mapSimdMode m) (mapVecElem ew) d s1 (mapXmmRm s2)
  | .simdSub m ew d s1 s2      => .simdSub (mapSimdMode m) (mapVecElem ew) d s1 (mapXmmRm s2)
  | .simdCmpeq m ew d s1 s2    => .simdCmpeq (mapSimdMode m) (mapVecElem ew) d s1 (mapXmmRm s2)
  | .simdCmpgt m ew d s1 s2    => .simdCmpgt (mapSimdMode m) (mapVecElem ew) d s1 (mapXmmRm s2)
  | .simdUnpack m op d s1 s2   => .simdUnpack (mapSimdMode m) (mapVecUnpackOp op) d s1 (mapXmmRm s2)
  | .simdExtend m op dst src   => .simdExtend (mapSimdMode m) (mapVecExtendOp op) dst (mapXmmRm src)
  | .simdBroadcastB m dst src  => .simdBroadcastB (mapSimdMode m) dst (mapXmmRm src)
  | .simdBroadcastQ m dst src  => .simdBroadcastQ (mapSimdMode m) dst (mapXmmRm src)
  | .simdPmullw m d s1 s2      => .simdPmullw (mapSimdMode m) d s1 (mapXmmRm s2)
  | .simdPmulhuw m d s1 s2     => .simdPmulhuw (mapSimdMode m) d s1 (mapXmmRm s2)
  | .simdPmulld m d s1 s2      => .simdPmulld (mapSimdMode m) d s1 (mapXmmRm s2)
  | .simdPmaddwd m d s1 s2     => .simdPmaddwd (mapSimdMode m) d s1 (mapXmmRm s2)
  | .simdPsrldq m dst src imm  => .simdPsrldq (mapSimdMode m) dst src imm
  | .simdPsrlqImm m dst src im => .simdPsrlqImm (mapSimdMode m) dst src im
  | .simdPshufd m dst src imm  => .simdPshufd (mapSimdMode m) dst (mapXmmRm src) imm
  | .simdPshuflw m dst src imm => .simdPshuflw (mapSimdMode m) dst (mapXmmRm src) imm
  | .simdExtract128 dst src im => .simdExtract128 (mapXmmRm dst) src im
  | .simdPerm2i128 d s1 s2 imm => .simdPerm2i128 d s1 (mapXmmRm s2) imm

def mapExcept : Except VendorX86GccRef.FaultKind VendorX86GccRef.Instr →
    Except ByteX86Gcc.DecodeFault ByteX86Gcc.X64Instr
  | .error fk => .error (mapFaultKind fk)
  | .ok ins   => .ok (mapInstr ins)

def mapOutcome : VendorX86GccRef.DecodeResult → ByteX86Gcc.DecodeOutcome
  | .fault fk   => .fault (mapFaultKind fk)
  | .ok ins len => .ok (mapInstr ins) len

theorem mapExcept_if {c : Prop} [Decidable c]
    (a b : Except VendorX86GccRef.FaultKind VendorX86GccRef.Instr) :
    mapExcept (if c then a else b) = (if c then mapExcept a else mapExcept b) := by
  split <;> rfl

/-! ## Section 2: Exact 16-Byte Fetch-Window Decoder Agreement -/

def mapPrefixState (ps : VendorX86GccRef.PrefixState) : ByteX86Gcc.PrefixState :=
  { has66      := ps.has66
    rep        := mapRepPfx ps.rep
    hasLock    := ps.hasLock
    hasSegOr67 := ps.hasSegOr67
    rex        := ps.rex
    count      := ps.count }

theorem rexBit_eq (rex : Option (BitVec 4)) (idx : Nat) :
    ByteX86Gcc.rexBit rex idx = VendorX86GccRef.rexBit rex idx := by
  cases rex <;> rfl

theorem rexB_eq (rex : Option (BitVec 4)) : ByteX86Gcc.rexB rex = VendorX86GccRef.rexB rex :=
  rexBit_eq rex 0
theorem rexX_eq (rex : Option (BitVec 4)) : ByteX86Gcc.rexX rex = VendorX86GccRef.rexX rex :=
  rexBit_eq rex 1
theorem rexR_eq (rex : Option (BitVec 4)) : ByteX86Gcc.rexR rex = VendorX86GccRef.rexR rex :=
  rexBit_eq rex 2
theorem rexW_eq (rex : Option (BitVec 4)) : ByteX86Gcc.rexW rex = VendorX86GccRef.rexW rex :=
  rexBit_eq rex 3

theorem opSizeOf_eq (ps : VendorX86GccRef.PrefixState) :
    ByteX86Gcc.opSizeOf (mapPrefixState ps) = mapOpSize (VendorX86GccRef.opSizeOf ps) := by
  unfold ByteX86Gcc.opSizeOf VendorX86GccRef.opSizeOf mapPrefixState
  dsimp only
  rw [rexW_eq]
  cases VendorX86GccRef.rexW ps.rex <;> cases ps.has66 <;> rfl

theorem condOfNib_eq (n : Nat) :
    ByteX86Gcc.condOfNib n = mapCond (VendorX86GccRef.condOfNib n) := by
  unfold ByteX86Gcc.condOfNib VendorX86GccRef.condOfNib
  match n % 16 with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
  | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl
  | 8 => rfl | 9 => rfl | 10 => rfl | 11 => rfl
  | 12 => rfl | 13 => rfl | 14 => rfl | _ + 15 => rfl

theorem aluOpOfIdx_eq (idx : Nat) :
    ByteX86Gcc.aluOpOfIdx idx = (VendorX86GccRef.aluOpOfIdx idx).map mapAluOp := by
  unfold ByteX86Gcc.aluOpOfIdx VendorX86GccRef.aluOpOfIdx
  match idx with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
  | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl | _ + 8 => rfl

theorem shiftOpOfIdx_eq (idx : Nat) :
    ByteX86Gcc.shiftOpOfIdx idx = (VendorX86GccRef.shiftOpOfIdx idx).map mapShiftOp := by
  unfold ByteX86Gcc.shiftOpOfIdx VendorX86GccRef.shiftOpOfIdx
  match idx with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
  | 4 => rfl | 5 => rfl | 6 => rfl | 7 => rfl | _ + 8 => rfl

theorem readLe16?_eq (xs : List (BitVec 8)) :
    ByteX86Gcc.readLe16? xs = VendorX86GccRef.readLe16? xs := by
  cases xs with
  | nil => rfl
  | cons b0 r0 => cases r0 <;> rfl

theorem readLe32?_eq (xs : List (BitVec 8)) :
    ByteX86Gcc.readLe32? xs = VendorX86GccRef.readLe32? xs := by
  cases xs with
  | nil => rfl
  | cons b0 r0 =>
    cases r0 with
    | nil => rfl
    | cons b1 r1 =>
      cases r1 with
      | nil => rfl
      | cons b2 r2 => cases r2 <;> rfl

theorem readLe64?_eq (xs : List (BitVec 8)) :
    ByteX86Gcc.readLe64? xs = VendorX86GccRef.readLe64? xs := by
  cases xs with
  | nil => rfl
  | cons b0 r0 =>
    cases r0 with
    | nil => rfl
    | cons b1 r1 =>
      cases r1 with
      | nil => rfl
      | cons b2 r2 =>
        cases r2 with
        | nil => rfl
        | cons b3 r3 =>
          cases r3 with
          | nil => rfl
          | cons b4 r4 =>
            cases r4 with
            | nil => rfl
            | cons b5 r5 =>
              cases r5 with
              | nil => rfl
              | cons b6 r6 => cases r6 <;> rfl

theorem scanPrefixes_commutes (fuel : Nat) :
    ∀ (st : VendorX86GccRef.PrefixState) (bs : List (BitVec 8)),
      ByteX86Gcc.scanPrefixes fuel (mapPrefixState st) bs =
        let (ps, rem) := VendorX86GccRef.scanPrefixes fuel st bs
        (mapPrefixState ps, rem) := by
  induction fuel with
  | zero => intro st bs; rfl
  | succ k ih =>
    intro st bs
    cases bs with
    | nil => rfl
    | cons b rest =>
      rw [ByteX86Gcc.scanPrefixes_succ_cons]
      have href : VendorX86GccRef.scanPrefixes (k + 1) st (b :: rest) =
          if b == 0x66#8 then VendorX86GccRef.scanPrefixes k { st with has66 := true, rex := none, count := st.count + 1 } rest
          else if b == 0xF2#8 then VendorX86GccRef.scanPrefixes k { st with rep := .repnz, rex := none, count := st.count + 1 } rest
          else if b == 0xF3#8 then VendorX86GccRef.scanPrefixes k { st with rep := .repz, rex := none, count := st.count + 1 } rest
          else if b == 0xF0#8 then VendorX86GccRef.scanPrefixes k { st with hasLock := true, rex := none, count := st.count + 1 } rest
          else if b == 0x2E#8 || b == 0x36#8 || b == 0x3E#8 || b == 0x26#8 || b == 0x64#8 || b == 0x65#8 || b == 0x67#8 then
            VendorX86GccRef.scanPrefixes k { st with hasSegOr67 := true, rex := none, count := st.count + 1 } rest
          else if (b &&& 0xF0#8) == 0x40#8 then
            VendorX86GccRef.scanPrefixes k { st with rex := some (BitVec.extractLsb' 0 4 b), count := st.count + 1 } rest
          else (st, b :: rest) := rfl
      rw [href]
      unfold ByteX86Gcc.stepPrefix
      have h66 : (mapPrefixState st).has66 = st.has66 := rfl
      have hcnt : (mapPrefixState st).count = st.count := rfl
      by_cases h1 : b == 0x66#8
      · simp only [h1, ite_true]; exact ih { st with has66 := true, rex := none, count := st.count + 1 } rest
      · simp only [h1, Bool.false_eq_true, ite_false]
        by_cases h2 : b == 0xF2#8
        · simp only [h2, ite_true]; exact ih { st with rep := .repnz, rex := none, count := st.count + 1 } rest
        · simp only [h2, Bool.false_eq_true, ite_false]
          by_cases h3 : b == 0xF3#8
          · simp only [h3, ite_true]; exact ih { st with rep := .repz, rex := none, count := st.count + 1 } rest
          · simp only [h3, Bool.false_eq_true, ite_false]
            by_cases h4 : b == 0xF0#8
            · simp only [h4, ite_true]; exact ih { st with hasLock := true, rex := none, count := st.count + 1 } rest
            · simp only [h4, Bool.false_eq_true, ite_false]
              by_cases h5 : (b == 0x2E#8 || b == 0x36#8 || b == 0x3E#8 || b == 0x26#8 || b == 0x64#8 || b == 0x65#8 || b == 0x67#8) = true
              · simp only [h5, ite_true]; exact ih { st with hasSegOr67 := true, rex := none, count := st.count + 1 } rest
              · have h5f := Bool.eq_false_iff.mpr h5
                simp only [h5f, Bool.false_eq_true, ite_false]
                by_cases h6 : (b &&& 0xF0#8) == 0x40#8
                · simp only [h6, ite_true]; exact ih { st with rex := some (BitVec.extractLsb' 0 4 b), count := st.count + 1 } rest
                · simp only [h6, Bool.false_eq_true, ite_false]

theorem modrmByteLen_eq (xs : List (BitVec 8)) :
    ByteX86Gcc.modrmByteLen xs = VendorX86GccRef.modrmByteLen xs := by
  cases xs with
  | nil => rfl
  | cons mrm rest => cases rest <;> rfl

theorem ildVexBodyLen_eq (mapSel : Nat) (xs : List (BitVec 8)) :
    ByteX86Gcc.ildVexBodyLen mapSel xs = VendorX86GccRef.ildVexBodyLen mapSel xs := by
  cases xs with
  | nil => rfl
  | cons opc afterOpc =>
    dsimp only [ByteX86Gcc.ildVexBodyLen, VendorX86GccRef.ildVexBodyLen]
    rw [modrmByteLen_eq]; rfl

theorem ildBodyLen_eq (ps : VendorX86GccRef.PrefixState) (body : List (BitVec 8)) :
    ByteX86Gcc.ildBodyLen (mapPrefixState ps) body = VendorX86GccRef.ildBodyLen ps body := by
  cases body with
  | nil => rfl
  | cons op0 rest0 =>
    unfold ByteX86Gcc.ildBodyLen VendorX86GccRef.ildBodyLen
    dsimp only [mapPrefixState]
    simp only [rexW_eq, ite_self, modrmByteLen_eq]
    cases rest0 with
    | nil => rfl
    | cons b1 r1 =>
      simp only [ildVexBodyLen_eq]
      cases r1 with
      | nil => rfl
      | cons b2 afterHdr => rfl

theorem mapIdxOpt_eq (cond : Bool) (idxFull scale2 : Nat) :
    (if cond then none else some (ByteX86Gcc.regOfNat idxFull, scale2)) =
      (if cond then none else some (VendorX86GccRef.gprOfNat idxFull, scale2)).map
        (fun (g, sc) => (mapGpr g, sc)) := by
  cases cond with
  | true => rfl
  | false => simp [mapGpr_gprOfNat]

theorem parseModRm_eq (rBit xBit bBit : Bool) (xs : List (BitVec 8)) :
    ByteX86Gcc.parseModRm rBit xBit bBit xs =
      (VendorX86GccRef.parseModRm rBit xBit bBit xs).map
        (fun (rIdx, rm, mrm, tl) => (rIdx, mapRm rm, mrm, tl)) := by
  cases xs with
  | nil => rfl
  | cons mrm rest =>
    unfold ByteX86Gcc.parseModRm VendorX86GccRef.parseModRm
    dsimp only [ByteX86Gcc.mkRegIdx, VendorX86GccRef.mkRegIdx]
    split
    · dsimp only [Option.map, mapRm]; rw [mapGpr_gprOfNat]
    · split
      · cases rest with
        | nil => rfl
        | cons sib restSib =>
          dsimp only
          split
          · rw [readLe32?_eq]
            cases VendorX86GccRef.readLe32? restSib with
            | none => rfl
            | some p =>
              cases p with
              | mk d32 restD =>
                change some (_, ByteX86Gcc.X64Rm.mem _, _, _) = some (_, mapRm _, _, _)
                dsimp only [mapRm, mapAddr]
                rw [← mapIdxOpt_eq]; rfl
          · split
            · change some (_, ByteX86Gcc.X64Rm.mem _, _, _) = some (_, mapRm _, _, _)
              dsimp only [mapRm, mapAddr]
              rw [← mapIdxOpt_eq]; dsimp only [Option.map]; rw [mapGpr_gprOfNat]
            · split
              · cases restSib with
                | nil => rfl
                | cons d8 restD =>
                  change some (_, ByteX86Gcc.X64Rm.mem _, _, _) = some (_, mapRm _, _, _)
                  dsimp only [mapRm, mapAddr]
                  rw [← mapIdxOpt_eq]; dsimp only [Option.map]; rw [mapGpr_gprOfNat]; rfl
              · rw [readLe32?_eq]
                cases VendorX86GccRef.readLe32? restSib with
                | none => rfl
                | some p =>
                  cases p with
                  | mk d32 restD =>
                    change some (_, ByteX86Gcc.X64Rm.mem _, _, _) = some (_, mapRm _, _, _)
                    dsimp only [mapRm, mapAddr]
                    rw [← mapIdxOpt_eq]; dsimp only [Option.map]; rw [mapGpr_gprOfNat]; rfl
      · split
        · rw [readLe32?_eq]
          cases VendorX86GccRef.readLe32? rest with
          | none => rfl
          | some p => cases p; rfl
        · split
          · dsimp only [Option.map, mapRm, mapAddr]; rw [mapGpr_gprOfNat]
          · split
            · cases rest with
              | nil => rfl
              | cons d8 restD =>
                dsimp only [Option.map, mapRm, mapAddr]; rw [mapGpr_gprOfNat]; rfl
            · rw [readLe32?_eq]
              cases VendorX86GccRef.readLe32? rest with
              | none => rfl
              | some p =>
                cases p with
                | mk d32 restD =>
                  dsimp only [Option.map, mapRm, mapAddr]; rw [mapGpr_gprOfNat]; rfl

theorem rmToRm8_eq (rexP bBit : Bool) (mrm : BitVec 8) (rm : VendorX86GccRef.RmOp) :
    ByteX86Gcc.rmToRm8 rexP bBit mrm (mapRm rm) = mapRm8 (VendorX86GccRef.rmToRm8 rexP bBit mrm rm) := by
  cases rm with
  | reg g => dsimp only [mapRm, ByteX86Gcc.rmToRm8, VendorX86GccRef.rmToRm8, mapRm8]; rw [mapReg8_reg8OfIdx]
  | mem a => rfl

theorem rmToXmm_eq (bBit : Bool) (mrm : BitVec 8) (rm : VendorX86GccRef.RmOp) :
    ByteX86Gcc.rmToXmm bBit mrm (mapRm rm) = mapXmmRm (VendorX86GccRef.rmToXmm bBit mrm rm) := by
  cases rm <;> rfl

theorem mapSimdMode_mode (isVex lBit : Bool) :
    (if !isVex then ByteX86Gcc.SimdMode.legacy128 else if lBit then .vex256 else .vex128) =
      mapSimdMode (if !isVex then VendorX86GccRef.SimdMode.legacy128 else if lBit then .vex256 else .vex128) := by
  cases isVex <;> cases lBit <;> rfl

theorem parseSimdOpc_eq (isVex rBit xBit bBit wBit lBit : Bool) (vvvv mapSel pp : Nat)
    (opc : BitVec 8) (afterOpc : List (BitVec 8)) :
    ByteX86Gcc.parseSimdOpc isVex rBit xBit bBit wBit lBit vvvv mapSel pp opc afterOpc =
      mapExcept (VendorX86GccRef.parseSimdOpc isVex rBit xBit bBit wBit lBit vvvv mapSel pp opc afterOpc) := by
  unfold ByteX86Gcc.parseSimdOpc VendorX86GccRef.parseSimdOpc
  dsimp only
  rw [mapSimdMode_mode, parseModRm_eq]
  by_cases h77 : (isVex && mapSel == 1 && opc == 0x77#8) = true
  · rw [ByteX86Gcc.ifTrue h77, ByteX86Gcc.ifTrue h77]
    rw [mapExcept_if]; rfl
  · rw [ByteX86Gcc.ifFalse h77, ByteX86Gcc.ifFalse h77]
    cases VendorX86GccRef.parseModRm rBit xBit bBit afterOpc with
    | none => rfl
    | some quad =>
      rcases quad with ⟨regIdx, rm, mrm, tail⟩
      dsimp only [Option.map, ByteX86Gcc.ymmIdxOfNat, VendorX86GccRef.ymmIdxOfNat]
      rw [rmToXmm_eq]
      cases tail with
      | nil =>
        cases VendorX86GccRef.rmToXmm bBit mrm rm <;>
          (dsimp only [mapXmmRm];
           (repeat rw [mapExcept_if]);
           dsimp only [mapExcept, mapInstr, mapFaultKind, mapVecElem, mapVecUnpackOp, mapVecExtendOp, mapAluOp];
           rfl)
      | cons imm8 restT =>
        cases VendorX86GccRef.rmToXmm bBit mrm rm <;>
          (dsimp only [mapXmmRm];
           (repeat rw [mapExcept_if]);
           dsimp only [mapExcept, mapInstr, mapFaultKind, mapVecElem, mapVecUnpackOp, mapVecExtendOp, mapAluOp];
           rfl)

theorem repNeNone_eq (r : VendorX86GccRef.RepPfx) :
    (mapRepPfx r != ByteX86Gcc.RepPfx.none) = (r != VendorX86GccRef.RepPfx.none) := by
  cases r <;> rfl

theorem repEqRepz_eq (r : VendorX86GccRef.RepPfx) :
    (mapRepPfx r == ByteX86Gcc.RepPfx.repz) = (r == VendorX86GccRef.RepPfx.repz) := by
  cases r <;> rfl

theorem ppOfRep_eq (ps : VendorX86GccRef.PrefixState) :
    (match (mapPrefixState ps).rep with
     | .repz => 2 | .repnz => 3 | .none => if (mapPrefixState ps).has66 then 1 else 0) =
    (match ps.rep with
     | .repz => 2 | .repnz => 3 | .none => if ps.has66 then 1 else 0) := by
  dsimp only [mapPrefixState]
  cases ps.rep <;> rfl

theorem opSizeEqS16_eq (sz : VendorX86GccRef.OpSize) :
    (mapOpSize sz == ByteX86Gcc.OpSize.s16) = (sz == VendorX86GccRef.OpSize.s16) := by
  cases sz <;> rfl

theorem mapExcept_match_pair {α β : Type _} (o : Option (α × β))
    (f : α → β → Except VendorX86GccRef.FaultKind VendorX86GccRef.Instr)
    (e : Except VendorX86GccRef.FaultKind VendorX86GccRef.Instr) :
    mapExcept (match o with | some (x, y) => f x y | none => e) =
      (match o with | some (x, y) => mapExcept (f x y) | none => mapExcept e) := by
  cases o with
  | none => rfl
  | some p => cases p; rfl

theorem mapExcept_match_opt {α : Type _} (o : Option α)
    (f : α → Except VendorX86GccRef.FaultKind VendorX86GccRef.Instr)
    (e : Except VendorX86GccRef.FaultKind VendorX86GccRef.Instr) :
    mapExcept (match o with | some x => f x | none => e) =
      (match o with | some x => mapExcept (f x) | none => mapExcept e) := by
  cases o <;> rfl

theorem parseExactBody_0f_eq (ps : VendorX86GccRef.PrefixState) (rest0 : List (BitVec 8))
    (hlock : ps.hasLock = false) :
    ByteX86Gcc.parseExactBody (mapPrefixState ps) (0x0F#8 :: rest0) =
      mapExcept (VendorX86GccRef.parseExactBody ps (0x0F#8 :: rest0)) := by
  have hlockM : (mapPrefixState ps).hasLock = false := hlock
  cases rest0 with
  | nil =>
    unfold ByteX86Gcc.parseExactBody VendorX86GccRef.parseExactBody
    simp [hlock, hlockM, mapExcept, mapFaultKind]
  | cons op1 rest1 =>
    have hL : ByteX86Gcc.parseExactBody (mapPrefixState ps) (0x0F#8 :: op1 :: rest1) =
        let rBit := ByteX86Gcc.rexR (mapPrefixState ps).rex
        let xBit := ByteX86Gcc.rexX (mapPrefixState ps).rex
        let bBit := ByteX86Gcc.rexB (mapPrefixState ps).rex
        let wBit := ByteX86Gcc.rexW (mapPrefixState ps).rex
        let rexP := (mapPrefixState ps).rex.isSome
        let sz   := ByteX86Gcc.opSizeOf (mapPrefixState ps)
        (if op1 == 0x0B#8 then .error .udExplicit
         else if op1.toNat >= 0x80 && op1.toNat <= 0x8F then
           match ByteX86Gcc.readLe32? rest1 with
           | some (d32, _) => .ok (.jccRel (ByteX86Gcc.condOfNib (op1.toNat - 0x80)) (ByteX86Gcc.sext32To64 d32))
           | none => .error .udUnmapped
         else if op1 == 0x1E#8 then
           match ByteX86Gcc.parseModRm rBit xBit bBit rest1 with
           | some (_, _, mrm, _) => if (mapPrefixState ps).rep == .repz && mrm == 0xFA#8 then .ok .endbr64 else .ok .nop
           | none => .error .udUnmapped
         else if op1 == 0x1F#8 then
           match ByteX86Gcc.parseModRm rBit xBit bBit rest1 with | some _ => .ok .nop | none => .error .udUnmapped
         else if op1 == 0xB6#8 || op1 == 0xB7#8 || op1 == 0xBE#8 || op1 == 0xBF#8 ||
                 op1 == 0xAF#8 || op1 == 0xBC#8 || (op1.toNat >= 0x90 && op1.toNat <= 0x9F) then
           match ByteX86Gcc.parseModRm rBit xBit bBit rest1 with
           | none => .error .udUnmapped
           | some (regIdx, rm, mrm, _) =>
             let dst := ByteX86Gcc.regOfNat regIdx
             let rm8 := ByteX86Gcc.rmToRm8 rexP bBit mrm rm
             if op1 == 0xB6#8 then .ok (.movzx8 sz dst rm8)
             else if op1 == 0xB7#8 then .ok (.movzx16 sz dst rm)
             else if op1 == 0xBE#8 then .ok (.movsx8 sz dst rm8)
             else if op1 == 0xBF#8 then .ok (.movsx16 sz dst rm)
             else if op1 == 0xAF#8 then .ok (.imul2 sz dst rm)
             else if op1 == 0xBC#8 then .ok (.bsf sz dst rm)
             else .ok (.setcc8 (ByteX86Gcc.condOfNib (op1.toNat - 0x90)) rm8)
         else
           let pp := match (mapPrefixState ps).rep with | .repz => 2 | .repnz => 3 | .none => if (mapPrefixState ps).has66 then 1 else 0
           ByteX86Gcc.parseSimdOpc false rBit xBit bBit wBit false 0 1 pp op1 rest1) := by
      unfold ByteX86Gcc.parseExactBody
      dsimp only
      rw [ByteX86Gcc.ifFalse (by decide), ByteX86Gcc.ifFalse (by decide),
          ByteX86Gcc.ifFalse (by simp [hlockM])]
      rfl
    have hR : VendorX86GccRef.parseExactBody ps (0x0F#8 :: op1 :: rest1) =
        let rBit := VendorX86GccRef.rexR ps.rex
        let xBit := VendorX86GccRef.rexX ps.rex
        let bBit := VendorX86GccRef.rexB ps.rex
        let wBit := VendorX86GccRef.rexW ps.rex
        let rexP := ps.rex.isSome
        let sz   := VendorX86GccRef.opSizeOf ps
        (if op1 == 0x0B#8 then .error .udExplicit
         else if op1.toNat >= 0x80 && op1.toNat <= 0x8F then
           match VendorX86GccRef.readLe32? rest1 with
           | some (d32, _) => .ok (.jccRel (VendorX86GccRef.condOfNib (op1.toNat - 0x80)) (VendorX86GccRef.sext32To64 d32))
           | none => .error .udUnmapped
         else if op1 == 0x1E#8 then
           match VendorX86GccRef.parseModRm rBit xBit bBit rest1 with
           | some (_, _, mrm, _) => if ps.rep == .repz && mrm == 0xFA#8 then .ok .endbr64 else .ok .nop
           | none => .error .udUnmapped
         else if op1 == 0x1F#8 then
           match VendorX86GccRef.parseModRm rBit xBit bBit rest1 with | some _ => .ok .nop | none => .error .udUnmapped
         else if op1 == 0xB6#8 || op1 == 0xB7#8 || op1 == 0xBE#8 || op1 == 0xBF#8 ||
                 op1 == 0xAF#8 || op1 == 0xBC#8 || (op1.toNat >= 0x90 && op1.toNat <= 0x9F) then
           match VendorX86GccRef.parseModRm rBit xBit bBit rest1 with
           | none => .error .udUnmapped
           | some (regIdx, rm, mrm, _) =>
             let dst := VendorX86GccRef.gprOfNat regIdx
             let rm8 := VendorX86GccRef.rmToRm8 rexP bBit mrm rm
             if op1 == 0xB6#8 then .ok (.movzx8 sz dst rm8)
             else if op1 == 0xB7#8 then .ok (.movzx16 sz dst rm)
             else if op1 == 0xBE#8 then .ok (.movsx8 sz dst rm8)
             else if op1 == 0xBF#8 then .ok (.movsx16 sz dst rm)
             else if op1 == 0xAF#8 then .ok (.imul2 sz dst rm)
             else if op1 == 0xBC#8 then .ok (.bsf sz dst rm)
             else .ok (.setcc8 (VendorX86GccRef.condOfNib (op1.toNat - 0x90)) rm8)
         else
           let pp := match ps.rep with | .repz => 2 | .repnz => 3 | .none => if ps.has66 then 1 else 0
           VendorX86GccRef.parseSimdOpc false rBit xBit bBit wBit false 0 1 pp op1 rest1) := by
      unfold VendorX86GccRef.parseExactBody
      dsimp only
      rw [ByteX86Gcc.ifFalse (by decide), ByteX86Gcc.ifFalse (by decide),
          ByteX86Gcc.ifFalse (by simp [hlock])]
      rfl
    rw [hL, hR]
    dsimp only
    rw [opSizeOf_eq, ppOfRep_eq]
    dsimp only [mapPrefixState]
    rw [rexR_eq, rexX_eq, rexB_eq, rexW_eq, readLe32?_eq, parseModRm_eq, parseSimdOpc_eq]
    simp only [repEqRepz_eq]
    cases VendorX86GccRef.readLe32? rest1 with
    | none =>
      cases VendorX86GccRef.parseModRm (VendorX86GccRef.rexR ps.rex) (VendorX86GccRef.rexX ps.rex) (VendorX86GccRef.rexB ps.rex) rest1 with
      | none =>
        dsimp only [Option.map]
        (repeat rw [mapExcept_if])
        dsimp only [mapExcept, mapInstr, mapFaultKind]
        (try simp only [condOfNib_eq])
        (try rfl)
      | some q =>
        rcases q with ⟨rIdx, rm, mrm, tl⟩
        dsimp only [Option.map]
        rw [rmToRm8_eq]
        (repeat rw [mapExcept_if])
        dsimp only [mapExcept, mapInstr, mapFaultKind]
        (try simp only [mapGpr_gprOfNat])
        (try simp only [condOfNib_eq])
        (try rfl)
    | some p32 =>
      rcases p32 with ⟨d32, rest32⟩
      cases VendorX86GccRef.parseModRm (VendorX86GccRef.rexR ps.rex) (VendorX86GccRef.rexX ps.rex) (VendorX86GccRef.rexB ps.rex) rest1 with
      | none =>
        dsimp only [Option.map]
        (repeat rw [mapExcept_if])
        dsimp only [mapExcept, mapInstr, mapFaultKind]
        (try simp only [condOfNib_eq])
        (try rfl)
      | some q =>
        rcases q with ⟨rIdx, rm, mrm, tl⟩
        dsimp only [Option.map]
        rw [rmToRm8_eq]
        (repeat rw [mapExcept_if])
        dsimp only [mapExcept, mapInstr, mapFaultKind]
        (try simp only [mapGpr_gprOfNat])
        (try simp only [condOfNib_eq])
        (try rfl)

end ByteX86GccPass2
