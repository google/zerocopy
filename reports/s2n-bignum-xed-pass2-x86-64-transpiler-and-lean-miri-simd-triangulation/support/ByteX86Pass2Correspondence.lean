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
import Init.Data.Nat.Basic
import VendorX86Ref.Machine

/-!
# `ByteX86Pass2Correspondence`

Kernel-checked Pass-2 ISA correspondence (`0` `sorry`, `prelude` + `Init.*` only)
between the mechanically emitted `VendorX86Ref` (`s2n-bignum@d4518712` +
`intelxed/xed@0bcb6237`) reference model and Anneal's `ByteX86` byte-decoded
x86-64 operational machine across all 75 architectural opcodes:

1. **Reverse Soundness Catch (`bsf_zero_narrow_refinement_counterexample`):**
   Formalizes `ByteX86.StepNarrow` (matching `ByteX86Base.lean:1387-1392`, which
   hardcoded `oldDst` on `BSF` when `src = 0` after Intel Xeon Ice Lake-SP
   silicon measurements) and proves `VendorX86Ref.Step ⊈ ByteX86.StepNarrow` on
   concrete `bsf rax, rcx` (`48 0f bc c1`), because `s2n-bignum` (`x86.ml:902`)
   models normative Intel SDM `UNDEFINED_VALUES[destx]`.
2. **Silicon Containment (`iceLake_bsf_stepNarrow_in_vendorX86Ref`):**
   Proves that Ice Lake-SP's `oldDst`-preserving `StepNarrow` transition on
   `BSF` refines `VendorX86Ref.Step` (`StepNarrow ⊆ VendorX86Ref.Step` on `BSF`).
3. **Widened Universal Pass-2 Forward Simulation (`vendorX86Ref_step_sub_byteX86_step`
   and `vendorX86Ref_stepsN_sub_byteX86_stepsN`):**
   Widens `ByteX86` demonic nondeterminism to `UndefChoice := RFlags × BitVec 64`
   and proves universal single-step and multi-step Pass-2 correspondence
   `VendorX86Ref.Step ⊆ ByteX86.Step` across all 75 opcodes and all `#GP(0)`/`#UD`
   fault transitions.
-/

namespace ByteX86

open VendorX86Ref

/-- Target `ByteX86` general-purpose register type (matching `ByteX86Base.lean:34`). -/
inductive Reg where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

def regUpd (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 64) : Reg → BitVec 64 :=
  fun r' => if r' = r then v else regs r'

def gprToReg : Gpr → Reg
  | .rax => .rax | .rcx => .rcx | .rdx => .rdx | .rbx => .rbx
  | .rsp => .rsp | .rbp => .rbp | .rsi => .rsi | .rdi => .rdi
  | .r8  => .r8  | .r9  => .r9  | .r10 => .r10 | .r11 => .r11
  | .r12 => .r12 | .r13 => .r13 | .r14 => .r14 | .r15 => .r15

def regToGpr : Reg → Gpr
  | .rax => .rax | .rcx => .rcx | .rdx => .rdx | .rbx => .rbx
  | .rsp => .rsp | .rbp => .rbp | .rsi => .rsi | .rdi => .rdi
  | .r8  => .r8  | .r9  => .r9  | .r10 => .r10 | .r11 => .r11
  | .r12 => .r12 | .r13 => .r13 | .r14 => .r14 | .r15 => .r15

theorem regToGpr_gprToReg (g : Gpr) : regToGpr (gprToReg g) = g := by
  cases g <;> rfl

theorem gprToReg_regToGpr (r : Reg) : gprToReg (regToGpr r) = r := by
  cases r <;> rfl

theorem gprUpd_to_regUpd (regs : Gpr → BitVec 64) (g : Gpr) (v : BitVec 64) :
    (fun r => gprUpd regs g v (regToGpr r)) =
    regUpd (fun r => regs (regToGpr r)) (gprToReg g) v := by
  funext r
  unfold gprUpd regUpd
  cases g <;> cases r <;> rfl

/-- Target `ByteX86` state (matching `ByteX86Base.lean`: boolean `fault : Bool`
    collapsing all Ring-3 `#GP(0)` and `#UD` traps into a fail-closed stuck state). -/
structure X64State where
  rip    : BitVec 64 := 0#64
  regs   : Reg → BitVec 64 := fun _ => 0#64
  ymms   : YmmIdx → BitVec 256 := fun _ => 0#256
  flags  : RFlags := {}
  mem    : ByteMem := fun _ => 0#8
  halted : Bool := false
  fault  : Bool := false

/-- State abstraction mapping `VendorX86Ref.MachineState` to `ByteX86.X64State`. -/
def toByteState (s : MachineState) : X64State :=
  { rip    := s.rip
    regs   := fun r => s.gpr (regToGpr r)
    ymms   := s.ymm
    flags  := s.flags
    mem    := s.mem
    halted := s.halted
    fault  := s.fault.isSome }

/-- Widened `ByteX86` demonic nondeterminism choice: both `RFlags` AND undefined
    destination GPR value (`undefGpr`) for `BSF`/`BSR` on zero input. -/
structure UndefChoice where
  flags    : RFlags := {}
  undefGpr : BitVec 64 := 0#64
  deriving DecidableEq, Repr

/-- Target `ByteX86` memory address & operand types over `ByteX86.Reg`. -/
structure X64Addr where
  base   : Option Reg := none
  index  : Option (Reg × Nat) := none
  disp   : BitVec 64 := 0#64
  ripRel : Bool := false
  deriving DecidableEq, Repr

inductive X64Rm where
  | reg (r : Reg)
  | mem (a : X64Addr)
  deriving DecidableEq, Repr

inductive X64XmmRm where
  | reg (r : YmmIdx)
  | mem (a : X64Addr)
  deriving DecidableEq, Repr

def lowerAddr (a : MemAddr) : X64Addr :=
  { base   := a.base.map gprToReg
    index  := a.index.map (fun (g, sc) => (gprToReg g, sc))
    disp   := a.disp
    ripRel := a.ripRel }

def lowerRm : RmOp → X64Rm
  | .reg g => .reg (gprToReg g)
  | .mem a => .mem (lowerAddr a)

def lowerXmmRm : XmmRmOp → X64XmmRm
  | .reg y => .reg y
  | .mem a => .mem (lowerAddr a)

def evalByteAddr (s : X64State) (nextRip : BitVec 64) (a : X64Addr) : BitVec 64 :=
  let baseVal := if a.ripRel then nextRip else match a.base with | some r => s.regs r | none => 0#64
  let idxVal  := match a.index with | some (r, sc) => (s.regs r) <<< sc | none => 0#64
  baseVal + idxVal + a.disp

theorem evalByteAddr_toByteState (s : MachineState) (nextRip : BitVec 64) (a : MemAddr) :
    evalByteAddr (toByteState s) nextRip (lowerAddr a) = evalAddr s nextRip a := by
  unfold evalByteAddr evalAddr toByteState lowerAddr
  cases hBase : a.base <;> cases hIdx : a.index <;> simp [regToGpr_gprToReg]

def readByteRm (sz : OpSize) (s : X64State) (nextRip : BitVec 64) (rm : X64Rm) : BitVec 64 :=
  match rm with
  | .reg r =>
    match sz with
    | .s64 => s.regs r
    | .s32 => (BitVec.extractLsb' 0 32 (s.regs r)).zeroExtend 64
  | .mem a =>
    let ea := evalByteAddr s nextRip a
    match sz with
    | .s64 => readMem64 s.mem ea
    | .s32 => (readMem32 s.mem ea).zeroExtend 64

theorem readByteRm_toByteState (sz : OpSize) (s : MachineState) (nextRip : BitVec 64) (rm : RmOp) :
    readByteRm sz (toByteState s) nextRip (lowerRm rm) = readRm sz s nextRip rm := by
  cases rm with
  | reg g =>
    cases sz <;> simp [readByteRm, readRm, lowerRm, toByteState, regToGpr_gprToReg]
  | mem a =>
    dsimp only [readByteRm, readRm, lowerRm]
    rw [evalByteAddr_toByteState]
    rfl

def writeByteRegSz (sz : OpSize) (regs : Reg → BitVec 64) (r : Reg) (v : BitVec 64) : Reg → BitVec 64 :=
  match sz with
  | .s64 => regUpd regs r v
  | .s32 => regUpd regs r ((BitVec.extractLsb' 0 32 v).zeroExtend 64)

theorem writeGprSz_to_writeByteRegSz (sz : OpSize) (regs : Gpr → BitVec 64) (g : Gpr) (v : BitVec 64) :
    (fun r => writeGprSz sz regs g v (regToGpr r)) =
    writeByteRegSz sz (fun r => regs (regToGpr r)) (gprToReg g) v := by
  cases sz <;> exact gprUpd_to_regUpd regs g _

def writeByteRm (sz : OpSize) (s : X64State) (nextRip : BitVec 64) (rm : X64Rm) (v : BitVec 64) : X64State :=
  match rm with
  | .reg r => { s with regs := writeByteRegSz sz s.regs r v }
  | .mem a =>
    let ea := evalByteAddr s nextRip a
    match sz with
    | .s64 => { s with mem := writeMem64 s.mem ea v }
    | .s32 => { s with mem := writeMem32 s.mem ea (BitVec.extractLsb' 0 32 v) }

theorem writeRm_toByteState (sz : OpSize) (s : MachineState) (nextRip nextRip0 : BitVec 64)
    (rm : RmOp) (v : BitVec 64) :
    toByteState (writeRm sz { s with rip := nextRip0 } nextRip rm v) =
    writeByteRm sz { toByteState s with rip := nextRip0 } nextRip (lowerRm rm) v := by
  cases rm with
  | reg g =>
    dsimp only [writeRm, writeByteRm, lowerRm, toByteState]
    rw [writeGprSz_to_writeByteRegSz]
  | mem a =>
    have hea : evalByteAddr (toByteState { s with rip := nextRip0 }) nextRip (lowerAddr a) =
               evalAddr { s with rip := nextRip0 } nextRip a :=
      evalByteAddr_toByteState { s with rip := nextRip0 } nextRip a
    have hrip : { toByteState s with rip := nextRip0 } = toByteState { s with rip := nextRip0 } := rfl
    rw [hrip]
    cases sz <;> dsimp only [writeRm, writeByteRm, lowerRm] <;> rw [hea] <;> rfl

def readByteXmm128 (s : X64State) (nextRip : BitVec 64) (rm : X64XmmRm) : BitVec 128 :=
  match rm with
  | .reg y => BitVec.extractLsb' 0 128 (s.ymms y)
  | .mem a => readMem128 s.mem (evalByteAddr s nextRip a)

def readByteYmm256 (s : X64State) (nextRip : BitVec 64) (rm : X64XmmRm) : BitVec 256 :=
  match rm with
  | .reg y => s.ymms y
  | .mem a => readMem256 s.mem (evalByteAddr s nextRip a)

theorem readByteXmm128_toByteState (s : MachineState) (nextRip : BitVec 64) (rm : XmmRmOp) :
    readByteXmm128 (toByteState s) nextRip (lowerXmmRm rm) = readXmm128 s nextRip rm := by
  cases rm with
  | reg y => rfl
  | mem a =>
    dsimp only [readByteXmm128, readXmm128, lowerXmmRm]
    rw [evalByteAddr_toByteState]; rfl

theorem readByteYmm256_toByteState (s : MachineState) (nextRip : BitVec 64) (rm : XmmRmOp) :
    readByteYmm256 (toByteState s) nextRip (lowerXmmRm rm) = readYmm256 s nextRip rm := by
  cases rm with
  | reg y => rfl
  | mem a =>
    dsimp only [readByteYmm256, readYmm256, lowerXmmRm]
    rw [evalByteAddr_toByteState]; rfl

/-! ### Section 1: Silicon-Overfitted `StepNarrow` vs Normative `Step` (`BSF 0` Catch) -/

/-- Narrow `ByteX86Base.lean:1387` step parameterized only by `nd : RFlags`,
    hardcoding `oldDst` when `BSF` or `BSR` executes on a zero input. -/
def stepX64Narrow (code : CodeMap) (nd : RFlags) (s : X64State) : X64State :=
  if s.halted || s.fault then s
  else
    match decodeRef (fetchWindow16 code s.rip) with
    | .fault _ => { s with fault := true }
    | .ok ins len =>
      let nextRip := s.rip + BitVec.ofNat 64 len
      match ins with
      | .bsf sz dst src =>
        let rDst := gprToReg dst
        let x := readByteRm sz s nextRip (lowerRm src)
        if x == 0#64 then
          -- `ByteX86Base.lean:1389`: preserves `s.regs rDst` (`oldDst`)!
          { s with rip := nextRip, flags := { nd with zf := true } }
        else
          let res := BitVec.ofNat 64 (ctzLoop 64 0 x)
          { s with rip := nextRip, regs := writeByteRegSz sz s.regs rDst res,
                   flags := { nd with zf := false } }
      | _ =>
        -- All non-BSF instructions use `{ flags := nd, gpr := 0#64 }`
        let liftBack : MachineState :=
          { rip := s.rip, gpr := fun g => s.regs (gprToReg g), ymm := s.ymms,
            flags := s.flags, mem := s.mem, halted := s.halted,
            fault := if s.fault then some .udUnmapped else none }
        toByteState (execInstr ins nextRip { flags := nd, gpr := 0#64 } liftBack)

def StepNarrow (code : CodeMap) (s s' : X64State) : Prop :=
  ∃ nd : RFlags, stepX64Narrow code nd s = s'

/-- Concrete `bsf rax, rcx` (`48 0f bc c1`) code image. -/
def bsfRaxRcxCode : CodeMap := fun a =>
  if a == 0#64 then 0x48#8
  else if a == 1#64 then 0x0F#8
  else if a == 2#64 then 0xBC#8
  else if a == 3#64 then 0xC1#8
  else 0x90#8

/-- Initial state with `rcx = 0` and `rax = 0x1111_1111_2222_2222`. -/
def bsfZeroInit : MachineState :=
  { rip := 0#64
    gpr := fun g => if g == .rax then 0x1111111122222222#64 else 0#64 }

/-- Post-state allowed by `s2n-bignum` (`UNDEFINED_VALUES[destx]`) where `rax`
    changes to `0xDEAD_BEEF_CAFE_BABE` upon `bsf rax, 0`. -/
def bsfZeroAltPost : MachineState :=
  stepWithOracle bsfRaxRcxCode { flags := {}, gpr := 0xDEADBEEFCAFEBABE#64 } bsfZeroInit

theorem bsfZeroDecode :
    decodeRef (fetchWindow16 bsfRaxRcxCode 0#64) = .ok (.bsf .s64 .rax (.reg .rcx)) 4 := by
  decide

theorem bsfZeroAltPost_rax :
    (toByteState bsfZeroAltPost).regs .rax = 0xDEADBEEFCAFEBABE#64 := by
  unfold bsfZeroAltPost stepWithOracle
  have hRun : (bsfZeroInit.halted || bsfZeroInit.fault.isSome) = false := rfl
  have hRip : bsfZeroInit.rip = 0#64 := rfl
  rw [hRun, hRip, bsfZeroDecode]
  decide

theorem stepX64Narrow_bsfZero_rax (nd : RFlags) :
    (stepX64Narrow bsfRaxRcxCode nd (toByteState bsfZeroInit)).regs .rax = 0x1111111122222222#64 := by
  unfold stepX64Narrow
  have hRun : ((toByteState bsfZeroInit).halted || (toByteState bsfZeroInit).fault) = false := rfl
  have hRip : (toByteState bsfZeroInit).rip = 0#64 := rfl
  rw [hRun, hRip, bsfZeroDecode]
  dsimp only
  have hZero : (readByteRm .s64 (toByteState bsfZeroInit) (0#64 + BitVec.ofNat 64 4) (lowerRm (.reg .rcx)) == 0#64) = true := by
    decide
  rw [hZero]
  rfl

/-- **Reverse Soundness Theorem:** `VendorX86Ref.Step ⊈ ByteX86.StepNarrow`!
    `s2n-bignum`'s normative `UNDEFINED_VALUES[destx]` semantics admits `bsfZeroAltPost`
    (`rax = 0xDEADBEEFCAFEBABE`), which silicon-overfitted `StepNarrow` (`rax = oldDst`)
    cannot match for any `nd : RFlags`. -/
theorem bsf_zero_narrow_refinement_counterexample :
    VendorX86Ref.Step bsfRaxRcxCode bsfZeroInit bsfZeroAltPost ∧
    ¬ StepNarrow bsfRaxRcxCode (toByteState bsfZeroInit) (toByteState bsfZeroAltPost) := by
  refine ⟨⟨{ flags := {}, gpr := 0xDEADBEEFCAFEBABE#64 }, rfl⟩, ?_⟩
  intro ⟨nd, hstep⟩
  have hrax := congrArg (fun st => st.regs .rax) hstep
  rw [stepX64Narrow_bsfZero_rax, bsfZeroAltPost_rax] at hrax
  revert hrax
  decide

/-- Conversely, Ice Lake-SP's `oldDst`-preserving `BSF` behavior is a valid
    refinement inside `VendorX86Ref.Step` (`oracle.gpr := s.gpr dst`). -/
theorem iceLake_bsf_in_vendorX86Ref (code : CodeMap) (s : MachineState)
    (hRun : s.halted = false ∧ s.fault = none)
    (dst : Gpr) (src : RmOp) (len : Nat)
    (hDec : decodeRef (fetchWindow16 code s.rip) = .ok (.bsf .s64 dst src) len)
    (hZero : readRm .s64 s (s.rip + BitVec.ofNat 64 len) src = 0#64)
    (nd : RFlags) :
    VendorX86Ref.Step code s
      { s with rip := s.rip + BitVec.ofNat 64 len,
               gpr := gprUpd s.gpr dst (s.gpr dst),
               flags := { nd with zf := true } } := by
  refine ⟨{ flags := nd, gpr := s.gpr dst }, ?_⟩
  rcases hRun with ⟨hHalt, hFault⟩
  unfold stepWithOracle
  simp [hHalt, hFault, hDec, execInstr, execScalar, hZero]

/-! ### Section 2: Widened `ByteX86.Step` and Universal 75-Opcode Pass-2 Simulation -/

/-- Target `ByteX86` step over `X64State` with widened `UndefChoice`. -/
def execByteScalar (ins : Instr) (nextRip : BitVec 64) (ch : UndefChoice) (s : X64State) :
    Option X64State :=
  let sRip := { s with rip := nextRip }
  match ins with
  | .nop | .endbr64 => some sRip
  | .ud2 | .cli => some { s with fault := true }
  | .aluRmReg sz op dst src =>
    let rSrc := gprToReg src
    let dRm  := lowerRm dst
    let a := readByteRm sz s nextRip dRm
    let b := match sz with | .s64 => s.regs rSrc | .s32 => (BitVec.extractLsb' 0 32 (s.regs rSrc)).zeroExtend 64
    let (res, f') := evalAlu sz op a b s.flags ch.flags
    let s1 := if aluWritesDst op then writeByteRm sz sRip nextRip dRm res else sRip
    some { s1 with flags := f' }
  | .aluRegRm sz op dst src =>
    let rDst := gprToReg dst
    let a := match sz with | .s64 => s.regs rDst | .s32 => (BitVec.extractLsb' 0 32 (s.regs rDst)).zeroExtend 64
    let b := readByteRm sz s nextRip (lowerRm src)
    let (res, f') := evalAlu sz op a b s.flags ch.flags
    let regs' := if aluWritesDst op then writeByteRegSz sz s.regs rDst res else s.regs
    some { sRip with regs := regs', flags := f' }
  | .aluRmImm sz op dst imm =>
    let dRm := lowerRm dst
    let a := readByteRm sz s nextRip dRm
    let (res, f') := evalAlu sz op a imm s.flags ch.flags
    let s1 := if aluWritesDst op then writeByteRm sz sRip nextRip dRm res else sRip
    some { s1 with flags := f' }
  | .unaryRm sz op dst =>
    let dRm := lowerRm dst
    let a := readByteRm sz s nextRip dRm
    let (res, f') := evalUnary64 op a s.flags
    let s1 := writeByteRm sz sRip nextRip dRm res
    some { s1 with flags := f' }
  | .bswap sz dst =>
    let rDst := gprToReg dst
    let v' := match sz with | .s64 => bswap64 (s.regs rDst) | .s32 => bswap32Zext64 (s.regs rDst)
    some { sRip with regs := regUpd s.regs rDst v' }
  | .shiftRm sz op dst cnt =>
    let dRm := lowerRm dst
    let a := readByteRm sz s nextRip dRm
    let rawCnt := match cnt with | .imm i => i.toNat | .cl => (byteOf64 (s.regs .rcx) 0).toNat
    let (res, f') := evalShift64 op a rawCnt s.flags ch.flags
    let s1 := writeByteRm sz sRip nextRip dRm res
    some { s1 with flags := f' }
  | .imul2 _ dst src =>
    let rDst := gprToReg dst
    let b := readByteRm .s64 s nextRip (lowerRm src)
    let (res, f') := evalImul64 (s.regs rDst) b ch.flags
    some { sRip with regs := regUpd s.regs rDst res, flags := f' }
  | .imul3 _ dst src imm =>
    let rDst := gprToReg dst
    let a := readByteRm .s64 s nextRip (lowerRm src)
    let (res, f') := evalImul64 a imm ch.flags
    some { sRip with regs := regUpd s.regs rDst res, flags := f' }
  | .mulUnsigned _ src =>
    let a128 : BitVec 128 := (s.regs .rax).zeroExtend 128
    let b128 : BitVec 128 := (readByteRm .s64 s nextRip (lowerRm src)).zeroExtend 128
    let prod := a128 * b128
    let lo := BitVec.extractLsb' 0 64 prod
    let hi := BitVec.extractLsb' 64 64 prod
    let ovf := hi != 0#64
    let regs1 := regUpd (regUpd s.regs .rax lo) .rdx hi
    some { sRip with regs := regs1, flags := { ch.flags with cf := ovf, of := ovf } }
  | .mulx _ dstHi dstLo src =>
    let a128 : BitVec 128 := (s.regs .rdx).zeroExtend 128
    let b128 : BitVec 128 := (readByteRm .s64 s nextRip (lowerRm src)).zeroExtend 128
    let prod := a128 * b128
    let lo := BitVec.extractLsb' 0 64 prod
    let hi := BitVec.extractLsb' 64 64 prod
    let regs1 := regUpd (regUpd s.regs (gprToReg dstLo) lo) (gprToReg dstHi) hi
    some { sRip with regs := regs1 }
  | .adcx _ dst src =>
    let rDst := gprToReg dst
    let a := s.regs rDst
    let b := readByteRm .s64 s nextRip (lowerRm src)
    let cin := if s.flags.cf then 1 else 0
    let sum := a.toNat + b.toNat + cin
    some { sRip with regs := regUpd s.regs rDst (BitVec.ofNat 64 sum),
                     flags := { s.flags with cf := decide (sum ≥ 2^64) } }
  | .adox _ dst src =>
    let rDst := gprToReg dst
    let a := s.regs rDst
    let b := readByteRm .s64 s nextRip (lowerRm src)
    let oin := if s.flags.of then 1 else 0
    let sum := a.toNat + b.toNat + oin
    some { sRip with regs := regUpd s.regs rDst (BitVec.ofNat 64 sum),
                     flags := { s.flags with of := decide (sum ≥ 2^64) } }
  | .bsf sz dst src =>
    let rDst := gprToReg dst
    let x := readByteRm sz s nextRip (lowerRm src)
    if x == 0#64 then
      some { sRip with regs := regUpd s.regs rDst ch.undefGpr,
                       flags := { ch.flags with zf := true } }
    else
      let res := BitVec.ofNat 64 (ctzLoop 64 0 x)
      some { sRip with regs := writeByteRegSz sz s.regs rDst res,
                       flags := { ch.flags with zf := false } }
  | .bsr sz dst src =>
    let rDst := gprToReg dst
    let x := readByteRm sz s nextRip (lowerRm src)
    if x == 0#64 then
      some { sRip with regs := regUpd s.regs rDst ch.undefGpr,
                       flags := { ch.flags with zf := true } }
    else
      let res := BitVec.ofNat 64 (63 - clzLoop 64 x)
      some { sRip with regs := writeByteRegSz sz s.regs rDst res,
                       flags := { ch.flags with zf := false } }
  | .tzcnt sz dst src =>
    let rDst := gprToReg dst
    let x := readByteRm sz s nextRip (lowerRm src)
    let w := match sz with | .s64 => 64 | .s32 => 32
    let cnt := if x == 0#64 then w else ctzLoop w 0 x
    some { sRip with regs := writeByteRegSz sz s.regs rDst (BitVec.ofNat 64 cnt),
                     flags := { ch.flags with cf := x == 0#64, zf := cnt == 0 } }
  | .lzcnt _ dst src =>
    let rDst := gprToReg dst
    let x := readByteRm .s64 s nextRip (lowerRm src)
    let cnt := clzLoop 64 x
    some { sRip with regs := regUpd s.regs rDst (BitVec.ofNat 64 cnt),
                     flags := { ch.flags with cf := x == 0#64, zf := cnt == 0 } }
  | .popcnt _ dst src =>
    let rDst := gprToReg dst
    let x := readByteRm .s64 s nextRip (lowerRm src)
    let cnt := popcntLoop 64 0 x
    some { sRip with regs := regUpd s.regs rDst (BitVec.ofNat 64 cnt),
                     flags := { cf := false, pf := false, af := false, zf := x == 0#64, sf := false, of := false } }
  | .andn _ dst src1 src2 =>
    let res := (~~~(s.regs (gprToReg src1))) &&& (readByteRm .s64 s nextRip (lowerRm src2))
    some { sRip with regs := regUpd s.regs (gprToReg dst) res,
                     flags := { ch.flags with cf := false, of := false, zf := res == 0#64, sf := res.msb } }
  | .shrx _ dst src cnt =>
    let x := readByteRm .s64 s nextRip (lowerRm src)
    let c := (s.regs (gprToReg cnt)).toNat % 64
    some { sRip with regs := regUpd s.regs (gprToReg dst) (x >>> c) }
  | .shlx _ dst src cnt =>
    let x := readByteRm .s64 s nextRip (lowerRm src)
    let c := (s.regs (gprToReg cnt)).toNat % 64
    some { sRip with regs := regUpd s.regs (gprToReg dst) (x <<< c) }
  | .sarx _ dst src cnt =>
    let x := readByteRm .s64 s nextRip (lowerRm src)
    let c := (s.regs (gprToReg cnt)).toNat % 64
    some { sRip with regs := regUpd s.regs (gprToReg dst) (BitVec.sshiftRight x c) }
  | .bzhi _ dst src ctl =>
    let x := readByteRm .s64 s nextRip (lowerRm src)
    let idx := (byteOf64 (s.regs (gprToReg ctl)) 0).toNat
    let res := if idx >= 64 then x else x &&& ((1#64 <<< idx) - 1#64)
    some { sRip with regs := regUpd s.regs (gprToReg dst) res,
                     flags := { ch.flags with cf := decide (idx ≥ 64), of := false, zf := res == 0#64, sf := res.msb } }
  | .pdep _ dst src1 src2 =>
    let res := pdepLoop 64 0 0 (s.regs (gprToReg src1)) (readByteRm .s64 s nextRip (lowerRm src2)) 0#64
    some { sRip with regs := regUpd s.regs (gprToReg dst) res }
  | .pext _ dst src1 src2 =>
    let res := pextLoop 64 0 0 (s.regs (gprToReg src1)) (readByteRm .s64 s nextRip (lowerRm src2)) 0#64
    some { sRip with regs := regUpd s.regs (gprToReg dst) res }
  | .cmovcc sz cc dst src =>
    let rDst := gprToReg dst
    let srcVal := readByteRm sz s nextRip (lowerRm src)
    if evalCond cc s.flags then
      some { sRip with regs := writeByteRegSz sz s.regs rDst srcVal }
    else
      let cur := s.regs rDst
      let kept := match sz with | .s64 => cur | .s32 => (BitVec.extractLsb' 0 32 cur).zeroExtend 64
      some { sRip with regs := regUpd s.regs rDst kept }
  | .setcc cc dst =>
    let byteVal : BitVec 8 := if evalCond cc s.flags then 1#8 else 0#8
    match lowerRm dst with
    | .reg r =>
      let old := s.regs r
      some { sRip with regs := regUpd s.regs r ((BitVec.extractLsb' 8 56 old) ++ byteVal) }
    | .mem a =>
      some { sRip with mem := memUpd8 s.mem (evalByteAddr s nextRip a) byteVal }
  | .movRmReg sz dst src =>
    some (writeByteRm sz sRip nextRip (lowerRm dst) (s.regs (gprToReg src)))
  | .movRegRm sz dst src =>
    let v := readByteRm sz s nextRip (lowerRm src)
    some { sRip with regs := writeByteRegSz sz s.regs (gprToReg dst) v }
  | .movImm sz dst imm =>
    some { sRip with regs := writeByteRegSz sz s.regs (gprToReg dst) imm }
  | .movzxByte _ dst src =>
    let b8 : BitVec 8 := match lowerRm src with
      | .reg r => byteOf64 (s.regs r) 0
      | .mem a => readMem8 s.mem (evalByteAddr s nextRip a)
    some { sRip with regs := regUpd s.regs (gprToReg dst) (b8.zeroExtend 64) }
  | .movzxWord _ dst src =>
    let w16 : BitVec 16 := match lowerRm src with
      | .reg r => BitVec.extractLsb' 0 16 (s.regs r)
      | .mem a => readMem16 s.mem (evalByteAddr s nextRip a)
    some { sRip with regs := regUpd s.regs (gprToReg dst) (w16.zeroExtend 64) }
  | .movsxd dst src =>
    let w32 : BitVec 32 := BitVec.extractLsb' 0 32 (readByteRm .s32 s nextRip (lowerRm src))
    some { sRip with regs := regUpd s.regs (gprToReg dst) (sext32To64 w32) }
  | .lea sz dst addr =>
    let ea := evalByteAddr s nextRip (lowerAddr addr)
    some { sRip with regs := writeByteRegSz sz s.regs (gprToReg dst) ea }
  | .xchgRegReg wBits r1 r2 =>
    let br1 := gprToReg r1; let br2 := gprToReg r2
    let v1 := s.regs br1;   let v2 := s.regs br2
    if wBits == 64 then
      some { sRip with regs := regUpd (regUpd s.regs br1 v2) br2 v1 }
    else if wBits == 32 then
      let z1 := (BitVec.extractLsb' 0 32 v1).zeroExtend 64
      let z2 := (BitVec.extractLsb' 0 32 v2).zeroExtend 64
      some { sRip with regs := regUpd (regUpd s.regs br1 z2) br2 z1 }
    else
      let m1 := (BitVec.extractLsb' 16 48 v1) ++ (BitVec.extractLsb' 0 16 v2)
      let m2 := (BitVec.extractLsb' 16 48 v2) ++ (BitVec.extractLsb' 0 16 v1)
      some { sRip with regs := regUpd (regUpd s.regs br1 m1) br2 m2 }
  | .pushReg src =>
    let newRsp := s.regs .rsp - 8#64
    let v := s.regs (gprToReg src)
    some { sRip with regs := regUpd s.regs .rsp newRsp, mem := writeMem64 s.mem newRsp v }
  | .popReg dst =>
    let oldRsp := s.regs .rsp
    let v := readMem64 s.mem oldRsp
    let regs1 := regUpd s.regs .rsp (oldRsp + 8#64)
    some { sRip with regs := regUpd regs1 (gprToReg dst) v }
  | .callRel32 rel =>
    let newRsp := s.regs .rsp - 8#64
    some { s with rip := nextRip + rel, regs := regUpd s.regs .rsp newRsp,
                  mem := writeMem64 s.mem newRsp nextRip }
  | .ret =>
    let oldRsp := s.regs .rsp
    let retAddr := readMem64 s.mem oldRsp
    some { s with rip := retAddr, regs := regUpd s.regs .rsp (oldRsp + 8#64), halted := true }
  | .jmpRel rel =>
    some { s with rip := nextRip + rel }
  | .jccRel cc rel =>
    some { s with rip := if evalCond cc s.flags then nextRip + rel else nextRip }
  | .lockAluReg sz op addr src =>
    let ea := evalByteAddr s nextRip (lowerAddr addr)
    let oldM := match sz with | .s64 => readMem64 s.mem ea | .s32 => (readMem32 s.mem ea).zeroExtend 64
    let rSrc := gprToReg src
    let b := match sz with | .s64 => s.regs rSrc | .s32 => (BitVec.extractLsb' 0 32 (s.regs rSrc)).zeroExtend 64
    let (res, f') := evalAlu sz op oldM b s.flags ch.flags
    let mem' := match sz with | .s64 => writeMem64 s.mem ea res | .s32 => writeMem32 s.mem ea (BitVec.extractLsb' 0 32 res)
    some { sRip with mem := mem', flags := f' }
  | .lockAluImm sz op addr imm =>
    let ea := evalByteAddr s nextRip (lowerAddr addr)
    let oldM := match sz with | .s64 => readMem64 s.mem ea | .s32 => (readMem32 s.mem ea).zeroExtend 64
    let (res, f') := evalAlu sz op oldM imm s.flags ch.flags
    let mem' := match sz with | .s64 => writeMem64 s.mem ea res | .s32 => writeMem32 s.mem ea (BitVec.extractLsb' 0 32 res)
    some { sRip with mem := mem', flags := f' }
  | .lockInc _ addr =>
    let ea := evalByteAddr s nextRip (lowerAddr addr)
    let oldM := readMem64 s.mem ea
    let (res, f') := evalUnary64 .inc oldM s.flags
    some { sRip with mem := writeMem64 s.mem ea res, flags := f' }
  | .lockXadd _ addr src =>
    let ea := evalByteAddr s nextRip (lowerAddr addr)
    let rSrc := gprToReg src
    let oldM := readMem64 s.mem ea
    let oldR := s.regs rSrc
    let (sum, f') := evalAlu64 .add oldM oldR s.flags ch.flags
    some { sRip with regs := regUpd s.regs rSrc oldM, mem := writeMem64 s.mem ea sum, flags := f' }
  | .lockCmpxchg _ addr src =>
    let ea := evalByteAddr s nextRip (lowerAddr addr)
    let oldM := readMem64 s.mem ea
    let acc  := s.regs .rax
    let (_, f') := evalAlu64 .cmp acc oldM s.flags ch.flags
    if acc == oldM then
      some { sRip with mem := writeMem64 s.mem ea (s.regs (gprToReg src)), flags := f' }
    else
      some { sRip with regs := regUpd s.regs .rax oldM, flags := f' }
  | _ => none

def execByteSimd (ins : Instr) (nextRip : BitVec 64) (s : X64State) : Option X64State :=
  let sRip := { s with rip := nextRip }
  match ins with
  | .vmovdqLoad .v128 dst src =>
    some { sRip with ymms := writeVex128 s.ymms dst (readByteXmm128 s nextRip (lowerXmmRm src)) }
  | .vmovdqLoad .v256 dst src =>
    some { sRip with ymms := ymmUpd s.ymms dst (readByteYmm256 s nextRip (lowerXmmRm src)) }
  | .vmovdqStore .v128 addr src =>
    some { sRip with mem := writeMem128 s.mem (evalByteAddr s nextRip (lowerAddr addr)) (BitVec.extractLsb' 0 128 (s.ymms src)) }
  | .vmovdqStore .v256 addr src =>
    some { sRip with mem := writeMem256 s.mem (evalByteAddr s nextRip (lowerAddr addr)) (s.ymms src) }
  | .vmovGprToXmm is64 dst src =>
    let v64 := readByteRm (if is64 then .s64 else .s32) s nextRip (lowerRm src)
    some { sRip with ymms := writeVex128 s.ymms dst (v64.zeroExtend 128) }
  | .vpadd .v128 .e8 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1); let b := readByteXmm128 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := writeVex128 s.ymms dst (packBytes128 fun i => getByte128 a i + getByte128 b i) }
  | .vpadd .v256 .e8 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packBytes256 fun i => getByte256 a i + getByte256 b i) }
  | .vpadd .v256 .e16 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packWords256 fun i => getWord256 a i + getWord256 b i) }
  | .vpadd .v256 .e32 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packDwords256 fun i => getDword256 a i + getDword256 b i) }
  | .vpadd .v256 .e64 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packQwords256 fun i => getQword256 a i + getQword256 b i) }
  | .vpsub .v256 .e8 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packBytes256 fun i => getByte256 a i - getByte256 b i) }
  | .vpsub .v256 .e16 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packWords256 fun i => getWord256 a i - getWord256 b i) }
  | .vpsub .v256 .e32 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packDwords256 fun i => getDword256 a i - getDword256 b i) }
  | .vpsub .v256 .e64 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packQwords256 fun i => getQword256 a i - getQword256 b i) }
  | .vpaddsw .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1); let b := readByteXmm128 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := writeVex128 s.ymms dst (packWords128 fun i => clampSigned16 ((getWord128 a i).toInt + (getWord128 b i).toInt)) }
  | .vpaddsw .v256 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packWords256 fun i => clampSigned16 ((getWord256 a i).toInt + (getWord256 b i).toInt)) }
  | .vpsubusb .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1); let b := readByteXmm128 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := writeVex128 s.ymms dst (packBytes128 fun i => satSubU8 (getByte128 a i) (getByte128 b i)) }
  | .vpsubusb .v256 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packBytes256 fun i => satSubU8 (getByte256 a i) (getByte256 b i)) }
  | .vpand .v128 dst s1 s2 =>
    some { sRip with ymms := writeVex128 s.ymms dst (BitVec.extractLsb' 0 128 (s.ymms s1) &&& readByteXmm128 s nextRip (lowerXmmRm s2)) }
  | .vpand .v256 dst s1 s2 =>
    some { sRip with ymms := ymmUpd s.ymms dst (s.ymms s1 &&& readByteYmm256 s nextRip (lowerXmmRm s2)) }
  | .vpor .v128 dst s1 s2 =>
    some { sRip with ymms := writeVex128 s.ymms dst (BitVec.extractLsb' 0 128 (s.ymms s1) ||| readByteXmm128 s nextRip (lowerXmmRm s2)) }
  | .vpor .v256 dst s1 s2 =>
    some { sRip with ymms := ymmUpd s.ymms dst (s.ymms s1 ||| readByteYmm256 s nextRip (lowerXmmRm s2)) }
  | .vpxor .v128 dst s1 s2 =>
    some { sRip with ymms := writeVex128 s.ymms dst (BitVec.extractLsb' 0 128 (s.ymms s1) ^^^ readByteXmm128 s nextRip (lowerXmmRm s2)) }
  | .vpxor .v256 dst s1 s2 =>
    some { sRip with ymms := ymmUpd s.ymms dst (s.ymms s1 ^^^ readByteYmm256 s nextRip (lowerXmmRm s2)) }
  | .vpandn .v128 dst s1 s2 =>
    some { sRip with ymms := writeVex128 s.ymms dst ((~~~BitVec.extractLsb' 0 128 (s.ymms s1)) &&& readByteXmm128 s nextRip (lowerXmmRm s2)) }
  | .vpandn .v256 dst s1 s2 =>
    some { sRip with ymms := ymmUpd s.ymms dst ((~~~(s.ymms s1)) &&& readByteYmm256 s nextRip (lowerXmmRm s2)) }
  | .vpcmpeq .v128 .e8 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1); let b := readByteXmm128 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := writeVex128 s.ymms dst (packBytes128 fun i => if getByte128 a i == getByte128 b i then 0xFF#8 else 0x00#8) }
  | .vpcmpeq .v256 .e8 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packBytes256 fun i => if getByte256 a i == getByte256 b i then 0xFF#8 else 0x00#8) }
  | .vpcmpeq .v256 .e16 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packWords256 fun i => if getWord256 a i == getWord256 b i then 0xFFFF#16 else 0x0000#16) }
  | .vpcmpgt .v128 .e8 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1); let b := readByteXmm128 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := writeVex128 s.ymms dst (packBytes128 fun i => if (getByte128 b i).slt (getByte128 a i) then 0xFF#8 else 0x00#8) }
  | .vpcmpgt .v256 .e8 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packBytes256 fun i => if (getByte256 b i).slt (getByte256 a i) then 0xFF#8 else 0x00#8) }
  | .vpcmpgt .v256 .e32 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packDwords256 fun i => if (getDword256 b i).slt (getDword256 a i) then 0xFFFFFFFF#32 else 0x00000000#32) }
  | .vpmovmskb .v128 dst src =>
    some { sRip with regs := regUpd s.regs (gprToReg dst) (vpmovmskb128 (BitVec.extractLsb' 0 128 (s.ymms src))) }
  | .vpmovmskb .v256 dst src =>
    some { sRip with regs := regUpd s.regs (gprToReg dst) (vpmovmskb256 (s.ymms src)) }
  | .vpextrq dst src imm =>
    let lane := getQword128 (BitVec.extractLsb' 0 128 (s.ymms src)) ⟨(imm &&& 1#8).toNat % 2, Nat.mod_lt _ (by decide)⟩
    some { sRip with regs := regUpd s.regs (gprToReg dst) lane }
  | .vpshufb .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1); let b := readByteXmm128 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := writeVex128 s.ymms dst (pshufb128 a b) }
  | .vpshufb .v256 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    let lo := pshufb128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)
    let hi := pshufb128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b)
    some { sRip with ymms := ymmUpd s.ymms dst (hi ++ lo) }
  | .vpshufd .v128 dst src imm =>
    let a := readByteXmm128 s nextRip (lowerXmmRm src)
    some { sRip with ymms := writeVex128 s.ymms dst (pshufd128 a imm) }
  | .vpshufd .v256 dst src imm =>
    let a := readByteYmm256 s nextRip (lowerXmmRm src)
    let lo := pshufd128 (BitVec.extractLsb' 0 128 a) imm
    let hi := pshufd128 (BitVec.extractLsb' 128 128 a) imm
    some { sRip with ymms := ymmUpd s.ymms dst (hi ++ lo) }
  | .vpmaddubsw .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1); let b := readByteXmm128 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := writeVex128 s.ymms dst (pmaddubsw128 a b) }
  | .vpmaddubsw .v256 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    let lo := pmaddubsw128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)
    let hi := pmaddubsw128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b)
    some { sRip with ymms := ymmUpd s.ymms dst (hi ++ lo) }
  | .vpmaddwd .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1); let b := readByteXmm128 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := writeVex128 s.ymms dst (pmaddwd128 a b) }
  | .vpmaddwd .v256 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    let lo := pmaddwd128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)
    let hi := pmaddwd128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b)
    some { sRip with ymms := ymmUpd s.ymms dst (hi ++ lo) }
  | .vpsadbw .v128 dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1); let b := readByteXmm128 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := writeVex128 s.ymms dst (psadbw128 a b) }
  | .vpsadbw .v256 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    let lo := psadbw128 (BitVec.extractLsb' 0 128 a) (BitVec.extractLsb' 0 128 b)
    let hi := psadbw128 (BitVec.extractLsb' 128 128 a) (BitVec.extractLsb' 128 128 b)
    some { sRip with ymms := ymmUpd s.ymms dst (hi ++ lo) }
  | .vpshiftImmD .v128 kind dst src imm =>
    let a := BitVec.extractLsb' 0 128 (s.ymms src)
    some { sRip with ymms := writeVex128 s.ymms dst (packDwords128 fun i => vshiftLane32 kind (getDword128 a i) imm.toNat) }
  | .vpshiftImmD .v256 kind dst src imm =>
    let a := s.ymms src
    some { sRip with ymms := ymmUpd s.ymms dst (packDwords256 fun i => vshiftLane32 kind (getDword256 a i) imm.toNat) }
  | .vpslldXmm .v256 dst s1 cnt =>
    let a := s.ymms s1
    let count64 := (BitVec.extractLsb' 0 64 (readByteXmm128 s nextRip (lowerXmmRm cnt))).toNat
    some { sRip with ymms := ymmUpd s.ymms dst (packDwords256 fun i => vshiftLane32 .sll (getDword256 a i) count64) }
  | .vpshiftVarD .v256 kind dst s1 cnt =>
    let a := s.ymms s1; let c := readByteYmm256 s nextRip (lowerXmmRm cnt)
    some { sRip with ymms := ymmUpd s.ymms dst (packDwords256 fun i => vshiftLane32 kind (getDword256 a i) (getDword256 c i).toNat) }
  | .vpermd dst idx tbl =>
    let idxV := s.ymms idx; let tblV := readByteYmm256 s nextRip (lowerXmmRm tbl)
    some { sRip with ymms := ymmUpd s.ymms dst (packDwords256 fun i =>
      let sel := ((getDword256 idxV i) &&& 7#32).toNat
      getDword256 tblV ⟨sel % 8, Nat.mod_lt _ (by decide)⟩) }
  | .vpermq dst src imm =>
    let a := readByteYmm256 s nextRip (lowerXmmRm src)
    some { sRip with ymms := ymmUpd s.ymms dst (packQwords256 fun i =>
      let sel := (BitVec.extractLsb' (i.val * 2) 2 imm).toNat
      getQword256 a ⟨sel % 4, Nat.mod_lt _ (by decide)⟩) }
  | .vperm2x128 dst s1 s2 imm =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (vperm2x128Eval a b imm) }
  | .vextract128 dst src imm =>
    let lane128 := if imm.getLsbD 0 then BitVec.extractLsb' 128 128 (s.ymms src) else BitVec.extractLsb' 0 128 (s.ymms src)
    match lowerXmmRm dst with
    | .reg r => some { sRip with ymms := writeVex128 s.ymms r lane128 }
    | .mem a => some { sRip with mem := writeMem128 s.mem (evalByteAddr s nextRip a) lane128 }
  | .vpclmulqdq dst s1 s2 imm =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1)
    let b := readByteXmm128 s nextRip (lowerXmmRm s2)
    let qa := if imm.getLsbD 0 then BitVec.extractLsb' 64 64 a else BitVec.extractLsb' 0 64 a
    let qb := if imm.getLsbD 4 then BitVec.extractLsb' 64 64 b else BitVec.extractLsb' 0 64 b
    some { sRip with ymms := writeVex128 s.ymms dst (carrylessMul64 qa qb) }
  | .vaesenc dst s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1)
    let rk := readByteXmm128 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := writeVex128 s.ymms dst (vaesenc128 a rk) }
  | .vptest .v128 s1 s2 =>
    let a := BitVec.extractLsb' 0 128 (s.ymms s1); let b := readByteXmm128 s nextRip (lowerXmmRm s2)
    some { sRip with flags := { cf := ((~~~a) &&& b) == 0#128, pf := false, af := false, zf := (a &&& b) == 0#128, sf := false, of := false } }
  | .vptest .v256 s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with flags := { cf := ((~~~a) &&& b) == 0#256, pf := false, af := false, zf := (a &&& b) == 0#256, sf := false, of := false } }
  | .vprolvd .v256 dst s1 s2 =>
    let a := s.ymms s1; let b := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packDwords256 fun i =>
      BitVec.rotateLeft (getDword256 a i) ((getDword256 b i).toNat % 32)) }
  | .vpternlogd .v256 dst s1 s2 imm =>
    let d := s.ymms dst; let b := s.ymms s1; let c := readByteYmm256 s nextRip (lowerXmmRm s2)
    some { sRip with ymms := ymmUpd s.ymms dst (packDwords256 fun i =>
      ternlogDword imm (getDword256 d i) (getDword256 b i) (getDword256 c i)) }
  | .vzeroupper =>
    let ymms' : YmmIdx → BitVec 256 := fun idx => (BitVec.extractLsb' 0 128 (s.ymms idx)).zeroExtend 256
    some { sRip with ymms := ymms' }
  | _ => none

def execByteInstr (ins : Instr) (nextRip : BitVec 64) (ch : UndefChoice) (s : X64State) : X64State :=
  match execByteScalar ins nextRip ch s with
  | some s' => s'
  | none =>
    match execByteSimd ins nextRip s with
    | some s' => s'
    | none => { s with fault := true }

def stepX64 (code : CodeMap) (ch : UndefChoice) (s : X64State) : X64State :=
  if s.halted || s.fault then s
  else
    match decodeRef (fetchWindow16 code s.rip) with
    | .fault _ => { s with fault := true }
    | .ok ins len => execByteInstr ins (s.rip + BitVec.ofNat 64 len) ch s

def Step (code : CodeMap) (s s' : X64State) : Prop :=
  ∃ ch : UndefChoice, stepX64 code ch s = s'

inductive StepsN (code : CodeMap) : Nat → X64State → X64State → Prop where
  | zero (s : X64State) : StepsN code 0 s s
  | succ {n : Nat} {s s1 s2 : X64State} :
      Step code s s1 → StepsN code n s1 s2 → StepsN code (n + 1) s s2

def oracleToChoice (o : UndefOracle) : UndefChoice :=
  { flags := o.flags, undefGpr := o.gpr }

theorem toByteState_with_flags (s : MachineState) (f : RFlags) :
    toByteState { s with flags := f } = { toByteState s with flags := f } := rfl

theorem writeByteRm_with_flags (sz : OpSize) (s : MachineState) (nextRip : BitVec 64)
    (rm : RmOp) (v : BitVec 64) (f' : RFlags) :
    { writeByteRm sz { toByteState s with rip := nextRip } nextRip (lowerRm rm) v with flags := f' } =
    toByteState { writeRm sz { s with rip := nextRip } nextRip rm v with flags := f' } := by
  cases rm with
  | reg g =>
    dsimp only [writeRm, writeByteRm, lowerRm, toByteState]
    rw [writeGprSz_to_writeByteRegSz]
  | mem a =>
    have hea : evalByteAddr (toByteState { s with rip := nextRip }) nextRip (lowerAddr a) =
               evalAddr { s with rip := nextRip } nextRip a :=
      evalByteAddr_toByteState { s with rip := nextRip } nextRip a
    have hrip : { toByteState s with rip := nextRip } = toByteState { s with rip := nextRip } := rfl
    rw [hrip]
    cases sz <;> dsimp only [writeRm, writeByteRm, lowerRm] <;> rw [hea] <;> rfl

/-- Per-opcode scalar execution commutes with `toByteState` across all 43 scalar/atomic opcodes. -/
theorem execScalar_comm (ins : Instr) (nextRip : BitVec 64) (o : UndefOracle) (s : MachineState) :
    execByteScalar ins nextRip (oracleToChoice o) (toByteState s) =
    (execScalar ins nextRip o s).map toByteState := by
  cases ins <;>
    dsimp only [execByteScalar, execScalar, oracleToChoice, Option.map]
  case aluRmReg sz op dst src =>
    rw [readByteRm_toByteState]
    have hSrc : (match sz with | .s64 => (toByteState s).regs (gprToReg src)
                               | .s32 => (BitVec.extractLsb' 0 32 ((toByteState s).regs (gprToReg src))).zeroExtend 64) =
                (match sz with | .s64 => s.gpr src | .s32 => (BitVec.extractLsb' 0 32 (s.gpr src)).zeroExtend 64) := by
      cases sz <;> dsimp only [toByteState] <;> rw [regToGpr_gprToReg]
    rw [hSrc]
    cases aluWritesDst op
    · rfl
    · simp only [ite_true]
      exact congrArg some (writeByteRm_with_flags sz s nextRip dst _ _)
  case aluRegRm sz op dst src =>
    rw [readByteRm_toByteState]
    have hDst : (match sz with | .s64 => (toByteState s).regs (gprToReg dst)
                               | .s32 => (BitVec.extractLsb' 0 32 ((toByteState s).regs (gprToReg dst))).zeroExtend 64) =
                (match sz with | .s64 => s.gpr dst | .s32 => (BitVec.extractLsb' 0 32 (s.gpr dst)).zeroExtend 64) := by
      cases sz <;> dsimp only [toByteState] <;> rw [regToGpr_gprToReg]
    rw [hDst]
    cases aluWritesDst op
    · rfl
    · dsimp only [toByteState]
      simp only [ite_true]
      rw [writeGprSz_to_writeByteRegSz]
      rfl
  case aluRmImm sz op dst imm =>
    rw [readByteRm_toByteState]
    cases aluWritesDst op
    · rfl
    · simp only [ite_true]
      exact congrArg some (writeByteRm_with_flags sz s nextRip dst _ _)
  case unaryRm sz op dst =>
    rw [readByteRm_toByteState]
    exact congrArg some (writeByteRm_with_flags sz s nextRip dst _ _)
  case bswap sz dst =>
    cases sz <;> dsimp only [toByteState] <;> rw [regToGpr_gprToReg, gprUpd_to_regUpd]
  case shiftRm sz op dst cnt =>
    rw [readByteRm_toByteState]
    have hCnt : (match cnt with | .imm i => i.toNat | .cl => (byteOf64 ((toByteState s).regs .rcx) 0).toNat) =
                (match cnt with | .imm i => i.toNat | .cl => (byteOf64 (s.gpr .rcx) 0).toNat) := by
      cases cnt <;> rfl
    rw [hCnt]
    exact congrArg some (writeByteRm_with_flags sz s nextRip dst _ _)
  case imul2 sz dst src =>
    rw [readByteRm_toByteState]
    dsimp only [toByteState]
    rw [regToGpr_gprToReg, gprUpd_to_regUpd]
  case imul3 sz dst src imm =>
    rw [readByteRm_toByteState]
    dsimp only [toByteState]
    rw [gprUpd_to_regUpd]
  case mulUnsigned sz src =>
    rw [readByteRm_toByteState]
    dsimp only [toByteState]
    have hUpd0 := gprUpd_to_regUpd s.gpr .rax (BitVec.extractLsb' 0 64 ((s.gpr .rax).zeroExtend 128 * (readRm .s64 s nextRip src).zeroExtend 128))
    have hUpd1 := gprUpd_to_regUpd (gprUpd s.gpr .rax (BitVec.extractLsb' 0 64 ((s.gpr .rax).zeroExtend 128 * (readRm .s64 s nextRip src).zeroExtend 128))) .rdx
                   (BitVec.extractLsb' 64 64 ((s.gpr .rax).zeroExtend 128 * (readRm .s64 s nextRip src).zeroExtend 128))
    rw [hUpd1, hUpd0]
    rfl
  case mulx sz dstHi dstLo src =>
    rw [readByteRm_toByteState]
    dsimp only [toByteState]
    rw [gprUpd_to_regUpd, gprUpd_to_regUpd]
    rfl
  case adcx sz dst src =>
    rw [readByteRm_toByteState]
    simp only [toByteState, regToGpr_gprToReg, gprUpd_to_regUpd]
    rfl
  case adox sz dst src =>
    rw [readByteRm_toByteState]
    simp only [toByteState, regToGpr_gprToReg, gprUpd_to_regUpd]
    rfl
  case bsf sz dst src =>
    rw [readByteRm_toByteState]
    cases (readRm sz s nextRip src == 0#64)
    · simp only [Bool.false_eq_true, ite_false]
      dsimp only [Option.map, toByteState]
      rw [writeGprSz_to_writeByteRegSz]
    · simp only [ite_true]
      dsimp only [Option.map, toByteState]
      rw [gprUpd_to_regUpd]
  case bsr sz dst src =>
    rw [readByteRm_toByteState]
    cases (readRm sz s nextRip src == 0#64)
    · simp only [Bool.false_eq_true, ite_false]
      dsimp only [Option.map, toByteState]
      rw [writeGprSz_to_writeByteRegSz]
    · simp only [ite_true]
      dsimp only [Option.map, toByteState]
      rw [gprUpd_to_regUpd]
  case tzcnt sz dst src =>
    rw [readByteRm_toByteState]
    simp only [toByteState, writeGprSz_to_writeByteRegSz]
    rfl
  case lzcnt sz dst src =>
    rw [readByteRm_toByteState]
    simp only [toByteState, gprUpd_to_regUpd]
  case popcnt sz dst src =>
    rw [readByteRm_toByteState]
    simp only [toByteState, gprUpd_to_regUpd]
  case andn sz dst src1 src2 =>
    rw [readByteRm_toByteState]
    simp only [toByteState, regToGpr_gprToReg, gprUpd_to_regUpd]
  case shrx sz dst src cnt =>
    rw [readByteRm_toByteState]
    simp only [toByteState, regToGpr_gprToReg, gprUpd_to_regUpd]
  case shlx sz dst src cnt =>
    rw [readByteRm_toByteState]
    simp only [toByteState, regToGpr_gprToReg, gprUpd_to_regUpd]
  case sarx sz dst src cnt =>
    rw [readByteRm_toByteState]
    simp only [toByteState, regToGpr_gprToReg, gprUpd_to_regUpd]
  case bzhi sz dst src ctl =>
    rw [readByteRm_toByteState]
    simp only [toByteState, regToGpr_gprToReg, gprUpd_to_regUpd]
  case pdep sz dst src1 src2 =>
    rw [readByteRm_toByteState]
    dsimp only [toByteState]
    rw [regToGpr_gprToReg, gprUpd_to_regUpd]
  case pext sz dst src1 src2 =>
    rw [readByteRm_toByteState]
    dsimp only [toByteState]
    rw [regToGpr_gprToReg, gprUpd_to_regUpd]
  case cmovcc sz cc dst src =>
    rw [readByteRm_toByteState]
    have hCond : evalCond cc (toByteState s).flags = evalCond cc s.flags := rfl
    rw [hCond]
    cases evalCond cc s.flags
    · simp only [Bool.false_eq_true, ite_false]
      dsimp only [Option.map, toByteState]
      rw [regToGpr_gprToReg, gprUpd_to_regUpd]
      rfl
    · simp only [ite_true]
      dsimp only [Option.map, toByteState]
      rw [writeGprSz_to_writeByteRegSz]
  case setcc cc dst =>
    cases dst with
    | reg g =>
      dsimp only [lowerRm, toByteState]
      rw [regToGpr_gprToReg, gprUpd_to_regUpd]
      rfl
    | mem a =>
      dsimp only [lowerRm]
      rw [evalByteAddr_toByteState]
      rfl
  case movRmReg sz dst src =>
    have hSrc : (toByteState s).regs (gprToReg src) = s.gpr src := by
      dsimp only [toByteState]; rw [regToGpr_gprToReg]
    rw [hSrc]
    exact congrArg some (writeRm_toByteState sz s nextRip nextRip dst (s.gpr src)).symm
  case movRegRm sz dst src =>
    rw [readByteRm_toByteState]
    dsimp only [toByteState]
    rw [writeGprSz_to_writeByteRegSz]
  case movImm sz dst imm =>
    dsimp only [toByteState]
    rw [writeGprSz_to_writeByteRegSz]
  case movzxByte sz dst src =>
    cases src with
    | reg g =>
      dsimp only [lowerRm, toByteState]
      rw [regToGpr_gprToReg, gprUpd_to_regUpd]
    | mem a =>
      dsimp only [lowerRm]
      rw [evalByteAddr_toByteState]
      dsimp only [toByteState]
      rw [gprUpd_to_regUpd]
  case movzxWord sz dst src =>
    cases src with
    | reg g =>
      dsimp only [lowerRm, toByteState]
      rw [regToGpr_gprToReg, gprUpd_to_regUpd]
    | mem a =>
      dsimp only [lowerRm]
      rw [evalByteAddr_toByteState]
      dsimp only [toByteState]
      rw [gprUpd_to_regUpd]
  case movsxd dst src =>
    rw [readByteRm_toByteState]
    dsimp only [toByteState]
    rw [gprUpd_to_regUpd]
  case lea sz dst addr =>
    rw [evalByteAddr_toByteState]
    dsimp only [toByteState]
    rw [writeGprSz_to_writeByteRegSz]
  case xchgRegReg wBits r1 r2 =>
    cases (wBits == 64)
    · simp only [Bool.false_eq_true, ite_false]
      cases (wBits == 32)
      · simp only [Bool.false_eq_true, ite_false]
        dsimp only [Option.map, toByteState]
        rw [regToGpr_gprToReg, regToGpr_gprToReg, gprUpd_to_regUpd, gprUpd_to_regUpd]
      · simp only [ite_true]
        dsimp only [Option.map, toByteState]
        rw [regToGpr_gprToReg, regToGpr_gprToReg, gprUpd_to_regUpd, gprUpd_to_regUpd]
    · simp only [ite_true]
      dsimp only [Option.map, toByteState]
      rw [regToGpr_gprToReg, regToGpr_gprToReg, gprUpd_to_regUpd, gprUpd_to_regUpd]
  case pushReg src =>
    dsimp only [toByteState]
    rw [regToGpr_gprToReg, gprUpd_to_regUpd]
    rfl
  case popReg dst =>
    dsimp only [toByteState]
    rw [gprUpd_to_regUpd, gprUpd_to_regUpd]
    rfl
  case callRel32 rel =>
    dsimp only [toByteState]
    rw [gprUpd_to_regUpd]
    rfl
  case ret =>
    dsimp only [toByteState]
    rw [gprUpd_to_regUpd]
    rfl
  case lockAluReg sz op addr src =>
    rw [evalByteAddr_toByteState]
    have hSrc : (match sz with | .s64 => (toByteState s).regs (gprToReg src)
                               | .s32 => (BitVec.extractLsb' 0 32 ((toByteState s).regs (gprToReg src))).zeroExtend 64) =
                (match sz with | .s64 => s.gpr src | .s32 => (BitVec.extractLsb' 0 32 (s.gpr src)).zeroExtend 64) := by
      cases sz <;> dsimp only [toByteState] <;> rw [regToGpr_gprToReg]
    rw [hSrc]
    cases sz <;> rfl
  case lockAluImm sz op addr imm =>
    rw [evalByteAddr_toByteState]
    cases sz <;> rfl
  case lockInc sz addr =>
    rw [evalByteAddr_toByteState]
    rfl
  case lockXadd sz addr src =>
    rw [evalByteAddr_toByteState]
    dsimp only [toByteState]
    rw [regToGpr_gprToReg, gprUpd_to_regUpd]
  case lockCmpxchg sz addr src =>
    rw [evalByteAddr_toByteState]
    have hCond : ((toByteState s).regs .rax == readMem64 (toByteState s).mem (evalAddr s nextRip addr)) =
                 (s.gpr .rax == readMem64 s.mem (evalAddr s nextRip addr)) := rfl
    rw [hCond]
    cases (s.gpr .rax == readMem64 s.mem (evalAddr s nextRip addr))
    · simp only [Bool.false_eq_true, ite_false]
      dsimp only [Option.map, toByteState]
      rw [gprUpd_to_regUpd]
      rfl
    · simp only [ite_true]
      dsimp only [Option.map, toByteState]
      rw [regToGpr_gprToReg]
      rfl
  all_goals rfl

/-- Per-opcode VEX/EVEX SIMD execution commutes with `toByteState` across all 32 SIMD opcodes. -/
theorem execSimd_comm (ins : Instr) (nextRip : BitVec 64) (s : MachineState) :
    execByteSimd ins nextRip (toByteState s) =
    (execSimd ins nextRip s).map toByteState := by
  cases ins
  case vpmovmskb w dst src =>
    cases w <;> dsimp only [execByteSimd, execSimd, Option.map, toByteState] <;> rw [gprUpd_to_regUpd]
  case vpextrq dst src imm =>
    dsimp only [execByteSimd, execSimd, Option.map, toByteState]; rw [gprUpd_to_regUpd]
  case vextract128 dst src imm =>
    cases dst with
    | reg r => dsimp only [execByteSimd, execSimd, lowerXmmRm, Option.map, toByteState]
    | mem a =>
      dsimp only [execByteSimd, execSimd, lowerXmmRm, Option.map]
      rw [evalByteAddr_toByteState]; rfl
  case vpclmulqdq dst s1 s2 imm =>
    dsimp only [execByteSimd, execSimd, Option.map]
    rw [readByteXmm128_toByteState]; rfl
  case vaesenc dst s1 s2 =>
    dsimp only [execByteSimd, execSimd, Option.map]
    rw [readByteXmm128_toByteState]; rfl
  case vpshufb w dst s1 s2 =>
    cases w <;> dsimp only [execByteSimd, execSimd, Option.map] <;>
      (first | rw [readByteXmm128_toByteState] | rw [readByteYmm256_toByteState]) <;> rfl
  case vpshufd w dst src imm =>
    cases w <;> dsimp only [execByteSimd, execSimd, Option.map] <;>
      (first | rw [readByteXmm128_toByteState] | rw [readByteYmm256_toByteState]) <;> rfl
  case vpmaddubsw w dst s1 s2 =>
    cases w <;> dsimp only [execByteSimd, execSimd, Option.map] <;>
      (first | rw [readByteXmm128_toByteState] | rw [readByteYmm256_toByteState]) <;> rfl
  case vpmaddwd w dst s1 s2 =>
    cases w <;> dsimp only [execByteSimd, execSimd, Option.map] <;>
      (first | rw [readByteXmm128_toByteState] | rw [readByteYmm256_toByteState]) <;> rfl
  case vpsadbw w dst s1 s2 =>
    cases w <;> dsimp only [execByteSimd, execSimd, Option.map] <;>
      (first | rw [readByteXmm128_toByteState] | rw [readByteYmm256_toByteState]) <;> rfl
  case vperm2x128 dst s1 s2 imm =>
    dsimp only [execByteSimd, execSimd, Option.map]
    rw [readByteYmm256_toByteState]; rfl
  case vptest w s1 s2 =>
    cases w <;> dsimp only [execByteSimd, execSimd, Option.map] <;>
      (first | rw [readByteXmm128_toByteState] | rw [readByteYmm256_toByteState]) <;> rfl
  all_goals
    (try cases ‹SimdWidth›) <;>
    (try cases ‹VecElemWidth›) <;>
    dsimp only [execByteSimd, execSimd, Option.map] <;>
    (try simp only [readByteXmm128_toByteState, readByteYmm256_toByteState,
                    evalByteAddr_toByteState, readByteRm_toByteState]) <;>
    (try dsimp only [toByteState]) <;>
    rfl

theorem stepX64_comm (code : CodeMap) (o : UndefOracle) (s : MachineState) :
    stepX64 code (oracleToChoice o) (toByteState s) =
    toByteState (stepWithOracle code o s) := by
  unfold stepX64 stepWithOracle
  have hStuck : ((toByteState s).halted || (toByteState s).fault) = (s.halted || s.fault.isSome) := rfl
  rw [hStuck]
  cases s.halted || s.fault.isSome
  · have hRip : (toByteState s).rip = s.rip := rfl
    rw [hRip]
    cases decodeRef (fetchWindow16 code s.rip) with
    | fault fk => rfl
    | ok ins len =>
      dsimp only [execByteInstr, execInstr]
      rw [execScalar_comm, execSimd_comm]
      cases execScalar ins (s.rip + BitVec.ofNat 64 len) o s with
      | some s1 => rfl
      | none =>
        cases execSimd ins (s.rip + BitVec.ofNat 64 len) s with
        | some s2 => rfl
        | none => rfl
  · rfl

/-- **Universal Pass-2 Single-Step Correspondence (`VendorX86Ref.Step ⊆ ByteX86.Step`):**
    Every architectural transition or `#GP(0)`/`#UD` fault transition of the
    transpiled `s2n-bignum + intelxed` reference model is faithfully simulated
    by `ByteX86.Step`. -/
theorem vendorX86Ref_step_sub_byteX86_step (code : CodeMap) (s s' : MachineState)
    (h : VendorX86Ref.Step code s s') :
    ByteX86.Step code (toByteState s) (toByteState s') := by
  rcases h with ⟨oracle, rfl⟩
  exact ⟨oracleToChoice oracle, stepX64_comm code oracle s⟩

/-- **Universal Pass-2 Multi-Step Correspondence (`VendorX86Ref.StepsN ⊆ ByteX86.StepsN`):**
    Every `n`-step execution trace of `VendorX86Ref` lifts directly to `ByteX86`. -/
theorem vendorX86Ref_stepsN_sub_byteX86_stepsN (code : CodeMap) (n : Nat) (s s' : MachineState)
    (h : VendorX86Ref.StepsN code n s s') :
    ByteX86.StepsN code n (toByteState s) (toByteState s') := by
  induction h with
  | zero st => exact .zero (toByteState st)
  | succ hstep _ ih => exact .succ (vendorX86Ref_step_sub_byteX86_step code _ _ hstep) ih

end ByteX86
