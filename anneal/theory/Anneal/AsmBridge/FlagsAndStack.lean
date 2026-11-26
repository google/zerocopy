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
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Trusted.MirAst.Types
public import Trusted.MirModel
public import Trusted.MirSemantics.Memory
public import Anneal.ByteSubLens.Lens
public import Anneal.AsmBridge.OperandAndCap

public section

namespace Anneal.AsmBridge.FlagsAndStack

open Trusted.MirAst Trusted.MirSemantics Anneal.ByteSubLens
open Anneal.AsmBridge.OperandAndCap

/-!
# Three-Class Flag Discipline, Stack/Red-Zone Rules, & Footprint Observer

Zero-TCB (`0` `noncomputable`, `0` `._unsafe_rec`, axioms `⊆ {propext}`)
architectural flag, stack, exit-edge, and memory-footprint contracts for
`core::arch::asm!`:

1. **Architecture-Scoped Three-Class Flag Discipline:**
   - **Class 1 (`CondFlags`):** Integer condition flags (`CF,PF,AF,ZF,SF,OF` /
     `NZCV`) — volatile across `CallProtocol`; required restored on `InlineAsm`
     exit iff `preservesFlags = true` (orthogonal to `clobber_abi`, matching
     `rustc` emitting `~{flags}`/`~{fpsr}` only without `PRESERVES_FLAGS`).
   - **Class 2 (`StickyFpSimdStatus`):** Sticky FP/SIMD exception & saturation
     status (`MXCSR[5:0]` / `FPSR` incl. `QC`) — volatile / caller-saved across
     `CallProtocol` and `clobber_abi` without `preserves_flags`, yet required
     restored on `InlineAsm` exit whenever `preservesFlags = true`.
   - **Class 3 (`InvariantControlFlags`, scoped by `TargetArch`):** Checks
     `x86DFZero`, `mxcsrControl`, `x87TagEmpty`, and `x87Fcw` on `.x86_64`,
     `fpcrControl` on `.aarch64`, and `rvvVstartZero` on `.riscv64`.
2. **Option-Combination, Site-Validity, Exit-Edge `SP`, & `noreturn`:**
   `validInlineAsmOptions` rejects `nomem && readonly` and requires
   `pure_ -> (nomem || readonly) && !noreturn`; `validInlineAsmSite` further
   enforces `pure` value-output/no-label, `noreturn` no-output, and
   `may_unwind` no-label (`AsmMayUnwind`) rules. Entry `SP` must be restored on
   every exit edge, and `noreturn = true` forbids `.fallthrough` while
   admitting declared `.labelJump` edges.
3. **Unified Stack, Active Red-Zone, & Heap/Caller-Buffer Memory Discipline:**
   - `protectedStackRegion` (`[entrySp - headroom, entrySp + callerFrame)`)
     protects below-`SP` stack scratch and the caller frame / return-address
     slot.
   - Inside `[entrySp - spec.stackHeadroomBytes, entrySp)`: forbidden under
     `nostack = true`, and otherwise bounded by the active stack + red-zone
     window `[curSp - spec.redZoneBytes, entrySp)` (active `128`-byte red zone
     on SysV x86-64 vs `0`-byte red zone on Win64/AAPCS64 until `curSp` is
     lowered).
   - Disjoint from `protectedStackRegion`: resolves exposed MIR allocations
     anywhere in address space (both heap/`.rodata` below the stack and
     caller buffers above the caller frame).
4. **Total Structural `IsaAccessFootprint` Observer (`0` `partial`, `0`
   `._unsafe_rec`):** Collects `readAddrs`, `writeAddrs`, `execAddrs` via
   `List.foldr` and checks disjointness from live Rust frames.
-/

/-- Structural equality on `Bool` avoiding `BEq` typeclass synthesis. -/
@[expose] def flagBoolEq (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

/-- Pure `List.foldr` membership check on `List Nat` (`0` `._unsafe_rec`). -/
@[expose] def natMemList (x : Nat) (xs : List Nat) : Bool :=
  xs.foldr (fun y acc => Nat.beq x y || acc) false

/-! ## Section 1: Self-Contained Platform Stack Specification -/

/-- Self-contained architectural stack geometry decoupled from layout ASTs. -/
structure AsmStackSpec where
  pointerBits        : Nat
  stackHeadroomBytes : Nat
  redZoneBytes       : Nat

/-- Canonical SysV x86-64 stack specification (128-byte red zone). -/
@[expose] def sysvX64StackSpec (headroom : Nat := 4096) : AsmStackSpec :=
  { pointerBits := 64, stackHeadroomBytes := headroom, redZoneBytes := 128 }

/-- Canonical AAPCS64 stack specification (no red zone). -/
@[expose] def aapcs64StackSpec (headroom : Nat := 4096) : AsmStackSpec :=
  { pointerBits := 64, stackHeadroomBytes := headroom, redZoneBytes := 0 }

/-- Canonical Win64 x86-64 stack specification (no red zone). -/
@[expose] def win64StackSpec (headroom : Nat := 4096) : AsmStackSpec :=
  { pointerBits := 64, stackHeadroomBytes := headroom, redZoneBytes := 0 }

/-- Upper exclusive address-space bound `2^spec.pointerBits`. -/
@[expose] def maxAddrBound (spec : AsmStackSpec) : Nat :=
  Nat.pow 2 spec.pointerBits

/-- Check that `[addr, addr + len)` excludes NULL (`addr >= 1`) and satisfies
strict non-wraparound (`addr + len < 2^spec.pointerBits`) so that even the
one-past-the-end pointer never wraps to `0` (`NULL`). -/
@[expose] def addrRangeFitsPointerBits (spec : AsmStackSpec)
    (addr len : Nat) : Bool :=
  Nat.blt 0 addr &&
  Nat.blt (addr + len) (maxAddrBound spec)

/-- Check that the protected stack and caller-frame region
`[entrySp - spec.stackHeadroomBytes, entrySp + callerFrameBytes)` excludes
NULL (`spec.stackHeadroomBytes < entrySp`, so `stackLo >= 1`) and satisfies
strict non-wraparound (`entrySp + callerFrameBytes < 2^spec.pointerBits`). -/
@[expose] def stackRegionFitsPointerBits (spec : AsmStackSpec)
    (entrySp callerFrameBytes : Nat) : Bool :=
  Nat.blt spec.stackHeadroomBytes entrySp &&
  Nat.blt (entrySp + callerFrameBytes) (maxAddrBound spec)

/-! ## Section 2: Architecture-Scoped Three-Class Flag Discipline -/

/-- Class 1: Integer condition flags (`x86 EFLAGS.{CF,PF,AF,ZF,SF,OF}` /
`AArch64 NZCV`). -/
structure CondFlags where
  cf : Bool
  pf : Bool
  af : Bool
  zf : Bool
  sf : Bool
  of : Bool

/-- Structural equality on `CondFlags`. -/
@[expose] def CondFlags.beq (a b : CondFlags) : Bool :=
  flagBoolEq a.cf b.cf &&
  flagBoolEq a.pf b.pf &&
  flagBoolEq a.af b.af &&
  flagBoolEq a.zf b.zf &&
  flagBoolEq a.sf b.sf &&
  flagBoolEq a.of b.of

/-- Class 2: Sticky FP/SIMD exception and saturation status (`MXCSR[5:0]`,
x87 FSW condition codes `C0..C3` & sticky exception bits, AArch64 `FPSR`
including cumulative saturation bit `QC`, and RISC-V `fflags` + `vxsat`). -/
structure StickyFpSimdStatus where
  invalidOp   : Bool
  denormal    : Bool
  divByZero   : Bool
  overflow    : Bool
  underflow   : Bool
  inexact     : Bool
  aarch64Qc   : Bool
  x87C0       : Bool := false
  x87C1       : Bool := false
  x87C2       : Bool := false
  x87C3       : Bool := false
  x87ExcFlags : UInt8 := 0
  rvFflags    : UInt8 := 0
  rvVxsat     : Bool := false

/-- Structural equality on `StickyFpSimdStatus`. -/
@[expose] def StickyFpSimdStatus.beq (a b : StickyFpSimdStatus) : Bool :=
  flagBoolEq a.invalidOp b.invalidOp &&
  flagBoolEq a.denormal b.denormal &&
  flagBoolEq a.divByZero b.divByZero &&
  flagBoolEq a.overflow b.overflow &&
  flagBoolEq a.underflow b.underflow &&
  flagBoolEq a.inexact b.inexact &&
  flagBoolEq a.aarch64Qc b.aarch64Qc &&
  flagBoolEq a.x87C0 b.x87C0 &&
  flagBoolEq a.x87C1 b.x87C1 &&
  flagBoolEq a.x87C2 b.x87C2 &&
  flagBoolEq a.x87C3 b.x87C3 &&
  Nat.beq a.x87ExcFlags.toNat b.x87ExcFlags.toNat &&
  Nat.beq a.rvFflags.toNat b.rvFflags.toNat &&
  flagBoolEq a.rvVxsat b.rvVxsat

/-- RISC-V vector configuration CSRs (`vtype`, `vl`, `vxrm`): volatile across
`CallProtocol` and `InlineAsm` without `preserves_flags`, yet required restored
under `options(preserves_flags)` per the Rust Reference. -/
structure RiscvVecConfig where
  vtype : UInt64 := 0
  vl    : UInt64 := 0
  vxrm  : UInt8 := 0

/-- Structural equality on `RiscvVecConfig`. -/
@[expose] def RiscvVecConfig.beq (a b : RiscvVecConfig) : Bool :=
  Nat.beq a.vtype.toNat b.vtype.toNat &&
  Nat.beq a.vl.toNat b.vl.toNat &&
  Nat.beq a.vxrm.toNat b.vxrm.toNat

/-- Class 3: ABI-invariant control flags (`x86 EFLAGS.DF = 0`, `MXCSR[15:6]`
rounding/FTZ/DAZ control, x87 empty tag word & `FCW`, AArch64 `FPCR` control,
and RISC-V `vstart = 0` & FP rounding mode `frm`). -/
structure InvariantControlFlags where
  x86DFZero     : Bool := true
  mxcsrControl  : UInt16 := 0x1f80
  x87TagEmpty   : Bool := true
  x87Fcw        : UInt16 := 0x037f
  fpcrControl   : UInt32 := 0
  rvvVstartZero : Bool := true
  rvFrm         : UInt8 := 0

/-- Architecture-scoped check that Class-3 control invariants hold on `post`
and preserve caller control modes from `pre`:
- `.x86_64`: `x86DFZero`, `mxcsrControl`, `x87TagEmpty`, and `x87Fcw`.
- `.aarch64`: `fpcrControl`.
- `.riscv64`: `rvvVstartZero` and `rvFrm`. -/
@[expose] def invariantControlOk (arch : TargetArch)
    (pre post : InvariantControlFlags) : Bool :=
  match arch with
  | .x86_64 =>
    pre.x86DFZero &&
    post.x86DFZero &&
    pre.x87TagEmpty &&
    post.x87TagEmpty &&
    Nat.beq post.mxcsrControl.toNat pre.mxcsrControl.toNat &&
    Nat.beq post.x87Fcw.toNat pre.x87Fcw.toNat
  | .aarch64 =>
    Nat.beq post.fpcrControl.toNat pre.fpcrControl.toNat
  | .riscv64 =>
    pre.rvvVstartZero &&
    post.rvvVstartZero &&
    Nat.beq post.rvFrm.toNat pre.rvFrm.toNat

/-- Complete 3-class architectural flag state including RISC-V vector CSRs. -/
structure ArchFlagState where
  condFlags          : CondFlags
  stickyFpSimdStatus : StickyFpSimdStatus
  invariantControl   : InvariantControlFlags
  riscvVecConfig     : RiscvVecConfig := ⟨0, 0, 0⟩

/-- Flag contract across a C/Rust `CallProtocol`: Class 1 and Class 2 are
volatile (caller-saved), while architecture-scoped Class 3 must remain
invariant and preserved. -/
@[expose] def callProtocolFlagsOk (arch : TargetArch)
    (pre post : ArchFlagState) : Bool :=
  invariantControlOk arch pre.invariantControl post.invariantControl

/-- Declarative `core::arch::asm!` option flags (`InlineAsmOptions`). -/
structure InlineAsmOptions where
  nostack        : Bool
  preservesFlags : Bool
  readonly       : Bool
  nomem          : Bool := false
  noreturn       : Bool := false
  pure_          : Bool
  mayUnwind      : Bool

/-- Rust `[asm.options]` option-only combination validity:
- `nomem` and `readonly` are mutually exclusive.
- `pure` requires either `nomem` or `readonly`, and forbids `noreturn`. -/
@[expose] def validInlineAsmOptions (opts : InlineAsmOptions) : Bool :=
  !(opts.nomem && opts.readonly) &&
  (!opts.pure_ || ((opts.nomem || opts.readonly) && !opts.noreturn))

/-- Whether `ops` contains at least one non-discarded value-producing output
operand (`.outEarly`, `.lateout`, `.inout_`, `.inlateout`). -/
@[expose] def hasValueOutputOperand (ops : List AsmOperandSpec) : Bool :=
  ops.foldr (fun o acc => o.kind.isValueOutput || acc) false

/-- Whether `ops` contains any output-bearing or clobber operand. -/
@[expose] def hasAnyOutputOperand (ops : List AsmOperandSpec) : Bool :=
  ops.foldr (fun o acc => o.kind.isOutput || acc) false

/-- Full operand- and label-aware Rust Reference (`Inline Assembly — Options`)
and `rustc` (`AsmMayUnwind`) site-validity check extending
`validInlineAsmOptions`:
- `options(pure)` requires `validInlineAsmOptions`, at least one non-discarded
  value output operand (`out`/`lateout`/`inout`/`inlateout`; discarded
  `out("r") _` clobbers do not satisfy `pure`), and zero `asm_goto` labels.
- `options(noreturn)` forbids all output operands (`out`, `lateout`, `inout`,
  `inlateout`, and clobbers).
- `options(may_unwind)` forbids `asm_goto` label operands (`numLabels = 0`),
  matching `rustc`'s `AsmMayUnwind` rejection. -/
@[expose] def validInlineAsmSite (opts : InlineAsmOptions)
    (ops : List AsmOperandSpec) (numLabels : Nat) : Bool :=
  validInlineAsmOptions opts &&
  (!opts.pure_ || (hasValueOutputOperand ops && Nat.beq numLabels 0)) &&
  (!opts.noreturn || !hasAnyOutputOperand ops) &&
  (!opts.mayUnwind || Nat.beq numLabels 0)

/-- Stage-1 inline-assembly summary contract binding a concrete `asm!` site
`siteId`, its declared `InlineAsmOptions`, operand list `operands`, and
`asm_goto` label count `numLabels` to pre/post relations over `State`. -/
structure InlineAsmContractSummary (State : Type) where
  siteId    : String
  options   : InlineAsmOptions
  operands  : List AsmOperandSpec
  numLabels : Nat
  pre       : State → Prop
  post      : State → State → Prop

/-- Stage-1 admission judgment for an `InlineAsmContractSummary` against a
disclosed inline-assembly site ledger `disclosedSites`, enforcing
`validInlineAsmSite` over `(options, operands, numLabels)`. -/
@[expose] def InlineAsmSummaryAdmitted {State : Type}
    (disclosedSites : List String)
    (summary : InlineAsmContractSummary State) : Prop :=
  summary.siteId ≠ "" ∧
  summary.siteId ∈ disclosedSites ∧
  validInlineAsmSite summary.options summary.operands summary.numLabels = true

/-- Architecture-scoped flag contract across an `InlineAsm` exit:
- Class 3 for `arch` is always required invariant and preserved.
- Whenever `opts.preservesFlags = true` (even if `clobberAbi = true`), Class 1
  (`condFlags`), Class 2 (`stickyFpSimdStatus`, including x87 FSW and RISC-V
  `fflags`/`vxsat`), and RISC-V `riscvVecConfig` (`vtype`, `vl`, `vxrm`) must
  all be restored.
- When `opts.preservesFlags = false`, Class 1, Class 2, and `riscvVecConfig`
  are volatile. -/
@[expose] def inlineAsmFlagsOk (arch : TargetArch) (opts : InlineAsmOptions)
    (_clobberAbi : Bool) (pre post : ArchFlagState) : Bool :=
  let ctrlOk :=
    invariantControlOk arch pre.invariantControl post.invariantControl
  if opts.preservesFlags then
    ctrlOk &&
    CondFlags.beq post.condFlags pre.condFlags &&
    StickyFpSimdStatus.beq post.stickyFpSimdStatus pre.stickyFpSimdStatus &&
    RiscvVecConfig.beq post.riscvVecConfig pre.riscvVecConfig
  else
    ctrlOk

/-- RISC-V `preserves_flags` coverage theorem: mutating any of the 6 RISC-V
FP/vector CSRs (`fflags`, `vxsat`, `vtype`, `vl`, `vxrm`, `frm`) or `vstart`
is rejected under `.riscv64` `preservesFlags = true`, while volatile CSRs
(`fflags`, `vxsat`, `vtype`, `vl`, `vxrm`) are permitted across `CallProtocol`
and `preservesFlags = false`, and ABI-invariant `frm`/`vstart` are enforced
across both (`[propext]`). -/
theorem riscv64_preservesFlags_fp_and_vec_state_verified :
    let rvCtrl : InvariantControlFlags :=
      { x86DFZero := false, mxcsrControl := 0, x87TagEmpty := false,
        x87Fcw := 0, fpcrControl := 0, rvvVstartZero := true, rvFrm := 0 }
    let baseCond : CondFlags := ⟨false, false, false, false, false, false⟩
    let baseSticky : StickyFpSimdStatus :=
      { invalidOp := false, denormal := false, divByZero := false,
        overflow := false, underflow := false, inexact := false,
        aarch64Qc := false }
    let pre : ArchFlagState := ⟨baseCond, baseSticky, rvCtrl, ⟨0, 4, 0⟩⟩
    let mutFflags : ArchFlagState :=
      { pre with stickyFpSimdStatus := { baseSticky with rvFflags := 1 } }
    let mutVxsat : ArchFlagState :=
      { pre with stickyFpSimdStatus := { baseSticky with rvVxsat := true } }
    let mutVtype : ArchFlagState :=
      { pre with riscvVecConfig := { pre.riscvVecConfig with vtype := 8 } }
    let mutVl : ArchFlagState :=
      { pre with riscvVecConfig := { pre.riscvVecConfig with vl := 16 } }
    let mutVxrm : ArchFlagState :=
      { pre with riscvVecConfig := { pre.riscvVecConfig with vxrm := 2 } }
    let mutFrm : ArchFlagState :=
      { pre with invariantControl := { rvCtrl with rvFrm := 1 } }
    let mutVstart : ArchFlagState :=
      { pre with invariantControl := { rvCtrl with rvvVstartZero := false } }
    let optsPres : InlineAsmOptions :=
      { nostack := true, preservesFlags := true, readonly := false,
        nomem := false, noreturn := false, pure_ := false, mayUnwind := false }
    let optsNoPres : InlineAsmOptions :=
      { optsPres with preservesFlags := false }
    callProtocolFlagsOk .riscv64 pre mutFflags = true ∧
    callProtocolFlagsOk .riscv64 pre mutVxsat = true ∧
    callProtocolFlagsOk .riscv64 pre mutVtype = true ∧
    callProtocolFlagsOk .riscv64 pre mutVl = true ∧
    callProtocolFlagsOk .riscv64 pre mutVxrm = true ∧
    inlineAsmFlagsOk .riscv64 optsNoPres false pre mutFflags = true ∧
    inlineAsmFlagsOk .riscv64 optsNoPres false pre mutVtype = true ∧
    inlineAsmFlagsOk .riscv64 optsPres false pre mutFflags = false ∧
    inlineAsmFlagsOk .riscv64 optsPres false pre mutVxsat = false ∧
    inlineAsmFlagsOk .riscv64 optsPres false pre mutVtype = false ∧
    inlineAsmFlagsOk .riscv64 optsPres false pre mutVl = false ∧
    inlineAsmFlagsOk .riscv64 optsPres false pre mutVxrm = false ∧
    callProtocolFlagsOk .riscv64 pre mutFrm = false ∧
    inlineAsmFlagsOk .riscv64 optsNoPres false pre mutFrm = false ∧
    inlineAsmFlagsOk .riscv64 optsPres false pre mutFrm = false ∧
    callProtocolFlagsOk .riscv64 pre mutVstart = false ∧
    inlineAsmFlagsOk .riscv64 optsNoPres false pre mutVstart = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl⟩

/-- Key 3-class & arch-scoping asymmetry theorem:
- Mutating Class 2 sticky FP/SIMD status (`inexact`/`QC`) is valid across a
  `CallProtocol` and under `preservesFlags = false`, yet rejected whenever
  `preservesFlags = true` (with or without `clobber_abi`).
- On `.x86_64`, violating `x86DFZero` or `x87TagEmpty` fails both
  `CallProtocol` and `InlineAsm`, while `rvvVstartZero = false` does not fail
  `.x86_64` (and `x86DFZero = false` does not fail `.aarch64`) (`[propext]`).
-/
theorem stickyFpStatus_call_volatile_yet_asm_preservesFlags_required :
    let x86Ctrl : InvariantControlFlags :=
      { x86DFZero := true, mxcsrControl := 0x1f80, x87TagEmpty := true,
        x87Fcw := 0x037f, fpcrControl := 0, rvvVstartZero := false }
    let armCtrl : InvariantControlFlags :=
      { x86DFZero := false, mxcsrControl := 0, x87TagEmpty := false,
        x87Fcw := 0, fpcrControl := 0x0100, rvvVstartZero := false }
    let baseCond : CondFlags := ⟨false, false, false, true, false, false⟩
    let pre : ArchFlagState :=
      ⟨baseCond,
       { invalidOp := false, denormal := false, divByZero := false,
         overflow := false, underflow := false, inexact := false,
         aarch64Qc := false, x87C0 := false, x87C1 := false, x87C2 := false,
         x87C3 := false, x87ExcFlags := 0 },
       x86Ctrl, ⟨0, 0, 0⟩⟩
    let postStickyMut : ArchFlagState :=
      { pre with
        stickyFpSimdStatus :=
          { pre.stickyFpSimdStatus with inexact := true, aarch64Qc := true } }
    let postX87FswMut : ArchFlagState :=
      { pre with
        stickyFpSimdStatus :=
          { pre.stickyFpSimdStatus with x87C0 := true, x87ExcFlags := 0x20 } }
    let postBadDf : ArchFlagState :=
      { pre with invariantControl := { x86Ctrl with x86DFZero := false } }
    let postBadX87 : ArchFlagState :=
      { pre with invariantControl := { x86Ctrl with x87TagEmpty := false } }
    let preArm : ArchFlagState :=
      { pre with invariantControl := armCtrl }
    let postArmBadFpcr : ArchFlagState :=
      { pre with invariantControl := { armCtrl with fpcrControl := 0x0200 } }
    let optsPreserves : InlineAsmOptions :=
      { nostack := true, preservesFlags := true, readonly := false,
        nomem := false, noreturn := false, pure_ := false, mayUnwind := false }
    let optsNoPreserves : InlineAsmOptions :=
      { optsPreserves with preservesFlags := false }
    callProtocolFlagsOk .x86_64 pre postStickyMut = true ∧
    inlineAsmFlagsOk .x86_64 optsNoPreserves true pre postStickyMut = true ∧
    inlineAsmFlagsOk .x86_64 optsPreserves true pre postStickyMut = false ∧
    inlineAsmFlagsOk .x86_64 optsPreserves false pre postStickyMut = false ∧
    callProtocolFlagsOk .x86_64 pre postX87FswMut = true ∧
    inlineAsmFlagsOk .x86_64 optsNoPreserves true pre postX87FswMut = true ∧
    inlineAsmFlagsOk .x86_64 optsPreserves false pre postX87FswMut = false ∧
    callProtocolFlagsOk .x86_64 pre postBadDf = false ∧
    callProtocolFlagsOk .x86_64 pre postBadX87 = false ∧
    inlineAsmFlagsOk .x86_64 optsNoPreserves false pre postBadDf = false ∧
    callProtocolFlagsOk .aarch64 preArm preArm = true ∧
    callProtocolFlagsOk .aarch64 preArm postArmBadFpcr = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 3: Exit-Edge `SP`, `noreturn`, Red-Zone, & MIR Stack Bridge -/

/-- Non-diverging, non-unwinding exit edge of an `InlineAsm` block. -/
inductive AsmExitEdge where
  | fallthrough
  | labelJump (labelIdx : Nat)

/-- Recorded stack pointer value at a concrete `InlineAsm` exit edge. -/
structure AsmExitRecord where
  edge   : AsmExitEdge
  exitSp : Nat

/-- Entry `SP` must be restored on every exit edge (both `.fallthrough` and
every `.labelJump labelIdx`), checked via `List.foldr` (`0` `._unsafe_rec`). -/
@[expose] def validAsmExitSp (entrySp : Nat)
    (exits : List AsmExitRecord) : Bool :=
  exits.foldr (fun rec acc => Nat.beq rec.exitSp entrySp && acc) true

/-- Check whether a single exit edge is permitted by `opts.noreturn` and
`declaredLabels`:
- `.fallthrough` is rejected whenever `opts.noreturn = true`.
- `.labelJump lbl` is allowed iff `lbl` appears in `declaredLabels`. -/
@[expose] def asmExitEdgePermitted (opts : InlineAsmOptions)
    (declaredLabels : List Nat) (edge : AsmExitEdge) : Bool :=
  match edge with
  | .fallthrough => !opts.noreturn
  | .labelJump lbl => natMemList lbl declaredLabels

/-- Full exit-edge check combining `validInlineAsmOptions`, `pure`/`may_unwind`
label exclusion, `SP` restoration, `noreturn`, and declared-label discipline
(`List.foldr`, `0` `._unsafe_rec`). -/
@[expose] def validAsmExits (opts : InlineAsmOptions) (entrySp : Nat)
    (declaredLabels : List Nat) (exits : List AsmExitRecord) : Bool :=
  let noLabels :=
    match declaredLabels with
    | [] => true
    | _ :: _ => false
  validInlineAsmOptions opts &&
  (!opts.pure_ || noLabels) &&
  (!opts.mayUnwind || noLabels) &&
  exits.foldr
    (fun rec acc =>
      Nat.beq rec.exitSp entrySp &&
      asmExitEdgePermitted opts declaredLabels rec.edge &&
      acc)
    true

/-- Even when `.fallthrough` restores `SP`, a `.labelJump` exit with drifted
`SP` is rejected (`[]` axioms). -/
theorem asm_label_jump_sp_drift_rejected :
    let entrySp : Nat := 65536
    let okExits : List AsmExitRecord :=
      [⟨.fallthrough, 65536⟩, ⟨.labelJump 0, 65536⟩]
    let driftedLabel : List AsmExitRecord :=
      [⟨.fallthrough, 65536⟩, ⟨.labelJump 0, 65520⟩]
    validAsmExitSp entrySp okExits = true ∧
    validAsmExitSp entrySp driftedLabel = false :=
  ⟨rfl, rfl⟩

/-- `noreturn = true` rejects `.fallthrough` exits while allowing declared
`.labelJump` exits, and invalid option combinations (`nomem && readonly`,
`pure` without `nomem`/`readonly`, or `pure && noreturn`) are rejected (`[]`
axioms). -/
theorem asm_noreturn_rejects_fallthrough_allows_declared_label :
    let optsNoRet : InlineAsmOptions :=
      { nostack := true, preservesFlags := false, readonly := false,
        nomem := false, noreturn := true, pure_ := false, mayUnwind := false }
    let optsBadCombo1 : InlineAsmOptions :=
      { optsNoRet with noreturn := false, nomem := true, readonly := true }
    let optsBadCombo2 : InlineAsmOptions :=
      { optsNoRet with noreturn := false, pure_ := true }
    let optsBadCombo3 : InlineAsmOptions :=
      { optsNoRet with readonly := true, pure_ := true }
    let entrySp : Nat := 65536
    let fallExit : List AsmExitRecord := [⟨.fallthrough, entrySp⟩]
    let lblExit : List AsmExitRecord := [⟨.labelJump 0, entrySp⟩]
    let undeclExit : List AsmExitRecord := [⟨.labelJump 2, entrySp⟩]
    validAsmExits optsNoRet entrySp [0, 1] fallExit = false ∧
    validAsmExits optsNoRet entrySp [0, 1] lblExit = true ∧
    validAsmExits optsNoRet entrySp [0, 1] undeclExit = false ∧
    validInlineAsmOptions optsBadCombo1 = false ∧
    validInlineAsmOptions optsBadCombo2 = false ∧
    validInlineAsmOptions optsBadCombo3 = false ∧
    validAsmExits optsBadCombo1 entrySp [0] lblExit = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Pure computable lookup of a MIR `Allocation` in `MemoryState` (`List.foldr`,
`0` `noncomputable`, `0` `._unsafe_rec`). -/
@[expose] def lookupMirAlloc (allocId : AllocId)
    (m : MemoryState) : Option Allocation :=
  m.allocations.foldr
    (fun a acc => if Nat.beq a.allocId allocId then some a else acc)
    none

/-- Pure computable MIR permission check for a byte range `[off, off + len)`
within allocation `allocId` of `m`: allocation must be live, in-bounds, and
mutable on writes. -/
@[expose] def mirMemPermitsAccess (m : MemoryState) (allocId off len : Nat)
    (isWrite : Bool) : Bool :=
  match lookupMirAlloc allocId m with
  | none => false
  | some a =>
    let mutOk :=
      if isWrite then
        match a.mutability with
        | .mut => true
        | .shared => false
      else
        true
    a.live && mutOk && Nat.ble (off + len) a.bytes.length

/-- Memory access classification for `InlineAsm` stack/red-zone checks. -/
inductive MemAccessKind where
  | read
  | write
  | exec

/-- Address-space byte interval `[start, start + len)`. -/
structure ByteInterval where
  start : Nat
  len   : Nat

/-- Computable disjointness of two half-open byte intervals, delegating directly
to `Anneal.ByteSubLens.rangesDisjoint`. -/
@[expose] def byteIntervalsDisjoint (a b : ByteInterval) : Bool :=
  rangesDisjoint a.start a.len b.start b.len

/-- Protected stack-scratch and caller-frame/return-address region
`[entrySp - spec.stackHeadroomBytes, entrySp + callerFrameBytes)`.
Note (fail-closed coverage boundary): treating the entire caller-frame span
`[entrySp, entrySp + callerFrameBytes)` as protected prevents exposing a
Rust-frame stack buffer living inside `[entrySp, entrySp + callerFrameBytes)`
into `asm!` without splitting the caller frame per slot. Only heap/`.rodata`
buffers below `entrySp - stackHeadroomBytes` and buffers at or above
`entrySp + callerFrameBytes` are currently exposable. -/
@[expose] def protectedStackRegion (spec : AsmStackSpec)
    (entrySp callerFrameBytes : Nat) : ByteInterval :=
  ⟨entrySp - spec.stackHeadroomBytes,
   spec.stackHeadroomBytes + callerFrameBytes⟩

/-- Explicit base-address placement of an exposed MIR allocation (supporting
heap/`.rodata` below the stack as well as caller buffers above the caller
frame), binding raw `InlineAsm` addresses to `(allocId, offset)` pairs. -/
structure ExposedMirAlloc where
  allocId  : AllocId
  baseAddr : Nat

/-- Resolve `addr` against `exposedAllocs` via `List.foldr` (`0` `._unsafe_rec`)
anywhere in address space (both heap/`.rodata` below the stack and buffers
above the caller frame), failing closed on NULL (`addr = 0`) and returning
`true` iff some exposed allocation placement in `m` covers `[addr, addr + len)`
with the required read/write permission. -/
@[expose] def resolveExposedMirAccess (m : MemoryState)
    (exposedAllocs : List ExposedMirAlloc) (addr len : Nat)
    (isWrite : Bool) : Bool :=
  Nat.blt 0 addr &&
  exposedAllocs.foldr
    (fun exp acc =>
      let hereOk :=
        Nat.ble exp.baseAddr addr &&
        mirMemPermitsAccess m exp.allocId (addr - exp.baseAddr) len isWrite
      hereOk || acc)
    false

/-- Stack-relative or exposed-memory access event emitted by an `InlineAsm`
block. -/
structure AsmStackAccess where
  addr : Nat
  len  : Nat
  kind : MemAccessKind

/-- Unified stack, active red-zone, `curSp`, pointer-width bound,
`nomem`/`readonly`, and exposed MIR memory access check:
- Gates on `validInlineAsmOptions opts`,
  `stackRegionFitsPointerBits spec entrySp callerFrameBytes`,
  `addrRangeFitsPointerBits spec acc.addr acc.len`, and `curSp` within
  `[entrySp - spec.stackHeadroomBytes, entrySp]`.
- `opts.nomem = true` forbids both `.read` and `.write`; `opts.readonly = true`
  forbids `.write`; `.exec` is always forbidden.
- Accesses strictly inside the scratch region
  `[entrySp - spec.stackHeadroomBytes, entrySp)`:
  * fault whenever `opts.nostack = true`,
  * require `spec.redZoneBytes <= curSp` (fail closed on underflow) and lying
    inside `[curSp - spec.redZoneBytes, entrySp)` (so `redZoneBytes = 128` on
    SysV vs `0` on Win64/AAPCS64 is actively enforced relative to `curSp`).
- Accesses strictly disjoint from `protectedStackRegion`:
  * resolve via `resolveExposedMirAccess` in `m` (supporting both heap/`.rodata`
    below `entrySp - stackHeadroomBytes` and caller buffers at or above
    `entrySp + callerFrameBytes`).
- Accesses touching `[entrySp, entrySp + callerFrameBytes)` or straddling
  stack-region boundaries fail closed. -/
@[expose] def asmStackAccessValid (spec : AsmStackSpec)
    (opts : InlineAsmOptions) (m : MemoryState)
    (entrySp curSp callerFrameBytes : Nat)
    (exposedAllocs : List ExposedMirAlloc) (acc : AsmStackAccess) : Bool :=
  let isRead :=
    match acc.kind with
    | .read => true
    | .write | .exec => false
  let isWrite :=
    match acc.kind with
    | .write => true
    | .read | .exec => false
  let isExec :=
    match acc.kind with
    | .exec => true
    | .read | .write => false
  let stackLo := entrySp - spec.stackHeadroomBytes
  if !validInlineAsmOptions opts ||
     !stackRegionFitsPointerBits spec entrySp callerFrameBytes ||
     !addrRangeFitsPointerBits spec acc.addr acc.len ||
     !Nat.ble stackLo curSp ||
     !Nat.ble curSp entrySp then
    false
  else if isExec || (opts.nomem && (isRead || isWrite)) ||
          (opts.readonly && isWrite) then
    false
  else if byteIntervalsDisjoint ⟨acc.addr, acc.len⟩
      (protectedStackRegion spec entrySp callerFrameBytes) then
    resolveExposedMirAccess m exposedAllocs acc.addr acc.len isWrite
  else if Nat.ble stackLo acc.addr && Nat.ble (acc.addr + acc.len) entrySp then
    !opts.nostack &&
    Nat.ble spec.redZoneBytes curSp &&
    Nat.ble (curSp - spec.redZoneBytes) acc.addr
  else
    false

/-- `opts.nomem = true` universally rejects both `.read` and `.write` accesses
in `asmStackAccessValid` (`[]` axioms). -/
theorem asm_nomem_rejects_read_and_write (spec : AsmStackSpec)
    (opts : InlineAsmOptions) (hNomem : opts.nomem = true)
    (m : MemoryState) (entrySp curSp callerFrameBytes : Nat)
    (exposed : List ExposedMirAlloc) (addr len : Nat) :
    asmStackAccessValid spec opts m entrySp curSp callerFrameBytes exposed
      ⟨addr, len, .read⟩ = false ∧
    asmStackAccessValid spec opts m entrySp curSp callerFrameBytes exposed
      ⟨addr, len, .write⟩ = false := by
  unfold asmStackAccessValid
  dsimp only
  rw [hNomem]
  cases (!validInlineAsmOptions opts ||
      !stackRegionFitsPointerBits spec entrySp callerFrameBytes ||
      !addrRangeFitsPointerBits spec addr len ||
      !Nat.ble (entrySp - spec.stackHeadroomBytes) curSp ||
      !Nat.ble curSp entrySp) with
  | true => exact ⟨rfl, rfl⟩
  | false => exact ⟨rfl, rfl⟩

/-- Active `redZoneBytes` + `curSp` + heap-below-stack theorem:
- At `curSp = entrySp`, `[entrySp - 16, entrySp - 8)` succeeds on SysV
  (`redZoneBytes = 128`, `nostack = false`), fails under `nostack = true`,
  and FAILS on Win64 and AAPCS64 (`redZoneBytes = 0`) until `curSp` is lowered
  to `entrySp - 16`.
- A heap MIR buffer placed below the stack (`baseAddr = 16384 < stackLo`) and a
  caller buffer above `[entrySp, entrySp + 8)` are both admitted, while an
  access overlapping the return-address slot `[entrySp, entrySp + 8)` or
  overflowing stack headroom fails (`[]` axioms). -/
theorem sysv_redzone_clobber_rejected_under_nostack :
    let sysv := sysvX64StackSpec 4096
    let win64 := win64StackSpec 4096
    let arm64 := aapcs64StackSpec 4096
    let entrySp : Nat := 65536
    let mem : MemoryState :=
      { nextAllocId := 3
        allocations :=
          [{ allocId := 1, alignLog2 := 3, mutability := .mut,
             bytes := [.init 0, .init 0, .init 0, .init 0,
                       .init 0, .init 0, .init 0, .init 0],
             live := true },
           { allocId := 2, alignLog2 := 4, mutability := .mut,
             bytes := [.init 1, .init 2, .init 3, .init 4,
                       .init 5, .init 6, .init 7, .init 8],
             live := true }] }
    let exposed : List ExposedMirAlloc := [⟨1, entrySp + 8⟩, ⟨2, 16384⟩]
    let optsNoStack : InlineAsmOptions :=
      { nostack := true, preservesFlags := false, readonly := false,
        nomem := false, noreturn := false, pure_ := false, mayUnwind := false }
    let optsWithStack : InlineAsmOptions :=
      { optsNoStack with nostack := false }
    let redzoneWrite : AsmStackAccess := ⟨entrySp - 16, 8, .write⟩
    let headroomOverflow : AsmStackAccess := ⟨entrySp - 4104, 8, .write⟩
    let retSlotWrite : AsmStackAccess := ⟨entrySp, 8, .write⟩
    let aboveSpLiveWrite : AsmStackAccess := ⟨entrySp + 8, 8, .write⟩
    let heapBelowStackWrite : AsmStackAccess := ⟨16384, 8, .write⟩
    let aboveSpUnmappedWrite : AsmStackAccess := ⟨entrySp + 64, 8, .write⟩
    sysv.redZoneBytes = 128 ∧
    asmStackAccessValid sysv optsNoStack mem entrySp entrySp 8 exposed
      redzoneWrite = false ∧
    asmStackAccessValid sysv optsWithStack mem entrySp entrySp 8 exposed
      redzoneWrite = true ∧
    asmStackAccessValid win64 optsWithStack mem entrySp entrySp 8 exposed
      redzoneWrite = false ∧
    asmStackAccessValid arm64 optsWithStack mem entrySp entrySp 8 exposed
      redzoneWrite = false ∧
    asmStackAccessValid win64 optsWithStack mem entrySp (entrySp - 16) 8 exposed
      redzoneWrite = true ∧
    asmStackAccessValid arm64 optsWithStack mem entrySp (entrySp - 16) 8 exposed
      redzoneWrite = true ∧
    asmStackAccessValid sysv optsWithStack mem entrySp (entrySp - 4096) 8
      exposed headroomOverflow = false ∧
    asmStackAccessValid sysv optsNoStack mem entrySp entrySp 8 exposed
      retSlotWrite = false ∧
    asmStackAccessValid sysv optsNoStack mem entrySp entrySp 8 exposed
      aboveSpLiveWrite = true ∧
    asmStackAccessValid sysv optsNoStack mem entrySp entrySp 8 exposed
      heapBelowStackWrite = true ∧
    asmStackAccessValid sysv optsNoStack mem entrySp entrySp 8 exposed
      aboveSpUnmappedWrite = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 4: Total Structural `IsaAccessFootprint` Observer -/

/-- Memory-effect event emitted by an ISA instruction step. -/
inductive IsaEffectEvent where
  | requireRead  (addr len : Nat)
  | requireWrite (addr len : Nat)
  | requireExec  (addr len : Nat)
  | regOnly

/-- Aggregated read/write/exec memory footprint collected from ISA effects
without erasing read/write/exec access requirements. -/
structure IsaAccessFootprint where
  readAddrs  : List ByteInterval
  writeAddrs : List ByteInterval
  execAddrs  : List ByteInterval

/-- Total structural `List.foldr` footprint observer (`0` `partial`, `0`
`._unsafe_rec`). -/
@[expose] def observeIsaEffects
    (events : List IsaEffectEvent) : IsaAccessFootprint :=
  events.foldr
    (fun ev fp =>
      match ev with
      | .requireRead a l =>
        { fp with readAddrs := ⟨a, l⟩ :: fp.readAddrs }
      | .requireWrite a l =>
        { fp with writeAddrs := ⟨a, l⟩ :: fp.writeAddrs }
      | .requireExec a l =>
        { fp with execAddrs := ⟨a, l⟩ :: fp.execAddrs }
      | .regOnly => fp)
    ⟨[], [], []⟩

/-- Check via `List.foldr` that a single interval `iv` is disjoint from every
interval in `frames`. -/
@[expose] def intervalDisjointFromList (iv : ByteInterval)
    (frames : List ByteInterval) : Bool :=
  frames.foldr (fun fr acc => byteIntervalsDisjoint iv fr && acc) true

/-- Check via `List.foldr` that every interval in `ivs` is disjoint from every
protected frame in `frames`. -/
@[expose] def intervalsDisjointFromFrames (ivs frames : List ByteInterval) :
    Bool :=
  ivs.foldr (fun iv acc => intervalDisjointFromList iv frames && acc) true

/-- Check that every write interval in a footprint is disjoint from all live
Rust stack frames, every interval excludes NULL (`start >= 1`) and satisfies
strict non-wraparound (`start + len < 2^spec.pointerBits`), and every
read/write interval touching `[entrySp - spec.stackHeadroomBytes, entrySp)`
requires `spec.redZoneBytes <= curSp` (no underflow) and lies strictly inside
`[curSp - spec.redZoneBytes, entrySp)` (rejecting boundary-straddling accesses
starting below `stackLo` or crossing `entrySp`, matching `asmStackAccessValid`)
while enforcing `validInlineAsmOptions`, `nomem`, `readonly`, and `nostack`. -/
@[expose] def isaFootprintSafe (spec : AsmStackSpec)
    (opts : InlineAsmOptions) (entrySp curSp : Nat)
    (liveRustFrames : List ByteInterval) (fp : IsaAccessFootprint) : Bool :=
  let stackLo := entrySp - spec.stackHeadroomBytes
  let scratchWin : ByteInterval := ⟨stackLo, spec.stackHeadroomBytes⟩
  let intervalStackOk (iv : ByteInterval) : Bool :=
    addrRangeFitsPointerBits spec iv.start iv.len &&
    (if byteIntervalsDisjoint iv scratchWin then
      true
    else
      !opts.nostack &&
      Nat.ble stackLo iv.start &&
      Nat.ble spec.redZoneBytes curSp &&
      Nat.ble (curSp - spec.redZoneBytes) iv.start &&
      Nat.ble (iv.start + iv.len) entrySp)
  let spOk :=
    validInlineAsmOptions opts &&
    stackRegionFitsPointerBits spec entrySp 0 &&
    Nat.ble stackLo curSp &&
    Nat.ble curSp entrySp
  let framesFit :=
    liveRustFrames.foldr
      (fun fr acc => addrRangeFitsPointerBits spec fr.start fr.len && acc)
      true
  let execsFit :=
    fp.execAddrs.foldr
      (fun iv acc => addrRangeFitsPointerBits spec iv.start iv.len && acc)
      true
  let writesDisjoint := intervalsDisjointFromFrames fp.writeAddrs liveRustFrames
  let nomemOk := !opts.nomem || (fp.readAddrs.isEmpty && fp.writeAddrs.isEmpty)
  let readonlyOk := !opts.readonly || fp.writeAddrs.isEmpty
  let readsStackOk :=
    fp.readAddrs.foldr (fun iv acc => intervalStackOk iv && acc) true
  let writesStackOk :=
    fp.writeAddrs.foldr (fun iv acc => intervalStackOk iv && acc) true
  spOk && framesFit && execsFit && writesDisjoint && nomemOk && readonlyOk &&
    readsStackOk && writesStackOk

/-- Total observer detects live Rust frame clobbers above `SP`, `nostack`
scratch writes below `SP`, Win64 red-zone writes at `curSp = entrySp`,
boundary-straddling writes starting below `stackLo` (`⟨61436, 4100⟩` and
`⟨61436, 8⟩`), and `nomem` read/write violations, while admitting bounded SysV
red-zone scratch disjoint from live Rust frames (`[]` axioms). -/
theorem isa_observer_frame_disjointness_verified :
    let sysv := sysvX64StackSpec 4096
    let win64 := win64StackSpec 4096
    let entrySp : Nat := 65536
    let rustFrames : List ByteInterval := [⟨65536, 64⟩, ⟨65600, 32⟩]
    let optsStack : InlineAsmOptions :=
      { nostack := false, preservesFlags := false, readonly := false,
        nomem := false, noreturn := false, pure_ := false, mayUnwind := false }
    let optsNoStack : InlineAsmOptions := { optsStack with nostack := true }
    let optsNoMem : InlineAsmOptions := { optsStack with nomem := true }
    let fpScratch := observeIsaEffects
      [.requireExec 4096 4, .requireWrite 65520 8, .requireRead 65520 8,
       .regOnly]
    let fpReadOnly := observeIsaEffects
      [.requireExec 4096 4, .requireRead 65600 8]
    let fpClobberFrame := observeIsaEffects
      [.requireExec 4096 4, .requireWrite 65544 8]
    let fpCrossAll := observeIsaEffects [.requireWrite 61436 4100]
    let fpCrossLo := observeIsaEffects [.requireWrite 61436 8]
    fpScratch.readAddrs = [⟨65520, 8⟩] ∧
    fpScratch.writeAddrs = [⟨65520, 8⟩] ∧
    fpScratch.execAddrs = [⟨4096, 4⟩] ∧
    isaFootprintSafe sysv optsStack entrySp entrySp rustFrames fpScratch =
      true ∧
    isaFootprintSafe win64 optsStack entrySp entrySp rustFrames fpScratch =
      false ∧
    isaFootprintSafe sysv optsNoStack entrySp entrySp rustFrames fpScratch =
      false ∧
    isaFootprintSafe sysv optsNoMem entrySp entrySp rustFrames fpReadOnly =
      false ∧
    isaFootprintSafe sysv optsStack entrySp entrySp rustFrames fpClobberFrame =
      false ∧
    isaFootprintSafe sysv optsNoStack entrySp entrySp rustFrames fpCrossAll =
      false ∧
    isaFootprintSafe sysv optsNoStack entrySp entrySp rustFrames fpCrossLo =
      false ∧
    isaFootprintSafe sysv optsStack entrySp entrySp rustFrames fpCrossLo =
      false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.AsmBridge.FlagsAndStack

end
