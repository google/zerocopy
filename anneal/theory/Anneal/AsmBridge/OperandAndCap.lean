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
public import Anneal.AsmBridge.RegLeaves

public section

namespace Anneal.AsmBridge.OperandAndCap

open Anneal.AsmBridge.RegLeaves

/-!
# Inline-Asm Operand Timing, `clobber_abi`, & Hardware/Vector-ABI Capabilities

Zero-TCB (`0` `noncomputable`, `0` `._unsafe_rec`, axioms `⊆ {propext}`)
contracts for:

1. **Operand Timing & Register-Allocation Admissibility:**
   - `AsmOperandKind` distinguishing `.clobberEarly` (`out("r") _`, conflicts
     with all inputs and outputs) from `.clobberLate` (`lateout("r") _` and
     `clobber_abi` volatile clobbers, which conflict with outputs and early
     clobbers while permitting aliasing with pure `.in_` operands).
   - `inValId? : Option Nat` on `AsmOperandSpec`: permits `(.inlateout, .in_)`
     register coalescing only when both carry matching `some vid` (same entry
     input value), rejecting aliasing when input values may differ.
   - Universal register-polymorphic instantiation across `N`-site inlining or
     loop unrolling (`regPolymorphicScheduleSound`,
     `regPolymorphicUnrollChainSound`).
   - Non-vacuous early-clobber soundness and lateout-aliasing refutation
     (`earlyClobber_prevents_twoStep_sub_clobber`).
2. **`clobber_abi` Callee-Saved Leaf Preservation:**
   - `CalleeSavedSpec` (`sysvCalleeSavedSpec`, `aapcs64CalleeSavedSpec`,
     `win64CalleeSavedSpec`) and `clobberAbiPreservesVecLeaf` modeling both
     AAPCS64 (`V8..V15` preserves `D8..D15` `[63:0]` only) and Win64
     (`XMM6..XMM15` preserves `[127:0]` only).
3. **Architecture-Scoped Hardware, OS `XCR0`, RFC 2396, & Vector-ABI Gating:**
   - `TargetArch` (`.x86_64`, `.aarch64`, `.riscv64`), `CpuFeatureSet` (with
     `osxsave`), `OsSimdState` (with `xcr0Hi16Zmm`), and 3-way RFC 2396
     `FnSafetyKind`.
   - `asmOperandHardwareReady` checking register-index bounds, `osxsave`,
     EVEX `xmm16..31`/`ymm16..31`/`zmm16..31` (`avx512f`, `avx512vl`,
     `xcr0Hi16Zmm`), and strict architecture separation.
   - `callTargetFeatureSafe`, `reifySafeFnPtrAllowed`,
     `abiVectorCallCompatible`, and `classifyAapcs64NeonHva`.
-/

/-! ## Constructive `Bool` and `Nat` Helpers -/

private theorem boolEq_false_true (h : false = true) : False :=
  Bool.noConfusion h

private theorem bandLeft {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => exact False.elim (boolEq_false_true h)
  | true => rfl

private theorem bandRight {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => exact False.elim (boolEq_false_true h)
  | true => exact h

private theorem natBeq_refl (n : Nat) : Nat.beq n n = true := by
  induction n with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBeq_symm (a b : Nat) : Nat.beq a b = Nat.beq b a := by
  revert b
  induction a with
  | zero =>
    intro b
    cases b <;> rfl
  | succ _ ih =>
    intro b
    cases b with
    | zero => rfl
    | succ b' => exact ih b'

private theorem ite_bool_true {α : Type} {b : Bool} {t e : α}
    (hb : b = true) : (if b then t else e) = t := by
  subst hb
  rfl

private theorem ite_bool_false {α : Type} {b : Bool} {t e : α}
    (hb : b = false) : (if b then t else e) = e := by
  subst hb
  rfl

/-- Pure structural equality on `Bool`. -/
@[expose] def capBoolEq (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

/-- Pure implication `a -> b` on `Bool`. -/
@[expose] def capBoolImp (a b : Bool) : Bool :=
  !a || b

/-- Pure `List.foldr` membership check on `List Nat` (`0` `._unsafe_rec`). -/
@[expose] def capNatMem (x : Nat) (xs : List Nat) : Bool :=
  xs.foldr (fun y acc => Nat.beq x y || acc) false

/-! ## Section 1: Target Architecture & Operand Timing Admissibility -/

/-- Target CPU architecture governing register files, hardware capability
checks, and ABI-invariant control flags. -/
inductive TargetArch where
  | x86_64
  | aarch64
  | riscv64

/-- Rust `core::arch::asm!` operand timing and direction kind:
- `.clobberEarly`: explicit early-clobber (`out("r") _`), conflicts with all
  inputs and outputs.
- `.clobberLate`: late clobber (`lateout("r") _` or `clobber_abi(...)`
  volatile register), conflicts with outputs and early clobbers while
  permitting aliasing with pure `.in_` operands. Matching `rustc`'s
  `clobber_abi(...)` lowering, expanding a `clobber_abi` volatile register list
  into `.clobberLate` operands MUST skip any register already bound to an
  explicit output operand (`outEarly`, `lateout`, `inout_`, `inlateout`). -/
inductive AsmOperandKind where
  | in_
  | outEarly
  | lateout
  | inout_
  | inlateout
  | clobberEarly
  | clobberLate

/-- Whether an operand reads an architectural input value on entry. -/
@[expose] def AsmOperandKind.isInput : AsmOperandKind → Bool
  | .in_ | .inout_ | .inlateout => true
  | .outEarly | .lateout | .clobberEarly | .clobberLate => false

/-- Whether an operand writes or clobbers its assigned physical register. -/
@[expose] def AsmOperandKind.isOutput : AsmOperandKind → Bool
  | .outEarly | .lateout | .inout_ | .inlateout
  | .clobberEarly | .clobberLate => true
  | .in_ => false

/-- Whether an operand may overwrite its physical register before all input
operands have been consumed. -/
@[expose] def AsmOperandKind.isEarlyClobber : AsmOperandKind → Bool
  | .outEarly | .inout_ | .clobberEarly => true
  | .in_ | .lateout | .inlateout | .clobberLate => false

/-- Whether an operand is a discarded clobber (`.clobberEarly` or
`.clobberLate`), required for clobber-only register classes such as x86 `k0`
(`kreg0`) and AArch64 SVE predicates `p0..p15` (`preg`). -/
@[expose] def AsmOperandKind.isClobberOnly : AsmOperandKind → Bool
  | .clobberEarly | .clobberLate => true
  | .in_ | .outEarly | .lateout | .inout_ | .inlateout => false

/-- Whether an operand is a value-producing (non-discarded) output operand
(`.outEarly`, `.lateout`, `.inout_`, `.inlateout`). -/
@[expose] def AsmOperandKind.isValueOutput : AsmOperandKind → Bool
  | .outEarly | .lateout | .inout_ | .inlateout => true
  | .in_ | .clobberEarly | .clobberLate => false

/-- Architectural register bank for inline-assembly operands. -/
inductive RegBank where
  | gp
  | vec
  | kMask

/-- Structural equality on `RegBank`. -/
@[expose] def RegBank.beq : RegBank → RegBank → Bool
  | .gp, .gp => true
  | .vec, .vec => true
  | .kMask, .kMask => true
  | _, _ => false

/-- Concrete physical register identifier `(bank, idx)`. -/
structure PhysReg where
  bank : RegBank
  idx  : Nat

/-- Structural equality on `PhysReg`. -/
@[expose] def PhysReg.beq (a b : PhysReg) : Bool :=
  RegBank.beq a.bank b.bank && Nat.beq a.idx b.idx

/-- Declarative inline-assembly operand constraint. Optional `inValId?` tags
entry input values so `(.inlateout, .in_)` coalescing is admitted only when
both operands carry the same entry value identifier (`some vid`). -/
structure AsmOperandSpec where
  kind      : AsmOperandKind
  bank      : RegBank
  widthBits : Nat
  inValId?  : Option Nat := none

/-- Whether two optional entry input value tags witness identical values. -/
@[expose] def sameInputVal (a b : Option Nat) : Bool :=
  match a, b with
  | some x, some y => Nat.beq x y
  | _, _ => false

/-- Total `List.foldr` exact-length zip (`0` `._unsafe_rec`). -/
@[expose] def zipExact {α β : Type} (xs : List α) (ys : List β) :
    Option (List (α × β)) :=
  (xs.foldr
    (fun x go rem =>
      match rem with
      | [] => none
      | y :: yt =>
        match go yt with
        | none => none
        | some ps => some ((x, y) :: ps))
    (fun rem =>
      match rem with
      | [] => some []
      | _ :: _ => none)) ys

/-- Two distinct operand positions conflict when assigned the same physical
register iff:
- both are output-bearing (`.outEarly`, `.lateout`, `.inout_`, `.inlateout`,
  `.clobberEarly`, `.clobberLate`), OR
- one is early-clobber (`.outEarly`, `.inout_`, `.clobberEarly`) and the
  other is input-bearing (`.in_`, `.inout_`, `.inlateout`), OR
- both are input-bearing (`.in_`, `.inout_`, `.inlateout`) without matching
  `some vid` in `inValId?` (a physical register can hold only one entry value,
  so distinct or untagged inputs cannot alias).
Pure `.in_` operands may alias `.lateout` and `.clobberLate` (modeling
`in("rdi") x` combined with `clobber_abi("C")`). -/
@[expose] def operandPairConflicts (p1 p2 : AsmOperandSpec × PhysReg) : Bool :=
  PhysReg.beq p1.2 p2.2 &&
  ((p1.1.kind.isOutput && p2.1.kind.isOutput) ||
   (p1.1.kind.isEarlyClobber && p2.1.kind.isInput) ||
   (p2.1.kind.isEarlyClobber && p1.1.kind.isInput) ||
   (p1.1.kind.isInput && p2.1.kind.isInput &&
     !sameInputVal p1.1.inValId? p2.1.inValId?))

/-- Check via `List.foldr` that `p` does not conflict with any element in
`rest` (`0` `._unsafe_rec`). -/
@[expose] def noConflictWith (p : AsmOperandSpec × PhysReg)
    (rest : List (AsmOperandSpec × PhysReg)) : Bool :=
  rest.foldr (fun q acc => !operandPairConflicts p q && acc) true

/-- Check via `List.foldr` that every operand matches its assigned register
bank and no two distinct operand positions conflict (`0` `._unsafe_rec`). -/
@[expose] def allPairsAdmissible
    (pairs : List (AsmOperandSpec × PhysReg)) : Bool :=
  (pairs.foldr
    (fun p st =>
      let bankOk := RegBank.beq p.1.bank p.2.bank
      let pairOk := noConflictWith p st.2
      (bankOk && pairOk && st.1, p :: st.2))
    (true, [])).1

/-- Computable Rust `[asm.register-operands]` register-allocation admissibility
judgment (`0` `._unsafe_rec`). -/
@[expose] def ValidRegAssignment (ops : List AsmOperandSpec)
    (assign : List PhysReg) : Bool :=
  match zipExact ops assign with
  | none => false
  | some pairs => allPairsAdmissible pairs

/-! ## Section 2: `N`-Site Inlining / Unrolling Register Polymorphism -/

/-- Register-parametric transition specification for an inline-assembly block
whose physical register assignment is chosen independently at each inlined or
unrolled call site. -/
structure RegParamTransition (State : Type) where
  ops  : List AsmOperandSpec
  pre  : List PhysReg → State → Prop
  step : List PhysReg → State → State
  post : List PhysReg → State → State → Prop

/-- Check via `List.foldr` that every site assignment in `assignments` is a
valid register assignment for `ops` (`0` `._unsafe_rec`). -/
@[expose] def allAssignmentsValid (ops : List AsmOperandSpec)
    (assignments : List (List PhysReg)) : Bool :=
  assignments.foldr (fun a acc => ValidRegAssignment ops a && acc) true

/-- Universal membership extraction from `allAssignmentsValid` (`[propext]`).
-/
theorem validRegAssignment_of_allAssignmentsValid
    (ops : List AsmOperandSpec) (assignments : List (List PhysReg))
    (hAll : allAssignmentsValid ops assignments = true)
    (assign : List PhysReg) (hMem : assign ∈ assignments) :
    ValidRegAssignment ops assign = true := by
  induction assignments with
  | nil => cases hMem
  | cons a rest ih =>
    dsimp only [allAssignmentsValid, List.foldr] at hAll
    cases hHead : ValidRegAssignment ops a with
    | false =>
      rw [hHead] at hAll
      exact False.elim (boolEq_false_true hAll)
    | true =>
      rw [hHead] at hAll
      cases hMem with
      | head _ => exact hHead
      | tail _ hTail => exact ih hAll hTail

/-- Universal register-polymorphic schedule soundness across `N`-site inlining
and loop unrolling: a single register-parametric proof over `ValidRegAssignment`
instantiates soundly for every site assignment in `assignments` without
repeating per-site proofs (`[propext]`). -/
theorem regPolymorphicScheduleSound {State : Type}
    (tr : RegParamTransition State)
    (hParam : ∀ (assign : List PhysReg) (s : State),
      ValidRegAssignment tr.ops assign = true →
      tr.pre assign s →
      tr.post assign s (tr.step assign s))
    (assignments : List (List PhysReg))
    (hAll : allAssignmentsValid tr.ops assignments = true) :
    ∀ (assign : List PhysReg) (s : State),
      assign ∈ assignments →
      tr.pre assign s →
      tr.post assign s (tr.step assign s) := by
  intro assign s hMem hPre
  exact hParam assign s
    (validRegAssignment_of_allAssignmentsValid tr.ops assignments hAll
      assign hMem)
    hPre

/-- Sequential composition of `N` inlined/unrolled sites sharing one
register-parametric invariant proof across arbitrary valid physical register
assignments `[assign_1, ..., assign_N]` (`[propext]`). -/
theorem regPolymorphicUnrollChainSound {State : Type}
    (tr : RegParamTransition State) (Inv : State → Prop)
    (hStep : ∀ (assign : List PhysReg) (s : State),
      ValidRegAssignment tr.ops assign = true →
      Inv s →
      Inv (tr.step assign s))
    (assignments : List (List PhysReg))
    (hAll : allAssignmentsValid tr.ops assignments = true)
    (s0 : State) (hInit : Inv s0) :
    Inv (assignments.foldl (fun s a => tr.step a s) s0) := by
  induction assignments generalizing s0 with
  | nil => exact hInit
  | cons a rest ih =>
    dsimp only [allAssignmentsValid, List.foldr] at hAll
    cases hHead : ValidRegAssignment tr.ops a with
    | false =>
      rw [hHead] at hAll
      exact False.elim (boolEq_false_true hAll)
    | true =>
      rw [hHead] at hAll
      dsimp only [List.foldl]
      exact ih hAll (tr.step a s0) (hStep a s0 hHead hInit)

/-! ## Section 3: Non-Vacuous Early-Clobber Soundness & Lateout Refutation -/

/-- Pure register-file update on a `Nat`-indexed GP bank. -/
@[expose] def writeGpReg (rf : Nat → Nat) (idx val : Nat) : Nat → Nat :=
  fun k => if Nat.beq k idx then val else rf k

/-- Two-step inline-assembly sequence `dst := a; dst := dst - b` executed on a
GP register file. -/
@[expose] def twoStepSubExec (rf : Nat → Nat) (rDst rA rB : Nat) : Nat → Nat :=
  let rf1 := writeGpReg rf rDst (rf rA)
  writeGpReg rf1 rDst (rf1 rDst - rf1 rB)

/-- Operand constraint list declaring `dst` as early-clobber (`.outEarly`). -/
@[expose] def twoStepSubEarlyOps : List AsmOperandSpec :=
  [⟨.outEarly, .gp, 64, none⟩, ⟨.in_, .gp, 64, none⟩, ⟨.in_, .gp, 64, none⟩]

/-- Misdeclared operand list declaring `dst` as `.lateout` instead of
`.outEarly`. -/
@[expose] def twoStepSubLateOps : List AsmOperandSpec :=
  [⟨.lateout, .gp, 64, none⟩, ⟨.in_, .gp, 64, none⟩, ⟨.in_, .gp, 64, none⟩]

/-- Under `.outEarly`, every valid physical register assignment guarantees
pairwise distinct `rDst`, `rA`, and `rB` (`rDst.idx != rB.idx` and
`rA.idx != rB.idx`), so `dst := a; dst := dst - b` computes `a - b` for ALL
register files and ALL valid assignments without admitting `rA = rB`
(`[propext]`). -/
theorem earlyClobber_twoStep_sub_sound (rf : Nat → Nat)
    (rDst rA rB : PhysReg)
    (hValid : ValidRegAssignment twoStepSubEarlyOps [rDst, rA, rB] = true) :
    twoStepSubExec rf rDst.idx rA.idx rB.idx rDst.idx =
      rf rA.idx - rf rB.idx ∧
    Nat.beq rA.idx rB.idx = false := by
  cases rDst with
  | mk bDst iDst =>
    cases rA with
    | mk bA iA =>
      cases rB with
      | mk bB iB =>
        dsimp only [ValidRegAssignment, twoStepSubEarlyOps, zipExact,
          allPairsAdmissible, noConflictWith, operandPairConflicts,
          PhysReg.beq, AsmOperandKind.isOutput,
          AsmOperandKind.isEarlyClobber, AsmOperandKind.isInput,
          sameInputVal, List.foldr] at hValid
        have hDstBlk := bandLeft hValid
        have hRest1 := bandRight hValid
        have hABlk := bandLeft hRest1
        have hRest2 := bandRight hRest1
        have hBankDst := bandLeft hDstBlk
        have hPairsDst := bandRight hDstBlk
        have hPairB := bandLeft (bandRight hPairsDst)
        have hBankA := bandLeft hABlk
        have hPairAB := bandLeft (bandRight hABlk)
        have hBankB := bandLeft (bandLeft hRest2)
        cases bDst with
        | vec => exact False.elim (boolEq_false_true hBankDst)
        | kMask => exact False.elim (boolEq_false_true hBankDst)
        | gp =>
          cases bA with
          | vec => exact False.elim (boolEq_false_true hBankA)
          | kMask => exact False.elim (boolEq_false_true hBankA)
          | gp =>
            cases bB with
            | vec => exact False.elim (boolEq_false_true hBankB)
            | kMask => exact False.elim (boolEq_false_true hBankB)
            | gp =>
              have hNeq : Nat.beq iDst iB = false := by
                cases hEq : Nat.beq iDst iB with
                | false => rfl
                | true =>
                  rw [hEq] at hPairB
                  exact False.elim (boolEq_false_true hPairB)
              have hNeqAB : Nat.beq iA iB = false := by
                cases hEq : Nat.beq iA iB with
                | false => rfl
                | true =>
                  rw [hEq] at hPairAB
                  exact False.elim (boolEq_false_true hPairAB)
              have hNeqSym : Nat.beq iB iDst = false := by
                rw [natBeq_symm iB iDst]
                exact hNeq
              refine ⟨?_, hNeqAB⟩
              dsimp only [twoStepSubExec, writeGpReg]
              rw [ite_bool_true (natBeq_refl iDst),
                  ite_bool_true (natBeq_refl iDst),
                  ite_bool_false hNeqSym]

/-- Combined early-clobber soundness, distinct-input enforcement, and
lateout-aliasing refutation:
1. Declaring `dst` as `.outEarly` guarantees `dst := a; dst := dst - b`
   computes `a - b` and forbids `rA = rB` for every valid assignment.
2. Misdeclaring `dst` as `.lateout` admits `phys(dst) = phys(b)` (`reg 0`),
   causing step 1 to clobber `b` and yielding `0 != 7 = a - b` (`[propext]`).
-/
theorem earlyClobber_prevents_twoStep_sub_clobber :
    (∀ (rf : Nat → Nat) (rDst rA rB : PhysReg),
      ValidRegAssignment twoStepSubEarlyOps [rDst, rA, rB] = true →
      twoStepSubExec rf rDst.idx rA.idx rB.idx rDst.idx =
        rf rA.idx - rf rB.idx ∧ Nat.beq rA.idx rB.idx = false) ∧
    (ValidRegAssignment twoStepSubEarlyOps [⟨.gp, 0⟩, ⟨.gp, 1⟩, ⟨.gp, 1⟩] =
      false) ∧
    (let rDst : PhysReg := ⟨.gp, 0⟩
     let rA : PhysReg := ⟨.gp, 1⟩
     let rB : PhysReg := ⟨.gp, 0⟩
     let rf : Nat → Nat := fun k => if Nat.beq k 1 then 10 else 3
     ValidRegAssignment twoStepSubLateOps [rDst, rA, rB] = true ∧
     twoStepSubExec rf rDst.idx rA.idx rB.idx rDst.idx = 0 ∧
     rf rA.idx - rf rB.idx = 7 ∧
     twoStepSubExec rf rDst.idx rA.idx rB.idx rDst.idx ≠
       rf rA.idx - rf rB.idx) := by
  refine ⟨earlyClobber_twoStep_sub_sound, rfl, rfl, rfl, rfl, ?_⟩
  intro hEq
  cases hEq

/-! ## Section 4: `clobber_abi` Callee-Saved Register Leaf Specifications -/

/-- Platform calling-convention callee-saved register specification recording
which GP registers and which low bit-prefix (`vecPreservedLo`) of callee-saved
vector registers survive a `clobber_abi` call boundary. -/
structure CalleeSavedSpec where
  gpRegs         : List Nat
  vecRegs        : List Nat
  vecPreservedLo : Nat

/-- SysV x86-64 callee-saved specification (`RBX, RBP, R12..R15`; no vector
registers are callee-saved). -/
@[expose] def sysvCalleeSavedSpec : CalleeSavedSpec :=
  { gpRegs := [3, 5, 12, 13, 14, 15]
    vecRegs := []
    vecPreservedLo := 0 }

/-- AAPCS64 callee-saved specification (`X19..X29`; `V8..V15` preserve only
`D8..D15` `[63:0]`, clobbering `[255:64]`). -/
@[expose] def aapcs64CalleeSavedSpec : CalleeSavedSpec :=
  { gpRegs := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
    vecRegs := [8, 9, 10, 11, 12, 13, 14, 15]
    vecPreservedLo := 64 }

/-- Win64 x86-64 callee-saved specification (`RBX, RBP, RDI, RSI, R12..R15`;
`XMM6..XMM15` preserve `[127:0]` only, clobbering `YMM` `[255:128]`). -/
@[expose] def win64CalleeSavedSpec : CalleeSavedSpec :=
  { gpRegs := [3, 5, 6, 7, 12, 13, 14, 15]
    vecRegs := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
    vecPreservedLo := 128 }

/-- Upper bit bound (exclusive) of each `VecLeafId`. -/
@[expose] def vecLeafUpperBit : VecLeafId → Nat
  | .b0_8 => 8
  | .b8_16 => 16
  | .b16_32 => 32
  | .b32_64 => 64
  | .b64_128 => 128
  | .ymm_b128_192 => 192
  | .ymm_b192_256 => 256

/-- Upper bit bound (exclusive) of each `ZmmLeafId`. -/
@[expose] def zmmLeafUpperBit : ZmmLeafId → Nat
  | .lo vid => vecLeafUpperBit vid
  | .zmm_b256_320 => 320
  | .zmm_b320_384 => 384
  | .zmm_b384_448 => 448
  | .zmm_b448_512 => 512

/-- Whether `clobber_abi` under `spec` preserves vector leaf `leaf` of vector
register `regIdx`. -/
@[expose] def clobberAbiPreservesVecLeaf (spec : CalleeSavedSpec)
    (regIdx : Nat) (leaf : VecLeafId) : Bool :=
  capNatMem regIdx spec.vecRegs &&
  Nat.ble (vecLeafUpperBit leaf) spec.vecPreservedLo

/-- Whether `clobber_abi` under `spec` preserves 512-bit `ZMM` leaf `leaf` of
register `regIdx`. -/
@[expose] def clobberAbiPreservesZmmLeaf (spec : CalleeSavedSpec)
    (regIdx : Nat) (leaf : ZmmLeafId) : Bool :=
  capNatMem regIdx spec.vecRegs &&
  Nat.ble (zmmLeafUpperBit leaf) spec.vecPreservedLo

/-- Exact `clobber_abi` vector leaf preservation vs clobbering on AAPCS64,
Win64, and SysV (`[]` axioms). -/
theorem clobberAbi_vecLeaf_preservation_verified :
    clobberAbiPreservesVecLeaf aapcs64CalleeSavedSpec 8 .b32_64 = true ∧
    clobberAbiPreservesVecLeaf aapcs64CalleeSavedSpec 8 .b64_128 = false ∧
    clobberAbiPreservesVecLeaf aapcs64CalleeSavedSpec 8 .ymm_b128_192 = false ∧
    clobberAbiPreservesVecLeaf aapcs64CalleeSavedSpec 0 .b32_64 = false ∧
    clobberAbiPreservesVecLeaf win64CalleeSavedSpec 6 .b64_128 = true ∧
    clobberAbiPreservesVecLeaf win64CalleeSavedSpec 6 .ymm_b128_192 = false ∧
    clobberAbiPreservesZmmLeaf win64CalleeSavedSpec 6 .zmm_b256_320 = false ∧
    clobberAbiPreservesVecLeaf sysvCalleeSavedSpec 6 .b0_8 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Section 5: Hardware/OS Capability Gating & Vector-ABI Compatibility -/

/-- Target CPU instruction-set feature set for x86-64 and AArch64 kernels. -/
structure CpuFeatureSet where
  sse2      : Bool := false
  ssse3     : Bool := false
  sse41     : Bool := false
  osxsave   : Bool := false
  avx       : Bool := false
  avx2      : Bool := false
  bmi1      : Bool := false
  bmi2      : Bool := false
  adx       : Bool := false
  pclmulqdq : Bool := false
  aes       : Bool := false
  avx512f   : Bool := false
  avx512vl  : Bool := false
  avx512bw  : Bool := false
  neon      : Bool := false
  dotprod   : Bool := false
  i8mm      : Bool := false
  sve       : Bool := false
  sve2      : Bool := false

/-- Empty CPU feature requirement set. -/
@[expose] def CpuFeatureSet.empty : CpuFeatureSet :=
  ⟨false, false, false, false, false, false, false, false, false, false,
   false, false, false, false, false, false, false, false, false⟩

/-- Whether `fs` requires zero optional target features. -/
@[expose] def CpuFeatureSet.isEmpty (fs : CpuFeatureSet) : Bool :=
  !fs.sse2 && !fs.ssse3 && !fs.sse41 && !fs.osxsave && !fs.avx && !fs.avx2 &&
  !fs.bmi1 && !fs.bmi2 && !fs.adx && !fs.pclmulqdq && !fs.aes &&
  !fs.avx512f && !fs.avx512vl && !fs.avx512bw &&
  !fs.neon && !fs.dotprod && !fs.i8mm && !fs.sve && !fs.sve2

/-- Componentwise feature subset check `req <= have_`. -/
@[expose] def CpuFeatureSet.subset (req have_ : CpuFeatureSet) : Bool :=
  capBoolImp req.sse2 have_.sse2 &&
  capBoolImp req.ssse3 have_.ssse3 &&
  capBoolImp req.sse41 have_.sse41 &&
  capBoolImp req.osxsave have_.osxsave &&
  capBoolImp req.avx have_.avx &&
  capBoolImp req.avx2 have_.avx2 &&
  capBoolImp req.bmi1 have_.bmi1 &&
  capBoolImp req.bmi2 have_.bmi2 &&
  capBoolImp req.adx have_.adx &&
  capBoolImp req.pclmulqdq have_.pclmulqdq &&
  capBoolImp req.aes have_.aes &&
  capBoolImp req.avx512f have_.avx512f &&
  capBoolImp req.avx512vl have_.avx512vl &&
  capBoolImp req.avx512bw have_.avx512bw &&
  capBoolImp req.neon have_.neon &&
  capBoolImp req.dotprod have_.dotprod &&
  capBoolImp req.i8mm have_.i8mm &&
  capBoolImp req.sve have_.sve &&
  capBoolImp req.sve2 have_.sve2

/-- OS-enabled SIMD architectural state (`XCR0` bits on x86-64, including
`Hi16_ZMM` bit 7 for `xmm16..31`/`ymm16..31`/`zmm16..31`, and active SVE
vector length in bytes on AArch64). -/
structure OsSimdState where
  xcr0Sse     : Bool := false
  xcr0Ymm     : Bool := false
  xcr0Zmm     : Bool := false
  xcr0Hi16Zmm : Bool := false
  sveLenBytes : Nat := 0

/-- Three-way Rust RFC 2396 function safety classification. -/
inductive FnSafetyKind where
  | safe
  | safeTargetFeatures (req : CpuFeatureSet)
  | unsafe_ (req : CpuFeatureSet)

/-- RFC 2396 safe-call check: a call outside an `unsafe` block is permitted
iff the callee is `.safe`, OR `.safeTargetFeatures req` with
`CpuFeatureSet.subset req callerFeatures = true`. -/
@[expose] def callTargetFeatureSafe (callerFeatures : CpuFeatureSet)
    (calleeKind : FnSafetyKind) : Bool :=
  match calleeKind with
  | .safe => true
  | .safeTargetFeatures req => CpuFeatureSet.subset req callerFeatures
  | .unsafe_ _ => false

/-- RFC 2396 safe `fn`-pointer reification check: rejects coercing
`.safeTargetFeatures req` to a safe `fn` pointer whenever `req` is non-empty,
and always rejects `.unsafe_`. -/
@[expose] def reifySafeFnPtrAllowed (calleeKind : FnSafetyKind) : Bool :=
  match calleeKind with
  | .safe => true
  | .safeTargetFeatures req => CpuFeatureSet.isEmpty req
  | .unsafe_ _ => false

/-- RFC 2396 safe-call characterization for `.safeTargetFeatures req` (`[]`
axioms). -/
theorem callTargetFeatureSafe_iff_subset (callerFeatures req : CpuFeatureSet) :
    callTargetFeatureSafe callerFeatures (.safeTargetFeatures req) =
      CpuFeatureSet.subset req callerFeatures :=
  rfl

/-- Coercing `.safeTargetFeatures req` to a safe `fn` pointer is rejected
whenever `req` is non-empty (`[]` axioms). -/
theorem reifySafeFnPtr_rejects_nonEmpty_targetFeatures (req : CpuFeatureSet)
    (hNonEmpty : CpuFeatureSet.isEmpty req = false) :
    reifySafeFnPtrAllowed (.safeTargetFeatures req) = false :=
  hNonEmpty

/-- Valid AArch64 SVE vector length in bytes per ARM DDI 0487: a 16-byte
(128-bit) multiple in `[16, 256]` (`128..2048` bits). -/
@[expose] def validSveLenBytes (n : Nat) : Bool :=
  Nat.ble 16 n && Nat.ble n 256 && Nat.beq (Nat.mod n 16) 0

/-- Whether an x86-64 `CpuFeatureSet`'s vector tiers satisfy architectural
implication (`avx512f -> avx -> sse2`). -/
@[expose] def x86VecFeatureTiersValid (f : CpuFeatureSet) : Bool :=
  capBoolImp f.avx f.sse2 &&
  capBoolImp f.avx512f (f.avx && f.sse2)

/-- Architecture-scoped hardware & OS `XCR0` readiness check for an `asm!`
operand or clobber bound to concrete physical register `reg`, closing `rustc`'s
`out("ymm0") _` / `out("zmm0") _` and EVEX `xmm16..31`/`ymm16..31` blind spots:
- Architectures never cross-satisfy (`cpu.neon` never satisfies `.x86_64`, and
  `cpu.sse2` never satisfies `.aarch64`).
- Every GP operand on `.x86_64` (`< 16`), `.aarch64` (`< 31`), and `.riscv64`
  (`< 32`) requires `0 < op.widthBits <= 64`.
- On `.x86_64`: vector operands (`reg.idx < 32`) require
  `0 < op.widthBits <= 512`. Baseline `<= 128`-bit `xmm0..15` requires
  `cpu.sse2` and `os.xcr0Sse` (OSFXSR/SSE without `osxsave`). `YMM` requires
  `cpu.sse2`, `cpu.avx`, `cpu.osxsave`, `xcr0Sse`, and `xcr0Ymm`. Every AVX-512
  use (`kMask`, `zmm0..15`, and `xmm16..31`/`ymm16..31`/`zmm16..31`) requires
  full lower tiers (`cpu.sse2 && cpu.avx && cpu.avx2 && cpu.avx512f`),
  `cpu.osxsave`, and all AVX-512 `XCR0` bits
  (`xcr0Sse && xcr0Ymm && xcr0Zmm && xcr0Hi16Zmm`); `k0` (`kreg0`) is
  clobber-only (`op.kind.isClobberOnly`), and `kMask` requires
  `0 < op.widthBits <= 64` with `avx512bw` above `16` bits.
- On `.aarch64`: vector operands (`reg.idx < 32`) require `0 < op.widthBits`;
  `<= 128`-bit NEON requires `cpu.neon`, while SVE `Z` (`> 128`-bit, up to
  `os.sveLenBytes * 8`) and clobber-only SVE predicate `P` (`.kMask`, `preg`,
  `reg.idx < 16`, `0 < op.widthBits <= os.sveLenBytes`) require `cpu.neon`,
  `cpu.sve || cpu.sve2`, and `validSveLenBytes os.sveLenBytes`. -/
@[expose] def asmOperandHardwareReady (arch : TargetArch)
    (cpu : CpuFeatureSet) (os : OsSimdState)
    (op : AsmOperandSpec) (reg : PhysReg) : Bool :=
  if !RegBank.beq op.bank reg.bank then
    false
  else
    let gpWidthOk := Nat.blt 0 op.widthBits && Nat.ble op.widthBits 64
    let x86Avx512Base :=
      cpu.sse2 && cpu.avx && cpu.avx2 && cpu.avx512f && cpu.osxsave &&
      os.xcr0Sse && os.xcr0Ymm && os.xcr0Zmm && os.xcr0Hi16Zmm
    let sveReady :=
      cpu.neon && (cpu.sve || cpu.sve2) && validSveLenBytes os.sveLenBytes
    match arch, reg.bank with
    | .x86_64, .gp => Nat.blt reg.idx 16 && gpWidthOk
    | .x86_64, .kMask =>
      let kindOk := if Nat.beq reg.idx 0 then op.kind.isClobberOnly else true
      let bwOk := Nat.ble op.widthBits 16 || cpu.avx512bw
      Nat.blt reg.idx 8 &&
      Nat.blt 0 op.widthBits && Nat.ble op.widthBits 64 &&
      kindOk && x86Avx512Base && bwOk
    | .x86_64, .vec =>
      if !Nat.blt reg.idx 32 || !Nat.blt 0 op.widthBits ||
         !Nat.ble op.widthBits 512 then
        false
      else if Nat.ble 16 reg.idx then
        x86Avx512Base && (Nat.ble 512 op.widthBits || cpu.avx512vl)
      else if Nat.ble op.widthBits 128 then
        cpu.sse2 && os.xcr0Sse
      else if Nat.ble op.widthBits 256 then
        cpu.sse2 && cpu.avx && cpu.osxsave && os.xcr0Sse && os.xcr0Ymm
      else
        x86Avx512Base
    | .aarch64, .gp => Nat.blt reg.idx 31 && gpWidthOk
    | .aarch64, .vec =>
      Nat.blt reg.idx 32 && Nat.blt 0 op.widthBits &&
      ((Nat.ble op.widthBits 128 && cpu.neon) ||
       (Nat.blt 128 op.widthBits && sveReady &&
        Nat.ble op.widthBits (os.sveLenBytes * 8)))
    | .aarch64, .kMask =>
      Nat.blt reg.idx 16 && op.kind.isClobberOnly && sveReady &&
      Nat.blt 0 op.widthBits && Nat.ble op.widthBits os.sveLenBytes
    | .riscv64, .gp => Nat.blt reg.idx 32 && gpWidthOk
    | .riscv64, .vec => false
    | .riscv64, .kMask => false

/-- Check via `zipExact` and `List.foldr` that a full register assignment is
both allocation-admissible and hardware/OS-state ready (`0` `._unsafe_rec`). -/
@[expose] def asmAssignmentHardwareReady (arch : TargetArch)
    (cpu : CpuFeatureSet) (os : OsSimdState)
    (ops : List AsmOperandSpec) (assign : List PhysReg) : Bool :=
  ValidRegAssignment ops assign &&
  match zipExact ops assign with
  | none => false
  | some pairs =>
    pairs.foldr
      (fun p acc => asmOperandHardwareReady arch cpu os p.1 p.2 && acc)
      true

/-- Platform profile for vector calling-convention compatibility. -/
inductive VectorAbiProfile where
  | sysvX86_64
  | aapcs64
  | win64X86_64

/-- Vector argument category checked across a call boundary. -/
inductive AbiVectorKind where
  | vec128
  | vec256
  | vec512
  | neonHva (count : Nat)

/-- Vector-ABI target-feature compatibility across a call boundary:
- SysV and Win64 x86-64: both sides must have tier-consistent feature sets
  (`x86VecFeatureTiersValid`) and agree on every vector feature tier up to the
  argument width — `+sse2` for `vec128`, `+sse2 && +avx` for `vec256`, and
  `+sse2 && +avx && +avx512f` for `vec512` (preventing LLVM `RetCC_X86_Win64_C`
  / `CC_X86_Win64_C` / SysV legalization split mismatches such as `2 x YMM` vs
  `4 x XMM` when `+avx512f` is absent on both sides).
- AAPCS64: admits `vec128` and NEON multi-vector HVA (`1 <= count <= 4`,
  modeling `uint8x16x2_t`..`uint8x16x4_t`) when both sides have `+neon`. -/
@[expose] def abiVectorCallCompatible (profile : VectorAbiProfile)
    (callerFeat calleeFeat : CpuFeatureSet) (argKind : AbiVectorKind) : Bool :=
  let x86TiersOk :=
    x86VecFeatureTiersValid callerFeat && x86VecFeatureTiersValid calleeFeat
  match profile, argKind with
  | .sysvX86_64, .vec128 | .win64X86_64, .vec128 =>
    x86TiersOk && capBoolEq callerFeat.sse2 calleeFeat.sse2
  | .sysvX86_64, .vec256 | .win64X86_64, .vec256 =>
    x86TiersOk &&
    capBoolEq callerFeat.sse2 calleeFeat.sse2 &&
    capBoolEq callerFeat.avx calleeFeat.avx
  | .sysvX86_64, .vec512 | .win64X86_64, .vec512 =>
    x86TiersOk &&
    capBoolEq callerFeat.sse2 calleeFeat.sse2 &&
    capBoolEq callerFeat.avx calleeFeat.avx &&
    capBoolEq callerFeat.avx512f calleeFeat.avx512f
  | .sysvX86_64, .neonHva _ | .win64X86_64, .neonHva _ => false
  | .aapcs64, .vec128 => callerFeat.neon && calleeFeat.neon
  | .aapcs64, .neonHva count =>
    callerFeat.neon && calleeFeat.neon &&
    Nat.ble 1 count && Nat.ble count 4
  | .aapcs64, .vec256 | .aapcs64, .vec512 => false

/-- AAPCS64 NEON multi-vector HVA register/stack placement outcome
(`uint8x16x2_t`..`uint8x16x4_t`, `1..4` x 16B `V` registers). -/
inductive NeonHvaPlacement where
  | vRegs (baseReg count : Nat)
  | stackSpill (byteSize : Nat)
  | invalidCount

/-- Classify an AAPCS64 NEON multi-vector HVA parameter given next available
FP/SIMD register index `fpNext` (`0..8`) and element count `count`:
- For `1 <= count <= 4` and `fpNext + count <= 8`, assigns
  `V[fpNext .. fpNext + count - 1]` and advances `fpNext` to `fpNext + count`.
- For `1 <= count <= 4` and `fpNext + count > 8`, spills all `count * 16`
  bytes to stack and saturates `fpNext` to `8`. -/
@[expose] def classifyAapcs64NeonHva (fpNext count : Nat) :
    NeonHvaPlacement × Nat :=
  if Nat.ble 1 count && Nat.ble count 4 then
    if Nat.ble (fpNext + count) 8 then
      (.vRegs fpNext count, fpNext + count)
    else
      (.stackSpill (count * 16), 8)
  else
    (.invalidCount, fpNext)

/-- End-to-end verification of `asmOperandHardwareReady` (including `osxsave`,
EVEX `ymm16` `Hi16_ZMM`/`avx512vl`, and strict arch separation), RFC 2396 safe
calls and `fn`-pointer reification, SysV and Win64 vector-ABI feature mismatch
detection, and AAPCS64 NEON multi-vector HVA register admission and spilling
(`[propext]`). -/
theorem capability_and_vector_abi_verified :
    let sse2Only : CpuFeatureSet := { sse2 := true, osxsave := true }
    let avx2NoOsxsave : CpuFeatureSet :=
      { sse2 := true, avx := true, avx2 := true }
    let avx2Cpu : CpuFeatureSet :=
      { sse2 := true, osxsave := true, avx := true, avx2 := true }
    let avx512NoVl : CpuFeatureSet :=
      { sse2 := true, osxsave := true, avx := true, avx2 := true,
        avx512f := true }
    let avx512Vl : CpuFeatureSet :=
      { avx512NoVl with avx512vl := true }
    let avx512Bw : CpuFeatureSet :=
      { avx512Vl with avx512bw := true }
    let neonCpu : CpuFeatureSet := { neon := true }
    let osSseOnly : OsSimdState := { xcr0Sse := true }
    let osAvx : OsSimdState := { xcr0Sse := true, xcr0Ymm := true }
    let osAvx512NoHi16 : OsSimdState :=
      { xcr0Sse := true, xcr0Ymm := true, xcr0Zmm := true }
    let osAvx512Full : OsSimdState :=
      { osAvx512NoHi16 with xcr0Hi16Zmm := true }
    let ymmOp : AsmOperandSpec := ⟨.clobberEarly, .vec, 256, none⟩
    let zmmOp : AsmOperandSpec := ⟨.clobberEarly, .vec, 512, none⟩
    let badWideOp : AsmOperandSpec := ⟨.clobberEarly, .vec, 1024, none⟩
    let k16Op : AsmOperandSpec := ⟨.in_, .kMask, 16, none⟩
    let k64Op : AsmOperandSpec := ⟨.clobberEarly, .kMask, 64, none⟩
    let xmmOp : AsmOperandSpec := ⟨.in_, .vec, 128, none⟩
    let ymm0 : PhysReg := ⟨.vec, 0⟩
    let ymm16 : PhysReg := ⟨.vec, 16⟩
    let k0 : PhysReg := ⟨.kMask, 0⟩
    let k1 : PhysReg := ⟨.kMask, 1⟩
    -- (a) RFC 2396 safe calls & fn-ptr reification
    callTargetFeatureSafe sse2Only (.safeTargetFeatures avx2Cpu) = false ∧
    callTargetFeatureSafe avx2Cpu (.safeTargetFeatures avx2Cpu) = true ∧
    callTargetFeatureSafe avx2Cpu (.unsafe_ avx2Cpu) = false ∧
    reifySafeFnPtrAllowed (.safeTargetFeatures avx2Cpu) = false ∧
    reifySafeFnPtrAllowed .safe = true ∧
    -- (b) Hardware + osxsave + XCR0[7:5] + AVX512BW + width<=512 + clobber-only
    asmOperandHardwareReady .x86_64 neonCpu osAvx xmmOp ymm0 = false ∧
    asmOperandHardwareReady .aarch64 sse2Only osAvx xmmOp ymm0 = false ∧
    asmOperandHardwareReady .x86_64 avx2NoOsxsave osAvx ymmOp ymm0 = false ∧
    asmOperandHardwareReady .x86_64 avx2Cpu osSseOnly ymmOp ymm0 = false ∧
    asmOperandHardwareReady .x86_64 avx2Cpu osAvx ymmOp ymm0 = true ∧
    asmOperandHardwareReady .x86_64 avx2Cpu osAvx ymmOp ymm16 = false ∧
    asmOperandHardwareReady .x86_64 avx512NoVl osAvx512Full ymmOp ymm16 =
      false ∧
    asmOperandHardwareReady .x86_64 avx512Vl osAvx512NoHi16 ymmOp ymm16 =
      false ∧
    asmOperandHardwareReady .x86_64 avx512Vl osAvx512Full ymmOp ymm16 = true ∧
    asmOperandHardwareReady .x86_64 avx512NoVl osAvx512NoHi16 zmmOp ymm0 =
      false ∧
    asmOperandHardwareReady .x86_64 avx512NoVl osAvx512Full zmmOp ymm0 = true ∧
    asmOperandHardwareReady .x86_64 avx512Bw osAvx512Full badWideOp ymm16 =
      false ∧
    asmOperandHardwareReady .x86_64 avx512NoVl osAvx512NoHi16 k16Op k1 =
      false ∧
    asmOperandHardwareReady .x86_64 avx512NoVl osAvx512Full k16Op k1 = true ∧
    asmOperandHardwareReady .x86_64 avx512NoVl osAvx512Full k16Op k0 = false ∧
    asmOperandHardwareReady .x86_64 avx512NoVl osAvx512Full k64Op k1 = false ∧
    asmOperandHardwareReady .x86_64 avx512Bw osAvx512Full k64Op k1 = true ∧
    asmOperandHardwareReady .x86_64 avx512Bw osAvx512Full k64Op k0 = true ∧
    -- (c) SysV & Win64 full-tier vec128/vec256/vec512 agreement & AAPCS64 HVA
    abiVectorCallCompatible .sysvX86_64 avx2Cpu sse2Only .vec256 = false ∧
    abiVectorCallCompatible .sysvX86_64 avx512NoVl avx2Cpu .vec512 = false ∧
    abiVectorCallCompatible .sysvX86_64 avx2Cpu sse2Only .vec512 = false ∧
    abiVectorCallCompatible .sysvX86_64 { sse2 := true } CpuFeatureSet.empty
      .vec256 = false ∧
    abiVectorCallCompatible .sysvX86_64 avx2Cpu avx2Cpu .vec256 = true ∧
    abiVectorCallCompatible .win64X86_64 sse2Only neonCpu .vec128 = false ∧
    abiVectorCallCompatible .win64X86_64 avx2Cpu sse2Only .vec256 = false ∧
    abiVectorCallCompatible .win64X86_64 avx512NoVl avx2Cpu .vec512 = false ∧
    abiVectorCallCompatible .win64X86_64 avx2Cpu sse2Only .vec512 = false ∧
    abiVectorCallCompatible .win64X86_64 { sse2 := true } CpuFeatureSet.empty
      .vec256 = false ∧
    abiVectorCallCompatible .win64X86_64 sse2Only sse2Only .vec128 = true ∧
    abiVectorCallCompatible .win64X86_64 avx2Cpu avx2Cpu .vec256 = true ∧
    abiVectorCallCompatible .win64X86_64 avx2Cpu avx2Cpu .vec512 = true ∧
    abiVectorCallCompatible .win64X86_64 avx512NoVl avx512NoVl .vec512 = true ∧
    abiVectorCallCompatible .aapcs64 neonCpu neonCpu (.neonHva 4) = true ∧
    classifyAapcs64NeonHva 4 4 = (.vRegs 4 4, 8) ∧
    classifyAapcs64NeonHva 6 3 = (.stackSpill 48, 8) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.AsmBridge.OperandAndCap

end
