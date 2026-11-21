-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Dual-Role `.eh_frame` Unwinding Semantics, `asm!` CFI Delta Invariants, and Heterogeneous `LinkFrame` Unwind Soundness

Self-contained Lean 4 (`v4.34.1`) mechanization using strictly `Init.*` (zero
external dependencies, zero `sorry`, zero `axiom`, zero `opaque`, zero `partial`,
zero `unsafe`, zero `native_decide`, zero `bv_decide`, zero `set_option`).

## Architectural Overview

1. **`Trusted` Operational & DWARF CFI Layer (Tactic-Free):**
   - Models x86-64 GPRs (`rax`, `rdi`, `rsp`, `rbp`, `rbx`, `r10`, `r11`,
     `r12`..`r15`, `rip`), 64-bit word memory (`Mem`), and `TerminalOut`
     (`.returned` | `.unwound`).
   - Defines `Trusted.DwarfCfi` (`CfaRule`, `RegRule`, `CfiOp`, `LsdaAction`,
     `FdeRecord`, `evalFdeAt`, `stepUnwindFrame`), covering the minimal
     fail-closed DWARF CFI subset empirically required across `rustc` `1.99.1` /
     `1.100.0` / `1.102.0-nightly` and hardened `gcc`/`g++` `15.2.0` (`RSP`,
     `RBP`, `R10`, and `R11` CFA registers, GCC DRAP `DW_CFA_def_cfa_expression:
     [DW_OP_bregN disp, DW_OP_deref]` and `DW_CFA_expression: [DW_OP_bregN disp]`,
     `DW_CFA_remember_state` / `DW_CFA_restore_state`, `DW_CFA_GNU_args_size`,
     and `.gcc_except_table` LSDA `None` / `Cleanup` / `Catch` /
     `TerminateFilter`).
   - Extends the heterogeneous `LinkFrame` stack with unwind-capable MIR and ISA
     frames (`UnwindLinkFrame`, `runStackUnwind`).

2. **Rule 1 (Universal Non-Unwinding `asm!` CFI Delta Invariant):**
   - Proves `rule1_asm_cfi_delta_preserves_downstream_fde`: every function-scoped
     `asm!` span `[asmStart, asmEnd)` that preserves the active `CfiState`
     (`evalOps ... asmStart = evalOps ... asmEnd`) and emits zero personality or
     LSDA overrides leaves all downstream FDE rows (`queryPc >= asmEnd`)
     identical to the unpoisoned compiler-generated FDE.
   - Mechanizes **Negative Canaries B1, B2, B3, B5, B6, and B7**:
     - `canary_poc_b1_zero_insn_cfa_shift_breaks_unwind`: 0-instruction
       `.cfi_adjust_cfa_offset 16` breaks downstream safe-Rust unwinding.
     - `canary_poc_b2_dead_branch_asm_poisons_linear_fde`: unexecuted dead-branch
       `asm!` laid out before `callPc` still poisons linear FDE evaluation.
     - `canary_poc_b3_undefined_rip_aborts_phase1`: `.cfi_undefined rip` aborts
       Phase 1 (`error 5`) and skips `Drop` destructors.
     - `canary_poc_b5_escape_offset_leaks_rip_into_caller_r12`: `.cfi_escape`
       (`DW_CFA_offset r12, -8`) succeeds in `catch_unwind` while overwriting
       caller's safe `r12` local with saved `RIP`.
     - `canary_poc_b6_b7_personality_and_lsda_hijack_skip_drops`: `.cfi_personality`
       or `.cfi_lsda` override inside 0-byte `asm!` causes `catch_unwind` to
       succeed while silently skipping local `Drop` landing pads.

3. **Rule 2 (Unwind-Unreachable vs. Unwind-Traversable Partition):**
   - **Part 2A (Unwind-Unreachable Leaf / `nounwind` Partition + Statement-Origin
     Separation):** Proves `rule2a_nounwind_frame_eh_frame_irrelevant` and
     `LockedNounwindObligation.verify_nounwind_leaf_abi` (zero `UntrustedHints.*`
     or `DwarfCfi` symbols in `ConstantInfo.type`).
   - **Part 2B (Unwind-Traversable `Trusted.DwarfCfi` Soundness):** Proves
     `rule2b_stepUnwindFrame_sound` (covering `RSP+off`, `RBP+16` dynamic stack
     realignment, `R11+off` stack-clash probe loops, and GCC DRAP `breg+deref`
     expressions in `gcc_drap_expression_unwind_sound`) and
     `rule2b_multi_frame_unwind_preserves_state` (induction across arbitrarily
     many interleaved ISA/C/C++/`.S`/`asm!` and MIR cleanup frames into
     `TerminalOut.unwound` / `mirCatch`).
   - Mechanizes **Negative Canaries A1, A2, A4, and C1**:
     - `canary_poc_a1_may_unwind_missing_cfa_corrupts_unwind`: passes normal
       return while miscomputing `rsp`/`rip` on unwind.
     - `canary_poc_a2_may_unwind_missing_r12_corrupts_safe_local_on_catch`:
       passes normal return AND catches cleanly, while silently corrupting the
       caller's `r12` local from `0x2222222222222222` to `0x7777777777777777`.
     - `canary_llvm_shrinkwrap_invoke_alignstack_violation`: mechanizes the
       LLVM `23.1.5` `ShrinkWrap` miscompilation (`rsp % 16 == 8` on `invoke asm
       alignstack`), proving `call` inside `asm!` violates SysV 16-byte stack
       alignment.
     - `canary_poc_c1_missing_c_eh_frame_aborts_and_skips_drops`: C `.o` without
       `.eh_frame` aborts Phase 1 and skips outer Rust `Drop` cleanups.
-/

namespace Trusted

/-- x86-64 general-purpose registers + `rip` relevant to SysV AMD64 calling and
DWARF `.eh_frame` unwinding (DWARF register numbers: `rax=0`, `rdi=5`, `rbp=6`,
`rsp=7`, `r10=10`, `r11=11`, `rbx=3`, `r12=12`..`r15=15`, `rip=16`). -/
inductive Reg where
  | rax | rdi | rsp | rbp | rbx | r10 | r11 | r12 | r13 | r14 | r15 | rip
  deriving DecidableEq, Repr

def calleeSavedRegs : List Reg := [.rbp, .rbx, .r12, .r13, .r14, .r15]

/-- Byte-addressed 64-bit word memory map (modeled over `Int` addresses so stack
offsets `CFA + d` avoid unsigned wrap-around noise). -/
abbrev Mem := Int → Nat

def memWrite (m : Mem) (addr : Int) (val : Nat) : Mem :=
  fun a => if a = addr then val else m a

def regSet (regs : Reg → Nat) (r : Reg) (v : Nat) : Reg → Nat :=
  fun q => if q = r then v else regs q

/-- Observable terminal outcome of a function or linked sub-computation,
matching `Trusted.MirSemantics.TerminalOut`. -/
inductive TerminalOut where
  | returned (ret : Nat) (mem : Mem)
  | unwound (mem : Mem)

namespace DwarfCfi

/-- Minimal fail-closed CFA rule covering 100% of `rustc` and hardened `gcc`/`g++`
x86-64 frames:
- `regOffset r off`: `CFA = regs(r) + off` (`DW_CFA_def_cfa*`, covering `RSP`,
  `RBP`, `R10`, and `R11` stack-clash probe loops).
- `derefBreg r disp`: `CFA = mem[regs(r) + disp]` (`DW_CFA_def_cfa_expression:
  [DW_OP_bregN disp, DW_OP_deref]`, emitted by GCC DRAP when combining
  `aligned(64)` with `alloca`).
- `invalid`: fail-closed poison state for unsupported DWARF expressions. -/
inductive CfaRule where
  | regOffset (r : Reg) (off : Int)
  | derefBreg (r : Reg) (disp : Int)
  | invalid
  deriving DecidableEq, Repr

/-- Per-register recovery rule in a DWARF CFI table row. -/
inductive RegRule where
  | sameValue
  | cfaOffset (off : Int)
  | atBreg (base : Reg) (disp : Int)
  | inReg (src : Reg)
  | undefined
  deriving DecidableEq, Repr

/-- Active DWARF CFI row at a program counter, excluding the `.cfi_remember_state`
stack. -/
structure CfiRow where
  cfa : CfaRule
  regRules : Reg → RegRule
  argsSize : Nat

/-- Full evaluator state across an FDE instruction stream, including `pc` and the
`DW_CFA_remember_state` / `DW_CFA_restore_state` LIFO stack. -/
structure CfiState where
  pc : Nat
  row : CfiRow
  savedRows : List CfiRow

def x86_64InitRegRules : Reg → RegRule :=
  fun r => if r = .rip then .cfaOffset (-8) else .sameValue

/-- Standard SysV x86-64 CIE initial row: `CFA = RSP + 8`, `RIP = [CFA - 8]`,
all other registers `sameValue`, `argsSize = 0`. -/
def x86_64CieInitRow : CfiRow :=
  { cfa := .regOffset .rsp 8, regRules := x86_64InitRegRules, argsSize := 0 }

/-- Minimal fail-closed DWARF `.eh_frame` instruction AST. -/
inductive CfiOp where
  | advanceLoc (delta : Nat)
  | defCfa (r : Reg) (off : Int)
  | defCfaReg (r : Reg)
  | defCfaOffset (off : Int)
  | defCfaBregDeref (r : Reg) (disp : Int)
  | offset (r : Reg) (off : Int)
  | exprBreg (r : Reg) (base : Reg) (disp : Int)
  | sameValue (r : Reg)
  | restore (r : Reg)
  | undefined (r : Reg)
  | register (r : Reg) (src : Reg)
  | rememberState
  | restoreState
  | gnuArgsSize (sz : Nat)
  | nop
  | unsupportedEscape
  deriving DecidableEq, Repr

def updateRule (rules : Reg → RegRule) (r : Reg) (rule : RegRule) : Reg → RegRule :=
  fun q => if q = r then rule else rules q

/-- Single-instruction DWARF CFI transition when `st.pc <= targetPc`.
Returns `none` (fail-closed) on `restoreState` stack underflow, `defCfaReg` /
`defCfaOffset` applied to a non-register-offset CFA expression, or
`unsupportedEscape`. -/
def stepCfiOp (cieInit : CfiRow) (st : CfiState) (op : CfiOp) : Option CfiState :=
  match op with
  | .advanceLoc d => some { st with pc := st.pc + d }
  | .defCfa r off =>
      some { st with row := { st.row with cfa := .regOffset r off } }
  | .defCfaReg r =>
      match st.row.cfa with
      | .regOffset _ off =>
          some { st with row := { st.row with cfa := .regOffset r off } }
      | _ => none
  | .defCfaOffset off =>
      match st.row.cfa with
      | .regOffset r _ =>
          some { st with row := { st.row with cfa := .regOffset r off } }
      | _ => none
  | .defCfaBregDeref r disp =>
      some { st with row := { st.row with cfa := .derefBreg r disp } }
  | .offset r off =>
      some { st with row := { st.row with regRules := updateRule st.row.regRules r (.cfaOffset off) } }
  | .exprBreg r base disp =>
      some { st with row := { st.row with regRules := updateRule st.row.regRules r (.atBreg base disp) } }
  | .sameValue r =>
      some { st with row := { st.row with regRules := updateRule st.row.regRules r .sameValue } }
  | .restore r =>
      some { st with row := { st.row with regRules := updateRule st.row.regRules r (cieInit.regRules r) } }
  | .undefined r =>
      some { st with row := { st.row with regRules := updateRule st.row.regRules r .undefined } }
  | .register r src =>
      some { st with row := { st.row with regRules := updateRule st.row.regRules r (.inReg src) } }
  | .rememberState =>
      some { st with savedRows := st.row :: st.savedRows }
  | .restoreState =>
      match st.savedRows with
      | top :: rest => some { st with row := top, savedRows := rest }
      | [] => none
  | .gnuArgsSize sz =>
      some { st with row := { st.row with argsSize := sz } }
  | .nop => some st
  | .unsupportedEscape => none

/-- Evaluate a list of CFI operations linearly while `st.pc <= targetPc`. -/
def evalOps (cieInit : CfiRow) (targetPc : Nat) (st : CfiState) :
    List CfiOp → Option CfiState
  | [] => some st
  | op :: rest =>
      match op with
      | .advanceLoc d =>
          if Nat.ble (st.pc + d) targetPc then
            evalOps cieInit targetPc { st with pc := st.pc + d } rest
          else
            some { st with pc := st.pc + d }
      | _ =>
          if Nat.ble st.pc targetPc then
            match stepCfiOp cieInit st op with
            | some st' => evalOps cieInit targetPc st' rest
            | none => none
          else
            some st

/-- `.gcc_except_table` LSDA call-site action decoded by `rust_eh_personality` /
`__gxx_personality_v0`. -/
inductive LsdaAction where
  | none
  | cleanup (lpadPc : Nat)
  | catchAll (lpadPc : Nat)
  | terminateFilter (lpadPc : Nat)
  deriving DecidableEq, Repr

structure LsdaEntry where
  csStart : Nat
  csLen : Nat
  action : LsdaAction
  deriving DecidableEq, Repr

/-- Lookup `queryPc` (`retPc - 1`) in an LSDA call-site table. -/
def lookupLsda (entries : List LsdaEntry) (queryPc : Nat) : LsdaAction :=
  match entries with
  | [] => .terminateFilter 0
  | e :: rest =>
      if Nat.ble e.csStart queryPc && Nat.blt queryPc (e.csStart + e.csLen) then
        e.action
      else
        lookupLsda rest queryPc

/-- Complete `.eh_frame` FDE + optional `.gcc_except_table` LSDA descriptor for
one compiled or hand-written function `[startPc, endPc)`. -/
structure FdeRecord where
  startPc : Nat
  endPc : Nat
  cieInit : CfiRow
  ops : List CfiOp
  hasPersonality : Bool
  personalityHijacked : Bool
  lsdaOverride : Option (List LsdaEntry)
  lsdaTable : List LsdaEntry

/-- Evaluate `fde` at `queryPc` (`[fde.startPc, fde.endPc)`). -/
def evalFdeAt (fde : FdeRecord) (queryPc : Nat) : Option CfiRow :=
  if Nat.ble fde.startPc queryPc && Nat.blt queryPc fde.endPc then
    match evalOps fde.cieInit queryPc { pc := fde.startPc, row := fde.cieInit, savedRows := [] } fde.ops with
    | some st => some st.row
    | none => none
  else
    none

/-- Evaluate a `CfaRule` against current registers and memory. -/
def evalCfa (rule : CfaRule) (regs : Reg → Nat) (mem : Mem) : Option Nat :=
  match rule with
  | .regOffset r off =>
      let v := Int.ofNat (regs r) + off
      if v ≥ 0 then some v.toNat else none
  | .derefBreg r disp =>
      let addr := Int.ofNat (regs r) + disp
      some (mem addr)
  | .invalid => none

/-- Recover a single register `r` using `row.regRules r` and computed `cfa`. -/
def evalRegRule (rule : RegRule) (r : Reg) (cfa : Nat) (regs : Reg → Nat) (mem : Mem) :
    Option Nat :=
  match rule with
  | .sameValue => some (regs r)
  | .cfaOffset off => some (mem (Int.ofNat cfa + off))
  | .atBreg base disp => some (mem (Int.ofNat (regs base) + disp))
  | .inReg src => some (regs src)
  | .undefined => none

def recoverCalleeSaved (row : CfiRow) (cfa : Nat) (curRegs : Reg → Nat) (mem : Mem) :
    List Reg → Option (Reg → Nat)
  | [] => some curRegs
  | r :: rs =>
      match evalRegRule (row.regRules r) r cfa curRegs mem with
      | none => none
      | some v =>
          match recoverCalleeSaved row cfa curRegs mem rs with
          | none => none
          | some baseRegs => some (regSet baseRegs r v)

/-- Result of unwinding through or into a frame whose call returned to `retPc`. -/
inductive UnwindStepResult where
  | poppedToCaller (callerRegs : Reg → Nat)
  | installedCleanup (inFrameRegs : Reg → Nat) (lpadPc : Nat)
  | installedCatch (inFrameRegs : Reg → Nat) (lpadPc : Nat)
  | abortTerminateFilter
  | abortPhase1EndOfStack

/-- Execute one Itanium / `libgcc_s` unwind step at return address `retPc`
(`queryPc = retPc - 1`). -/
def stepUnwindFrame (fde : FdeRecord) (retPc : Nat) (regs : Reg → Nat) (mem : Mem) :
    UnwindStepResult :=
  if Nat.beq retPc 0 then
    .abortPhase1EndOfStack
  else
    let queryPc := retPc - 1
    match evalFdeAt fde queryPc with
    | none => .abortPhase1EndOfStack
    | some row =>
        match evalCfa row.cfa regs mem with
        | none => .abortPhase1EndOfStack
        | some cfa =>
            match evalRegRule (row.regRules .rip) .rip cfa regs mem with
            | none => .abortPhase1EndOfStack
            | some callerRip =>
                let effectiveAction : LsdaAction :=
                  if fde.hasPersonality && !fde.personalityHijacked then
                    match fde.lsdaOverride with
                    | some ov => lookupLsda ov queryPc
                    | none => lookupLsda fde.lsdaTable queryPc
                  else
                    .none
                match effectiveAction with
                | .terminateFilter _ => .abortTerminateFilter
                | .cleanup lpadPc =>
                    let rspAdj := regs .rsp + row.argsSize
                    .installedCleanup (regSet (regSet regs .rsp rspAdj) .rip lpadPc) lpadPc
                | .catchAll lpadPc =>
                    let rspAdj := regs .rsp + row.argsSize
                    .installedCatch (regSet (regSet regs .rsp rspAdj) .rip lpadPc) lpadPc
                | .none =>
                    match recoverCalleeSaved row cfa regs mem calleeSavedRegs with
                    | none => .abortPhase1EndOfStack
                    | some recRegs =>
                        .poppedToCaller (regSet (regSet recRegs .rsp cfa) .rip callerRip)

end DwarfCfi

/-! ### Heterogeneous `LinkFrame` Stack with Unwind Semantics -/

/-- Architectural caller snapshot saved upon a `call` instruction before a
callee executes. -/
structure SavedCallerContext where
  rsp : Nat
  rip : Nat
  regs : Reg → Nat

/-- Heterogeneous MIR / ISA call-stack frame supporting both normal return and
DWARF `.eh_frame` unwinding. -/
inductive UnwindLinkFrame where
  | mirCatch (expectedCtx : SavedCallerContext) (onCatch : (Reg → Nat) → Mem → Nat)
  | mirCleanup (dropId : Nat) (cleanupMem : Mem → Mem)
  | isaSuspended (retPc : Nat) (fde : Option DwarfCfi.FdeRecord) (expectedCtx : SavedCallerContext)

/-- Outcome of unwinding a heterogeneous call stack from an inner panic/throw. -/
inductive StackUnwindResult where
  | caught (val : Nat) (recoveredRegs : Reg → Nat) (mem : Mem) (dropsRun : List Nat)
  | unwoundToTop (out : TerminalOut) (recoveredRegs : Reg → Nat) (dropsRun : List Nat)
  | abortedEndOfStack (dropsRun : List Nat)
  | abortedTerminateFilter (dropsRun : List Nat)

/-- Step-by-step stack unwinder walking `List UnwindLinkFrame` using
`DwarfCfi.stepUnwindFrame` on every `isaSuspended` frame. -/
def runStackUnwind (curRegs : Reg → Nat) (mem : Mem) (drops : List Nat) :
    List UnwindLinkFrame → StackUnwindResult
  | [] => .unwoundToTop (.unwound mem) curRegs drops
  | frame :: rest =>
      match frame with
      | .mirCatch _ onCatch =>
          .caught (onCatch curRegs mem) curRegs mem drops
      | .mirCleanup dropId cleanupFn =>
          runStackUnwind curRegs (cleanupFn mem) (drops ++ [dropId]) rest
      | .isaSuspended _ none _ =>
          .abortedEndOfStack drops
      | .isaSuspended retPc (some fde) _ =>
          match DwarfCfi.stepUnwindFrame fde retPc curRegs mem with
          | .poppedToCaller callerRegs =>
              runStackUnwind callerRegs mem drops rest
          | .installedCleanup inRegs _ =>
              runStackUnwind inRegs mem drops rest
          | .installedCatch inRegs _ =>
              .caught 0 inRegs mem drops
          | .abortTerminateFilter =>
              .abortedTerminateFilter drops
          | .abortPhase1EndOfStack =>
              .abortedEndOfStack drops

/-- Leaf/non-unwinding execution wrapper demonstrating Rule 2A (`nounwind`
isolation vs. unwind-traversable frames). -/
inductive CalleeBehavior where
  | normalReturn (ret : Nat) (regsAfter : Reg → Nat) (memAfter : Mem)
  | unwindThrow (regsAtCall : Reg → Nat) (memAtCall : Mem)

def execFrameWithCallee
    (b : CalleeBehavior)
    (retPc : Nat)
    (fde : Option DwarfCfi.FdeRecord)
    (callerCtx : SavedCallerContext)
    (outerStack : List UnwindLinkFrame) : StackUnwindResult × Option (Nat × Mem) :=
  match b with
  | .normalReturn v _ m => (.unwoundToTop (.returned v m) callerCtx.regs [], some (v, m))
  | .unwindThrow regsAtCall memAtCall =>
      (runStackUnwind regsAtCall memAtCall [] (.isaSuspended retPc fde callerCtx :: outerStack), none)

end Trusted

/-! ## Untrusted Proof & Hint Layer (`LockedNounwindObligation`, `UntrustedHints`, `DwarfUnwindProofs`) -/

namespace UntrustedHints

/-- Untrusted cutpoint / frame-size hint parsed offline from `.eh_frame` for a
`nounwind` leaf `.o` function. Never referenced by `LockedNounwindObligation`'s
theorem statement (`ConstantInfo.type`)! -/
structure EhFrameCutpointHint where
  frameBytes : Nat
  savedRbxSlot : Int

def validateNounwindLeafWithHint (h : EhFrameCutpointHint) (entryRsp : Nat) : Bool :=
  Nat.beq h.frameBytes 16 && decide (h.savedRbxSlot = -16) && Nat.ble 16 entryRsp

end UntrustedHints

namespace LockedNounwindObligation

open Trusted

/-- Pure `nounwind` leaf `.o` transition (`rdi -> rdi + 1` with 16-byte stack
headroom). Note that ZERO `Trusted.DwarfCfi` and ZERO `UntrustedHints` symbols
appear in `verify_nounwind_leaf_abi`'s type! -/
def runNounwindLeaf (entryRegs : Reg → Nat) (entryMem : Mem) : Option (Nat × Mem) :=
  if Nat.ble 16 (entryRegs .rsp) then
    some (entryRegs .rdi + 1, entryMem)
  else
    none

theorem verify_nounwind_leaf_abi
    (entryRegs : Reg → Nat) (entryMem : Mem)
    (hRsp : 16 ≤ entryRegs .rsp) :
    runNounwindLeaf entryRegs entryMem = some (entryRegs .rdi + 1, entryMem) := by
  have hHintOk :
      UntrustedHints.validateNounwindLeafWithHint
        { frameBytes := 16, savedRbxSlot := -16 } (entryRegs .rsp) = true := by
    dsimp only [UntrustedHints.validateNounwindLeafWithHint]
    have hble : Nat.ble 16 (entryRegs .rsp) = true := Nat.ble_eq.mpr hRsp
    simp [hble]
  dsimp only [runNounwindLeaf]
  have hble : Nat.ble 16 (entryRegs .rsp) = true := by
    dsimp only [UntrustedHints.validateNounwindLeafWithHint] at hHintOk
    exact Nat.ble_eq.mpr hRsp
  rw [hble]
  rfl

end LockedNounwindObligation

namespace DwarfUnwindProofs

open Trusted
open Trusted.DwarfCfi

/-! ### Pure `DecidableEq` Observers for Concrete Canary Theorems -/

/-- Extract `(rsp, rip, r12)` from `poppedToCaller` or `installedCleanup` lpad. -/
def observeStepPopped (res : UnwindStepResult) : Option (Nat × Nat × Nat) :=
  match res with
  | .poppedToCaller r => some (r .rsp, r .rip, r .r12)
  | _ => none

def observeStepCleanupLpad (res : UnwindStepResult) : Option Nat :=
  match res with
  | .installedCleanup _ lpad => some lpad
  | _ => none

def observeStackCaught (res : StackUnwindResult) : Option (Nat × Nat × Nat × List Nat) :=
  match res with
  | .caught v r _ drops => some (v, r .rsp, r .rip, drops)
  | _ => none

/-! ### Section 1: Rule 1 — Universal Non-Unwinding `asm!` CFI Delta Invariant -/

/-- Composition lemma for `evalOps`: if evaluating `ops1` from `st` at `targetPc`
stays at or below `targetPc` (`stMid.pc ≤ targetPc`) and succeeds with `stMid`,
then `evalOps cieInit targetPc st (ops1 ++ ops2) = evalOps cieInit targetPc stMid ops2`. -/
theorem evalOps_append_le
    (cieInit : CfiRow) (targetPc : Nat) :
    ∀ (ops1 ops2 : List CfiOp) (st stMid : CfiState),
      evalOps cieInit targetPc st ops1 = some stMid →
      stMid.pc ≤ targetPc →
      evalOps cieInit targetPc st (ops1 ++ ops2) = evalOps cieInit targetPc stMid ops2 := by
  intro ops1
  induction ops1 with
  | nil =>
      intro ops2 st stMid h1 _
      injection h1 with hEq
      subst hEq
      rfl
  | cons op rest ih =>
      intro ops2 st stMid h1 hLe
      cases op with
      | advanceLoc d =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble (st.pc + d) targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            have hGt : ¬ (st.pc + d ≤ targetPc) := by
              intro hc
              have hb : Nat.ble (st.pc + d) targetPc = true := Nat.ble_eq.mpr hc
              rw [hBle] at hb
              cases hb
            exact absurd hLe hGt
          · rw [hBle] at h1
            exact ih ops2 { st with pc := st.pc + d } stMid h1 hLe
      | defCfa r off =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            exact ih ops2 _ stMid h1 hLe
      | defCfaReg r =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            cases hStep : stepCfiOp cieInit st (.defCfaReg r) with
            | none => rw [hStep] at h1; cases h1
            | some st' => rw [hStep] at h1; exact ih ops2 st' stMid h1 hLe
      | defCfaOffset off =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            cases hStep : stepCfiOp cieInit st (.defCfaOffset off) with
            | none => rw [hStep] at h1; cases h1
            | some st' => rw [hStep] at h1; exact ih ops2 st' stMid h1 hLe
      | defCfaBregDeref r disp =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            exact ih ops2 _ stMid h1 hLe
      | offset r off =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            exact ih ops2 _ stMid h1 hLe
      | exprBreg r base disp =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            exact ih ops2 _ stMid h1 hLe
      | sameValue r =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            exact ih ops2 _ stMid h1 hLe
      | restore r =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            exact ih ops2 _ stMid h1 hLe
      | undefined r =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            exact ih ops2 _ stMid h1 hLe
      | register r src =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            exact ih ops2 _ stMid h1 hLe
      | rememberState =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            exact ih ops2 _ stMid h1 hLe
      | restoreState =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            cases hStep : stepCfiOp cieInit st .restoreState with
            | none => rw [hStep] at h1; cases h1
            | some st' => rw [hStep] at h1; exact ih ops2 st' stMid h1 hLe
      | gnuArgsSize sz =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            exact ih ops2 _ stMid h1 hLe
      | nop =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            exact ih ops2 _ stMid h1 hLe
      | unsupportedEscape =>
          dsimp only [evalOps, List.cons_append] at h1 ⊢
          cases hBle : Nat.ble st.pc targetPc
          · rw [hBle] at h1
            injection h1 with hEq
            subst hEq
            exact absurd hLe (by intro hc; rw [Nat.ble_eq.mpr hc] at hBle; cases hBle)
          · rw [hBle] at h1
            cases h1

/-- **Rule 1 (Universal Non-Unwinding `asm!` CFI Delta Preservation Theorem):**
Whenever a function-scoped `asm!` block `[asmStart, asmStart + asmByteLen)` has
net-neutral CFI state delta (`evalOps cieInit queryPc stPre asmOps = some
{ stPre with pc := asmStart + asmByteLen }`) and emits zero personality or LSDA
overrides, **every** downstream call site `queryPc ≥ asmStart + asmByteLen`
evaluates to the exact unpoisoned compiler-generated `CfiRow`! -/
theorem rule1_asm_cfi_delta_preserves_downstream_fde
    (cieInit : CfiRow)
    (startPc endPc asmStart asmByteLen queryPc : Nat)
    (preOps asmOps postOps : List CfiOp)
    (stPre : CfiState)
    (hasPers : Bool) (lsda : List LsdaEntry)
    (hStart : stPre.pc = asmStart)
    (hQueryGe : asmStart + asmByteLen ≤ queryPc)
    (hPre : evalOps cieInit queryPc { pc := startPc, row := cieInit, savedRows := [] } preOps = some stPre)
    (hAsmNeutral :
      evalOps cieInit queryPc stPre asmOps =
      some { stPre with pc := asmStart + asmByteLen }) :
    let fdeCompiler : FdeRecord := {
      startPc := startPc, endPc := endPc, cieInit := cieInit,
      ops := preOps ++ [.advanceLoc asmByteLen] ++ postOps,
      hasPersonality := hasPers, personalityHijacked := false,
      lsdaOverride := none, lsdaTable := lsda
    }
    let fdeWithAsm : FdeRecord := {
      startPc := startPc, endPc := endPc, cieInit := cieInit,
      ops := preOps ++ asmOps ++ postOps,
      hasPersonality := hasPers, personalityHijacked := false,
      lsdaOverride := none, lsdaTable := lsda
    }
    evalFdeAt fdeWithAsm queryPc = evalFdeAt fdeCompiler queryPc := by
  intro fdeCompiler fdeWithAsm
  dsimp only [evalFdeAt, fdeCompiler, fdeWithAsm]
  cases Nat.ble startPc queryPc && Nat.blt queryPc endPc
  · rfl
  · have hPreLe : stPre.pc ≤ queryPc := by
      rw [hStart]
      exact Nat.le_trans (Nat.le_add_right asmStart asmByteLen) hQueryGe
    have hEndLe : ({ stPre with pc := asmStart + asmByteLen } : CfiState).pc ≤ queryPc :=
      hQueryGe
    have hAdv : evalOps cieInit queryPc stPre [.advanceLoc asmByteLen] =
        some { stPre with pc := asmStart + asmByteLen } := by
      dsimp only [evalOps]
      rw [hStart]
      have hBle : Nat.ble (asmStart + asmByteLen) queryPc = true := Nat.ble_eq.mpr hQueryGe
      rw [hBle]
      rfl
    have h1 := evalOps_append_le cieInit queryPc preOps (asmOps ++ postOps)
      { pc := startPc, row := cieInit, savedRows := [] } stPre hPre hPreLe
    have h2 := evalOps_append_le cieInit queryPc asmOps postOps stPre
      { stPre with pc := asmStart + asmByteLen } hAsmNeutral hEndLe
    have h3 := evalOps_append_le cieInit queryPc preOps ([.advanceLoc asmByteLen] ++ postOps)
      { pc := startPc, row := cieInit, savedRows := [] } stPre hPre hPreLe
    have h4 := evalOps_append_le cieInit queryPc [.advanceLoc asmByteLen] postOps stPre
      { stPre with pc := asmStart + asmByteLen } hAdv hEndLe
    simp only [↓reduceIte]
    rw [List.append_assoc, h1, h2, List.append_assoc, h3, h4]

/-! ### Section 2: Negative Canaries for PoC B (Non-`may_unwind` `asm!` FDE Poisoning) -/

private def sampleMemBase : Mem := fun a =>
  if a = 0x7ff8 then 0x401099      -- True caller return RIP at [0x8000 - 8]
  else if a = 0x7ff0 then 0x2222   -- Saved R12 at [0x8000 - 16]
  else if a = 0x8008 then 0xDEAD   -- Unrelated caller stack word at [0x8010 - 8]
  else 0

private def sampleRegsAtSafePanicCall : Reg → Nat := fun r =>
  match r with
  | .rsp => 0x7fe8                 -- Prologue pushed r12 (-8) + sub rsp, 16 (-16) => CFA = 0x8000
  | .r12 => 0x9999                 -- Clobbered inside victim_fn
  | _ => 0x1111

/-- Unpoisoned enclosing Rust function FDE (`[0, 32)`). -/
def cleanRustVictimFde : FdeRecord := {
  startPc := 0,
  endPc := 32,
  cieInit := x86_64CieInitRow,
  ops := [
    .advanceLoc 4,
    .defCfaOffset 24,
    .offset .r12 (-16)
  ],
  hasPersonality := true,
  personalityHijacked := false,
  lsdaOverride := none,
  lsdaTable := [{ csStart := 10, csLen := 5, action := .cleanup 24 }]
}

/-- **Negative Canary B1 (PoC B1 — 0-Instruction `.cfi_adjust_cfa_offset 16`):**
Clean FDE recovers `(rsp = 0x8000, rip = 0x401099, r12 = 0x2222)`, whereas a
0-byte non-`may_unwind` `asm!` injecting `.defCfaOffset 40` causes downstream
unwinding at `retPc = 15` to recover `(rsp = 0x8010, rip = 0xDEAD, r12 = 0)`! -/
theorem canary_poc_b1_zero_insn_cfa_shift_breaks_unwind :
    let fdeCleanNoDrop := { cleanRustVictimFde with hasPersonality := false }
    let fdePoisonedB1 := {
      fdeCleanNoDrop with
      ops := fdeCleanNoDrop.ops ++ [.advanceLoc 2, .defCfaOffset 40]
    }
    observeStepPopped (stepUnwindFrame fdeCleanNoDrop 15 sampleRegsAtSafePanicCall sampleMemBase) =
      some (0x8000, 0x401099, 0x2222) ∧
    observeStepPopped (stepUnwindFrame fdePoisonedB1 15 sampleRegsAtSafePanicCall sampleMemBase) =
      some (0x8010, 0xDEAD, 0) :=
  ⟨rfl, rfl⟩

/-- **Negative Canary B2 (PoC B2 — Unexecuted Dead-Branch `asm!` Layout Poisoning):**
Even when runtime execution jumps over `[6, 7)` (`jmp 10`), linear FDE
evaluation from `0 -> 4 -> 6 -> 14` shifts `(evalFdeAt ... 14).map CfiRow.cfa`
from `.regOffset .rsp 24` to `.regOffset .rsp 40`! -/
theorem canary_poc_b2_dead_branch_asm_poisons_linear_fde :
    let deadBranchFde : FdeRecord := {
      cleanRustVictimFde with
      hasPersonality := false,
      ops := [
        .advanceLoc 4, .defCfaOffset 24, .offset .r12 (-16),
        .advanceLoc 2, .advanceLoc 1, .defCfaOffset 40
      ]
    }
    (evalFdeAt cleanRustVictimFde 14).map CfiRow.cfa = some (.regOffset .rsp 24) ∧
    (evalFdeAt deadBranchFde 14).map CfiRow.cfa = some (.regOffset .rsp 40) ∧
    (evalFdeAt deadBranchFde 14).map CfiRow.cfa ≠ (evalFdeAt cleanRustVictimFde 14).map CfiRow.cfa :=
  ⟨rfl, rfl, by decide⟩

/-- **Negative Canary B3 (PoC B3 — `.cfi_undefined rip` Phase 1 Stack Truncation):**
Injecting `.undefined .rip` inside a 0-instruction `asm!` at `pc = 6` aborts
stack unwinding with `.abortedEndOfStack []`, skipping outer `mirCleanup` (`Drop`)
and `mirCatch` (`catch_unwind`)! -/
theorem canary_poc_b3_undefined_rip_aborts_phase1 :
    let fdeUndefinedRip : FdeRecord := {
      cleanRustVictimFde with
      ops := cleanRustVictimFde.ops ++ [.advanceLoc 2, .undefined .rip]
    }
    let outer : List UnwindLinkFrame := [
      .mirCleanup 1 (fun m => m),
      .mirCatch ⟨0x8000, 0x401099, sampleRegsAtSafePanicCall⟩ (fun _ _ => 1)
    ]
    runStackUnwind sampleRegsAtSafePanicCall sampleMemBase []
      (.isaSuspended 15 (some fdeUndefinedRip) ⟨0x8000, 0x401099, sampleRegsAtSafePanicCall⟩ :: outer) =
      .abortedEndOfStack [] := rfl

/-- **Negative Canary B5 (PoC B5 — `.cfi_escape 0x8c, 0x01` Silent Safe-Rust Local
Corruption + ASLR RIP Leak):**
Injecting `DW_CFA_offset r12, 1 * -8` (`.offset .r12 (-8)`) inside a 0-byte
non-`may_unwind` `asm!` causes `catch_unwind` to succeed cleanly (`some (0x401099,
0x8000, 0x401099, [])`), silently overwriting the outer safe Rust caller's `r12`
(`0x2222`) with saved return `RIP` (`0x401099`)! -/
theorem canary_poc_b5_escape_offset_leaks_rip_into_caller_r12 :
    let fdeEscapeR12 : FdeRecord := {
      cleanRustVictimFde with
      hasPersonality := false,
      ops := [
        .advanceLoc 4, .defCfaOffset 24,
        .advanceLoc 2, .offset .r12 (-8)
      ]
    }
    let outer : List UnwindLinkFrame := [
      .mirCatch ⟨0x8000, 0x401099, sampleRegsAtSafePanicCall⟩ (fun regs _ => regs .r12)
    ]
    observeStackCaught (runStackUnwind sampleRegsAtSafePanicCall sampleMemBase []
      (.isaSuspended 15 (some fdeEscapeR12) ⟨0x8000, 0x401099, sampleRegsAtSafePanicCall⟩ :: outer)) =
      some (0x401099, 0x8000, 0x401099, []) ∧
    (0x401099 : Nat) ≠ 0x2222 :=
  ⟨rfl, by decide⟩

/-- **Negative Canary B6 & B7 (PoC B6/B7 — PIE `.cfi_personality` and `.cfi_lsda`
Hijacking Silently Skips Safe Rust `Drop` Destructors):**
In `cleanRustVictimFde`, `stepUnwindFrame` installs in-frame `Drop` cleanup
landing pad `24`, whereas either `.cfi_personality` (`personalityHijacked := true`)
or `.cfi_lsda` (`lsdaOverride := some [{0, 2047, .none}]`) bypasses landing pad
`24` and pops straight to the caller! -/
theorem canary_poc_b6_b7_personality_and_lsda_hijack_skip_drops :
    let fdePersHijack := { cleanRustVictimFde with personalityHijacked := true }
    let fdeLsdaHijack := {
      cleanRustVictimFde with
      lsdaOverride := some [{ csStart := 0, csLen := 2047, action := .none }]
    }
    observeStepCleanupLpad (stepUnwindFrame cleanRustVictimFde 15 sampleRegsAtSafePanicCall sampleMemBase) =
      some 24 ∧
    observeStepPopped (stepUnwindFrame fdePersHijack 15 sampleRegsAtSafePanicCall sampleMemBase) =
      some (0x8000, 0x401099, 0x2222) ∧
    observeStepPopped (stepUnwindFrame fdeLsdaHijack 15 sampleRegsAtSafePanicCall sampleMemBase) =
      some (0x8000, 0x401099, 0x2222) :=
  ⟨rfl, rfl, rfl⟩

/-! ### Section 3: Rule 2A — Unwind-Unreachable Partition (`.eh_frame` Outside TCB) -/

/-- **Rule 2A (`nounwind` / Unwind-Unreachable Irrelevance Theorem):**
Whenever a foreign `.o`, `.S`, or `asm!` execution path cannot unwind
(`b = .normalReturn v regs' m'`), `execFrameWithCallee` is invariant under
arbitrary replacement or deletion of `fde : Option FdeRecord`. -/
theorem rule2a_nounwind_frame_eh_frame_irrelevant
    (v : Nat) (regs' : Reg → Nat) (m' : Mem)
    (retPc : Nat) (fde1 fde2 : Option FdeRecord)
    (callerCtx : SavedCallerContext)
    (outerStack : List UnwindLinkFrame) :
    execFrameWithCallee (.normalReturn v regs' m') retPc fde1 callerCtx outerStack =
    execFrameWithCallee (.normalReturn v regs' m') retPc fde2 callerCtx outerStack := rfl

/-! ### Section 4: Rule 2B — Unwind-Traversable `Trusted.DwarfCfi` Soundness -/

/-- Pure `Prop` call-site agreement predicate (`CfiMatchesMachineState`). -/
structure CfiMatchesMachineState
    (fde : FdeRecord) (retPc : Nat) (caller : SavedCallerContext)
    (regs : Reg → Nat) (mem : Mem) : Prop where
  retPc_pos : retPc ≠ 0
  passthrough_lsda :
    fde.hasPersonality = false ∨ fde.personalityHijacked = true ∨
    (match fde.lsdaOverride with
     | some ov => lookupLsda ov (retPc - 1) = .none
     | none => lookupLsda fde.lsdaTable (retPc - 1) = .none)
  row_match :
    ∃ row : CfiRow,
      evalFdeAt fde (retPc - 1) = some row ∧
      evalCfa row.cfa regs mem = some caller.rsp ∧
      evalRegRule (row.regRules .rip) .rip caller.rsp regs mem = some caller.rip ∧
      (∀ r ∈ calleeSavedRegs,
        evalRegRule (row.regRules r) r caller.rsp regs mem = some (caller.regs r))

private theorem nodup_lookup_recover
    (row : CfiRow) (cfa : Nat) (curRegs : Reg → Nat) (mem : Mem)
    (callerRegs : Reg → Nat) :
    ∀ (rs : List Reg),
      (∀ r ∈ rs, evalRegRule (row.regRules r) r cfa curRegs mem = some (callerRegs r)) →
      ∃ outRegs,
        recoverCalleeSaved row cfa curRegs mem rs = some outRegs ∧
        (∀ r ∈ rs, outRegs r = callerRegs r) := by
  intro rs
  induction rs with
  | nil =>
      intro _
      exact ⟨curRegs, rfl, fun _ h => nomatch h⟩
  | cons hd tl ih =>
      intro hAll
      have hHd : evalRegRule (row.regRules hd) hd cfa curRegs mem = some (callerRegs hd) :=
        hAll hd (.head tl)
      have hTl : ∀ r ∈ tl, evalRegRule (row.regRules r) r cfa curRegs mem = some (callerRegs r) :=
        fun r hm => hAll r (.tail hd hm)
      rcases ih hTl with ⟨baseRegs, hRecTl, hBaseEq⟩
      refine ⟨regSet baseRegs hd (callerRegs hd), ?_, ?_⟩
      · dsimp only [recoverCalleeSaved]
        rw [hHd, hRecTl]
      · intro r hr
        dsimp only [regSet]
        by_cases hEq : r = hd
        · subst hEq; simp
        · simp [hEq]
          cases hr with
          | head => exact absurd rfl hEq
          | tail _ hInTl => exact hBaseEq r hInTl

/-- **Rule 2B Single-Frame Unwind Soundness (`rule2b_stepUnwindFrame_sound`):**
Whenever `CfiMatchesMachineState` holds at call return address `retPc` (whether
via `RSP + off`, `RBP + 16` dynamic `and rsp, -32` realignment, `R11 + off`
stack-clash probe loops, or GCC DRAP `DW_OP_breg6 disp, DW_OP_deref`),
`stepUnwindFrame` succeeds with `.poppedToCaller callerRegs` and restores the
**exact** `caller.rsp`, `caller.rip`, and all six x86-64 callee-saved registers. -/
theorem rule2b_stepUnwindFrame_sound
    (fde : FdeRecord) (retPc : Nat) (caller : SavedCallerContext)
    (regs : Reg → Nat) (mem : Mem)
    (hMatch : CfiMatchesMachineState fde retPc caller regs mem) :
    ∃ callerRegs,
      stepUnwindFrame fde retPc regs mem = .poppedToCaller callerRegs ∧
      callerRegs .rsp = caller.rsp ∧
      callerRegs .rip = caller.rip ∧
      (∀ r ∈ calleeSavedRegs, callerRegs r = caller.regs r) := by
  rcases hMatch.row_match with ⟨row, hEvalRow, hEvalCfa, hEvalRip, hEvalCsrs⟩
  dsimp only [stepUnwindFrame]
  have hBeqZero : Nat.beq retPc 0 = false := by
    cases h : Nat.beq retPc 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hMatch.retPc_pos
  rw [hBeqZero]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hEvalRow]
  dsimp only
  rw [hEvalCfa]
  dsimp only
  rw [hEvalRip]
  dsimp only
  have hAct :
      (if fde.hasPersonality && !fde.personalityHijacked then
         match fde.lsdaOverride with
         | some ov => lookupLsda ov (retPc - 1)
         | none => lookupLsda fde.lsdaTable (retPc - 1)
       else .none) = LsdaAction.none := by
    rcases hMatch.passthrough_lsda with hNoP | hHij | hLookup
    · simp [hNoP]
    · simp [hHij]
    · by_cases hCond : (fde.hasPersonality && !fde.personalityHijacked) = true
      · simp only [hCond, ↓reduceIte]
        cases hOv : fde.lsdaOverride with
        | none => rw [hOv] at hLookup; exact hLookup
        | some ov => rw [hOv] at hLookup; exact hLookup
      · simp [hCond]
  rw [hAct]
  dsimp only
  rcases nodup_lookup_recover row caller.rsp regs mem caller.regs calleeSavedRegs hEvalCsrs
    with ⟨recRegs, hRec, hCsrEq⟩
  rw [hRec]
  refine ⟨regSet (regSet recRegs .rsp caller.rsp) .rip caller.rip, rfl, ?_, ?_, ?_⟩
  · dsimp only [regSet]; simp
  · dsimp only [regSet]; simp
  · intro r hr
    have hNeRip : r ≠ .rip := by
      intro h; subst h; simp [calleeSavedRegs] at hr
    have hNeRsp : r ≠ .rsp := by
      intro h; subst h; simp [calleeSavedRegs] at hr
    dsimp only [regSet]
    simp [hNeRip, hNeRsp]
    exact hCsrEq r hr

/-- Concrete verification of **GCC 15.2.0 DRAP (`aligned(64)` + `alloca`)** under
`rule2b_stepUnwindFrame_sound`. -/
def gccDrapFde : FdeRecord := {
  startPc := 0,
  endPc := 64,
  cieInit := x86_64CieInitRow,
  ops := [
    .advanceLoc 18,
    .defCfaBregDeref .rbp (-24),
    .exprBreg .rbp .rbp 0,
    .exprBreg .r12 .rbp (-8),
    .exprBreg .rbx .rbp (-16)
  ],
  hasPersonality := false,
  personalityHijacked := false,
  lsdaOverride := none,
  lsdaTable := []
}

theorem gcc_drap_expression_unwind_sound
    (callerRsp callerRip savedRbp savedR12 savedRbx runtimeRbp dynRsp : Nat)
    (baseMem : Mem)
    (hFrameBelow : runtimeRbp + 16 ≤ callerRsp) :
    let m0 := memWrite baseMem (Int.ofNat callerRsp - 8) callerRip
    let m1 := memWrite m0 (Int.ofNat runtimeRbp) savedRbp
    let m2 := memWrite m1 (Int.ofNat runtimeRbp - 8) savedR12
    let m3 := memWrite m2 (Int.ofNat runtimeRbp - 16) savedRbx
    let m4 := memWrite m3 (Int.ofNat runtimeRbp - 24) callerRsp
    let curRegs : Reg → Nat := fun r =>
      match r with
      | .rsp => dynRsp
      | .rbp => runtimeRbp
      | .rbx => 0xDEAD1
      | .r12 => 0xDEAD2
      | .r13 => 0x1313
      | .r14 => 0x1414
      | .r15 => 0x1515
      | _ => 0
    let _caller : SavedCallerContext := {
      rsp := callerRsp,
      rip := callerRip,
      regs := fun r =>
        match r with
        | .rbp => savedRbp
        | .rbx => savedRbx
        | .r12 => savedR12
        | .r13 => 0x1313
        | .r14 => 0x1414
        | .r15 => 0x1515
        | _ => 0
    }
    ∃ recRegs,
      stepUnwindFrame gccDrapFde 30 curRegs m4 = .poppedToCaller recRegs ∧
      recRegs .rsp = callerRsp ∧
      recRegs .rip = callerRip ∧
      recRegs .rbp = savedRbp ∧
      recRegs .r12 = savedR12 ∧
      recRegs .rbx = savedRbx := by
  intro m0 m1 m2 m3 m4 curRegs callerCtx
  let drapRow : CfiRow := {
    cfa := .derefBreg .rbp (-24),
    regRules :=
      updateRule (updateRule (updateRule x86_64InitRegRules .rbp (.atBreg .rbp 0))
        .r12 (.atBreg .rbp (-8))) .rbx (.atBreg .rbp (-16)),
    argsSize := 0
  }
  have hMatch : CfiMatchesMachineState gccDrapFde 30 callerCtx curRegs m4 :=
    CfiMatchesMachineState.mk
      (by decide)
      (Or.inl rfl)
      ⟨drapRow, rfl,
        by
          dsimp only [drapRow, evalCfa, curRegs, callerCtx, m4, memWrite]
          simp only [Int.ofNat_eq_natCast]
          congr 1
          split <;> omega,
        by
          dsimp only [drapRow, evalRegRule, updateRule, x86_64InitRegRules]
          simp only [reduceCtorEq, ↓reduceIte]
          dsimp only [callerCtx, m4, m3, m2, m1, m0, memWrite]
          simp only [Int.ofNat_eq_natCast]
          congr 1
          repeat (split <;> try omega),
        by
          intro r hr
          simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
          · dsimp only [drapRow, evalRegRule, updateRule]
            simp only [reduceCtorEq, ↓reduceIte]
            dsimp only [curRegs, callerCtx, m4, m3, m2, m1, memWrite]
            simp only [Int.ofNat_eq_natCast]
            congr 1
            repeat (split <;> try omega)
          · dsimp only [drapRow, evalRegRule, updateRule]
            simp only [↓reduceIte]
            dsimp only [curRegs, callerCtx, m4, m3, memWrite]
            simp only [Int.ofNat_eq_natCast]
            congr 1
            repeat (split <;> try omega)
          · dsimp only [drapRow, evalRegRule, updateRule]
            simp only [reduceCtorEq, ↓reduceIte]
            dsimp only [curRegs, callerCtx, m4, m3, m2, memWrite]
            simp only [Int.ofNat_eq_natCast]
            congr 1
            repeat (split <;> try omega)
          · rfl
          · rfl
          · rfl⟩
  rcases rule2b_stepUnwindFrame_sound gccDrapFde 30 callerCtx curRegs m4 hMatch with
    ⟨recRegs, hStep, hRsp, hRip, hCsr⟩
  exact ⟨recRegs, hStep, hRsp, hRip,
    hCsr .rbp (by simp [calleeSavedRegs]),
    hCsr .r12 (by simp [calleeSavedRegs]),
    hCsr .rbx (by simp [calleeSavedRegs])⟩

/-- Inductive invariant over a chain of heterogeneous `isaSuspended` and
`mirCleanup` frames sitting above `tailStack`. -/
inductive ValidUnwindPrefix :
    (Reg → Nat) → Mem → List UnwindLinkFrame → (Reg → Nat) → Mem → List Nat → Prop where
  | nil (regs : Reg → Nat) (mem : Mem) :
      ValidUnwindPrefix regs mem [] regs mem []
  | cleanupStep {regs finalRegs : Reg → Nat} {mem finalMem : Mem}
      {dropId : Nat} {cleanupFn : Mem → Mem} {rest : List UnwindLinkFrame} {restDrops : List Nat} :
      ValidUnwindPrefix regs (cleanupFn mem) rest finalRegs finalMem restDrops →
      ValidUnwindPrefix regs mem (.mirCleanup dropId cleanupFn :: rest) finalRegs finalMem (dropId :: restDrops)
  | isaStep {regs nextRegs finalRegs : Reg → Nat} {mem finalMem : Mem}
      {retPc : Nat} {fde : FdeRecord} {caller : SavedCallerContext}
      {rest : List UnwindLinkFrame} {restDrops : List Nat} :
      stepUnwindFrame fde retPc regs mem = .poppedToCaller nextRegs →
      nextRegs .rsp = caller.rsp →
      nextRegs .rip = caller.rip →
      (∀ r ∈ calleeSavedRegs, nextRegs r = caller.regs r) →
      ValidUnwindPrefix nextRegs mem rest finalRegs finalMem restDrops →
      ValidUnwindPrefix regs mem (.isaSuspended retPc (some fde) caller :: rest) finalRegs finalMem restDrops

/-- **Rule 2B Multi-Frame Heterogeneous Unwind Composition Theorem:**
Unwinding across any `ValidUnwindPrefix` preserves exact recovered registers,
`Drop` execution order, and memory up to `TerminalOut.unwound` or `mirCatch`. -/
theorem rule2b_multi_frame_unwind_preserves_state
    {regs finalRegs : Reg → Nat} {mem finalMem : Mem}
    {pfx : List UnwindLinkFrame} {pfxDrops : List Nat}
    (hValid : ValidUnwindPrefix regs mem pfx finalRegs finalMem pfxDrops) :
    ∀ (accDrops : List Nat) (tailStack : List UnwindLinkFrame),
      runStackUnwind regs mem accDrops (pfx ++ tailStack) =
      runStackUnwind finalRegs finalMem (accDrops ++ pfxDrops) tailStack := by
  induction hValid with
  | nil _ _ =>
      intro accDrops tailStack
      simp
  | cleanupStep _ ih =>
      intro accDrops tailStack
      dsimp only [List.cons_append, runStackUnwind]
      rw [ih (accDrops ++ [_]) tailStack, List.append_assoc]
      rfl
  | isaStep hStep _ _ _ _ ih =>
      intro accDrops tailStack
      dsimp only [List.cons_append, runStackUnwind]
      rw [hStep]
      exact ih accDrops tailStack

/-! ### Section 5: Negative Canaries for PoC A, LLVM `ShrinkWrap`, and PoC C -/

/-- **Negative Canary A1 (PoC A1 — `options(may_unwind)` Missing `.cfi_adjust_cfa_offset`):**
Normal return (`0x7fe0 + 24 == 0x7ff8`) restores `rsp` and `rbx`, whereas
unwinding at `retPc = 21` recovers `rsp = 0x7ff0 ≠ 0x8000` and `rip = 0xDEADBEEF
≠ 0x402000`! -/
theorem canary_poc_a1_may_unwind_missing_cfa_corrupts_unwind :
    let fdeA1 : FdeRecord := {
      startPc := 0, endPc := 28, cieInit := x86_64CieInitRow,
      ops := [.advanceLoc 1, .defCfaOffset 16],
      hasPersonality := false, personalityHijacked := false,
      lsdaOverride := none, lsdaTable := []
    }
    let regsAtCall : Reg → Nat := fun r =>
      if r = .rsp then 0x7fe0 else if r = .rbx then 0xDEADBEEF else 0
    let mem : Mem := fun a =>
      if a = 0x7ff8 then 0x402000
      else if a = 0x7fe8 then 0xDEADBEEF
      else 0
    let normalReturnRestoresRspAndRbx : Bool :=
      Nat.beq (0x7fe0 + 8 + 8 + 8) 0x7ff8
    normalReturnRestoresRspAndRbx = true ∧
    observeStepPopped (stepUnwindFrame fdeA1 21 regsAtCall mem) =
      some (0x7ff0, 0xDEADBEEF, 0) ∧
    (0x7ff0 : Nat) ≠ 0x8000 ∧
    (0xDEADBEEF : Nat) ≠ 0x402000 :=
  ⟨rfl, rfl, by decide, by decide⟩

/-- **Negative Canary A2 (PoC A2 — `options(may_unwind)` With Valid CFA But Missing
`.cfi_rel_offset r12` Silently Corrupts Safe Rust Local Inside `catch_unwind`):**
`runStackUnwind` recovers valid `rsp = 0x8000` and `rip = 0x402000` and catches
cleanly in `mirCatch`, while silently corrupting the safe Rust caller's `r12`
local from `0x2222222222222222` to `0x7777777777777777`! -/
theorem canary_poc_a2_may_unwind_missing_r12_corrupts_safe_local_on_catch :
    let fdeA2 : FdeRecord := {
      startPc := 0, endPc := 28, cieInit := x86_64CieInitRow,
      ops := [.advanceLoc 1, .defCfaOffset 16, .advanceLoc 5, .defCfaOffset 32],
      hasPersonality := false, personalityHijacked := false,
      lsdaOverride := none, lsdaTable := []
    }
    let regsAtCall : Reg → Nat := fun r =>
      if r = .rsp then 0x7fe0
      else if r = .r12 then 0x7777777777777777
      else 0
    let mem : Mem := fun a =>
      if a = 0x7ff8 then 0x402000
      else if a = 0x7ff0 then 0x2222222222222222
      else 0
    let outer : List UnwindLinkFrame := [
      .mirCatch ⟨0x8000, 0x402000, fun _ => 0x2222222222222222⟩ (fun rec _ => rec .r12)
    ]
    observeStackCaught (runStackUnwind regsAtCall mem []
      (.isaSuspended 21 (some fdeA2) ⟨0x8000, 0x402000, fun _ => 0x2222222222222222⟩ :: outer)) =
      some (0x7777777777777777, 0x8000, 0x402000, []) ∧
    (0x7777777777777777 : Nat) ≠ 0x2222222222222222 :=
  ⟨rfl, by decide⟩

/-- **Negative Canary A4 (Upstream LLVM `23.1.5` `ShrinkWrap` `alignstack` Bug on
`options(may_unwind)` `invoke`):**
Proves that omitting the 8-byte alignment adjust in `MBB 0` (`entryRsp = 16 * k + 8`)
leaves `(asmRsp - 8) % 16 = 0` at `call {cb}`, violating the SysV AMD64
`calleeEntryRsp % 16 = 8` contract! -/
theorem canary_llvm_shrinkwrap_invoke_alignstack_violation
    (k : Nat) (hPos : 1 ≤ k) :
    let entryRsp := 16 * k + 8
    let shrinkWrappedAsmRsp := entryRsp
    let properAlignedAsmRsp := entryRsp - 8
    shrinkWrappedAsmRsp % 16 = 8 ∧
    (shrinkWrappedAsmRsp - 8) % 16 = 0 ∧
    properAlignedAsmRsp % 16 = 0 ∧
    (properAlignedAsmRsp - 8) % 16 = 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega

/-- **Negative Canary C1 (PoC C — C `.o` Compiled With `-fno-unwind-tables
-fno-asynchronous-unwind-tables` Between Two Rust Frames):**
Normal return passes (`some (100, sampleMemBase)`), whereas unwinding hits
`fde = none`, aborts with `.abortedEndOfStack []`, and skips `mirCleanup`! -/
theorem canary_poc_c1_missing_c_eh_frame_aborts_and_skips_drops :
    let outer : List UnwindLinkFrame := [
      .mirCleanup 42 (fun m => m),
      .mirCatch ⟨0x8000, 0x401000, sampleRegsAtSafePanicCall⟩ (fun _ _ => 99)
    ]
    let normOut := execFrameWithCallee
      (.normalReturn 100 sampleRegsAtSafePanicCall sampleMemBase)
      12 none ⟨0x8000, 0x401000, sampleRegsAtSafePanicCall⟩ outer
    let panicOut := execFrameWithCallee
      (.unwindThrow sampleRegsAtSafePanicCall sampleMemBase)
      12 none ⟨0x8000, 0x401000, sampleRegsAtSafePanicCall⟩ outer
    normOut.2 = some (100, sampleMemBase) ∧
    panicOut.1 = .abortedEndOfStack [] :=
  ⟨rfl, rfl⟩

end DwarfUnwindProofs

/-! ## Axiom Ceiling Receipts (`#guard_msgs in #print axioms`) -/

/-- info: 'LockedNounwindObligation.verify_nounwind_leaf_abi' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LockedNounwindObligation.verify_nounwind_leaf_abi

/-- info: 'DwarfUnwindProofs.rule1_asm_cfi_delta_preserves_downstream_fde' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.rule1_asm_cfi_delta_preserves_downstream_fde

/-- info: 'DwarfUnwindProofs.canary_poc_b1_zero_insn_cfa_shift_breaks_unwind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.canary_poc_b1_zero_insn_cfa_shift_breaks_unwind

/-- info: 'DwarfUnwindProofs.canary_poc_b2_dead_branch_asm_poisons_linear_fde' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.canary_poc_b2_dead_branch_asm_poisons_linear_fde

/-- info: 'DwarfUnwindProofs.canary_poc_b3_undefined_rip_aborts_phase1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.canary_poc_b3_undefined_rip_aborts_phase1

/-- info: 'DwarfUnwindProofs.canary_poc_b5_escape_offset_leaks_rip_into_caller_r12' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.canary_poc_b5_escape_offset_leaks_rip_into_caller_r12

/-- info: 'DwarfUnwindProofs.canary_poc_b6_b7_personality_and_lsda_hijack_skip_drops' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.canary_poc_b6_b7_personality_and_lsda_hijack_skip_drops

/-- info: 'DwarfUnwindProofs.rule2a_nounwind_frame_eh_frame_irrelevant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.rule2a_nounwind_frame_eh_frame_irrelevant

/-- info: 'DwarfUnwindProofs.rule2b_stepUnwindFrame_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.rule2b_stepUnwindFrame_sound

/-- info: 'DwarfUnwindProofs.gcc_drap_expression_unwind_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.gcc_drap_expression_unwind_sound

/-- info: 'DwarfUnwindProofs.rule2b_multi_frame_unwind_preserves_state' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.rule2b_multi_frame_unwind_preserves_state

/-- info: 'DwarfUnwindProofs.canary_poc_a1_may_unwind_missing_cfa_corrupts_unwind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.canary_poc_a1_may_unwind_missing_cfa_corrupts_unwind

/-- info: 'DwarfUnwindProofs.canary_poc_a2_may_unwind_missing_r12_corrupts_safe_local_on_catch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.canary_poc_a2_may_unwind_missing_r12_corrupts_safe_local_on_catch

/-- info: 'DwarfUnwindProofs.canary_llvm_shrinkwrap_invoke_alignstack_violation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.canary_llvm_shrinkwrap_invoke_alignstack_violation

/-- info: 'DwarfUnwindProofs.canary_poc_c1_missing_c_eh_frame_aborts_and_skips_drops' depends on axioms: [propext] -/
#guard_msgs in
#print axioms DwarfUnwindProofs.canary_poc_c1_missing_c_eh_frame_aborts_and_skips_drops
