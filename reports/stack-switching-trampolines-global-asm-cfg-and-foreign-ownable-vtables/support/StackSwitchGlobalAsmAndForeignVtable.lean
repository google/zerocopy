-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Stack-Switching Trampolines, Section-Wide `global_asm!` Cutpoint Graphs,
13-Opcode `DwarfCfi` (`DW_CFA_undefined`), and COFE-Free `ForeignOwnable` Vtables

Self-contained Lean 4 (`v4.34.1`) mechanization using strictly `Init.*` (zero
external dependencies, zero `sorry`, zero `axiom`, zero `opaque`, zero
`partial`, zero `unsafe`, zero `native_decide`, zero `bv_decide`, zero
`set_option`, zero Iris COFEs or step-indexing).

## Summary of Mechanized Theorems

1. **`SectionWideAsmCfg` (Section-Wide Entry-Cutpoint Graph vs. Naive Lifters):**
   - `canary_st_size_zero_vacuous_accepts_faulting_body`
   - `canary_st_size_rejects_shared_local_tail_helper`
   - `canary_next_sym_partition_breaks_fallthrough_and_cross_sym_jump`
   - `swecg_cutpoint_sound`
   - `swecg_verifies_five_entry_cluster`

2. **`StackPoolAndCfi` (13-Opcode `DwarfCfi` with `DW_CFA_undefined`, Linear
   `StackPool`, and Dormant-Stack Tree Borrows):**
   - `stack_root_cfi_undefined_halts_cleanly`
   - `canary_x64_missing_undef_reads_unmapped`
   - `canary_a64_missing_undef_sameval_loops_forever`
   - `two_entry_switch_preserves_protectors_and_disjointness`
   - `dormant_stack_tree_borrows_complete_matrix`

3. **`ForeignOwnableVtable` (COFE-Free First-Order Linear `ForeignHandlePool`
   for Temporally Disjoint C Ops-Table Vtables):**
   - `reentrant_shared_ioctl_arbitrary_depth_sound`
   - `cofe_free_vtable_trace_sound`
   - `canary_bug1_open_nonzero_after_into_foreign_leaks_handle`
   - `canary_bug2_reentrant_unguarded_borrow_mut_aliasing_ub`
   - `canary_bug3_double_release_from_foreign_uaf`
-/

namespace StackSwitchGlobalAsmAndForeignVtable

/-! ## Part 1: Section-Wide Entry-Cutpoint Graph (`SWECG`) for `global_asm!` and `.S` -/

namespace SectionWideAsmCfg

/-- Decoded machine instruction at a byte offset inside an executable ELF
section (`SHF_ALLOC | SHF_EXECINSTR`). -/
inductive AsmInsn where
  | addImm (byteLen : Nat) (imm : Nat)
  | mulImm (byteLen : Nat) (factor : Nat)
  | addRipData (byteLen : Nat) (dataOff : Nat)
  | movRaxRdi (byteLen : Nat)
  | jmp (byteLen : Nat) (targetOff : Nat)
  | jeFlagZero (byteLen : Nat) (targetOff : Nat)
  | ret (byteLen : Nat)
  | embeddedData
  deriving DecidableEq, Repr

/-- Symbol-table record (`SHT_SYMTAB`) inside an executable section. -/
structure ElfSym where
  symId : Nat
  stValue : Nat
  stSize : Nat
  deriving DecidableEq, Repr

/-- Executable ELF section image: total byte size, instruction/data layout by
byte offset, and read-only constant values stored at embedded data offsets. -/
structure ExecSection where
  secSize : Nat
  decodeAt : Nat → AsmInsn
  roQuadAt : Nat → Nat

/-- Machine register state for section-level control-flow semantics. -/
structure RegState where
  pc : Nat
  rdi : Nat
  esi : Nat
  rax : Nat
  deriving DecidableEq, Repr

inductive StepExecOut where
  | step (next : RegState)
  | returned (rax : Nat)
  | fault
  deriving DecidableEq, Repr

/-- One small-step execution transition inside `[rangeLo, rangeHi)` of `sec`.
Executing `embeddedData` or branching/falling outside `[rangeLo, rangeHi)`
fails closed with `.fault`. -/
def stepInSlice (sec : ExecSection) (rangeLo rangeHi : Nat) (st : RegState) :
    StepExecOut :=
  if decide (st.pc < rangeLo ∨ rangeHi ≤ st.pc) then
    .fault
  else
    match sec.decodeAt st.pc with
    | .addImm len imm =>
        if decide (len = 0 ∨ rangeHi < st.pc + len) then .fault
        else .step { st with pc := st.pc + len, rdi := st.rdi + imm }
    | .mulImm len factor =>
        if decide (len = 0 ∨ rangeHi < st.pc + len) then .fault
        else .step { st with pc := st.pc + len, rax := st.rdi * factor }
    | .addRipData len dataOff =>
        if decide (len = 0 ∨ rangeHi < st.pc + len ∨ sec.secSize < dataOff + 8) then
          .fault
        else
          .step { st with pc := st.pc + len, rax := st.rax + sec.roQuadAt dataOff }
    | .movRaxRdi len =>
        if decide (len = 0 ∨ rangeHi < st.pc + len) then .fault
        else .step { st with pc := st.pc + len, rax := st.rdi }
    | .jmp len target =>
        if decide (len = 0 ∨ target < rangeLo ∨ rangeHi ≤ target) then .fault
        else .step { st with pc := target }
    | .jeFlagZero len target =>
        if decide (len = 0 ∨ rangeHi < st.pc + len ∨ target < rangeLo ∨ rangeHi ≤ target) then
          .fault
        else if st.esi = 0 then
          .step { st with pc := target }
        else
          .step { st with pc := st.pc + len }
    | .ret len =>
        if decide (len = 0 ∨ rangeHi < st.pc + len) then .fault
        else .returned st.rax
    | .embeddedData => .fault

/-- Multi-step bounded evaluator over `[rangeLo, rangeHi)`. -/
def runInSlice (sec : ExecSection) (rangeLo rangeHi : Nat) :
    Nat → RegState → Option Nat
  | 0, _ => none
  | fuel + 1, st =>
      match stepInSlice sec rangeLo rangeHi st with
      | .returned v => some v
      | .fault => none
      | .step st' => runInSlice sec rangeLo rangeHi fuel st'

/-- Naive Lifter A: per-symbol `[st_value, st_value + st_size)` byte slicing,
vacuously accepting `st_size = 0` symbols (`global_asm!` / Perlasm `.S`). -/
def naiveStSizeAcceptsVacuous (sec : ExecSection) (sym : ElfSym) : Prop :=
  sym.stSize = 0 ∨
    ∀ rdi esi, ∃ fuel v,
      runInSlice sec sym.stValue (sym.stValue + sym.stSize) fuel
        { pc := sym.stValue, rdi := rdi, esi := esi, rax := 0 } = some v

/-- Negative Canary 1: When `global_asm!` or Perlasm `.S` omits `.size`
(`st_size = 0`), vacuous per-symbol slicing accepts a symbol whose entry byte
immediately faults! -/
theorem canary_st_size_zero_vacuous_accepts_faulting_body :
    ∃ (sec : ExecSection) (sym : ElfSym),
      sym.stSize = 0 ∧
      naiveStSizeAcceptsVacuous sec sym ∧
      stepInSlice sec 0 sec.secSize
        { pc := sym.stValue, rdi := 7, esi := 0, rax := 0 } = .fault := by
  refine ⟨{ secSize := 8, decodeAt := fun _ => .embeddedData, roQuadAt := fun _ => 0 },
    { symId := 1, stValue := 0, stSize := 0 }, rfl, Or.inl rfl, rfl⟩

/-- Concrete 61-byte multi-entry `global_asm!` section mirroring Probe Suite 2:
- `0x00`: `gasm_nosize_fast` (`st_size = 0`), falls through into `0x04`!
- `0x04`: `gasm_nosize_common` (`st_size = 0`), jumps to `.Lshared_tail` (`0x10`)
- `0x0a`: `gasm_sized_with_shared_tail` (`st_size = 6`), jumps to `.Lshared_tail` (`0x10`)
- `0x10`: `.Lshared_tail` (`STB_LOCAL`): `imul rax, rdi, 2`; `add rax, [rip -> 0x20]`; `ret`
- `0x20`: `.Linline_const` (8-byte constant `100` embedded inside `.text`!)
- `0x28`: `gasm_two_entry_enter` (`st_size = 12`): `je 0x30`; `add rdi, 100`; `0x30`: `mov rax, rdi`; `ret`
- `0x34`: `gasm_two_entry_alt` (`st_size = 0`, 2nd entry): `add rdi, 300`; `jmp 0x30` -/
def probeClusterSec : ExecSection where
  secSize := 61
  roQuadAt := fun off => if off = 0x20 then 100 else 0
  decodeAt := fun pc =>
    if pc = 0x00 then .addImm 4 10
    else if pc = 0x04 then .addImm 4 5
    else if pc = 0x08 then .jmp 2 0x10
    else if pc = 0x0a then .addImm 4 20
    else if pc = 0x0e then .jmp 2 0x10
    else if pc = 0x10 then .mulImm 4 2
    else if pc = 0x14 then .addRipData 7 0x20
    else if pc = 0x1b then .ret 1
    else if pc = 0x28 then .jeFlagZero 4 0x30
    else if pc = 0x2c then .addImm 4 100
    else if pc = 0x30 then .movRaxRdi 3
    else if pc = 0x33 then .ret 1
    else if pc = 0x34 then .addImm 7 300
    else if pc = 0x3b then .jmp 2 0x30
    else .embeddedData

def symNosizeFast : ElfSym := { symId := 1, stValue := 0x00, stSize := 0 }
def symNosizeCommon : ElfSym := { symId := 2, stValue := 0x04, stSize := 0 }
def symSizedSharedTail : ElfSym := { symId := 3, stValue := 0x0a, stSize := 6 }
def symTwoEntryEnter : ElfSym := { symId := 4, stValue := 0x28, stSize := 12 }
def symTwoEntryAlt : ElfSym := { symId := 5, stValue := 0x34, stSize := 0 }

/-- Negative Canary 2: Even when `.size` IS emitted (`symSizedSharedTail`,
`[0x0a, 0x10)`), per-symbol slicing fails closed on `jmp .Lshared_tail` (`0x10`)
because the shared `.L` tail helper lies outside `[0x0a, 0x10)`! -/
theorem canary_st_size_rejects_shared_local_tail_helper :
    ∀ fuel,
      runInSlice probeClusterSec symSizedSharedTail.stValue
        (symSizedSharedTail.stValue + symSizedSharedTail.stSize) fuel
        { pc := 0x0a, rdi := 7, esi := 0, rax := 0 } = none := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ f1 =>
    cases f1 with
    | zero => rfl
    | succ f2 => rfl

/-- Negative Canary 3: Naive `[st_value, next_global_sym)` slicing fails on
fallthroughs (`[0x00, 0x04)`), cross-symbol backward jumps (`[0x34, 0x3d)` into
`0x30`), and linear disassembly across `.Linline_const` (`0x20`)! -/
theorem canary_next_sym_partition_breaks_fallthrough_and_cross_sym_jump :
    (∀ fuel, runInSlice probeClusterSec 0x00 0x04 fuel
      { pc := 0x00, rdi := 7, esi := 0, rax := 0 } = none) ∧
    (∀ fuel, runInSlice probeClusterSec 0x34 0x3d fuel
      { pc := 0x34, rdi := 7, esi := 0, rax := 0 } = none) ∧
    stepInSlice probeClusterSec 0 61
      { pc := 0x20, rdi := 0, esi := 0, rax := 0 } = .fault := by
  refine ⟨?_, ?_, rfl⟩
  · intro fuel
    cases fuel with
    | zero => rfl
    | succ f1 =>
      cases f1 with
      | zero => rfl
      | succ f2 => rfl
  · intro fuel
    cases fuel with
    | zero => rfl
    | succ f1 =>
      cases f1 with
      | zero => rfl
      | succ f2 => rfl

inductive MultiStepSec (sec : ExecSection) : Nat → RegState → RegState → Prop where
  | refl (st : RegState) : MultiStepSec sec 0 st st
  | step {k : Nat} {s1 s2 s3 : RegState} :
      stepInSlice sec 0 sec.secSize s1 = .step s2 →
      MultiStepSec sec k s2 s3 →
      MultiStepSec sec (k + 1) s1 s3

theorem multiStep_prepend_run (sec : ExecSection) {k fuel : Nat}
    {s1 s2 : RegState} {v : Nat}
    (hSteps : MultiStepSec sec k s1 s2)
    (hTerm : runInSlice sec 0 sec.secSize fuel s2 = some v) :
    runInSlice sec 0 sec.secSize (k + fuel) s1 = some v := by
  induction hSteps with
  | refl _ =>
    simpa [Nat.zero_add] using hTerm
  | @step k s1 s2 s3 h1 _ ih =>
    have hEq : k + 1 + fuel = (k + fuel) + 1 := by omega
    rw [hEq]
    simp [runInSlice, h1, ih hTerm]

/-- Section-Wide Entry-Cutpoint Graph (`SWECG`) certificate over `[0, sec.secSize)`. -/
structure SwecgCertificate (sec : ExecSection) where
  isCut : Nat → Bool
  rank : Nat → Nat
  spec : Nat → Nat → Nat → Nat
  dataReadSafe : ∀ pc len dOff,
    sec.decodeAt pc = .addRipData len dOff →
    ∀ q, dOff ≤ q → q < dOff + 8 → sec.decodeAt q = .embeddedData
  cutValid : ∀ c rdi esi rax,
    isCut c = true →
    (∃ fuel, runInSlice sec 0 sec.secSize fuel
      { pc := c, rdi := rdi, esi := esi, rax := rax } = some (spec c rdi esi)) ∨
    (∃ k c' rdi' esi' rax',
      isCut c' = true ∧
      rank c' < rank c ∧
      spec c' rdi' esi' = spec c rdi esi ∧
      MultiStepSec sec k { pc := c, rdi := rdi, esi := esi, rax := rax }
        { pc := c', rdi := rdi', esi := esi', rax := rax' })

/-- Theorem 1 (`swecg_cutpoint_sound`): Every entry/cutpoint in a section with a
valid `SwecgCertificate` terminates cleanly in `.returned (spec c rdi esi)`
without faulting or executing embedded data bytes. -/
theorem swecg_cutpoint_sound (sec : ExecSection) (cert : SwecgCertificate sec) :
    ∀ n c rdi esi rax,
      cert.rank c ≤ n →
      cert.isCut c = true →
      ∃ fuel,
        runInSlice sec 0 sec.secSize fuel
          { pc := c, rdi := rdi, esi := esi, rax := rax } =
          some (cert.spec c rdi esi) := by
  intro n
  induction n with
  | zero =>
    intro c rdi esi rax hRank hCut
    rcases cert.cutValid c rdi esi rax hCut with hDirect | ⟨_, _, _, _, _, _, hLt, _, _⟩
    · exact hDirect
    · omega
  | succ n ih =>
    intro c rdi esi rax hRank hCut
    rcases cert.cutValid c rdi esi rax hCut with hDirect | ⟨k, c', rdi', esi', rax', hCut', hLt, hSpecEq, hSteps⟩
    · exact hDirect
    · have hLe : cert.rank c' ≤ n := by omega
      rcases ih c' rdi' esi' rax' hLe hCut' with ⟨fuel2, hRun2⟩
      refine ⟨k + fuel2, ?_⟩
      rw [← hSpecEq]
      exact multiStep_prepend_run sec hSteps hRun2

/-- Concrete verification of all 5 global symbols in `probeClusterSec`. -/
theorem swecg_verifies_five_entry_cluster (x : Nat) :
    runInSlice probeClusterSec 0 61 6 { pc := symNosizeFast.stValue, rdi := x, esi := 0, rax := 0 } =
      some ((x + 10 + 5) * 2 + 100) ∧
    runInSlice probeClusterSec 0 61 5 { pc := symNosizeCommon.stValue, rdi := x, esi := 0, rax := 0 } =
      some ((x + 5) * 2 + 100) ∧
    runInSlice probeClusterSec 0 61 5 { pc := symSizedSharedTail.stValue, rdi := x, esi := 0, rax := 0 } =
      some ((x + 20) * 2 + 100) ∧
    runInSlice probeClusterSec 0 61 4 { pc := symTwoEntryEnter.stValue, rdi := x, esi := 1, rax := 0 } =
      some (x + 100) ∧
    runInSlice probeClusterSec 0 61 4 { pc := symTwoEntryAlt.stValue, rdi := x, esi := 0, rax := 0 } =
      some (x + 300) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end SectionWideAsmCfg

/-! ## Part 2: 13-Opcode `DwarfCfi` (`DW_CFA_undefined`), `StackPool`, and Dormant-Stack Tree Borrows -/

namespace StackPoolAndCfi

inductive CfiReg where
  | sp
  | fp
  | csr
  | ra
  deriving DecidableEq, Repr

inductive CfaRule where
  | regOffset (r : CfiReg) (off : Int)
  | derefBreg (r : CfiReg) (disp : Int)
  | invalid
  deriving DecidableEq, Repr

inductive RegRule where
  | sameValue
  | cfaOffset (off : Int)
  | atBreg (base : CfiReg) (disp : Int)
  | inReg (src : CfiReg)
  | undefined
  deriving DecidableEq, Repr

structure CfiRow where
  cfa : CfaRule
  regRules : CfiReg → RegRule
  argsSize : Nat

structure CfiState where
  pc : Nat
  row : CfiRow
  savedRows : List CfiRow

/-- 13-Opcode DWARF `.eh_frame` instruction set including `DW_CFA_undefined` (`0x07`). -/
inductive CfiOp where
  | advanceLoc (delta : Nat)
  | defCfa (r : CfiReg) (off : Int)
  | defCfaReg (r : CfiReg)
  | defCfaOffset (off : Int)
  | defCfaBregDeref (r : CfiReg) (disp : Int)
  | offset (r : CfiReg) (off : Int)
  | exprBreg (r : CfiReg) (b : CfiReg) (disp : Int)
  | sameValue (r : CfiReg)
  | restore (r : CfiReg)
  | register (r : CfiReg) (src : CfiReg)
  | rememberState
  | restoreState
  | undefined (r : CfiReg)
  | gnuArgsSize (sz : Nat)
  | nop
  deriving DecidableEq, Repr

def updateRegRule (rules : CfiReg → RegRule) (r : CfiReg) (rule : RegRule) :
    CfiReg → RegRule :=
  fun q => if q = r then rule else rules q

def stepCfiOp (cieInit : CfiRow) (st : CfiState) (op : CfiOp) : Option CfiState :=
  match op with
  | .advanceLoc d => some { st with pc := st.pc + d }
  | .defCfa r off => some { st with row := { st.row with cfa := .regOffset r off } }
  | .defCfaReg r =>
      match st.row.cfa with
      | .regOffset _ off => some { st with row := { st.row with cfa := .regOffset r off } }
      | _ => none
  | .defCfaOffset off =>
      match st.row.cfa with
      | .regOffset r _ => some { st with row := { st.row with cfa := .regOffset r off } }
      | _ => none
  | .defCfaBregDeref r disp =>
      some { st with row := { st.row with cfa := .derefBreg r disp } }
  | .offset r off =>
      some { st with row := { st.row with regRules := updateRegRule st.row.regRules r (.cfaOffset off) } }
  | .exprBreg r b disp =>
      some { st with row := { st.row with regRules := updateRegRule st.row.regRules r (.atBreg b disp) } }
  | .sameValue r =>
      some { st with row := { st.row with regRules := updateRegRule st.row.regRules r .sameValue } }
  | .restore r =>
      some { st with row := { st.row with regRules := updateRegRule st.row.regRules r (cieInit.regRules r) } }
  | .register r src =>
      some { st with row := { st.row with regRules := updateRegRule st.row.regRules r (.inReg src) } }
  | .rememberState => some { st with savedRows := st.row :: st.savedRows }
  | .restoreState =>
      match st.savedRows with
      | top :: rest => some { st with row := top, savedRows := rest }
      | [] => none
  | .undefined r =>
      some { st with row := { st.row with regRules := updateRegRule st.row.regRules r .undefined } }
  | .gnuArgsSize sz => some { st with row := { st.row with argsSize := sz } }
  | .nop => some st

def evalCfiOps (cieInit : CfiRow) (targetPc : Nat) :
    List CfiOp → CfiState → Option CfiState
  | [], st => some st
  | op :: rest, st =>
      match op with
      | .advanceLoc d =>
          if decide (st.pc + d ≤ targetPc) then
            evalCfiOps cieInit targetPc rest { st with pc := st.pc + d }
          else
            some st
      | _ =>
          match stepCfiOp cieInit st op with
          | some st' => evalCfiOps cieInit targetPc rest st'
          | none => none

def x86_64CieInit : CfiRow where
  cfa := .regOffset .sp 8
  regRules := fun r => if r = .ra then .cfaOffset (-8) else .sameValue
  argsSize := 0

def aarch64AapcsCieInit : CfiRow where
  cfa := .regOffset .sp 0
  regRules := fun _ => .sameValue
  argsSize := 0

def aarch64UnwindingCrateCieInit : CfiRow where
  cfa := .regOffset .sp 0
  regRules := fun r => if r = .ra then .undefined else .sameValue
  argsSize := 0

structure WordMem where
  isMapped : Int → Bool
  readWord : Int → Int

inductive UnwindStepOut where
  | caller (regs : CfiReg → Int)
  | endOfStack
  | faultUnmapped (addr : Int)
  | faultInvalidCfi

def evalCfa (row : CfiRow) (regs : CfiReg → Int) (mem : WordMem) :
    Except UnwindStepOut Int :=
  match row.cfa with
  | .regOffset r off => .ok (regs r + off)
  | .derefBreg r disp =>
      let addr := regs r + disp
      if mem.isMapped addr then .ok (mem.readWord addr)
      else .error (.faultUnmapped addr)
  | .invalid => .error .faultInvalidCfi

def evalSavedReg (cfa : Int) (rule : RegRule) (r : CfiReg)
    (regs : CfiReg → Int) (mem : WordMem) : Except UnwindStepOut (Option Int) :=
  match rule with
  | .undefined => .ok none
  | .sameValue => .ok (some (regs r))
  | .cfaOffset off =>
      let addr := cfa + off
      if mem.isMapped addr then .ok (some (mem.readWord addr))
      else .error (.faultUnmapped addr)
  | .atBreg b disp =>
      let addr := regs b + disp
      if mem.isMapped addr then .ok (some (mem.readWord addr))
      else .error (.faultUnmapped addr)
  | .inReg src => .ok (some (regs src))

def stepUnwindRow (row : CfiRow) (regs : CfiReg → Int) (mem : WordMem) :
    UnwindStepOut :=
  match evalCfa row regs mem with
  | .error e => e
  | .ok cfa =>
      match evalSavedReg cfa (row.regRules .ra) .ra regs mem with
      | .error e => e
      | .ok none => .endOfStack
      | .ok (some raVal) =>
          if raVal = 0 then .endOfStack
          else
            match evalSavedReg cfa (row.regRules .fp) .fp regs mem,
                  evalSavedReg cfa (row.regRules .csr) .csr regs mem with
            | .error e, _ => e
            | _, .error e => e
            | .ok fpOpt, .ok csrOpt =>
                .caller fun q =>
                  match q with
                  | .sp => cfa
                  | .ra => raVal
                  | .fp => fpOpt.getD 0
                  | .csr => csrOpt.getD 0

def unwindWalk (fdeForPc : Int → Option CfiRow) (mem : WordMem) :
    Nat → (CfiReg → Int) → UnwindStepOut
  | 0, regs => .caller regs
  | fuel + 1, regs =>
      if regs .ra = 0 then .endOfStack
      else
        match fdeForPc (regs .ra - 1) with
        | none => .endOfStack
        | some row =>
            match stepUnwindRow row regs mem with
            | .caller regs' => unwindWalk fdeForPc mem fuel regs'
            | terminal => terminal

/-- Theorem 2a: `.cfi_undefined` on `RA` (`RIP` / `X30`) halts stack unwinding
cleanly with `.endOfStack` across x86-64 and both AArch64 unwinder regimes even
when `[stackTop, ∞)` is unmapped (`PROT_NONE`). -/
theorem stack_root_cfi_undefined_halts_cleanly
    (stackTop : Int) (regs : CfiReg → Int) (mem : WordMem)
    (hSp : regs .sp = stackTop)
    (_hGuardUnmapped : mem.isMapped stackTop = false) :
    (∃ stX64,
      evalCfiOps x86_64CieInit 4 [.defCfa .sp 0, .undefined .ra, .undefined .fp]
        { pc := 0, row := x86_64CieInit, savedRows := [] } = some stX64 ∧
      stepUnwindRow stX64.row regs mem = .endOfStack) ∧
    (∃ stA64,
      evalCfiOps aarch64AapcsCieInit 4 [.undefined .ra, .undefined .fp]
        { pc := 0, row := aarch64AapcsCieInit, savedRows := [] } = some stA64 ∧
      stepUnwindRow stA64.row regs mem = .endOfStack) ∧
    (∃ stUw,
      evalCfiOps aarch64UnwindingCrateCieInit 4 [.undefined .ra, .undefined .fp]
        { pc := 0, row := aarch64UnwindingCrateCieInit, savedRows := [] } = some stUw ∧
      stepUnwindRow stUw.row regs mem = .endOfStack) := by
  have _ := hSp
  exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

/-- Negative Canary 4: Omitting `.cfi_undefined rip` on x86-64 dereferences
unmapped `[stackTop]` (`PROT_NONE`) and faults (`SIGSEGV`). -/
theorem canary_x64_missing_undef_reads_unmapped
    (stackTop : Int) (regs : CfiReg → Int) (mem : WordMem)
    (hSp : regs .sp = stackTop)
    (hGuardUnmapped : mem.isMapped stackTop = false) :
    stepUnwindRow x86_64CieInit regs mem = .faultUnmapped stackTop := by
  have hAddr : regs .sp + 8 + -8 = stackTop := by omega
  simp [stepUnwindRow, x86_64CieInit, evalCfa, evalSavedReg, hAddr, hGuardUnmapped]

/-- Negative Canary 5: Omitting `.cfi_undefined x30` on AArch64 traps AAPCS64
`SameValue` unwinders (`libgcc_s`, `llvm-libunwind`) in an infinite fixed-point
loop for all fuel `n`, while `unwinding 0.2.10` returns `.endOfStack`. -/
theorem canary_a64_missing_undef_sameval_loops_forever
    (stackTop rootRetPc : Int) (hNz : rootRetPc ≠ 0)
    (mem : WordMem) :
    let regs : CfiReg → Int := fun r =>
      match r with | .sp => stackTop | .ra => rootRetPc | _ => 0
    let fdeMap : Int → Option CfiRow := fun _ => some aarch64AapcsCieInit
    (∀ fuel, unwindWalk fdeMap mem fuel regs = .caller regs) ∧
    stepUnwindRow aarch64UnwindingCrateCieInit regs mem = .endOfStack := by
  intro regs fdeMap
  have hStepId : stepUnwindRow aarch64AapcsCieInit regs mem = .caller regs := by
    simp [stepUnwindRow, aarch64AapcsCieInit, evalCfa, evalSavedReg, regs, hNz]
    funext q
    cases q <;> rfl
  refine ⟨?_, ?_⟩
  · intro fuel
    induction fuel with
    | zero => rfl
    | succ f ih =>
      simp [unwindWalk, regs, hNz, fdeMap, hStepId, ih]
  · simp [stepUnwindRow, aarch64UnwindingCrateCieInit, evalCfa, evalSavedReg]

/-! ### First-Order Linear `StackPool` and Dormant-Stack Tree Borrows Protectors -/

abbrev StackId := Nat
abbrev AllocId := Nat
abbrev BorTag := Nat
abbrev FrameId := Nat

inductive TbPerm where
  | cell
  | reservedFrz (conflicted : Bool)
  | reservedIM
  | unique
  | frozen
  | disabled
  deriving DecidableEq, Repr

inductive AccessKind where | read | write deriving DecidableEq, Repr
inductive AccessRel where | local_ | foreign deriving DecidableEq, Repr

def tbStep (kind : AccessKind) (rel : AccessRel) (old : TbPerm)
    (isProtected accessed : Bool) : Option TbPerm :=
  match kind, rel with
  | .read, .local_ =>
      match old with | .disabled => none | p => some p
  | .write, .local_ =>
      match old with
      | .cell => some .cell
      | .reservedFrz true => if isProtected then none else some .unique
      | .reservedFrz false => some .unique
      | .reservedIM => some .unique
      | .unique => some .unique
      | .frozen => none
      | .disabled => none
  | .read, .foreign =>
      match old with
      | .cell => some .cell
      | .frozen => some .frozen
      | .disabled => some .disabled
      | .reservedFrz _ =>
          if isProtected then some (.reservedFrz true) else some old
      | .reservedIM => some .reservedIM
      | .unique =>
          if isProtected then (if accessed then none else some .disabled)
          else some .frozen
  | .write, .foreign =>
      match old with
      | .cell => some .cell
      | .reservedIM => some .reservedIM
      | .disabled => some .disabled
      | _ => if isProtected && accessed then none else some .disabled

structure ActiveProtector where
  frameId : FrameId
  allocId : AllocId
  tag : BorTag
  deriving DecidableEq, Repr

structure RustStackFrame where
  frameId : FrameId
  spLo : Int
  spHi : Int
  protectors : List ActiveProtector
  deriving DecidableEq, Repr

inductive StackLifecycle where
  | active (curSp : Int) (frames : List RustStackFrame)
  | dormant (savedSp : Int) (resumeSym : Nat) (savedCsr : Nat) (frames : List RustStackFrame)
  | uninit
  deriving DecidableEq, Repr

structure StackSlot where
  sid : StackId
  base : Int
  top : Int
  state : StackLifecycle
  deriving DecidableEq, Repr

def slotFrames (s : StackSlot) : List RustStackFrame :=
  match s.state with
  | .active _ fs => fs
  | .dormant _ _ _ fs => fs
  | .uninit => []

def frameProtectors : List RustStackFrame → List ActiveProtector
  | [] => []
  | f :: rest => f.protectors ++ frameProtectors rest

def poolActiveProtectors : List StackSlot → List ActiveProtector
  | [] => []
  | s :: rest => frameProtectors (slotFrames s) ++ poolActiveProtectors rest

def hasProtector (ps : List ActiveProtector) (aid : AllocId) (t : BorTag) : Bool :=
  match ps with
  | [] => false
  | p :: rest =>
      if decide (p.allocId = aid ∧ p.tag = t) then true
      else hasProtector rest aid t

def IntervalsDisjoint (lo1 hi1 lo2 hi2 : Int) : Prop :=
  hi1 ≤ lo2 ∨ hi2 ≤ lo1

def StackSlotWf (s : StackSlot) : Prop :=
  s.base < s.top ∧
  match s.state with
  | .active sp _ => s.base ≤ sp ∧ sp ≤ s.top
  | .dormant sp _ _ _ => s.base ≤ sp ∧ sp ≤ s.top
  | .uninit => True

def PoolPairwiseDisjoint : List StackSlot → Prop
  | [] => True
  | s :: rest =>
      (∀ t ∈ rest, t.sid ≠ s.sid ∧ IntervalsDisjoint s.base s.top t.base t.top) ∧
      PoolPairwiseDisjoint rest

def switchOneSlot (fromSid toSid : StackId) (saveSp : Int)
    (returnSym csrSnap : Nat) (s : StackSlot) : StackSlot :=
  if s.sid = fromSid then
    match s.state with
    | .active _ fs => { s with state := .dormant saveSp returnSym csrSnap fs }
    | _ => s
  else if s.sid = toSid then
    match s.state with
    | .dormant savedSp _ _ fs => { s with state := .active savedSp fs }
    | _ => s
  else s

def switchStacksInPool (fromSid toSid : StackId) (saveSp : Int)
    (returnSym csrSnap : Nat) : List StackSlot → List StackSlot
  | [] => []
  | s :: rest =>
      switchOneSlot fromSid toSid saveSp returnSym csrSnap s ::
        switchStacksInPool fromSid toSid saveSp returnSym csrSnap rest

theorem switchOneSlot_coords_and_frames (fromSid toSid : StackId) (saveSp : Int)
    (returnSym csrSnap : Nat) (s : StackSlot) :
    let s' := switchOneSlot fromSid toSid saveSp returnSym csrSnap s
    s'.sid = s.sid ∧ s'.base = s.base ∧ s'.top = s.top ∧
    slotFrames s' = slotFrames s := by
  cases s with
  | mk sid base top st =>
    dsimp [switchOneSlot]
    split
    · cases st <;> exact ⟨rfl, rfl, rfl, rfl⟩
    · split
      · cases st <;> exact ⟨rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl⟩

theorem switchOneSlot_wf (fromSid toSid : StackId) (saveSp : Int)
    (returnSym csrSnap : Nat) (s : StackSlot)
    (hWf : StackSlotWf s)
    (hSave : s.sid = fromSid → s.base ≤ saveSp ∧ saveSp ≤ s.top) :
    StackSlotWf (switchOneSlot fromSid toSid saveSp returnSym csrSnap s) := by
  rcases s with ⟨sid, base, top, st⟩
  dsimp [StackSlotWf] at hWf hSave
  rcases hWf with ⟨hLt, hStWf⟩
  by_cases h1 : sid = fromSid
  · have hB := hSave h1
    cases st <;> simp [switchOneSlot, StackSlotWf, h1, hLt, hB, hStWf]
  · by_cases h2 : sid = toSid
    · subst h2
      cases st with
      | active _ _ => exact ⟨by simp [switchOneSlot, h1, hLt], by simpa [switchOneSlot, h1] using hStWf⟩
      | dormant _ _ _ _ => exact ⟨by simp [switchOneSlot, h1, hLt], by simpa [switchOneSlot, h1] using hStWf⟩
      | uninit => simp [switchOneSlot, StackSlotWf, h1, hLt]
    · cases st with
      | active _ _ => exact ⟨by simp [switchOneSlot, h1, h2, hLt], by simpa [switchOneSlot, h1, h2] using hStWf⟩
      | dormant _ _ _ _ => exact ⟨by simp [switchOneSlot, h1, h2, hLt], by simpa [switchOneSlot, h1, h2] using hStWf⟩
      | uninit => simp [switchOneSlot, StackSlotWf, h1, h2, hLt]

theorem mem_switchStacksInPool {fromSid toSid : StackId} {saveSp : Int}
    {returnSym csrSnap : Nat} {pool : List StackSlot} {t' : StackSlot}
    (ht' : t' ∈ switchStacksInPool fromSid toSid saveSp returnSym csrSnap pool) :
    ∃ t ∈ pool, t' = switchOneSlot fromSid toSid saveSp returnSym csrSnap t := by
  induction pool with
  | nil => contradiction
  | cons s rest ih =>
    simp only [switchStacksInPool, List.mem_cons] at ht'
    rcases ht' with rfl | hRest
    · exact ⟨s, List.mem_cons_self, rfl⟩
    · rcases ih hRest with ⟨t, ht, hEq⟩
      exact ⟨t, List.mem_cons_of_mem s ht, hEq⟩

/-- Theorem 2b (`two_entry_switch_preserves_protectors_and_disjointness`):
2-entry trampoline stack switching preserves all dormant Rust frames'
`StrongProtector`s in `poolActiveProtectors`, pairwise stack interval
disjointness, and stack-pointer bounds across `StackPool`. -/
theorem two_entry_switch_preserves_protectors_and_disjointness
    (fromSid toSid : StackId) (_hNe : fromSid ≠ toSid)
    (saveSp : Int) (returnSym csrSnap : Nat) (pool : List StackSlot)
    (hDisj : PoolPairwiseDisjoint pool)
    (hSaveValid : ∀ s ∈ pool, s.sid = fromSid → s.base ≤ saveSp ∧ saveSp ≤ s.top)
    (hWf : ∀ s ∈ pool, StackSlotWf s) :
    let pool' := switchStacksInPool fromSid toSid saveSp returnSym csrSnap pool
    poolActiveProtectors pool' = poolActiveProtectors pool ∧
    PoolPairwiseDisjoint pool' ∧
    (∀ s' ∈ pool', StackSlotWf s') := by
  induction pool with
  | nil =>
    simp [switchStacksInPool, poolActiveProtectors, PoolPairwiseDisjoint]
  | cons s rest ih =>
    rcases hDisj with ⟨hHeadDisj, hRestDisj⟩
    rcases ih hRestDisj
      (fun t ht hId => hSaveValid t (List.mem_cons_of_mem s ht) hId)
      (fun t ht => hWf t (List.mem_cons_of_mem s ht)) with ⟨ihProt, ihDisj, ihWf⟩
    rcases switchOneSlot_coords_and_frames fromSid toSid saveSp returnSym csrSnap s
      with ⟨hsSid, hsBase, hsTop, hsFrames⟩
    refine ⟨?_, ?_, ?_⟩
    · simp [switchStacksInPool, poolActiveProtectors, hsFrames, ihProt]
    · simp only [switchStacksInPool, PoolPairwiseDisjoint]
      refine ⟨?_, ihDisj⟩
      intro t' ht'
      rcases mem_switchStacksInPool ht' with ⟨t, ht, rfl⟩
      rcases switchOneSlot_coords_and_frames fromSid toSid saveSp returnSym csrSnap t
        with ⟨htSid, htBase, htTop, _⟩
      rw [htSid, htBase, htTop, hsSid, hsBase, hsTop]
      exact hHeadDisj t ht
    · intro s' hs'
      simp only [switchStacksInPool, List.mem_cons] at hs'
      rcases hs' with rfl | hInRest
      · exact switchOneSlot_wf fromSid toSid saveSp returnSym csrSnap s
          (hWf s List.mem_cons_self) (hSaveValid s List.mem_cons_self)
      · exact ihWf s' hInRest

/-- Theorem 2c & Negative Canaries 6–8: Complete dormant-stack Tree Borrows
matrix matching Miri probes `m2b`–`m2g`. -/
theorem dormant_stack_tree_borrows_complete_matrix :
    let frameA : RustStackFrame :=
      { frameId := 100, spLo := 0x1000, spHi := 0x2000,
        protectors := [{ frameId := 100, allocId := 1, tag := 10 }] }
    let poolInit : List StackSlot :=
      [ { sid := 0, base := 0x1000, top := 0x2000, state := .active 0x1800 [frameA] },
        { sid := 1, base := 0x4000, top := 0x6000, state := .dormant 0x5800 1 0 [] } ]
    let poolWhileBDormantA := switchStacksInPool 0 1 0x17c0 2 0 poolInit
    let isProtOnB := hasProtector (poolActiveProtectors poolWhileBDormantA) 1 10
    let poolResumedA := switchStacksInPool 1 0 0x5800 1 0 poolWhileBDormantA
    let isProtOnResume := hasProtector (poolActiveProtectors poolResumedA) 1 10
    isProtOnB = true ∧
    tbStep .write .local_ (.reservedFrz false) isProtOnB false = some .unique ∧
    tbStep .write .foreign .unique isProtOnB true = none ∧
    tbStep .read .foreign .unique isProtOnB true = none ∧
    (tbStep .read .foreign .unique false true = some .frozen ∧
     tbStep .read .local_ .frozen false true = some .frozen) ∧
    (tbStep .read .foreign (.reservedFrz false) isProtOnB false = some (.reservedFrz true) ∧
     tbStep .write .local_ (.reservedFrz true) isProtOnResume false = none) := by
  exact ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end StackPoolAndCfi

/-! ## Part 3: COFE-Free First-Order Linear `ForeignHandlePool` for C Ops-Table Vtables -/

namespace ForeignOwnableVtable

abbrev HandleId := Nat

/-- Linear ownership/borrow typestate in `ForeignHandlePool`:
`Unallocated -> Owned -> (Shared n | MutLoaned) -> Owned -> Freed`. -/
inductive HandleState where
  | unallocated
  | owned
  | shared (readers : Nat)  -- `readers + 1` active reentrant shared `borrow`s
  | mutLoaned               -- 1 active exclusive `borrow_mut`
  | freed                   -- Reclaimed via `from_foreign` and dropped
  deriving DecidableEq, Repr

/-- C `struct file` state modeling Linux `fs/open.c` (`FMODE_OPENED` bit) and
`void *private_data`. -/
structure CFile where
  fModeOpened : Bool
  fFlags : Nat
  privateData : Option HandleId
  deriving DecidableEq, Repr

/-- First-order COFE-free world for temporally disjoint C ops-table callbacks. -/
structure VtableWorld where
  nextHid : HandleId
  stateOf : HandleId → HandleState
  payloadOf : HandleId → Nat
  file : CFile

def emptyVtableWorld : VtableWorld where
  nextHid := 0
  stateOf := fun _ => .unallocated
  payloadOf := fun _ => 0
  file := { fModeOpened := false, fFlags := 0, privateData := none }

def setHandle (w : VtableWorld) (hid : HandleId) (st : HandleState) (val : Nat) :
    VtableWorld :=
  { w with
    stateOf := fun q => if q = hid then st else w.stateOf q
    payloadOf := fun q => if q = hid then val else w.payloadOf q }

/-- Sound `open` + Linux `do_dentry_open` (`fs/open.c:999-1004`):
Validates flags *before* calling `into_foreign`, ensuring `fModeOpened = true`
iff a fresh `.owned` handle is stored in `private_data`. -/
def soundVfsOpen (w : VtableWorld) (flags initVal : Nat) : VtableWorld × Int :=
  if w.file.fModeOpened then (w, -16)
  else if flags = 0x4000 then
    ({ w with file := { fModeOpened := false, fFlags := flags, privateData := none } }, -22)
  else
    let hid := w.nextHid
    let w1 := setHandle w hid .owned initVal
    ({ w1 with
       nextHid := hid + 1
       file := { fModeOpened := true, fFlags := flags, privateData := some hid } }, 0)

/-- Reentrant shared `unlocked_ioctl` (`ForeignOwnable::borrow`) across
**arbitrary** C->Rust callback nesting depth `depth : Nat`:
transitions `Owned -> Shared 0 -> ... -> Shared depth -> ... -> Owned`. -/
def execReentrantSharedIoctl (hid : HandleId) (delta : Nat) :
    Nat → VtableWorld → Option VtableWorld
  | 0, w =>
      match w.stateOf hid with
      | .owned => some (setHandle w hid .owned (w.payloadOf hid + delta))
      | .shared n => some (setHandle w hid (.shared n) (w.payloadOf hid + delta))
      | _ => none
  | depth + 1, w =>
      match w.stateOf hid with
      | .owned =>
          let wEnter := setHandle w hid (.shared 0) (w.payloadOf hid)
          match execReentrantSharedIoctl hid delta depth wEnter with
          | some wMid => some (setHandle wMid hid .owned (wMid.payloadOf hid + delta))
          | none => none
      | .shared n =>
          let wEnter := setHandle w hid (.shared (n + 1)) (w.payloadOf hid)
          match execReentrantSharedIoctl hid delta depth wEnter with
          | some wMid => some (setHandle wMid hid (.shared n) (wMid.payloadOf hid + delta))
          | none => none
      | _ => none

/-- Checked exclusive `MutLoaned` `unlocked_ioctl`: if a C callback re-enters
`ioctl` while `.mutLoaned` is active, the nested call fails closed with `-EBUSY`
(`-16`) instead of creating aliasing `&mut T` references! -/
def soundCheckedMutReentrantIoctl (w : VtableWorld) : Option (VtableWorld × Int) :=
  if !w.file.fModeOpened then some (w, -9)
  else
    match w.file.privateData with
    | none => none
    | some hid =>
        if w.stateOf hid = .owned then
          let wLoaned := setHandle w hid .mutLoaned (w.payloadOf hid)
          let nestedRc : Int :=
            if wLoaned.stateOf hid = .mutLoaned then -16 else 0
          let wRestored := setHandle wLoaned hid .owned (wLoaned.payloadOf hid)
          some (wRestored, nestedRc)
        else
          some (w, -16)

/-- Sound Linux `__fput` + `release` (`fs/file_table.c:493-512`):
Skips `release` when `!fModeOpened`, and when `fModeOpened` linearly consumes
`.owned -> .freed` and clears `privateData := none`. -/
def soundVfsFput (w : VtableWorld) : Option VtableWorld :=
  if !w.file.fModeOpened then some w
  else
    match w.file.privateData with
    | none => none
    | some hid =>
        if w.stateOf hid = .owned then
          let wFreed := setHandle w hid .freed (w.payloadOf hid)
          some { wFreed with file := { w.file with fModeOpened := false, privateData := none } }
        else none

inductive VfsEvent where
  | openCall (flags : Nat) (initVal : Nat)
  | reentrantSharedIoctl (depth : Nat) (delta : Nat)
  | checkedMutReentrantIoctl
  | fputClose
  deriving DecidableEq, Repr

def stepVfsEvent (w : VtableWorld) (ev : VfsEvent) : Option VtableWorld :=
  match ev with
  | .openCall flags initVal => some (soundVfsOpen w flags initVal).1
  | .reentrantSharedIoctl depth delta =>
      if !w.file.fModeOpened then some w
      else
        match w.file.privateData with
        | none => none
        | some hid => execReentrantSharedIoctl hid delta depth w
  | .checkedMutReentrantIoctl =>
      match soundCheckedMutReentrantIoctl w with
      | some (w', _) => some w'
      | none => none
  | .fputClose => soundVfsFput w

def runVfsTrace : VtableWorld → List VfsEvent → Option VtableWorld
  | w, [] => some w
  | w, ev :: rest =>
      match stepVfsEvent w ev with
      | some w' => runVfsTrace w' rest
      | none => none

/-- Inactive handle predicate: a handle holds ZERO live Rust ownership or loans
iff it is either `.unallocated` or `.freed`. -/
def IsInactive (st : HandleState) : Prop :=
  st = .unallocated ∨ st = .freed

/-- Global COFE-free vtable invariant:
- Every `hid ≥ w.nextHid` is `.unallocated`.
- When `fModeOpened = false`, `privateData = none` and **every** `hid` is
  inactive (`.unallocated` or `.freed` — zero leaked handles!).
- When `fModeOpened = true`, `privateData = some hid` with `hid < w.nextHid`,
  `w.stateOf hid = .owned` (no dangling loans across C return boundaries), and
  every other `q ≠ hid` is inactive! -/
def VtableInv (w : VtableWorld) : Prop :=
  (∀ q, w.nextHid ≤ q → w.stateOf q = .unallocated) ∧
  match w.file.fModeOpened, w.file.privateData with
  | false, none => ∀ q, IsInactive (w.stateOf q)
  | true, some hid =>
      hid < w.nextHid ∧
      w.stateOf hid = .owned ∧
      (∀ q, q ≠ hid → IsInactive (w.stateOf q))
  | _, _ => False

/-- Lemma: Nested `Shared n` execution across arbitrary depth `depth` preserves
all other handle states, restores `w.stateOf hid = .shared n`, and accumulates
`(depth + 1) * delta` into `payloadOf hid`! -/
theorem reentrant_shared_inner_law (hid : HandleId) (delta : Nat) :
    ∀ depth n (w : VtableWorld),
      w.stateOf hid = .shared n →
      ∃ w',
        execReentrantSharedIoctl hid delta depth w = some w' ∧
        w'.nextHid = w.nextHid ∧
        w'.file = w.file ∧
        w'.stateOf hid = .shared n ∧
        (∀ q, q ≠ hid → w'.stateOf q = w.stateOf q) ∧
        w'.payloadOf hid = w.payloadOf hid + (depth + 1) * delta := by
  intro depth
  induction depth with
  | zero =>
    intro n w hSt
    refine ⟨setHandle w hid (.shared n) (w.payloadOf hid + delta), ?_, rfl, rfl, ?_, ?_, ?_⟩
    · simp [execReentrantSharedIoctl, hSt]
    · simp [setHandle]
    · intro q hNe
      simp [setHandle, hNe]
    · simp [setHandle]
  | succ d ih =>
    intro n w hSt
    let wEnter := setHandle w hid (.shared (n + 1)) (w.payloadOf hid)
    have hEnterSt : wEnter.stateOf hid = .shared (n + 1) := by simp [wEnter, setHandle]
    rcases ih (n + 1) wEnter hEnterSt with
      ⟨wMid, hMidExec, hMidNext, hMidFile, _, hMidOther, hMidPay⟩
    refine ⟨setHandle wMid hid (.shared n) (wMid.payloadOf hid + delta), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [execReentrantSharedIoctl, hSt, wEnter, hMidExec]
    · simp [setHandle, hMidNext, wEnter]
    · simp [setHandle, hMidFile, wEnter]
    · simp [setHandle]
    · intro q hNe
      simp [setHandle, hNe, hMidOther q hNe, wEnter]
    · have hEnterPay : wEnter.payloadOf hid = w.payloadOf hid := by simp [wEnter, setHandle]
      simp only [setHandle, ↓reduceIte, hMidPay, hEnterPay]
      calc
        w.payloadOf hid + (d + 1) * delta + delta
          = w.payloadOf hid + ((d + 1) * delta + 1 * delta) := by omega
        _ = w.payloadOf hid + (d + 1 + 1) * delta := by rw [← Nat.right_distrib]

/-- Theorem 3a (`reentrant_shared_ioctl_arbitrary_depth_sound`): Starting from
`.owned`, arbitrary `depth`-nested reentrant `ioctl -> C -> ioctl` callbacks
borrow via `Shared 0 .. Shared (depth - 1)` and return cleanly in `.owned` with
exact accumulated state `(depth + 1) * delta`! -/
theorem reentrant_shared_ioctl_arbitrary_depth_sound (hid : HandleId) (delta depth : Nat)
    (w : VtableWorld) (hOwned : w.stateOf hid = .owned) :
    ∃ w',
      execReentrantSharedIoctl hid delta depth w = some w' ∧
      w'.nextHid = w.nextHid ∧
      w'.file = w.file ∧
      w'.stateOf hid = .owned ∧
      (∀ q, q ≠ hid → w'.stateOf q = w.stateOf q) ∧
      w'.payloadOf hid = w.payloadOf hid + (depth + 1) * delta := by
  cases depth with
  | zero =>
    refine ⟨setHandle w hid .owned (w.payloadOf hid + delta), ?_, rfl, rfl, ?_, ?_, ?_⟩
    · simp [execReentrantSharedIoctl, hOwned]
    · simp [setHandle]
    · intro q hNe; simp [setHandle, hNe]
    · simp [setHandle]
  | succ d =>
    let wEnter := setHandle w hid (.shared 0) (w.payloadOf hid)
    have hEnterSt : wEnter.stateOf hid = .shared 0 := by simp [wEnter, setHandle]
    rcases reentrant_shared_inner_law hid delta d 0 wEnter hEnterSt with
      ⟨wMid, hMidExec, hMidNext, hMidFile, _, hMidOther, hMidPay⟩
    refine ⟨setHandle wMid hid .owned (wMid.payloadOf hid + delta), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [execReentrantSharedIoctl, hOwned, wEnter, hMidExec]
    · simp [setHandle, hMidNext, wEnter]
    · simp [setHandle, hMidFile, wEnter]
    · simp [setHandle]
    · intro q hNe
      simp [setHandle, hNe, hMidOther q hNe, wEnter]
    · have hEnterPay : wEnter.payloadOf hid = w.payloadOf hid := by simp [wEnter, setHandle]
      simp only [setHandle, ↓reduceIte, hMidPay, hEnterPay]
      calc
        w.payloadOf hid + (d + 1) * delta + delta
          = w.payloadOf hid + ((d + 1) * delta + 1 * delta) := by omega
        _ = w.payloadOf hid + (d + 1 + 1) * delta := by rw [← Nat.right_distrib]

theorem stepVfsEvent_preserves_inv (w : VtableWorld) (ev : VfsEvent)
    (hInv : VtableInv w) :
    ∃ w', stepVfsEvent w ev = some w' ∧ VtableInv w' := by
  rcases hInv with ⟨hUnalloc, hFileInv⟩
  cases ev with
  | openCall flags initVal =>
    simp only [stepVfsEvent, soundVfsOpen]
    cases hOpen : w.file.fModeOpened
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases hPriv : w.file.privateData with
      | some _ => rw [hOpen, hPriv] at hFileInv; contradiction
      | none =>
        rw [hOpen, hPriv] at hFileInv
        by_cases hFl : flags = 0x4000
        · simp only [hFl, ↓reduceIte]
          exact ⟨_, rfl, hUnalloc, hFileInv⟩
        · simp only [hFl, ↓reduceIte]
          refine ⟨_, rfl, ?_, Nat.lt_succ_self w.nextHid, by simp [setHandle], ?_⟩
          · intro q (hGe : w.nextHid + 1 ≤ q)
            have hNe : q ≠ w.nextHid := Nat.ne_of_gt hGe
            have hLe : w.nextHid ≤ q := Nat.le_of_lt hGe
            simp [setHandle, hNe, hUnalloc q hLe]
          · intro q hNe
            simp [setHandle, hNe]
            exact hFileInv q
    · simp only [↓reduceIte]
      exact ⟨w, rfl, hUnalloc, by simpa [hOpen] using hFileInv⟩
  | reentrantSharedIoctl depth delta =>
    simp only [stepVfsEvent]
    cases hOpen : w.file.fModeOpened
    · simp only [Bool.not_false, ↓reduceIte]
      exact ⟨w, rfl, hUnalloc, by simpa [hOpen] using hFileInv⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hPriv : w.file.privateData with
      | none => rw [hOpen, hPriv] at hFileInv; contradiction
      | some hid =>
        rw [hOpen, hPriv] at hFileInv
        rcases hFileInv with ⟨hLt, hOwn, hOtherInact⟩
        rcases reentrant_shared_ioctl_arbitrary_depth_sound hid delta depth w hOwn with
          ⟨w', hExec, hNextEq, hFileEq, hOwn', hOtherEq, _⟩
        refine ⟨w', hExec, ?_, ?_⟩
        · intro q hGe
          rw [hNextEq] at hGe
          have hNe : q ≠ hid := Nat.ne_of_gt (Nat.lt_of_lt_of_le hLt hGe)
          rw [hOtherEq q hNe]
          exact hUnalloc q hGe
        · rw [hFileEq, hOpen, hPriv, hNextEq]
          refine ⟨hLt, hOwn', ?_⟩
          intro q hNe
          rw [hOtherEq q hNe]
          exact hOtherInact q hNe
  | checkedMutReentrantIoctl =>
    simp only [stepVfsEvent, soundCheckedMutReentrantIoctl]
    cases hOpen : w.file.fModeOpened
    · simp only [Bool.not_false, ↓reduceIte]
      exact ⟨w, rfl, hUnalloc, by simpa [hOpen] using hFileInv⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hPriv : w.file.privateData with
      | none => rw [hOpen, hPriv] at hFileInv; contradiction
      | some hid =>
        rw [hOpen, hPriv] at hFileInv
        rcases hFileInv with ⟨hLt, hOwn, hOtherInact⟩
        simp only [hOwn, ↓reduceIte]
        refine ⟨_, rfl, ?_, ?_⟩
        · intro q hGe
          dsimp [setHandle] at hGe
          have hNe : q ≠ hid := Nat.ne_of_gt (Nat.lt_of_lt_of_le hLt hGe)
          simp [setHandle, hNe, hUnalloc q hGe]
        · dsimp [setHandle]
          rw [hOpen, hPriv]
          refine ⟨hLt, by simp, ?_⟩
          intro q hNe
          simp [hNe, hOtherInact q hNe]
  | fputClose =>
    simp only [stepVfsEvent, soundVfsFput]
    cases hOpen : w.file.fModeOpened
    · simp only [Bool.not_false, ↓reduceIte]
      exact ⟨w, rfl, hUnalloc, by simpa [hOpen] using hFileInv⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hPriv : w.file.privateData with
      | none => rw [hOpen, hPriv] at hFileInv; contradiction
      | some hid =>
        rw [hOpen, hPriv] at hFileInv
        rcases hFileInv with ⟨hLt, hOwn, hOtherInact⟩
        simp only [hOwn, ↓reduceIte]
        refine ⟨_, rfl, ?_, ?_⟩
        · intro q hGe
          dsimp [setHandle] at hGe
          have hNe : q ≠ hid := Nat.ne_of_gt (Nat.lt_of_lt_of_le hLt hGe)
          simp [setHandle, hNe, hUnalloc q hGe]
        · intro q
          by_cases hq : q = hid
          · subst hq
            simp [setHandle, IsInactive]
          · simp [setHandle, hq]
            exact hOtherInact q hq

/-- Theorem 3b (`cofe_free_vtable_trace_sound`): Across **any** finite C event
trace `evs : List VfsEvent` starting from `emptyVtableWorld` (including failed
`open`s, arbitrarily nested reentrant `Shared` `ioctl`s, checked `MutLoaned`
`ioctl`s, and `fput` `release`s), execution succeeds without UB and preserves
`VtableInv` — proved by first-order structural induction with ZERO Iris COFEs
and ZERO step-indexing! -/
theorem cofe_free_vtable_trace_sound (evs : List VfsEvent) :
    ∃ wFinal,
      runVfsTrace emptyVtableWorld evs = some wFinal ∧
      VtableInv wFinal := by
  have hInit : VtableInv emptyVtableWorld := by
    refine ⟨fun _ _ => rfl, fun _ => Or.inl rfl⟩
  suffices ∀ w, VtableInv w → ∃ wFinal, runVfsTrace w evs = some wFinal ∧ VtableInv wFinal from
    this emptyVtableWorld hInit
  induction evs with
  | nil =>
    intro w hw
    exact ⟨w, rfl, hw⟩
  | cons ev rest ih =>
    intro w hw
    rcases stepVfsEvent_preserves_inv w ev hw with ⟨w', hStep, hw'⟩
    simp only [runVfsTrace, hStep]
    exact ih w' hw'

/-! ### Negative Canaries 9–11: The Three Real C Ops-Table Lifecycle Bugs -/

/-- Buggy `open` that assigns `(*file).private_data = ptr.into_foreign()` BEFORE
a fallible flag check (`flags = 0x4000` -> `-EINVAL`), leaving `fModeOpened = false`
in `do_dentry_open` (`fs/open.c:1000-1004`). -/
def buggyOpenIntoForeignBeforeErr (w : VtableWorld) (flags initVal : Nat) :
    VtableWorld × Int :=
  let hid := w.nextHid
  let wAlloc :=
    { (setHandle w hid .owned initVal) with
      nextHid := hid + 1
      file := { fModeOpened := false, fFlags := flags, privateData := some hid } }
  if flags = 0x4000 then
    (wAlloc, -22) -- Returns -EINVAL; VFS does NOT set `fModeOpened := true`!
  else
    ({ wAlloc with file := { wAlloc.file with fModeOpened := true } }, 0)

/-- Negative Canary 9 (`Bug 1`: `open` non-zero return after `into_foreign` leak):
After `buggyOpenIntoForeignBeforeErr` returns `-22`, Linux `__fput`
(`soundVfsFput`) sees `fModeOpened = false` and skips `release`, permanently
leaking handle `0` in `.owned` (`¬ IsInactive (wAfterFput.stateOf 0)`)! -/
theorem canary_bug1_open_nonzero_after_into_foreign_leaks_handle :
    let (wAfterOpen, rc) := buggyOpenIntoForeignBeforeErr emptyVtableWorld 0x4000 42
    rc = -22 ∧
    ∃ wAfterFput,
      soundVfsFput wAfterOpen = some wAfterFput ∧
      wAfterFput.file.fModeOpened = false ∧
      wAfterFput.stateOf 0 = .owned ∧
      ¬ IsInactive (wAfterFput.stateOf 0) := by
  refine ⟨rfl, _, rfl, rfl, rfl, ?_⟩
  intro hInact
  rcases hInact with h | h <;> cases h

/-- Unguarded `<Box<T> as ForeignOwnable>::borrow_mut` (`kbox.rs:543-548`):
acquires `MutLoaned` (`&mut T`), invokes a C helper that re-enters `borrow_mut`
on the same handle! -/
def tryBorrowMutLinear (hid : HandleId) (w : VtableWorld) : Option VtableWorld :=
  if w.stateOf hid = .owned then
    some (setHandle w hid .mutLoaned (w.payloadOf hid))
  else
    none

/-- Negative Canary 10 (`Bug 2`: reentrant `ioctl -> C -> ioctl` `borrow_mut`
aliasing UB): While outer `ioctl` holds `.mutLoaned` (and its Tree Borrows
`FnEntry` `StrongProtector` is active on `Unique`), a nested `borrow_mut` both
violates linear `ForeignHandlePool` exclusivity (`none`) AND triggers immediate
Tree Borrows `ForeignAccess` UB (`StackPoolAndCfi.tbStep = none`)! -/
theorem canary_bug2_reentrant_unguarded_borrow_mut_aliasing_ub :
    let (wOpen, _) := soundVfsOpen emptyVtableWorld 0 10
    ∃ wOuterMut,
      tryBorrowMutLinear 0 wOpen = some wOuterMut ∧
      tryBorrowMutLinear 0 wOuterMut = none ∧
      StackPoolAndCfi.tbStep .read .foreign .unique true true = none ∧
      StackPoolAndCfi.tbStep .write .foreign .unique true true = none := by
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- Buggy `from_foreign` `release` invoked twice without linear `Owned -> Freed`
rejection (or C calling `release` twice on a stale `private_data` pointer). -/
def tryFromForeignRelease (hid : HandleId) (w : VtableWorld) : Option VtableWorld :=
  if w.stateOf hid = .owned then
    some (setHandle w hid .freed (w.payloadOf hid))
  else
    none

/-- Negative Canary 11 (`Bug 3`: double `release` / post-`release` `ioctl` UAF):
Once `from_foreign` transitions handle `0` from `.owned` to `.freed`, both a
second `from_foreign` (`release`) and a late `ioctl` (`borrow`) fail closed on
the `.freed` handle (`use-after-free / double-free`)! -/
theorem canary_bug3_double_release_from_foreign_uaf :
    let (wOpen, _) := soundVfsOpen emptyVtableWorld 0 77
    ∃ wReleasedOnce,
      tryFromForeignRelease 0 wOpen = some wReleasedOnce ∧
      wReleasedOnce.stateOf 0 = .freed ∧
      tryFromForeignRelease 0 wReleasedOnce = none ∧
      execReentrantSharedIoctl 0 5 0 wReleasedOnce = none := by
  exact ⟨_, rfl, rfl, rfl, rfl⟩

end ForeignOwnableVtable

/-! ## Axiom-Ceiling Verification (`#guard_msgs in #print axioms`) -/

/--
info: 'StackSwitchGlobalAsmAndForeignVtable.SectionWideAsmCfg.swecg_cutpoint_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms SectionWideAsmCfg.swecg_cutpoint_sound

/-- info: 'StackSwitchGlobalAsmAndForeignVtable.SectionWideAsmCfg.swecg_verifies_five_entry_cluster' does not depend on any axioms -/
#guard_msgs in
#print axioms SectionWideAsmCfg.swecg_verifies_five_entry_cluster

/-- info: 'StackSwitchGlobalAsmAndForeignVtable.StackPoolAndCfi.stack_root_cfi_undefined_halts_cleanly' depends on axioms: [propext] -/
#guard_msgs in
#print axioms StackPoolAndCfi.stack_root_cfi_undefined_halts_cleanly

/--
info: 'StackSwitchGlobalAsmAndForeignVtable.StackPoolAndCfi.canary_x64_missing_undef_reads_unmapped' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms StackPoolAndCfi.canary_x64_missing_undef_reads_unmapped

/--
info: 'StackSwitchGlobalAsmAndForeignVtable.StackPoolAndCfi.canary_a64_missing_undef_sameval_loops_forever' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms StackPoolAndCfi.canary_a64_missing_undef_sameval_loops_forever

/--
info: 'StackSwitchGlobalAsmAndForeignVtable.StackPoolAndCfi.two_entry_switch_preserves_protectors_and_disjointness' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms StackPoolAndCfi.two_entry_switch_preserves_protectors_and_disjointness

/-- info: 'StackSwitchGlobalAsmAndForeignVtable.StackPoolAndCfi.dormant_stack_tree_borrows_complete_matrix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms StackPoolAndCfi.dormant_stack_tree_borrows_complete_matrix

/--
info: 'StackSwitchGlobalAsmAndForeignVtable.ForeignOwnableVtable.reentrant_shared_ioctl_arbitrary_depth_sound' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms ForeignOwnableVtable.reentrant_shared_ioctl_arbitrary_depth_sound

/--
info: 'StackSwitchGlobalAsmAndForeignVtable.ForeignOwnableVtable.cofe_free_vtable_trace_sound' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms ForeignOwnableVtable.cofe_free_vtable_trace_sound

/-- info: 'StackSwitchGlobalAsmAndForeignVtable.ForeignOwnableVtable.canary_bug1_open_nonzero_after_into_foreign_leaks_handle' does not depend on any axioms -/
#guard_msgs in
#print axioms ForeignOwnableVtable.canary_bug1_open_nonzero_after_into_foreign_leaks_handle

/-- info: 'StackSwitchGlobalAsmAndForeignVtable.ForeignOwnableVtable.canary_bug2_reentrant_unguarded_borrow_mut_aliasing_ub' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ForeignOwnableVtable.canary_bug2_reentrant_unguarded_borrow_mut_aliasing_ub

/-- info: 'StackSwitchGlobalAsmAndForeignVtable.ForeignOwnableVtable.canary_bug3_double_release_from_foreign_uaf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ForeignOwnableVtable.canary_bug3_double_release_from_foreign_uaf

end StackSwitchGlobalAsmAndForeignVtable
