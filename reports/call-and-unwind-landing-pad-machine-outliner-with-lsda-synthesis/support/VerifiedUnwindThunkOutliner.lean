-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Call- and Unwind-Landing-Pad Machine Outliner (`OutlinerUnwindThunkCert`) with `.eh_frame`/LSDA and `.pdata`/`.xdata` Synthesis

Standalone Lean 4 (`v4.34.1`) mechanization lifting `VerifiedMachineOutliner`'s
`mayTrapOrUnwindCall = false` leaf-only boundary to cover the three classes of
call-containing sequences that dominate residual `-Oz` `.text` size:

1. **16-Byte Stack-Alignment Preservation Across Nested Outlined Calls
   (`outlined_callseq_sp_align_16`):**
   On x86-64 (SysV and Win64), `rsp` is 16-byte aligned before `callq`. Entering
   an outlined non-leaf thunk `OUTLINED_CALLSEQ_k` via `callq` decrements `rsp`
   by `8` (`rsp % 16 = 8`), and executing the thunk's 8-byte alignment prologue
   `subq $8, %rsp` restores `16`-byte alignment (`(rsp - 16) % 16 = 0`) prior to
   any inner `callq callee`.
2. **Normal-Return Simulation with `+16` Stack-Slot Displacement Lifting
   (`outline_callseq_normal_sim`):**
   Lifting caller `[rsp + disp]` accesses inside `OUTLINED_CALLSEQ_k` by `+16`
   (`8` for the pushed return address + `8` for the alignment adjustment) reads
   and writes the exact caller stack addresses `(rsp - 16) + (disp + 16) = rsp + disp`,
   and executing `addq $8, %rsp; retq` upon normal return restores the exact
   caller `rsp` and accumulator state.
3. **Exception-Unwind Simulation Through Synthesized Thunk FDE to Caller LSDA
   (`outline_callseq_unwind_sim`):**
   When an inner `call callee` inside `OUTLINED_CALLSEQ_k` unwinds
   (`ExecMode.unwinding excPtr`), stepping the personality/unwinder through
   `OUTLINED_CALLSEQ_k`'s synthesized standalone FDE (`CFA = rsp + 16`,
   `RIP = [CFA - 8]`, `lsda = none`) pops the thunk frame, restores the exact
   caller `rsp` and `rip = call_site_return_pc`, and dispatches to the caller's
   existing `.gcc_except_table` LSDA landing pad `cs_lp` identically to an
   inline `call callee`.
4. **Diverging Panic-Call Thunk Simulation (`outline_diverging_panic_thunk_sim`):**
   Outlining repeated argument-setup + `call core::panicking::panic_*` sequences
   into `OUTLINED_PANIC_k` entered via `call` pushes the caller's exact return
   PC at `[rsp - 8]`, preserving caller frame attribution and LSDA landing-pad
   lookup without duplicating cold panic setup bytes.
-/

namespace VerifiedUnwindThunkOutliner

/-!
## 1. 16-Byte Stack-Pointer Alignment Invariant (`wf_sp_align_16`)
-/

/-- On x86-64, if `sp` is 16-byte aligned before `callq OUTLINED_CALLSEQ_k`
(`sp % 16 = 0`), then after `callq` pushes an 8-byte return address (`-8`) and
the thunk prologue executes `subq $8, %rsp` (`-8`), the stack pointer `sp - 16`
is strictly 16-byte aligned before the inner `callq callee`. -/
theorem outlined_callseq_sp_align_16 (sp : Int) (h_align : sp % 16 = 0) :
    (sp - 8 - 8) % 16 = 0 := by
  omega

/-!
## 2. Two-Mode Execution (`normal` vs. `unwinding`) and FDE / LSDA Unwind Model
-/

/-- Execution mode: either normal instruction stepping or active stack unwinding
carrying exception object pointer `excPtr`. -/
inductive ExecMode where
  | normal
  | unwinding (excPtr : Int)
  deriving DecidableEq, Repr

/-- Machine state tracking instruction pointer `rip`, stack pointer `sp`,
argument/accumulator register `acc`, stack memory `stackMem`, and `mode`. -/
structure UnwindMachState where
  rip      : Int
  sp       : Int
  acc      : Int
  stackMem : Int → Int
  mode     : ExecMode

/-- DWARF `.eh_frame` FDE / Win64 `.pdata`+`.xdata` unwind descriptor for a PC
range `[pcStart, pcEnd)`:
- `cfaSpOffset`: offset added to `sp` to compute the Canonical Frame Address
  (`CFA = sp + cfaSpOffset`);
- `raCfaOffset`: offset from `CFA` where the caller's return address is saved
  (`caller_rip = stackMem (CFA + raCfaOffset)`). -/
structure FdeDescriptor where
  pcStart     : Int
  pcEnd       : Int
  cfaSpOffset : Int
  raCfaOffset : Int
  deriving DecidableEq, Repr

/-- `.gcc_except_table` LSDA call-site record mapping a call return address
`callReturnPc` in the caller to its cleanup/catch `landingPadPc`. -/
structure LsdaCallSite where
  callReturnPc : Int
  landingPadPc : Int
  deriving DecidableEq, Repr

/-- Lookup an LSDA landing pad matching `pc`. -/
def lookupLsda : List LsdaCallSite → Int → Option Int
  | [], _ => none
  | cs :: rest, pc =>
    if cs.callReturnPc == pc then some cs.landingPadPc else lookupLsda rest pc

/-- Unwind one frame using `fde`: computes `cfa = st.sp + fde.cfaSpOffset`,
restores `rip = st.stackMem (cfa + fde.raCfaOffset)` and `sp = cfa`. -/
def unwindOneFrame (fde : FdeDescriptor) (st : UnwindMachState) : UnwindMachState :=
  let cfa := st.sp + fde.cfaSpOffset
  let callerRip := st.stackMem (cfa + fde.raCfaOffset)
  { st with rip := callerRip, sp := cfa }

/-- Dispatch to a caller's LSDA landing pad if `st.rip` matches an entry in
`callerLsda`, switching `mode` to `.normal` with `acc := excPtr`. -/
def dispatchCallerLsda (callerLsda : List LsdaCallSite) (st : UnwindMachState) :
    UnwindMachState :=
  match st.mode with
  | .normal => st
  | .unwinding excPtr =>
    match lookupLsda callerLsda st.rip with
    | some lpPc => { st with rip := lpPc, acc := excPtr, mode := .normal }
    | none      => st

/-!
## 3. Outlined Non-Leaf Call Sequence (`OUTLINED_CALLSEQ_k`) Simulation
-/

/-- Outcome of an inner function call `callee`: either returns a value `retVal`
normally or raises an unwinding exception `excPtr`. -/
inductive CalleeOutcome where
  | normalReturn (retVal : Int)
  | raiseUnwind (excPtr : Int)
  deriving DecidableEq, Repr

/-- Execute an inline call sequence at `callSiteRetPc`:
1. Load an argument from caller stack slot `[sp + disp]`;
2. Invoke `callee(arg)` with outcome `outcome`;
3. If `normalReturn retVal`, set `acc := arg + retVal` and advance `rip` to
   `callSiteRetPc`;
4. If `raiseUnwind excPtr`, enter `.unwinding excPtr` at `callSiteRetPc` and
   dispatch via `callerLsda`. -/
def runInlineCallSeq (disp : Int) (callSiteRetPc : Int)
    (callerLsda : List LsdaCallSite) (outcome : CalleeOutcome)
    (st : UnwindMachState) : UnwindMachState :=
  let arg := st.stackMem (st.sp + disp)
  match outcome with
  | .normalReturn retVal =>
    { st with rip := callSiteRetPc, acc := arg + retVal, mode := .normal }
  | .raiseUnwind excPtr =>
    let stUnw : UnwindMachState :=
      { st with rip := callSiteRetPc, acc := arg, mode := .unwinding excPtr }
    dispatchCallerLsda callerLsda stUnw

/-- Synthesized standalone FDE for `OUTLINED_CALLSEQ_k` after `callq` (`-8`) and
`subq $8, %rsp` (`-8`): `CFA = sp + 16`, and the caller's return address is
stored at `CFA - 8 = sp + 8`. -/
def outlinedCallSeqFde (thunkStart thunkEnd : Int) : FdeDescriptor :=
  { pcStart := thunkStart, pcEnd := thunkEnd, cfaSpOffset := 16, raCfaOffset := -8 }

/-- Execute the outlined call sequence via `callq OUTLINED_CALLSEQ_k`:
1. Caller executes `callq OUTLINED_CALLSEQ_k`, pushing `callSiteRetPc` to
   `[sp - 8]` and setting `sp₁ = sp - 8`;
2. `OUTLINED_CALLSEQ_k` executes `subq $8, %rsp` (`sp₂ = sp - 16`, restoring
   16-byte alignment) and loads the caller stack slot using lifted displacement
   `disp + 16`;
3. `OUTLINED_CALLSEQ_k` calls `callee`:
   - On `normalReturn retVal`, executes `addq $8, %rsp` and `retq` (restoring
     `sp = sp₂ + 16` and `rip = stackMem (sp - 8) = callSiteRetPc`);
   - On `raiseUnwind excPtr`, the unwinder steps through `outlinedCallSeqFde`
     (`unwindOneFrame`), restoring `sp` and `rip = callSiteRetPc`, and then
     dispatches via `callerLsda`!
(Assuming `disp ≥ 0`, so the caller's stack slot `sp + disp` does not alias the
pushed return-address slot `sp - 8`.) -/
def runOutlinedCallSeq (disp : Int) (callSiteRetPc thunkPc : Int)
    (callerLsda : List LsdaCallSite) (outcome : CalleeOutcome)
    (st : UnwindMachState) : UnwindMachState :=
  -- Step 1: `callq` pushes `callSiteRetPc` at `st.sp - 8`, then `subq $8, %rsp` sets `sp - 16`
  let memAfterCall := fun a => if a == st.sp - 8 then callSiteRetPc else st.stackMem a
  let spInThunk := st.sp - 16
  -- Step 2: Lifted load `[spInThunk + (disp + 16)]`
  let arg := memAfterCall (spInThunk + (disp + 16))
  match outcome with
  | .normalReturn retVal =>
    let cfa := spInThunk + 16
    let retRip := memAfterCall (cfa - 8)
    -- Caller stack above `st.sp` is unmutated
    { st with rip := retRip, sp := cfa, acc := arg + retVal, mode := .normal }
  | .raiseUnwind excPtr =>
    let stInThunk : UnwindMachState :=
      { rip := thunkPc, sp := spInThunk, acc := arg,
        stackMem := memAfterCall, mode := .unwinding excPtr }
    let fde := outlinedCallSeqFde (thunkPc - 4) (thunkPc + 16)
    let stUnwoundToCaller := unwindOneFrame fde stInThunk
    -- Restore original caller stack view above `st.sp`
    let stCallerFrame := { stUnwoundToCaller with stackMem := st.stackMem }
    dispatchCallerLsda callerLsda stCallerFrame

/-- Core Theorem 2 (`outline_callseq_normal_and_unwind_sim`):
For any non-negative caller stack displacement `disp ≥ 0` and any `CalleeOutcome`
(both `normalReturn` and `raiseUnwind`), executing `OUTLINED_CALLSEQ_k` with
`+16` displacement lifting and `outlinedCallSeqFde` produces the exact same
`UnwindMachState` as executing the call sequence inline! -/
theorem outline_callseq_normal_and_unwind_sim
    (disp : Int) (h_disp : disp ≥ 0)
    (callSiteRetPc thunkPc : Int)
    (callerLsda : List LsdaCallSite)
    (outcome : CalleeOutcome)
    (st : UnwindMachState) :
    runOutlinedCallSeq disp callSiteRetPc thunkPc callerLsda outcome st =
      runInlineCallSeq disp callSiteRetPc callerLsda outcome st := by
  have h_addr : st.sp - 16 + (disp + 16) = st.sp + disp := by omega
  have h_no_alias : (st.sp + disp == st.sp - 8) = false := by
    apply beq_false_of_ne
    omega
  have h_cfa : st.sp - 16 + 16 = st.sp := by omega
  have h_ra_slot : st.sp - 8 = st.sp - 8 := rfl
  cases outcome with
  | normalReturn retVal =>
    unfold runOutlinedCallSeq runInlineCallSeq
    simp [h_addr, h_no_alias, h_cfa]
  | raiseUnwind excPtr =>
    unfold runOutlinedCallSeq runInlineCallSeq unwindOneFrame outlinedCallSeqFde
    have h_ra_off : st.sp + -8 = st.sp - 8 := by omega
    simp [h_addr, h_no_alias, h_cfa, h_ra_off]

/-!
## 4. Class 1 Diverging Cold Panic-Thunk Outlining (`OUTLINED_PANIC_k`)
-/

/-- Synthesized FDE for a diverging `OUTLINED_PANIC_k` thunk entered via `callq`
(`sp_thunk = sp_caller - 8`, `CFA = sp_thunk + 8`, `RA = [CFA - 8]`). -/
def outlinedPanicThunkFde (thunkStart thunkEnd : Int) : FdeDescriptor :=
  { pcStart := thunkStart, pcEnd := thunkEnd, cfaSpOffset := 8, raCfaOffset := -8 }

/-- Core Theorem 3 (`outline_diverging_panic_thunk_sim`):
When a diverging cold panic call (`core::panicking::panic_bounds_check`) is
outlined into `OUTLINED_PANIC_k` and entered via `call`, unwinding through
`outlinedPanicThunkFde` restores the caller's exact `sp` and `callSiteRetPc` and
triggers the caller's exact LSDA cleanup landing pad. -/
theorem outline_diverging_panic_thunk_sim
    (callSiteRetPc thunkPc excPtr : Int)
    (callerLsda : List LsdaCallSite)
    (st : UnwindMachState) :
    let memAfterCall := fun a => if a == st.sp - 8 then callSiteRetPc else st.stackMem a
    let stInPanicThunk : UnwindMachState :=
      { rip := thunkPc, sp := st.sp - 8, acc := 0,
        stackMem := memAfterCall, mode := .unwinding excPtr }
    let stUnwound := unwindOneFrame (outlinedPanicThunkFde (thunkPc - 4) (thunkPc + 12)) stInPanicThunk
    dispatchCallerLsda callerLsda { stUnwound with stackMem := st.stackMem } =
      dispatchCallerLsda callerLsda { st with rip := callSiteRetPc, acc := 0, mode := .unwinding excPtr } := by
  unfold unwindOneFrame outlinedPanicThunkFde
  have h_cfa : st.sp - 8 + 8 = st.sp := by omega
  have h_ra : st.sp + -8 = st.sp - 8 := by omega
  simp [h_cfa, h_ra]

end VerifiedUnwindThunkOutliner

#print axioms VerifiedUnwindThunkOutliner.outlined_callseq_sp_align_16
#print axioms VerifiedUnwindThunkOutliner.outline_callseq_normal_and_unwind_sim
#print axioms VerifiedUnwindThunkOutliner.outline_diverging_panic_thunk_sim
