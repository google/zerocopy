-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Mechanized Invariants for `options(nostack)` Red Zones, `MXCSR` Partitioning, PC-Range Fault Overlays, and Tear-Free Seqlock Trace Algebra

Checked with Lean `v4.34.1` (`lean -DElab.async=false -Ddebug.skipKernelTC=false`),
importing only `Init.*`, with zero `sorry` and zero `native_decide`.

Contents:
- **Part A (`NostackRedZoneInvariant` & `MxcsrPartition`):**
  1. `naive_endpoint_nostack_corrupts_redzone_local`: proves that checking only
     `rsp_exit = rsp_entry` unsoundly admits balanced `push; pop` sequences that
     silently overwrite live safe Rust locals in the 128-byte System V red zone.
  2. `stepwise_nostack_preserves_redzone_and_frame` & `no_redzone_relaxes_local_footprint`:
     establishes the exact step-wise `rsp >= rsp_entry` and disjoint-write invariant
     across default SysV red-zone vs. `-C no-redzone=yes` frames.
  3. `vaddps_inexact_violates_normative_preserves_flags_but_satisfies_split` &
     `crtfastmath_init_array_breaks_rfc3514_subnormal`: formalizes the split between
     preserved `MXCSR[15:6]` control bits and monotonic `MXCSR[5:0]` sticky exception
     flags, and proves how `.init_array` `crtfastmath.o` constructors poison pure safe
     Rust subnormal evaluation relative to CTFE.
- **Part B (`FaultTableOverlay`):**
  4. `atomic_noop_fault_model_unsound_for_usercopy`: proves that modeling a faulting
     memory copy as an atomic state rollback is unsound under partial prefix writes.
  5. `fault_overlay_usercopy_partial_write_exact` & `rseq_pre_commit_abort_preserves_mem`:
     unifies `asm_goto` static jump labels, synchronous `[start_pc, end_pc) -> fixup_pc`
     `usercopy`/`__ex_table` fault recovery with exact `written + rem = req` partial-write
     accounting, and asynchronous `rseq` pre-commit abort redirection.
- **Part C (`MemTraceEvent` Over `OpenComponent` Traces):**
  6. `plain_seqlock_reader_triggers_data_race_ub`: proves that optimistic seqlock readers
     using `.plain` non-atomic loads trigger immediate data-race UB even when torn
     reads are discarded by `seq1 != seq2`.
  7. `seqlock_single_copy_atomic_reader_sound`: proves both data-race freedom (even on
     torn overlapping retries) and exact multi-word snapshot coherence whenever an
     optimistic reader using `.singleCopyAtomic` (`asm!` `mov` / `READ_ONCE`) loads
     observes matching even sequence counters `seq1 = seq2`.
  8. `sequential_schedule_collapses_mem_trace_to_state`: proves that in the absence of
     concurrent writers, `MemTraceEvent` collapses extensionally to plain sequential
     state updates with zero proof overhead.
-/

namespace NostackMxcsrOverlaySeqlock

/-! ## Part A: `options(nostack)` Red-Zone Invariant & `MXCSR` Partition -/

structure StackState where
  rsp : Nat
  mem : Nat → Nat

def writeMem (m : Nat → Nat) (addr val : Nat) : Nat → Nat :=
  fun a => if a = addr then val else m a

inductive StackMicroOp where
  | push8 (val : Nat)
  | pop8
  | store8 (addr val : Nat)
  | aluNop

def stepStackOp (st : StackState) (op : StackMicroOp) : StackState :=
  match op with
  | .push8 val =>
      let newRsp := st.rsp - 8
      { rsp := newRsp, mem := writeMem st.mem newRsp val }
  | .pop8 =>
      { rsp := st.rsp + 8, mem := st.mem }
  | .store8 addr val =>
      { rsp := st.rsp, mem := writeMem st.mem addr val }
  | .aluNop => st

def runStackOps (st : StackState) (ops : List StackMicroOp) : StackState :=
  ops.foldl stepStackOp st

def redZoneBytes (noRedZone : Bool) : Nat :=
  if noRedZone then 0 else 128

/-- Caller-owned stack addresses protected across an `options(nostack)` block:
    under default System V AMD64 (`noRedZone = false`), LLVM places live leaf-frame
    Rust locals inside `[rspEntry - 128, rspEntry)` as well as `[rspEntry, ∞)`. -/
def inCallerProtectedStack (noRedZone : Bool) (rspEntry addr : Nat) : Prop :=
  rspEntry - redZoneBytes noRedZone ≤ addr

/-- Naive endpoint-only `nostack` check (`rsp_exit = rsp_entry`). -/
def NaiveEndpointNostack (rspEntry : Nat) (sFinal : StackState) : Prop :=
  sFinal.rsp = rspEntry

/-- Theorem A1 (Sharpness): Balanced `push poison; pop` satisfies `rsp_exit = rsp_entry`
    yet silently overwrites a live safe Rust local at `rspEntry - 8` in the red zone. -/
theorem naive_endpoint_nostack_corrupts_redzone_local
    (rspEntry origVal poison : Nat)
    (hRsp : 128 ≤ rspEntry)
    (hDiff : poison ≠ origVal) :
    let s0 : StackState := { rsp := rspEntry, mem := fun a => if a = rspEntry - 8 then origVal else 0 }
    let ops : List StackMicroOp := [.push8 poison, .pop8]
    let sFinal := runStackOps s0 ops
    NaiveEndpointNostack rspEntry sFinal ∧
      inCallerProtectedStack false rspEntry (rspEntry - 8) ∧
      sFinal.mem (rspEntry - 8) = poison ∧
      sFinal.mem (rspEntry - 8) ≠ s0.mem (rspEntry - 8) := by
  intro s0 ops sFinal
  have h1 : rspEntry - 8 + 8 = rspEntry := by omega
  have hProtected : rspEntry - 128 ≤ rspEntry - 8 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [NaiveEndpointNostack, sFinal, runStackOps, ops, stepStackOp, s0]
    exact h1
  · dsimp [inCallerProtectedStack, redZoneBytes]
    exact hProtected
  · dsimp [sFinal, runStackOps, ops, stepStackOp, writeMem, s0]
    simp
  · dsimp [sFinal, runStackOps, ops, stepStackOp, writeMem, s0]
    simp [hDiff]

/-- Step-wise admissibility of a single micro-op under `options(nostack)`:
    `rsp` never drops below `rspEntry`, and any store address outside `explicitMut`
    is strictly disjoint from `inCallerProtectedStack noRedZone rspEntry`. -/
def ValidNostackOp
    (noRedZone : Bool) (rspEntry : Nat) (explicitMut : Nat → Bool)
    (st : StackState) (op : StackMicroOp) : Prop :=
  match op with
  | .push8 _ => False
  | .pop8 => st.rsp ≥ rspEntry
  | .store8 addr _ =>
      st.rsp ≥ rspEntry ∧ (explicitMut addr = true ∨ ¬ inCallerProtectedStack noRedZone rspEntry addr)
  | .aluNop => st.rsp ≥ rspEntry

def StepwiseNostackTrace
    (noRedZone : Bool) (rspEntry : Nat) (explicitMut : Nat → Bool) :
    StackState → List StackMicroOp → Prop
  | st, [] => st.rsp ≥ rspEntry
  | st, op :: rest =>
      ValidNostackOp noRedZone rspEntry explicitMut st op ∧
        StepwiseNostackTrace noRedZone rspEntry explicitMut (stepStackOp st op) rest

/-- Theorem A2 (Soundness): Every micro-op trace satisfying `StepwiseNostackTrace`
    maintains `rsp >= rspEntry` at every step and preserves every caller-protected
    stack byte (including all red-zone locals when `noRedZone = false`) outside
    explicitly passed mutable pointer targets. -/
theorem stepwise_nostack_preserves_redzone_and_frame
    (noRedZone : Bool) (rspEntry : Nat) (explicitMut : Nat → Bool)
    (ops : List StackMicroOp) (st : StackState)
    (hTrace : StepwiseNostackTrace noRedZone rspEntry explicitMut st ops) :
    (runStackOps st ops).rsp ≥ rspEntry ∧
      ∀ a, inCallerProtectedStack noRedZone rspEntry a → explicitMut a = false →
        (runStackOps st ops).mem a = st.mem a := by
  induction ops generalizing st with
  | nil =>
      exact ⟨hTrace, fun _ _ _ => rfl⟩
  | cons op rest ih =>
      obtain ⟨hValid, hRest⟩ := hTrace
      obtain ⟨hRspFinal, hMemRest⟩ := ih (stepStackOp st op) hRest
      refine ⟨hRspFinal, fun a hProt hNotMut => ?_⟩
      rw [runStackOps] at *
      dsimp [List.foldl]
      rw [hMemRest a hProt hNotMut]
      cases op with
      | push8 _ => exact False.elim hValid
      | pop8 => rfl
      | aluNop => rfl
      | store8 addr val =>
          obtain ⟨_, hDisj⟩ := hValid
          dsimp [stepStackOp, writeMem]
          cases hDisj with
          | inl hMut =>
              have hNe : a ≠ addr := by
                intro hEq
                subst hEq
                rw [hMut] at hNotMut
                contradiction
              simp [hNe]
          | inr hNotProt =>
              have hNe : a ≠ addr := by
                intro hEq
                subst hEq
                exact hNotProt hProt
              simp [hNe]

/-- Theorem A3: Under `-C no-redzone=yes` (`noRedZone = true`), LLVM allocates safe
    Rust locals at `[rspEntry, ∞)` (`sub rsp, N`), so `[rspEntry - 128, rspEntry)` is
    excluded from `inCallerProtectedStack` while `[rspEntry, ∞)` remains protected. -/
theorem no_redzone_relaxes_local_footprint (rspEntry : Nat) (hRsp : 128 ≤ rspEntry) :
    inCallerProtectedStack false rspEntry (rspEntry - 8) ∧
      ¬ inCallerProtectedStack true rspEntry (rspEntry - 8) ∧
      inCallerProtectedStack true rspEntry rspEntry := by
  dsimp [inCallerProtectedStack, redZoneBytes]
  refine ⟨by omega, by omega, by omega⟩

/-! ### `MXCSR` Partition (`ControlBits` `[15:6]` vs `StickyFlags` `[5:0]`) & `crtfastmath.o` -/

structure MxcsrState where
  /-- `MXCSR[15:6]`: `FTZ` (bit 15), `RC` (bits 14:13), masks (bits 12:7), `DAZ` (bit 6). -/
  controlBits : Nat
  /-- `MXCSR[5:0]`: sticky exception status bits (`PE`, `UE`, `OE`, `ZE`, `DE`, `IE`). -/
  stickyFlags : Nat
  deriving DecidableEq, Repr

/-- Default System V AMD64 / Rust RFC 3514 `MXCSR = 0x1f80`:
    all 6 exceptions masked (`0x1f80 >> 6 = 0x7e`), `RC = RNE (0)`, `DAZ = 0`, `FTZ = 0`,
    and clean sticky flags `0`. -/
def defaultMxcsr : MxcsrState :=
  { controlBits := 0x7e, stickyFlags := 0 }

/-- Normative `r[asm.rules.preserved-registers]` when `options(preserves_flags)` is set:
    requires restoring `MXCSR` exception flags (`PE, UE, OE, ZE, DE, IE`) as well as control bits. -/
def NormativePreservesFlagsMxcsr (mEntry mExit : MxcsrState) : Prop :=
  mExit.controlBits = mEntry.controlBits ∧ mExit.stickyFlags = mEntry.stickyFlags

/-- Split `MXCSR` contract for `asm!` *without* `preserves_flags` and SysV C ABI calls:
    `controlBits` (`[15:6]`) sits in `Frame` (must be preserved), while `stickyFlags` (`[5:0]`)
    sits in `Slack` (monotonically ORed by ordinary IEEE-754 operations). -/
def SplitMxcsrFrameSlack (mEntry mExit : MxcsrState) : Prop :=
  mExit.controlBits = mEntry.controlBits ∧
    (mExit.stickyFlags &&& mEntry.stickyFlags) = mEntry.stickyFlags

def stepInexactFpOp (m : MxcsrState) : MxcsrState :=
  { m with stickyFlags := m.stickyFlags ||| 0x20 }

/-- Theorem A4: A single inexact SSE/AVX instruction (e.g. `vaddss` setting `PE = 0x20`)
    violates `options(preserves_flags)` (`NormativePreservesFlagsMxcsr`) from a clean entry state,
    while satisfying `SplitMxcsrFrameSlack` when `preserves_flags` is omitted. -/
theorem vaddps_inexact_violates_normative_preserves_flags_but_satisfies_split :
    ¬ NormativePreservesFlagsMxcsr defaultMxcsr (stepInexactFpOp defaultMxcsr) ∧
      SplitMxcsrFrameSlack defaultMxcsr (stepInexactFpOp defaultMxcsr) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hSticky := h.2
    dsimp [defaultMxcsr, stepInexactFpOp] at hSticky
    omega
  · dsimp [SplitMxcsrFrameSlack, defaultMxcsr, stepInexactFpOp]
    exact ⟨rfl, rfl⟩

/-- `crtfastmath.o` `.init_array` constructor `set_fast_math`: ORs `DAZ` (`1 << 0` in `[15:6]`)
    and `FTZ` (`1 << 9` in `[15:6]`), changing `MXCSR` from `0x1f80` (`controlBits = 0x7e`)
    to `0x9fc0` (`controlBits = 0x27f`). -/
def setFastMathCtor (m : MxcsrState) : MxcsrState :=
  { m with controlBits := m.controlBits ||| 0x201 }

def runInitArray (ctors : List (MxcsrState → MxcsrState)) (m0 : MxcsrState) : MxcsrState :=
  ctors.foldl (fun m f => f m) m0

def hasDazOrFtz (m : MxcsrState) : Bool :=
  (m.controlBits &&& 0x201) != 0

/-- Pure safe Rust runtime addition `subnormal + 0.0` vs CTFE `const` addition. -/
def evalSafeRustSubnormalAddZeroRt (m : MxcsrState) (subnormalBits : Nat) : Nat :=
  if hasDazOrFtz m then 0 else subnormalBits

def evalSafeRustSubnormalAddZeroCtfe (subnormalBits : Nat) : Nat :=
  subnormalBits

/-- Theorem A5: Linking `crtfastmath.o` into `.init_array` mutates `MXCSR` `controlBits`
    before `main()`, causing pure safe Rust runtime subnormal evaluation (with zero FFI calls)
    to flush `0x00400000` to `0` and diverge from Rust CTFE! -/
theorem crtfastmath_init_array_breaks_rfc3514_subnormal :
    let cleanBoot := runInitArray [] defaultMxcsr
    let poisonedBoot := runInitArray [setFastMathCtor] defaultMxcsr
    evalSafeRustSubnormalAddZeroRt cleanBoot 0x00400000 =
        evalSafeRustSubnormalAddZeroCtfe 0x00400000 ∧
      evalSafeRustSubnormalAddZeroRt poisonedBoot 0x00400000 = 0 ∧
      evalSafeRustSubnormalAddZeroRt poisonedBoot 0x00400000 ≠
        evalSafeRustSubnormalAddZeroCtfe 0x00400000 := by
  dsimp [defaultMxcsr, setFastMathCtor, runInitArray, hasDazOrFtz,
         evalSafeRustSubnormalAddZeroRt, evalSafeRustSubnormalAddZeroCtfe]
  refine ⟨rfl, rfl, by decide⟩


/-! ## Part B: Sideband ELF Control-Flow Overlays (`asm_goto`, `usercopy` / `__ex_table`, `rseq`) -/

inductive SidebandOverlay where
  /-- Static key (`asm_goto` + `__jump_table`): redirects `patchPc` to `targetPc` when enabled. -/
  | staticJump (patchPc targetPc : Nat) (enabled : Bool)
  /-- Synchronous fault fixup (`__ex_table` or Starnix `[startPc, endPc) -> fixupPc`). -/
  | syncFaultFixup (startPc endPc fixupPc : Nat)
  /-- Asynchronous Linux `rseq` critical section (`[startPc, commitPc) -> abortPc` on preemption). -/
  | asyncRseqAbort (startPc commitPc abortPc : Nat)

def lookupSyncFixup (overlays : List SidebandOverlay) (faultPc : Nat) : Option Nat :=
  match overlays with
  | [] => none
  | .syncFaultFixup s e fix :: rest =>
      if s ≤ faultPc ∧ faultPc < e then some fix else lookupSyncFixup rest faultPc
  | _ :: rest => lookupSyncFixup rest faultPc

def lookupAsyncRseqAbort (overlays : List SidebandOverlay) (pc : Nat) : Option Nat :=
  match overlays with
  | [] => none
  | .asyncRseqAbort s c abort :: rest =>
      if s ≤ pc ∧ pc < c then some abort else lookupAsyncRseqAbort rest pc
  | _ :: rest => lookupAsyncRseqAbort rest pc

structure CopyMachineState where
  pc : Nat
  dst : Nat
  src : Nat
  rem : Nat
  retReg : Nat
  mem : Nat → Nat

/-- PC layout for a byte-granularity `usercopy` loop (`[10, 12)` guarded by `syncFaultFixup 10 12 20`,
    normal completion at `12 -> 30`, fault fixup at `20 -> 30`). -/
def stepUsercopyWithOverlay
    (isMapped : Nat → Bool) (overlays : List SidebandOverlay)
    (st : CopyMachineState) : Option CopyMachineState :=
  if st.pc = 10 then
    if st.rem = 0 then
      some { st with pc := 12 }
    else if isMapped st.src then
      let b := st.mem st.src
      some { st with
        pc := 10
        dst := st.dst + 1
        src := st.src + 1
        rem := st.rem - 1
        mem := writeMem st.mem st.dst b }
    else
      -- Synchronous page fault (`#PF` / `SIGSEGV`) at `st.pc = 10`: consult fault table!
      match lookupSyncFixup overlays st.pc with
      | some fixPc => some { st with pc := fixPc }
      | none => none -- Unhandled hardware trap!
  else if st.pc = 12 then
    some { st with pc := 30, retReg := 0 }
  else if st.pc = 20 then
    some { st with pc := 30, retReg := st.rem }
  else
    some st

def runCopySteps
    (isMapped : Nat → Bool) (overlays : List SidebandOverlay) :
    Nat → CopyMachineState → Option CopyMachineState
  | 0, st => some st
  | fuel + 1, st =>
      match stepUsercopyWithOverlay isMapped overlays st with
      | none => none
      | some st' => runCopySteps isMapped overlays fuel st'

/-- Inductive loop lemma for `valid` mapped prefix bytes followed by an unmapped page boundary. -/
theorem copy_mapped_prefix_exact
    (overlays : List SidebandOverlay)
    (valid tail dst src ret0 : Nat)
    (mem : Nat → Nat)
    (isMapped : Nat → Bool)
    (hDisj : dst + valid ≤ src ∨ src + valid ≤ dst)
    (hMapped : ∀ i, i < valid → isMapped (src + i) = true) :
    ∃ mem',
      runCopySteps isMapped overlays valid
        { pc := 10, dst := dst, src := src, rem := valid + tail, retReg := ret0, mem := mem } =
        some { pc := 10, dst := dst + valid, src := src + valid, rem := tail, retReg := ret0, mem := mem' } ∧
      (∀ i, i < valid → mem' (dst + i) = mem (src + i)) ∧
      (∀ a, (∀ i, i < valid → a ≠ dst + i) → mem' a = mem a) := by
  induction valid generalizing dst src mem with
  | zero =>
      refine ⟨mem, ?_, ?_, ?_⟩
      · simp [runCopySteps]
      · intro i hi; omega
      · intro a _; rfl
  | succ k ih =>
      have hMap0 : isMapped src = true := by
        have h0 := hMapped 0 (by omega)
        simpa using h0
      have hRemSub : k + 1 + tail - 1 = k + tail := by omega
      let mem1 := writeMem mem dst (mem src)
      have hDisj' : (dst + 1) + k ≤ (src + 1) ∨ (src + 1) + k ≤ (dst + 1) := by omega
      have hMapped' : ∀ i, i < k → isMapped ((src + 1) + i) = true := by
        intro i hi
        have h := hMapped (i + 1) (by omega)
        have hEq : src + (i + 1) = src + 1 + i := by omega
        rw [← hEq]
        exact h
      obtain ⟨mem', hRunRest, hPrefixRest, hFrameRest⟩ :=
        ih (dst + 1) (src + 1) mem1 hDisj' hMapped'
      have hStepUnfold :
          runCopySteps isMapped overlays (k + 1)
            { pc := 10, dst := dst, src := src, rem := k + 1 + tail, retReg := ret0, mem := mem } =
          runCopySteps isMapped overlays k
            { pc := 10, dst := dst + 1, src := src + 1, rem := k + tail, retReg := ret0, mem := mem1 } := by
        dsimp [runCopySteps, stepUsercopyWithOverlay]
        simp [hMap0, hRemSub, mem1]
      refine ⟨mem', ?_, ?_, ?_⟩
      · rw [hStepUnfold]
        have hAddDst : dst + 1 + k = dst + (k + 1) := by omega
        have hAddSrc : src + 1 + k = src + (k + 1) := by omega
        rw [hAddDst, hAddSrc] at hRunRest
        exact hRunRest
      · intro i hi
        cases i with
        | zero =>
            have hOut : ∀ j, j < k → dst + 0 ≠ (dst + 1) + j := by omega
            have hKeep := hFrameRest (dst + 0) hOut
            simp [mem1, writeMem] at hKeep ⊢
            exact hKeep
        | succ j =>
            have hj : j < k := by omega
            have hEqDst : dst + (j + 1) = (dst + 1) + j := by omega
            have hEqSrc : src + (j + 1) = (src + 1) + j := by omega
            rw [hEqDst, hEqSrc, hPrefixRest j hj]
            have hNeDst : (src + 1) + j ≠ dst := by omega
            dsimp [mem1, writeMem]
            simp [hNeDst]
      · intro a hNotIn
        have hNotTail : ∀ j, j < k → a ≠ (dst + 1) + j := by
          intro j hj
          have h := hNotIn (j + 1) (by omega)
          intro hEq
          apply h
          omega
        rw [hFrameRest a hNotTail]
        have hNe0 : a ≠ dst := by
          have h := hNotIn 0 (by omega)
          simpa using h
        dsimp [mem1, writeMem]
        simp [hNe0]

/-- Theorem B2 (General Soundness of PC-Range Fault Overlay on Partial Usercopy):
    For any `valid` mapped bytes followed by an unmapped byte (`tail + 1` remaining),
    `[10, 12) -> 20` catches the synchronous fault without trapping, sets `retReg = tail + 1`
    (so `copied + retReg = valid + (tail + 1)`), writes the exact `valid`-byte prefix to `dst`,
    and leaves all other memory untouched. -/
theorem fault_overlay_usercopy_partial_write_exact
    (valid tail dst src ret0 : Nat)
    (mem : Nat → Nat)
    (isMapped : Nat → Bool)
    (hDisj : dst + valid ≤ src ∨ src + valid ≤ dst)
    (hMapped : ∀ i, i < valid → isMapped (src + i) = true)
    (hFaultAtBoundary : isMapped (src + valid) = false) :
    let overlays := [SidebandOverlay.syncFaultFixup 10 12 20]
    ∃ mem',
      runCopySteps isMapped overlays (valid + 2)
        { pc := 10, dst := dst, src := src, rem := valid + (tail + 1), retReg := ret0, mem := mem } =
        some { pc := 30, dst := dst + valid, src := src + valid, rem := tail + 1, retReg := tail + 1, mem := mem' } ∧
      (∀ i, i < valid → mem' (dst + i) = mem (src + i)) ∧
      (∀ a, (∀ i, i < valid → a ≠ dst + i) → mem' a = mem a) := by
  intro overlays
  obtain ⟨mem', hPrefixRun, hPrefixBytes, hFrameBytes⟩ :=
    copy_mapped_prefix_exact overlays valid (tail + 1) dst src ret0 mem isMapped hDisj hMapped
  refine ⟨mem', ?_, hPrefixBytes, hFrameBytes⟩
  have hSplit :
      ∀ n s, runCopySteps isMapped overlays (n + 2) s =
        match runCopySteps isMapped overlays n s with
        | none => none
        | some s1 => runCopySteps isMapped overlays 2 s1 := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ m ihm =>
        intro s
        dsimp [runCopySteps]
        cases stepUsercopyWithOverlay isMapped overlays s with
        | none => rfl
        | some sNext => exact ihm sNext
  rw [hSplit valid]
  rw [hPrefixRun]
  dsimp [runCopySteps, stepUsercopyWithOverlay, overlays, lookupSyncFixup]
  simp [hFaultAtBoundary]

/-- Theorem B1 (Sharpness): Modeling a faulting `usercopy` as an atomic no-op that
    leaves destination memory equal to `memInit` is unsound whenever `valid > 0`
    bytes precede an unmapped page boundary (instantiated at `valid = 19, req = 32, rem = 13`). -/
theorem atomic_noop_fault_model_unsound_for_usercopy :
    let isMapped := fun addr => decide (addr < 1019)
    let overlays := [SidebandOverlay.syncFaultFixup 10 12 20]
    let memInit := fun addr => if 1000 ≤ addr ∧ addr < 1019 then 77 else 0xaa
    ∃ mem',
      runCopySteps isMapped overlays 21
        { pc := 10, dst := 2000, src := 1000, rem := 32, retReg := 999, mem := memInit } =
        some { pc := 30, dst := 2019, src := 1019, rem := 13, retReg := 13, mem := mem' } ∧
      mem' 2000 = 77 ∧
      mem' 2000 ≠ memInit 2000 ∧
      mem' 2019 = 0xaa := by
  intro isMapped overlays memInit
  have hDisj : 2000 + 19 ≤ 1000 ∨ 1000 + 19 ≤ 2000 := by omega
  have hMap : ∀ i, i < 19 → isMapped (1000 + i) = true := by
    intro i hi
    dsimp [isMapped]
    exact decide_eq_true (by omega)
  have hUnmap : isMapped (1000 + 19) = false := by
    dsimp [isMapped]
    exact decide_eq_false (by omega)
  obtain ⟨mem', hRun, hPre, hFrm⟩ :=
    fault_overlay_usercopy_partial_write_exact 19 12 2000 1000 999 memInit isMapped hDisj hMap hUnmap
  refine ⟨mem', hRun, ?_, ?_, ?_⟩
  · have h0 := hPre 0 (by omega)
    simpa [memInit] using h0
  · have h0 := hPre 0 (by omega)
    have hInit : memInit 2000 = 0xaa := by decide
    have hNew : mem' 2000 = 77 := by simpa [memInit] using h0
    omega
  · have hOut : ∀ i, i < 19 → 2019 ≠ 2000 + i := by omega
    have hEq := hFrm 2019 hOut
    have hInit : memInit 2019 = 0xaa := by decide
    omega

/-- Linux `rseq` pre-commit abort soundness (`Theorem B3`): if every instruction in
    `[startPc, commitPc)` writes only register/thread-private state and only `commitPc`
    mutates shared memory, redirecting any preempted `pc ∈ [startPc, commitPc)` to `abortPc`
    preserves shared memory identically (`st'.sharedMem = st.sharedMem`). -/
structure RseqState where
  pc : Nat
  scratchReg : Nat
  sharedMem : Nat → Nat

def stepRseqPreempt (overlays : List SidebandOverlay) (st : RseqState) : RseqState :=
  match lookupAsyncRseqAbort overlays st.pc with
  | some abortPc => { st with pc := abortPc }
  | none => st

theorem rseq_pre_commit_abort_preserves_mem
    (startPc commitPc abortPc : Nat) (st : RseqState)
    (hInWindow : startPc ≤ st.pc ∧ st.pc < commitPc) :
    let overlays := [SidebandOverlay.asyncRseqAbort startPc commitPc abortPc]
    let st' := stepRseqPreempt overlays st
    st'.pc = abortPc ∧ st'.sharedMem = st.sharedMem := by
  intro overlays st'
  dsimp [st', stepRseqPreempt, overlays, lookupAsyncRseqAbort]
  simp [hInWindow]


/-! ## Part C: Weak-Memory & Tear-Free Seqlock Trace Algebra (`MemTraceEvent`) -/

inductive AccessOrder where
  | plain            -- Non-atomic MIR load/store (`Atomicity::None` in MiniRust/`lean-miri`)
  | singleCopyAtomic -- Tear-free single-instruction `asm!` `mov` / `READ_ONCE` / `WRITE_ONCE`
  | acquire
  | release
  | acqRel
  | seqCst
  deriving DecidableEq, Repr

inductive MemTraceEvent where
  | load (ord : AccessOrder) (addr : Nat) (val : Nat)
  | store (ord : AccessOrder) (addr : Nat) (val : Nat)
  | rmw (ord : AccessOrder) (addr : Nat) (oldVal newVal : Nat)
  | fence (ord : AccessOrder)
  deriving DecidableEq, Repr

def eventAddr? : MemTraceEvent → Option Nat
  | .load _ a _ => some a
  | .store _ a _ => some a
  | .rmw _ a _ _ => some a
  | .fence _ => none

def isWriteEvent : MemTraceEvent → Bool
  | .load _ _ _ => false
  | .store _ _ _ => true
  | .rmw _ _ _ _ => true
  | .fence _ => false

def isPlainEvent : MemTraceEvent → Bool
  | .load .plain _ _ => true
  | .store .plain _ _ => true
  | .rmw .plain _ _ _ => true
  | _ => false

structure TimedTraceItem where
  tid : Nat
  ev : MemTraceEvent
  deriving DecidableEq, Repr

/-- MiniRust / C++20 / `lean-miri` data-race criterion: two unordered accesses (`¬ hb i j ∧ ¬ hb j i`)
    by distinct threads to the same address, at least one a write, trigger immediate UB
    if and only if at least one access is `.plain` (`Atomicity::None`). -/
def HasPlainDataRace (tr : List TimedTraceItem) (hb : Nat → Nat → Prop) : Prop :=
  ∃ i j : Nat, ∃ ti tj : TimedTraceItem,
    tr[i]? = some ti ∧
    tr[j]? = some tj ∧
    i ≠ j ∧
    ti.tid ≠ tj.tid ∧
    (∃ a, eventAddr? ti.ev = some a ∧ eventAddr? tj.ev = some a) ∧
    (isWriteEvent ti.ev = true ∨ isWriteEvent tj.ev = true) ∧
    (isPlainEvent ti.ev = true ∨ isPlainEvent tj.ev = true) ∧
    ¬ hb i j ∧ ¬ hb j i

/-- Theorem C1 (Sharpness): An optimistic seqlock reader that reads payload words via `.plain`
    non-atomic MIR loads triggers `HasPlainDataRace` UB against a concurrent writer store,
    EVEN WHEN the reader later observes `seq1 = 2 ≠ 4 = seq2` and discards the payload! -/
theorem plain_seqlock_reader_triggers_data_race_ub :
    let addrSeq := 0
    let addrPayload := 1
    let tr : List TimedTraceItem := [
      { tid := 1, ev := .load .acquire addrSeq 2 },          -- idx 0: reader seq1 = 2
      { tid := 2, ev := .store .release addrSeq 3 },         -- idx 1: writer begins epoch (odd = 3)
      { tid := 1, ev := .load .plain addrPayload 42 },       -- idx 2: reader PLAIN load (DATA RACE!)
      { tid := 2, ev := .store .singleCopyAtomic addrPayload 99 }, -- idx 3: writer concurrent store
      { tid := 2, ev := .store .release addrSeq 4 },         -- idx 4: writer finishes epoch (even = 4)
      { tid := 1, ev := .load .acquire addrSeq 4 }           -- idx 5: reader sees seq2 = 4 != 2, discards!
    ]
    let hb := fun i j =>
      -- Same-thread program order only; concurrent overlapping reader/writer have no hb between 2 and 3!
      (i = 0 ∧ (j = 2 ∨ j = 5)) ∨ (i = 2 ∧ j = 5) ∨
      (i = 1 ∧ (j = 3 ∨ j = 4)) ∨ (i = 3 ∧ j = 4)
    HasPlainDataRace tr hb := by
  intro addrSeq addrPayload tr hb
  refine ⟨2, 3, { tid := 1, ev := .load .plain 1 42 }, { tid := 2, ev := .store .singleCopyAtomic 1 99 },
          rfl, rfl, by decide, by decide, ⟨1, rfl, rfl⟩, Or.inr rfl, Or.inl rfl, ?_, ?_⟩
  · intro h; dsimp [hb] at h; omega
  · intro h; dsimp [hb] at h; omega

/-- Lemma: Any trace whose shared-memory events never use `.plain` ordering is guaranteed
    free of `HasPlainDataRace` UB under *every* happens-before relation `hb`—including
    interleavings where a seqlock writer overlaps an optimistic reader! -/
theorem non_plain_trace_never_data_races
    (tr : List TimedTraceItem) (hb : Nat → Nat → Prop)
    (hNoPlain : ∀ item ∈ tr, isPlainEvent item.ev = false) :
    ¬ HasPlainDataRace tr hb := by
  intro ⟨i, j, ti, tj, hi, hj, _, _, _, _, hPlain, _, _⟩
  have hMemI : ti ∈ tr := List.mem_of_getElem? hi
  have hMemJ : tj ∈ tr := List.mem_of_getElem? hj
  cases hPlain with
  | inl hPi =>
      rw [hNoPlain ti hMemI] at hPi
      contradiction
  | inr hPj =>
      rw [hNoPlain tj hMemJ] at hPj
      contradiction

/-! ### Tear-Free Optimistic Seqlock Snapshot Coherence Proof -/

/-- Axiomatic execution witness for a `K`-word seqlock with sequence-counter protocol:
    - Initial epoch `0` holds coherent snapshot `epochSnap 0 : Nat → Nat` (`seq = 0`).
    - Writer epoch `e + 1` increments `seq` to odd `2 * e + 1` (`Release`), writes each word `j`
      with `epochSnap (e + 1) j` via `.singleCopyAtomic`, and increments `seq` to even `2 * (e + 1)`
      (`Release`).
    - An optimistic reader attempt reads `seq1` (`Acquire`), reads each word `j` from some
      single-copy-atomic writer epoch `srcEpoch j` (`SingleCopyAtomic`, so no intra-word bit tearing,
      though `srcEpoch j₁` and `srcEpoch j₂` MAY differ when a writer overlaps!), executes
      `fence .acquire`, and reloads `seq2` (`Acquire`). -/
structure SeqlockReaderAttempt (epochSnap : Nat → Nat → Nat) where
  seq1 : Nat
  seq2 : Nat
  /-- For each payload word `j`, single-copy atomicity guarantees `wordVal j = epochSnap (srcEpoch j) j`
      for some writer epoch `srcEpoch j`. -/
  srcEpoch : Nat → Nat
  wordVal : Nat → Nat
  hSingleCopyAtomic : ∀ j, wordVal j = epochSnap (srcEpoch j) j
  /-- Release-Acquire + coherence lower bound: if `seq1 = 2 * e` (writer epoch `e` already completed
      its `Release` store `seq := 2 * e` before reader's `Acquire` load `seq1`), then every subsequent
      payload read `wordVal j` observes epoch `>= e` (cannot read overwritten pre-`e` stores). -/
  hAcqAfterEpochComplete : ∀ e j, seq1 = 2 * e → e ≤ srcEpoch j
  /-- Load-Acquire / `fence .acquire` before `seq2` upper bound: if `seq2 = 2 * e` (writer epoch
      `e + 1` has NOT yet executed its `Release`/ordered odd store `seq := 2 * e + 1` before `seq2`),
      and `wordVal j` is ordered before `seq2` via `fence .acquire`, then `wordVal j` cannot observe
      any store from epoch `>= e + 1`, so `srcEpoch j <= e`. -/
  hFenceBeforeSeq2 : ∀ e j, seq2 = 2 * e → srcEpoch j ≤ e

def optimisticReadResult {epochSnap : Nat → Nat → Nat}
    (att : SeqlockReaderAttempt epochSnap) : Option (Nat → Nat) :=
  if att.seq1 % 2 == 0 && att.seq1 == att.seq2 then
    some att.wordVal
  else
    none

/-- Theorem C2 (Tear-Free Optimistic Seqlock Soundness):
    1. Every shared trace emitted using `.singleCopyAtomic` / `.acquire` / `.release` / `.fence`
       is 100% free of `HasPlainDataRace` UB—even on aborted attempts where `srcEpoch 0 ≠ srcEpoch 1`
       observes a torn multi-word combination across concurrent writers!
    2. Whenever `optimisticReadResult att = some snap`, there exists a unique writer epoch `e`
       (`seq1 = seq2 = 2 * e`) such that for EVERY payload word `j`, `snap j = epochSnap e j`
       (exact multi-word snapshot coherence!). -/
theorem seqlock_single_copy_atomic_reader_sound
    {epochSnap : Nat → Nat → Nat}
    (att : SeqlockReaderAttempt epochSnap)
    (tr : List TimedTraceItem) (hb : Nat → Nat → Prop)
    (hTraceNonPlain : ∀ item ∈ tr, isPlainEvent item.ev = false) :
    ¬ HasPlainDataRace tr hb ∧
      ∀ snap, optimisticReadResult att = some snap →
        ∃ e, att.seq1 = 2 * e ∧ att.seq2 = 2 * e ∧ ∀ j, snap j = epochSnap e j := by
  refine ⟨non_plain_trace_never_data_races tr hb hTraceNonPlain, ?_⟩
  intro snap hRes
  dsimp [optimisticReadResult] at hRes
  split at hRes
  case isTrue hCond =>
    injection hRes with hSnapEq
    subst hSnapEq
    have hAnd : (att.seq1 % 2 == 0) = true ∧ (att.seq1 == att.seq2) = true :=
      Bool.and_eq_true_iff.mp hCond
    have hEven : att.seq1 % 2 = 0 := of_decide_eq_true hAnd.1
    have hSeqEq : att.seq1 = att.seq2 := of_decide_eq_true hAnd.2
    refine ⟨att.seq1 / 2, ?_, ?_, ?_⟩
    · omega
    · omega
    · intro j
      have hEq2 : att.seq1 = 2 * (att.seq1 / 2) := by omega
      have hEq2' : att.seq2 = 2 * (att.seq1 / 2) := by omega
      have hLo : att.seq1 / 2 ≤ att.srcEpoch j := att.hAcqAfterEpochComplete (att.seq1 / 2) j hEq2
      have hHi : att.srcEpoch j ≤ att.seq1 / 2 := att.hFenceBeforeSeq2 (att.seq1 / 2) j hEq2'
      have hEpochEq : att.srcEpoch j = att.seq1 / 2 := by omega
      rw [att.hSingleCopyAtomic j, hEpochEq]
  case isFalse =>
    contradiction

/-! ### Upward-Compatible Zero-Overhead Collapse to Sequential Memory (`Theorem C3`) -/

/-- Sequential memory interpreter over `MemTraceEvent` (ignoring ordering tags). -/
def stepSeqMemEvent (m : Nat → Nat) (ev : MemTraceEvent) : Option (Nat → Nat) :=
  match ev with
  | .load _ addr val => if m addr = val then some m else none
  | .store _ addr val => some (writeMem m addr val)
  | .rmw _ addr oldVal newVal =>
      if m addr = oldVal then some (writeMem m addr newVal) else none
  | .fence _ => some m

def eraseOrderToPlain : MemTraceEvent → MemTraceEvent
  | .load _ addr val => .load .plain addr val
  | .store _ addr val => .store .plain addr val
  | .rmw _ addr oldVal newVal => .rmw .plain addr oldVal newVal
  | .fence _ => .fence .plain

def runSeqMemTrace : List MemTraceEvent → (Nat → Nat) → Option (Nat → Nat)
  | [], m => some m
  | ev :: rest, m =>
      match stepSeqMemEvent m ev with
      | none => none
      | some m' => runSeqMemTrace rest m'

/-- Theorem C3 (Zero-Overhead Sequential Collapse):
    In any single-threaded / uncontended execution, `MemTraceEvent` with arbitrary weak-memory
    orderings (`.singleCopyAtomic`, `.acquire`, `.release`, `.acqRel`, `.seqCst`) evaluates
    identically to its order-erased `.plain` sequential projection—preserving zero-overhead
    sequential reasoning when concurrency is absent. -/
theorem sequential_schedule_collapses_mem_trace_to_state
    (evs : List MemTraceEvent) (m : Nat → Nat) :
    runSeqMemTrace evs m = runSeqMemTrace (evs.map eraseOrderToPlain) m := by
  induction evs generalizing m with
  | nil => rfl
  | cons ev rest ih =>
      have hStepEq : stepSeqMemEvent m ev = stepSeqMemEvent m (eraseOrderToPlain ev) := by
        cases ev <;> rfl
      dsimp [List.map, runSeqMemTrace]
      rw [← hStepEq]
      cases stepSeqMemEvent m ev with
      | none => rfl
      | some m' => exact ih m'

/-- `OpenComponent` step interface parameterized by `MemTraceEvent` (bridging mixed MIR-ISA
    call stacks to concurrent weak-memory and seqlock trace composition). -/
inductive OpenMemStep (S Q R : Type) where
  | tau (next : S)
  | mem (ev : MemTraceEvent) (next : S)
  | call (query : Q) (onReply : R → S)
  | ret (reply : R)
  | ub

structure OpenMemComponent (S Q R : Type) where
  step : S → OpenMemStep S Q R

/-- Forward simulation over `OpenMemComponent` preserves exact `MemTraceEvent` sequences
    (including `.plain` vs `.singleCopyAtomic` vs `.acquire`/`.release`/`.fence` tags). -/
def OpenMemSim {S₁ S₂ Q R : Type}
    (c₁ : OpenMemComponent S₁ Q R) (c₂ : OpenMemComponent S₂ Q R)
    (Rel : S₁ → S₂ → Prop) : Prop :=
  ∀ s₁ s₂, Rel s₁ s₂ →
    match c₁.step s₁, c₂.step s₂ with
    | .tau s₁', .tau s₂' => Rel s₁' s₂'
    | .mem ev₁ s₁', .mem ev₂ s₂' => ev₁ = ev₂ ∧ Rel s₁' s₂'
    | .call q₁ k₁, .call q₂ k₂ => q₁ = q₂ ∧ ∀ r, Rel (k₁ r) (k₂ r)
    | .ret r₁, .ret r₂ => r₁ = r₂
    | .ub, .ub => True
    | _, _ => False

inductive TraceOfSteps {S Q R : Type} (c : OpenMemComponent S Q R) :
    Nat → S → List MemTraceEvent → Option R → Prop where
  | zero (s : S) : TraceOfSteps c 0 s [] none
  | tau {n s s' tr out} :
      c.step s = .tau s' → TraceOfSteps c n s' tr out → TraceOfSteps c (n + 1) s tr out
  | mem {n s s' ev tr out} :
      c.step s = .mem ev s' → TraceOfSteps c n s' tr out → TraceOfSteps c (n + 1) s (ev :: tr) out
  | ret {n s r} :
      c.step s = .ret r → TraceOfSteps c (n + 1) s [] (some r)

/-- Theorem C4: `OpenMemSim` preserves exact emitted `MemTraceEvent` lists and terminal replies,
    so any verified `OpenMemComponent` refinement preserves both `HasPlainDataRace` freedom
    and `sequential_schedule_collapses_mem_trace_to_state`. -/
theorem open_mem_sim_preserves_mem_trace
    {S₁ S₂ Q R : Type}
    (c₁ : OpenMemComponent S₁ Q R) (c₂ : OpenMemComponent S₂ Q R)
    (Rel : S₁ → S₂ → Prop)
    (hSim : OpenMemSim c₁ c₂ Rel)
    (fuel : Nat) (s₁ : S₁) (s₂ : S₂) (tr : List MemTraceEvent) (out : Option R)
    (hRel : Rel s₁ s₂)
    (hTr : TraceOfSteps c₁ fuel s₁ tr out) :
    TraceOfSteps c₂ fuel s₂ tr out := by
  induction hTr generalizing s₂ with
  | zero _ => exact .zero s₂
  | @tau n s s₁' tr out hStep₁ _ ih =>
      have hStepSim := hSim s s₂ hRel
      rw [hStep₁] at hStepSim
      cases hStep₂ : c₂.step s₂ <;> rw [hStep₂] at hStepSim
      case tau s₂' => exact .tau hStep₂ (ih s₂' hStepSim)
      all_goals exact False.elim hStepSim
  | @mem n s s₁' ev tr out hStep₁ _ ih =>
      have hStepSim := hSim s s₂ hRel
      rw [hStep₁] at hStepSim
      cases hStep₂ : c₂.step s₂ <;> rw [hStep₂] at hStepSim
      case mem ev₂ s₂' =>
        obtain ⟨hEvEq, hRel'⟩ := hStepSim
        subst hEvEq
        exact .mem hStep₂ (ih s₂' hRel')
      all_goals exact False.elim hStepSim
  | @ret n s r hStep₁ =>
      have hStepSim := hSim s s₂ hRel
      rw [hStep₁] at hStepSim
      cases hStep₂ : c₂.step s₂ <;> rw [hStep₂] at hStepSim
      case ret r₂ =>
        subst hStepSim
        exact .ret hStep₂
      all_goals exact False.elim hStepSim

#print axioms naive_endpoint_nostack_corrupts_redzone_local
#print axioms stepwise_nostack_preserves_redzone_and_frame
#print axioms no_redzone_relaxes_local_footprint
#print axioms vaddps_inexact_violates_normative_preserves_flags_but_satisfies_split
#print axioms crtfastmath_init_array_breaks_rfc3514_subnormal
#print axioms atomic_noop_fault_model_unsound_for_usercopy
#print axioms fault_overlay_usercopy_partial_write_exact
#print axioms rseq_pre_commit_abort_preserves_mem
#print axioms plain_seqlock_reader_triggers_data_race_ub
#print axioms seqlock_single_copy_atomic_reader_sound
#print axioms sequential_schedule_collapses_mem_trace_to_state
#print axioms open_mem_sim_preserves_mem_trace

end NostackMxcsrOverlaySeqlock
