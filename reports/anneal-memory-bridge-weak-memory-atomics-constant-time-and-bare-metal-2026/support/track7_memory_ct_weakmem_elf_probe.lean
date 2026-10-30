-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Track 7 Mechanization Probe: 4-Phase Memory Bridge, Constant-Time CT-Cube,
# Weak-Memory Atomics, `compiler_fence` ISR Safety, and Bare-Metal ELF Startup

This standalone Lean 4.34.1 file mechanizes the five core mathematical pillars
of Track 7 for Anneal's verified Rust compiler architecture:

1. **The 4-Phase Memory Bridge (`Phase1AllocMem` -> `Phase4FlatHwMem`)**:
   Refines abstract `(AllocId, offset)` block memory (extending Anneal's
   `Trusted/Memory.lean`) through a quasi-concrete disjoint-interval model
   supporting strict-provenance `ptr.with_addr`, an explicit activation-stack
   frame model (`FrameADT`), and a flat byte-addressable hardware memory with a
   downward-growing `SP` register under a static `StackBudget`.
2. **Three-Component Trace `(iota, sigma, lambda)` & `CompCertCT` CT-Cube**:
   Proves that register spilling modifies the single-execution microarchitectural
   leakage trace `lambda` (by emitting stack address observations
   `LeakEvent.leakAddr (sp + ofs)`), yet preserves 2-safety constant-time
   non-interference via a relational 2-simulation ("CT-Cube") because spill
   decisions and stack offsets are static functions of syntax and `sp` is
   public. Also proves a negative canary showing that `SelectOpt` (`cmov` to
   branch conversion) violates constant-time.
3. **`compiler_fence` and Asynchronous Interrupt Handler (ISR) Safety**:
   Proves that if `core::sync::atomic::compiler_fence(SeqCst)` emits no
   intermediate synchronization event in `iota` during mid-end optimizations,
   reordering two non-atomic stores (`data := 42; ready := 1`) is sequentially
   sound at function exit yet violates the same-CPU interrupt handler invariant
   (`ready = 1 -> data = 42`) at intermediate preemption points. Preserving an
   explicit `IotaEvent.compilerFence` barrier until `Asmgen` guarantees the ISR
   invariant at every preemption point.
4. **Weak-Memory Atomic Lowering Hazards (RISC-V RVWMO & AArch64 RCpc)**:
   Mechanizes the 2-thread Store-Buffering (`SB` / Dekker) execution graph and
   proves that:
   - Mixing RISC-V Table A.6 `store(SeqCst)` (`fence rw,w; sw`) with Table A.7
     `load(SeqCst)` (`lw.aq` without a leading `fence rw,rw`) removes the
     `Store -> Load` preserved program order (`ppo`) edge and permits the
     non-SC weak outcome `(r0 = 0, r1 = 0)`, whereas retaining the leading
     `fence rw,rw` (or adding a psABI trailing `fence rw,rw`) forbids it.
   - Lowering AArch64 `SeqCst` loads to `LDAPR` (`Q`, ARMv8.3-A `FEAT_LRCPC`)
     paired with `STLR` (`L`) permits `(r0 = 0, r1 = 0)` because `[L]; sb; [Q]`
     is absent from Barrier-Ordered-Before (`bob`), whereas lowering `SeqCst`
     loads to `LDAR` (`A`) enforces `[L]; sb; [A]` in `bob` and forbids it.
5. **Bare-Metal Startup (`_start`, `linker.ld`) & Static ELF Relocations**:
   Mechanizes `LinkerLayoutSpec`, proves that executing `_start` (copying
   `.data` from Flash LMA to SRAM VMA, zeroing `.bss`, and setting `SP`)
   establishes the initial `Static` memory validity and stack invariant required
   by `MirSemantics`, and proves exact symbol recovery for static PC-relative
   ELF relocations.
-/

namespace Track7Probe

-- ============================================================================
-- Part 1: The 4-Phase Memory Bridge & Strict Provenance (`with_addr`)
-- ============================================================================

/-- Abstract allocation identifier matching Anneal's `Trusted/MirSemantics.lean`
and MiniRust / Cerberus VIP allocation IDs. -/
abbrev AllocId := Nat

/-- An individual byte cell in abstract/quasi-concrete memory, tracking
initialization and optional pointer provenance. -/
inductive MemByte where
  | uninit : MemByte
  | init (val : UInt8) (prov : Option AllocId) : MemByte
  deriving DecidableEq, Repr

/-- Pointer value carrying an explicit provenance `AllocId` and a byte offset
within that allocation (Phase 1) or a flat integer address (Phase 2). -/
structure ProvenancePtr where
  prov : AllocId
  offset : Nat
  deriving DecidableEq, Repr

/-- Phase 1 (Abstract Allocation Model): Memory is indexed by `(AllocId, ofs)`
with no numerical ordering between distinct allocations. -/
structure Phase1AllocMem where
  cells : AllocId → Nat → MemByte
  size : AllocId → Nat

/-- Phase 1 bounds check: offset `ofs` lies strictly within `size aid`. -/
def Phase1AllocMem.inBounds (m : Phase1AllocMem) (p : ProvenancePtr) : Prop :=
  p.offset < m.size p.prov

/-- Phase 1 byte read: succeeds only when `p` is in bounds for its provenance. -/
def Phase1AllocMem.loadByte (m : Phase1AllocMem) (p : ProvenancePtr) :
    Option MemByte :=
  if p.offset < m.size p.prov then
    some (m.cells p.prov p.offset)
  else
    none

/-- Phase 2 (Quasi-Concrete Disjoint Interval Model): Each live allocation is
assigned a concrete base address `base aid` in the flat address space such that
distinct allocations occupy disjoint address intervals. -/
structure Phase2Layout where
  base : AllocId → Nat
  size : AllocId → Nat
  disjoint :
    ∀ a1 a2 ofs1 ofs2,
      a1 ≠ a2 →
      ofs1 < size a1 →
      ofs2 < size a2 →
      base a1 + ofs1 ≠ base a2 + ofs2

/-- Concrete flat address of a `ProvenancePtr` under a `Phase2Layout`. -/
def ProvenancePtr.toFlatAddr (L : Phase2Layout) (p : ProvenancePtr) : Nat :=
  L.base p.prov + p.offset

/-- Strict-provenance `ptr.with_addr(addr)` (and Cerberus VIP `copy_alloc_id`)
on a quasi-concrete pointer: replaces the pointer's concrete address with `addr`
while preserving its provenance `p.prov` by storing the relative offset
`addr - L.base p.prov`. -/
def ProvenancePtr.withAddr (L : Phase2Layout) (p : ProvenancePtr)
    (addr : Nat) : ProvenancePtr :=
  { prov := p.prov, offset := addr - L.base p.prov }

/-- Round-trip law for `withAddr`: whenever `addr ≥ L.base p.prov`, setting the
address to `addr` via `withAddr` yields exact flat address `addr` while
preserving provenance `p.prov`. -/
theorem withAddr_toFlatAddr_roundtrip (L : Phase2Layout) (p : ProvenancePtr)
    (addr : Nat) (hGe : L.base p.prov ≤ addr) :
    (p.withAddr L addr).toFlatAddr L = addr ∧
      (p.withAddr L addr).prov = p.prov := by
  unfold ProvenancePtr.withAddr ProvenancePtr.toFlatAddr
  simp only [and_true]
  omega

/-- Phase 3 (Explicit Activation Stack `FrameADT` Model): Per-call local stack
slots and register-spill slots are grouped into an explicit activation frame
record rather than separate unbounded heap blocks. -/
structure FrameRecord where
  frameSize : Nat
  slots : Nat → UInt8

/-- Phase 3 state: an explicit call stack of activation frames (`frames`)
paired with static/heap memory. -/
structure Phase3FrameState where
  frames : List FrameRecord
  staticMem : Nat → UInt8

/-- Total bytes currently allocated on the Phase 3 activation stack. -/
def totalFrameBytes : List FrameRecord → Nat
  | [] => 0
  | f :: fs => f.frameSize + totalFrameBytes fs

/-- Phase 4 (Flat Hardware Memory with `SP` and `StackBudget`): A single flat
byte-addressable RAM `ram : Nat → UInt8` with hardware stack pointer `sp : Nat`
growing downward from `stackTop` down to `stackLimit = stackTop - stackBudget`. -/
structure Phase4FlatHwState where
  ram : Nat → UInt8
  sp : Nat
  stackTop : Nat
  stackBudget : Nat

/-- Relational invariant linking Phase 3 (`FrameADT` top frame) and Phase 4
(flat hardware RAM at `[sp, sp + top.frameSize)`), together with disjointness
from the static segment `[0, staticLimit)`. -/
def Phase3To4Refines (staticLimit : Nat) (s3 : Phase3FrameState)
    (s4 : Phase4FlatHwState) : Prop :=
  staticLimit ≤ s4.stackTop - s4.stackBudget ∧
  s4.stackTop - s4.stackBudget ≤ s4.sp ∧
  s4.sp ≤ s4.stackTop ∧
  (∀ addr, addr < staticLimit → s4.ram addr = s3.staticMem addr) ∧
  match s3.frames with
  | [] => s4.sp = s4.stackTop
  | top :: _ =>
      s4.sp + top.frameSize ≤ s4.stackTop ∧
      (∀ ofs, ofs < top.frameSize → s4.ram (s4.sp + ofs) = top.slots ofs)

/-- Phase 3 to Phase 4 simulation theorem: Under `Phase3To4Refines`, reading
offset `ofs < top.frameSize` from the active stack frame in Phase 3 yields the
exact byte stored at `sp + ofs` in flat hardware RAM in Phase 4, and cannot
alias any address in the static segment `[0, staticLimit)`. -/
theorem phase3_to_phase4_load_preserved (staticLimit : Nat)
    (s3 : Phase3FrameState) (s4 : Phase4FlatHwState) (top : FrameRecord)
    (rest : List FrameRecord) (ofs : Nat)
    (hFrames : s3.frames = top :: rest)
    (hRef : Phase3To4Refines staticLimit s3 s4)
    (hOfs : ofs < top.frameSize) :
    s4.ram (s4.sp + ofs) = top.slots ofs ∧ staticLimit ≤ s4.sp + ofs := by
  rcases hRef with ⟨hDisj, hSpLow, _hSpHigh, _hStatic, hTop⟩
  rw [hFrames] at hTop
  rcases hTop with ⟨_hFrameBound, hSlotEq⟩
  refine ⟨hSlotEq ofs hOfs, ?_⟩
  omega

/-- Stack-budget safety theorem: If the caller's `sp` equals
`stackTop - usedBytes` and the new frame's `frameSize` satisfies
`usedBytes + frameSize ≤ stackBudget`, then allocating the frame by decrementing
`sp' := sp - frameSize` never underflows `stackTop - stackBudget` and never
aliases `[0, staticLimit)`. -/
theorem stack_overflow_impossible_under_budget (staticLimit stackTop stackBudget
    usedBytes frameSize : Nat)
    (hStaticDisj : staticLimit ≤ stackTop - stackBudget)
    (hBudgetLeTop : stackBudget ≤ stackTop)
    (hFit : usedBytes + frameSize ≤ stackBudget) :
    let sp := stackTop - usedBytes
    let sp' := sp - frameSize
    stackTop - stackBudget ≤ sp' ∧ staticLimit ≤ sp' := by
  intro sp sp'
  omega

-- ============================================================================
-- Part 2: Three-Component Trace (iota, sigma, lambda) & CompCertCT CT-Cube
-- ============================================================================

/-- Security classification of program locations for constant-time analysis. -/
inductive SecLevel where
  | pub : SecLevel
  | sec : SecLevel
  deriving DecidableEq, Repr

/-- Microarchitectural leakage observation component (`lambda`), modeling
branch-condition and memory-address observations in `CompCertCT` (Barthe et al.
POPL 2020) and Jasmin (`jasmin-lang/jasmin`). -/
inductive LeakEvent where
  | leakBranch (cond : Bool) : LeakEvent
  | leakAddr (addr : Nat) : LeakEvent
  deriving DecidableEq, Repr

/-- I/O, volatile MMIO, and compiler-fence synchronization trace component
(`iota`). -/
inductive IotaEvent where
  | mmioRead (addr : Nat) (val : Nat) : IotaEvent
  | mmioWrite (addr : Nat) (val : Nat) : IotaEvent
  | compilerFence : IotaEvent
  deriving DecidableEq, Repr

/-- Shared-memory concurrency trace component (`sigma`). -/
inductive SigmaEvent where
  | atomicLoad (loc : Nat) (val : Nat) : SigmaEvent
  | atomicStore (loc : Nat) (val : Nat) : SigmaEvent
  | fence : SigmaEvent
  deriving DecidableEq, Repr

/-- Unified three-component operational trace element `(iota, sigma, lambda)`
specializing the `Obs` parameter of Anneal's `Trusted/StepResult.lean`. -/
structure TraceTriple where
  iota : List IotaEvent
  sigma : List SigmaEvent
  lambda : List LeakEvent
  deriving DecidableEq, Repr

/-- Register machine state with a public stack pointer `sp`, a register file
`regs : Nat → Nat`, and a spill stack `stack : Nat → Nat`. -/
structure RegMachineState where
  sp : Nat
  regs : Nat → Nat
  stack : Nat → Nat

/-- Low-equivalence (`s1 ≈_L s2`) between two machine states: their public
stack pointers agree (`s1.sp = s2.sp`) and all public registers agree, while
secret registers may hold arbitrary distinct values. -/
def LowEquiv (regPolicy : Nat → SecLevel) (s1 s2 : RegMachineState) : Prop :=
  s1.sp = s2.sp ∧
  ∀ r, regPolicy r = SecLevel.pub → s1.regs r = s2.regs r

/-- Source register-transfer instruction before register spilling. -/
inductive RtlInstr where
  | binAdd (dst src1 src2 : Nat) : RtlInstr
  | cmov (dst condReg srcT srcF : Nat) : RtlInstr
  deriving DecidableEq, Repr

/-- Target instruction after a register-spilling pass (which spills `dst` to
stack offset `spillOfs`) or after an unsafe `SelectOpt` pass (which lowers
`cmov` to a conditional branch). -/
inductive TargetInstr where
  | binAddSpilled (dst src1 src2 spillOfs : Nat) : TargetInstr
  | cmovSpilled (dst condReg srcT srcF spillOfs : Nat) : TargetInstr
  | selectBranch (dst condReg srcT srcF : Nat) : TargetInstr
  deriving DecidableEq, Repr

/-- Source leakage semantics (`lambda_src`): pure register arithmetic and
hardware `cmov` emit zero microarchitectural leakage events (`[]`). -/
def evalRtlLeak (_s : RegMachineState) : RtlInstr → List LeakEvent
  | RtlInstr.binAdd _ _ _ => []
  | RtlInstr.cmov _ _ _ _ => []

/-- Target leakage semantics (`lambda_tgt`):
- Spilled instructions write their result to `[sp + spillOfs]`, emitting an
  address leakage event `[LeakEvent.leakAddr (s.sp + spillOfs)]`.
- `selectBranch` branches on `s.regs condReg != 0`, emitting
  `[LeakEvent.leakBranch (s.regs condReg != 0)]`. -/
def evalTargetLeak (s : RegMachineState) : TargetInstr → List LeakEvent
  | TargetInstr.binAddSpilled _ _ _ spillOfs =>
      [LeakEvent.leakAddr (s.sp + spillOfs)]
  | TargetInstr.cmovSpilled _ _ _ _ spillOfs =>
      [LeakEvent.leakAddr (s.sp + spillOfs)]
  | TargetInstr.selectBranch _ condReg _ _ =>
      [LeakEvent.leakBranch (!decide (s.regs condReg = 0))]

/-- Static register-spilling pass parameterized by a syntax-driven slot map
`slotOf : Nat → Nat`. -/
def spillInstr (slotOf : Nat → Nat) : RtlInstr → TargetInstr
  | RtlInstr.binAdd dst s1 s2 =>
      TargetInstr.binAddSpilled dst s1 s2 (slotOf dst)
  | RtlInstr.cmov dst condReg sT sF =>
      TargetInstr.cmovSpilled dst condReg sT sF (slotOf dst)

/-- Theorem 2a (`spillPass_modifies_single_trace`): Spilling a register
strictly modifies the single-execution leakage trace (`lambda_tgt ≠ lambda_src`),
demonstrating why standard single-execution CompCert trace preservation cannot
verify register allocation under constant-time leakage semantics. -/
theorem spillPass_modifies_single_trace (slotOf : Nat → Nat)
    (s : RegMachineState) (i : RtlInstr) :
    evalTargetLeak s (spillInstr slotOf i) ≠ evalRtlLeak s i := by
  cases i <;> simp [spillInstr, evalTargetLeak, evalRtlLeak]

/-- Theorem 2b (`spillPass_preserves_constantTime` — The `CompCertCT` CT-Cube
2-Simulation Theorem): For any two low-equivalent initial states `s1` and `s2`
(`LowEquiv regPolicy s1 s2`), even when `i` operates on secret registers, the
spilled target instruction emits identical leakage traces on both runs
(`evalTargetLeak s1 (spillInstr slotOf i) = evalTargetLeak s2 (spillInstr slotOf i)`),
because the stack offset `slotOf dst` is a static function of instruction syntax
and `s1.sp = s2.sp` is public! -/
theorem spillPass_preserves_constantTime (regPolicy : Nat → SecLevel)
    (slotOf : Nat → Nat) (s1 s2 : RegMachineState) (i : RtlInstr)
    (hLow : LowEquiv regPolicy s1 s2) :
    evalTargetLeak s1 (spillInstr slotOf i) =
      evalTargetLeak s2 (spillInstr slotOf i) := by
  rcases hLow with ⟨hSp, _hRegs⟩
  cases i <;> simp [spillInstr, evalTargetLeak, hSp]

/-- Unsafe `SelectOpt` transformation (mirroring LLVM's `SelectOptimize` pass),
rewriting constant-time `cmov` into a conditional branch `selectBranch`. -/
def selectOptInstr : RtlInstr → TargetInstr
  | RtlInstr.binAdd dst s1 s2 => TargetInstr.binAddSpilled dst s1 s2 0
  | RtlInstr.cmov dst condReg sT sF =>
      TargetInstr.selectBranch dst condReg sT sF

/-- Theorem 2c (`selectOpt_violates_constantTime` — Negative Canary): When
`condReg` is secret (`regPolicy 1 = SecLevel.sec`), two low-equivalent states
`s1` (with secret condition `0`) and `s2` (with secret condition `1`) produce
identical source leakage traces under `cmov`, but distinct target leakage traces
under `selectOptInstr`. -/
theorem selectOpt_violates_constantTime :
    let regPolicy : Nat → SecLevel := fun r =>
      if r = 1 then SecLevel.sec else SecLevel.pub
    let s1 : RegMachineState :=
      { sp := 0x1000, regs := fun _ => 0, stack := fun _ => 0 }
    let s2 : RegMachineState :=
      { sp := 0x1000,
        regs := fun r => if r = 1 then 1 else 0,
        stack := fun _ => 0 }
    let instr := RtlInstr.cmov 2 1 3 4
    LowEquiv regPolicy s1 s2 ∧
    evalRtlLeak s1 instr = evalRtlLeak s2 instr ∧
    evalTargetLeak s1 (selectOptInstr instr) ≠
      evalTargetLeak s2 (selectOptInstr instr) := by
  refine ⟨?_, rfl, ?_⟩
  · constructor
    · rfl
    · intro r hPub
      by_cases h1 : r = 1
      · subst h1
        contradiction
      · simp [h1]
  · intro hEq
    dsimp [selectOptInstr, evalTargetLeak] at hEq
    nomatch hEq

-- ============================================================================
-- Part 3: `compiler_fence` & Asynchronous Interrupt Handler (ISR) Reordering
-- ============================================================================

/-- Memory state shared between main thread and same-CPU Interrupt Service
Routine (ISR): `data` payload and `ready` flag. -/
structure IsrMemState where
  data : Nat
  ready : Nat
  deriving DecidableEq, Repr

/-- The asynchronous ISR invariant: whenever the interrupt handler fires and
observes `ready = 1`, `data` must already equal `42`. -/
def IsrInvariant (m : IsrMemState) : Prop :=
  m.ready = 1 → m.data = 42

/-- Mid-end statement in the presence of `compiler_fence`. -/
inductive FenceStmt where
  | storeData (v : Nat) : FenceStmt
  | storeReady (v : Nat) : FenceStmt
  | compilerFenceSeqCst : FenceStmt
  deriving DecidableEq, Repr

/-- Single-step execution producing updated memory and an `IotaEvent` list. -/
def stepFenceStmt (m : IsrMemState) : FenceStmt → IsrMemState × List IotaEvent
  | FenceStmt.storeData v => ({ m with data := v }, [])
  | FenceStmt.storeReady v => ({ m with ready := v }, [])
  | FenceStmt.compilerFenceSeqCst => (m, [IotaEvent.compilerFence])

/-- Final state of executing a statement list sequentially. -/
def runSeqFinal (m : IsrMemState) : List FenceStmt → IsrMemState
  | [] => m
  | stmt :: rest => runSeqFinal (stepFenceStmt m stmt).1 rest

/-- All intermediate states (preemption points) reachable during execution of
a statement list, where a same-CPU asynchronous interrupt handler may run. -/
def reachablePreemptionStates (m : IsrMemState) :
    List FenceStmt → List IsrMemState
  | [] => [m]
  | stmt :: rest =>
      let m' := (stepFenceStmt m stmt).1
      m :: reachablePreemptionStates m' rest

/-- Source program: `data := 42; compiler_fence(SeqCst); ready := 1`. -/
def srcIsrProg : List FenceStmt :=
  [FenceStmt.storeData 42,
   FenceStmt.compilerFenceSeqCst,
   FenceStmt.storeReady 1]

/-- Illegally reordered target program when `compiler_fence` is erased early:
`ready := 1; data := 42`. -/
def reorderedBadProg : List FenceStmt :=
  [FenceStmt.storeReady 1,
   FenceStmt.storeData 42]

/-- Initial memory state (`data = 0, ready = 0`). -/
def initIsrMem : IsrMemState := { data := 0, ready := 0 }

/-- Theorem 3a (`reorder_without_compiler_fence_sound_sequentially`): If an
optimizer only checks final memory state at function exit (and ignores
`IotaEvent.compilerFence`), `srcIsrProg` and `reorderedBadProg` yield the exact
same final memory state `{ data := 42, ready := 1 }`. -/
theorem reorder_without_compiler_fence_sound_sequentially :
    runSeqFinal initIsrMem srcIsrProg =
      runSeqFinal initIsrMem reorderedBadProg := rfl

/-- Theorem 3b (`reorder_without_compiler_fence_violates_isr_safety`): At the
preemption point after the first instruction of `reorderedBadProg`, the memory
state `{ data := 0, ready := 1 }` is reachable and violates `IsrInvariant`. -/
theorem reorder_without_compiler_fence_violates_isr_safety :
    ∃ m ∈ reachablePreemptionStates initIsrMem reorderedBadProg,
      ¬ IsrInvariant m := by
  refine ⟨{ data := 0, ready := 1 }, ?_, ?_⟩
  · simp [reorderedBadProg, reachablePreemptionStates, stepFenceStmt,
      initIsrMem]
  · intro hInv
    have h42 : (0 : Nat) = 42 := hInv rfl
    omega

/-- Theorem 3c (`preserving_compiler_fence_guarantees_isr_safety`): In
`srcIsrProg`, where `compiler_fence(SeqCst)` prevents reordering `storeReady 1`
across `compilerFenceSeqCst`, every reachable preemption state satisfies
`IsrInvariant`. -/
theorem preserving_compiler_fence_guarantees_isr_safety :
    ∀ m ∈ reachablePreemptionStates initIsrMem srcIsrProg,
      IsrInvariant m := by
  intro m hIn
  simp only [srcIsrProg, reachablePreemptionStates, stepFenceStmt, initIsrMem,
    List.mem_cons, List.not_mem_nil, or_false] at hIn
  rcases hIn with rfl | rfl | rfl | rfl
  · intro hReady
    nomatch hReady
  · intro hReady
    nomatch hReady
  · intro hReady
    nomatch hReady
  · intro _hReady
    rfl

-- ============================================================================
-- Part 4: Weak-Memory Atomic Compilation Hazards (RISC-V & AArch64)
-- ============================================================================

/-- The 4 memory events of the 2-thread Store-Buffering (`SB` / Dekker) litmus
test:
- Thread 0 executes `wx` (`x := 1`) followed in program order by `ry` (`r0 := y`)
- Thread 1 executes `wy` (`y := 1`) followed in program order by `rx` (`r1 := x`)
-/
inductive SbEvent where
  | wx : SbEvent
  | ry : SbEvent
  | wy : SbEvent
  | rx : SbEvent
  deriving DecidableEq, Repr

/-- For the weak outcome `(r0 = 0, r1 = 0)` where both loads read the initial
value `0` before the opposite thread's store of `1`, the from-reads (`fr`)
relation orders `ry` before `wy` (`ry ->_fr wy`) and `rx` before `wx`
(`rx ->_fr wx`). -/
def sbWeakFr (e1 e2 : SbEvent) : Prop :=
  (e1 = SbEvent.ry ∧ e2 = SbEvent.wy) ∨
  (e1 = SbEvent.rx ∧ e2 = SbEvent.wx)

/-- An execution is globally consistent with a preserved-program-order relation
`ppo` under `sbWeakFr` iff there exists a strict timestamp assignment
`tau : SbEvent → Nat` respecting both `ppo` and `sbWeakFr` (equivalent to
acyclicity of `ppo ∪ fr`). -/
def SbWeakOutcomeAllowed (ppo : SbEvent → SbEvent → Prop) : Prop :=
  ∃ tau : SbEvent → Nat,
    (∀ e1 e2, ppo e1 e2 → tau e1 < tau e2) ∧
    (∀ e1 e2, sbWeakFr e1 e2 → tau e1 < tau e2)

/-- RISC-V lowering choice for `store(SeqCst)` and `load(SeqCst)`:
- `tableA6Leading`: Table A.6 (`fence rw,w; sw` and `fence rw,rw; lw; fence r,rw`)
- `mixedA6StoreA7Load`: Table A.6 store (`fence rw,w; sw`, no `.rl` bit and no
  trailing `fence rw,rw`) mixed with Table A.7 load (`lw.aq`, no leading
  `fence rw,rw`)
- `psAbiTrailingCompatible`: psABI compatible store (`fence rw,w; sw; fence rw,rw`)
  paired with any load (`lw.aq` or `fence rw,rw; lw; fence r,rw`). -/
inductive RiscvScScheme where
  | tableA6Leading : RiscvScScheme
  | mixedA6StoreA7Load : RiscvScScheme
  | psAbiTrailingCompatible : RiscvScScheme
  deriving DecidableEq, Repr

/-- Under RVWMO, a `Store -> Load` pair (`wx -> ry` or `wy -> rx`) on the same
thread is in `ppo` iff either a `fence rw,rw` separates the store and load
(`tableA6Leading` and `psAbiTrailingCompatible`) or the store has `.rl` and the
load has `.aq`. In `mixedA6StoreA7Load`, the store is a plain `sw` (preceded by
`fence rw,w`) and the load is `lw.aq` (with no leading `fence rw,rw`), so NO
`ppo` edge holds between the store and the load! -/
def riscvSbPpo (scheme : RiscvScScheme) (e1 e2 : SbEvent) : Prop :=
  match scheme with
  | RiscvScScheme.mixedA6StoreA7Load => False
  | RiscvScScheme.tableA6Leading =>
      (e1 = SbEvent.wx ∧ e2 = SbEvent.ry) ∨
      (e1 = SbEvent.wy ∧ e2 = SbEvent.rx)
  | RiscvScScheme.psAbiTrailingCompatible =>
      (e1 = SbEvent.wx ∧ e2 = SbEvent.ry) ∨
      (e1 = SbEvent.wy ∧ e2 = SbEvent.rx)

/-- Theorem 4a (`riscv_mixed_tableA6_A7_allows_weak_sb`): Mixing Table A.6
`store(SeqCst)` (`fence rw,w; sw`) with Table A.7 `load(SeqCst)` (`lw.aq`)
permits the non-SC weak outcome `(r0 = 0, r1 = 0)` in Store Buffering. -/
theorem riscv_mixed_tableA6_A7_allows_weak_sb :
    SbWeakOutcomeAllowed (riscvSbPpo RiscvScScheme.mixedA6StoreA7Load) := by
  refine ⟨fun e =>
    match e with
    | SbEvent.ry => 0
    | SbEvent.rx => 0
    | SbEvent.wx => 1
    | SbEvent.wy => 1, ?_, ?_⟩
  · intro e1 e2 hPpo
    contradiction
  · intro e1 e2 hFr
    rcases hFr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact Nat.zero_lt_one

/-- Theorem 4b (`riscv_corrected_leading_fence_forbids_weak_sb`): Under the
consistent Table A.6 leading-fence scheme (`fence rw,rw; lw; fence r,rw`), the
weak outcome `(r0 = 0, r1 = 0)` is impossible. -/
theorem riscv_corrected_leading_fence_forbids_weak_sb :
    ¬ SbWeakOutcomeAllowed (riscvSbPpo RiscvScScheme.tableA6Leading) := by
  intro ⟨tau, hPpo, hFr⟩
  have h1 : tau SbEvent.wx < tau SbEvent.ry :=
    hPpo SbEvent.wx SbEvent.ry (Or.inl ⟨rfl, rfl⟩)
  have h2 : tau SbEvent.ry < tau SbEvent.wy :=
    hFr SbEvent.ry SbEvent.wy (Or.inl ⟨rfl, rfl⟩)
  have h3 : tau SbEvent.wy < tau SbEvent.rx :=
    hPpo SbEvent.wy SbEvent.rx (Or.inr ⟨rfl, rfl⟩)
  have h4 : tau SbEvent.rx < tau SbEvent.wx :=
    hFr SbEvent.rx SbEvent.wx (Or.inr ⟨rfl, rfl⟩)
  omega

/-- Theorem 4c (`riscv_psabi_trailing_fence_forbids_weak_sb`): Adding the psABI
trailing `fence rw,rw` to `store(SeqCst)` also forbids `(r0 = 0, r1 = 0)` even
when paired with Table A.7 `lw.aq` loads. -/
theorem riscv_psabi_trailing_fence_forbids_weak_sb :
    ¬ SbWeakOutcomeAllowed
        (riscvSbPpo RiscvScScheme.psAbiTrailingCompatible) := by
  intro ⟨tau, hPpo, hFr⟩
  have h1 : tau SbEvent.wx < tau SbEvent.ry :=
    hPpo SbEvent.wx SbEvent.ry (Or.inl ⟨rfl, rfl⟩)
  have h2 : tau SbEvent.ry < tau SbEvent.wy :=
    hFr SbEvent.ry SbEvent.wy (Or.inl ⟨rfl, rfl⟩)
  have h3 : tau SbEvent.wy < tau SbEvent.rx :=
    hPpo SbEvent.wy SbEvent.rx (Or.inr ⟨rfl, rfl⟩)
  have h4 : tau SbEvent.rx < tau SbEvent.wx :=
    hFr SbEvent.rx SbEvent.wx (Or.inr ⟨rfl, rfl⟩)
  omega

/-- AArch64 instruction classes from `weakmemory/imm/src/hardware/Arm.v:45-47`
and `herdtools7/herd/libdir/aarch64hwreqs.cat:128-138`:
- `stlr` (`L`): Store-Release (`STLR`)
- `ldapr` (`Q`): Load-AcquirePC (`LDAPR` in ARMv8.3-A `FEAT_LRCPC`)
- `ldar` (`A`): Load-Acquire (`LDAR`). -/
inductive ArmLoadKind where
  | ldapr_Q : ArmLoadKind
  | ldar_A : ArmLoadKind
  deriving DecidableEq, Repr

/-- In `Arm.v:70-75`, Barrier-Ordered-Before (`bob`) includes `[L]; sb; [A]`
(`STLR` followed by `LDAR`), but omits `[L]; sb; [Q]` (`STLR` followed by
`LDAPR`). -/
def aarch64SbBob (loadKind : ArmLoadKind) (e1 e2 : SbEvent) : Prop :=
  match loadKind with
  | ArmLoadKind.ldapr_Q => False
  | ArmLoadKind.ldar_A =>
      (e1 = SbEvent.wx ∧ e2 = SbEvent.ry) ∨
      (e1 = SbEvent.wy ∧ e2 = SbEvent.rx)

/-- Theorem 4d (`aarch64_stlr_ldapr_allows_weak_sb` &
`aarch64_stlr_ldar_forbids_weak_sb`): Lowering `SeqCst` loads to `LDAPR` (`Q`)
allows the forbidden `(r0 = 0, r1 = 0)` Store-Buffering outcome when paired
with `STLR` (`L`), whereas lowering `SeqCst` loads to `LDAR` (`A`) forbids it. -/
theorem aarch64_stlr_ldapr_vs_ldar_sb :
    SbWeakOutcomeAllowed (aarch64SbBob ArmLoadKind.ldapr_Q) ∧
    ¬ SbWeakOutcomeAllowed (aarch64SbBob ArmLoadKind.ldar_A) := by
  constructor
  · refine ⟨fun e =>
      match e with
      | SbEvent.ry => 0
      | SbEvent.rx => 0
      | SbEvent.wx => 1
      | SbEvent.wy => 1, ?_, ?_⟩
    · intro e1 e2 hBob
      contradiction
    · intro e1 e2 hFr
      rcases hFr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact Nat.zero_lt_one
  · intro ⟨tau, hBob, hFr⟩
    have h1 : tau SbEvent.wx < tau SbEvent.ry :=
      hBob SbEvent.wx SbEvent.ry (Or.inl ⟨rfl, rfl⟩)
    have h2 : tau SbEvent.ry < tau SbEvent.wy :=
      hFr SbEvent.ry SbEvent.wy (Or.inl ⟨rfl, rfl⟩)
    have h3 : tau SbEvent.wy < tau SbEvent.rx :=
      hBob SbEvent.wy SbEvent.rx (Or.inr ⟨rfl, rfl⟩)
    have h4 : tau SbEvent.rx < tau SbEvent.wx :=
      hFr SbEvent.rx SbEvent.wx (Or.inr ⟨rfl, rfl⟩)
    omega

-- ============================================================================
-- Part 5: Bare-Metal Startup (`_start`, `linker.ld`) & ELF Relocations
-- ============================================================================

/-- Declarative linker script layout specification (`LinkerLayoutSpec`) for a
bare-metal image with Flash LMA (`.data` load image) and SRAM VMA (`.data`,
`.bss`, and downward-growing `.stack`). -/
structure LinkerLayoutSpec where
  dataLmaStart : Nat
  dataVmaStart : Nat
  dataSize : Nat
  bssVmaStart : Nat
  bssSize : Nat
  stackBottom : Nat
  stackTop : Nat
  disjointLmaData : dataLmaStart + dataSize ≤ dataVmaStart
  disjointDataBss : dataVmaStart + dataSize ≤ bssVmaStart
  disjointBssStack : bssVmaStart + bssSize ≤ stackBottom
  validStackRange : stackBottom ≤ stackTop

/-- Bare-metal `_start` initialization semantics: copies `.data` of length
`L.dataSize` from Flash LMA (`L.dataLmaStart`) to SRAM VMA (`L.dataVmaStart`),
zeroes `.bss` of length `L.bssSize` at `L.bssVmaStart`, leaves all other
addresses (including Flash `.text`/`.rodata` and `MMIO`) unchanged, and sets
`sp := L.stackTop`. -/
def execStartStub (L : LinkerLayoutSpec) (flashRam : Nat → UInt8) :
    Phase4FlatHwState :=
  { ram := fun addr =>
      if L.dataVmaStart ≤ addr ∧ addr < L.dataVmaStart + L.dataSize then
        flashRam (L.dataLmaStart + (addr - L.dataVmaStart))
      else if L.bssVmaStart ≤ addr ∧ addr < L.bssVmaStart + L.bssSize then
        0
      else
        flashRam addr,
    sp := L.stackTop,
    stackTop := L.stackTop,
    stackBudget := L.stackTop - L.stackBottom }

/-- The Rust entry invariant expected by `MirSemantics` at the entry of `main`:
1. Every offset `ofs < L.dataSize` in `.data` VMA contains its initial Flash LMA
   byte `flashRam (L.dataLmaStart + ofs)`.
2. Every offset `ofs < L.bssSize` in `.bss` VMA contains `0`.
3. Every Flash/RODATA address `addr < L.dataLmaStart + L.dataSize` is
   preserved unchanged.
4. The hardware stack pointer `sp` is initialized to `L.stackTop` above
   `L.bssVmaStart + L.bssSize`. -/
def RustEntryInvariant (L : LinkerLayoutSpec) (flashRam : Nat → UInt8)
    (s : Phase4FlatHwState) : Prop :=
  (∀ ofs, ofs < L.dataSize →
    s.ram (L.dataVmaStart + ofs) = flashRam (L.dataLmaStart + ofs)) ∧
  (∀ ofs, ofs < L.bssSize →
    s.ram (L.bssVmaStart + ofs) = 0) ∧
  (∀ addr, addr < L.dataLmaStart + L.dataSize →
    s.ram addr = flashRam addr) ∧
  s.sp = L.stackTop ∧
  L.bssVmaStart + L.bssSize ≤ s.sp - s.stackBudget

/-- Theorem 5a (`startStub_establishes_rust_entry_invariant`): Executing the
bare-metal `_start` stub under any valid `LinkerLayoutSpec` establishes
`RustEntryInvariant`. -/
theorem startStub_establishes_rust_entry_invariant (L : LinkerLayoutSpec)
    (flashRam : Nat → UInt8) :
    RustEntryInvariant L flashRam (execStartStub L flashRam) := by
  have h1 := L.disjointLmaData
  have h2 := L.disjointDataBss
  have h3 := L.disjointBssStack
  have h4 := L.validStackRange
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · intro ofs hOfs
    unfold execStartStub
    simp only
    have hInData :
        L.dataVmaStart ≤ L.dataVmaStart + ofs ∧
        L.dataVmaStart + ofs < L.dataVmaStart + L.dataSize := by omega
    have hSub : L.dataVmaStart + ofs - L.dataVmaStart = ofs := by omega
    simp only [hInData, and_self, ↓reduceIte, hSub]
  · intro ofs hOfs
    unfold execStartStub
    simp only
    have hNotData :
        ¬ (L.dataVmaStart ≤ L.bssVmaStart + ofs ∧
           L.bssVmaStart + ofs < L.dataVmaStart + L.dataSize) := by omega
    have hInBss :
        L.bssVmaStart ≤ L.bssVmaStart + ofs ∧
        L.bssVmaStart + ofs < L.bssVmaStart + L.bssSize := by omega
    simp only [hNotData, ↓reduceIte, hInBss, and_self]
  · intro addr hAddr
    unfold execStartStub
    simp only
    have hNotData :
        ¬ (L.dataVmaStart ≤ addr ∧
           addr < L.dataVmaStart + L.dataSize) := by omega
    have hNotBss :
        ¬ (L.bssVmaStart ≤ addr ∧
           addr < L.bssVmaStart + L.bssSize) := by omega
    simp only [hNotData, hNotBss, ↓reduceIte]
  · unfold execStartStub
    simp only
    omega

/-- Static PC-relative ELF relocation resolver (`S + A - P` over signed 64-bit
integers, modeling `R_X86_64_PC32` and non-relaxed `R_RISCV_PCREL_HI20` +
`R_RISCV_PCREL_LO12_I` displacement calculation). -/
def computePcRelDisplacement (symbolVma addend pc : Int) : Int :=
  symbolVma + addend - pc

/-- Runtime effective address computation (`PC + displacement`). -/
def evalPcRelAddress (pc displacement : Int) : Int :=
  pc + displacement

/-- Theorem 5b (`elf_pcrel_relocation_exact`): Evaluating a PC-relative address
at instruction address `pc` with static ELF relocation displacement
`computePcRelDisplacement symbolVma addend pc` recovers the exact target address
`symbolVma + addend`. -/
theorem elf_pcrel_relocation_exact (symbolVma addend pc : Int) :
    evalPcRelAddress pc (computePcRelDisplacement symbolVma addend pc) =
      symbolVma + addend := by
  unfold evalPcRelAddress computePcRelDisplacement
  omega

-- ============================================================================
-- Axiom Footprint Audit (Zero `sorryAx`, Zero `Lean.ofReduceBool`)
-- ============================================================================

/--
info: 'Track7Probe.withAddr_toFlatAddr_roundtrip' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms withAddr_toFlatAddr_roundtrip

/--
info: 'Track7Probe.phase3_to_phase4_load_preserved' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms phase3_to_phase4_load_preserved

/--
info: 'Track7Probe.stack_overflow_impossible_under_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms stack_overflow_impossible_under_budget

/--
info: 'Track7Probe.spillPass_modifies_single_trace' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms spillPass_modifies_single_trace

/--
info: 'Track7Probe.spillPass_preserves_constantTime' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms spillPass_preserves_constantTime

/--
info: 'Track7Probe.selectOpt_violates_constantTime' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms selectOpt_violates_constantTime

/--
info: 'Track7Probe.reorder_without_compiler_fence_sound_sequentially' does not depend on any axioms
-/
#guard_msgs in
#print axioms reorder_without_compiler_fence_sound_sequentially

/--
info: 'Track7Probe.reorder_without_compiler_fence_violates_isr_safety' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms reorder_without_compiler_fence_violates_isr_safety

/--
info: 'Track7Probe.preserving_compiler_fence_guarantees_isr_safety' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms preserving_compiler_fence_guarantees_isr_safety

/--
info: 'Track7Probe.riscv_mixed_tableA6_A7_allows_weak_sb' does not depend on any axioms
-/
#guard_msgs in
#print axioms riscv_mixed_tableA6_A7_allows_weak_sb

/--
info: 'Track7Probe.riscv_corrected_leading_fence_forbids_weak_sb' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms riscv_corrected_leading_fence_forbids_weak_sb

/--
info: 'Track7Probe.riscv_psabi_trailing_fence_forbids_weak_sb' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms riscv_psabi_trailing_fence_forbids_weak_sb

/--
info: 'Track7Probe.aarch64_stlr_ldapr_vs_ldar_sb' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms aarch64_stlr_ldapr_vs_ldar_sb

/--
info: 'Track7Probe.startStub_establishes_rust_entry_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms startStub_establishes_rust_entry_invariant

/--
info: 'Track7Probe.elf_pcrel_relocation_exact' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms elf_pcrel_relocation_exact

end Track7Probe
