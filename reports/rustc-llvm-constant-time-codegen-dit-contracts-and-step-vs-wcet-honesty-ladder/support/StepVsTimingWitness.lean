/-!
# Architectural Step-Count, Storage-NI, Post-Link CT, and Microarchitectural Timing-NI Separation Witness

Self-contained `Type 0` Lean 4 (`v4.34.1`) witness establishing five results for the
Stage 0 -> Stage 1 -> Stage 2 verification honesty ladder:
1. `retired_step_parity_does_not_imply_wcet_or_timing_ni`:
   Identical retired instruction counts and identical architectural outputs do not bound
   microarchitectural cycles (WCET) and do not imply timing noninterference.
2. `storage_ni_and_step_parity_do_not_imply_cache_timing_ni`:
   Storage-channel noninterference + retired-step parity do not imply cache-line or
   cycle-timing noninterference.
3. `mir_ct_broken_by_single_trace_refining_lowering`:
   A single-trace functionally sound MIR-to-ISA lowering pass can break MIR-level
   constant-time by introducing a secret-dependent branch / memory load.
4. `dit_enabled_without_allowlist_still_leaks_div`:
   Setting hardware `DIT`/`DOITM` without an opcode allowlist excluding variable-latency
   `DIV`/subnormal-FP instructions still violates cycle-timing noninterference.
5. `postlink_ct_under_dit_and_uarch_reset_implies_timing_ni`:
   Combining post-link `CtProduct` trace equality, a `DIT`/`DOITM`/`Zkt` opcode allowlist,
   `ditEnabled = true`, and microarchitectural isolation (`uarchReset`) soundly implies
   microarchitectural cycle-timing noninterference.

Zero external imports, zero `sorry`, zero extra axioms.
-/

namespace StepVsTimingHonestyLadder

/-- Abstract input split into public and secret components. -/
structure Input : Type 0 where
  pub : Nat
  sec : Bool
deriving DecidableEq, Repr

/-- Two inputs agree on all public data. -/
def LowEq (x y : Input) : Prop := x.pub = y.pub

/-- Machine opcode classes relevant to hardware data-independent timing contracts. -/
inductive Opcode : Type 0 where
  | aluConst      -- ADD/SUB/XOR/AND/CMOV/CSEL/CZERO (in DIT/DOITM/Zkt allowlist)
  | loadAddr      -- Memory load whose latency depends on cache state & address
  | condBranch    -- Conditional branch whose target leaks over PC/BTB
  | divVarTime    -- DIV/IDIV/UDIV/SDIV (explicitly excluded from DIT/DOITM/Zkt)
  | fpSubnormal   -- IEEE-754 FP without FTZ/DAZ (excluded from DOITM/Zkt)
deriving DecidableEq, Repr

/-- Opcode allowlist admitted by hardware `PSTATE.DIT` / `DOITM` / `Zkt` contracts. -/
def Opcode.isDitSafe : Opcode → Bool
  | .aluConst   => true
  | .loadAddr   => true
  | .condBranch => true
  | .divVarTime => false
  | .fpSubnormal => false

/-- One architectural retired instruction step with its architectural observation
    and operand-dependent / microarchitectural state-dependent cycle latency. -/
structure StepEvent : Type 0 where
  pc       : Nat
  op       : Opcode
  memAddr  : Option Nat
  operand  : Nat
deriving DecidableEq, Repr

/-- Post-link architectural constant-time projection (`CtProduct` observation):
    PC + opcode + memory address (data-value blind). -/
structure ArchCtObs : Type 0 where
  pc      : Nat
  op      : Opcode
  memAddr : Option Nat
deriving DecidableEq, Repr

def StepEvent.toArchCtObs (e : StepEvent) : ArchCtObs :=
  { pc := e.pc, op := e.op, memAddr := e.memAddr }

/-- Microarchitectural state visible to timing (e.g., cache line residency,
    prior-domain microarchitectural pollution). -/
structure UarchState : Type 0 where
  /-- Whether address `a` is hot in L1D (true = 1 cycle, false = 40 cycles). -/
  cacheHot : Nat → Bool
  /-- Whether hardware `PSTATE.DIT` / `DOITM` / `Zkt` mode is active. -/
  ditEnabled : Bool

/-- Cycle latency of a single retired instruction under a given microarchitectural state.
    Notice:
    - Under `ditEnabled = true`, `aluConst` and `condBranch` take 1 cycle independent of `operand`.
    - `divVarTime` and `fpSubnormal` remain operand-dependent EVEN WHEN `ditEnabled = true`
      (modeling universal ISA exemptions for `DIV`/`UDIV`/`SDIV` and subnormal FP).
    - `loadAddr` latency depends on `u.cacheHot addr` (1 cycle hit vs. 40 cycles miss). -/
def stepCycles (u : UarchState) (e : StepEvent) : Nat :=
  match e.op with
  | .aluConst =>
      if u.ditEnabled then 1 else (if e.operand == 0 then 1 else 3)
  | .condBranch => 1
  | .loadAddr =>
      match e.memAddr with
      | some a => if u.cacheHot a then 1 else 40
      | none   => 1
  | .divVarTime =>
      -- Exempt from PSTATE.DIT / DOITM / Zkt: latency depends on operand magnitude
      if e.operand == 0 then 4 else 44
  | .fpSubnormal =>
      -- Subnormal assist penalty regardless of DIT/DOITM
      if e.operand == 0 then 3 else 120

/-- Total microarchitectural cycle count of an execution trace under fixed cache-state model. -/
def traceCycles (u : UarchState) : List StepEvent → Nat
  | []      => 0
  | e :: es => stepCycles u e + traceCycles u es

/-- A compiled program model returning final architectural storage, public output,
    and the retired instruction trace. -/
structure ProgModel : Type 0 where
  finalStorage : Input → Nat
  trace        : Input → List StepEvent

/-- Rung (a): Architectural retired-instruction count. -/
def retiredSteps (p : ProgModel) (x : Input) : Nat :=
  (p.trace x).length

/-- Rung (a) property: Uniform retired step bound `≤ B` (and exact step parity). -/
def HasRetiredStepParity (p : ProgModel) : Prop :=
  ∀ x y : Input, LowEq x y → retiredSteps p x = retiredSteps p y

/-- Rung (b) property: Storage-channel-only noninterference (`finalStorage` depends only on `pub`). -/
def SatisfiesStorageNI (p : ProgModel) : Prop :=
  ∀ x y : Input, LowEq x y → p.finalStorage x = p.finalStorage y

/-- Rung (c) property: Post-link architectural constant-time (`CtProduct`: identical PC, opcode,
    and memory-address trace across public-equivalent inputs). -/
def SatisfiesPostLinkArchCT (p : ProgModel) : Prop :=
  ∀ x y : Input, LowEq x y →
    (p.trace x).map StepEvent.toArchCtObs = (p.trace y).map StepEvent.toArchCtObs

/-- Opcode allowlist discipline: every emitted instruction in `p` is `DIT`/`DOITM`/`Zkt`-safe. -/
def AllOpcodesDitSafe (p : ProgModel) : Prop :=
  ∀ (x : Input) (e : StepEvent), e ∈ p.trace x → e.op.isDitSafe = true

/-- Rung (d) property: Microarchitectural cycle-timing noninterference given
    an isolated/reset initial microarchitectural state `u`. -/
def SatisfiesCycleTimingNI (u : UarchState) (p : ProgModel) : Prop :=
  ∀ x y : Input, LowEq x y → traceCycles u (p.trace x) = traceCycles u (p.trace y)

-- ============================================================================
-- Witness 1 & 2: Retired-Step Parity + Storage NI != WCET / Cache-Timing NI
-- ============================================================================

/-- Concrete program that computes the same public result (`pub + 1`) in exactly 3 retired
    instructions for every input, but loads cache line 0 when `sec = false` and cache line 1
    when `sec = true` (modeling a secret-indexed LUT or secret pointer select). -/
def progCacheLeak : ProgModel where
  finalStorage := fun x => x.pub + 1
  trace := fun x =>
    [ { pc := 0, op := .aluConst, memAddr := none, operand := x.pub }
    , { pc := 4, op := .loadAddr, memAddr := some (if x.sec then 64 else 0), operand := 0 }
    , { pc := 8, op := .aluConst, memAddr := none, operand := 1 }
    ]

/-- Microarchitectural state where line 0 is warm in L1D and line 64 misses to DRAM. -/
def uarchLine0Hot : UarchState where
  cacheHot   := fun addr => addr == 0
  ditEnabled := true

theorem retired_step_parity_does_not_imply_wcet_or_timing_ni :
    HasRetiredStepParity progCacheLeak ∧
    (∀ x, retiredSteps progCacheLeak x = 3) ∧
    ¬ SatisfiesCycleTimingNI uarchLine0Hot progCacheLeak := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y _
    rfl
  · intro x
    rfl
  · intro hni
    have hlow : LowEq { pub := 7, sec := false } { pub := 7, sec := true } := rfl
    have heq := hni { pub := 7, sec := false } { pub := 7, sec := true } hlow
    -- 3 cycles (L1 hit) vs 42 cycles (L1 miss)
    change 3 = 42 at heq
    cases heq

theorem storage_ni_and_step_parity_do_not_imply_cache_timing_ni :
    SatisfiesStorageNI progCacheLeak ∧
    HasRetiredStepParity progCacheLeak ∧
    ¬ SatisfiesPostLinkArchCT progCacheLeak ∧
    ¬ SatisfiesCycleTimingNI uarchLine0Hot progCacheLeak := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hlow
    exact congrArg (· + 1) hlow
  · intro x y _
    rfl
  · intro hct
    have hlow : LowEq { pub := 7, sec := false } { pub := 7, sec := true } := rfl
    have heq := hct { pub := 7, sec := false } { pub := 7, sec := true } hlow
    cases heq
  · exact retired_step_parity_does_not_imply_wcet_or_timing_ni.2.2

-- ============================================================================
-- Witness 3: MIR-Level CT Broken by a Functionally Sound Lowering Pass
-- ============================================================================

/-- Source MIR program: branchless wrapping-mask select loading both arms unconditionally. -/
def progMirBranchless : ProgModel where
  finalStorage := fun x => if x.sec then x.pub * 3 + 1 else x.pub
  trace := fun x =>
    [ { pc := 0, op := .loadAddr, memAddr := some 0,  operand := 0 }
    , { pc := 4, op := .loadAddr, memAddr := some 64, operand := 0 }
    , { pc := 8, op := .aluConst, memAddr := none,    operand := x.pub }
    ]

/-- Lowered target binary after LLVM `InstCombine + SelectOptimize` (mirroring empirical
    `ct_wrap_mask_load_arms` on `rustc 1.102.0-nightly` / LLVM 23.1.5): functionally identical
    output, but sinks loads behind a secret-dependent branch `jne`. -/
def progLlvmBroken : ProgModel where
  finalStorage := fun x => if x.sec then x.pub * 3 + 1 else x.pub
  trace := fun x =>
    if x.sec then
      [ { pc := 0,  op := .condBranch, memAddr := none,    operand := 1 }
      , { pc := 12, op := .loadAddr,   memAddr := some 0,  operand := 0 }
      , { pc := 16, op := .aluConst,   memAddr := none,    operand := x.pub }
      ]
    else
      [ { pc := 0,  op := .condBranch, memAddr := none,    operand := 0 }
      , { pc := 4,  op := .loadAddr,   memAddr := some 64, operand := 0 }
      ]

theorem mir_ct_broken_by_single_trace_refining_lowering :
    SatisfiesPostLinkArchCT progMirBranchless ∧
    (∀ x, progLlvmBroken.finalStorage x = progMirBranchless.finalStorage x) ∧
    ¬ SatisfiesPostLinkArchCT progLlvmBroken := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y _
    rfl
  · intro x
    rfl
  · intro hct
    have hlow : LowEq { pub := 5, sec := false } { pub := 5, sec := true } := rfl
    have heq := hct { pub := 5, sec := false } { pub := 5, sec := true } hlow
    cases heq

-- ============================================================================
-- Witness 4: DIT/DOITM Enabled WITHOUT Opcode Allowlist Still Leaks via DIV
-- ============================================================================

/-- Program that passes PC+address `PostLinkArchCT` (constant PC and no memory ops),
    yet executes a variable-latency `DIV` with a secret operand (`KyberSlash` class). -/
def progDivUnderDit : ProgModel where
  finalStorage := fun x => x.pub
  trace := fun x =>
    [ { pc := 0, op := .divVarTime, memAddr := none, operand := if x.sec then 1 else 0 } ]

theorem dit_enabled_without_allowlist_still_leaks_div :
    SatisfiesPostLinkArchCT progDivUnderDit ∧
    uarchLine0Hot.ditEnabled = true ∧
    ¬ AllOpcodesDitSafe progDivUnderDit ∧
    ¬ SatisfiesCycleTimingNI uarchLine0Hot progDivUnderDit := by
  refine ⟨?_, rfl, ?_, ?_⟩
  · intro x y _
    rfl
  · intro hsafe
    have hmem : { pc := 0, op := Opcode.divVarTime, memAddr := none, operand := 0 }
        ∈ progDivUnderDit.trace { pub := 0, sec := false } := List.Mem.head _
    have h := hsafe { pub := 0, sec := false } _ hmem
    cases h
  · intro hni
    have hlow : LowEq { pub := 0, sec := false } { pub := 0, sec := true } := rfl
    have heq := hni { pub := 0, sec := false } { pub := 0, sec := true } hlow
    -- 4 cycles vs 44 cycles despite PSTATE.DIT = 1
    change 4 = 44 at heq
    cases heq

-- ============================================================================
-- Witness 5 (Positive Soundness): Post-Link Arch-CT + DIT Allowlist + Uarch Reset => Cycle Timing NI
-- ============================================================================

/-- Under `ditEnabled = true`, any `DIT`-safe instruction's cycle latency depends SOLELY
    on its `ArchCtObs` (PC, opcode, memory address) and the isolated microarchitectural state `u`. -/
theorem stepCycles_eq_of_dit_safe_and_obs_eq
    (u : UarchState) (hdit : u.ditEnabled = true)
    (e1 e2 : StepEvent)
    (hsafe : e1.op.isDitSafe = true)
    (hobs : e1.toArchCtObs = e2.toArchCtObs) :
    stepCycles u e1 = stepCycles u e2 := by
  cases e1 with | mk pc1 op1 addr1 val1 =>
  cases e2 with | mk pc2 op2 addr2 val2 =>
  cases hobs
  cases op1 with
  | aluConst =>
      simp [stepCycles, hdit]
  | loadAddr => rfl
  | condBranch => rfl
  | divVarTime => cases hsafe
  | fpSubnormal => cases hsafe

theorem traceCycles_eq_of_dit_safe_and_obs_eq
    (u : UarchState) (hdit : u.ditEnabled = true)
    (t1 t2 : List StepEvent)
    (hsafe : ∀ e, e ∈ t1 → e.op.isDitSafe = true)
    (hobs : t1.map StepEvent.toArchCtObs = t2.map StepEvent.toArchCtObs) :
    traceCycles u t1 = traceCycles u t2 := by
  induction t1 generalizing t2 with
  | nil =>
      cases t2 with
      | nil => rfl
      | cons _ _ => cases hobs
  | cons e1 rest1 ih =>
      cases t2 with
      | nil => cases hobs
      | cons e2 rest2 =>
          have hpair := List.cons.inj hobs
          have h1 := stepCycles_eq_of_dit_safe_and_obs_eq u hdit e1 e2
            (hsafe e1 (List.Mem.head _)) hpair.1
          have h2 := ih rest2 (fun e hm => hsafe e (List.Mem.tail _ hm)) hpair.2
          simp [traceCycles, h1, h2]

/-- Positive Honesty-Ladder Upgrade Theorem:
    Post-link `CtProduct` trace equality + `DIT`/`DOITM`/`Zkt` opcode allowlist +
    hardware `ditEnabled = true` + fixed/reset initial microarchitectural state `u`
    soundly imply microarchitectural cycle-timing noninterference. -/
theorem postlink_ct_under_dit_and_uarch_reset_implies_timing_ni
    (u : UarchState) (p : ProgModel)
    (hdit  : u.ditEnabled = true)
    (hct   : SatisfiesPostLinkArchCT p)
    (hsafe : AllOpcodesDitSafe p) :
    SatisfiesCycleTimingNI u p := by
  intro x y hlow
  exact traceCycles_eq_of_dit_safe_and_obs_eq u hdit (p.trace x) (p.trace y)
    (hsafe x) (hct x y hlow)

#print axioms retired_step_parity_does_not_imply_wcet_or_timing_ni
#print axioms storage_ni_and_step_parity_do_not_imply_cache_timing_ni
#print axioms mir_ct_broken_by_single_trace_refining_lowering
#print axioms dit_enabled_without_allowlist_still_leaks_div
#print axioms postlink_ct_under_dit_and_uarch_reset_implies_timing_ni

end StepVsTimingHonestyLadder
