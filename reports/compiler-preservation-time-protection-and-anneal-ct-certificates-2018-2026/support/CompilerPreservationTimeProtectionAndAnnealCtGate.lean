/-
  CompilerPreservationTimeProtectionAndAnnealCtGate.lean
  ------------------------------------------------------
  Lean 4.34.1 Mechanization of:
  1. Compiler Constant-Time & Secret-Erasure Preservation Breakdowns and
     Two Architectural Solutions (`CompCert-CT` / Besson et al. Lockstep Simulation
     vs. Anneal / `Jasmin` / `Kraken` Consumer-Bound Machine-Byte Certificates):
     - `cmov_to_branch_lowering_breaks_ct`
       (Simon, Chisnall & Anderson EuroS&P 2018; Schneider et al. 2024/2025)
     - `dead_store_elimination_breaks_secret_scrubbing`
       (Simon et al. EuroS&P 2018; Besson, Dang & Jensen CSF 2019 `BSopdead`)
     - `secret_register_spill_breaks_memory_erasure`
       (Barthe et al. `CompCert-CT` POPL 2020; Besson, Dang & Jensen CSF 2019 `Allocation` spill)
     - `ct_lockstep_simulation_preserves_ct_and_scrubbing`
       (`CompCert-CT` POPL 2020 + Besson et al. CSF 2019 IFP relational simulation)
     - `consumer_bound_machine_byte_ct_cert_defeats_bad_compiler`
       (Anneal / `Jasmin` / `Kraken` consumer-bound target-byte checker rejecting all 3 compiler bugs)

  2. Kernel Context-Switch & Domain-Exit Boundary: `seL4` Time Protection
     (Ge, Yarom, Chothia & Heiser, EuroSys 2019, DOI 10.1145/3302424.3303976):
     - `isolated_ct_insufficient_across_context_switch`
       (Two extensions `extA`, `extB` each satisfying `IsolatedCT` in isolation leak `extA`'s
        secret when composed sequentially across a naive context switch without `TimeProtection`)
     - `unpadded_cache_flush_leaks_via_clock`
       (Ge et al. EuroSys 2019 §4.4: even when caches/registers/stack are flushed on switch,
        unpadded dirty-cache flush latency leaks `extA`'s secret via `cycleClock`)
     - `sel4_time_protection_compositional_noninterference`
       (Enforcing `sel4TimeProtectedSwitch` — register/stack zeroization + L1/BPU flush +
        deterministic worst-case cycle padding — restores compositional multi-extension noninterference)
     - `sel4_time_protection_schedule_noninterference`
       (Inductive multi-extension schedule composition across arbitrary extension sequences)

  3. Anneal's 7-Obligation Consumer-Bound Side-Channel-Free Ring-0 Admission Gate
     (`ob1_byteBinding` .. `ob6_boundedFuelTermination` + `ob7_sideChannelFreedom` =
      `ob7a_archConstantTime && ob7b_speculativeConstantTime &&
       ob7c_secretExitAndSpillScrubbing && ob7d_secretIndependentFuelTiming`):
     - `anneal_ring0_ct_extension_admission_soundness` (7-Obligation Sufficiency)
     - `drop_ob7a_unsound`, `drop_ob7b_unsound`, `drop_ob7c_unsound`, `drop_ob7d_unsound`
     - `anneal_ob7_four_subobligations_necessary` (4-Way Non-Redundancy of `ob7a`–`ob7d`)

  4. Mid-Execution Preemption Window vs. Bounded Non-Preemptible & ISR-Scrubbed `Time Protection`
     (Ge et al. EuroSys 2019 §4.5):
     - `mid_execution_preemption_bypasses_exit_scrub`
     - `time_protected_isr_or_nonpreemptible_fuel_soundness`

  Toolchain: Lean 4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52)
  Axiom Policy: Zero axioms (`0 sorryAx`, `0 Classical.choice`, `0 Lean.ofReduceBool`).
-/

namespace CompilerPreservationTimeProtectionAndAnnealCtGate

/-! ## Section 0: Constructive Equality & Boolean Helpers (Axiom-Free) -/

/-- Constructive boolean equality on `Nat` avoiding `Classical.choice` and `propext`. -/
def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | n + 1, m + 1 => natEq n m

theorem natEq_refl (n : Nat) : natEq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natEq_eq {n m : Nat} (h : natEq n m = true) : n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => rfl
    | succ _ => nomatch h
  | succ k ih =>
    cases m with
    | zero => nomatch h
    | succ j =>
      exact congrArg Nat.succ (ih h)

/-- Constructive `≤` check on `Nat`. -/
def natLe : Nat → Nat → Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | n + 1, m + 1 => natLe n m

theorem natLe_refl (n : Nat) : natLe n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

/-- Constructive `<` check on `Nat`. -/
def natLt (n m : Nat) : Bool := natLe (n + 1) m

/-- Constructive equality on `Bool`. -/
def boolEq : Bool → Bool → Bool
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true

theorem boolEq_eq {a b : Bool} (h : boolEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | nomatch h

theorem band_eq_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a with
  | false => nomatch h
  | true =>
    cases b with
    | false => nomatch h
    | true => exact ⟨rfl, rfl⟩

/-- Constructive equality on `List Nat`. -/
def natListEq : List Nat → List Nat → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys => natEq x y && natListEq xs ys

theorem natListEq_refl (xs : List Nat) : natListEq xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp [natListEq]
    exact Eq.trans (congrArg (fun b => b && natListEq rest rest) (natEq_refl x)) ih

theorem natListEq_eq {xs ys : List Nat} (h : natListEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => nomatch h
  | cons x rest ih =>
    cases ys with
    | nil => nomatch h
    | cons y restY =>
      dsimp [natListEq] at h
      have ⟨hxy, hrest⟩ := band_eq_true h
      have hx : x = y := natEq_eq hxy
      have hr : rest = restY := ih hrest
      exact hx ▸ hr ▸ rfl

/-!
## Section 1: Why Source/Bytecode CT Certificates Are Invalidated by
Unverified Backend/JIT Passes & How `CompCert-CT` / `Jasmin` / Target-Byte Certificates Solve It

We formalize a concrete source/IR and target machine-code semantics capturing:
1. Architectural return values (`retVal : Nat`),
2. Leakage observation traces (`obsTrace : List ObsEvent`: branch direction & memory address traces),
3. Post-return residual secrets in the shared kernel stack (`residualStackSec : Nat`) and
   scratch registers (`residualRegSec : Nat`).
-/

/-- Side-channel observation event emitted during instruction execution. -/
inductive ObsEvent where
  | pcStep (pc : Nat)
  | branchTaken (condBit : Bool)
  | memAccess (addr : Nat)
  | varLatencyOp (operandVal : Nat)
  deriving DecidableEq, Repr

/-- Extension invocation input state in Ring 0. -/
structure ExtInputState where
  pubIn : Nat     -- Public argument (e.g., packet length / public selector)
  secIn : Nat     -- Secret input (e.g., cryptographic key / capability secret)
  pubVal1 : Nat   -- Public value 1
  pubVal2 : Nat   -- Public value 2
  deriving DecidableEq, Repr

/-- Extension execution outcome including return value, leakage trace, and residual state. -/
structure ExtOutcome where
  retVal : Nat
  obsTrace : List ObsEvent
  residualStackSec : Nat
  residualRegSec : Nat
  deriving DecidableEq, Repr

/--
Unified IR / machine operations for modeling compiler transformations between
source/bytecode extensions and target machine-code extensions:
- `cmovSelectSec`: branchless constant-time select `(if secIn != 0 then pubVal1 else pubVal2)` into `retReg`,
  emitting only `ObsEvent.pcStep`.
- `branchSelectSec`: lowered diamond conditional branch on `secIn != 0`, emitting
  `ObsEvent.branchTaken ( !natEq secIn 0 )` into the PC/branch trace.
- `storeSecretToStack (slot : Nat)`: writes `secIn` into stack slot `slot` (public offset `slot`).
- `scrubStackSlot (slot : Nat)`: overwrites stack slot `slot` with `0` (dead-store target before `ret`).
- `computeInSecretReg`: computes using `secIn` in a scratch register `r_sec`.
- `scrubSecretReg`: overwrites scratch register `r_sec := 0`.
- `spillSecretRegToStack (slot : Nat)`: compiler-inserted register spill of `r_sec` to `stack[slot]`.
- `reloadSpilledSecretReg (slot : Nat)`: compiler-inserted reload from `stack[slot]`.
- `ret`: returns `retReg`.
-/
inductive CompilerIrInstr where
  | cmovSelectSec
  | branchSelectSec
  | storeSecretToStack (slot : Nat)
  | scrubStackSlot (slot : Nat)
  | computeInSecretReg
  | scrubSecretReg
  | spillSecretRegToStack (slot : Nat)
  | reloadSpilledSecretReg (slot : Nat)
  | ret
  deriving DecidableEq, Repr

abbrev SrcProg := List CompilerIrInstr
abbrev TgtProg := List CompilerIrInstr

/-- Internal execution state while stepping a `CompilerIrInstr` sequence. -/
structure IrExecState where
  pc : Nat
  retReg : Nat
  secReg : Nat
  stackSlot0 : Nat
  trace : List ObsEvent
  halted : Bool
  deriving DecidableEq, Repr

/-- Step a single instruction in `CompilerIrInstr`. -/
def stepIrInstr (inp : ExtInputState) (st : IrExecState) (instr : CompilerIrInstr) : IrExecState :=
  if st.halted then st
  else
    match instr with
    | .cmovSelectSec =>
      let chosen := if natEq inp.secIn 0 then inp.pubVal2 else inp.pubVal1
      { st with
        pc := st.pc + 1
        retReg := chosen
        trace := st.trace ++ [ObsEvent.pcStep st.pc] }
    | .branchSelectSec =>
      let cond := !natEq inp.secIn 0
      let chosen := if natEq inp.secIn 0 then inp.pubVal2 else inp.pubVal1
      { st with
        pc := st.pc + 1
        retReg := chosen
        trace := st.trace ++ [ObsEvent.pcStep st.pc, ObsEvent.branchTaken cond] }
    | .storeSecretToStack slot =>
      { st with
        pc := st.pc + 1
        stackSlot0 := if natEq slot 0 then inp.secIn else st.stackSlot0
        trace := st.trace ++ [ObsEvent.pcStep st.pc, ObsEvent.memAccess slot] }
    | .scrubStackSlot slot =>
      { st with
        pc := st.pc + 1
        stackSlot0 := if natEq slot 0 then 0 else st.stackSlot0
        trace := st.trace ++ [ObsEvent.pcStep st.pc, ObsEvent.memAccess slot] }
    | .computeInSecretReg =>
      { st with
        pc := st.pc + 1
        secReg := inp.secIn
        retReg := inp.pubIn + inp.pubVal1
        trace := st.trace ++ [ObsEvent.pcStep st.pc] }
    | .scrubSecretReg =>
      { st with
        pc := st.pc + 1
        secReg := 0
        trace := st.trace ++ [ObsEvent.pcStep st.pc] }
    | .spillSecretRegToStack slot =>
      { st with
        pc := st.pc + 1
        stackSlot0 := if natEq slot 0 then st.secReg else st.stackSlot0
        trace := st.trace ++ [ObsEvent.pcStep st.pc, ObsEvent.memAccess slot] }
    | .reloadSpilledSecretReg slot =>
      { st with
        pc := st.pc + 1
        secReg := if natEq slot 0 then st.stackSlot0 else st.secReg
        trace := st.trace ++ [ObsEvent.pcStep st.pc, ObsEvent.memAccess slot] }
    | .ret =>
      { st with
        pc := st.pc + 1
        trace := st.trace ++ [ObsEvent.pcStep st.pc]
        halted := true }

def runIrProgLoop (inp : ExtInputState) : List CompilerIrInstr → IrExecState → IrExecState
  | [], st => st
  | i :: rest, st => runIrProgLoop inp rest (stepIrInstr inp st i)

def initialIrState : IrExecState :=
  { pc := 0, retReg := 0, secReg := 0, stackSlot0 := 0, trace := [], halted := false }

def runSrc (prog : SrcProg) (inp : ExtInputState) : ExtOutcome :=
  let finalSt := runIrProgLoop inp prog initialIrState
  { retVal := finalSt.retReg
    obsTrace := finalSt.trace
    residualStackSec := finalSt.stackSlot0
    residualRegSec := finalSt.secReg }

def runTgt (prog : TgtProg) (inp : ExtInputState) : ExtOutcome :=
  runSrc prog inp

/--
A source/bytecode extension satisfies Constant-Time and Post-Exit Secret Scrubbing
(`SourceCTAndScrubbed`) iff:
1. For any two inputs with equal public fields (`pubIn`, `pubVal1`, `pubVal2`),
   the observation traces are identical (`obsTrace` is secret-independent);
2. On all inputs, residual stack and scratch register secrets are scrubbed to `0` on exit.
-/
def PublicEquivInput (s₁ s₂ : ExtInputState) : Prop :=
  s₁.pubIn = s₂.pubIn ∧ s₁.pubVal1 = s₂.pubVal1 ∧ s₁.pubVal2 = s₂.pubVal2

def SourceCTAndScrubbed (prog : SrcProg) : Prop :=
  (∀ s₁ s₂ : ExtInputState, PublicEquivInput s₁ s₂ →
    (runSrc prog s₁).obsTrace = (runSrc prog s₂).obsTrace) ∧
  (∀ s : ExtInputState,
    (runSrc prog s).residualStackSec = 0 ∧ (runSrc prog s).residualRegSec = 0)

def TargetCTAndScrubbed (prog : TgtProg) : Prop :=
  (∀ s₁ s₂ : ExtInputState, PublicEquivInput s₁ s₂ →
    (runTgt prog s₁).obsTrace = (runTgt prog s₂).obsTrace) ∧
  (∀ s : ExtInputState,
    (runTgt prog s).residualStackSec = 0 ∧ (runTgt prog s).residualRegSec = 0)

/-!
### Counterexample 1: `cmov_to_branch_lowering_breaks_ct`
(Simon, Chisnall & Anderson EuroS&P 2018; Schneider et al. 2024/2025)
Rewriting branchless `cmovSelectSec` into `branchSelectSec` preserves architectural return values
on 100% of inputs while leaking `secIn != 0` into the target PC/branch trace.
-/

def P_cmov_src : SrcProg :=
  [.cmovSelectSec, .ret]

/-- Compiler optimization pass lowering `cmovSelectSec` into a diamond branch `branchSelectSec`. -/
def lowerCmovToBranch : SrcProg → TgtProg
  | [] => []
  | i :: rest =>
    let i' :=
      match i with
      | .cmovSelectSec => .branchSelectSec
      | .branchSelectSec => .branchSelectSec
      | .storeSecretToStack s => .storeSecretToStack s
      | .scrubStackSlot s => .scrubStackSlot s
      | .computeInSecretReg => .computeInSecretReg
      | .scrubSecretReg => .scrubSecretReg
      | .spillSecretRegToStack s => .spillSecretRegToStack s
      | .reloadSpilledSecretReg s => .reloadSpilledSecretReg s
      | .ret => .ret
    i' :: lowerCmovToBranch rest

theorem cmov_to_branch_lowering_breaks_ct :
    SourceCTAndScrubbed P_cmov_src ∧
    (∀ s : ExtInputState,
      (runTgt (lowerCmovToBranch P_cmov_src) s).retVal = (runSrc P_cmov_src s).retVal) ∧
    (∃ s₁ s₂ : ExtInputState,
      PublicEquivInput s₁ s₂ ∧
      (runTgt (lowerCmovToBranch P_cmov_src) s₁).obsTrace ≠
        (runTgt (lowerCmovToBranch P_cmov_src) s₂).obsTrace) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro s₁ s₂ _
      rfl
    · intro s
      exact ⟨rfl, rfl⟩
  · intro s
    rfl
  · refine ⟨{ pubIn := 1, secIn := 0, pubVal1 := 10, pubVal2 := 20 },
            { pubIn := 1, secIn := 42, pubVal1 := 10, pubVal2 := 20 },
            ⟨rfl, rfl, rfl⟩, ?_⟩
    intro hEq
    nomatch hEq

/-!
### Counterexample 2: `dead_store_elimination_breaks_secret_scrubbing`
(Simon, Chisnall & Anderson EuroS&P 2018; Besson, Dang & Jensen CSF 2019 `BSopdead`)
Eliding a post-computation secret-erasure store `scrubStackSlot 0` immediately before `ret`
(because `stackSlot0` is architecturally dead after function return) preserves both the
extension's return value AND its step-by-step PC/address trace on all inputs, yet leaves the
secret in the shared kernel stack where the next extension reads it!
-/

def P_scrub_src : SrcProg :=
  [.storeSecretToStack 0, .computeInSecretReg, .scrubSecretReg, .scrubStackSlot 0, .ret]

/-- Dead-Store Elimination (DSE) pass removing `scrubStackSlot` prior to `ret`. -/
def dsePass : SrcProg → TgtProg
  | [] => []
  | i :: rest =>
    match i with
    | .scrubStackSlot _ => dsePass rest
    | .cmovSelectSec => .cmovSelectSec :: dsePass rest
    | .branchSelectSec => .branchSelectSec :: dsePass rest
    | .storeSecretToStack s => .storeSecretToStack s :: dsePass rest
    | .computeInSecretReg => .computeInSecretReg :: dsePass rest
    | .scrubSecretReg => .scrubSecretReg :: dsePass rest
    | .spillSecretRegToStack s => .spillSecretRegToStack s :: dsePass rest
    | .reloadSpilledSecretReg s => .reloadSpilledSecretReg s :: dsePass rest
    | .ret => .ret :: dsePass rest

/-- Next extension invoked on the shared kernel stack reads stack slot 0. -/
def readResidualSharedStack (out : ExtOutcome) : Nat :=
  out.residualStackSec

theorem dead_store_elimination_breaks_secret_scrubbing :
    SourceCTAndScrubbed P_scrub_src ∧
    (∀ s : ExtInputState,
      (runTgt (dsePass P_scrub_src) s).retVal = (runSrc P_scrub_src s).retVal) ∧
    (∀ s₁ s₂ : ExtInputState, PublicEquivInput s₁ s₂ →
      (runTgt (dsePass P_scrub_src) s₁).obsTrace = (runTgt (dsePass P_scrub_src) s₂).obsTrace) ∧
    (∀ s : ExtInputState,
      (runTgt (dsePass P_scrub_src) s).residualStackSec = s.secIn ∧
      readResidualSharedStack (runTgt (dsePass P_scrub_src) s) = s.secIn) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro s₁ s₂ _
      rfl
    · intro s
      exact ⟨rfl, rfl⟩
  · intro s
    rfl
  · intro s₁ s₂ _
    rfl
  · intro s
    exact ⟨rfl, rfl⟩

/-!
### Counterexample 3: `secret_register_spill_breaks_memory_erasure`
(Barthe et al. `CompCert-CT` POPL 2020; Besson, Dang & Jensen CSF 2019 §IV.B `Allocation` spill)
Source program `P_reg_only_src` never touches stack memory: it computes in a register,
scrubs the register to `0` (`scrubSecretReg`), and returns.
During register allocation (`Allocation` / `Stacking`), the compiler spills `secReg` to
`stack[0]` (`spillSecretRegToStack 0`) and reloads it (`reloadSpilledSecretReg 0`), then
executes the original `scrubSecretReg`.
Even though:
1. Return values are 100% preserved on all inputs,
2. The target PC/address trace `obsTrace` is 100% Constant-Time (since the stack spill offset `0`
   is a fixed public constant — the exact case allowed by `CompCert-CT`!), and
3. The architectural register `secReg` is scrubbed to `0` on exit,
the spilled copy of `secIn` remains in `residualStackSec` after `ret`!
-/

def P_reg_only_src : SrcProg :=
  [.computeInSecretReg, .scrubSecretReg, .ret]

/-- Register allocator pass that spills and reloads `secReg` around `computeInSecretReg`. -/
def regAllocSpillPass : SrcProg → TgtProg
  | [] => []
  | i :: rest =>
    match i with
    | .computeInSecretReg =>
      .computeInSecretReg :: .spillSecretRegToStack 0 :: .reloadSpilledSecretReg 0 ::
        regAllocSpillPass rest
    | .cmovSelectSec => .cmovSelectSec :: regAllocSpillPass rest
    | .branchSelectSec => .branchSelectSec :: regAllocSpillPass rest
    | .storeSecretToStack s => .storeSecretToStack s :: regAllocSpillPass rest
    | .scrubStackSlot s => .scrubStackSlot s :: regAllocSpillPass rest
    | .scrubSecretReg => .scrubSecretReg :: regAllocSpillPass rest
    | .spillSecretRegToStack s => .spillSecretRegToStack s :: regAllocSpillPass rest
    | .reloadSpilledSecretReg s => .reloadSpilledSecretReg s :: regAllocSpillPass rest
    | .ret => .ret :: regAllocSpillPass rest

theorem secret_register_spill_breaks_memory_erasure :
    SourceCTAndScrubbed P_reg_only_src ∧
    (∀ s : ExtInputState,
      (runTgt (regAllocSpillPass P_reg_only_src) s).retVal =
        (runSrc P_reg_only_src s).retVal) ∧
    (∀ s₁ s₂ : ExtInputState, PublicEquivInput s₁ s₂ →
      (runTgt (regAllocSpillPass P_reg_only_src) s₁).obsTrace =
        (runTgt (regAllocSpillPass P_reg_only_src) s₂).obsTrace) ∧
    (∀ s : ExtInputState,
      (runTgt (regAllocSpillPass P_reg_only_src) s).residualRegSec = 0 ∧
      (runTgt (regAllocSpillPass P_reg_only_src) s).residualStackSec = s.secIn) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro s₁ s₂ _
      rfl
    · intro s
      exact ⟨rfl, rfl⟩
  · intro s
    rfl
  · intro s₁ s₂ _
    rfl
  · intro s
    exact ⟨rfl, rfl⟩

/-!
### Architectural Solution 1: `ct_lockstep_simulation_preserves_ct_and_scrubbing`
(`CompCert-CT` POPL 2020 Leak-Transforming Simulation + Besson et al. CSF 2019 IFP Erasure)

If a verified compiler or JIT pass is accompanied by a relational **Leakage- & Erasure-Preserving
Simulation Certificate (`CTSimulates`)** with a deterministic public-parameterized trace
transformation `f_leak : Nat → List ObsEvent → List ObsEvent` (modeling `CompCert-CT`'s
memory-injection trace map $F(s,\sigma,\iota)$) and post-exit stack/register scrubbing preservation,
then `SourceCTAndScrubbed P_src` transfers soundly to `TargetCTAndScrubbed P_tgt`.
-/

structure CTSimulates (P_src : SrcProg) (P_tgt : TgtProg) where
  /-- Deterministic trace transformer depending only on public input `pubIn` and source trace. -/
  f_leak : Nat → List ObsEvent → List ObsEvent
  /-- Functional return-value preservation. -/
  ret_equiv : ∀ s : ExtInputState, (runTgt P_tgt s).retVal = (runSrc P_src s).retVal
  /-- Leak-transforming simulation (`CompCert-CT` POPL 2020 §4.2). -/
  trace_sim : ∀ s : ExtInputState,
    (runTgt P_tgt s).obsTrace = f_leak s.pubIn (runSrc P_src s).obsTrace
  /-- Exit stack and scratch-register erasure preservation (Besson et al. CSF 2019 §III). -/
  scrub_sim : ∀ s : ExtInputState,
    (runSrc P_src s).residualStackSec = 0 ∧ (runSrc P_src s).residualRegSec = 0 →
    (runTgt P_tgt s).residualStackSec = 0 ∧ (runTgt P_tgt s).residualRegSec = 0

theorem ct_lockstep_simulation_preserves_ct_and_scrubbing
    (P_src : SrcProg) (P_tgt : TgtProg)
    (sim : CTSimulates P_src P_tgt)
    (hSrc : SourceCTAndScrubbed P_src) :
    TargetCTAndScrubbed P_tgt ∧
    (∀ s : ExtInputState, (runTgt P_tgt s).retVal = (runSrc P_src s).retVal) := by
  rcases hSrc with ⟨hSrcCt, hSrcScrub⟩
  refine ⟨⟨?_, ?_⟩, sim.ret_equiv⟩
  · intro s₁ s₂ hPub
    rw [sim.trace_sim s₁, sim.trace_sim s₂]
    have hSrcTrace : (runSrc P_src s₁).obsTrace = (runSrc P_src s₂).obsTrace :=
      hSrcCt s₁ s₂ hPub
    rw [hPub.1, hSrcTrace]
  · intro s
    exact sim.scrub_sim s (hSrcScrub s)

/-!
### Architectural Solution 2: `consumer_bound_machine_byte_ct_cert_defeats_bad_compiler`
(Anneal / `Jasmin` / `Kraken` Target-Byte Certificate Checker)

Instead of trusting the compiler pipeline (or requiring a full `CompCert-CT` + IFP proof of LLVM/rustc),
a consumer-bound kernel certificate checker inspects the **target machine program `P_tgt` itself**
at Ring-0 load time, tracking:
- `noSecretBranch`: absence of `branchSelectSec`,
- `regTainted`: whether `secReg` currently holds an unscrubbed secret,
- `stackSlot0Tainted`: whether `stackSlot0` currently holds an unscrubbed secret (either from
  an explicit store or a compiler-inserted register spill!),
- `sawRet`: whether `ret` is reached with `regTainted == false` and `stackSlot0Tainted == false`.
-/

structure TargetByteAbstractState where
  noSecretBranch : Bool
  regTainted : Bool
  stackSlot0Tainted : Bool
  sawRet : Bool
  deriving DecidableEq, Repr

def stepTargetByteChecker (st : TargetByteAbstractState) (instr : CompilerIrInstr) :
    TargetByteAbstractState :=
  if st.sawRet then st
  else
    match instr with
    | .cmovSelectSec => st
    | .branchSelectSec => { st with noSecretBranch := false }
    | .storeSecretToStack slot =>
      { st with stackSlot0Tainted := if natEq slot 0 then true else st.stackSlot0Tainted }
    | .scrubStackSlot slot =>
      { st with stackSlot0Tainted := if natEq slot 0 then false else st.stackSlot0Tainted }
    | .computeInSecretReg =>
      { st with regTainted := true }
    | .scrubSecretReg =>
      { st with regTainted := false }
    | .spillSecretRegToStack slot =>
      { st with
        stackSlot0Tainted :=
          if natEq slot 0 then (st.regTainted || st.stackSlot0Tainted) else st.stackSlot0Tainted }
    | .reloadSpilledSecretReg slot =>
      { st with
        regTainted :=
          if natEq slot 0 then (st.stackSlot0Tainted || st.regTainted) else st.regTainted }
    | .ret =>
      { st with sawRet := true }

def runTargetByteCheckerLoop : List CompilerIrInstr → TargetByteAbstractState → TargetByteAbstractState
  | [], st => st
  | i :: rest, st => runTargetByteCheckerLoop rest (stepTargetByteChecker st i)

def initialTargetCheckerState : TargetByteAbstractState :=
  { noSecretBranch := true, regTainted := false, stackSlot0Tainted := false, sawRet := false }

/--
Consumer-bound target-level Constant-Time + Secret-Erasure certificate checker:
verifies that no secret branch executes, a `ret` is reached, and both `regTainted` and
`stackSlot0Tainted` are `false` at `ret`.
-/
def checkTargetByteCtAndScrubCert (prog : TgtProg) : Bool :=
  let finalSt := runTargetByteCheckerLoop prog initialTargetCheckerState
  finalSt.noSecretBranch && finalSt.sawRet && (!finalSt.regTainted) && (!finalSt.stackSlot0Tainted)

/--
Besson et al. (CSF 2019 §V.B) spill-patching compiler pass: inserts `scrubStackSlot 0`
before `ret` to zeroize the compiler-introduced stack spill slot.
-/
def bessonPatchedSpillPass : SrcProg → TgtProg
  | [] => []
  | i :: rest =>
    match i with
    | .computeInSecretReg =>
      .computeInSecretReg :: .spillSecretRegToStack 0 :: .reloadSpilledSecretReg 0 ::
        bessonPatchedSpillPass rest
    | .ret =>
      .scrubStackSlot 0 :: .ret :: bessonPatchedSpillPass rest
    | .cmovSelectSec => .cmovSelectSec :: bessonPatchedSpillPass rest
    | .branchSelectSec => .branchSelectSec :: bessonPatchedSpillPass rest
    | .storeSecretToStack s => .storeSecretToStack s :: bessonPatchedSpillPass rest
    | .scrubStackSlot s => .scrubStackSlot s :: bessonPatchedSpillPass rest
    | .scrubSecretReg => .scrubSecretReg :: bessonPatchedSpillPass rest
    | .spillSecretRegToStack s => .spillSecretRegToStack s :: bessonPatchedSpillPass rest
    | .reloadSpilledSecretReg s => .reloadSpilledSecretReg s :: bessonPatchedSpillPass rest

/--
Step-invariant lemma connecting `stepTargetByteChecker` to concrete execution `stepIrInstr`:
1. If `noSecretBranch` remains `true`, `stepIrInstr`'s `trace` is identical for any two inputs
   `s₁, s₂` whenever their starting `pc` and `trace` match;
2. If `regTainted = false`, then `secReg = 0`;
3. If `stackSlot0Tainted = false`, then `stackSlot0 = 0`.
-/
theorem stepTargetByteChecker_invariant
    (instr : CompilerIrInstr)
    (absSt : TargetByteAbstractState)
    (s₁ s₂ : ExtInputState)
    (st₁ st₂ : IrExecState)
    (hHalted : st₁.halted = absSt.sawRet ∧ st₂.halted = absSt.sawRet)
    (hPc : st₁.pc = st₂.pc)
    (hTrace : absSt.noSecretBranch = true → st₁.trace = st₂.trace)
    (hReg₁ : absSt.regTainted = false → st₁.secReg = 0)
    (hStack₁ : absSt.stackSlot0Tainted = false → st₁.stackSlot0 = 0) :
    let absSt' := stepTargetByteChecker absSt instr
    let st₁' := stepIrInstr s₁ st₁ instr
    let st₂' := stepIrInstr s₂ st₂ instr
    (st₁'.halted = absSt'.sawRet ∧ st₂'.halted = absSt'.sawRet) ∧
    st₁'.pc = st₂'.pc ∧
    (absSt'.noSecretBranch = true → st₁'.trace = st₂'.trace) ∧
    (absSt'.regTainted = false → st₁'.secReg = 0) ∧
    (absSt'.stackSlot0Tainted = false → st₁'.stackSlot0 = 0) := by
  rcases hHalted with ⟨hH₁, hH₂⟩
  cases hSaw : absSt.sawRet with
  | true =>
    have h1 : st₁.halted = true := by rw [hH₁, hSaw]
    have h2 : st₂.halted = true := by rw [hH₂, hSaw]
    dsimp [stepTargetByteChecker, stepIrInstr]
    rw [hSaw, h1, h2]
    dsimp
    exact ⟨⟨hH₁, hH₂⟩, hPc, hTrace, hReg₁, hStack₁⟩
  | false =>
    have h1 : st₁.halted = false := by rw [hH₁, hSaw]
    have h2 : st₂.halted = false := by rw [hH₂, hSaw]
    cases instr with
    | cmovSelectSec =>
      dsimp [stepTargetByteChecker, stepIrInstr]
      rw [hSaw, h1, h2]
      dsimp
      refine ⟨⟨hSaw.symm, hSaw.symm⟩, by rw [hPc], ?_, hReg₁, hStack₁⟩
      intro hNoBr
      rw [hTrace hNoBr, hPc]
    | branchSelectSec =>
      dsimp [stepTargetByteChecker, stepIrInstr]
      rw [hSaw, h1, h2]
      dsimp
      refine ⟨⟨rfl, rfl⟩, by rw [hPc], ?_, hReg₁, hStack₁⟩
      intro hFalse
      contradiction
    | storeSecretToStack slot =>
      dsimp [stepTargetByteChecker, stepIrInstr]
      rw [hSaw, h1, h2]
      dsimp
      refine ⟨⟨rfl, rfl⟩, by rw [hPc], ?_, hReg₁, ?_⟩
      · intro hNoBr
        rw [hTrace hNoBr, hPc]
      · cases hSlot : natEq slot 0 with
        | true =>
          dsimp
          intro hFalse
          contradiction
        | false =>
          dsimp
          exact hStack₁
    | scrubStackSlot slot =>
      dsimp [stepTargetByteChecker, stepIrInstr]
      rw [hSaw, h1, h2]
      dsimp
      refine ⟨⟨rfl, rfl⟩, by rw [hPc], ?_, hReg₁, ?_⟩
      · intro hNoBr
        rw [hTrace hNoBr, hPc]
      · cases hSlot : natEq slot 0 with
        | true =>
          dsimp
          intro _
          rfl
        | false =>
          dsimp
          exact hStack₁
    | computeInSecretReg =>
      dsimp [stepTargetByteChecker, stepIrInstr]
      rw [hSaw, h1, h2]
      dsimp
      refine ⟨⟨rfl, rfl⟩, by rw [hPc], ?_, ?_, hStack₁⟩
      · intro hNoBr
        rw [hTrace hNoBr, hPc]
      · intro hFalse
        contradiction
    | scrubSecretReg =>
      dsimp [stepTargetByteChecker, stepIrInstr]
      rw [hSaw, h1, h2]
      dsimp
      refine ⟨⟨rfl, rfl⟩, by rw [hPc], ?_, ?_, hStack₁⟩
      · intro hNoBr
        rw [hTrace hNoBr, hPc]
      · intro _
        rfl
    | spillSecretRegToStack slot =>
      dsimp [stepTargetByteChecker, stepIrInstr]
      rw [hSaw, h1, h2]
      dsimp
      refine ⟨⟨rfl, rfl⟩, by rw [hPc], ?_, hReg₁, ?_⟩
      · intro hNoBr
        rw [hTrace hNoBr, hPc]
      · cases hSlot : natEq slot 0 with
        | true =>
          dsimp
          intro hOr
          cases hR : absSt.regTainted with
          | true =>
            rw [hR] at hOr
            contradiction
          | false =>
            exact hReg₁ hR
        | false =>
          dsimp
          exact hStack₁
    | reloadSpilledSecretReg slot =>
      dsimp [stepTargetByteChecker, stepIrInstr]
      rw [hSaw, h1, h2]
      dsimp
      refine ⟨⟨rfl, rfl⟩, by rw [hPc], ?_, ?_, hStack₁⟩
      · intro hNoBr
        rw [hTrace hNoBr, hPc]
      · cases hSlot : natEq slot 0 with
        | true =>
          dsimp
          intro hOr
          cases hS : absSt.stackSlot0Tainted with
          | true =>
            rw [hS] at hOr
            contradiction
          | false =>
            exact hStack₁ hS
        | false =>
          dsimp
          exact hReg₁
    | ret =>
      dsimp [stepTargetByteChecker, stepIrInstr]
      rw [hSaw, h1, h2]
      dsimp
      refine ⟨⟨rfl, rfl⟩, by rw [hPc], ?_, hReg₁, hStack₁⟩
      · intro hNoBr
        rw [hTrace hNoBr, hPc]

theorem runTargetByteCheckerLoop_invariant
    (prog : TgtProg)
    (absSt : TargetByteAbstractState)
    (s₁ s₂ : ExtInputState)
    (st₁ st₂ : IrExecState)
    (hHalted : st₁.halted = absSt.sawRet ∧ st₂.halted = absSt.sawRet)
    (hPc : st₁.pc = st₂.pc)
    (hTrace : absSt.noSecretBranch = true → st₁.trace = st₂.trace)
    (hReg₁ : absSt.regTainted = false → st₁.secReg = 0)
    (hStack₁ : absSt.stackSlot0Tainted = false → st₁.stackSlot0 = 0) :
    let absSt' := runTargetByteCheckerLoop prog absSt
    let st₁' := runIrProgLoop s₁ prog st₁
    let st₂' := runIrProgLoop s₂ prog st₂
    (st₁'.halted = absSt'.sawRet ∧ st₂'.halted = absSt'.sawRet) ∧
    st₁'.pc = st₂'.pc ∧
    (absSt'.noSecretBranch = true → st₁'.trace = st₂'.trace) ∧
    (absSt'.regTainted = false → st₁'.secReg = 0) ∧
    (absSt'.stackSlot0Tainted = false → st₁'.stackSlot0 = 0) := by
  induction prog generalizing absSt st₁ st₂ with
  | nil =>
    exact ⟨hHalted, hPc, hTrace, hReg₁, hStack₁⟩
  | cons i rest ih =>
    have hStep :=
      stepTargetByteChecker_invariant i absSt s₁ s₂ st₁ st₂ hHalted hPc hTrace hReg₁ hStack₁
    rcases hStep with ⟨hH', hPc', hTr', hReg', hStack'⟩
    exact ih (stepTargetByteChecker absSt i) (stepIrInstr s₁ st₁ i) (stepIrInstr s₂ st₂ i)
      hH' hPc' hTr' hReg' hStack'

/--
Theorem (`consumer_bound_machine_byte_ct_cert_defeats_bad_compiler`):
1. Any target program `P_tgt` accepted by `checkTargetByteCtAndScrubCert P_tgt = true` is guaranteed
   to satisfy `TargetCTAndScrubbed P_tgt` (regardless of whether the compiler had bugs);
2. All three buggy compiler outputs (`lowerCmovToBranch P_cmov_src`, `dsePass P_scrub_src`,
   and `regAllocSpillPass P_reg_only_src`) are deterministically rejected (`= false`) at Ring-0
   load time;
3. The spill-scrubbed compilation (`bessonPatchedSpillPass P_reg_only_src`) is accepted (`= true`)
   and satisfies `TargetCTAndScrubbed`.
-/
theorem consumer_bound_machine_byte_ct_cert_defeats_bad_compiler :
    (∀ P_tgt : TgtProg,
      checkTargetByteCtAndScrubCert P_tgt = true → TargetCTAndScrubbed P_tgt) ∧
    checkTargetByteCtAndScrubCert (lowerCmovToBranch P_cmov_src) = false ∧
    checkTargetByteCtAndScrubCert (dsePass P_scrub_src) = false ∧
    checkTargetByteCtAndScrubCert (regAllocSpillPass P_reg_only_src) = false ∧
    checkTargetByteCtAndScrubCert (bessonPatchedSpillPass P_reg_only_src) = true ∧
    TargetCTAndScrubbed (bessonPatchedSpillPass P_reg_only_src) := by
  have hSound : ∀ P_tgt : TgtProg,
      checkTargetByteCtAndScrubCert P_tgt = true → TargetCTAndScrubbed P_tgt := by
    intro P_tgt hCheck
    dsimp [checkTargetByteCtAndScrubCert] at hCheck
    rcases band_eq_true hCheck with ⟨h123, hNoStack⟩
    rcases band_eq_true h123 with ⟨h12, hNoReg⟩
    rcases band_eq_true h12 with ⟨hNoBr, _hSawRet⟩
    have hRegFalse : (runTargetByteCheckerLoop P_tgt initialTargetCheckerState).regTainted = false := by
      cases h : (runTargetByteCheckerLoop P_tgt initialTargetCheckerState).regTainted with
      | false => rfl
      | true => rw [h] at hNoReg; contradiction
    have hStackFalse : (runTargetByteCheckerLoop P_tgt initialTargetCheckerState).stackSlot0Tainted = false := by
      cases h : (runTargetByteCheckerLoop P_tgt initialTargetCheckerState).stackSlot0Tainted with
      | false => rfl
      | true => rw [h] at hNoStack; contradiction
    refine ⟨?_, ?_⟩
    · intro s₁ s₂ _hPub
      have hInv :=
        runTargetByteCheckerLoop_invariant P_tgt initialTargetCheckerState s₁ s₂
          initialIrState initialIrState
          ⟨rfl, rfl⟩ rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      exact hInv.2.2.1 hNoBr
    · intro s
      have hInv :=
        runTargetByteCheckerLoop_invariant P_tgt initialTargetCheckerState s s
          initialIrState initialIrState
          ⟨rfl, rfl⟩ rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      exact ⟨hInv.2.2.2.2 hStackFalse, hInv.2.2.2.1 hRegFalse⟩
  refine ⟨hSound, rfl, rfl, rfl, rfl, hSound (bessonPatchedSpillPass P_reg_only_src) rfl⟩

/-!
## Section 2: Kernel Context-Switch & Domain-Exit Boundary: `seL4` Time Protection
(Ge, Yarom, Chothia & Heiser, EuroSys 2019, DOI 10.1145/3302424.3303976)

We model a multi-extension / multi-domain kernel CPU state `KernelCpuState` containing:
- Shared microarchitectural & residual kernel state
  `mu = (cacheState, bpuState, scratchRegs, sharedStack, cycleClock)`:
  1. `cacheState : Nat` — dirty L1-D / shared kernel cache lines left on-core;
  2. `bpuState : Nat` — branch predictor (BTB / BHB / RSB) state;
  3. `scratchRegs : Nat` — residual general-purpose / vector register values;
  4. `sharedStack : Nat` — residual values in shared kernel stack when `Kernel_Clone` is absent;
  5. `cycleClock : Nat` — hardware cycle counter visible across domain switches.
-/

structure MicroArchState where
  cacheState : Nat
  bpuState : Nat
  scratchRegs : Nat
  sharedStack : Nat
  cycleClock : Nat
  deriving DecidableEq, Repr

def cleanMicroArchState (baseClock : Nat) : MicroArchState :=
  { cacheState := 0
    bpuState := 0
    scratchRegs := 0
    sharedStack := 0
    cycleClock := baseClock }

/-- Execution output of a single kernel extension / domain slice. -/
structure DomExecResult where
  pubOut : Nat
  archTrace : List ObsEvent
  execCycles : Nat
  dirtyCacheLines : Nat
  postMu : MicroArchState
  deriving DecidableEq, Repr

/--
A kernel extension / domain slice takes:
- its domain secret `domSec : Nat`,
- public input `pubIn : Nat`, and
- incoming `mu : MicroArchState`,
and produces a `DomExecResult`.
-/
structure DomExtension where
  runDom : Nat → Nat → MicroArchState → DomExecResult

/--
An extension `ext` satisfies `IsolatedCT` in isolation iff, whenever invoked from a
clean microarchitectural baseline `cleanMicroArchState baseClock`, its public output `pubOut`
and architectural observation trace `archTrace` depend ONLY on `pubIn` and `baseClock`
(completely independent of `domSec`).
-/
def IsolatedCT (ext : DomExtension) : Prop :=
  ∀ (sec₁ sec₂ pubIn baseClock : Nat),
    let r₁ := ext.runDom sec₁ pubIn (cleanMicroArchState baseClock)
    let r₂ := ext.runDom sec₂ pubIn (cleanMicroArchState baseClock)
    r₁.pubOut = r₂.pubOut ∧ r₁.archTrace = r₂.archTrace

/--
Naive context switch (without `seL4` Time Protection): switches from Domain A to Domain B
while leaving Domain A's residual `cacheState`, `bpuState`, `scratchRegs`, `sharedStack`,
and unpadded `cycleClock` intact in `MicroArchState`.
-/
def naiveContextSwitch (resA : DomExecResult) : MicroArchState :=
  resA.postMu

/--
Partial context switch that flushes caches, BPU, scratch registers, and shared stack to `0`,
but fails to pad the L1-D cache-flush latency (violating Ge et al. EuroSys 2019 Requirement 4:
"Flush Deterministically", because flushing `dirtyCacheLines` takes `dirtyCacheLines` cycles).
-/
def unpaddedFlushSwitch (resA : DomExecResult) : MicroArchState :=
  { cacheState := 0
    bpuState := 0
    scratchRegs := 0
    sharedStack := 0
    cycleClock := resA.postMu.cycleClock + resA.dirtyCacheLines }

/--
`seL4` Time-Protected Domain Switch (Ge et al. EuroSys 2019 §3.2, Requirements 1–5):
1. Flushes on-core L1-D, L1-I, TLB, and BPU (`cacheState := 0`, `bpuState := 0`);
2. Uses partitioned `Kernel_Clone` stack and zeroes scratch registers (`scratchRegs := 0`, `sharedStack := 0`);
3. Pads total domain execution + L1-D flush latency to the configured worst-case domain switch
   budget `baseClock + worstCaseBudget` by polling the hardware cycle counter (`cycleClock`).
-/
def sel4TimeProtectedSwitch (baseClock worstCaseBudget : Nat) (_resA : DomExecResult) :
    MicroArchState :=
  { cacheState := 0
    bpuState := 0
    scratchRegs := 0
    sharedStack := 0
    cycleClock := baseClock + worstCaseBudget }

/--
Concrete Extension A (`extA_residual`):
In isolation from `cleanMicroArchState`, `extA_residual` returns public `pubIn` and emits a
fixed public trace `[ObsEvent.pcStep 0]`, so `IsolatedCT extA_residual` holds!
However, during its internal computation, `extA_residual` leaves `domSec` in `sharedStack`
and `scratchRegs`, and dirties `domSec % 2` cache lines.
-/
def extA_residual : DomExtension where
  runDom := fun domSec pubIn mu =>
    let dirty := if natEq domSec 0 then 1 else 8
    { pubOut := pubIn + mu.sharedStack
      archTrace := [ObsEvent.pcStep 0]
      execCycles := 10
      dirtyCacheLines := dirty
      postMu :=
        { cacheState := dirty
          bpuState := domSec
          scratchRegs := domSec
          sharedStack := domSec
          cycleClock := mu.cycleClock + 10 } }

/--
Concrete Extension B (`extB_observer`):
In isolation from `cleanMicroArchState` (where `sharedStack = 0`, `scratchRegs = 0`,
`cacheState = 0`), `extB_observer` has no secret of its own and outputs
`pubIn + mu.sharedStack + mu.cycleClock`, which depends ONLY on `pubIn` and `baseClock`,
so `IsolatedCT extB_observer` ALSO holds!
-/
def extB_observer : DomExtension where
  runDom := fun _domSecB pubIn mu =>
    { pubOut := pubIn + mu.sharedStack + mu.cycleClock
      archTrace := [ObsEvent.pcStep 0]
      execCycles := 5
      dirtyCacheLines := 0
      postMu :=
        { mu with cycleClock := mu.cycleClock + 5 } }

/--
Theorem (`isolated_ct_insufficient_across_context_switch`):
Both `extA_residual` and `extB_observer` satisfy `IsolatedCT` individually (`IsolatedCT extA_residual`
and `IsolatedCT extB_observer`), yet when `extA_residual` and `extB_observer` execute sequentially
across `naiveContextSwitch`, `extB_observer`'s public output directly leaks `extA_residual`'s secret!
-/
theorem isolated_ct_insufficient_across_context_switch :
    IsolatedCT extA_residual ∧
    IsolatedCT extB_observer ∧
    (∃ (secA₁ secA₂ pubIn baseClock : Nat),
      (extB_observer.runDom 0 pubIn
        (naiveContextSwitch (extA_residual.runDom secA₁ pubIn (cleanMicroArchState baseClock)))).pubOut ≠
      (extB_observer.runDom 0 pubIn
        (naiveContextSwitch (extA_residual.runDom secA₂ pubIn (cleanMicroArchState baseClock)))).pubOut) := by
  refine ⟨?_, ?_, ?_⟩
  · intro sec₁ sec₂ pubIn baseClock
    exact ⟨rfl, rfl⟩
  · intro sec₁ sec₂ pubIn baseClock
    exact ⟨rfl, rfl⟩
  · refine ⟨0, 77, 10, 100, ?_⟩
    intro hEq
    contradiction

/--
Theorem (`unpadded_cache_flush_leaks_via_clock` — Ge et al. EuroSys 2019 §4.4):
Even if the kernel zeroes `scratchRegs`, `sharedStack`, `cacheState`, and `bpuState` on context
switch (`unpaddedFlushSwitch`), failing to pad the variable L1-D dirty-line flush latency leaks
Domain A's secret (`secA₁ = 0` vs `secA₂ = 77`) to Domain B through `mu.cycleClock`!
-/
theorem unpadded_cache_flush_leaks_via_clock :
    ∃ (secA₁ secA₂ pubIn baseClock : Nat),
      let resA₁ := extA_residual.runDom secA₁ pubIn (cleanMicroArchState baseClock)
      let resA₂ := extA_residual.runDom secA₂ pubIn (cleanMicroArchState baseClock)
      let muB₁ := unpaddedFlushSwitch resA₁
      let muB₂ := unpaddedFlushSwitch resA₂
      muB₁.cacheState = 0 ∧ muB₁.bpuState = 0 ∧ muB₁.scratchRegs = 0 ∧ muB₁.sharedStack = 0 ∧
      muB₂.cacheState = 0 ∧ muB₂.bpuState = 0 ∧ muB₂.scratchRegs = 0 ∧ muB₂.sharedStack = 0 ∧
      (extB_observer.runDom 0 pubIn muB₁).pubOut ≠
        (extB_observer.runDom 0 pubIn muB₂).pubOut := by
  refine ⟨0, 77, 10, 100, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro hEq
  contradiction

/--
Theorem (`sel4_time_protection_compositional_noninterference`):
When the kernel enforces `sel4TimeProtectedSwitch baseClock worstCaseBudget` at the domain switch
between ANY extension `extA` and ANY observer extension `extB`:
1. The microarchitectural and residual state `mu` entering `extB` is 100% independent of
   Domain A's secret `secA₁` vs `secA₂`;
2. For any `secB` and `pubIn`, `extB`'s entire `DomExecResult` (`pubOut`, `archTrace`, `postMu`)
   is identical under `secA₁` and `secA₂`!
-/
theorem sel4_time_protection_compositional_noninterference
    (extA extB : DomExtension)
    (secA₁ secA₂ secB pubIn baseClock worstCaseBudget : Nat) :
    let resA₁ := extA.runDom secA₁ pubIn (cleanMicroArchState baseClock)
    let resA₂ := extA.runDom secA₂ pubIn (cleanMicroArchState baseClock)
    let muB₁ := sel4TimeProtectedSwitch baseClock worstCaseBudget resA₁
    let muB₂ := sel4TimeProtectedSwitch baseClock worstCaseBudget resA₂
    muB₁ = muB₂ ∧
    extB.runDom secB pubIn muB₁ = extB.runDom secB pubIn muB₂ := by
  exact ⟨rfl, rfl⟩

/--
Multi-extension schedule runner enforcing `sel4TimeProtectedSwitch` after every extension slice
in a schedule `List (DomExtension × Nat)` (pairing each extension with its domain secret).
-/
def runTimeProtectedSchedule
    (pubIn worstCaseBudget : Nat) :
    List (DomExtension × Nat) → Nat → MicroArchState
  | [], currentClock => cleanMicroArchState currentClock
  | (ext, domSec) :: rest, currentClock =>
    let res := ext.runDom domSec pubIn (cleanMicroArchState currentClock)
    let _switchedMu := sel4TimeProtectedSwitch currentClock worstCaseBudget res
    runTimeProtectedSchedule pubIn worstCaseBudget rest (currentClock + worstCaseBudget)

/--
Theorem (`sel4_time_protection_schedule_noninterference`):
Across an arbitrary multi-extension schedule of length $k$, replacing the secret inputs of all $k$
domains with any other secret list of the same length leaves the final post-switch
`MicroArchState` (and the entry `MicroArchState` of any subsequent observer extension)
100% invariant!
-/
theorem sel4_time_protection_schedule_noninterference
    (pubIn worstCaseBudget : Nat)
    (s₁ s₂ : List (DomExtension × Nat))
    (hLen : s₁.length = s₂.length)
    (baseClock : Nat) :
    runTimeProtectedSchedule pubIn worstCaseBudget s₁ baseClock =
      runTimeProtectedSchedule pubIn worstCaseBudget s₂ baseClock := by
  induction s₁ generalizing s₂ baseClock with
  | nil =>
    cases s₂ with
    | nil => rfl
    | cons _ _ => contradiction
  | cons hd₁ tl₁ ih =>
    cases s₂ with
    | nil => contradiction
    | cons hd₂ tl₂ =>
      dsimp [List.length] at hLen
      injection hLen with hLenTl
      dsimp [runTimeProtectedSchedule]
      exact ih tl₂ hLenTl (baseClock + worstCaseBudget)

/-!
## Section 3: Anneal's 7-Obligation Consumer-Bound Side-Channel-Free Ring-0
Admission Gate (`Obligation 7: ob7_sideChannelFreedom`) — Sufficiency & 4-Way Necessity

We now extend Anneal's 6-obligation consumer-bound Ring-0 admission gate
(`ob1_byteBinding` .. `ob6_boundedFuelTermination`) with **Obligation 7 (`ob7_sideChannelFreedom`)**,
consisting of 4 orthogonal machine-checked sub-obligations on the decoded candidate bytes:
- `ob7a_archConstantTime`: No secret-dependent branch conditions, memory addresses, or
  variable-latency ALU operations (`varTimeDivSecret`, `branchSecret`);
- `ob7b_speculativeConstantTime`: Every memory load is either public/masked in-bounds
  (`loadPublic`, `specLoadMasked`) or guarded by a speculation fence, with zero unmasked
  transient loads (`specLoadUnmasked`);
- `ob7c_secretExitAndSpillScrubbing`: Every secret-tainted scratch register (`aluSecret`) and
  every secret stack spill (`storeStackSecretSpill`) is overwritten with `0` (`scrubScratchRegs`,
  `scrubStackSlot`) prior to `ret`;
- `ob7d_secretIndependentFuelTiming`: The total instruction step count (`stepsTaken`) to `ret`
  is independent of secret inputs (no `secretFuelDelay`).
-/

/--
Ring-0 instruction set modeling both classic kernel safety (`ob1`–`ob6`) and the four
side-channel dimensions (`ob7a`–`ob7d`).
-/
inductive CtRing0Instr where
  | aluSecret                   -- Constant-latency ALU op on `secIn`, taints scratch reg
  | varTimeDivSecret            -- Variable-latency division on `secIn` (violates `ob7a`)
  | branchSecret                -- Secret-dependent branch direction in `archObsTrace` (violates `ob7a`)
  | loadPublic (slot : Nat)     -- Public-address load within `[0, stackBound)`
  | specLoadMasked (slot : Nat) -- Bitwise-masked speculative-safe load within `[0, stackBound)`
  | specLoadUnmasked (slot : Nat) -- Unmasked load that under misprediction (`oracle = true`) leaks `secIn` into `specObsTrace` (violates `ob7b`)
  | storeStackSecretSpill (slot : Nat) -- Spills `secIn` to `stack[slot]` (violates `ob7c` if unscrubbed before `ret`)
  | scrubStackSlot (slot : Nat) -- Scrubs `stack[slot] := 0`
  | scrubScratchRegs            -- Scrubs scratch registers to `0`
  | secretFuelDelay             -- Secret-dependent internal cycle/step delay (`stepsTaken += 1 + secIn`) with no address/branch event (violates `ob7d`)
  | helperCall (helperId : Nat) -- Calls kernel helper (`ob3_helperContract`)
  | cli                         -- Masks interrupts (`ob5_irqDiscipline`)
  | sti                         -- Unmasks interrupts (`ob5_irqDiscipline`)
  | privEscalate                -- Forbidden privilege write (`ob2_privilegeSafety`)
  | clobberCalleeSaved          -- Clobbers callee-saved register (`ob4_abiPreservation`)
  | ret                         -- Returns cleanly to Ring-0 caller
  deriving DecidableEq, Repr

/-- Bijective byte encoding of `CtRing0Instr` (`opcode :: operand`). -/
def encodeCtInstr : CtRing0Instr → List Nat
  | .aluSecret                   => [1, 0]
  | .varTimeDivSecret            => [2, 0]
  | .branchSecret                => [3, 0]
  | .loadPublic slot             => [4, slot]
  | .specLoadMasked slot         => [5, slot]
  | .specLoadUnmasked slot       => [6, slot]
  | .storeStackSecretSpill slot  => [7, slot]
  | .scrubStackSlot slot         => [8, slot]
  | .scrubScratchRegs            => [9, 0]
  | .secretFuelDelay             => [10, 0]
  | .helperCall helperId         => [11, helperId]
  | .cli                         => [12, 0]
  | .sti                         => [13, 0]
  | .privEscalate                => [14, 0]
  | .clobberCalleeSaved          => [15, 0]
  | .ret                         => [16, 0]

def encodeCtProg : List CtRing0Instr → List Nat
  | [] => []
  | i :: rest => encodeCtInstr i ++ encodeCtProg rest

/-- Decode a single `(opcode, operand)` byte pair without overlapping pattern matches. -/
def decodeOneCtInstr (opcode operand : Nat) : Option CtRing0Instr :=
  if natEq opcode 1 && natEq operand 0 then some .aluSecret
  else if natEq opcode 2 && natEq operand 0 then some .varTimeDivSecret
  else if natEq opcode 3 && natEq operand 0 then some .branchSecret
  else if natEq opcode 4 then some (.loadPublic operand)
  else if natEq opcode 5 then some (.specLoadMasked operand)
  else if natEq opcode 6 then some (.specLoadUnmasked operand)
  else if natEq opcode 7 then some (.storeStackSecretSpill operand)
  else if natEq opcode 8 then some (.scrubStackSlot operand)
  else if natEq opcode 9 && natEq operand 0 then some .scrubScratchRegs
  else if natEq opcode 10 && natEq operand 0 then some .secretFuelDelay
  else if natEq opcode 11 then some (.helperCall operand)
  else if natEq opcode 12 && natEq operand 0 then some .cli
  else if natEq opcode 13 && natEq operand 0 then some .sti
  else if natEq opcode 14 && natEq operand 0 then some .privEscalate
  else if natEq opcode 15 && natEq operand 0 then some .clobberCalleeSaved
  else if natEq opcode 16 && natEq operand 0 then some .ret
  else none

/-- Trusted Ring-0 byte decoder (`Option (List CtRing0Instr)`). -/
def decodeCtRing0Bytes : List Nat → Option (List CtRing0Instr)
  | [] => some []
  | _ :: [] => none
  | op :: arg :: rest =>
    match decodeOneCtInstr op arg with
    | none => none
    | some instr =>
      match decodeCtRing0Bytes rest with
      | none => none
      | some p => some (instr :: p)

/-- Constructive equality on `CtRing0Instr` via its injective 2-byte encoding. -/
def ctInstrEq (a b : CtRing0Instr) : Bool :=
  natListEq (encodeCtInstr a) (encodeCtInstr b)

theorem ctInstrEq_eq {a b : CtRing0Instr} (h : ctInstrEq a b = true) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | (dsimp [ctInstrEq, encodeCtInstr, natListEq, natEq, Bool.and] at h
       exact congrArg _ (natEq_eq (band_eq_true h).1))
    | nomatch h

def ctProgEq : List CtRing0Instr → List CtRing0Instr → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | x :: xs, y :: ys => ctInstrEq x y && ctProgEq xs ys

theorem ctProgEq_eq {xs ys : List CtRing0Instr} (h : ctProgEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => nomatch h
  | cons x rest ih =>
    cases ys with
    | nil => nomatch h
    | cons y restY =>
      dsimp [ctProgEq] at h
      have ⟨hxy, hrest⟩ := band_eq_true h
      exact (ctInstrEq_eq hxy) ▸ (ih hrest) ▸ rfl

def optionCtProgEq : Option (List CtRing0Instr) → Option (List CtRing0Instr) → Bool
  | none, none => true
  | none, some _ => false
  | some _, none => false
  | some xs, some ys => ctProgEq xs ys

theorem optionCtProgEq_eq {a b : Option (List CtRing0Instr)} (h : optionCtProgEq a b = true) :
    a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some _ => nomatch h
  | some xs =>
    cases b with
    | none => nomatch h
    | some ys =>
      dsimp [optionCtProgEq] at h
      exact congrArg some (ctProgEq_eq h)

/-- Candidate native extension image submitted to the Ring-0 loader. -/
structure CtCandidateImage where
  bytes : List Nat
  stackBound : Nat
  deriving DecidableEq, Repr

/-- Ring-0 Admission Request. -/
structure CtAdmissionRequest where
  candidate : CtCandidateImage
  allowedHelpers : List Nat
  deriving DecidableEq, Repr

/-- Certificate accompanying a candidate Ring-0 extension. -/
structure CtExtensionCert where
  decodedProg : List CtRing0Instr
  fuelBound : Nat
  deriving DecidableEq, Repr

def natMem (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => natEq x y || natMem x ys

/-! ### The 6 Classic Ring-0 Safety Obligations (`ob1`–`ob6`) -/

/-- Obligation 1: Consumer-bound byte decoding matches `cert.decodedProg` and memory slots are in-bounds. -/
def checkSlotsInBounds (stackBound : Nat) : List CtRing0Instr → Bool
  | [] => true
  | instr :: rest =>
    let ok :=
      match instr with
      | .loadPublic slot => natLt slot stackBound
      | .specLoadMasked slot => natLt slot stackBound
      | .specLoadUnmasked slot => natLt slot stackBound
      | .storeStackSecretSpill slot => natLt slot stackBound && natEq slot 0
      | .scrubStackSlot slot => natLt slot stackBound && natEq slot 0
      | .aluSecret => true
      | .varTimeDivSecret => true
      | .branchSecret => true
      | .scrubScratchRegs => true
      | .secretFuelDelay => true
      | .helperCall _ => true
      | .cli => true
      | .sti => true
      | .privEscalate => true
      | .clobberCalleeSaved => true
      | .ret => true
    ok && checkSlotsInBounds stackBound rest

def ob1_byteBinding (req : CtAdmissionRequest) (cert : CtExtensionCert) : Bool :=
  optionCtProgEq (decodeCtRing0Bytes req.candidate.bytes) (some cert.decodedProg) &&
  checkSlotsInBounds req.candidate.stackBound cert.decodedProg

/-- Obligation 2: Privilege safety (no `privEscalate`). -/
def ob2_privilegeSafety : List CtRing0Instr → Bool
  | [] => true
  | instr :: rest =>
    match instr with
    | .privEscalate => false
    | .aluSecret => ob2_privilegeSafety rest
    | .varTimeDivSecret => ob2_privilegeSafety rest
    | .branchSecret => ob2_privilegeSafety rest
    | .loadPublic _ => ob2_privilegeSafety rest
    | .specLoadMasked _ => ob2_privilegeSafety rest
    | .specLoadUnmasked _ => ob2_privilegeSafety rest
    | .storeStackSecretSpill _ => ob2_privilegeSafety rest
    | .scrubStackSlot _ => ob2_privilegeSafety rest
    | .scrubScratchRegs => ob2_privilegeSafety rest
    | .secretFuelDelay => ob2_privilegeSafety rest
    | .helperCall _ => ob2_privilegeSafety rest
    | .cli => ob2_privilegeSafety rest
    | .sti => ob2_privilegeSafety rest
    | .clobberCalleeSaved => ob2_privilegeSafety rest
    | .ret => ob2_privilegeSafety rest

/-- Obligation 3: Helper call contract (every `helperCall id` is in `allowedHelpers`). -/
def ob3_helperContract (allowedHelpers : List Nat) : List CtRing0Instr → Bool
  | [] => true
  | instr :: rest =>
    match instr with
    | .helperCall hId => natMem hId allowedHelpers && ob3_helperContract allowedHelpers rest
    | .aluSecret => ob3_helperContract allowedHelpers rest
    | .varTimeDivSecret => ob3_helperContract allowedHelpers rest
    | .branchSecret => ob3_helperContract allowedHelpers rest
    | .loadPublic _ => ob3_helperContract allowedHelpers rest
    | .specLoadMasked _ => ob3_helperContract allowedHelpers rest
    | .specLoadUnmasked _ => ob3_helperContract allowedHelpers rest
    | .storeStackSecretSpill _ => ob3_helperContract allowedHelpers rest
    | .scrubStackSlot _ => ob3_helperContract allowedHelpers rest
    | .scrubScratchRegs => ob3_helperContract allowedHelpers rest
    | .secretFuelDelay => ob3_helperContract allowedHelpers rest
    | .cli => ob3_helperContract allowedHelpers rest
    | .sti => ob3_helperContract allowedHelpers rest
    | .privEscalate => ob3_helperContract allowedHelpers rest
    | .clobberCalleeSaved => ob3_helperContract allowedHelpers rest
    | .ret => ob3_helperContract allowedHelpers rest

/-- Obligation 4: ABI preservation (no `clobberCalleeSaved`). -/
def ob4_abiPreservation : List CtRing0Instr → Bool
  | [] => true
  | instr :: rest =>
    match instr with
    | .clobberCalleeSaved => false
    | .aluSecret => ob4_abiPreservation rest
    | .varTimeDivSecret => ob4_abiPreservation rest
    | .branchSecret => ob4_abiPreservation rest
    | .loadPublic _ => ob4_abiPreservation rest
    | .specLoadMasked _ => ob4_abiPreservation rest
    | .specLoadUnmasked _ => ob4_abiPreservation rest
    | .storeStackSecretSpill _ => ob4_abiPreservation rest
    | .scrubStackSlot _ => ob4_abiPreservation rest
    | .scrubScratchRegs => ob4_abiPreservation rest
    | .secretFuelDelay => ob4_abiPreservation rest
    | .helperCall _ => ob4_abiPreservation rest
    | .cli => ob4_abiPreservation rest
    | .sti => ob4_abiPreservation rest
    | .privEscalate => ob4_abiPreservation rest
    | .ret => ob4_abiPreservation rest

/-- Obligation 5: IRQ discipline (`cli`/`sti` balanced and interrupts unmasked at `ret`). -/
def checkIrqLoop : List CtRing0Instr → Bool → Bool
  | [], irqMasked => !irqMasked
  | instr :: rest, irqMasked =>
    match instr with
    | .cli => checkIrqLoop rest true
    | .sti => if irqMasked then checkIrqLoop rest false else false
    | .ret => (!irqMasked)
    | .aluSecret => checkIrqLoop rest irqMasked
    | .varTimeDivSecret => checkIrqLoop rest irqMasked
    | .branchSecret => checkIrqLoop rest irqMasked
    | .loadPublic _ => checkIrqLoop rest irqMasked
    | .specLoadMasked _ => checkIrqLoop rest irqMasked
    | .specLoadUnmasked _ => checkIrqLoop rest irqMasked
    | .storeStackSecretSpill _ => checkIrqLoop rest irqMasked
    | .scrubStackSlot _ => checkIrqLoop rest irqMasked
    | .scrubScratchRegs => checkIrqLoop rest irqMasked
    | .secretFuelDelay => checkIrqLoop rest irqMasked
    | .helperCall _ => checkIrqLoop rest irqMasked
    | .privEscalate => checkIrqLoop rest irqMasked
    | .clobberCalleeSaved => checkIrqLoop rest irqMasked

def ob5_irqDiscipline (prog : List CtRing0Instr) : Bool :=
  checkIrqLoop prog false

/-- Obligation 6: Bounded-fuel termination (`fuelBound == prog.length` and `prog` reaches `ret`). -/
def hasRetInstr : List CtRing0Instr → Bool
  | [] => false
  | instr :: rest =>
    match instr with
    | .ret => true
    | .aluSecret => hasRetInstr rest
    | .varTimeDivSecret => hasRetInstr rest
    | .branchSecret => hasRetInstr rest
    | .loadPublic _ => hasRetInstr rest
    | .specLoadMasked _ => hasRetInstr rest
    | .specLoadUnmasked _ => hasRetInstr rest
    | .storeStackSecretSpill _ => hasRetInstr rest
    | .scrubStackSlot _ => hasRetInstr rest
    | .scrubScratchRegs => hasRetInstr rest
    | .secretFuelDelay => hasRetInstr rest
    | .helperCall _ => hasRetInstr rest
    | .cli => hasRetInstr rest
    | .sti => hasRetInstr rest
    | .privEscalate => hasRetInstr rest
    | .clobberCalleeSaved => hasRetInstr rest

def ob6_boundedFuelTermination (cert : CtExtensionCert) : Bool :=
  natEq cert.fuelBound cert.decodedProg.length && hasRetInstr cert.decodedProg

/-! ### Obligation 7 (`ob7_sideChannelFreedom`): 4 Orthogonal Sub-Obligations (`ob7a`–`ob7d`) -/

/--
`ob7a_archConstantTime`:
Every reachable instruction prior to `ret` has secret-independent branch conditions,
memory addresses, and ALU latencies (no `varTimeDivSecret` and no `branchSecret`).
-/
def ob7a_archConstantTime : List CtRing0Instr → Bool
  | [] => true
  | instr :: rest =>
    match instr with
    | .ret => true
    | .varTimeDivSecret => false
    | .branchSecret => false
    | .aluSecret => ob7a_archConstantTime rest
    | .loadPublic _ => ob7a_archConstantTime rest
    | .specLoadMasked _ => ob7a_archConstantTime rest
    | .specLoadUnmasked _ => ob7a_archConstantTime rest
    | .storeStackSecretSpill _ => ob7a_archConstantTime rest
    | .scrubStackSlot _ => ob7a_archConstantTime rest
    | .scrubScratchRegs => ob7a_archConstantTime rest
    | .secretFuelDelay => ob7a_archConstantTime rest
    | .helperCall _ => ob7a_archConstantTime rest
    | .cli => ob7a_archConstantTime rest
    | .sti => ob7a_archConstantTime rest
    | .privEscalate => ob7a_archConstantTime rest
    | .clobberCalleeSaved => ob7a_archConstantTime rest

/--
`ob7b_speculativeConstantTime`:
Every memory load prior to `ret` is speculative-safe (no `specLoadUnmasked`).
-/
def ob7b_speculativeConstantTime : List CtRing0Instr → Bool
  | [] => true
  | instr :: rest =>
    match instr with
    | .ret => true
    | .specLoadUnmasked _ => false
    | .aluSecret => ob7b_speculativeConstantTime rest
    | .varTimeDivSecret => ob7b_speculativeConstantTime rest
    | .branchSecret => ob7b_speculativeConstantTime rest
    | .loadPublic _ => ob7b_speculativeConstantTime rest
    | .specLoadMasked _ => ob7b_speculativeConstantTime rest
    | .storeStackSecretSpill _ => ob7b_speculativeConstantTime rest
    | .scrubStackSlot _ => ob7b_speculativeConstantTime rest
    | .scrubScratchRegs => ob7b_speculativeConstantTime rest
    | .secretFuelDelay => ob7b_speculativeConstantTime rest
    | .helperCall _ => ob7b_speculativeConstantTime rest
    | .cli => ob7b_speculativeConstantTime rest
    | .sti => ob7b_speculativeConstantTime rest
    | .privEscalate => ob7b_speculativeConstantTime rest
    | .clobberCalleeSaved => ob7b_speculativeConstantTime rest

/--
`ob7c_secretExitAndSpillScrubbing`:
Tracks register taint (`regTainted`) and stack spill taint (`stackTainted`) up to `ret`,
requiring both to be `false` when `ret` executes.
-/
def checkScrubLoop : List CtRing0Instr → Bool → Bool → Bool
  | [], regTainted, stackTainted => (!regTainted) && (!stackTainted)
  | instr :: rest, regTainted, stackTainted =>
    match instr with
    | .ret => (!regTainted) && (!stackTainted)
    | .aluSecret => checkScrubLoop rest true stackTainted
    | .varTimeDivSecret => checkScrubLoop rest true stackTainted
    | .scrubScratchRegs => checkScrubLoop rest false stackTainted
    | .storeStackSecretSpill _ => checkScrubLoop rest regTainted true
    | .scrubStackSlot _ => checkScrubLoop rest regTainted false
    | .branchSecret => checkScrubLoop rest regTainted stackTainted
    | .loadPublic _ => checkScrubLoop rest regTainted stackTainted
    | .specLoadMasked _ => checkScrubLoop rest regTainted stackTainted
    | .specLoadUnmasked _ => checkScrubLoop rest regTainted stackTainted
    | .secretFuelDelay => checkScrubLoop rest regTainted stackTainted
    | .helperCall _ => checkScrubLoop rest regTainted stackTainted
    | .cli => checkScrubLoop rest regTainted stackTainted
    | .sti => checkScrubLoop rest regTainted stackTainted
    | .privEscalate => checkScrubLoop rest regTainted stackTainted
    | .clobberCalleeSaved => checkScrubLoop rest regTainted stackTainted

def ob7c_secretExitAndSpillScrubbing (prog : List CtRing0Instr) : Bool :=
  checkScrubLoop prog false false

/--
`ob7d_secretIndependentFuelTiming`:
Total step/cycle count up to `ret` is independent of secret inputs (no `secretFuelDelay`).
-/
def ob7d_secretIndependentFuelTiming : List CtRing0Instr → Bool
  | [] => true
  | instr :: rest =>
    match instr with
    | .ret => true
    | .secretFuelDelay => false
    | .aluSecret => ob7d_secretIndependentFuelTiming rest
    | .varTimeDivSecret => ob7d_secretIndependentFuelTiming rest
    | .branchSecret => ob7d_secretIndependentFuelTiming rest
    | .loadPublic _ => ob7d_secretIndependentFuelTiming rest
    | .specLoadMasked _ => ob7d_secretIndependentFuelTiming rest
    | .specLoadUnmasked _ => ob7d_secretIndependentFuelTiming rest
    | .storeStackSecretSpill _ => ob7d_secretIndependentFuelTiming rest
    | .scrubStackSlot _ => ob7d_secretIndependentFuelTiming rest
    | .scrubScratchRegs => ob7d_secretIndependentFuelTiming rest
    | .helperCall _ => ob7d_secretIndependentFuelTiming rest
    | .cli => ob7d_secretIndependentFuelTiming rest
    | .sti => ob7d_secretIndependentFuelTiming rest
    | .privEscalate => ob7d_secretIndependentFuelTiming rest
    | .clobberCalleeSaved => ob7d_secretIndependentFuelTiming rest

/-- Combined Obligation 7 (`ob7_sideChannelFreedom`). -/
def ob7_sideChannelFreedom (prog : List CtRing0Instr) : Bool :=
  ob7a_archConstantTime prog &&
  ob7b_speculativeConstantTime prog &&
  ob7c_secretExitAndSpillScrubbing prog &&
  ob7d_secretIndependentFuelTiming prog

/--
Anneal's Full 7-Obligation Consumer-Bound Side-Channel-Free Ring-0 Admission Gate.
-/
def admitCtKernelExtension (req : CtAdmissionRequest) (cert : CtExtensionCert) : Bool :=
  ob1_byteBinding req cert &&
  ob2_privilegeSafety cert.decodedProg &&
  ob3_helperContract req.allowedHelpers cert.decodedProg &&
  ob4_abiPreservation cert.decodedProg &&
  ob5_irqDiscipline cert.decodedProg &&
  ob6_boundedFuelTermination cert &&
  ob7_sideChannelFreedom cert.decodedProg

/-! ### Operational Semantics of Loaded Ring-0 Extension Bytes -/

structure CtRing0State where
  pubIn : Nat
  secIn : Nat
  ringLevel : Nat
  calleeSaved : Nat
  irqMasked : Bool
  residualRegSecret : Nat
  residualStackSecret : Nat
  archObsTrace : List ObsEvent
  specObsTrace : List ObsEvent
  stepsTaken : Nat
  halted : Bool
  faulted : Bool
  deriving DecidableEq, Repr

def initialCtRing0State (pubIn secIn calleeSaved : Nat) : CtRing0State :=
  { pubIn := pubIn
    secIn := secIn
    ringLevel := 0
    calleeSaved := calleeSaved
    irqMasked := false
    residualRegSecret := 0
    residualStackSecret := 0
    archObsTrace := []
    specObsTrace := []
    stepsTaken := 0
    halted := false
    faulted := false }

def stepCtRing0Instr
    (stackBound : Nat)
    (allowedHelpers : List Nat)
    (oracle : Bool)
    (st : CtRing0State)
    (instr : CtRing0Instr) : CtRing0State :=
  if st.halted || st.faulted then st
  else
    match instr with
    | .aluSecret =>
      { st with
        residualRegSecret := st.secIn
        archObsTrace := st.archObsTrace ++ [ObsEvent.pcStep 1]
        specObsTrace := st.specObsTrace ++ [ObsEvent.pcStep 1]
        stepsTaken := st.stepsTaken + 1 }
    | .varTimeDivSecret =>
      { st with
        residualRegSecret := st.secIn
        archObsTrace := st.archObsTrace ++ [ObsEvent.varLatencyOp st.secIn]
        specObsTrace := st.specObsTrace ++ [ObsEvent.varLatencyOp st.secIn]
        stepsTaken := st.stepsTaken + 1 }
    | .branchSecret =>
      let b := !natEq st.secIn 0
      { st with
        archObsTrace := st.archObsTrace ++ [ObsEvent.branchTaken b]
        specObsTrace := st.specObsTrace ++ [ObsEvent.branchTaken b]
        stepsTaken := st.stepsTaken + 1 }
    | .loadPublic slot =>
      if natLt slot stackBound then
        { st with
          archObsTrace := st.archObsTrace ++ [ObsEvent.memAccess slot]
          specObsTrace := st.specObsTrace ++ [ObsEvent.memAccess slot]
          stepsTaken := st.stepsTaken + 1 }
      else
        { st with faulted := true }
    | .specLoadMasked slot =>
      if natLt slot stackBound then
        { st with
          archObsTrace := st.archObsTrace ++ [ObsEvent.memAccess slot]
          specObsTrace := st.specObsTrace ++ [ObsEvent.memAccess slot]
          stepsTaken := st.stepsTaken + 1 }
      else
        { st with faulted := true }
    | .specLoadUnmasked slot =>
      if natLt slot stackBound then
        let specEv :=
          if oracle then ObsEvent.memAccess (slot + st.secIn) else ObsEvent.memAccess slot
        { st with
          archObsTrace := st.archObsTrace ++ [ObsEvent.memAccess slot]
          specObsTrace := st.specObsTrace ++ [specEv]
          stepsTaken := st.stepsTaken + 1 }
      else
        { st with faulted := true }
    | .storeStackSecretSpill slot =>
      if natLt slot stackBound && natEq slot 0 then
        { st with
          residualStackSecret := st.secIn
          archObsTrace := st.archObsTrace ++ [ObsEvent.memAccess slot]
          specObsTrace := st.specObsTrace ++ [ObsEvent.memAccess slot]
          stepsTaken := st.stepsTaken + 1 }
      else
        { st with faulted := true }
    | .scrubStackSlot slot =>
      if natLt slot stackBound && natEq slot 0 then
        { st with
          residualStackSecret := 0
          archObsTrace := st.archObsTrace ++ [ObsEvent.memAccess slot]
          specObsTrace := st.specObsTrace ++ [ObsEvent.memAccess slot]
          stepsTaken := st.stepsTaken + 1 }
      else
        { st with faulted := true }
    | .scrubScratchRegs =>
      { st with
        residualRegSecret := 0
        archObsTrace := st.archObsTrace ++ [ObsEvent.pcStep 9]
        specObsTrace := st.specObsTrace ++ [ObsEvent.pcStep 9]
        stepsTaken := st.stepsTaken + 1 }
    | .secretFuelDelay =>
      let extraSteps := if natEq st.secIn 0 then 1 else 2
      { st with
        archObsTrace := st.archObsTrace ++ [ObsEvent.pcStep 10]
        specObsTrace := st.specObsTrace ++ [ObsEvent.pcStep 10]
        stepsTaken := st.stepsTaken + extraSteps }
    | .helperCall hId =>
      if natMem hId allowedHelpers then
        { st with
          archObsTrace := st.archObsTrace ++ [ObsEvent.pcStep (100 + hId)]
          specObsTrace := st.specObsTrace ++ [ObsEvent.pcStep (100 + hId)]
          stepsTaken := st.stepsTaken + 1 }
      else
        { st with faulted := true }
    | .cli =>
      { st with
        irqMasked := true
        archObsTrace := st.archObsTrace ++ [ObsEvent.pcStep 12]
        specObsTrace := st.specObsTrace ++ [ObsEvent.pcStep 12]
        stepsTaken := st.stepsTaken + 1 }
    | .sti =>
      if st.irqMasked then
        { st with
          irqMasked := false
          archObsTrace := st.archObsTrace ++ [ObsEvent.pcStep 13]
          specObsTrace := st.specObsTrace ++ [ObsEvent.pcStep 13]
          stepsTaken := st.stepsTaken + 1 }
      else
        { st with faulted := true }
    | .privEscalate =>
      { st with ringLevel := 3, faulted := true }
    | .clobberCalleeSaved =>
      { st with calleeSaved := st.calleeSaved + 1, stepsTaken := st.stepsTaken + 1 }
    | .ret =>
      if st.irqMasked then
        { st with faulted := true }
      else
        { st with
          halted := true
          archObsTrace := st.archObsTrace ++ [ObsEvent.pcStep 16]
          specObsTrace := st.specObsTrace ++ [ObsEvent.pcStep 16]
          stepsTaken := st.stepsTaken + 1 }

def runCtProgWithFuel
    (stackBound : Nat)
    (allowedHelpers : List Nat)
    (oracle : Bool) :
    Nat → List CtRing0Instr → CtRing0State → CtRing0State
  | 0, _, st => st
  | _ + 1, [], st => st
  | fuel + 1, i :: rest, st =>
    let st' := stepCtRing0Instr stackBound allowedHelpers oracle st i
    runCtProgWithFuel stackBound allowedHelpers oracle fuel rest st'

/--
Execute the raw candidate bytes `bytes` loaded by the Ring-0 consumer.
-/
def runCtLoadedBytes
    (req : CtAdmissionRequest)
    (fuel : Nat)
    (oracle : Bool)
    (st : CtRing0State) : CtRing0State :=
  match decodeCtRing0Bytes req.candidate.bytes with
  | none => { st with faulted := true }
  | some prog =>
    runCtProgWithFuel req.candidate.stackBound req.allowedHelpers oracle fuel prog st

/-! ### Inductive Invariant & Master Sufficiency Proof (`anneal_ring0_ct_extension_admission_soundness`) -/

theorem halted_runCtProgWithFuel
    (stackBound : Nat)
    (allowedHelpers : List Nat)
    (oracle : Bool)
    (fuel : Nat)
    (prog : List CtRing0Instr)
    (st : CtRing0State)
    (hHalted : st.halted = true) :
    runCtProgWithFuel stackBound allowedHelpers oracle fuel prog st = st := by
  induction fuel generalizing prog st with
  | zero => rfl
  | succ k ih =>
    cases prog with
    | nil => rfl
    | cons i rest =>
      have hStep : stepCtRing0Instr stackBound allowedHelpers oracle st i = st := by
        dsimp [stepCtRing0Instr]
        rw [hHalted]
        rfl
      dsimp [runCtProgWithFuel]
      rw [hStep]
      exact ih rest st hHalted

/--
Inductive lockstep safety + 2-safety relational invariant over `prog : List CtRing0Instr`
when `fuel = prog.length` and all obligations `ob1`–`ob7` hold.
-/
theorem runCtProgWithFuel_soundness_loop
    (stackBound : Nat)
    (allowedHelpers : List Nat)
    (oracle : Bool)
    (prog : List CtRing0Instr)
    (st₁ st₂ : CtRing0State)
    (irqFlag regTaint stackTaint : Bool)
    (hNotHalted₁ : st₁.halted = false)
    (hNotFaulted₁ : st₁.faulted = false)
    (hNotHalted₂ : st₂.halted = false)
    (hNotFaulted₂ : st₂.faulted = false)
    (hRing : st₁.ringLevel = 0 ∧ st₂.ringLevel = 0)
    (hCallee : st₁.calleeSaved = st₂.calleeSaved)
    (hIrqState : st₁.irqMasked = irqFlag ∧ st₂.irqMasked = irqFlag)
    (hArchTrace : st₁.archObsTrace = st₂.archObsTrace)
    (hSpecTrace : st₁.specObsTrace = st₂.specObsTrace)
    (hSteps : st₁.stepsTaken = st₂.stepsTaken)
    (hRegClean : regTaint = false → st₁.residualRegSecret = 0 ∧ st₂.residualRegSecret = 0)
    (hStackClean : stackTaint = false → st₁.residualStackSecret = 0 ∧ st₂.residualStackSecret = 0)
    (hSlots : checkSlotsInBounds stackBound prog = true)
    (hOb2 : ob2_privilegeSafety prog = true)
    (hOb3 : ob3_helperContract allowedHelpers prog = true)
    (hOb4 : ob4_abiPreservation prog = true)
    (hOb5 : checkIrqLoop prog irqFlag = true)
    (hHasRet : hasRetInstr prog = true)
    (hOb7a : ob7a_archConstantTime prog = true)
    (hOb7b : ob7b_speculativeConstantTime prog = true)
    (hOb7c : checkScrubLoop prog regTaint stackTaint = true)
    (hOb7d : ob7d_secretIndependentFuelTiming prog = true) :
    let out₁ := runCtProgWithFuel stackBound allowedHelpers oracle prog.length prog st₁
    let out₂ := runCtProgWithFuel stackBound allowedHelpers oracle prog.length prog st₂
    out₁.faulted = false ∧ out₂.faulted = false ∧
    out₁.halted = true ∧ out₂.halted = true ∧
    out₁.ringLevel = 0 ∧ out₂.ringLevel = 0 ∧
    out₁.calleeSaved = st₁.calleeSaved ∧ out₂.calleeSaved = st₂.calleeSaved ∧
    out₁.irqMasked = false ∧ out₂.irqMasked = false ∧
    out₁.archObsTrace = out₂.archObsTrace ∧
    out₁.specObsTrace = out₂.specObsTrace ∧
    out₁.residualRegSecret = 0 ∧ out₁.residualStackSecret = 0 ∧
    out₂.residualRegSecret = 0 ∧ out₂.residualStackSecret = 0 ∧
    out₁.stepsTaken = out₂.stepsTaken := by
  induction prog generalizing st₁ st₂ irqFlag regTaint stackTaint with
  | nil =>
    contradiction
  | cons instr rest ih =>
    rcases hRing with ⟨hR₁, hR₂⟩
    rcases hIrqState with ⟨hI₁, hI₂⟩
    cases instr with
    | ret =>
      have hIrqFalse : irqFlag = false := by
        dsimp [checkIrqLoop] at hOb5
        cases irqFlag with
        | false => rfl
        | true => contradiction
      have hScrubbed : regTaint = false ∧ stackTaint = false := by
        dsimp [checkScrubLoop] at hOb7c
        rcases band_eq_true hOb7c with ⟨hRT, hST⟩
        refine ⟨?_, ?_⟩
        · cases regTaint with
          | false => rfl
          | true => contradiction
        · cases stackTaint with
          | false => rfl
          | true => contradiction
      have ⟨hReg0₁, hReg0₂⟩ := hRegClean hScrubbed.1
      have ⟨hStack0₁, hStack0₂⟩ := hStackClean hScrubbed.2
      have hStep₁ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₁ .ret =
            { st₁ with
              halted := true
              archObsTrace := st₁.archObsTrace ++ [ObsEvent.pcStep 16]
              specObsTrace := st₁.specObsTrace ++ [ObsEvent.pcStep 16]
              stepsTaken := st₁.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₁, hNotFaulted₁, hI₁, hIrqFalse]
        rfl
      have hStep₂ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₂ .ret =
            { st₂ with
              halted := true
              archObsTrace := st₂.archObsTrace ++ [ObsEvent.pcStep 16]
              specObsTrace := st₂.specObsTrace ++ [ObsEvent.pcStep 16]
              stepsTaken := st₂.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₂, hNotFaulted₂, hI₂, hIrqFalse]
        rfl
      dsimp [List.length, runCtProgWithFuel]
      rw [hStep₁, hStep₂]
      rw [halted_runCtProgWithFuel stackBound allowedHelpers oracle rest.length rest _ rfl]
      rw [halted_runCtProgWithFuel stackBound allowedHelpers oracle rest.length rest _ rfl]
      refine ⟨hNotFaulted₁, hNotFaulted₂, rfl, rfl, hR₁, hR₂, rfl, rfl, ?_, ?_, ?_, ?_,
              hReg0₁, hStack0₁, hReg0₂, hStack0₂, ?_⟩
      · rw [hI₁, hIrqFalse]
      · rw [hI₂, hIrqFalse]
      · rw [hArchTrace]
      · rw [hSpecTrace]
      · rw [hSteps]
    | varTimeDivSecret =>
      dsimp [ob7a_archConstantTime] at hOb7a
      contradiction
    | branchSecret =>
      dsimp [ob7a_archConstantTime] at hOb7a
      contradiction
    | specLoadUnmasked _ =>
      dsimp [ob7b_speculativeConstantTime] at hOb7b
      contradiction
    | secretFuelDelay =>
      dsimp [ob7d_secretIndependentFuelTiming] at hOb7d
      contradiction
    | privEscalate =>
      dsimp [ob2_privilegeSafety] at hOb2
      contradiction
    | clobberCalleeSaved =>
      dsimp [ob4_abiPreservation] at hOb4
      contradiction
    | aluSecret =>
      dsimp [checkSlotsInBounds] at hSlots
      dsimp [ob2_privilegeSafety] at hOb2
      dsimp [ob3_helperContract] at hOb3
      dsimp [ob4_abiPreservation] at hOb4
      dsimp [checkIrqLoop] at hOb5
      dsimp [hasRetInstr] at hHasRet
      dsimp [ob7a_archConstantTime] at hOb7a
      dsimp [ob7b_speculativeConstantTime] at hOb7b
      dsimp [checkScrubLoop] at hOb7c
      dsimp [ob7d_secretIndependentFuelTiming] at hOb7d
      dsimp [List.length, runCtProgWithFuel]
      have hStep₁ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₁ .aluSecret =
            { st₁ with
              residualRegSecret := st₁.secIn
              archObsTrace := st₁.archObsTrace ++ [ObsEvent.pcStep 1]
              specObsTrace := st₁.specObsTrace ++ [ObsEvent.pcStep 1]
              stepsTaken := st₁.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₁, hNotFaulted₁]
        rfl
      have hStep₂ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₂ .aluSecret =
            { st₂ with
              residualRegSecret := st₂.secIn
              archObsTrace := st₂.archObsTrace ++ [ObsEvent.pcStep 1]
              specObsTrace := st₂.specObsTrace ++ [ObsEvent.pcStep 1]
              stepsTaken := st₂.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₂, hNotFaulted₂]
        rfl
      rw [hStep₁, hStep₂]
      exact ih _ _ irqFlag true stackTaint
        hNotHalted₁ hNotFaulted₁ hNotHalted₂ hNotFaulted₂
        ⟨hR₁, hR₂⟩ hCallee ⟨hI₁, hI₂⟩
        (by rw [hArchTrace]) (by rw [hSpecTrace]) (by rw [hSteps])
        (by intro h; contradiction) hStackClean
        hSlots hOb2 hOb3 hOb4 hOb5 hHasRet hOb7a hOb7b hOb7c hOb7d
    | scrubScratchRegs =>
      dsimp [checkSlotsInBounds] at hSlots
      dsimp [ob2_privilegeSafety] at hOb2
      dsimp [ob3_helperContract] at hOb3
      dsimp [ob4_abiPreservation] at hOb4
      dsimp [checkIrqLoop] at hOb5
      dsimp [hasRetInstr] at hHasRet
      dsimp [ob7a_archConstantTime] at hOb7a
      dsimp [ob7b_speculativeConstantTime] at hOb7b
      dsimp [checkScrubLoop] at hOb7c
      dsimp [ob7d_secretIndependentFuelTiming] at hOb7d
      dsimp [List.length, runCtProgWithFuel]
      have hStep₁ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₁ .scrubScratchRegs =
            { st₁ with
              residualRegSecret := 0
              archObsTrace := st₁.archObsTrace ++ [ObsEvent.pcStep 9]
              specObsTrace := st₁.specObsTrace ++ [ObsEvent.pcStep 9]
              stepsTaken := st₁.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₁, hNotFaulted₁]
        rfl
      have hStep₂ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₂ .scrubScratchRegs =
            { st₂ with
              residualRegSecret := 0
              archObsTrace := st₂.archObsTrace ++ [ObsEvent.pcStep 9]
              specObsTrace := st₂.specObsTrace ++ [ObsEvent.pcStep 9]
              stepsTaken := st₂.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₂, hNotFaulted₂]
        rfl
      rw [hStep₁, hStep₂]
      exact ih _ _ irqFlag false stackTaint
        hNotHalted₁ hNotFaulted₁ hNotHalted₂ hNotFaulted₂
        ⟨hR₁, hR₂⟩ hCallee ⟨hI₁, hI₂⟩
        (by rw [hArchTrace]) (by rw [hSpecTrace]) (by rw [hSteps])
        (fun _ => ⟨rfl, rfl⟩) hStackClean
        hSlots hOb2 hOb3 hOb4 hOb5 hHasRet hOb7a hOb7b hOb7c hOb7d
    | loadPublic slot =>
      dsimp [checkSlotsInBounds] at hSlots
      rcases band_eq_true hSlots with ⟨hSlotOk, hSlotsRest⟩
      dsimp [ob2_privilegeSafety] at hOb2
      dsimp [ob3_helperContract] at hOb3
      dsimp [ob4_abiPreservation] at hOb4
      dsimp [checkIrqLoop] at hOb5
      dsimp [hasRetInstr] at hHasRet
      dsimp [ob7a_archConstantTime] at hOb7a
      dsimp [ob7b_speculativeConstantTime] at hOb7b
      dsimp [checkScrubLoop] at hOb7c
      dsimp [ob7d_secretIndependentFuelTiming] at hOb7d
      dsimp [List.length, runCtProgWithFuel]
      have hStep₁ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₁ (.loadPublic slot) =
            { st₁ with
              archObsTrace := st₁.archObsTrace ++ [ObsEvent.memAccess slot]
              specObsTrace := st₁.specObsTrace ++ [ObsEvent.memAccess slot]
              stepsTaken := st₁.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₁, hNotFaulted₁, hSlotOk]
        rfl
      have hStep₂ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₂ (.loadPublic slot) =
            { st₂ with
              archObsTrace := st₂.archObsTrace ++ [ObsEvent.memAccess slot]
              specObsTrace := st₂.specObsTrace ++ [ObsEvent.memAccess slot]
              stepsTaken := st₂.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₂, hNotFaulted₂, hSlotOk]
        rfl
      rw [hStep₁, hStep₂]
      exact ih _ _ irqFlag regTaint stackTaint
        hNotHalted₁ hNotFaulted₁ hNotHalted₂ hNotFaulted₂
        ⟨hR₁, hR₂⟩ hCallee ⟨hI₁, hI₂⟩
        (by rw [hArchTrace]) (by rw [hSpecTrace]) (by rw [hSteps])
        hRegClean hStackClean
        hSlotsRest hOb2 hOb3 hOb4 hOb5 hHasRet hOb7a hOb7b hOb7c hOb7d
    | specLoadMasked slot =>
      dsimp [checkSlotsInBounds] at hSlots
      rcases band_eq_true hSlots with ⟨hSlotOk, hSlotsRest⟩
      dsimp [ob2_privilegeSafety] at hOb2
      dsimp [ob3_helperContract] at hOb3
      dsimp [ob4_abiPreservation] at hOb4
      dsimp [checkIrqLoop] at hOb5
      dsimp [hasRetInstr] at hHasRet
      dsimp [ob7a_archConstantTime] at hOb7a
      dsimp [ob7b_speculativeConstantTime] at hOb7b
      dsimp [checkScrubLoop] at hOb7c
      dsimp [ob7d_secretIndependentFuelTiming] at hOb7d
      dsimp [List.length, runCtProgWithFuel]
      have hStep₁ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₁ (.specLoadMasked slot) =
            { st₁ with
              archObsTrace := st₁.archObsTrace ++ [ObsEvent.memAccess slot]
              specObsTrace := st₁.specObsTrace ++ [ObsEvent.memAccess slot]
              stepsTaken := st₁.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₁, hNotFaulted₁, hSlotOk]
        rfl
      have hStep₂ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₂ (.specLoadMasked slot) =
            { st₂ with
              archObsTrace := st₂.archObsTrace ++ [ObsEvent.memAccess slot]
              specObsTrace := st₂.specObsTrace ++ [ObsEvent.memAccess slot]
              stepsTaken := st₂.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₂, hNotFaulted₂, hSlotOk]
        rfl
      rw [hStep₁, hStep₂]
      exact ih _ _ irqFlag regTaint stackTaint
        hNotHalted₁ hNotFaulted₁ hNotHalted₂ hNotFaulted₂
        ⟨hR₁, hR₂⟩ hCallee ⟨hI₁, hI₂⟩
        (by rw [hArchTrace]) (by rw [hSpecTrace]) (by rw [hSteps])
        hRegClean hStackClean
        hSlotsRest hOb2 hOb3 hOb4 hOb5 hHasRet hOb7a hOb7b hOb7c hOb7d
    | storeStackSecretSpill slot =>
      dsimp [checkSlotsInBounds] at hSlots
      rcases band_eq_true hSlots with ⟨hSlotOk, hSlotsRest⟩
      dsimp [ob2_privilegeSafety] at hOb2
      dsimp [ob3_helperContract] at hOb3
      dsimp [ob4_abiPreservation] at hOb4
      dsimp [checkIrqLoop] at hOb5
      dsimp [hasRetInstr] at hHasRet
      dsimp [ob7a_archConstantTime] at hOb7a
      dsimp [ob7b_speculativeConstantTime] at hOb7b
      dsimp [checkScrubLoop] at hOb7c
      dsimp [ob7d_secretIndependentFuelTiming] at hOb7d
      dsimp [List.length, runCtProgWithFuel]
      have hStep₁ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₁ (.storeStackSecretSpill slot) =
            { st₁ with
              residualStackSecret := st₁.secIn
              archObsTrace := st₁.archObsTrace ++ [ObsEvent.memAccess slot]
              specObsTrace := st₁.specObsTrace ++ [ObsEvent.memAccess slot]
              stepsTaken := st₁.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₁, hNotFaulted₁, hSlotOk]
        rfl
      have hStep₂ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₂ (.storeStackSecretSpill slot) =
            { st₂ with
              residualStackSecret := st₂.secIn
              archObsTrace := st₂.archObsTrace ++ [ObsEvent.memAccess slot]
              specObsTrace := st₂.specObsTrace ++ [ObsEvent.memAccess slot]
              stepsTaken := st₂.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₂, hNotFaulted₂, hSlotOk]
        rfl
      rw [hStep₁, hStep₂]
      exact ih _ _ irqFlag regTaint true
        hNotHalted₁ hNotFaulted₁ hNotHalted₂ hNotFaulted₂
        ⟨hR₁, hR₂⟩ hCallee ⟨hI₁, hI₂⟩
        (by rw [hArchTrace]) (by rw [hSpecTrace]) (by rw [hSteps])
        hRegClean (by intro h; contradiction)
        hSlotsRest hOb2 hOb3 hOb4 hOb5 hHasRet hOb7a hOb7b hOb7c hOb7d
    | scrubStackSlot slot =>
      dsimp [checkSlotsInBounds] at hSlots
      rcases band_eq_true hSlots with ⟨hSlotOk, hSlotsRest⟩
      dsimp [ob2_privilegeSafety] at hOb2
      dsimp [ob3_helperContract] at hOb3
      dsimp [ob4_abiPreservation] at hOb4
      dsimp [checkIrqLoop] at hOb5
      dsimp [hasRetInstr] at hHasRet
      dsimp [ob7a_archConstantTime] at hOb7a
      dsimp [ob7b_speculativeConstantTime] at hOb7b
      dsimp [checkScrubLoop] at hOb7c
      dsimp [ob7d_secretIndependentFuelTiming] at hOb7d
      dsimp [List.length, runCtProgWithFuel]
      have hStep₁ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₁ (.scrubStackSlot slot) =
            { st₁ with
              residualStackSecret := 0
              archObsTrace := st₁.archObsTrace ++ [ObsEvent.memAccess slot]
              specObsTrace := st₁.specObsTrace ++ [ObsEvent.memAccess slot]
              stepsTaken := st₁.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₁, hNotFaulted₁, hSlotOk]
        rfl
      have hStep₂ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₂ (.scrubStackSlot slot) =
            { st₂ with
              residualStackSecret := 0
              archObsTrace := st₂.archObsTrace ++ [ObsEvent.memAccess slot]
              specObsTrace := st₂.specObsTrace ++ [ObsEvent.memAccess slot]
              stepsTaken := st₂.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₂, hNotFaulted₂, hSlotOk]
        rfl
      rw [hStep₁, hStep₂]
      exact ih _ _ irqFlag regTaint false
        hNotHalted₁ hNotFaulted₁ hNotHalted₂ hNotFaulted₂
        ⟨hR₁, hR₂⟩ hCallee ⟨hI₁, hI₂⟩
        (by rw [hArchTrace]) (by rw [hSpecTrace]) (by rw [hSteps])
        hRegClean (fun _ => ⟨rfl, rfl⟩)
        hSlotsRest hOb2 hOb3 hOb4 hOb5 hHasRet hOb7a hOb7b hOb7c hOb7d
    | helperCall hId =>
      dsimp [checkSlotsInBounds] at hSlots
      dsimp [ob2_privilegeSafety] at hOb2
      dsimp [ob3_helperContract] at hOb3
      rcases band_eq_true hOb3 with ⟨hAllowed, hOb3Rest⟩
      dsimp [ob4_abiPreservation] at hOb4
      dsimp [checkIrqLoop] at hOb5
      dsimp [hasRetInstr] at hHasRet
      dsimp [ob7a_archConstantTime] at hOb7a
      dsimp [ob7b_speculativeConstantTime] at hOb7b
      dsimp [checkScrubLoop] at hOb7c
      dsimp [ob7d_secretIndependentFuelTiming] at hOb7d
      dsimp [List.length, runCtProgWithFuel]
      have hStep₁ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₁ (.helperCall hId) =
            { st₁ with
              archObsTrace := st₁.archObsTrace ++ [ObsEvent.pcStep (100 + hId)]
              specObsTrace := st₁.specObsTrace ++ [ObsEvent.pcStep (100 + hId)]
              stepsTaken := st₁.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₁, hNotFaulted₁, hAllowed]
        rfl
      have hStep₂ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₂ (.helperCall hId) =
            { st₂ with
              archObsTrace := st₂.archObsTrace ++ [ObsEvent.pcStep (100 + hId)]
              specObsTrace := st₂.specObsTrace ++ [ObsEvent.pcStep (100 + hId)]
              stepsTaken := st₂.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₂, hNotFaulted₂, hAllowed]
        rfl
      rw [hStep₁, hStep₂]
      exact ih _ _ irqFlag regTaint stackTaint
        hNotHalted₁ hNotFaulted₁ hNotHalted₂ hNotFaulted₂
        ⟨hR₁, hR₂⟩ hCallee ⟨hI₁, hI₂⟩
        (by rw [hArchTrace]) (by rw [hSpecTrace]) (by rw [hSteps])
        hRegClean hStackClean
        hSlots hOb2 hOb3Rest hOb4 hOb5 hHasRet hOb7a hOb7b hOb7c hOb7d
    | cli =>
      dsimp [checkSlotsInBounds] at hSlots
      dsimp [ob2_privilegeSafety] at hOb2
      dsimp [ob3_helperContract] at hOb3
      dsimp [ob4_abiPreservation] at hOb4
      dsimp [checkIrqLoop] at hOb5
      dsimp [hasRetInstr] at hHasRet
      dsimp [ob7a_archConstantTime] at hOb7a
      dsimp [ob7b_speculativeConstantTime] at hOb7b
      dsimp [checkScrubLoop] at hOb7c
      dsimp [ob7d_secretIndependentFuelTiming] at hOb7d
      dsimp [List.length, runCtProgWithFuel]
      have hStep₁ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₁ .cli =
            { st₁ with
              irqMasked := true
              archObsTrace := st₁.archObsTrace ++ [ObsEvent.pcStep 12]
              specObsTrace := st₁.specObsTrace ++ [ObsEvent.pcStep 12]
              stepsTaken := st₁.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₁, hNotFaulted₁]
        rfl
      have hStep₂ :
          stepCtRing0Instr stackBound allowedHelpers oracle st₂ .cli =
            { st₂ with
              irqMasked := true
              archObsTrace := st₂.archObsTrace ++ [ObsEvent.pcStep 12]
              specObsTrace := st₂.specObsTrace ++ [ObsEvent.pcStep 12]
              stepsTaken := st₂.stepsTaken + 1 } := by
        dsimp [stepCtRing0Instr]
        rw [hNotHalted₂, hNotFaulted₂]
        rfl
      rw [hStep₁, hStep₂]
      exact ih _ _ true regTaint stackTaint
        hNotHalted₁ hNotFaulted₁ hNotHalted₂ hNotFaulted₂
        ⟨hR₁, hR₂⟩ hCallee ⟨rfl, rfl⟩
        (by rw [hArchTrace]) (by rw [hSpecTrace]) (by rw [hSteps])
        hRegClean hStackClean
        hSlots hOb2 hOb3 hOb4 hOb5 hHasRet hOb7a hOb7b hOb7c hOb7d
    | sti =>
      dsimp [checkSlotsInBounds] at hSlots
      dsimp [ob2_privilegeSafety] at hOb2
      dsimp [ob3_helperContract] at hOb3
      dsimp [ob4_abiPreservation] at hOb4
      cases irqFlag with
      | false =>
        dsimp [checkIrqLoop] at hOb5
        contradiction
      | true =>
        dsimp [checkIrqLoop] at hOb5
        dsimp [hasRetInstr] at hHasRet
        dsimp [ob7a_archConstantTime] at hOb7a
        dsimp [ob7b_speculativeConstantTime] at hOb7b
        dsimp [checkScrubLoop] at hOb7c
        dsimp [ob7d_secretIndependentFuelTiming] at hOb7d
        dsimp [List.length, runCtProgWithFuel]
        have hStep₁ :
            stepCtRing0Instr stackBound allowedHelpers oracle st₁ .sti =
              { st₁ with
                irqMasked := false
                archObsTrace := st₁.archObsTrace ++ [ObsEvent.pcStep 13]
                specObsTrace := st₁.specObsTrace ++ [ObsEvent.pcStep 13]
                stepsTaken := st₁.stepsTaken + 1 } := by
          dsimp [stepCtRing0Instr]
          rw [hNotHalted₁, hNotFaulted₁, hI₁]
          rfl
        have hStep₂ :
            stepCtRing0Instr stackBound allowedHelpers oracle st₂ .sti =
              { st₂ with
                irqMasked := false
                archObsTrace := st₂.archObsTrace ++ [ObsEvent.pcStep 13]
                specObsTrace := st₂.specObsTrace ++ [ObsEvent.pcStep 13]
                stepsTaken := st₂.stepsTaken + 1 } := by
          dsimp [stepCtRing0Instr]
          rw [hNotHalted₂, hNotFaulted₂, hI₂]
          rfl
        rw [hStep₁, hStep₂]
        exact ih _ _ false regTaint stackTaint
          hNotHalted₁ hNotFaulted₁ hNotHalted₂ hNotFaulted₂
          ⟨hR₁, hR₂⟩ hCallee ⟨rfl, rfl⟩
          (by rw [hArchTrace]) (by rw [hSpecTrace]) (by rw [hSteps])
          hRegClean hStackClean
          hSlots hOb2 hOb3 hOb4 hOb5 hHasRet hOb7a hOb7b hOb7c hOb7d

/--
Master Sufficiency Theorem (`anneal_ring0_ct_extension_admission_soundness`):
Any `(req, cert)` accepted by `admitCtKernelExtension req cert = true` guarantees that
running the loaded bytes `req.candidate.bytes` from any two initial states `s₁, s₂` sharing
public inputs (`pubIn`, `calleeSaved`):
1. Satisfies all 6 classic Ring-0 safety properties (`faulted = false`, `halted = true`,
   `ringLevel = 0`, `calleeSaved` preserved, `irqMasked = false`);
2. Satisfies Architectural 2-Safety Constant-Time (`out₁.archObsTrace = out₂.archObsTrace`);
3. Satisfies Speculative 2-Safety Constant-Time (`out₁.specObsTrace = out₂.specObsTrace`);
4. Satisfies Post-Exit Secret Zeroization (`residualRegSecret = 0 ∧ residualStackSecret = 0`);
5. Satisfies Total-Execution-Time / Fuel Noninterference (`out₁.stepsTaken = out₂.stepsTaken`).
-/
theorem anneal_ring0_ct_extension_admission_soundness
    (req : CtAdmissionRequest)
    (cert : CtExtensionCert)
    (hAdmit : admitCtKernelExtension req cert = true)
    (pubIn sec₁ sec₂ calleeSaved : Nat)
    (oracle : Bool) :
    let s₁ := initialCtRing0State pubIn sec₁ calleeSaved
    let s₂ := initialCtRing0State pubIn sec₂ calleeSaved
    let out₁ := runCtLoadedBytes req cert.fuelBound oracle s₁
    let out₂ := runCtLoadedBytes req cert.fuelBound oracle s₂
    out₁.faulted = false ∧ out₂.faulted = false ∧
    out₁.halted = true ∧ out₂.halted = true ∧
    out₁.ringLevel = 0 ∧ out₂.ringLevel = 0 ∧
    out₁.calleeSaved = calleeSaved ∧ out₂.calleeSaved = calleeSaved ∧
    out₁.irqMasked = false ∧ out₂.irqMasked = false ∧
    out₁.archObsTrace = out₂.archObsTrace ∧
    out₁.specObsTrace = out₂.specObsTrace ∧
    out₁.residualRegSecret = 0 ∧ out₁.residualStackSecret = 0 ∧
    out₂.residualRegSecret = 0 ∧ out₂.residualStackSecret = 0 ∧
    out₁.stepsTaken = out₂.stepsTaken := by
  dsimp [admitCtKernelExtension] at hAdmit
  rcases band_eq_true hAdmit with ⟨h16, hOb7⟩
  rcases band_eq_true h16 with ⟨h15, hOb6⟩
  rcases band_eq_true h15 with ⟨h14, hOb5⟩
  rcases band_eq_true h14 with ⟨h13, hOb4⟩
  rcases band_eq_true h13 with ⟨h12, hOb3⟩
  rcases band_eq_true h12 with ⟨hOb1, hOb2⟩
  dsimp [ob1_byteBinding] at hOb1
  rcases band_eq_true hOb1 with ⟨hDecodeEq, hSlots⟩
  have hDecode : decodeCtRing0Bytes req.candidate.bytes = some cert.decodedProg :=
    optionCtProgEq_eq hDecodeEq
  dsimp [ob6_boundedFuelTermination] at hOb6
  rcases band_eq_true hOb6 with ⟨hFuelEq, hHasRet⟩
  have hFuel : cert.fuelBound = cert.decodedProg.length := natEq_eq hFuelEq
  dsimp [ob7_sideChannelFreedom] at hOb7
  rcases band_eq_true hOb7 with ⟨h7abc, hOb7d⟩
  rcases band_eq_true h7abc with ⟨h7ab, hOb7c⟩
  rcases band_eq_true h7ab with ⟨hOb7a, hOb7b⟩
  dsimp [runCtLoadedBytes]
  rw [hDecode, hFuel]
  exact runCtProgWithFuel_soundness_loop
    req.candidate.stackBound req.allowedHelpers oracle cert.decodedProg
    (initialCtRing0State pubIn sec₁ calleeSaved)
    (initialCtRing0State pubIn sec₂ calleeSaved)
    false false false
    rfl rfl rfl rfl ⟨rfl, rfl⟩ rfl ⟨rfl, rfl⟩ rfl rfl rfl
    (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
    hSlots hOb2 hOb3 hOb4 hOb5 hHasRet hOb7a hOb7b hOb7c hOb7d

/-!
### 4-Way Sub-Obligation Necessity (`anneal_ob7_four_subobligations_necessary`):
Dropping ANY ONE of `ob7a`, `ob7b`, `ob7c`, or `ob7d` while keeping `ob1`–`ob6` and the
other three `ob7` sub-obligations intact admits a concrete Ring-0 extension that leaks secrets!
-/

/-- Gate weakened by dropping ONLY `ob7a_archConstantTime`. -/
def admitWithoutOb7a (req : CtAdmissionRequest) (cert : CtExtensionCert) : Bool :=
  ob1_byteBinding req cert &&
  ob2_privilegeSafety cert.decodedProg &&
  ob3_helperContract req.allowedHelpers cert.decodedProg &&
  ob4_abiPreservation cert.decodedProg &&
  ob5_irqDiscipline cert.decodedProg &&
  ob6_boundedFuelTermination cert &&
  ob7b_speculativeConstantTime cert.decodedProg &&
  ob7c_secretExitAndSpillScrubbing cert.decodedProg &&
  ob7d_secretIndependentFuelTiming cert.decodedProg

/-- Gate weakened by dropping ONLY `ob7b_speculativeConstantTime`. -/
def admitWithoutOb7b (req : CtAdmissionRequest) (cert : CtExtensionCert) : Bool :=
  ob1_byteBinding req cert &&
  ob2_privilegeSafety cert.decodedProg &&
  ob3_helperContract req.allowedHelpers cert.decodedProg &&
  ob4_abiPreservation cert.decodedProg &&
  ob5_irqDiscipline cert.decodedProg &&
  ob6_boundedFuelTermination cert &&
  ob7a_archConstantTime cert.decodedProg &&
  ob7c_secretExitAndSpillScrubbing cert.decodedProg &&
  ob7d_secretIndependentFuelTiming cert.decodedProg

/-- Gate weakened by dropping ONLY `ob7c_secretExitAndSpillScrubbing`. -/
def admitWithoutOb7c (req : CtAdmissionRequest) (cert : CtExtensionCert) : Bool :=
  ob1_byteBinding req cert &&
  ob2_privilegeSafety cert.decodedProg &&
  ob3_helperContract req.allowedHelpers cert.decodedProg &&
  ob4_abiPreservation cert.decodedProg &&
  ob5_irqDiscipline cert.decodedProg &&
  ob6_boundedFuelTermination cert &&
  ob7a_archConstantTime cert.decodedProg &&
  ob7b_speculativeConstantTime cert.decodedProg &&
  ob7d_secretIndependentFuelTiming cert.decodedProg

/-- Gate weakened by dropping ONLY `ob7d_secretIndependentFuelTiming`. -/
def admitWithoutOb7d (req : CtAdmissionRequest) (cert : CtExtensionCert) : Bool :=
  ob1_byteBinding req cert &&
  ob2_privilegeSafety cert.decodedProg &&
  ob3_helperContract req.allowedHelpers cert.decodedProg &&
  ob4_abiPreservation cert.decodedProg &&
  ob5_irqDiscipline cert.decodedProg &&
  ob6_boundedFuelTermination cert &&
  ob7a_archConstantTime cert.decodedProg &&
  ob7b_speculativeConstantTime cert.decodedProg &&
  ob7c_secretExitAndSpillScrubbing cert.decodedProg

/-- Counterexample 7a: Uses `varTimeDivSecret` then `scrubScratchRegs` then `ret`. -/
def badProg7a : List CtRing0Instr := [.varTimeDivSecret, .scrubScratchRegs, .ret]
def badReq7a : CtAdmissionRequest :=
  { candidate := { bytes := encodeCtProg badProg7a, stackBound := 4 }, allowedHelpers := [] }
def badCert7a : CtExtensionCert :=
  { decodedProg := badProg7a, fuelBound := 3 }

theorem drop_ob7a_unsound :
    admitWithoutOb7a badReq7a badCert7a = true ∧
    admitCtKernelExtension badReq7a badCert7a = false ∧
    (let out₁ := runCtLoadedBytes badReq7a badCert7a.fuelBound false (initialCtRing0State 1 0 99)
     let out₂ := runCtLoadedBytes badReq7a badCert7a.fuelBound false (initialCtRing0State 1 42 99)
     out₁.faulted = false ∧ out₁.halted = true ∧
     out₁.residualRegSecret = 0 ∧ out₁.residualStackSecret = 0 ∧
     out₁.stepsTaken = out₂.stepsTaken ∧
     out₁.archObsTrace ≠ out₂.archObsTrace) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro hEq
  injection hEq with hHd _
  injection hHd
  contradiction

/-- Counterexample 7b: Uses `specLoadUnmasked 0` then `ret`. -/
def badProg7b : List CtRing0Instr := [.specLoadUnmasked 0, .ret]
def badReq7b : CtAdmissionRequest :=
  { candidate := { bytes := encodeCtProg badProg7b, stackBound := 4 }, allowedHelpers := [] }
def badCert7b : CtExtensionCert :=
  { decodedProg := badProg7b, fuelBound := 2 }

theorem drop_ob7b_unsound :
    admitWithoutOb7b badReq7b badCert7b = true ∧
    admitCtKernelExtension badReq7b badCert7b = false ∧
    (let out₁ := runCtLoadedBytes badReq7b badCert7b.fuelBound true (initialCtRing0State 1 0 99)
     let out₂ := runCtLoadedBytes badReq7b badCert7b.fuelBound true (initialCtRing0State 1 42 99)
     out₁.faulted = false ∧ out₁.halted = true ∧
     out₁.archObsTrace = out₂.archObsTrace ∧
     out₁.residualRegSecret = 0 ∧ out₁.residualStackSecret = 0 ∧
     out₁.stepsTaken = out₂.stepsTaken ∧
     out₁.specObsTrace ≠ out₂.specObsTrace) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro hEq
  injection hEq with hHd _
  injection hHd
  contradiction

/-- Counterexample 7c: Spills secret to stack (`storeStackSecretSpill 0`) without scrubbing before `ret`. -/
def badProg7c : List CtRing0Instr := [.storeStackSecretSpill 0, .ret]
def badReq7c : CtAdmissionRequest :=
  { candidate := { bytes := encodeCtProg badProg7c, stackBound := 4 }, allowedHelpers := [] }
def badCert7c : CtExtensionCert :=
  { decodedProg := badProg7c, fuelBound := 2 }

theorem drop_ob7c_unsound :
    admitWithoutOb7c badReq7c badCert7c = true ∧
    admitCtKernelExtension badReq7c badCert7c = false ∧
    (let out₁ := runCtLoadedBytes badReq7c badCert7c.fuelBound true (initialCtRing0State 1 0 99)
     let out₂ := runCtLoadedBytes badReq7c badCert7c.fuelBound true (initialCtRing0State 1 42 99)
     out₂.faulted = false ∧ out₂.halted = true ∧
     out₁.archObsTrace = out₂.archObsTrace ∧
     out₁.specObsTrace = out₂.specObsTrace ∧
     out₁.stepsTaken = out₂.stepsTaken ∧
     out₂.residualStackSecret = 42) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Counterexample 7d: Uses `secretFuelDelay` then `ret` (leaking secret via total `stepsTaken`). -/
def badProg7d : List CtRing0Instr := [.secretFuelDelay, .ret]
def badReq7d : CtAdmissionRequest :=
  { candidate := { bytes := encodeCtProg badProg7d, stackBound := 4 }, allowedHelpers := [] }
def badCert7d : CtExtensionCert :=
  { decodedProg := badProg7d, fuelBound := 2 }

theorem drop_ob7d_unsound :
    admitWithoutOb7d badReq7d badCert7d = true ∧
    admitCtKernelExtension badReq7d badCert7d = false ∧
    (let out₁ := runCtLoadedBytes badReq7d badCert7d.fuelBound true (initialCtRing0State 1 0 99)
     let out₂ := runCtLoadedBytes badReq7d badCert7d.fuelBound true (initialCtRing0State 1 42 99)
     out₁.faulted = false ∧ out₁.halted = true ∧
     out₁.archObsTrace = out₂.archObsTrace ∧
     out₁.specObsTrace = out₂.specObsTrace ∧
     out₁.residualRegSecret = 0 ∧ out₁.residualStackSecret = 0 ∧
     out₂.residualRegSecret = 0 ∧ out₂.residualStackSecret = 0 ∧
     out₁.stepsTaken ≠ out₂.stepsTaken) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro hEq
  contradiction

/--
Master 4-Way Non-Redundancy Theorem (`anneal_ob7_four_subobligations_necessary`):
Each of the four sub-obligations `ob7a_archConstantTime`, `ob7b_speculativeConstantTime`,
`ob7c_secretExitAndSpillScrubbing`, and `ob7d_secretIndependentFuelTiming` is strictly
necessary for Ring-0 side-channel freedom: dropping any single sub-obligation while preserving
`ob1`–`ob6` and the other three `ob7` sub-obligations admits a concrete Ring-0 extension
that leaks secrets across one of the four orthogonal channels.
-/
theorem anneal_ob7_four_subobligations_necessary :
    (admitWithoutOb7a badReq7a badCert7a = true ∧
     (runCtLoadedBytes badReq7a badCert7a.fuelBound false (initialCtRing0State 1 0 99)).archObsTrace ≠
       (runCtLoadedBytes badReq7a badCert7a.fuelBound false (initialCtRing0State 1 42 99)).archObsTrace) ∧
    (admitWithoutOb7b badReq7b badCert7b = true ∧
     (runCtLoadedBytes badReq7b badCert7b.fuelBound true (initialCtRing0State 1 0 99)).specObsTrace ≠
       (runCtLoadedBytes badReq7b badCert7b.fuelBound true (initialCtRing0State 1 42 99)).specObsTrace) ∧
    (admitWithoutOb7c badReq7c badCert7c = true ∧
     (runCtLoadedBytes badReq7c badCert7c.fuelBound true (initialCtRing0State 1 42 99)).residualStackSecret = 42) ∧
    (admitWithoutOb7d badReq7d badCert7d = true ∧
     (runCtLoadedBytes badReq7d badCert7d.fuelBound true (initialCtRing0State 1 0 99)).stepsTaken ≠
       (runCtLoadedBytes badReq7d badCert7d.fuelBound true (initialCtRing0State 1 42 99)).stepsTaken) := by
  exact ⟨⟨drop_ob7a_unsound.1, drop_ob7a_unsound.2.2.2.2.2.2.2⟩,
         ⟨drop_ob7b_unsound.1, drop_ob7b_unsound.2.2.2.2.2.2.2.2⟩,
         ⟨drop_ob7c_unsound.1, drop_ob7c_unsound.2.2.2.2.2.2.2⟩,
         ⟨drop_ob7d_unsound.1, drop_ob7d_unsound.2.2.2.2.2.2.2.2.2.2⟩⟩

/-!
## Section 4: Mid-Execution Preemption Window vs. Bounded Non-Preemptible &
ISR-Scrubbed `Time Protection` (Ge et al. EuroSys 2019 §4.5)

Even if a Ring-0 extension satisfies `ob7c_secretExitAndSpillScrubbing` (overwriting all secret
registers and stack spill slots with `0` before `ret`), a hardware timer interrupt that preempts
the extension at an intermediate instruction PC `preemptStep < cert.fuelBound` (after loading a
secret into a scratch register or stack spill slot, but *before* the pre-`ret` scrub instructions
execute) exposes live secrets if the ISR switches domains naively!

We prove:
1. `mid_execution_preemption_bypasses_exit_scrub`:
   A concrete extension `goodScrubbedProg` that passes `admitCtKernelExtension` (`= true`) and
   scrubs all secrets to `0` at full completion (`fuel = 5`) leaves both `residualRegSecret = 42`
   and `residualStackSecret = 42` exposed when preempted mid-execution at `preemptStep = 2`!
2. `time_protected_isr_or_nonpreemptible_fuel_soundness`:
   Both (i) bounded non-preemptible execution within a timer tick (`natLe cert.fuelBound maxTickBudget = true`,
   Ge et al. EuroSys 2019 §4.5 timer-tick alignment) and (ii) preemptive ISR context-saving into a
   domain-private PCB paired with `sel4TimeProtectedSwitch` (`timeProtectedPreemptIsr`) preserve
   complete 2-safety noninterference and zero residual secrets across the domain boundary!
-/

/--
A valid, side-channel-free Ring-0 extension that computes in a secret register, spills to
`stack[0]`, scrubs both the scratch register and `stack[0]`, and returns.
-/
def goodScrubbedProg : List CtRing0Instr :=
  [.aluSecret, .storeStackSecretSpill 0, .scrubScratchRegs, .scrubStackSlot 0, .ret]

def goodScrubbedReq : CtAdmissionRequest :=
  { candidate := { bytes := encodeCtProg goodScrubbedProg, stackBound := 4 }
    allowedHelpers := [] }

def goodScrubbedCert : CtExtensionCert :=
  { decodedProg := goodScrubbedProg, fuelBound := 5 }

/--
Theorem (`mid_execution_preemption_bypasses_exit_scrub`):
1. `(goodScrubbedReq, goodScrubbedCert)` is admitted by the full 7-obligation gate
   (`admitCtKernelExtension goodScrubbedReq goodScrubbedCert = true`);
2. Running to normal completion (`fuel = 5`) zeroes both `residualRegSecret = 0` and
   `residualStackSecret = 0`;
3. Yet if a timer interrupt preempts execution at `preemptStep = 2` (after `.aluSecret` and
   `.storeStackSecretSpill 0`, before `.scrubScratchRegs` and `.scrubStackSlot 0` run) without
   ISR scrubbing, the interrupted CPU state exposes both `residualRegSecret = 42` and
   `residualStackSecret = 42`!
-/
theorem mid_execution_preemption_bypasses_exit_scrub :
    admitCtKernelExtension goodScrubbedReq goodScrubbedCert = true ∧
    (let fullOut :=
       runCtLoadedBytes goodScrubbedReq goodScrubbedCert.fuelBound false
         (initialCtRing0State 1 42 99)
     fullOut.halted = true ∧
     fullOut.residualRegSecret = 0 ∧
     fullOut.residualStackSecret = 0) ∧
    (let midOut :=
       runCtLoadedBytes goodScrubbedReq 2 false
         (initialCtRing0State 1 42 99)
     midOut.halted = false ∧
     midOut.residualRegSecret = 42 ∧
     midOut.residualStackSecret = 42) := by
  exact ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

/--
Discipline (i): Bounded Non-Preemptible Execution Within Timer Tick
(Ge et al. EuroSys 2019 §4.5 + Anneal `ob6_boundedFuelTermination`).
When `admitCtKernelExtension req cert && natLe cert.fuelBound maxTickBudget`, the extension is
guaranteed to reach `ret` within `maxTickBudget` steps before the timer interrupt unmasks.
-/
def runBoundedTickNonPreemptible
    (req : CtAdmissionRequest)
    (cert : CtExtensionCert)
    (maxTickBudget : Nat)
    (oracle : Bool)
    (st : CtRing0State) : Option CtRing0State :=
  if admitCtKernelExtension req cert && natLe cert.fuelBound maxTickBudget then
    some (runCtLoadedBytes req cert.fuelBound oracle st)
  else
    none

/--
Domain-private Process Control Block (`SavedDomainPcb`) residing in the domain's colored
`Kernel_Clone` memory partition (Ge et al. EuroSys 2019 Requirement 2).
-/
structure SavedDomainPcb where
  savedRegSecret : Nat
  savedStackSecret : Nat
  savedStepsTaken : Nat
  deriving DecidableEq, Repr

/--
Outcome of a `seL4` Time-Protected Preemptive ISR Context Switch (`timeProtectedPreemptIsr`):
- `savedPcb`: stores the preempted extension's live registers/stack in its private `Kernel_Clone` PCB;
- `nextDomainCpuState`: the scrubbed CPU state visible to the incoming domain;
- `nextDomainMu`: the flushed and cycle-padded `MicroArchState` visible to the incoming domain.
-/
structure PreemptSwitchOutcome where
  savedPcb : SavedDomainPcb
  nextDomainCpuState : CtRing0State
  nextDomainMu : MicroArchState
  deriving DecidableEq, Repr

/--
Discipline (ii): Time-Protected Preemptive ISR Context Switch (`timeProtectedPreemptIsr`).
When an extension is preempted at arbitrary instruction step `preemptStep`, the ISR:
1. Saves live `residualRegSecret` and `residualStackSecret` into the outgoing domain's private `SavedDomainPcb`;
2. Zeroes `residualRegSecret := 0` and `residualStackSecret := 0` and resets the CPU state for the
   next domain (`initialCtRing0State nextPubIn 0 nextCalleeSaved`);
3. Executes `sel4TimeProtectedSwitch baseClock worstCaseBudget` to flush `L1-D`/`L1-I`/`BPU` and
   pad `cycleClock` to `baseClock + worstCaseBudget`.
-/
def timeProtectedPreemptIsr
    (req : CtAdmissionRequest)
    (preemptStep baseClock worstCaseBudget nextPubIn nextCalleeSaved : Nat)
    (oracle : Bool)
    (st : CtRing0State) : PreemptSwitchOutcome :=
  let midSt := runCtLoadedBytes req preemptStep oracle st
  let dummyRes : DomExecResult :=
    { pubOut := 0
      archTrace := midSt.archObsTrace
      execCycles := midSt.stepsTaken
      dirtyCacheLines := midSt.residualStackSecret
      postMu := cleanMicroArchState (baseClock + midSt.stepsTaken) }
  { savedPcb :=
      { savedRegSecret := midSt.residualRegSecret
        savedStackSecret := midSt.residualStackSecret
        savedStepsTaken := midSt.stepsTaken }
    nextDomainCpuState := initialCtRing0State nextPubIn 0 nextCalleeSaved
    nextDomainMu := sel4TimeProtectedSwitch baseClock worstCaseBudget dummyRes }

/--
Theorem (`time_protected_isr_or_nonpreemptible_fuel_soundness`):
1. Under **Discipline (i) (Bounded Non-Preemptible Execution Within Timer Tick)**:
   For any `(req, cert)` with `admitCtKernelExtension req cert = true` and
   `natLe cert.fuelBound maxTickBudget = true`, executing `req` under `runBoundedTickNonPreemptible`
   completes prior to preemption (`halted = true`, `faulted = false`), zeroes all residual secrets
   (`residualRegSecret = 0 ∧ residualStackSecret = 0`), and guarantees full 2-safety noninterference
   (`archObsTrace`, `specObsTrace`, and `stepsTaken` identical for any `sec₁, sec₂`).
2. Under **Discipline (ii) (Time-Protected Preemptive ISR Context Switch)**:
   At *any* preemption step `preemptStep` (including mid-secret-computation `preemptStep = 2`),
   `timeProtectedPreemptIsr` preserves the outgoing domain's live secrets in its private `savedPcb`
   while guaranteeing that the CPU state (`nextDomainCpuState`) and microarchitectural state
   (`nextDomainMu`) exposed to the next scheduled domain have zero residual secrets and are
   100% identical across any `sec₁, sec₂`!
-/
theorem time_protected_isr_or_nonpreemptible_fuel_soundness
    (req : CtAdmissionRequest)
    (cert : CtExtensionCert)
    (maxTickBudget preemptStep baseClock worstCaseBudget pubIn sec₁ sec₂ calleeSaved : Nat)
    (oracle : Bool)
    (hAdmit : admitCtKernelExtension req cert = true)
    (hFit : natLe cert.fuelBound maxTickBudget = true) :
    (let s₁ := initialCtRing0State pubIn sec₁ calleeSaved
     let s₂ := initialCtRing0State pubIn sec₂ calleeSaved
     let out₁ := runCtLoadedBytes req cert.fuelBound oracle s₁
     let out₂ := runCtLoadedBytes req cert.fuelBound oracle s₂
     runBoundedTickNonPreemptible req cert maxTickBudget oracle s₁ = some out₁ ∧
     runBoundedTickNonPreemptible req cert maxTickBudget oracle s₂ = some out₂ ∧
     out₁.halted = true ∧ out₁.faulted = false ∧
     out₁.residualRegSecret = 0 ∧ out₁.residualStackSecret = 0 ∧
     out₁.archObsTrace = out₂.archObsTrace ∧
     out₁.specObsTrace = out₂.specObsTrace ∧
     out₁.stepsTaken = out₂.stepsTaken) ∧
    (let s₁ := initialCtRing0State pubIn sec₁ calleeSaved
     let s₂ := initialCtRing0State pubIn sec₂ calleeSaved
     let isr₁ := timeProtectedPreemptIsr req preemptStep baseClock worstCaseBudget pubIn calleeSaved oracle s₁
     let isr₂ := timeProtectedPreemptIsr req preemptStep baseClock worstCaseBudget pubIn calleeSaved oracle s₂
     isr₁.savedPcb.savedRegSecret = (runCtLoadedBytes req preemptStep oracle s₁).residualRegSecret ∧
     isr₁.savedPcb.savedStackSecret = (runCtLoadedBytes req preemptStep oracle s₁).residualStackSecret ∧
     isr₁.nextDomainCpuState.residualRegSecret = 0 ∧
     isr₁.nextDomainCpuState.residualStackSecret = 0 ∧
     isr₁.nextDomainCpuState = isr₂.nextDomainCpuState ∧
     isr₁.nextDomainMu = isr₂.nextDomainMu) := by
  have hSound :=
    anneal_ring0_ct_extension_admission_soundness req cert hAdmit pubIn sec₁ sec₂ calleeSaved oracle
  have hCond : (admitCtKernelExtension req cert && natLe cert.fuelBound maxTickBudget) = true := by
    rw [hAdmit, hFit]
    rfl
  have hRun₁ :
      runBoundedTickNonPreemptible req cert maxTickBudget oracle
        (initialCtRing0State pubIn sec₁ calleeSaved) =
      some (runCtLoadedBytes req cert.fuelBound oracle (initialCtRing0State pubIn sec₁ calleeSaved)) := by
    dsimp [runBoundedTickNonPreemptible]
    rw [hCond]
    rfl
  have hRun₂ :
      runBoundedTickNonPreemptible req cert maxTickBudget oracle
        (initialCtRing0State pubIn sec₂ calleeSaved) =
      some (runCtLoadedBytes req cert.fuelBound oracle (initialCtRing0State pubIn sec₂ calleeSaved)) := by
    dsimp [runBoundedTickNonPreemptible]
    rw [hCond]
    rfl
  refine ⟨⟨hRun₁, hRun₂, hSound.2.2.1, hSound.1, hSound.2.2.2.2.2.2.2.2.2.2.2.2.1,
           hSound.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hSound.2.2.2.2.2.2.2.2.2.2.1,
           hSound.2.2.2.2.2.2.2.2.2.2.2.1, hSound.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩,
          ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## Section 5: Axiom Audit (`#print axioms`) -/

#print axioms natEq_refl
#print axioms natEq_eq
#print axioms natLe_refl
#print axioms boolEq_eq
#print axioms band_eq_true
#print axioms natListEq_refl
#print axioms natListEq_eq
#print axioms cmov_to_branch_lowering_breaks_ct
#print axioms dead_store_elimination_breaks_secret_scrubbing
#print axioms secret_register_spill_breaks_memory_erasure
#print axioms ct_lockstep_simulation_preserves_ct_and_scrubbing
#print axioms stepTargetByteChecker_invariant
#print axioms runTargetByteCheckerLoop_invariant
#print axioms consumer_bound_machine_byte_ct_cert_defeats_bad_compiler
#print axioms isolated_ct_insufficient_across_context_switch
#print axioms unpadded_cache_flush_leaks_via_clock
#print axioms sel4_time_protection_compositional_noninterference
#print axioms sel4_time_protection_schedule_noninterference
#print axioms ctInstrEq_eq
#print axioms ctProgEq_eq
#print axioms optionCtProgEq_eq
#print axioms halted_runCtProgWithFuel
#print axioms runCtProgWithFuel_soundness_loop
#print axioms anneal_ring0_ct_extension_admission_soundness
#print axioms drop_ob7a_unsound
#print axioms drop_ob7b_unsound
#print axioms drop_ob7c_unsound
#print axioms drop_ob7d_unsound
#print axioms anneal_ob7_four_subobligations_necessary
#print axioms mid_execution_preemption_bypasses_exit_scrub
#print axioms time_protected_isr_or_nonpreemptible_fuel_soundness

end CompilerPreservationTimeProtectionAndAnnealCtGate
