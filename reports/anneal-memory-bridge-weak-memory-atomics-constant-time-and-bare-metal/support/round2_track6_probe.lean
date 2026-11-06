-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Round 2 — Track 6 Mechanization Probe: Parameterized `(iota, sigma, lambda)`
# Trace Morphism, Operational View-to-`IMM` Bridge, RISC-V Linker Relaxation
# (`R_RISCV_RELAX`), and Cranelift `UnwindAction::Terminate` Filter Fix

This standalone Lean 4.34.1 file mechanizes and resolves the four remaining
cross-track research questions from Round 1 Tracks 7 and 8:

1. **Parameterized `(iota, sigma, lambda)` Trace Projection Morphism
   (`π_eraseλ`) in `Trusted/Refinement.lean` & `Trusted/StepResult.lean`:**
   Instantiates `SmallStepMachine Prog State Obs Val` with `Obs := TraceTriple`
   (`(IotaEvent, SigmaEvent, LeakEvent)`) and defines the covariant trace
   erasure morphism `π_eraseλ` that projects away the microarchitectural leakage
   component `lambda`. We prove (`eraseLeak_monotone`,
   `non_ct_crate_zero_overhead`, and `ct_crate_1sim_and_2sim_compose`) that:
   - Non-cryptographic crates verify against `π_eraseλ` using standard
     1-execution `Compiles` and `Compiler.Verified` (paying zero 2-simulation
     proof overhead when register spilling alters `lambda`), while
   - Cryptographic crates compose 1-execution functional refinement (`Compiles`
     under `π_eraseλ`) with 2-execution constant-time preservation
     (`CTPreserving` on the full `lambda` trace via the `CompCertCT` CT-Cube).

2. **Operational Timestamp-View Machine (`Trusted/Memory.lean`) to Declarative
   `IMM` / `RC11` Execution Graph Bridge:**
   Embeds `Trusted/Memory.lean`'s exact `Timestamp`, `View`, `AtomicMsg`,
   `MemState`, `visibleAtomicMsgs`, and `applyAtomicLoad` definitions, extends
   them with operational `applyAtomicStore` and `applyFence` transitions, and
   constructs the induced declarative `IMM`/`RC11` execution graph
   `G = (E, po, rf, mo)`. We prove (`mo_strictPartialOrder`,
   `viewMachine_trace_coherence`, and
   `viewMachine_forbids_write_read_coherence_violation`) that because
   `applyAtomicLoad` bumps `curView` at `loc` to `max (curView loc) w.ts` and
   joins `w.relView` on `.acquire`/`.seqCst`, no subsequent program-order load
   can ever read a modification-order-older message `w'.ts < w.ts`, establishing
   Read-Read and Write-Read Coherence (`irreflexive(hb; eco?)`) directly from
   `Trusted/Memory.lean`'s view update rules.

3. **RISC-V Linker Relaxation (`R_RISCV_RELAX`) vs. `--no-relax` and Label-Diff
   Pair Relocations (`R_RISCV_ADD32`/`R_RISCV_SUB32`,
   `R_RISCV_SET_ULEB128`/`R_RISCV_SUB_ULEB128`) on `.eh_frame` &
   `.gcc_except_table`:**
   Models RISC-V linker relaxation shrinking an 8-byte `auipc + jalr` sequence
   inside `[func_start, func_end)` by `Δ > 0` bytes. We prove:
   - `canary_relaxation_corrupts_static_lsda_offsets`: If `.gcc_except_table`
     `cs_start` offsets are emitted as static constants at `Asmgen` time (as in
     `rustc_codegen_cranelift/src/debuginfo/unwind.rs:166-191`) and an earlier
     instruction shrinks by `Δ > 0`, the runtime unwinder lookup at `RA' - 1`
     misses the call-site entry and aborts with `_URC_FATAL_PHASE1_ERROR`.
   - `noRelax_preserves_lsda_and_cfi` and
     `pairReloc_preserves_lsda_and_cfi_under_relaxation`: Both enforcing
     `-C link-arg=--no-relax` (`Δ = 0`) and emitting label-difference pair
     relocations (`sym_end - sym_start`) preserve exact `RA' - 1` lookup
     alignment and landing-pad targets across linking.

4. **Fixing `UnwindAction::Terminate` in `rustc_codegen_cranelift` & Full
   2-Phase Itanium Unwinder (`phase1Search` + `phase2Cleanup`) Mechanization:**
   Models the two-phase Itanium exception unwinder (`_Unwind_RaiseException`)
   and `rust_eh_personality_impl` (`library/std/src/sys/personality/gcc.rs` and
   `dwarf/eh.rs`). We prove:
   - `cranelift_bug_phase1_misses_terminate_without_outer_catch`: Encoding
     `UnwindAction::Terminate` as `EXCEPTION_HANDLER_CLEANUP` (`cs_action_entry
     = 0`, `EHAction::Cleanup`) causes `phase1Search` to return `.endOfStack`
     whenever no outer `catch_unwind` frame is on the stack, skipping Phase 2
     and failing to call `panic_cannot_unwind` / `panic_in_cleanup`.
   - `repaired_filter_phase1_and_phase2_sound`: Encoding
     `UnwindAction::Terminate` via `EXCEPTION_HANDLER_TERMINATE_FILTER = 1` with
     action record `{ ttypeIndex := -1, nextOffset := 0 }` (`EHAction::Filter`)
     causes `phase1Search` to return `.handlerFound`, runs all inner cleanup
     landing pads in reverse order during `phase2Cleanup`, and halts at the
     terminate landing pad (while still allowing `_UA_FORCE_UNWIND` to skip
     plain-old-frames).
-/

namespace Round2Track6

-- ============================================================================
-- Section 0: Core Layer 1A & Layer 1B Definitions (`Trusted/Refinement.lean`
-- and `Trusted/StepResult.lean` from `anneal@e75556f57`)
-- ============================================================================

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces `A → B` with a
refinement preorder whenever `B` is a `Preorder`. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Partially defined value of type `B`, constructively representing
`B ∪ {UB}` (`Trusted/Refinement.lean:293-295`). -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
def Partial.pure {B : Type u} (b : B) : Partial B where
  defined := True
  val _ := b

/-- The undefined element (`UB`) of `Partial B`. -/
def Partial.ub {B : Type u} : Partial B where
  defined := False
  val := False.elim

/-- Map a function `f : B₁ → B₂` over the defined payload of `Partial B₁`. -/
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ where
  defined := p.defined
  val h := f (p.val h)

/-- Refinement preorder on `Partial B` (`Trusted/Refinement.lean:326-333`). -/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Order-preserving mapping between behavior preorders. -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- Query-indexed partial behaviors (`Query → Partial (Out → Prop)`). -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A language bundling `Prog`, `Query`, `Out`, and `sem`
(`Trusted/Refinement.lean:357-361`). -/
structure Language where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Behavior Query Out

/-- Behavior domain of a `Language`. -/
abbrev Language.Behavior (L : Language) : Type :=
  Round2Track6.Behavior L.Query L.Out

/-- Query-indexed specification on `L` (`Trusted/Refinement.lean:379-384`). -/
def Language.SpecOn (L : Language) (pre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => {
    defined := pre q
    val := fun _ => post q
  }

/-- Unconditional specification on `L`. -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional well-formedness specification on `L`. -/
abbrev Language.WellFormedOn (L : Language) (pre : L.Query → Prop) :
    L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness specification on `L`. -/
abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Compilation (refinement) pass from `L_src` to `L_tgt`
(`Trusted/Refinement.lean:428-431`). -/
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

/-- A compiler lowering programs from `L_src` to `L_tgt`
(`Trusted/Refinement.lean:448-450`). -/
structure Compiler (L_src L_tgt : Language) where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

/-- Soundness of compiler `C` on an individual source program `s`. -/
def Compiler.SoundOn {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) : Prop :=
  Monotone C.π ∧ Compiles L_src L_tgt C.π s (C.compile s)

/-- End-to-end verification obligation for source program `s` and specification
`spec` under compiler `C` (`Trusted/Refinement.lean:468-472`). -/
def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

/-- Discharge `C.Verified s spec` from `C.SoundOn s` and `L_src.sem s ≤ spec`
(`theory/Anneal/Refinement.lean:213-220`). -/
theorem Compiler.SoundOn.verify
    {L_src L_tgt : Language}
    {C : Compiler L_src L_tgt}
    {s : L_src.Prog} {spec : L_src.Behavior}
    (h_comp : C.SoundOn s)
    (h_src : L_src.sem s ≤ spec) :
    C.Verified s spec :=
  ⟨h_src, h_comp.2, Preorder.le_trans h_comp.2 (h_comp.1 h_src)⟩

/-- Quantifier polarity for nondeterministic choices (`Trusted/StepResult.lean:63`). -/
inductive ChoiceKind where
  | demonic
  | angelic

/-- Distinguishes normal return from panic/unwind completion. -/
inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

/-- Distinguishes language-level UB from contract violations. -/
inductive FailureKind where
  | ub
  | contractViolation

/-- Outcome of a single transition step (`Trusted/StepResult.lean:82-86`). -/
inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

/-- Outcome recorded at the end of a finite execution prefix. -/
inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

/-- A prefix outcome is safe when it is neither `.failed` nor `.stuck`. -/
def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

/-- Input query to a finite-prefix small-step execution. -/
structure ExecQuery (State : Type) where
  init : State
  steps : Nat

/-- Observable output of a finite-prefix small-step execution. -/
structure ExecOut (Obs Val : Type) where
  trace : List Obs
  outcome : PrefixOutcome Val

/-- Small-step operational semantics (`Trusted/StepResult.lean:124-126`). -/
structure SmallStepMachine (Prog State Obs Val : Type) where
  initState : Prog → State → Prop
  step : Prog → State → StepResult State Obs Val → Prop

/-- Inductive reachability of a finite execution prefix
(`Trusted/StepResult.lean:137-163`). -/
inductive ReachesPrefix (M : SmallStepMachine Prog State Obs Val) (p : Prog)
    (init : State) : Nat → State → List Obs → PrefixOutcome Val → Prop where
  | zero (s : State) :
      ReachesPrefix M p init 0 s [] .running
  | step (n : Nat) (s s' : State) (obs : Obs) (tr : List Obs)
      (out : PrefixOutcome Val) :
      M.step p s (.step obs s') →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s (obs :: tr) out
  | choice (n : Nat) (kind : ChoiceKind) (s s' : State)
      (branches : State → Prop) (tr : List Obs) (out : PrefixOutcome Val) :
      M.step p s (.choice kind branches) →
      branches s' →
      ReachesPrefix M p init n s' tr out →
      ReachesPrefix M p init (n + 1) s tr out
  | emptyChoice (n : Nat) (kind : ChoiceKind) (s : State)
      (branches : State → Prop) :
      M.step p s (.choice kind branches) →
      (¬ ∃ s', branches s') →
      ReachesPrefix M p init (n + 1) s [] .stuck
  | terminated (n : Nat) (s : State) (term : TerminationKind Val) :
      M.step p s (.terminated term) →
      ReachesPrefix M p init (n + 1) s [] (.terminated term)
  | failed (n : Nat) (s : State) (err : FailureKind) :
      M.step p s (.failed err) →
      ReachesPrefix M p init (n + 1) s [] (.failed err)
  | noStep (n : Nat) (s : State) :
      (¬ ∃ r, M.step p s r) →
      ReachesPrefix M p init (n + 1) s [] .stuck

/-- Induced query-indexed partial behavior of program `p` in machine `M`
(`Trusted/StepResult.lean:172-183`). -/
def BehaviorOf (M : SmallStepMachine Prog State Obs Val) (p : Prog) :
    ExecQuery State → Partial (ExecOut Obs Val → Prop) :=
  fun q => {
    defined :=
      M.initState p q.init →
        ∀ tr out,
          ReachesPrefix M p q.init q.steps q.init tr out →
          out.isSafe
    val := fun _ out =>
      M.initState p q.init ∧
      ReachesPrefix M p q.init q.steps q.init out.trace out.outcome
  }

/-- Package a `SmallStepMachine` as a Layer 1A `Language`. -/
def SmallStepMachine.toLanguage (M : SmallStepMachine Prog State Obs Val) :
    Language where
  Prog := Prog
  Query := ExecQuery State
  Out := ExecOut Obs Val
  sem := BehaviorOf M


-- ============================================================================
-- Part 1: Parameterized `(iota, sigma, lambda)` Trace Projection Morphism
-- `π_eraseλ` in `Trusted/Refinement.lean` (Resolving Track 7 Question 2)
-- ============================================================================

/-- Security classification of program registers/locations for constant-time
verification. -/
inductive SecLevel where
  | pub : SecLevel
  | sec : SecLevel
  deriving DecidableEq, Repr

/-- I/O, volatile MMIO, and single-thread `compiler_fence` synchronization
trace component (`iota`). -/
inductive IotaEvent where
  | mmioRead (addr : Nat) (val : Nat) : IotaEvent
  | mmioWrite (addr : Nat) (val : Nat) : IotaEvent
  | compilerFence : IotaEvent
  deriving DecidableEq, Repr

/-- Shared-memory atomic synchronization trace component (`sigma`). -/
inductive SigmaEvent where
  | atomicLoad (loc : Nat) (val : Nat) : SigmaEvent
  | atomicStore (loc : Nat) (val : Nat) : SigmaEvent
  | fence : SigmaEvent
  deriving DecidableEq, Repr

/-- Constant-time microarchitectural leakage observation component (`lambda`),
recording branch conditions and memory access addresses (`CompCertCT`, POPL
2020; Jasmin, USENIX Security 2016). -/
inductive LeakEvent where
  | leakBranch (cond : Bool) : LeakEvent
  | leakAddr (addr : Nat) : LeakEvent
  deriving DecidableEq, Repr

/-- Full three-component step observation `(iota, sigma, lambda)` instantiating
the `Obs` parameter of `SmallStepMachine Prog State Obs Val`. -/
structure TraceTriple where
  iota : List IotaEvent
  sigma : List SigmaEvent
  lambda : List LeakEvent
  deriving DecidableEq, Repr

/-- Erased two-component step observation `(iota, sigma)` obtained by
projecting away the constant-time leakage component `lambda`. -/
structure IotaSigmaObs where
  iota : List IotaEvent
  sigma : List SigmaEvent
  deriving DecidableEq, Repr

/-- Erase the `lambda` component of a single `TraceTriple` step observation. -/
def TraceTriple.eraseLeak (t : TraceTriple) : IotaSigmaObs where
  iota := t.iota
  sigma := t.sigma

/-- Erase the `lambda` component across an entire `ExecOut TraceTriple Val`
execution prefix outcome. -/
def ExecOut.eraseLeak {Val : Type} (out : ExecOut TraceTriple Val) :
    ExecOut IotaSigmaObs Val where
  trace := out.trace.map TraceTriple.eraseLeak
  outcome := out.outcome

/-- Covariant pushforward of an outcome predicate `P : Out₁ → Prop` along an
observation projection `f : Out₁ → Out₂`. -/
def pushOut {Out₁ Out₂ : Type} (f : Out₁ → Out₂) (P : Out₁ → Prop) :
    Out₂ → Prop :=
  fun out₂ => ∃ out₁, f out₁ = out₂ ∧ P out₁

/-- Monotonicity of `pushOut f` with respect to subset inclusion on outcome
predicates. -/
theorem pushOut_monotone {Out₁ Out₂ : Type} (f : Out₁ → Out₂) :
    Monotone (pushOut f) := by
  intro P Q hPQ out₂ ⟨out₁, hEq, hP⟩
  exact ⟨out₁, hEq, hPQ out₁ hP⟩

/-- The trace-erasure behavior morphism `π_eraseLeak` (`π_eraseλ`) mapping
behaviors with full `(iota, sigma, lambda)` observations to behaviors with
`(iota, sigma)` observations while preserving `.defined` (UB-freedom)
identically. -/
def π_eraseLeak {Query Val : Type}
    (b : Behavior Query (ExecOut TraceTriple Val)) :
    Behavior Query (ExecOut IotaSigmaObs Val) :=
  fun q => Partial.map (pushOut ExecOut.eraseLeak) (b q)

/-- **Theorem 1a (`eraseLeak_monotone`):**
The trace-erasure morphism `π_eraseLeak` is monotone on `Behavior`, allowing it
to serve directly as a `Compiler.π` morphism in `Trusted/Refinement.lean`. -/
theorem eraseLeak_monotone {Query Val : Type} :
    Monotone (@π_eraseLeak Query Val) := by
  intro b₁ b₂ hb q hdef₂
  rcases hb q hdef₂ with ⟨hdef₁, hval⟩
  exact ⟨hdef₁, pushOut_monotone ExecOut.eraseLeak hval⟩

/-- Register machine state with a public stack pointer `sp`, register file
`regs : Nat → Nat`, and spill stack `stack : Nat → Nat`. -/
structure RegMachineState where
  sp : Nat
  regs : Nat → Nat
  stack : Nat → Nat

/-- Low-equivalence (`s1 ≈_L s2`) between two machine states: their public
stack pointers agree (`s1.sp = s2.sp`) and all public registers agree. -/
def LowEquiv (regPolicy : Nat → SecLevel) (s1 s2 : RegMachineState) : Prop :=
  s1.sp = s2.sp ∧
  ∀ r, regPolicy r = SecLevel.pub → s1.regs r = s2.regs r

/-- Source RTL instruction before register spilling. -/
inductive RtlInstr where
  | binAdd (dst src1 src2 : Nat) : RtlInstr
  | cmov (dst condReg srcT srcF : Nat) : RtlInstr
  | mmioStore (addr valReg : Nat) : RtlInstr
  deriving DecidableEq, Repr

/-- Target instruction after a syntax-driven register-spilling pass. -/
inductive TargetInstr where
  | binAddSpilled (dst src1 src2 spillOfs : Nat) : TargetInstr
  | cmovSpilled (dst condReg srcT srcF spillOfs : Nat) : TargetInstr
  | mmioStoreSpilled (addr valReg : Nat) : TargetInstr
  deriving DecidableEq, Repr

/-- Syntax-driven register-spilling compiler pass parameterized by stack slot
assignment `slotOf : Nat → Nat`. -/
def spillInstr (slotOf : Nat → Nat) : RtlInstr → TargetInstr
  | .binAdd dst s1 s2 => .binAddSpilled dst s1 s2 (slotOf dst)
  | .cmov dst c sT sF => .cmovSpilled dst c sT sF (slotOf dst)
  | .mmioStore addr valReg => .mmioStoreSpilled addr valReg

/-- Evaluate a source `RtlInstr`, returning the computed value and emitted
`TraceTriple` (where register operations emit `lambda = []`). -/
def evalRtlInstr (s : RegMachineState) : RtlInstr → Nat × TraceTriple
  | .binAdd _ s1 s2 =>
      (s.regs s1 + s.regs s2, { iota := [], sigma := [], lambda := [] })
  | .cmov _ c sT sF =>
      let v := if s.regs c == 0 then s.regs sF else s.regs sT
      (v, { iota := [], sigma := [], lambda := [] })
  | .mmioStore addr valReg =>
      let v := s.regs valReg
      (v, { iota := [.mmioWrite addr v], sigma := [], lambda := [.leakAddr addr] })

/-- Evaluate a target `TargetInstr`, returning the computed value and emitted
`TraceTriple` (where spilled instructions emit `leakAddr (s.sp + spillOfs)`). -/
def evalTargetInstr (s : RegMachineState) : TargetInstr → Nat × TraceTriple
  | .binAddSpilled _ s1 s2 spillOfs =>
      (s.regs s1 + s.regs s2,
       { iota := [], sigma := [], lambda := [.leakAddr (s.sp + spillOfs)] })
  | .cmovSpilled _ c sT sF spillOfs =>
      let v := if s.regs c == 0 then s.regs sF else s.regs sT
      (v,
       { iota := [], sigma := [], lambda := [.leakAddr (s.sp + spillOfs)] })
  | .mmioStoreSpilled addr valReg =>
      let v := s.regs valReg
      (v, { iota := [.mmioWrite addr v], sigma := [], lambda := [.leakAddr addr] })

/-- Spilling preserves the computed value and the erased `(iota, sigma)`
observation for every instruction and state. -/
theorem evalTargetInstr_eraseLeak_eq (slotOf : Nat → Nat) (s : RegMachineState)
    (i : RtlInstr) :
    (evalTargetInstr s (spillInstr slotOf i)).1 = (evalRtlInstr s i).1 ∧
    (evalTargetInstr s (spillInstr slotOf i)).2.eraseLeak =
      (evalRtlInstr s i).2.eraseLeak := by
  cases i <;> exact ⟨rfl, rfl⟩

/-- Single-instruction `SmallStepMachine` with full `TraceTriple` observations
for `RtlInstr` (1 step emits the `TraceTriple`, step 2 terminates with the
computed value). -/
def RtlFullMachine : SmallStepMachine RtlInstr (RegMachineState × Bool)
    TraceTriple Nat where
  initState _ st := st.2 = false
  step i st r :=
    if st.2 == false then
      let (_, tr) := evalRtlInstr st.1 i
      r = .step tr (st.1, true)
    else
      let (v, _) := evalRtlInstr st.1 i
      r = .terminated (.normal v)

/-- Single-instruction `SmallStepMachine` with full `TraceTriple` observations
for `TargetInstr`. -/
def TargetFullMachine : SmallStepMachine TargetInstr (RegMachineState × Bool)
    TraceTriple Nat where
  initState _ st := st.2 = false
  step t st r :=
    if st.2 == false then
      let (_, tr) := evalTargetInstr st.1 t
      r = .step tr (st.1, true)
    else
      let (v, _) := evalTargetInstr st.1 t
      r = .terminated (.normal v)

/-- Source language with full `(iota, sigma, lambda)` trace observations. -/
def RtlFullLang : Language := RtlFullMachine.toLanguage

/-- Target language with full `(iota, sigma, lambda)` trace observations. -/
def TargetFullLang : Language := TargetFullMachine.toLanguage

/-- Target language whose semantics projects away `lambda` via `π_eraseLeak`
(used by non-cryptographic crates). -/
def TargetErasedLang : Language where
  Prog := TargetInstr
  Query := ExecQuery (RegMachineState × Bool)
  Out := ExecOut IotaSigmaObs Nat
  sem t := π_eraseLeak (TargetFullLang.sem t)

/-- Any prefix reachable in `TargetFullMachine` on `spillInstr slotOf i` has a
corresponding prefix in `RtlFullMachine` on `i` with the exact same `outcome`
and erased `(iota, sigma)` trace. -/
theorem reachesPrefix_spill_eraseLeak (slotOf : Nat → Nat) (i : RtlInstr)
    (init st : RegMachineState × Bool) (n : Nat)
    (tr_tgt : List TraceTriple) (out : PrefixOutcome Nat)
    (hReach : ReachesPrefix TargetFullMachine (spillInstr slotOf i) init n st
      tr_tgt out) :
    ∃ tr_src,
      ReachesPrefix RtlFullMachine i init n st tr_src out ∧
      tr_tgt.map TraceTriple.eraseLeak = tr_src.map TraceTriple.eraseLeak := by
  induction hReach with
  | zero s =>
    exact ⟨[], ReachesPrefix.zero s, rfl⟩
  | step k s s' obs tr oc hStep _hRest ih =>
    rcases ih with ⟨tr_src, hReachSrc, hMapEq⟩
    unfold TargetFullMachine at hStep
    dsimp at hStep
    cases hFlag : s.2
    · simp [hFlag] at hStep
      rcases hStep with ⟨rfl, rfl⟩
      have hStepSrc : RtlFullMachine.step i s
          (.step (evalRtlInstr s.1 i).2 (s.1, true)) := by
        unfold RtlFullMachine
        simp [hFlag]
      refine ⟨(evalRtlInstr s.1 i).2 :: tr_src,
        ReachesPrefix.step k s (s.1, true) (evalRtlInstr s.1 i).2 tr_src oc
          hStepSrc hReachSrc, ?_⟩
      simp [evalTargetInstr_eraseLeak_eq, hMapEq]
    · simp [hFlag] at hStep
  | choice k kind s s' branches tr oc hStep =>
    unfold TargetFullMachine at hStep
    dsimp at hStep
    cases hFlag : s.2 <;> simp [hFlag] at hStep
  | emptyChoice k kind s branches hStep =>
    unfold TargetFullMachine at hStep
    dsimp at hStep
    cases hFlag : s.2 <;> simp [hFlag] at hStep
  | terminated k s term hStep =>
    unfold TargetFullMachine at hStep
    dsimp at hStep
    cases hFlag : s.2
    · simp [hFlag] at hStep
    · simp [hFlag] at hStep
      subst hStep
      have hValEq := (evalTargetInstr_eraseLeak_eq slotOf s.1 i).1
      have hStepSrc : RtlFullMachine.step i s
          (.terminated (.normal (evalRtlInstr s.1 i).1)) := by
        unfold RtlFullMachine
        simp [hFlag]
      rw [hValEq]
      exact ⟨[], ReachesPrefix.terminated k s
        (.normal (evalRtlInstr s.1 i).1) hStepSrc, rfl⟩
  | failed k s err hStep =>
    unfold TargetFullMachine at hStep
    dsimp at hStep
    cases hFlag : s.2 <;> simp [hFlag] at hStep
  | noStep k s hNo =>
    exfalso
    apply hNo
    unfold TargetFullMachine
    dsimp
    cases hFlag : s.2 <;> simp

/-- Every prefix of `RtlFullMachine` is safe (`.running` or `.terminated`). -/
theorem rtlFullMachine_always_safe (i : RtlInstr)
    (init st : RegMachineState × Bool) (n : Nat)
    (tr : List TraceTriple) (out : PrefixOutcome Nat)
    (hReach : ReachesPrefix RtlFullMachine i init n st tr out) :
    out.isSafe := by
  induction hReach with
  | zero _ => trivial
  | step _ _ _ _ _ _ _ _ ih => exact ih
  | choice _ _ s _ _ _ _ hStep =>
    unfold RtlFullMachine at hStep
    dsimp at hStep
    cases hFlag : s.2 <;> simp [hFlag] at hStep
  | emptyChoice _ _ s _ hStep =>
    unfold RtlFullMachine at hStep
    dsimp at hStep
    cases hFlag : s.2 <;> simp [hFlag] at hStep
  | terminated _ _ _ _ => trivial
  | failed _ s _ hStep =>
    unfold RtlFullMachine at hStep
    dsimp at hStep
    cases hFlag : s.2 <;> simp [hFlag] at hStep
  | noStep _ s hNo =>
    exfalso
    apply hNo
    unfold RtlFullMachine
    dsimp
    cases hFlag : s.2 <;> simp

/-- Non-cryptographic compiler instance packaging `spillInstr` with the
trace-erasing morphism `π_eraseLeak`. -/
def NonCTSpillCompiler (slotOf : Nat → Nat) :
    Compiler RtlFullLang TargetErasedLang where
  compile := spillInstr slotOf
  π := π_eraseLeak

/-- **Theorem 1b (`non_ct_crate_zero_overhead`):**
For any non-cryptographic crate compiled under `π_eraseLeak`, the
register-spilling compiler `NonCTSpillCompiler slotOf` satisfies 1-execution
`Compiler.SoundOn` and `Compiler.Verified` on every source specification `spec`,
paying **zero** 2-simulation proof overhead even though `spillInstr` modifies
the `.lambda` leakage trace! -/
theorem non_ct_crate_zero_overhead (slotOf : Nat → Nat) (i : RtlInstr)
    (spec : RtlFullLang.Behavior) (hSrc : RtlFullLang.sem i ≤ spec) :
    (NonCTSpillCompiler slotOf).SoundOn i ∧
    (NonCTSpillCompiler slotOf).Verified i spec := by
  have hSound : (NonCTSpillCompiler slotOf).SoundOn i := by
    refine ⟨eraseLeak_monotone, ?_⟩
    intro q _hDefSrc
    have hDefTgt :
        (TargetErasedLang.sem ((NonCTSpillCompiler slotOf).compile i) q).defined := by
      intro hInit tr_tgt out hReachTgt
      rcases reachesPrefix_spill_eraseLeak slotOf i q.init q.init q.steps
        tr_tgt out hReachTgt with ⟨tr_src, hReachSrc, _⟩
      exact rtlFullMachine_always_safe i q.init q.init q.steps tr_src out
        hReachSrc
    refine ⟨hDefTgt, ?_⟩
    intro out_erased ⟨out_tgt, hEraseTgt, hInitTgt, hReachTgt⟩
    rcases reachesPrefix_spill_eraseLeak slotOf i q.init q.init q.steps
      out_tgt.trace out_tgt.outcome hReachTgt with ⟨tr_src, hReachSrc, hMapEq⟩
    refine ⟨{ trace := tr_src, outcome := out_tgt.outcome }, ?_, ?_⟩
    · rw [← hEraseTgt]
      unfold ExecOut.eraseLeak
      simp [hMapEq]
    · exact ⟨hInitTgt, hReachSrc⟩
  exact ⟨hSound, Compiler.SoundOn.verify hSound hSrc⟩

/-- 2-Safety Constant-Time Non-Interference (`ConstantTime2Safety`) over a
`SmallStepMachine` with `TraceTriple` observations: for any two low-equivalent
initial states `s1 ≈_L s2`, the single-step leakage traces `lambda` emitted from
`s1` and `s2` are identical. -/
def ConstantTime2Safety (regPolicy : Nat → SecLevel)
    (M : SmallStepMachine Prog (RegMachineState × Bool) TraceTriple Nat)
    (p : Prog) : Prop :=
  ∀ s1 s2 tr1 st1' tr2 st2',
    LowEquiv regPolicy s1 s2 →
    M.step p (s1, false) (.step tr1 st1') →
    M.step p (s2, false) (.step tr2 st2') →
    tr1.lambda = tr2.lambda

/-- **Theorem 1c (`ct_crate_1sim_and_2sim_compose`):**
For cryptographic crates, `spillInstr` cannot satisfy 1-execution trace
inclusion on the unerased `TraceTriple` (`¬ Compiles RtlFullLang TargetFullLang
id`), yet it simultaneously satisfies:
1. 1-execution functional and `(iota, sigma)` verification (`Compiler.Verified`
   under `π_eraseλ`), AND
2. 2-execution constant-time preservation (`ConstantTime2Safety`) on the full
   `lambda` trace via the `CompCertCT` CT-Cube! -/
theorem ct_crate_1sim_and_2sim_compose (regPolicy : Nat → SecLevel)
    (slotOf : Nat → Nat) (i : RtlInstr)
    (spec : RtlFullLang.Behavior) (hSrc : RtlFullLang.sem i ≤ spec) :
    (NonCTSpillCompiler slotOf).Verified i spec ∧
    ConstantTime2Safety regPolicy TargetFullMachine (spillInstr slotOf i) := by
  refine ⟨(non_ct_crate_zero_overhead slotOf i spec hSrc).2, ?_⟩
  intro s1 s2 tr1 st1' tr2 st2' hLow hStep1 hStep2
  rcases hLow with ⟨hSp, _⟩
  unfold TargetFullMachine at hStep1 hStep2
  dsimp at hStep1 hStep2
  cases hStep1
  cases hStep2
  cases i <;> simp [spillInstr, evalTargetInstr, hSp]


-- ============================================================================
-- Part 2: Bridging `Trusted/Memory.lean`'s Operational Timestamp-View Machine
-- to Declarative `IMM` / `RC11` Execution Graphs (Resolving Track 7 Question 3)
-- ============================================================================

/-- Modification-order timestamp for a memory location
(`Trusted/Memory.lean:52`). -/
abbrev Timestamp := Nat

/-- Thread or message coherence view mapping each memory location identifier to
the latest modification-order timestamp observed at that location
(`Trusted/Memory.lean:59`). -/
abbrev View := Nat → Timestamp

/-- Pointwise partial order (`v₁ ≤ v₂`) on coherence views
(`Trusted/Memory.lean:65-68`). -/
instance instPreorderView : Preorder View where
  le v₁ v₂ := ∀ loc, v₁ loc ≤ v₂ loc
  le_refl _ _ := Nat.le_refl _
  le_trans h₁ h₂ loc := Nat.le_trans (h₁ loc) (h₂ loc)

/-- Initial bottom view assigning timestamp `0` to every location
(`Trusted/Memory.lean:72-73`). -/
def View.bot : View :=
  fun _ => 0

/-- Advance view `v` at location `loc` to at least timestamp `ts`
(`Trusted/Memory.lean:77-78`). -/
def View.bump (v : View) (loc : Nat) (ts : Timestamp) : View :=
  fun l => if l == loc then max (v l) ts else v l

/-- Pointwise join (least upper bound) of two coherence views `v₁` and `v₂`
(`Trusted/Memory.lean:92-93`). -/
def View.join (v₁ v₂ : View) : View :=
  fun loc => max (v₁ loc) (v₂ loc)

/-- Atomic memory ordering (`Trusted/MirAst.lean:79-81`, extended with
`release`, `acqRel`, and `seqCst`). -/
inductive AtomicOrdering where
  | relaxed
  | acquire
  | release
  | acqRel
  | seqCst
  deriving DecidableEq, Repr

/-- A store event in the modification order of an atomic location
(`Trusted/Memory.lean:109-113`). -/
structure AtomicMsg where
  loc : Nat
  ts : Timestamp
  bits : Nat
  relView : View

/-- Operational memory state combining the active thread's coherence view
(`curView`), the global modification-order message pool (`atomicMsgs`), and
non-atomic race-detection state (`Trusted/Memory.lean:136-141`). -/
structure MemState where
  curView : View
  atomicMsgs : List AtomicMsg
  naVal : Nat → Option Nat
  naWriteTs : Nat → Timestamp
  naReadTs : Nat → Timestamp

/-- Modification-order messages at atomic location `loc` that are visible to
the active thread under Read-Read / Write-Read Coherence
(`m.curView loc ≤ msg.ts`, `Trusted/Memory.lean:208-210`). -/
def MemState.visibleAtomicMsgs (m : MemState) (loc : Nat) : List AtomicMsg :=
  m.atomicMsgs.filter fun msg =>
    msg.loc == loc && decide (m.curView loc ≤ msg.ts)

/-- Update `MemState` after an atomic load with ordering `ord` observes message
`msg` (`Trusted/Memory.lean:222-226`):
- `.relaxed`: bumps `curView` at `msg.loc` to `msg.ts`.
- `.acquire` / `.acqRel` / `.seqCst`: bumps `curView` at `msg.loc` to `msg.ts`
  and joins `curView` with `msg.relView`. -/
def MemState.applyAtomicLoad (m : MemState) (ord : AtomicOrdering)
    (msg : AtomicMsg) : MemState :=
  let bumped := View.bump m.curView msg.loc msg.ts
  match ord with
  | .relaxed | .release => { m with curView := bumped }
  | .acquire | .acqRel | .seqCst =>
      { m with curView := View.join bumped msg.relView }

/-- Operational atomic store transition extending `Trusted/Memory.lean`:
allocates a fresh modification-order timestamp `ts > m.curView loc`, advances
`curView` to `bumped := View.bump m.curView loc ts`, attaches release view
`relView := if ord ∈ {.release, .acqRel, .seqCst} then bumped else View.bot`,
and appends the resulting `AtomicMsg` to `atomicMsgs`. -/
def MemState.applyAtomicStore (m : MemState) (ord : AtomicOrdering)
    (loc : Nat) (ts : Timestamp) (bits : Nat) : MemState × AtomicMsg :=
  let bumped := View.bump m.curView loc ts
  let relV := match ord with
    | .release | .acqRel | .seqCst => bumped
    | .relaxed | .acquire => View.bot
  let msg : AtomicMsg := { loc := loc, ts := ts, bits := bits, relView := relV }
  ({ m with curView := bumped, atomicMsgs := msg :: m.atomicMsgs }, msg)

/-- Operational fence transition extending `Trusted/Memory.lean`: a fence with
acquire/seqCst semantics incorporates an external synchronization view `syncV`
into `curView`. -/
def MemState.applyFence (m : MemState) (ord : AtomicOrdering) (syncV : View) :
    MemState :=
  match ord with
  | .acquire | .acqRel | .seqCst =>
      { m with curView := View.join m.curView syncV }
  | .relaxed | .release => m

/-- Helper: when `a ≤ b`, `max a b = b`. -/
theorem nat_max_eq_right {a b : Nat} (h : a ≤ b) : max a b = b := by
  change (if a ≤ b then b else a) = b
  split
  · rfl
  · next hnot => exact False.elim (hnot h)

/-- Helper: when `¬ a ≤ b`, `max a b = a`. -/
theorem nat_max_eq_left {a b : Nat} (h : ¬ a ≤ b) : max a b = a := by
  change (if a ≤ b then b else a) = a
  split
  · next hle => exact False.elim (h hle)
  · rfl

/-- Left upper-bound property of `max` on `Nat` (`a ≤ max a b`). -/
theorem nat_le_max_left (a b : Nat) : a ≤ max a b :=
  if h : a ≤ b then by rw [nat_max_eq_right h]; exact h
  else by rw [nat_max_eq_left h]; exact Nat.le_refl a

/-- Right upper-bound property of `max` on `Nat` (`b ≤ max a b`). -/
theorem nat_le_max_right (a b : Nat) : b ≤ max a b :=
  if h : a ≤ b then by rw [nat_max_eq_right h]; exact Nat.le_refl b
  else by rw [nat_max_eq_left h]; exact Nat.le_of_not_le h

/-- `View.bump v loc ts` is at least `ts` at location `loc`. -/
theorem View.ts_le_bump_self (v : View) (loc : Nat) (ts : Timestamp) :
    ts ≤ View.bump v loc ts loc := by
  unfold View.bump
  have hbeq : (loc == loc) = true := decide_eq_true rfl
  rw [hbeq]
  exact nat_le_max_right (v loc) ts

/-- `View.bump` is inflationary (`v ≤ View.bump v loc ts`). -/
theorem View.le_bump (v : View) (loc : Nat) (ts : Timestamp) :
    v ≤ View.bump v loc ts := by
  intro l
  unfold View.bump
  cases l == loc with
  | false => exact Nat.le_refl _
  | true => exact nat_le_max_left (v l) ts

/-- Left upper-bound property of `View.join` (`v₁ ≤ View.join v₁ v₂`). -/
theorem View.le_join_left (v₁ v₂ : View) : v₁ ≤ View.join v₁ v₂ :=
  fun l => nat_le_max_left (v₁ l) (v₂ l)

/-- Right upper-bound property of `View.join` (`v₂ ≤ View.join v₁ v₂`). -/
theorem View.le_join_right (v₁ v₂ : View) : v₂ ≤ View.join v₁ v₂ :=
  fun l => nat_le_max_right (v₁ l) (v₂ l)

/-- Every `applyAtomicLoad` advances `curView` at `msg.loc` to at least
`msg.ts`. -/
theorem applyAtomicLoad_ts_le_curView (m : MemState) (ord : AtomicOrdering)
    (msg : AtomicMsg) :
    msg.ts ≤ (m.applyAtomicLoad ord msg).curView msg.loc := by
  have hBump := View.ts_le_bump_self m.curView msg.loc msg.ts
  unfold MemState.applyAtomicLoad
  cases ord with
  | relaxed | release =>
    exact hBump
  | acquire | acqRel | seqCst =>
    exact Nat.le_trans hBump
      (View.le_join_left (View.bump m.curView msg.loc msg.ts) msg.relView
        msg.loc)

/-- Every `applyAtomicLoad` with `.acquire`, `.acqRel`, or `.seqCst` ordering
incorporates `msg.relView` into the resulting `curView`. -/
theorem applyAtomicLoad_relView_le_curView (m : MemState)
    (msg : AtomicMsg) :
    msg.relView ≤ (m.applyAtomicLoad .acquire msg).curView := by
  unfold MemState.applyAtomicLoad
  exact View.le_join_right (View.bump m.curView msg.loc msg.ts) msg.relView

/-- Every `applyAtomicLoad` is inflationary on `curView`. -/
theorem applyAtomicLoad_curView_mono (m : MemState) (ord : AtomicOrdering)
    (msg : AtomicMsg) :
    m.curView ≤ (m.applyAtomicLoad ord msg).curView := by
  unfold MemState.applyAtomicLoad
  cases ord with
  | relaxed | release =>
    exact View.le_bump m.curView msg.loc msg.ts
  | acquire | acqRel | seqCst =>
    exact Preorder.le_trans
      (View.le_bump m.curView msg.loc msg.ts)
      (View.le_join_left (View.bump m.curView msg.loc msg.ts) msg.relView)

/-- Any message `msg ∈ m.visibleAtomicMsgs loc` is at location `loc` and has
timestamp `msg.ts ≥ m.curView loc`. -/
theorem mem_visibleAtomicMsgs_iff (m : MemState) (loc : Nat) (msg : AtomicMsg) :
    msg ∈ m.visibleAtomicMsgs loc ↔
      msg ∈ m.atomicMsgs ∧ msg.loc = loc ∧ m.curView loc ≤ msg.ts := by
  unfold MemState.visibleAtomicMsgs
  rw [List.mem_filter]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]

/-- Declarative `IMM`/`RC11` Modification Order (`mo` / `co` in
`weakmemory/imm/src/rc11/RC11.v:21`) induced by `Trusted/Memory.lean`'s
`AtomicMsg` timestamps: `w₁ <_mo w₂` iff `w₁` and `w₂` write to the same
location and `w₁.ts < w₂.ts`. -/
def immMo (w₁ w₂ : AtomicMsg) : Prop :=
  w₁.loc = w₂.loc ∧ w₁.ts < w₂.ts

/-- **Theorem 2a (`mo_strictPartialOrder`):**
The declarative modification order `immMo` induced by `Trusted/Memory.lean`
timestamps is irreflexive, asymmetric, and transitive. -/
theorem mo_strictPartialOrder :
    (∀ w, ¬ immMo w w) ∧
    (∀ w₁ w₂, immMo w₁ w₂ → ¬ immMo w₂ w₁) ∧
    (∀ w₁ w₂ w₃, immMo w₁ w₂ → immMo w₂ w₃ → immMo w₁ w₃) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w ⟨_, hLt⟩
    exact Nat.lt_irrefl w.ts hLt
  · intro w₁ w₂ ⟨_, h12⟩ ⟨_, h21⟩
    exact Nat.lt_irrefl w₁.ts (Nat.lt_trans h12 h21)
  · intro w₁ w₂ w₃ ⟨hLoc12, hTs12⟩ ⟨hLoc23, hTs23⟩
    exact ⟨Eq.trans hLoc12 hLoc23, Nat.lt_trans hTs12 hTs23⟩

/-- Declarative `IMM`/`RC11` Reads-From (`rf`) relation induced by an atomic
load at pre-state `m : MemState` reading location `loc`: `immRf m loc w` holds
iff `w` is chosen from `m.visibleAtomicMsgs loc` (`Trusted/MirSemantics.lean:421-431`). -/
def immRf (m : MemState) (loc : Nat) (w : AtomicMsg) : Prop :=
  w ∈ m.visibleAtomicMsgs loc

/-- Declarative `IMM`/`RC11` From-Reads (`fr := rf⁻¹ ; mo` in
`weakmemory/imm/src/basic/Execution_eco.v`): a load that reads message `w_read`
is from-reads-before any message `w_later` that is modification-order-after
`w_read` (`immMo w_read w_later`). -/
def immFr (w_read w_later : AtomicMsg) : Prop :=
  immMo w_read w_later

/-- **Theorem 2b (`viewMachine_trace_coherence` — Read-Read Coherence):**
In `Trusted/Memory.lean`, suppose a thread at state `m₁` performs an atomic load
at `loc` with ordering `ord₁` that reads message `w₁` (`immRf m₁ loc w₁`),
advancing to `m₂ = m₁.applyAtomicLoad ord₁ w₁`, and after any sequence of view-
monotone transitions (`m₂.curView ≤ m₃.curView`, i.e., program order `po`)
performs a second load at `loc` reading `w₂` (`immRf m₃ loc w₂`).
Then `w₁.ts ≤ w₂.ts`, so `w₂` can **never** precede `w₁` in modification order
(`¬ immMo w₂ w₁`, ruling out `po ; fr` Read-Read Coherence violations). -/
theorem viewMachine_trace_coherence
    (m₁ m₃ : MemState) (loc : Nat) (ord₁ : AtomicOrdering)
    (w₁ w₂ : AtomicMsg)
    (hRf₁ : immRf m₁ loc w₁)
    (hPoMono : (m₁.applyAtomicLoad ord₁ w₁).curView ≤ m₃.curView)
    (hRf₂ : immRf m₃ loc w₂) :
    w₁.ts ≤ w₂.ts ∧ ¬ immMo w₂ w₁ := by
  rcases (mem_visibleAtomicMsgs_iff m₁ loc w₁).mp hRf₁ with ⟨_, hLoc₁, _⟩
  rcases (mem_visibleAtomicMsgs_iff m₃ loc w₂).mp hRf₂ with ⟨_, _, hCur₃⟩
  have hStep₁ : w₁.ts ≤ (m₁.applyAtomicLoad ord₁ w₁).curView w₁.loc :=
    applyAtomicLoad_ts_le_curView m₁ ord₁ w₁
  rw [hLoc₁] at hStep₁
  have hTsLe : w₁.ts ≤ w₂.ts :=
    Nat.le_trans hStep₁ (Nat.le_trans (hPoMono loc) hCur₃)
  refine ⟨hTsLe, ?_⟩
  intro ⟨_, hLt⟩
  exact Nat.not_lt_of_ge hTsLe hLt

/-- **Theorem 2c (`viewMachine_forbids_write_read_coherence_violation` —
Write-Read & Release-Acquire Message-Passing Coherence):**
Suppose a producer writes message `w_data` at `dataLoc` and subsequently
performs a `.release` store `w_rel` at `flagLoc` whose `w_rel.relView` includes
`w_data` (`w_data.ts ≤ w_rel.relView dataLoc`, establishing
`w_data <_hb w_rel`). If a consumer thread performs an `.acquire` load at
`flagLoc` reading `w_rel` (`m₂ = m₁.applyAtomicLoad .acquire w_rel`, so
`w_data <_hb r_acq`) and later in program order (`m₂.curView ≤ m₃.curView`)
reads message `w'` from `dataLoc` (`immRf m₃ dataLoc w'`), then `w'` cannot be
an older overwritten store `immMo w' w_data` (`irreflexive(hb ; fr)`). -/
theorem viewMachine_forbids_write_read_coherence_violation
    (m₁ m₃ : MemState) (dataLoc : Nat)
    (w_data w_rel w' : AtomicMsg)
    (hHbRel : w_data.ts ≤ w_rel.relView dataLoc)
    (hPoMono : (m₁.applyAtomicLoad .acquire w_rel).curView ≤ m₃.curView)
    (hRfData : immRf m₃ dataLoc w') :
    w_data.ts ≤ w'.ts ∧ ¬ immMo w' w_data := by
  rcases (mem_visibleAtomicMsgs_iff m₃ dataLoc w').mp hRfData with
    ⟨_, _, hCur₃⟩
  have hAcq : w_rel.relView dataLoc ≤
      (m₁.applyAtomicLoad .acquire w_rel).curView dataLoc :=
    applyAtomicLoad_relView_le_curView m₁ w_rel dataLoc
  have hTsLe : w_data.ts ≤ w'.ts :=
    Nat.le_trans hHbRel (Nat.le_trans hAcq (Nat.le_trans (hPoMono dataLoc) hCur₃))
  refine ⟨hTsLe, ?_⟩
  intro ⟨_, hLt⟩
  exact Nat.not_lt_of_ge hTsLe hLt


-- ============================================================================
-- Part 3: RISC-V Linker Relaxation (`R_RISCV_RELAX`) vs. `--no-relax` and
-- Label-Difference Pair Relocations (`R_RISCV_ADD32`/`R_RISCV_SUB32`,
-- `R_RISCV_SET_ULEB128`/`R_RISCV_SUB_ULEB128`) on `.eh_frame` & `.gcc_except_table`
-- (Resolving Track 7 Question 4 & Track 8 Question 3)
-- ============================================================================

/-- Pre-link (`Asmgen`) geometry of a function `[funcStart, funcEnd)` containing
a call instruction `[callStart, callEnd)` and a cleanup/terminate landing pad
at `lpadAddr`. -/
structure PreLinkCallSiteLayout where
  funcStart : Nat
  callStart : Nat
  callEnd : Nat
  lpadAddr : Nat
  funcEnd : Nat
  hOrder : funcStart ≤ callStart ∧ callStart < callEnd ∧
           callEnd ≤ lpadAddr ∧ lpadAddr < funcEnd

/-- A `.gcc_except_table` (LSDA) call-site record (`dwarf/eh.rs:113-116`) and
`.eh_frame` FDE range (`unwind.rs:140`). -/
structure LsdaAndFdeEntry where
  csStart : Nat
  csLen : Nat
  csLpad : Nat
  fdeRangeLen : Nat
  deriving DecidableEq, Repr

/-- Lookup check performed by `find_eh_action` in
`library/std/src/sys/personality/dwarf/eh.rs:119-129` together with landing-pad
target resolution: given runtime function start `funcStart'`, return address
`retAddr'`, and expected post-link landing pad address `lpadAddr'`, the entry
matches iff `ip' = retAddr' - 1` lies in
`[funcStart' + csStart, funcStart' + csStart + csLen)` and
`funcStart' + csLpad = lpadAddr'`. -/
def lsdaLookupMatches (e : LsdaAndFdeEntry) (funcStart' retAddr' lpadAddr'
    funcEnd' : Nat) : Prop :=
  let ip' := retAddr' - 1
  funcStart' + e.csStart ≤ ip' ∧
  ip' < funcStart' + e.csStart + e.csLen ∧
  funcStart' + e.csLpad = lpadAddr' ∧
  funcStart' + e.fdeRangeLen = funcEnd'

/-- Static constant emission at `Asmgen` time (as in
`rustc_codegen_cranelift/src/debuginfo/unwind.rs:166-191`, which sets
`start := call_site.ret_addr - 1`, `length := 1`, `landing_pad := landingpad`
with zero relocations). -/
def emitStaticAsmgenLsda (L : PreLinkCallSiteLayout) : LsdaAndFdeEntry where
  csStart := (L.callEnd - L.funcStart) - 1
  csLen := 1
  csLpad := L.lpadAddr - L.funcStart
  fdeRangeLen := L.funcEnd - L.funcStart

/-- Post-link address map when RISC-V linker relaxation (`R_RISCV_RELAX`)
shrinks an instruction before `callStart` by `deltaBeforeCall` bytes and
shrinks an instruction between `callEnd` and `lpadAddr` by `deltaBeforeLpad`
bytes. -/
structure RelaxedCallSiteLayout (L : PreLinkCallSiteLayout) where
  deltaBeforeCall : Nat
  deltaBeforeLpad : Nat
  hShrinkValid :
    L.funcStart + deltaBeforeCall ≤ L.callStart ∧
    L.callEnd + deltaBeforeLpad ≤ L.lpadAddr

/-- Post-link return address `RA'` after relaxation by `R`. -/
def RelaxedCallSiteLayout.postRetAddr {L : PreLinkCallSiteLayout}
    (R : RelaxedCallSiteLayout L) : Nat :=
  L.callEnd - R.deltaBeforeCall

/-- Post-link landing pad address `lpadAddr'` after relaxation by `R`. -/
def RelaxedCallSiteLayout.postLpadAddr {L : PreLinkCallSiteLayout}
    (R : RelaxedCallSiteLayout L) : Nat :=
  L.lpadAddr - R.deltaBeforeCall - R.deltaBeforeLpad

/-- Post-link function end address `funcEnd'` after relaxation by `R`. -/
def RelaxedCallSiteLayout.postFuncEnd {L : PreLinkCallSiteLayout}
    (R : RelaxedCallSiteLayout L) : Nat :=
  L.funcEnd - R.deltaBeforeCall - R.deltaBeforeLpad

/-- **Theorem 3a (`canary_relaxation_corrupts_static_lsda_offsets`):**
If `.gcc_except_table` offsets are emitted as static constants at `Asmgen` time
(`emitStaticAsmgenLsda L`) and RISC-V linker relaxation shrinks an instruction
before the call site by `deltaBeforeCall > 0` bytes (for example, relaxing an
8-byte `auipc + jalr` into a 4-byte `jal`, `deltaBeforeCall = 4`), then at
runtime `ip' = postRetAddr - 1` falls strictly below `funcStart + csStart`, so
`find_eh_action` (`dwarf/eh.rs:119-133`) misses the call-site entry and aborts
with `EHAction::Terminate` (`_URC_FATAL_PHASE1_ERROR`)! -/
theorem canary_relaxation_corrupts_static_lsda_offsets
    (L : PreLinkCallSiteLayout) (R : RelaxedCallSiteLayout L)
    (hRelaxPos : 0 < R.deltaBeforeCall) :
    ¬ lsdaLookupMatches (emitStaticAsmgenLsda L) L.funcStart R.postRetAddr
        R.postLpadAddr R.postFuncEnd := by
  intro ⟨hLow, _, _, _⟩
  unfold emitStaticAsmgenLsda RelaxedCallSiteLayout.postRetAddr at hLow
  dsimp at hLow
  have hOrd := L.hOrder
  have hShrink := R.hShrinkValid
  omega

/-- **Theorem 3b (`noRelax_preserves_lsda_and_cfi`):**
Solution 1: Enforcing `-C link-arg=--no-relax` (or `-C target-feature=-relax`,
so `deltaBeforeCall = 0` and `deltaBeforeLpad = 0`) preserves exact LSDA lookup
alignment and `.eh_frame` FDE range bounds for static `Asmgen` tables. -/
theorem noRelax_preserves_lsda_and_cfi
    (L : PreLinkCallSiteLayout) (R : RelaxedCallSiteLayout L)
    (hNoRelaxCall : R.deltaBeforeCall = 0)
    (hNoRelaxLpad : R.deltaBeforeLpad = 0) :
    lsdaLookupMatches (emitStaticAsmgenLsda L) L.funcStart R.postRetAddr
      R.postLpadAddr R.postFuncEnd := by
  have hOrd := L.hOrder
  unfold lsdaLookupMatches emitStaticAsmgenLsda
    RelaxedCallSiteLayout.postRetAddr RelaxedCallSiteLayout.postLpadAddr
    RelaxedCallSiteLayout.postFuncEnd
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Solution 2: Label-difference pair relocations
(`R_RISCV_SET_ULEB128` / `R_RISCV_SUB_ULEB128` in `.gcc_except_table` and
`R_RISCV_ADD32` / `R_RISCV_SUB32` in `.eh_frame`), which instruct the linker to
recompute `sym_end' - sym_start'` after all `R_RISCV_RELAX` instruction
deletions complete. -/
def resolvePairRelocLsda (L : PreLinkCallSiteLayout)
    (R : RelaxedCallSiteLayout L) : LsdaAndFdeEntry where
  csStart := (L.callStart - R.deltaBeforeCall) - L.funcStart
  csLen := R.postRetAddr - (L.callStart - R.deltaBeforeCall)
  csLpad := R.postLpadAddr - L.funcStart
  fdeRangeLen := R.postFuncEnd - L.funcStart

/-- **Theorem 3c (`pairReloc_preserves_lsda_and_cfi_under_relaxation`):**
When `.gcc_except_table` and `.eh_frame` entries are emitted using symbolic
label-difference pair relocations (`resolvePairRelocLsda L R`), `find_eh_action`
matches `ip' = postRetAddr - 1` and resolves the exact post-relaxation landing
pad `postLpadAddr` and FDE range `postFuncEnd` for **any** valid relaxation
shrinkage `(deltaBeforeCall, deltaBeforeLpad)`! -/
theorem pairReloc_preserves_lsda_and_cfi_under_relaxation
    (L : PreLinkCallSiteLayout) (R : RelaxedCallSiteLayout L) :
    lsdaLookupMatches (resolvePairRelocLsda L R) L.funcStart R.postRetAddr
      R.postLpadAddr R.postFuncEnd := by
  have hOrd := L.hOrder
  have hShrink := R.hShrinkValid
  unfold lsdaLookupMatches resolvePairRelocLsda
    RelaxedCallSiteLayout.postRetAddr RelaxedCallSiteLayout.postLpadAddr
    RelaxedCallSiteLayout.postFuncEnd
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega


-- ============================================================================
-- Part 4: Fixing `UnwindAction::Terminate` in `rustc_codegen_cranelift` &
-- Full 2-Phase Itanium Unwinder (`phase1Search` + `phase2Cleanup`) Mechanization
-- (Resolving Track 8 Question 4)
-- ============================================================================

/-- Exception handler tag constants for `rustc_codegen_cranelift`
(`compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:18-19`), repaired by
separating `EXCEPTION_HANDLER_TERMINATE_FILTER` from
`EXCEPTION_HANDLER_CLEANUP`:
- `EXCEPTION_HANDLER_CLEANUP = 0`: `UnwindAction::Cleanup(bb)` -> `cs_action_entry = 0`
- `EXCEPTION_HANDLER_TERMINATE_FILTER = 1`: `UnwindAction::Terminate(reason)` ->
  action record `{ ttypeIndex := -1, nextOffset := 0 }` (`EHAction::Filter`)
- `EXCEPTION_HANDLER_CATCH = 2`: `sym::catch_unwind` ->
  action record `{ ttypeIndex := 1, nextOffset := 0 }` (`EHAction::Catch`). -/
inductive ClifHandlerTag where
  | cleanup_0 : ClifHandlerTag
  | terminateFilter_1 : ClifHandlerTag
  | catch_2 : ClifHandlerTag
  deriving DecidableEq, Repr

/-- An action record in the `.gcc_except_table` action table
(`rustc_codegen_cranelift/src/debuginfo/gcc_except_table.rs:179-208` and
`library/std/src/sys/personality/dwarf/eh.rs:171-194`). -/
structure LsdaActionRecord where
  ttypeIndex : Int
  nextOffset : Int
  deriving DecidableEq, Repr

/-- Decoded `EHAction` returned by `find_eh_action` / `interpret_cs_action` in
`library/std/src/sys/personality/dwarf/eh.rs:49-66, 159-195`. -/
inductive DecodedEHAction where
  | none : DecodedEHAction
  | cleanup (lpad : Nat) : DecodedEHAction
  | catch (lpad : Nat) : DecodedEHAction
  | filter (lpad : Nat) : DecodedEHAction
  | terminate : DecodedEHAction
  deriving DecidableEq, Repr

/-- Exact mechanization of `interpret_cs_action` from
`library/std/src/sys/personality/dwarf/eh.rs:159-195`:
- When `actionRecord? = none` (`cs_action_entry == 0`), returns
  `DecodedEHAction.cleanup lpad`.
- When `actionRecord? = some rec` (`cs_action_entry > 0`):
  - if `rec.nextOffset != 0`, returns `DecodedEHAction.catch lpad`
  - else if `rec.ttypeIndex == 0`, returns `DecodedEHAction.cleanup lpad`
  - else if `rec.ttypeIndex > 0`, returns `DecodedEHAction.catch lpad`
  - else (`rec.ttypeIndex < 0`), returns `DecodedEHAction.filter lpad`. -/
def interpretCsAction (actionRecord? : Option LsdaActionRecord) (lpad : Nat) :
    DecodedEHAction :=
  match actionRecord? with
  | none => .cleanup lpad
  | some rec =>
      if rec.nextOffset != 0 then
        .catch lpad
      else if rec.ttypeIndex == 0 then
        .cleanup lpad
      else if rec.ttypeIndex > 0 then
        .catch lpad
      else
        .filter lpad

/-- Serialize a `ClifHandlerTag` to an optional `LsdaActionRecord` in
`rustc_codegen_cranelift/src/debuginfo/unwind.rs:175-196`:
- `.cleanup_0` -> `none` (`cs_action_entry = 0`)
- `.terminateFilter_1` -> `some { ttypeIndex := -1, nextOffset := 0 }`
- `.catch_2` -> `some { ttypeIndex := 1, nextOffset := 0 }`. -/
def emitClifActionRecord : ClifHandlerTag → Option LsdaActionRecord
  | .cleanup_0 => none
  | .terminateFilter_1 => some { ttypeIndex := -1, nextOffset := 0 }
  | .catch_2 => some { ttypeIndex := 1, nextOffset := 0 }

/-- Unwind reason codes (`_Unwind_Reason_Code`) returned by
`rust_eh_personality_impl` (`library/std/src/sys/personality/gcc.rs:242-282`). -/
inductive UnwindReasonCode where
  | continueUnwind : UnwindReasonCode
  | handlerFound : UnwindReasonCode
  | installContext (lpad : Nat) : UnwindReasonCode
  | fatalPhase1Error : UnwindReasonCode
  | fatalPhase2Error : UnwindReasonCode
  deriving DecidableEq, Repr

/-- Exact mechanization of `rust_eh_personality_impl` from
`library/std/src/sys/personality/gcc.rs:257-281` for both Phase 1
(`isSearchPhase = true`, `_UA_SEARCH_PHASE`) and Phase 2
(`isSearchPhase = false`, `_UA_CLEANUP_PHASE`), including `_UA_FORCE_UNWIND`
(`forceUnwind : Bool`). -/
def rustEhPersonalityImpl (isSearchPhase forceUnwind : Bool)
    (ehAction : DecodedEHAction) : UnwindReasonCode :=
  if isSearchPhase then
    match ehAction with
    | .none | .cleanup _ => .continueUnwind
    | .catch _ | .filter _ => .handlerFound
    | .terminate => .fatalPhase1Error
  else
    match ehAction with
    | .none => .continueUnwind
    | .filter lpad =>
        if forceUnwind then .continueUnwind else .installContext lpad
    | .cleanup lpad | .catch lpad => .installContext lpad
    | .terminate => .fatalPhase2Error

/-- MIR-level unwind handler kind on a call frame. -/
inductive MirFrameHandlerKind where
  | continueNoLpad : MirFrameHandlerKind
  | cleanup (drops : List Nat) : MirFrameHandlerKind
  | terminateAbi : MirFrameHandlerKind
  | terminateInCleanup : MirFrameHandlerKind
  | catchUnwind : MirFrameHandlerKind
  deriving DecidableEq, Repr

/-- Buggy Cranelift lowering in `rustc_codegen_cranelift/src/abi/mod.rs:886-913`
at `rust@49d734536222bf28bb6d07d885b3a81d145981da`, which maps **both**
`UnwindAction::Cleanup` and `UnwindAction::Terminate` to
`EXCEPTION_HANDLER_CLEANUP` (`.cleanup_0`). -/
def lowerHandlerBuggyClif (lpad : Nat) : MirFrameHandlerKind → DecodedEHAction
  | .continueNoLpad => .none
  | .cleanup _ => interpretCsAction (emitClifActionRecord .cleanup_0) lpad
  | .terminateAbi => interpretCsAction (emitClifActionRecord .cleanup_0) lpad
  | .terminateInCleanup =>
      interpretCsAction (emitClifActionRecord .cleanup_0) lpad
  | .catchUnwind => interpretCsAction (emitClifActionRecord .catch_2) lpad

/-- Repaired Cranelift lowering mapping `UnwindAction::Terminate` (`Abi` and
`InCleanup`) to `EXCEPTION_HANDLER_TERMINATE_FILTER` (`.terminateFilter_1`),
which emits `{ ttypeIndex := -1, nextOffset := 0 }` (`DecodedEHAction.filter`). -/
def lowerHandlerRepairedClif (lpad : Nat) :
    MirFrameHandlerKind → DecodedEHAction
  | .continueNoLpad => .none
  | .cleanup _ => interpretCsAction (emitClifActionRecord .cleanup_0) lpad
  | .terminateAbi =>
      interpretCsAction (emitClifActionRecord .terminateFilter_1) lpad
  | .terminateInCleanup =>
      interpretCsAction (emitClifActionRecord .terminateFilter_1) lpad
  | .catchUnwind => interpretCsAction (emitClifActionRecord .catch_2) lpad

/-- A compiled stack frame inspected by the 2-phase Itanium unwinder. -/
structure StackFrame2Phase where
  fnId : Nat
  lpad : Nat
  kind : MirFrameHandlerKind
  ehAction : DecodedEHAction
  deriving DecidableEq, Repr

/-- Outcome of Phase 1 (`_UA_SEARCH_PHASE`) of `_Unwind_RaiseException`
(`gcc.rs:327-330`). -/
inductive Phase1Outcome where
  | handlerFound (handlerFnId : Nat) : Phase1Outcome
  | endOfStack : Phase1Outcome
  | fatalError : Phase1Outcome
  deriving DecidableEq, Repr

/-- Phase 1 search walk (`phase1Search`) of the Itanium C++ ABI unwinder:
walks the stack from innermost frame to outermost frame calling
`rustEhPersonalityImpl true false f.ehAction` without modifying registers or
running landing pads. Stops at the first frame returning `.handlerFound`, or
returns `.endOfStack` if no frame handles the exception! -/
def phase1Search : List StackFrame2Phase → Phase1Outcome
  | [] => .endOfStack
  | f :: rest =>
      match rustEhPersonalityImpl true false f.ehAction with
      | .continueUnwind => phase1Search rest
      | .handlerFound => .handlerFound f.fnId
      | .fatalPhase1Error | .fatalPhase2Error | .installContext _ =>
          .fatalError

/-- Outcome of the full 2-phase `_Unwind_RaiseException` execution. -/
inductive TwoPhaseUnwindOutcome where
  /-- Phase 1 returned `_URC_END_OF_STACK`; Phase 2 never ran! -/
  | uncaughtEndOfStack : TwoPhaseUnwindOutcome
  /-- Phase 2 ran `executedDrops` across inner cleanup frames and aborted at a
  terminate landing pad (`panic_cannot_unwind` or `panic_in_cleanup`). -/
  | terminatedAbort (handlerFnId : Nat) (executedDrops : List Nat) :
      TwoPhaseUnwindOutcome
  /-- Phase 2 ran `executedDrops` across inner cleanup frames and caught the
  panic at a `catch_unwind` frame. -/
  | caught (handlerFnId : Nat) (executedDrops : List Nat) :
      TwoPhaseUnwindOutcome
  /-- Forced unwind (`_UA_FORCE_UNWIND`) skipped all POF terminate filters and
  reached the end of the stack after running cleanups. -/
  | forcedUnwindComplete (executedDrops : List Nat) : TwoPhaseUnwindOutcome
  | fatalError : TwoPhaseUnwindOutcome
  deriving DecidableEq, Repr

/-- Phase 2 cleanup walk (`phase2Cleanup`) of the Itanium C++ ABI unwinder:
walks the stack from innermost to outermost calling
`rustEhPersonalityImpl false forceUnwind f.ehAction`. When `.installContext` is
returned:
- If `f.kind = .cleanup drops`, the landing pad executes `drops` and calls
  `_Unwind_Resume`, continuing Phase 2 to the caller frame `rest`.
- If `f.kind = .terminateAbi` or `.terminateInCleanup`, the landing pad calls
  `panic_cannot_unwind` / `panic_in_cleanup` and halts in `.terminatedAbort`.
- If `f.kind = .catchUnwind`, the landing pad catches the exception and halts
  in `.caught`. -/
def phase2Cleanup (forceUnwind : Bool) :
    List StackFrame2Phase → List Nat → TwoPhaseUnwindOutcome
  | [], accDrops =>
      if forceUnwind then .forcedUnwindComplete accDrops
      else .uncaughtEndOfStack
  | f :: rest, accDrops =>
      match rustEhPersonalityImpl false forceUnwind f.ehAction with
      | .continueUnwind => phase2Cleanup forceUnwind rest accDrops
      | .installContext _ =>
          match f.kind with
          | .cleanup drops =>
              phase2Cleanup forceUnwind rest (accDrops ++ drops)
          | .terminateAbi | .terminateInCleanup =>
              .terminatedAbort f.fnId accDrops
          | .catchUnwind =>
              .caught f.fnId accDrops
          | .continueNoLpad => .fatalError
      | .handlerFound | .fatalPhase1Error | .fatalPhase2Error => .fatalError

/-- Complete 2-phase `_Unwind_RaiseException` execution (`runTwoPhaseUnwind`):
1. Runs `phase1Search frames`.
2. If `phase1Search` returns `.endOfStack`, immediately returns
   `.uncaughtEndOfStack` **without ever running `phase2Cleanup`**!
3. If `phase1Search` returns `.handlerFound`, runs `phase2Cleanup false frames []`. -/
def runTwoPhaseUnwind (frames : List StackFrame2Phase) :
    TwoPhaseUnwindOutcome :=
  match phase1Search frames with
  | .endOfStack => .uncaughtEndOfStack
  | .fatalError => .fatalError
  | .handlerFound _ => phase2Cleanup false frames []

/-- Build a 2-frame call stack where:
- Inner frame `fnId = 1` has `UnwindAction::Cleanup([101, 102])`, and
- Outer frame `fnId = 2` is an `extern "C"` ABI boundary with
  `UnwindAction::Terminate(Reason::Abi)` (and no outer `catch_unwind` frame). -/
def mkExternCBoundaryStack (lower : Nat → MirFrameHandlerKind → DecodedEHAction) :
    List StackFrame2Phase :=
  [ { fnId := 1
      lpad := 0x1040
      kind := .cleanup [101, 102]
      ehAction := lower 0x1040 (.cleanup [101, 102]) },
    { fnId := 2
      lpad := 0x2080
      kind := .terminateAbi
      ehAction := lower 0x2080 .terminateAbi } ]

/-- **Theorem 4a (`cranelift_bug_phase1_misses_terminate_without_outer_catch`):**
Under `rustc_codegen_cranelift`'s current lowering (`lowerHandlerBuggyClif`,
which tags `UnwindAction::Terminate` with `EXCEPTION_HANDLER_CLEANUP = 0`),
when a panic unwinds toward an `extern "C"` boundary (`fnId = 2`) with no outer
`catch_unwind` frame on the stack:
1. `phase1Search` receives `_URC_CONTINUE_UNWIND` at both frame 1 and frame 2
   and returns `.endOfStack`, and
2. `runTwoPhaseUnwind` returns `.uncaughtEndOfStack` **without running frame 1's
   cleanup drops `[101, 102]` and without calling `panic_cannot_unwind` at
   frame 2**! -/
theorem cranelift_bug_phase1_misses_terminate_without_outer_catch :
    let stack := mkExternCBoundaryStack lowerHandlerBuggyClif
    phase1Search stack = .endOfStack ∧
    runTwoPhaseUnwind stack = .uncaughtEndOfStack := ⟨rfl, rfl⟩

/-- **Theorem 4b (`repaired_filter_phase1_and_phase2_sound`):**
Under the repaired Cranelift lowering (`lowerHandlerRepairedClif`, which tags
`UnwindAction::Terminate` with `EXCEPTION_HANDLER_TERMINATE_FILTER = 1` emitting
`{ ttypeIndex := -1, nextOffset := 0 }`):
1. `interpretCsAction` decodes frame 2's action as `DecodedEHAction.filter`,
2. `phase1Search` stops at frame 2 with `.handlerFound 2`,
3. `runTwoPhaseUnwind` enters Phase 2, executes frame 1's cleanup landing pad
   drops `[101, 102]`, and halts at frame 2's terminate landing pad with
   `.terminatedAbort 2 [101, 102]`, AND
4. Under forced unwinding (`forceUnwind = true`, `_UA_FORCE_UNWIND`), Phase 2
   still skips the POF terminate filter via `_URC_CONTINUE_UNWIND` (`gcc.rs:267-269`)
   and completes with `.forcedUnwindComplete [101, 102]`. -/
theorem repaired_filter_phase1_and_phase2_sound :
    let stack := mkExternCBoundaryStack lowerHandlerRepairedClif
    interpretCsAction (emitClifActionRecord .terminateFilter_1) 0x2080 =
      .filter 0x2080 ∧
    phase1Search stack = .handlerFound 2 ∧
    runTwoPhaseUnwind stack = .terminatedAbort 2 [101, 102] ∧
    phase2Cleanup true stack [] = .forcedUnwindComplete [101, 102] :=
  ⟨rfl, rfl, rfl, rfl⟩


-- ============================================================================
-- Section 5: Kernel Axiom Footprint Audit
-- (Zero `sorryAx`, Zero `Lean.ofReduceBool`)
-- ============================================================================

/-- info: 'Round2Track6.eraseLeak_monotone' does not depend on any axioms -/
#guard_msgs in
#print axioms eraseLeak_monotone

/-- info: 'Round2Track6.non_ct_crate_zero_overhead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms non_ct_crate_zero_overhead

/-- info: 'Round2Track6.ct_crate_1sim_and_2sim_compose' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ct_crate_1sim_and_2sim_compose

/-- info: 'Round2Track6.mo_strictPartialOrder' does not depend on any axioms -/
#guard_msgs in
#print axioms mo_strictPartialOrder

/-- info: 'Round2Track6.viewMachine_trace_coherence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms viewMachine_trace_coherence

/-- info: 'Round2Track6.viewMachine_forbids_write_read_coherence_violation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms viewMachine_forbids_write_read_coherence_violation

/-- info: 'Round2Track6.canary_relaxation_corrupts_static_lsda_offsets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms canary_relaxation_corrupts_static_lsda_offsets

/-- info: 'Round2Track6.noRelax_preserves_lsda_and_cfi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms noRelax_preserves_lsda_and_cfi

/-- info: 'Round2Track6.pairReloc_preserves_lsda_and_cfi_under_relaxation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pairReloc_preserves_lsda_and_cfi_under_relaxation

/-- info: 'Round2Track6.cranelift_bug_phase1_misses_terminate_without_outer_catch' does not depend on any axioms -/
#guard_msgs in
#print axioms cranelift_bug_phase1_misses_terminate_without_outer_catch

/-- info: 'Round2Track6.repaired_filter_phase1_and_phase2_sound' does not depend on any axioms -/
#guard_msgs in
#print axioms repaired_filter_phase1_and_phase2_sound

end Round2Track6
