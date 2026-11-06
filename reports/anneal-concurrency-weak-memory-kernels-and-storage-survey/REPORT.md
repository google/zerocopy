# Concurrency, Weak Memory, OS Kernels, Hardware Drivers, Crash-Safe Storage, and Distributed Systems: Real-World Tools, Historical Failures, and Anneal Refinement Mapping

## Summary

### Part I — Real-World Verification Tools and Refinement Architecture Mapping

Basis: normative + documentation + source + execution + derived

Across the 78 concrete verification, model-checking, synthesis, and simulation
tools surveyed in this report—spanning weak-memory consistency (Category A),
lock-free data structures and safe memory reclamation (Category B), interrupt
and OS kernel substrates (Category C), hardware device drivers and DMA/IOMMU
isolation (Category D), crash-consistent storage and persistent memory
(Category E), distributed consensus and deterministic simulation testing
(Category F), and authoritative ISA-to-RTL hardware co-verification
(Category G)—every verification workflow reduces to a combination of Anneal's
four orthogonal `trusted/lean/` primitives:

1. **`Language (SemObs : Type)` and `BehaviorCodec L₁ L₂`
   (`trusted/lean/Trusted/Refinement.lean`):** Separating `Language SemObs`
   (`Prog → Query → Partial (Out → Prop)`) from operational machines allows
   axiomatic execution-graph models (`RC11`, `IMM`, `LKMM`, `Px86`, `PArm`) and
   operational state machines (`Promising 2.0`, `x86-TSO`, `SmallStepMachine`)
   to compose as first-class peers via `Compiles` and `Abstracts`. However,
   `BehaviorCodec`'s partial-bijection law (`decodeOut o₂ = some o₁ →
   encodeOut o₁ = o₂`) forbids directly decoding a concrete outcome type `L₂.Out`
   that retains unobservable execution witnesses (such as an internal reads-from
   schedule ID in an execution graph, un-drained store buffers, caller-saved
   scratch registers, or un-flushed pipeline reorder buffers) into a coarser
   abstract outcome `L₁.Out` (`raw_graph_codec_impossible`). Concrete languages
   must either quotient internal witnesses inside `Language.sem` before the
   codec boundary (`AxiomaticWmmModel.toLanguage`) or restrict `decodeOut` to
   canonical flushed terminal states (`burchDillCodec`).
2. **`ProductiveOn` and `InhabitedPre`
   (`trusted/lean/Trusted/Refinement.lean`):** By requiring both
   `defined` (no reachable `StepResult.failed .ub`) and a non-empty outcome set
   (`∃ o, val h o`) on a non-vacuous domain (`InhabitedPre pre`), `ProductiveOn`
   simultaneously certifies data-race freedom (`RC11`/`LKMM`), use-after-free
   freedom across epoch/hazard-pointer grace periods (`smr-iris`), non-vacuity
   of prophecy variables (`Iris`/`Voila`), and strict determinism of simulated
   schedules (`Turmoil`/`MadSim`/`VOPR`).
3. **Positive Per-Obligation `VerificationResult`
   (`trusted/lean/Trusted/Refinement.lean`):** Disjoining `ob.id ∈ waived ∨
   ob.prop` per obligation (`verificationResult_non_contamination`) enables
   hybrid verification architectures—such as `Asterinas ostd`, `VeriSMo`, and
   `Anvil`—to combine SMT/deductive proofs on core invariants with bounded model
   checking (`Kani`, `GenMC`, `Loom`) or explicitly audited hardware axioms
   without risking antecedent Principle-of-Explosion (`False.elim`) across the
   crate.
4. **`SmallStepMachine` with `EventualBehaviorOf` and `StepResult.externalCall`
   (`trusted/lean/Trusted/StepResult.lean`):** `EventualBehaviorOf` absorbs
   variable-latency internal stuttering ($k \to 1$ failed `CAS` spins, directory
   coherence messages, and multi-cycle RTL pipeline stalls) while
   `StepResult.externalCall` gates every `read_volatile`/`write_volatile` MMIO
   access, DMA doorbell transfer, and syscall/FFI transition on a boolean
   `boundaryInv` (`mmio_protocol_violation_is_ub`). Two critical modeling
   patterns emerge for systems verification without expanding `trusted/lean/`:
   - **Fair-Schedule-in-Query Pattern (`fair_schedule_in_query_starvation_free`):**
     Pure `StepResult.choice .demonic` admits unfair infinite paths that starve
     runnable threads or fail `LL/SC` (`ldxr`/`stxr`, `lr`/`sc`) reservations
     forever (`unfair_demonic_admits_divergence`). Embedding the infinite
     schedule in `Query := State × Schedule` and constraining `pre` to fair
     schedules (`InhabitedPre IsFairSchedule`) verifies starvation freedom and
     lock/wait-freedom with zero Büchi/Rabin automata in the TCB.
   - **Universal Finite-Horizon Query Pattern
     (`universal_horizon_preserves_safety_traces`):** Because
     `EventualOut.diverges` carries no `List Obs` trace
     (`diverging_reactive_loop_erases_trace`), non-terminating reactive loops
     (OS kernels, interrupt handlers, `Raft`/`Paxos` nodes, and clocked RTL top
     modules) must either be verified per event-handler step or parameterized by
     an arbitrary finite horizon `Query := InitState × (horizon : Nat)` so every
     finite execution prefix terminates cleanly in `.terminated trace
     (.normal ())`.

### Part II — Historical Verification Failures, Postmortems, and Architectural Defenses

Historical verification failures across weak-memory compilation, concurrent data
structures, verified operating system kernels, crash-safe storage systems, and
distributed consensus protocols rarely stem from arithmetic errors inside a
proof assistant's kernel. Instead, they arise at five recurring structural
seams:

1. **Non-compositional weak-memory lowering and global optimization assumptions**
   (the C/C++11-to-Power and ARMv7/ARMv8 trailing-sync vs. leading-sync/`stlr`
   compilation bugs exposed by Manerkar et al. at MICRO 2016 and repaired in
   `RC11` by Lahav et al. at PLDI 2017, and the failure of thread-local
   uncapped certification in `Promising 1.0` under global value-range and
   register-promotion optimizations resolved by `Promising 2.0` at PLDI 2020).
2. **Unsynchronized reclamation, aliasing-model mismatches, and unsound
   `Send`/`Sync` trait bounds in concurrent Rust** (`crossbeam-epoch` missing
   `SeqCst` barriers and Stacked/Tree Borrows provenance violations in `#462` /
   `#535`, `std::sync::Arc::get_mut` relaxed-memory synchronization bug exposed
   by *RustBelt Meets Relaxed Memory* at POPL 2020, `RwLockReadGuard` unsound
   `Sync` implementation when `T: Send` in `rust-lang/rust#41622` /
   `CVE-2018-1000810`, and the systemic race and lifetime defects in legacy
   `std::sync::mpsc` that forced its replacement by `crossbeam-channel` in
   `rust-lang/rust#93563`).
3. **Missing memory barriers across hardware-software and guest-host rings**
   (weak-memory deadlocks and data races in Linux kernel `qspinlock`,
   `seqlock`, RCU, and VirtIO split/packed ring `VIRTIO_RING_F_EVENT_IDX`
   notification suppression uncovered on ARM64 and RISC-V by `VSync`, `Herd7` /
   `LKMM`, and `GenMC`).
4. **Unmodeled hardware, boot, DMA/IOMMU, TLB, preemption, and crash-recovery
   boundaries in verified kernels and filesystems** (`seL4`, `CertiKOS`,
   `Komodo`, and `SeKVM` assumptions around bootloader setup, non-coherent
   caches, ARMv8 Break-Before-Make [`BBM`] TLB shootdowns, unmodeled DMA
   channels, speculative execution [`Meltdown`/`Spectre`], `seL4` worst-case
   interrupt latency spikes during `CNode` capability revocation requiring
   explicit preemption points, and `FSCQ` crash-safety bugs found by
   `Yggdrasil` in unverified FUSE bindings and non-idempotent multi-crash
   recovery).
5. **Flawed inductive invariants, unverified wire-marshaling codecs, and SMT
   quantifier instability in distributed systems** (Pamela Zave's Alloy
   refutation of all seven published `Chord` DHT ring invariants under churn,
   the UDP packet serialization bottlenecks in `IronFleet` and `Verdi` that
   motivated `Cheerios`, and Z3 E-matching quantifier instability—the "butterfly
   effect"—that dominated proof maintenance in `IronFleet` and `Chapar`).

This report synthesizes the primary-source root causes of each failure class and
maps their architectural lessons onto Anneal's four `trusted/lean/` primitives:
(1) `Language (SemObs : Type)` + `BehaviorCodec L₁ L₂`, (2) `ProductiveOn` +
`InhabitedPre`, (3) positive per-obligation `VerificationResult`, and
(4) `SmallStepMachine` with `EventualBehaviorOf` + `StepResult.externalCall`.
All seven representative failure mechanisms and their corresponding repairs are
mechanized in a standalone 678-line Lean 4.34.1 artifact
([`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean))
with zero `sorryAx` and zero custom axioms.

---

## Applicability

This package unifies the real-world verification tool mapping and the historical verification failure postmortems for this domain against the durable `joshlf/anneal` repository revisions (`24367bd1a8c784f2578535954f9915e24894a56f`, `5fc1139f2208b3c9cfb513573c4a731cc32bb457`, and `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`) and the self-contained Lean 4 (`v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`) refinement definitions below.

### Self-Contained Anneal Refinement Primitives (`Language`, `Behavior`, `StepResult`, `VerificationResult`)

To ensure this report is self-contained without depending on unmerged development branches, the core Lean 4 refinement definitions referenced throughout Part I and Part II are given inline below:

```lean
/-- Constructive partial behavior cell representing `B ∪ {UB}`. -/
structure Partial (B : Type u) where
  defined : Prop
  val : defined → B

/-- Pointwise refinement preorder on `Partial (Out → Prop)`:
`p₁ ≤ p₂` iff every defined specification query `h₂ : p₂.defined` is defined in
`p₁` (`h₁ : p₁.defined`) and every outcome permitted by `p₁` satisfies `p₂`. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

structure Language (SemObs : Type := Unit) where
  Prog  : Type
  Query : Type
  Out   : Type
  dom   : Prog → Query → Prop := fun _ _ => True
  obs   : Out → SemObs
  sem   : Prog → Behavior Query Out

def Language.SpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    Behavior L.Query L.Out :=
  fun q => { defined := pre q, val := fun _ o => post q o }

/-- Non-vacuity witness: at least one query in `dom` satisfies `pre`. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  ∃ q, dom q ∧ pre q

abbrev InhabitedPre {Query : Type} (pre : Query → Prop) : Prop :=
  ∃ q, pre q

/-- Dijkstra's Law of the Excluded Miracle: every admitted query has at least
one defined outcome. -/
def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete, non-vacuous behavioral verification of `prog` against `(pre, post)`
within `prog`'s own domain `L.dom prog`. -/
def Language.Verified {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn (L.dom prog) pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Partial behavior codec between two languages `L₁` and `L₂` sharing `SemObs`. -/
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  decode_encode_query : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  encodeOut : L₁.Out → L₂.Out
  decodeOut : L₂.Out → Option L₁.Out
  decode_encode_out : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  encode_of_decode_some : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → encodeOut o₁ = o₂
  obs_decodeOut : ∀ {o₂ o₁}, decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

/-- Right-nested conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- A named proof obligation with a private constructor so proof authors cannot
forge weaker propositions under a trusted obligation identifier. -/
structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

abbrev Obligation.assumed {Id : Type} (id : Id) : Obligation Id :=
  ⟨id, False⟩

structure TrustPolicy (Id : Type) where
  isAllowed : Id → Prop

/-- Positive per-obligation verification gate preventing Principle-of-Explosion
contamination from waived or assumed obligations. -/
def VerificationResult {Id : Type} [DecidableEq Id]
    (policy : TrustPolicy Id) (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))

inductive ChoiceKind where
  | demonic
  | angelic

inductive FailureKind where
  | ub
  | fuelExhausted

inductive Terminal (Val : Type) where
  | normal (v : Val)
  | panic
  | abort

/-- Single-step operational outcome for `SmallStepMachine`. -/
inductive StepResult (State Obs Val : Type) where
  | step (next : State) (obs : List Obs := [])
  | choice (kind : ChoiceKind) (branches : State → List Obs → Prop)
  | terminated (term : Terminal Val) (obs : List Obs := [])
  | failed (kind : FailureKind)
  | stuck

/-- Structural external-call boundary guard checking `boundaryInv` at the call
transition before branching demonically over environment return states. -/
def StepResult.externalCall {State Obs Val : Type}
    (boundaryInv : Bool) (branches : State → List Obs → Prop) :
    StepResult State Obs Val :=
  if boundaryInv then .choice .demonic branches else .failed .ub

inductive EventualOut (Obs Val : Type) where
  | terminated (trace : List Obs) (term : Terminal Val)
  | diverges
```

### Part I Applicability — Real-World Verification Tools

Basis: source + execution

The findings and formal encodings in this report apply to the 57 concrete
subjects recorded in `REPORT.json`, anchored to:

- **Anneal's trusted verification core** at
  `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`
  (`trusted/lean/Trusted/Refinement.lean` and
  `trusted/lean/Trusted/StepResult.lean`) and the MIR-to-x86-64 compiler branch
  at `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457`
  (`trusted/lean/Trusted/X86Semantics.lean`),
- **Lean 4** at `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`
  (`v4.34.1`), invoked with `-DElab.async=false -Ddebug.skipKernelTC=false`
  over standalone modules importing only `prelude` and `Init.NotationExtra`,
- **Rust** at `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`
  (`1.99.1`), and
- **53 upstream verification, model-checking, OS kernel, driver, storage,
  distributed-systems, and hardware ISA/RTL repositories** pinned at the exact
  40-character Git commit revisions listed in `REPORT.json` and audited in
  `## Evidence`.

All six cross-cutting architectural theorems (`verificationResult_non_contamination`,
`raw_graph_codec_impossible`, `sc_robustness_transfer`,
`unfair_demonic_admits_divergence`, `fair_schedule_in_query_starvation_free`,
`mmio_protocol_violation_is_ub`, `mmio_valid_driver_productive`,
`crash_recovery_idempotent_converges`, `diverging_reactive_loop_erases_trace`,
`universal_horizon_preserves_safety_traces`, and `burch_dill_rtl_refines_isa`)
are mechanically checked by the Lean 4.34.1 kernel in
[ConcurrencySystemsStressTests.lean](support/ConcurrencySystemsStressTests.lean)
(`sha256: b42fce7d800c8190c456ca826ea945ad0fade66c7b4dcb697a19e9cb419063a3`).

### Part II Applicability — Historical Verification Failures and Postmortems

This report applies to:

- **Anneal (`joshlf/anneal`)** at `trusted/lean` revision
  `24367bd1a8c784f2578535954f9915e24894a56f` (`trusted/lean/Trusted/Refinement.lean`
  and `trusted/lean/Trusted/StepResult.lean`) and `main` revision
  `24367bd1a8c784f2578535954f9915e24894a56f` (`trusted/lean/Trusted.lean` and
  `trusted/lean/Trusted/Attributes.lean`), together with the four-primitive
  refinement architecture (`Language SemObs` + `BehaviorCodec`, `ProductiveOn` +
  `InhabitedPre`, positive per-obligation `VerificationResult`, and
  `SmallStepMachine` with `EventualBehaviorOf` + `StepResult.externalCall`).
- **Lean 4 (`leanprover/lean4`)** at `v4.34.1`
  (`5045d0056413266e57c625dcd7c365b10e377c52`), used to check the standalone
  canary and repair probe in
  `support/concurrency_systems_failure_canaries_probe.lean`.
- **Rust standard library (`rust-lang/rust`)** at
  `d8ef4f3fe7031514cbd7d056b7b058814987ecec` (`library/core/src/sync/atomic.rs`,
  `library/alloc/src/sync.rs`, and `library/std/src/sync/mpsc/mod.rs`), as a
  normative baseline for Rust's C++20-derived atomic memory model and repaired
  `Arc`, `RwLockReadGuard`, and `mpsc` implementations.
- **Primary research and verification postmortems** identified in `REPORT.json`
  across weak memory (`MICRO 2016`, `PLDI 2017`, `POPL 2020`, `PLDI 2020`,
  `ASPLOS 2021`), verified OS kernels and storage (`seL4/l4v`, `OSDI 2016`), and
  distributed systems (`CCR 2012`, `TSE 2017`, `SOSP 2015`, `PLDI 2015`,
  `POPL 2016`).

The subjects in `REPORT.json` are related by **architectural stress-testing and
defect-mode transfer**: historical failures in upstream compilers, concurrent
libraries, verified kernels, storage systems, and distributed verifiers are
analyzed to derive necessary soundness invariants for Anneal's `trusted/` TCB
and `theory/` proof libraries. Exact mechanized claims in
`support/concurrency_systems_failure_canaries_probe.lean` are finite-state or
inductive abstractions capturing the core counterexample traces and repair
invariants; they do not re-execute full Power/ARMv8 silicon, Linux kernel boots,
or multi-node network clusters.

---

## Findings

### Part I — Real-World Verification Tools Mapped to Anneal's Refinement Primitives

### 1. Category A: Weak-Memory Models, Atomic Lowering, and Fence Insertion

Basis: normative + documentation + source + execution + derived

Category A covers 16 real-world tools and mechanized proof frameworks addressing
three Anneal verification use cases: axiomatic/operational weak-memory
consistency and data-race freedom (`anneal-wmm-axiomatic` / `5.5` & `5.8`),
verified atomic lowering and barrier placement (`anneal-atomic-lower` / `5.6` &
`5.7`), and sequential-consistency (`SC`) robustness checking and fence
synthesis (`anneal-sc-robustness`).

#### 1.1 Declarative `.cat` Simulators and Stateless/Bounded Weak-Memory Model Checkers (`Herd7`, `GenMC`, `Nidhugg`, `Dartagnan`/`Dat3M`, `CDSChecker`, `Loom`, `Shuttle`)

1. **Goals, Target Users, and Concrete Inputs/Outputs:**
   - **`Herd7` and `diy7` (`herd/herdtools7@9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34`, v7.58+1):**
     Created by Jade Alglave and Luc Maranget (INRIA), `herd7` is the normative
     reference simulator for axiomatic memory models written in the `.cat`
     relational calculus (including the official Linux Kernel Memory Model
     `LKMM` in `tools/memory-model/` of `torvalds/linux`, `RC11`, `ARMv8-A`
     Flat, and `RISC-V RVWMO`). It takes `.litmus` assembly/C tests and `.cat`
     relational specifications (`po`, `rf`, `co`/`mo`, `fr`, `rmw`, `ppo`,
     `hb`) and outputs the complete set of consistent execution graphs and
     allowed/forbidden final state assertions.
   - **`GenMC` (`MPI-SWS/genmc@fab5bba7d9efaf76990227c2f59d62c11c7ea2a3`):**
     Developed by Michalis Kokologiannakis and Viktor Vafeiadis (MPI-SWS),
     `GenMC` is a stateless model checker (SMC) operating on LLVM-IR (supporting
     both C/C++ via `clang` and Rust via `rustc --emit=llvm-bc`). It verifies
     assertion safety, data-race freedom, lock-freedom (bounded spin-loop the
     `Assume` transformation), and memory safety under `RC11`, `IMM`, and `LKMM`
     using declarative TruSt-based Dynamic Partial Order Reduction (DPOR) in
     polynomial space and optimal time per consistent execution graph.
   - **`Nidhugg` (`nidhugg/nidhugg@845a14632ff33f27ba78e72e0693668219197bb2`):**
     Created by Carl Leonardsson, Parosh Aziz Abdulla, Bengt Jonsson, and
     Konstantinos Sagonas (Uppsala University), `Nidhugg` performs stateless
     DPOR over LLVM-IR under operational hardware memory models (`SC`, `TSO`,
     `PSO`, `POWER`, and `ARM`) using chronological trace representations.
   - **`Dartagnan` / `Dat3M` (`hernanponcedeleon/Dat3M@b81ec6c55503e824bb0ddc4ebac6c6f0a63d56d8`):**
     Developed by Hernán Ponce de León, Florian Furbach, Keijo Heljanko, and
     Roland Meyer, `Dat3M` is a bounded model checker (BMC) that ingests both
     C/LLVM-IR programs and arbitrary `.cat` memory models (`RC11`, `LKMM`,
     `ARMv8`, `RVWMO`, `PTX`/`Vulkan` GPU models) and reduces bounded
     reachability and race-freedom directly to SMT (`QF_BV + QF_IDL`) via the
     `Caat` relational-to-SMT encoder.
   - **`CDSChecker` (Norris & Demsky, OOPSLA 2013, DOI `10.1145/2509136.2509514`):**
     Pioneering C/C++11 dynamic model checker by Brian Norris and Brian Demsky
     (UC Irvine) that instruments `std::atomic` operations at runtime and
     explores `C-2011` modification-order (`mo`) and reads-from (`rf`) choices
     with promises to handle release sequences.
   - **`Loom` (`tokio-rs/loom@948c8cc78b178ede6eeff3afc7d97f2f4ea08559`):**
     Created by Carl Lerche and the Tokio team, `Loom` is a Rust-native library
     model checker implementing CDSChecker's C-2011 DPOR algorithm via mock
     replacements for `std::sync::atomic`, `Mutex`, `RwLock`, `Condvar`, and
     `thread::spawn`.
   - **`Shuttle` (`awslabs/shuttle@cee89eb23a6eb883a3d8002c018326d709f240b1`):**
     Developed by AWS Labs (Bornholt et al., OOPSLA 2021), `Shuttle` shares
     `Loom`'s drop-in `std::sync` mock signature in Rust but replaces exhaustive
     DPOR with randomized scheduling algorithms—Probabilistic Concurrency
     Testing (`PCT`, Burckhardt et al. ASPLOS 2010) and random-walk schedules—to
     scale to thousands of synchronization steps in production AWS storage and
     hypervisor components (`s2n-quic`, `mountpoint-s3`).

2. **History, Design Philosophy, and Tradeoffs:**
   - The lineage progresses from explicit operational state-space exploration to
     execution-graph DPOR: early stateless checkers (`CHESS`, `Nidhugg` on
     `TSO`/`PSO`) explored per-step thread schedules combined with store-buffer
     flush steps, suffering exponential blowup on weak memory. `CDSChecker` and
     `Loom` moved to C-2011 reads-from (`rf`) exploration, and `GenMC` (PLDI 2019 /
     POPL 2021 TruSt algorithm) achieved *optimal* stateless DPOR over
     declarative `.cat`-style graphs by reversing Backward-Revisit edges
     without storing visited sets.
   - **Tradeoff (`Loom` vs. `Shuttle` vs. `GenMC` vs. `Dartagnan`):** `Loom` and
     `Shuttle` require source-level conditional compilation (`#[cfg(loom)]`) and
     do not intercept raw pointers or inline assembly; furthermore, `Loom`
     models only a fragment of C-2011 (`Acquire`/`Release`/`Relaxed` loads/stores,
     approximating `SeqCst` as `AcqRel` and rejecting general `Relaxed` load
     buffering cycles). `GenMC` and `Dartagnan` operate directly on compiled
     LLVM bitcode and handle full `RC11`/`IMM`/`LKMM`/hardware models, trading
     off loop unrolling bounds (`--unroll=K`).

3. **Formal Theory and TCB Analysis:**
   - None of `Herd7`, `GenMC`, `Nidhugg`, `Dartagnan`, `Loom`, or `Shuttle`
     emits a kernel-checkable proof certificate: their TCB includes the tool's
     own C++/Java/Rust implementation, LLVM bitcode lowering (which can erase or
     alter source-level UB before `GenMC`/`Dartagnan` sees the IR), and loop
     unrolling bounds.

4. **Mapping onto Anneal's Four `trusted/` Primitives and Architectural Insights:**
   - **Primitive #1 (`Language SemObs` & `BehaviorCodec`):** As mechanized in
     [ConcurrencySystemsStressTests.lean](support/ConcurrencySystemsStressTests.lean)
     (`AxiomaticWmmModel.toLanguage`, lines 318–337), Anneal's `Language SemObs`
     does *not* require operational state transitions: an axiomatic memory model
     (`RC11`, `IMM`, `LKMM`) instantiates `L_wmm : Language SemObs` directly by
     setting `(L_wmm.sem prog q).defined` to assert that *no* consistent
     pre-execution graph $G \in \text{PreExec}(prog, q)$ contains a non-atomic
     data-race edge ($\neg \text{HasDataRace}(G)$), and setting
     `(L_wmm.sem prog q).val h v` to assert the existence of a maximal
     consistent execution graph $G$ whose terminal observation is $v$.
   - **Critical Stress Test (`raw_graph_codec_impossible`, lines 298–313):** If
     `L_wmm_raw.Out` were defined as the raw `WmmExecGraph` (retaining internal
     `rf`/`mo` schedule choices `scheduleId`) while `L_spec.Out` is the terminal
     value `Nat`, then whenever two distinct consistent execution graphs
     $G_1 \neq G_2$ produce the same final value $v$, `BehaviorCodec`'s
     partial-bijection law (`decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`)
     derives $G_1 = \text{encodeOut}(v) = G_2$, a contradiction! Therefore,
     `L_wmm.Out` must project out internal `rf`/`mo` graph edges inside
     `Language.sem` (or via an intra-language refinement) before crossing a
     `BehaviorCodec` boundary.

#### 1.2 Mechanized Weak-Memory Metatheory, Verified Atomic Compilation, and Fence Insertion (`Kater`, `IMM`, `Promising 2.0`/`Promising-ARM`, `CompCertTSO`, Cambridge C++11, `Musketeer`, `Trencher`, `Memorax`, `Fender`/`Offence`)

1. **Goals, Lineage, and Architecture of Each Tool:**
   - **`Kater` (`MPI-SWS/kater@017fdbb530e421fd76cf39f2906354471b2ce96e`):**
     Developed by Michalis Kokologiannakis, Ori Lahav, and Viktor Vafeiadis
     (POPL 2023, DOI `10.1145/3571235`), `Kater` automates weak-memory
     metatheory—proving model inclusion ($M_1 \subseteq M_2$), correctness of
     compiler transformations (instruction reordering, access strengthening,
     merged accesses), and soundness of `GenMC` consistency checks—by encoding
     acyclic relational `.cat` constraints into Kleene Algebra with Tests (`KAT`)
     and deciding inclusion via finite-state automata equivalence.
   - **`IMM` (`weakmemory/imm@4ca191b072df081dd3a6d9aa755959dc901b1bd0`):**
     Developed by Anton Podkopaev, Ori Lahav, and Viktor Vafeiadis (POPL 2019,
     DOI `10.1145/3290382`), `IMM` is a Coq formalization of an Intermediate
     Memory Model that factors $M_{\text{src}} \times N_{\text{tgt}}$
     compilation proofs into $M_{\text{src}} \to \text{IMM}$ (`RC11`,
     `Promising`) and $\text{IMM} \to N_{\text{tgt}}$ (`POWER`, `ARMv7`,
     `ARMv8`, `RISC-V`, `x86-TSO`).
   - **`Promising 2.0` (`snu-sf/promising2-coq@6b70a57d10666ec66bfa96b7801dd870f9054da9`)
     and `Promising-ARM` (`snu-sf/promising-arm@10291375ccd03152eadf739d280e2c59e10fa9af`):**
     Developed by Jeehoon Kang, Sung-Hwan Lee, Chung-Kil Hur, Ori Lahav, and
     Viktor Vafeiadis at Seoul National University and MPI-SWS (POPL 2017 /
     PLDI 2020, DOI `10.1145/3385412.3386010`; Pye et al. OOPSLA 2019),
     `Promising` defines an *operational* weak-memory machine in Coq where
     threads maintain per-location timestamped view fronts (`View`), memory is a
     global append-only log of timestamped messages, and out-of-order stores are
     modeled by threads *promising* future writes only when they can deterministically
     *certify* that the promise can be fulfilled within a capped memory state
     (solving the Out-Of-Thin-Air `OOTA` problem while supporting thread-local
     optimizations and global value-range analysis).
   - **`CompCertTSO` (Ševčík, Vafeiadis, Zappa Nardelli, Jagannathan, Sewell,
     POPL 2011 / JACM 2013, DOI `10.1145/2487241.2487248`) and Cambridge C++11
     Compilation Proofs (Batty, Owens, Sarkar, Sewell, Weber, POPL 2011 /
     POPL 2012):** `CompCertTSO` extends CompCert in Coq to verify compilation
     of ClightTSO to `x86-TSO` assembly with per-thread FIFO store buffers and
     stacked thread-local allocations; the Cambridge group mechanized the
     normative C/C++11 axiomatic model in Lem/HOL4/Coq and proved soundness of
     standard `x86`, `ARM`, and `Power` atomic lowering tables (and found the
     famous Power/ARM `SeqCst` compilation counterexamples).
   - **Fence Synthesis & Robustness Checkers (`Memorax` at
     `memorax/memorax@2f25c43f279bb315aba7ac3fcf7c37bbb7d1af5e`, Abdulla et al.
     TACAS 2013; `Trencher`, Bouajjani, Meyer, Muskalla, CAV 2011/2013;
     `Musketeer`, Alglave et al. CAV 2014, DOI `10.1007/978-3-319-08867-9_34`;
     `Fender`/`Offence`, Kuperstein, Vechev, Yahav, FMCAD 2010 /Jade Alglave et
     al.):** These tools verify *`M`-robustness against `SC`* (whether every
     weak-memory trace under `TSO`/`PSO`/`POWER`/`ARM` equals an `SC`
     interleaving) and automatically synthesize minimal fence placements
     (`mfence`, `dmb`) to eliminate critical cycles ($hb \cup fr \cup co$
     cycles).

2. **Mapping onto Anneal's Four `trusted/` Primitives:**
   - **Transitive `Compiles` via `L_IMM` (`anneal-atomic-lower`):** Anneal
     mirrors `IMM`'s factoring directly by instantiating `L_RC11`, `L_IMM`, and
     `L_arch` (`L_X86TSO`, `L_AArch64POP`, `L_RVWMO`) as `Language`s and
     composing `Compiles L_RC11 L_IMM codec₁ s_mir s_imm` with
     `Compiles L_IMM L_arch codec₂ s_imm t_asm`.
   - **LL/SC Forward-Progress Boundary (`anneal-atomic-lower`):** On `ARMv8`
     (`ldaxr`/`stlxr`) and `RISC-V` (`lr.d`/`sc.d`), an atomic `fetch_add` in
     `L_IMM` compiles to a retry loop in `L_arch` where spurious exclusive
     monitor failures are modeled by `StepResult.choice .demonic`. Under pure
     unfair demonic choice, `L_arch` admits `.diverges` (`unfair_demonic_admits_divergence`),
     which violates `Compiles` against a single-step terminating `L_IMM` RMW
     unless `Query` incorporates the architectural forward-progress schedule
     (`fair_schedule_in_query_starvation_free`).
   - **Weak-Memory Robustness as Self-Refinement (`sc_robustness_transfer`,
     lines 343–353):** In Anneal, `M`-robustness (and `Musketeer`/`Memorax`/`vsyncer`
     fence insertion $P \mapsto P'$) is expressed as
     `Compiles L_SC L_WMM (BehaviorCodec.id L_SC) P P'`, which composes via
     `refinesBehavior_trans` with any high-level proof `Abstracts L_spec L_SC c
     spec P` to establish `Abstracts L_spec L_WMM c spec P'`.

| Tool / Framework | Primary Subject Pin / Citation | Memory Models Supported | Verification Method & Certificate Endpoint | Anneal `trusted/` Primitive Mapping |
| :--- | :--- | :--- | :--- | :--- |
| **`Herd7` / `diy7`** | `herd/herdtools7@9574394fc4b2` (`7.58+1`) | Arbitrary `.cat` (`RC11`, `LKMM`, `ARMv8`, `RVWMO`) | Exhaustive litmus execution graph enumeration | `AxiomaticWmmModel.toLanguage` (`Language SemObs`) |
| **`GenMC`** | `MPI-SWS/genmc@fab5bba7d9ef` | `RC11`, `IMM`, `LKMM`, `SC` | TruSt optimal stateless DPOR on LLVM-IR | Bounded oracle discharging `VerificationResult` obligations |
| **`Nidhugg`** | `nidhugg/nidhugg@845a14632ff3` | `SC`, `TSO`, `PSO`, `POWER`, `ARM` | Chronological-trace stateless DPOR on LLVM-IR | Operational `SmallStepMachine` store-buffer trace exploration |
| **`Dartagnan` (`Dat3M`)** | `hernanponcedeleon/Dat3M@b81ec6c55503` | `.cat` (`RC11`, `LKMM`, `ARMv8`, `RVWMO`, `PTX`) | Relational `.cat`-to-SMT (`QF_BV + QF_IDL`) BMC | Bit-blasted `LRAT`/`Alethe` certificate into `VerificationResult` |
| **`CDSChecker` / `Loom`** | `tokio-rs/loom@948c8cc78b17` | `C-2011` subset (`Acq`/`Rel`/`Relaxed`) | Runtime DPOR over mock `std::sync::atomic` | Finite-harness `ProductiveOn` exploration |
| **`Shuttle`** | `awslabs/shuttle@cee89eb23a6e` | `SeqCst` / mock `std::sync` schedules | Randomized `PCT` & seed-driven schedule exploration | Seed-parameterized `Query` in `SmallStepMachine` |
| **`Kater`** | `MPI-SWS/kater@017fdbb530e4` | `.cat` relational fragments | Kleene Algebra with Tests (`KAT`) automata inclusion | Certifies `Compiles L_IMM L_arch` lowering schemes |
| **`IMM`** | `weakmemory/imm@4ca191b072df` | `RC11`, `Promising` $\to$ `IMM` $\to$ `ARMv8`/`RVWMO`/`TSO` | Mechanized Coq graph-refinement proofs | Factored `Compiles L_RC11 L_IMM` $\circ$ `Compiles L_IMM L_arch` |
| **`Promising 2.0` / `ARM`** | `snu-sf/promising2-coq@6b70a57d1066` | Operational `Promising 2.0` & `ARMv8`/`RISC-V` | Mechanized Coq timestamp-view + certification machine | Operational `SmallStepMachine` with timestamped views |
| **`Memorax` / `Musketeer`** | `memorax/memorax@2f25c43f279b` | `TSO`, `PSO`, `VIPS`, `POWER`, `ARM` | Reachability / critical-cycle LP fence synthesis | `sc_robustness_transfer`: `Compiles L_SC L_WMM idCodec P P'` |

---

### 2. Category B: Fine-Grained Concurrent Data Structures, Safe Memory Reclamation, and Liveness

Basis: normative + documentation + source + execution + derived

Category B covers 12 tool ecosystems addressing three Anneal use cases:
lock-free linearizability and contextual refinement with helping/prophecies
(`anneal-linearize` / `5.1` & `5.2`), safe memory reclamation (`SMR`) for
hazard pointers, `crossbeam-epoch`, and RCU (`anneal-smr-epoch` / `5.3`), and
deadlock/starvation/wait-freedom (`anneal-progress-sync` / `5.4`).

#### 2.1 Concurrent Separation Logics, Atomic Triples, and Refinement Layers (`Iris`/`ReLoC`/`GPFSL`, `CIVL`, `Voila`, `CAVE`/`Poling`, `Verus` TSM, `Armada`, `Starling`)

1. **Goals, Lineage, and Architecture of Each Tool:**
   - **`Iris` (`rocq-iris/iris@8e4909593a3a84f850d224a344cbd3a380672088`),
     `ReLoC` (Frumin, Krebbers, Birkedal, LICS 2018), `GPS`/`iRC11`/`GPFSL`
     (`https://gitlab.mpi-sws.org/iris/gpfsl@48b7183f1b91f7cc53cfdab16e21387e9bfe9c14`
     and `kaist-cp/relaxed-memory-separation-logic@6fe1475af1f8c49f8c144a67d9175b5b3e6bc472`),
     and `Cosmo` (Mével, Jourdan, Pottier, ICFP 2020):**
     `Iris` unifies concurrent separation logic (`CSL`) around two core
     mechanisms in Coq: user-defined Partial Commutative Monoids (`CMRA`s /
     ghost resources) and step-indexed impredicative invariants (`inv N P`).
     `ReLoC` layers logical-relations contextual refinement (`e₁ ≤_ctx e₂ : τ`)
     and structural prophecies (Jung et al. POPL 2020) on top of Iris to verify
     lock-free algorithms with future-dependent linearization points (Michael-Scott
     queue, Herlihy-Wing queue). `GPS` (Turon et al. OOPSLA 2014), `iRC11` (Dang
     et al. POPL 2020), and `GPFSL` extend Iris to weak memory (`ORC11`) with
     per-location protocol modalities ($\text{GPS}$ ghost state machines, atomic
     read-modify-write views, and release-acquire resources).
   - **`CIVL` (`boogie-org/boogie@fcecf73a49d11ad3ab16729abd03169e5ecfd938`):**
     Developed by Shaz Qadeer, Serdar Tasiran, Chris Hawblitzel, and Bernhard
     Kragl (CAV 2015 / CAV 2018 / POPL 2020), `CIVL` is built directly into the
     Boogie intermediate verification language. It verifies concurrent programs
     through *layered refinement* (`@layer(k)`), combining Lipton's left/right
     movers (reduction to coarse-grained atomic actions), permission-based
     linear/tie types (`{:linear}`), and pending-async obligations via SMT (`Z3`).
   - **`Voila` (`viperproject/voila@900470c4035812bde4f80defc5e4e2e79c1fcae6`):**
     Developed by Wolf, Schwerhoff, and Müller at ETH Zürich (OOPSLA 2021, DOI
     `10.1145/3485519`), `Voila` automates the `TaDA` (Time and Data
     Abstraction, da Rocha Pinto et al. ECOOP 2014) concurrent separation logic
     by translating `TaDA` *atomic triples* ($\langle \forall x.\, P(x) \rangle\,
     c\, \langle Q(x) \rangle$) and interference guards into sequential Viper
     (`Silicon`/`Carbon`) SMT obligations.
   - **`CAVE` (Vafeiadis, CAV 2010) and `Poling` (Zhu, Petri, Jagannathan,
     CAV 2015):** Automated shape-analysis and linearizability verifiers for C
     lock-free data structures (Treiber stack, Michael-Scott queue,arris list);
     `CAVE` combines RGSep (Rely-Guarantee + Separation Logic) with brute-force
     search for linearization points, while `Poling` adds *helping* support via
     history/prophecy abstraction over thread-local views.
   - **`Verus` `tokenized_state_machines` (`verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c`):**
     Developed by Travis Hance, Andrea Lattuada, Chris Hawblitzel, Jon Howell,
     Rob Johnson, and Bryan Parno (OSDI 2023 / SOSP 2024), Verus's
     `tokenized_state_machines!` macro compiles an abstract concurrent protocol
     (with `#[sharding(variable)]`, `#[sharding(map)]`, `#[sharding(multiset)]`,
     and `#[sharding(storage_option)]` fields) into linear `tracked` Rust ghost
     tokens whose transitions are checked automatically by Z3 and tied to
     physical atomic variables (`AtomicU64`, `PCell`) via `LocalInvariant`.
   - **`Armada` (`microsoft/armada@da7497dcf506417df1899ac58850706a31e3acd5`):**
     Developed by Lorch et al. at Microsoft Research (PLDI 2020, DOI
     `10.1145/3385412.3385971`), `Armada` is a Dafny-based verification
     framework for low-level concurrent C-like code under `x86-TSO` weak memory
     that automates 8 proof strategies (Lipton reduction, store-buffer
     elimination `TSO-to-SC`, invariant strengthening, variable hiding, and
     inductive refinement) across a chain of state machines.
   - **`Starling` (`MattWindsor91/starling-tool@438fe7259e06aaf8433c259244fef2985de797a5`):**
     Developed by Matt Windsor, Mike Dodds, Ben Simner, and Matthew Parkinson
     (CAV 2017), `Starling` reduces concurrent Views-framework proofs (Dinsdale-Young
     et al. POPL 2013) to sequential SMT/Grashopper obligations over bounded
     view-fragments.

2. **Safe Memory Reclamation (`smr-iris`) and Liveness/Progress Tools (`LiLi`/`TaDA-Live`, `Fair-Iris`/`Trillium`, `VeriFast`, `VSync`):**
   - **`smr-iris` (`kaist-cp/smr-verification@53fdc1648c17c5527c2499ed0ad10d55c01e1344`):**
     Developed by Jaehwang Jung, Janggun Lee, Jeehoon Kang et al. at KAIST
     (POPL 2023, DOI `10.1145/3571219`; OOPSLA 2023), `smr-iris` gives the first
     modular mechanized Iris specifications for **Hazard Pointers** and
     **Epoch-Based Reclamation (`crossbeam-epoch`)** under both `SC` and `ORC11`
     weak memory, decoupling the SMR engine's grace-period/shield protocol from
     client data structures (Michael-Scott queue, Harris-Michael list, Chase-Lev
     deque) and discovering a missing `SeqCst` fence bug in historical SMR designs.
   - **Liveness, Lock-Freedom, and Starvation-Freedom Logics (`LiLi`, Liang &
     Feng POPL 2016 / `TaDA-Live`, D'Osualdo et al. ESOP 2021; `Trillium` &
     `Fair-Iris`, Tassarotti, Timany, Birkedal et al. at
     `https://gitlab.mpi-sws.org/iris/transfinite@dde9f193fb3d504be680480b2ca21052edae49df`;
     `VeriFast` at `verifast/verifast@0a83dba42db7ce0b445034ece5298afe980e57dc`):**
     Standard step-indexed Iris (`rocq-iris/iris`) can only prove *safety*
     (finite-prefix properties) because $\triangleright^n \text{False}$ holds at
     index $n$. `Transfinite Iris` (Spies et al. POPL 2021) replaces $\mathbb{N}$
     step-indexing with ordinal step-indexing, and `Trillium` / `Fair-Iris`
     (POPL 2024) embeds a fair operational model into Iris where each thread has
     a decreasing fuel/fairness token (`fuel_token tid f`) that must be stepped
     whenever `tid` is scheduled, proving starvation-freedom under weak fairness.
     `VeriFast` (Jacobs, Hamin et al.) verifies deadlock freedom and termination
     of locks/channels via fractional *wait-level tokens* and call-permission
     ordinals.
   - **`VSync` (`open-s4c/libvsync@dd93f802704c9c941eb7397fa101039bf21118ff`
     and `open-s4c/vsyncer@76569f0d2ee9a688da95b8025116b3a202e67321`):**
     Developed by Huawei Dresden Research Center (Oberhauser et al., ASPLOS 2021,
     DOI `10.1145/3445814.3446748`), `libvsync` provides 30+ lock-free queues,
     spinlocks (ticket, MCS, CLH, hemLock, RWlocks), and SMR primitives verified
     by `vsyncer` (which drives `GenMC` and `Dartagnan` across iterative barrier
     relaxations to find the weakest sound `Acquire`/`Release`/`Relaxed`
     orderings for `ARMv8` and `RISC-V`).

3. **Mapping onto Anneal's Four `trusted/` Primitives and Architectural Insights:**
   - **Ghost State & Prophecy Erasure in `theory/`:** A major architectural lesson
     from comparing `Verus` (`tokenized_state_machines`), `CIVL`, and `Iris` is
     that **ghost state (`CMRA`, `tracked` tokens, prophecy variables) never
     needs to enter Anneal's `trusted/lean/` TCB**. Because `EventualBehaviorOf`
     defines behavior extensionally over complete concrete traces `EventualOut
     Obs Val`, backward simulation, prophecy tokens, and Iris/Verus ghost token
     algebras live purely inside `theory/` and discharge `Abstracts L_atomic_spec
     L_conc` and `ProductiveOn` by adequacy!
   - **Mechanized Fair-Schedule-in-Query Pattern (`fair_schedule_in_query_starvation_free`,
     lines 398–453):** Unlike `Transfinite Iris` / `Fair-Iris` (which had to
     rebuild its entire meta-theory over ordinals and fair operational
     transitions), Anneal's `SmallStepMachine` requires *zero* changes to verify
     starvation-freedom or `LL/SC` termination under fairness: we instantiate
     `Query := InitState × Schedule` with `pre (s₀, sched) := IsFairSchedule
     (s₀, sched)` and prove `InhabitedPre IsFairSchedule` (`fairSchedule_inhabited`,
     lines 386–388) + `ProductiveOn IsFairSchedule prog`!

---

### 3. Category C: Interrupts, Preemption, Context Switch, MMU/TLB, and Microkernel IPC

Basis: normative + documentation + source + execution + derived

Category C covers 13 tool and kernel-verification ecosystems addressing four
Anneal use cases: interrupt/NMI/signal re-entrancy and `compiler_fence`
verification (`anneal-isr-reentrant` / `5.14`), preemptive scheduler
context-switch and stack-pointer handoff (`anneal-ctx-switch` / `5.14`),
page-table walks, Break-Before-Make (`BBM`), and cross-core IPI TLB shootdowns
(`anneal-mmu-tlb` / `5.13`), and microkernel fastpath IPC and capability
non-interference (`anneal-cap-ipc` / `5.16`).

#### 3.1 Interrupt Re-Entrancy, Preemption, and Context-Switch Verifiers (`CertiKOS`/`mCertiKOSi`, `Goblint`, `i-CBMC`, `RTIC`, `XCAP`/`OCAP`, `Asterinas ostd`)

1. **Goals, Lineage, and Architecture of Each Tool:**
   - **`CertiKOS` and `mCertiKOSi` (Gu, Shao, Chen, Wu, Kim, Sjöberg et al.,
     POPL 2015 / OSDI 2016, DOI `10.5555/3026877.3026928`; `switch_kt` context
     switch and interruptible kernel layers in Coq):**
     Developed at Yale and Columbia (`DeepSpec`), `CertiKOS` introduced
     *Certified Concurrent Abstraction Layers (`CCAL`)* on top of `CompCertX`
     (which extends CompCert with per-thread kernel stacks and assembly helpers).
     `mCertiKOSi` models hardware interrupts at every x86 instruction step by
     interleaving an abstract interrupt handler layer whenever `EFLAGS.IF == 1`,
     and verifies the assembly context-switch routine `switch_kt` (`movl %esp,
     0(%eax); movl 0(%edx), %esp; ret`) by lifting raw stack-pointer swaps into
     deterministic thread-local continuation steps at the layer above.
   - **`Goblint` ISR Analyzer (`goblint/analyzer@1463f411ce87edd49198033856b2946fc3366fb2`):**
     Developed at TU Munich and the University of Tartu (Schwarz, Saan, Seidl,
     et al., Vojdani et al. ASE 2016 / TACAS 2021), `Goblint` is an OCaml
     abstract interpreter for multi-threaded and interrupt-driven C (OSEK/AUTOSAR
     embedded automotive kernels and Linux device drivers). It tracks currently
     held spinlocks, interrupt-masking priority ceiling levels (`DisableAllInterrupts`,
     `local_irq_save`), and thread-modular side-effecting constraint systems to
     prove absence of ISR data races and single-core interrupt deadlocks.
   - **`i-CBMC` (Kroening, Liang, Melham, Schrammel, Tautschnig, ASE 2015, DOI
     `10.1109/ASE.2015.46`):** Extends CBMC bounded model checking to asymmetric
     nested Interrupt Service Routines (ISRs) by encoding priority-preemptive
     interrupt arrival via symbolic shadow copies of shared variables bounded by
     hardware interrupt-enable registers (`IE`/`IP`).
   - **`RTIC` (`rtic-rs/rtic@f1797184d6168e54c345b17019c237eea70b9ed4`):**
     Real-Time Interrupt-driven Concurrency framework for embedded Rust
     (`cortex-m` NVIC / RISC-V CLIC). `RTIC` enforces the **Stack Resource
     Policy (`SRP`, Baker 1991)** at compile time: every shared resource $R$ is
     assigned a priority ceiling $\lceil R \rceil = \max_{t \in \text{users}(R)}
     \text{prio}(t)$, and locking $R$ temporarily raises `BASEPRI` to
     $\lceil R \rceil$. This statically guarantees **both data-race freedom and
     deadlock freedom on a single shared hardware call stack** without dynamic
     spinlocks or heap allocation.
   - **`XCAP` and `OCAP` (Ni & Shao, POPL 2006; Ni, Yu, Shao, PLDI 2007, DOI
     `10.1145/1250734.1250763`; Feng, Shao, Vaynberg, Heng, Zha, PLDI 2007/2008):**
     Foundational Coq program logics (`XCAP` for first-class code pointers and
     embedded coroutine `yield`/`switch` return continuations; `OCAP` for
     interoperating open assembly modules and `cli`/`sti` interrupt handlers)
     that verify machine-level x86 context switches where `esp` and `eip` are
     manipulated as ordinary data registers.
   - **`Asterinas ostd` (`asterinas/asterinas@a5238eb6a965a4616ce07a48f5dfbc8042c4cd44`):**
     As established in the corpus (`tock-asterinas-current-source-review`),
     Asterinas pioneers the **Framekernel** architecture: all `unsafe` Rust code
     in the entire Linux-compatible OS is confined to `ostd` (~14% of the
     codebase), which exposes safe abstractions for `Task` context switching,
     `TrapFrame`, `DisabledLocalIrqGuard` (`compiler_fence` + `cli`/`sti`),
     `SpinLock` (with IRQ-disable tokens preventing ISR deadlock), `PageTable`,
     and `DmaCoherent`/`DmaStream`, with ongoing Verus verification of `ostd`
     page-table and frame-allocator invariants.

2. **Microkernels, Hypervisors, and Hardware MMU/TLB Verifiers (`seL4`, `VeriSMo`, `Verified NR-OS`, `Islaris`, `SeKVM`, `Komodo`, `Atmosphere`):**
   - **`seL4` (`seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5`):**
     The gold-standard formally verified microkernel in Isabelle/HOL (Klein et
     al. SOSP 2009 / TOCS 2014). Its refinement chain spans an Abstract
     Specification (`ASpec`), an Executable Design Specification (`ExecSpec`
     generated from Haskell), and the C implementation (`CSpec` parsed via Norrish's
     C-to-Isabelle parser) plus binary translation validation (`seL4/graph-refine@6c6f2612b17f48ddfe41ee62ff1b077e320b9c89`).
     Specifically, seL4 verifies the **IPC Fastpath** (`Call` and `ReplyRecv`
     shown to refine the general slowpath), **Capability Access Control**
     (`capDL` authority confinement: integrity and authority non-amplification),
     and **Information-Flow Non-Interference** (confidentiality across domain-scheduled
     partitions), while trusting assembly context-switch stubs and hardware TLB
     maintenance instructions (`invlpg`/`tlbi`) at the C boundary.
   - **`VeriSMo` (`microsoft/verismo@6bc6dd326d8b9ca30ffec57a544b13b5fadf3cb3`):**
     Developed at Microsoft Research and OSU (Zhou, Li, Hawblitzel, Parno, et
     al., OSDI 2024), `VeriSMo` is the first formally verified security module
     for **AMD SEV-SNP** Confidential VMs (running at `VMPL0` in Rust and
     verified with **Verus**). `VeriSMo` verifies Reverse Map Table (`RMP` /
     `pvalidate`) page security states (Private vs. Shared with untrusted host
     hypervisor), secret-page zeroization before host sharing, and dynamic
     information-flow security of `VMPL0` traps and VirtIO shared buffers.
   - **`Verified NR-OS` Page Tables (`matthias-brun/verified-nrkernel@1c861090537664b78544cda5d53711b1fcfa05e2`):**
     Developed by Matthias Brun, Reto Achermann, Andrea Lattuada, et al. at ETH
     Zürich (OSDI 2023 / SOSP 2024 in Dafny and Verus), this project verifies a
     4-level x86-64 / ARMv8 hardware page-table manager (`map_frame`, `unmap`)
     against an explicit operational model of the hardware MMU and TLB, proving
     that nested bitfield PTE manipulations implement an abstract flat map of
     virtual-to-physical mappings.
   - **`Islaris` and `Isla-ARMv8-VMSA` (`rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`):**
     Developed by Michael Sammler, Angus Hammond, Rodolphe Lepigre, Brian
     Campbell, Jean Pichon-Pharabod, Derek Dreyer, Deepak Garg, and Peter Sewell
     (PLDI 2022, DOI `10.1145/3519939.3523434`; Simner et al. ESOP 2020 / POPL
     2022 for `ARMv8-A VMSA`), `Islaris` connects the `Isla` symbolic evaluator
     (running the official Armv8-A `ASL`/`Sail` specification) to an `Iris`
     program logic in Coq. Together with the REMS `VMSA` model, it verifies
     machine-code exception vectors, page-table walk translation caches,
     **Break-Before-Make (`BBM`)** sequences, and `dsb ishst; tlbi; dsb ish;
     isb` cross-core TLB shootdowns.
   - **`SeKVM` (`VeriGu/SeKVM-4.18@75e3591e663958c370c919aa36fbd484be341043`):**
     Developed by Shih-Wei Li, Xupeng Li, Ronghui Gu, Jason Nieh, and John Zhuang
     Hui at Columbia University (SOSP 2021, DOI `10.1145/3477132.3483570`),
     `SeKVM` retrofits formal verification onto Linux's commodity Arm64 KVM
     hypervisor using `CertiKOS`-style micro-layers in Coq, verifying Stage-2
     NPT (`S2PT`) page-table isolation, VM world switches, and SMMUv3 DMA protection.
   - **`Komodo` (`microsoft/komodo@de1865c8bd0d85cdfd9a980ad7131448acfaf136`)
     and `Atmosphere` (`mars-research/atmosphere@bd485f22f1d5e4d1623e133700dc233086059603`):**
     `Komodo` (Ferraiuolo, Baumann, Hawblitzel, Parno, SOSP 2017) verifies an
     ARM TrustZone Monitor Mode enclave supervisor written in `Vale` assembly +
     `Dafny`, proving non-interference between enclaves across world switches and
     page-table updates. `Atmosphere` (Chen, Mars Research / University of Utah,
     SOSP 2023) verifies a microkernel in Rust using **Verus**, using linear tracked
     array/page permissions to eliminate run-time reference counting bugs in page
     tables and process tables.

3. **Mapping onto Anneal's Four `trusted/` Primitives and Architectural Insights:**
   - **Asymmetric Interrupts and `compiler_fence` in `SmallStepMachine`
     (`anneal-isr-reentrant`):** In `M_isr : SmallStepMachine`, every step checks
     whether `IrqMaskBits` (or `RTIC` `BASEPRI`) permits interrupt $irq$; if so,
     `StepResult.choice .demonic` branches between the next normal instruction
     and pushing an interrupt frame onto the call stack. Uncommitted non-atomic
     writes that have not been flushed by `compiler_fence(Ordering::SeqCst)`
     remain in the thread's intra-thread reorder window; if an ISR accesses the
     same location before `compiler_fence`, `step` emits `StepResult.failed .ub`.
   - **Context Switch as Cross-Machine `BehaviorCodec` (`anneal-ctx-switch`):**
     Like `CertiKOS`'s `switch_kt` and `XCAP`, Anneal bridges the single-CPU
     concrete ISA machine `L_isa` (where all thread stacks occupy disjoint ranges
     in a flat address space and `sp` is swapped on `switch_to`) to an abstract
     multi-thread machine `L_threads` via `Abstracts L_threads L_isa codec`.
     Critically, to obey `BehaviorCodec.encode_of_decode_some`, `L_isa.Out` must
     project out dead caller-saved scratch registers (`r10`, `r11`, `RFLAGS`) at
     the context-switch boundary!
   - **Hardware Autonomous Page-Table Walkers (`anneal-mmu-tlb`):** Following
     `Isla-ARMv8-VMSA` and `Verified NR-OS`, the hardware MMU walker is modeled
     in `L_HardwareMMU`'s `SmallStepMachine` as a spontaneous demonic branch
     (`StepResult.choice .demonic`) that can read `PhysMem` PTEs at *any* step
     and cache translations in `TlbCache[core]`. If the OS frees a page frame
     before completing `invlpg`/`tlbi` + cross-core IPI shootdowns, or installs
     overlapping block/page mappings without ARMv8 Break-Before-Make, a demonic
     TLB hit triggers `StepResult.failed .ub`.
   - **2-Safety Information-Flow Non-Interference via Deterministic `Abstracts`
     (`anneal-cap-ipc`):** In `seL4`, `VeriSMo`, `SeKVM`, and `Komodo`,
     confidentiality is a 2-safety hyperproperty ($s_1 \approx_d s_2 \implies
     \text{obs}_d(\text{run}(s_1)) = \text{obs}_d(\text{run}(s_2))$). In Anneal's
     `trusted/lean/`, this requires *no* hyperproperty extension: proving
     `Abstracts L_domain_spec L_kernel codec_d spec kernel` where
     `codec_d.decodeQuery` projects *only* domain $d$'s visible state and
     `L_domain_spec.sem spec` is deterministic (verified non-empty by
     `ProductiveOn`) automatically guarantees that secret state outside domain
     $d$ cannot influence domain $d$'s observations!

| Tool / System | Primary Subject Pin / Citation | Target Domain & Architecture | Proof Engine & TCB | Anneal `trusted/` Primitive Mapping |
| :--- | :--- | :--- | :--- | :--- |
| **`CertiKOS` (`mCertiKOSi`)** | OSDI 2016 (`10.5555/3026877.3026928`) | Preemptive x86 OS kernel (`switch_kt`, ISRs) | Coq + `CompCertX` CCAL layers | `Abstracts L_threads L_PreemptISA` + demonic IRQ injection |
| **`Goblint`** | `goblint/analyzer@1463f411ce87` | OSEK/AUTOSAR & Linux ISR race/deadlock analysis | OCaml abstract interpreter | Certifying priority-ceiling fixpoint into `VerificationResult` |
| **`RTIC`** | `rtic-rs/rtic@f1797184d616` | Cortex-M / RISC-V Stack Resource Policy (`SRP`) | Rust type/macro priority ceiling enforcement | Static priority-ceiling invariant in `SmallStepMachine` |
| **`Asterinas ostd`** | `asterinas/asterinas@a5238eb6a965` | Framekernel `ostd` (`Task`, `TrapFrame`, `PageTable`) | Safe Rust boundary + Verus (`Z3`) proofs | Scoped `VerificationResult` + `StepResult.externalCall` |
| **`seL4` (`l4v`)** | `seL4/l4v@6b4076aeb35f` | ARM/x86/RISC-V microkernel IPC fastpath & `capDL` | Isabelle/HOL + `graph-refine` binary validator | `Compiles` (fastpath $\le$ slowpath) + deterministic `Abstracts` (IFC) |
| **`VeriSMo`** | `microsoft/verismo@6bc6dd326d8b` | AMD SEV-SNP `VMPL0` confidential VM monitor | Verus (`Z3`) + tracked RMP page state | `Abstracts` with adversarial shared-memory `.choice .demonic` |
| **`Verified NR-OS`** | `matthias-brun/verified-nrkernel@1c8610905376` | x86-64 / ARMv8 4-level radix page tables & TLB | Verus / Dafny (`Z3`) | `Abstracts L_FlatVirtMem L_HardwareMMU` |
| **`Islaris` / `VMSA`** | `rems-project/islaris@c978e10f50db` | Armv8-A machine code, exception vectors & `BBM`/`tlbi` | `Isla` (`Sail`/`ASL`) + Coq `Iris` | Authoritative `L_sail_isa` + spontaneous MMU walker steps |
| **`SeKVM` / `Komodo`** | `VeriGu/SeKVM-4.18@75e3591e6639` / `microsoft/komodo@de1865c8bd0d` | Arm64 KVM Stage-2 NPT / TrustZone enclaves | Coq (`SeKVM`) / `Vale`+`Dafny` (`Komodo`) | Layered `Abstracts` + non-interference domain codecs |
| **`Atmosphere`** | `mars-research/atmosphere@bd485f22f1d5` | Rust microkernel page & process tables | Verus (`Z3`) linear tracked permissions | Ghost permission erasure into `L_mir.ProductiveOn` |

---

### 4. Category D: Hardware Device Drivers, MMIO, DMA, IOMMU, and VirtIO Rings

Basis: normative + documentation + source + execution + derived

Category D covers 9 tool families addressing three Anneal use cases: `volatile`
MMIO register protocol verification against CMSIS-SVD/datasheet state machines
(`anneal-mmio-svd` / `5.15`), DMA buffer ownership transfer, cache maintenance,
and IOMMU/SMMU aperture isolation (`anneal-dma-iommu` / `5.15`), and
Split/Packed VirtIO ring-buffer verification across weakly-ordered or adversarial
host-device shared memory (`anneal-virtio-ring` / `5.15` & `6.16`).

#### 4.1 MMIO Register Protocol, Driver Model Checking, and Synthesis Tools (`Kani`, `Termite`/`Termite-2`, `SafeMMIO`, `SLAM`/`SDV`/`Corral`, `Klever`/`LDV`)

1. **Goals, Lineage, and Architecture of Each Tool:**
   - **`Kani` SVD/MMIO Harnesses (`model-checking/kani@9461e07af7ec929f050aa4192f29363c9be07779`):**
     Developed by AWS (VanHattum et al., ICSE-SEIP 2022), `Kani` translates Rust
     MIR to `GOTO` programs checked by CBMC/Kissat/CaDiCaL. For embedded and
     kernel drivers (`svd2rust`, `tock-registers`), `Kani` replaces
     `core::ptr::read_volatile` and `write_volatile` with stub harnesses
     (`kani::any()`) that track shadow register state machines, bitfield
     Write-1-to-Clear (`W1C`) rules, and reserved-bit preservation.
   - **`Termite` and `Termite-2` (Ryzhyk, Chubb, Kuz, Le Sueur, Heiser, SOSP 2009 /
     Ryzhyk, Walker, Keys, Legg, Raghunath, Vij, OSDI 2014, DOI
     `10.5555/2685048.2685082`):** Pioneered at NICTA/UNSW, `Termite` synthesizes
     correct-by-construction C device drivers from formal state-machine
     specifications of the OS interface and the hardware device datasheet (via
     two-player Büchi/reachability games where the driver is the protagonist and
     the device/bus is the demonic environment); `Termite-2` adds user-guided
     interactive transition refinement for complex I2C/SPI/Ethernet controllers.
   - **`SafeMMIO` / Rust Typestate SVD Generators (`svd2rust`, `tock-registers`
     at `tock/tock@9554639b17501a9f5940cef7a1770a0823e790c3`, Fuchsia `hwreg`):**
     Encode Read-Only (`RO`), Write-Only (`WO`), Read-Write (`RW`), and
     peripheral enable/disable typestates in Rust types, though without formal
     verification of multi-register temporal protocols (e.g., polling `TX_EMPTY`
     before writing `TX_DATA`) or weak-memory barriers (`dmb osh`).
   - **`SLAM` / `SDV` / `Corral` (`boogie-org/corral@33dd98eed1e2d5087c7c5df9a782652772af2b2e`):**
     Microsoft's flagship Windows Driver Kit (`WDK`) Static Driver Verifier
     (Ball & Rajamani, POPL 2002; Lal, Qadeer, Lahiri, CAV 2012). `SDV` compiles
     SLIC (Specification Language for Interface Checking) temporal rules—such as
     `SpinLock` acquire/release pairing, `IRQL` interrupt-level constraints
     (`KeAcquireSpinLock` requires `IRQL <= DISPATCH_LEVEL`), and IRP completion
     protocols—into instrumentation in Boogie checked by `Corral`'s stratified
     inlining and CEGAR engine.
   - **`Klever` / `LDV` (`ldv-klever/klever@49fef330955ea175fd73dd22f2670c68b811d51a`):**
     Developed by the ISP RAS Linux Driver Verification (`LDV`) project (Novikov,
     Zakharov et al., ISoLA 2018), `Klever` extracts environment models and
     aspect-oriented safety specifications (`clk_prepare_enable`, `dma_map_single`,
     `mutex_lock`, `usb_alloc_urb`) across the Linux kernel and verifies C
     drivers via `CPAchecker` and `Ultimate Automizer`.

#### 4.2 DMA Ownership, IOMMU/SMMU Isolation, and VirtIO Ring Verifiers (`SeKVM`/`CertiKOS-IO`/`seL4 SMMU`, `embassy`/`embedded-dma`, `VeriSMo`/`Asterinas` VirtIO)

1. **Goals, Lineage, and Architecture of Each Tool:**
   - **IOMMU and SMMU Formal Proofs (`SeKVM` SMMUv3 at
     `VeriGu/SeKVM-4.18@75e3591e663958c370c919aa36fbd484be341043`; `CertiKOS-IO`,
     alka et al. / Yale; `seL4` Arm SMMU & Intel VT-d models in `seL4/l4v`):**
     Without an IOMMU/SMMU proof, a formally verified OS kernel (`seL4`,
     `CertiKOS`, `SeKVM`) can be trivially subverted by a rogue PCIe/platform
     device performing DMA writes over kernel code or page tables. `SeKVM` and
     `CertiKOS-IO` model DMA engines as concurrent hardware agents whose memory
     accesses are translated through the IOMMU Stage-2 IOVA page tables, proving
     that untrusted devices can only read/write frames explicitly granted in
     their IOMMU domain.
   - **`embassy` (`embassy-rs/embassy@14cf6a68ec0bfd0ecf873f7e3dbb2eb69013fa29`)
     and `embedded-dma` (`rust-embedded/embedded-dma@37deca203dc3281fb459f0da92d41b6743a62a48`):**
     Define the `ReadBuffer` and `WriteBuffer` unsafe traits in embedded Rust to
     transfer buffer ownership to asynchronous DMA transfers (`Transfer<'a>`),
     highlighted by the famous "Soundness of DMA in Rust" problem (if a `Future`
     owning a stack DMA buffer is `core::mem::forget`-ed before the DMA transfer
     completes, the stack frame is popped while hardware DMA continues writing
     to the stack, causing catastrophic UAF unless buffers are `'static`/pinned
     or `Drop` blocks until hardware abort completes).
   - **`VeriSMo` (`microsoft/verismo@6bc6dd326d8b9ca30ffec57a544b13b5fadf3cb3`)
     and `Asterinas` (`asterinas/asterinas@a5238eb6a965a4616ce07a48f5dfbc8042c4cd44`)
     VirtIO Split/Packed Ring Verifiers:**
     In Confidential Computing (`AMD SEV-SNP` / `Intel TDX`), VirtIO descriptor
     rings (`vring_desc`, `vring_avail`, `vring_used`) reside in **untrusted
     shared bounce pages** (`SWIOTLB`) readable and writable by a potentially
     malicious host VMM at any clock cycle. `VeriSMo` uses Verus to verify that
     guest VirtIO drivers copy descriptor indices (`used.id`, `len`) into
     private guest registers before bounds-checking them (eliminating
     **double-fetch TOCTOU** bugs), bound descriptor chain traversals by queue
     size $N$, and never expose private VMPL0 pages to DMA.

2. **Mapping onto Anneal's Four `trusted/` Primitives and Architectural Insights:**
   - **Mechanized Hardware Datasheet Gate via `StepResult.externalCall`
     (`mmio_protocol_violation_is_ub` and `mmio_valid_driver_productive`, lines
     455–523 of [ConcurrencySystemsStressTests.lean](support/ConcurrencySystemsStressTests.lean)):**
     Every `read_volatile` and `write_volatile` to an MMIO aperture or DMA
     doorbell lowers in Anneal's driver `SmallStepMachine` to
     `StepResult.externalCall boundaryInv branches`. Here `boundaryInv : Bool`
     evaluates:
     1. Register alignment, bit-width, and `RO`/`WO`/reserved-bit mask rules,
     2. Peripheral datasheet protocol preconditions (e.g., `fifoReady == true`
        before writing `TX_DATA`),
     3. Cache-coherency maintenance on non-coherent ARM/RISC-V buses (`dc cvac`
        clean before TX DMA doorbell; `dc ivac` invalidate before RX CPU read),
        and
     4. Disjoint CPU–DMA ownership (`!dmaActive`—no active Stacked/Tree Borrows
        reference overlaps an active DMA buffer, and if a DMA `Transfer` is
        dropped early, `boundaryInv` fails unless hardware DMA abort completes!).
     As proved in `mmio_protocol_violation_is_ub`, any violation of `boundaryInv`
     immediately yields `defined = False` (`.failed .ub`), while
     `mmio_valid_driver_productive` proves that a driver polling status before
     accessing MMIO/DMA satisfies `ProductiveOn` across all demonic hardware
     responses (`branches`).
   - **Adversarial Host/Device Shared Memory (`anneal-virtio-ring`):** By
     including a spontaneous demonic transition (`StepResult.choice .demonic`)
     that mutates unpinned shared `SWIOTLB`/`vring_used` bytes between *every*
     two guest instructions in `SmallStepMachine`, Anneal automatically rejects
     any VirtIO driver with a double-fetch TOCTOU vulnerability!

---

### 5. Category E: Crash Consistency, Asynchronous NVMe, and Persistent Memory

Basis: normative + documentation + source + execution + derived

Category E covers 8 tool ecosystems addressing three Anneal use cases:
crash-horizon refinement and idempotent recovery verification
(`anneal-crash-refine` / `5.12`), asynchronous NVMe Submission/Completion Queue
and PRP scatter-gather list verification (`anneal-nvme-blk` / `5.15`), and
non-volatile persistent memory (`PMEM`/`CXL`) cache-line flush verification
under `Px86`/`PArm` (`anneal-pmem-persist` / `5.12`).

#### 5.1 Crash Hoare Logics, Verified File Systems, and Storage Engines (`Perennial`/`GoJournal`/`DaisyNFS`, `FSCQ`/`DFSCQ`/`SFSCQ`, `VeriBetrKV`, `Microsoft verified-storage`, `Cogent`/`BilbyFS`, `Yggdrasil`)

1. **Goals, Lineage, and Architecture of Each Tool:**
   - **`Perennial` (`mit-pdos/perennial@d62b13ac1ff88e21e9f1fbc18cbfeab30cc9ca8e`),
     `GoJournal` (`mit-pdos/go-journal@1d09d436fcbd943296f43372c3896714254838c0`),
     and `DaisyNFS` (`mit-pdos/daisy-nfsd@68530c3b62abe31ce280e71a2b0d40026a70e5ee`):**
     Developed at MIT PDOS by Tej Chajed, Joseph Tassarotti, Frans Kaashoek, and
     Nickolai Zeldovich (SOSP 2019 / OSDI 2021, DOI `10.1145/3341301.3359632`),
     `Perennial` extends `Iris` in Coq to verify **concurrent crash-safe systems**
     written in Go (translated via `Goose` into `GooseLang`). `Perennial`
     introduces *crash obligations* (`wpc s k E1 P Φ Φc`, Weakest Precondition
     with Crash) ensuring that at every step of concurrent execution, if the
     machine crashes and runs `recover()`, the durable disk state satisfies the
     crash postcondition $\Phi_c$, and proves **crash-recovery refinement**
     across multi-crash generations via ghost generation tokens. `GoJournal`
     verifies a concurrent write-ahead log (imported by a Linux kernel ext4-like
     file system), and `DaisyNFS` verifies a concurrent crash-safe NFSv3 server.
   - **`FSCQ`, `DFSCQ`, and `SFSCQ` (`mit-pdos/fscq@2c7ef9c268fd79a81b26b44ef720f8e6a1e938a0`):**
     Developed by Haogang Chen, Daniel Ziegler, Tej Chajed, Adam Chlipala, Frans
     Kaashoek, and Nickolai Zeldovich (SOSP 2015 / SOSP 2017 / EuroSys 2018),
     `FSCQ` introduced **Crash Hoare Logic (`CHL`)** in Coq, modeling async disk
     writes via sector-level subset flushes (`disk := Addr → Val × List Val`
     where a barrier drains the pending write list and a crash nondeterministically
     selects any suffix). `DFSCQ` formalizes metadata-prefix specifications for
     `fdatasync`/`fsync` optimization, and `SFSCQ` proves crash-safe data
     confidentiality (`non-interference` across crashes).
   - **`VeriBetrKV` (`secure-foundations/veribetrkv-osdi2020@053dd16ab01939843a213e0590983fd22e2d0d4d`):**
     Developed by Travis Hance, Andrea Lattuada, Jon Howell, Rob Johnson, Bryan
     Parno et al. (OSDI 2020, DOI `10.5555/3488766.3488780`), `VeriBetrKV` is a
     high-performance crash-safe $\text{B}^\varepsilon$-tree key-value store
     verified in **Linear Dafny** (whose linear/inout borrow extensions directly
     inspired **Verus**!). It uses a 6-layer state-machine refinement hierarchy
     connecting an abstract crash-atomic map + journal down to asynchronous disk
     I/O control blocks and copy-on-write node marshaling.
   - **`Microsoft verified-storage` (`microsoft/verified-storage@afcc157f40a1381773daa8be7333f5d123e96739`):**
     Developed at Microsoft Research (OSDI 2024 / SOSP 2024), `verified-storage`
     uses **Verus** in Rust to verify high-throughput persistent-memory (`PMEM`)
     and NVMe storage engines (including multithreaded ring-buffer write-ahead
     logs and corruption-detecting checksums) against out-of-order crash models.
   - **`Cogent` and `BilbyFS` (`NICTA/cogent@49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a`):**
     Developed at NICTA/Data61 (Amani et al., ASPLOS 2016, DOI
     `10.1145/2872362.2872404`), `Cogent` is a restricted linear, functional
     systems language whose compiler emits *both* C code and an Isabelle/HOL
     refinement proof (`Compiles L_Cogent L_C`), used to verify the `BilbyFS`
     flash file system without manual pointer-aliasing proofs.
   - **`Yggdrasil` (`locore/yggdrasil@e1de61d798acafb9ae2d8387d176c4b091773623`):**
     Developed by Helgi Sigurbjarnarson, James Bornholt, Emina Torlak, and Xi
     Wang at the University of Washington (OSDI 2016), `Yggdrasil` achieves
     *push-button* (zero manual invariant annotation) verification of file
     systems (`xv6` FS, `Yxv6`) by requiring the implementation and specification
     to satisfy **crash refinement** on finite unrolled execution paths checked
     by Z3 over stratified array theories.

#### 5.2 Persistent Memory Weak-Persistency Models and Model Checkers (`Px86`/`PArm`/`Spirea`, `Jaaru`/`Witcher`/`PMTest`)

1. **Goals, Lineage, and Architecture of Each Tool:**
   - **`Px86`, `PArm`, and `Spirea` (Raad, Wickerson, Neiger, Vafeiadis, POPL
     2020, DOI `10.1145/3371099`; Raad et al. OOPSLA 2020; Vindum, Frumin,
     Birkedal, OOPSLA 2022 / PLDI 2023 `Spirea`):**
     Formalize the architectural interaction between weak memory ordering and
     cache-line persistence ordering on Intel x86 (`Px86`: `clflush`,
     `clflushopt`, `clwb`, `sfence`) and ARMv8.2 (`PArm`: `dc cvap` Point of
     Persistence, `dc cvadp`, `dsb ish`). Because CPU caches are volatile
     (outside eADR), dirty cache lines evict to NVM in arbitrary order unless
     ordered by explicit flush + fence instructions. `Spirea` builds a mechanized
     crash-aware concurrent separation logic on top of `Iris` and `Perennial` in
     Coq for `Px86` persistent lock-free data structures.
   - **`Jaaru` (`uci-plrg/jaaru@640e2ad4d9089d0ff8a4fa17e2f4347b8f31449b`),
     `Witcher` (Cai et al. SOSP 2021), and `PMTest` (Liu et al. ASPLOS 2019):**
     `Jaaru` (Gorjiara, Xu, Demsky, ASPLOS 2021, DOI `10.1145/3445814.3446735`)
     is an LLVM-instrumented model checker for PMDK/NVM programs that avoids the
     $2^N$ subset explosion of unflushed cache lines by tracking *commit stores*
     in the recovery polling loop and pruning equivalent post-crash states via
     Z3 interval constraints.

2. **Mapping onto Anneal's Four `trusted/` Primitives and Architectural Insights:**
   - **Multi-Crash Reboot Closure Inside `SmallStepMachine` (`anneal-crash-refine`
     and `crash_recovery_idempotent_converges`, lines 527–543 of
     [ConcurrencySystemsStressTests.lean](support/ConcurrencySystemsStressTests.lean)):**
     Rather than adding a specialized Crash Hoare Logic (`wpc`) primitive to
     `trusted/lean/`, Anneal models power loss directly inside `SmallStepMachine`!
     The machine state is `(VolatileRam, InFlightWrites, DurableDisk)` (or
     `(VolatileCacheLines, PersistedNvmLines)` for `Px86`/`PArm`). At every step
     of normal execution *or* `recover()` execution, a demonic branch
     (`StepResult.choice .demonic`) can trigger a **Crash Transition**:
     1. `VolatileRam` is wiped to `ram₀`,
     2. A demonic subset of `InFlightWrites` is applied to `DurableDisk` (and the
        rest discarded),
     3. `Obs.crash` is emitted to the trace, and
     4. Control jumps to the entry point of `recover()`.
     As mechanized in `crash_recovery_idempotent_converges`, when `recover` is
     idempotent (`∀ d, recover (recover d) = recover d`), arbitrary $k$-crash
     reboot cascades during recovery converge to the exact same abstract disk
     state, proven via standard `Abstracts L_atomic_disk L_crash_machine`!
   - **Asynchronous NVMe Queue & PRP Validation (`anneal-nvme-blk`):** Ringing
     the NVMe Submission Queue (`SQ`) Tail Doorbell triggers
     `StepResult.externalCall`, where `boundaryInv` checks unique Command ID
     (`cid`) ownership and Physical Region Page (`PRP`) page-boundary alignment
     invariants, while `branches` models out-of-order Completion Queue (`CQ`)
     Phase-Tag toggles.

---

### 6. Category F: Distributed Consensus, Deterministic Simulation Testing (DST), and Byzantine Fault Tolerance

Basis: normative + documentation + source + execution + derived

Category F covers 12 tool ecosystems addressing three Anneal use cases:
distributed state-machine replication and consensus refinement
(`anneal-consensus-smr` / `5.11`), deterministic simulation testing (`DST`)
trace refinement and linearizability checking (`anneal-dst-trace` / `5.11`), and
Byzantine fault-tolerant (`BFT`) quorum intersection and equivocation detection
(`anneal-bft-quorum` / `5.11`).

#### 6.1 Mechanized Distributed Systems & Consensus Verifiers (`IronFleet`, `Verdi`/`Cheerios`, `Anvil`, `Aneris`/`Grove`, `Ivy`/`I4`/`DistAI`, `Veil`, `Velisarios`, `ByMC`, `Apalache`)

1. **Goals, Lineage, and Architecture of Each Tool:**
   - **`IronFleet` (`microsoft/Ironclad@2fe4dcdc323b92e93f759cc3e373521366b7f691`):**
     Developed by Chris Hawblitzel, Jon Howell, Manos Kapritsos, Jacob Lorch,
     Bryan Parno, Michael Roberts, Srinath Setty, and Brian Zill at Microsoft
     Research (SOSP 2015, DOI `10.1145/2815400.2815428`), `IronFleet` verified
     practical Multi-Paxos (`IronRSL`) and sharded key-value store (`IronKV`)
     implementations in Dafny, proving **both safety and liveness** (eventual
     progress under TLA+-style temporal fairness formulas embedded in Dafny).
     `IronFleet`'s key architectural split layers a global TLA+ distributed
     protocol layer over a per-host imperative I/O refinement layer connected by
     verified UDP packet marshaling.
   - **`Verdi` (`uwplse/verdi@7e1641b758d8f0032aa7de63620bc115330e0a6b`) and
     `Cheerios` (`uwplse/cheerios@5c9318c269f9cae1c1c6583a44405969ac0be0dd`):**
     Developed by James Wilcox, Doug Woos, Pavel Panchekha, Zachary Tatlock et
     al. at the University of Washington (PLDI 2015 / CPP 2016), `Verdi`
     verifies distributed systems (most famously **Verdi-Raft**, a 50,000-line
     Coq proof of the Raft consensus protocol's Linearizability and State Machine
     Safety) using **Verified System Transformers (`VST`s)** that transform a
     protocol proved under an idealized fault model into one tolerant of packet
     duplication, reordering, and node crash-recovery, paired with `Cheerios`
     verified wire-format serialization.
   - **`Anvil` (`anvil-verifier/anvil@e83ea0f5516ce2ece26740266165180018741e66`):**
     Developed by Xudong Sun, Wenjie Ma, Jiawei Tyler Gu, Zicheng Ma, Tej
     Chajed, Jon Howell, Andrea Lattuada, Oded Padon, Lalith Suresh, Adriana
     Szekeres, and Tianyin Xu at UIUC, VMware Research, and UW-Madison (OSDI
     2024), `Anvil` uses **Verus** (`verus-tla` temporal logic embedding in Rust)
     to build and verify production **Kubernetes controllers** (ZooKeeper,
     RabbitMQ, FluentBit operators), proving **Eventually Stable Reconciliation
     (`ESR` liveness)** and safety across API-server crashes, watch-event drops,
     and controller restarts.
   - **`Aneris` (`logsem/aneris@59ae37946838df77fb2c573803b68462a3af9d0f`) and
     `Grove` (`mit-pdos/grove@f3f405eaab259c391906e1088aac35216bac11a4`):**
     `Aneris` (Krogh-Jespersen, Timany, Ohlenbusch, Gregersen, Birkedal, ESOP
     2020) is an `Iris`-based higher-order distributed separation logic in Coq
     with socket/IP points-to assertions ($a \mapsto_{\text{socket}} \Phi$).
     `Grove` (Sharma, Kaashoek, Zeldovich, SOSP 2023) extends `Perennial` and
     `GooseLang` with *time-bounded leases*, monotonic epoch Ghost state, and RPC
     specifications to verify **`GroveKV`**, a distributed, multithreaded,
     crash-safe key-value store with reconfiguration in Go.
   - **`Ivy` (`kenmcmil/ivy@8858a0241ed37141757b7a051acc24c58e49c2f3`), `I4`
     (Ma et al. SOSP 2019), `DistAI` (Yao et al. OSDI 2021), and `Veil`
     (`verse-lab/veil@eb458cb602d3cf9a19d8f5d8af21edcf27775c8e`):**
     Kenneth McMillan and Oded Padon designed `Ivy` (PLDI 2016 / POPL 2018) to
     keep distributed protocol verification inside the **Effectively
     Propositional (`EPR`, $\exists^* \forall^*$ Bernays-Schönfinkel-Ramsey)**
     decidable fragment of first-order logic, where Z3 produces finite
     counterexample models whenever an inductive invariant fails. `I4` and
     `DistAI` automatically synthesize inductive invariants for `Ivy` protocols
     from finite-instance cutoffs. `Veil` (Verse Lab, CAV/POPL 2025–2026) brings
     `Ivy`-style two-state relational transition specifications and automated
     SMT/`lean-auto` discharge directly into **Lean 4** (`ActionSpec.lean`).
   - **Byzantine Fault Tolerance & Symbolic Model Checkers (`Velisarios` at
     `vrahli/Velisarios@6fb353b18610cd79210755fcc90123536c367aaa`, Rahli et al.
     ESOP 2018; `ByMC` at `konnov/bymc@266366f738bce9dbd5d04336fd9123d85ae2bca1`,
     Konnov, Veith, Widder, POPL 2017; `Apalache` at
     `apalache-mc/apalache@9a13950e0ebddcb3d7a79cb9e854b0866e1c5712`, Konnov,
     Kukovec, Tran, OOPSLA 2019):**
     `Velisarios` verifies `PBFT` in Coq using logic-of-events epistemic causal
     chains. `ByMC` verifies parameterized threshold-guarded BFT algorithms
     ($N > 3t$, quorum threshold $2t + 1$) for unbounded $N$ via counter
     abstraction and threshold automata. `Apalache` translates TLA+ specifications
     (such as Tendermint BFT accountability and IBC cross-chain protocols) into
     bounded symbolic SMT (`Z3`) queries.

#### 6.2 Deterministic Simulation Testing (`DST`) and Linearizability Oracles (`Turmoil`, `MadSim`, `FoundationDB`, `TigerBeetle VOPR`, `Porcupine`, `Knossos`, `Stateright`)

1. **Goals, Lineage, and Architecture of Each Tool:**
   - **`FoundationDB` Simulation (`apple/foundationdb@bcdefac96277de4a26d59cdf352d478391d347f9`),
     `TigerBeetle VOPR` (`tigerbeetle/tigerbeetle@0450c32b2c3c3ab6114f3402cc601341cc8192aa`),
     `Turmoil` (`tokio-rs/turmoil@6a1f50223b5a1884bf8890053c85eec04a8af267`),
     and `MadSim` (`madsim-rs/madsim@519950efb4711464f300ed7edf2967ed62d5f502`):**
     Pioneered by `FoundationDB` (Zhou et al. SIGMOD 2021) and extended to
     storage consensus by `TigerBeetle`'s Viewstamped Operation Replicator
     (`VOPR`, which combines network partitions/reordering with storage gray
     failures, directed bitrot, and misdirected DMA writes), Deterministic
     Simulation Testing multiplexing an entire cluster of nodes onto a single OS
     thread driven by a deterministic PRNG `seed : u64`. In Rust, `Turmoil`
     provides simulated network links and host crashes for Tokio services, while
     `MadSim` (used in `RisingWave` and `tikv`) replaces `tokio`, `tonic`, `time`,
     and `rand` at link/compile time so unmodified async Rust code runs
     deterministically from a 64-bit seed.
   - **`Porcupine` (`anishathalye/porcupine@97cd067defd99df172053ba7f4ca5bbae57fe446`),
     `Knossos` (`jepsen-io/knossos@14ead19fb3d24745429e367c8ae9779e147ff6cb`),
     and `Stateright` (`stateright/stateright@ab8c8be9341505e0f71edbe5dd88ed275bd976a4`):**
     `Knossos` (Kingsbury / Jepsen) and `Porcupine` (Athalye, MIT) check whether
     a recorded concurrent invocation/response history $H$ is linearizable with
     respect to a sequential specification (`Porcupine` exploits $P$-compositionality
     and bitset state caching in Go to run $1000\times$ faster than `Knossos`).
     `Stateright` embeds both an explicit-state breadth/depth-first model
     checker and a Wing-Gong linearizability tester directly in Rust for actor
     systems (`Actor::on_msg`, `Actor::on_timeout`).

2. **Mapping onto Anneal's Four `trusted/` Primitives and Architectural Insights:**
   - **Two-Tier Distributed Composition (`IronFleet` / `Verdi` Pattern in Anneal):**
     1. **Tier 1 (Node Handler Refinement):** Each node's Rust event handler
        `step_msg(msg) -> Vec<OutMsg>` is verified via `Compiles L_io_node
        L_mir_node codec_node`, where wire serialization (`Cheerios`/`EverParse`/
        `zerocopy`) directly instantiates `BehaviorCodec`'s partial bijection
        (`decodeOut (encodeOut msg) = some msg`) and socket/WAL calls use
        `StepResult.externalCall`.
     2. **Tier 2 (Network Protocol Refinement):** $N$ instances of `L_io_node`
        are embedded into `L_network : SmallStepMachine`, where packet delivery,
        duplication, dropping, node crashes, or Byzantine equivocations (bounded
        by $|B| \le f < N/3$ in `pre : Query → Prop`) are transitions under
        `StepResult.choice .demonic`, discharging `Abstracts L_central_smr
        L_network`.
   - **Critical Stress Test 5B: Infinite Reactive Server Loops vs.
     `EventualOut.diverges` (`diverging_reactive_loop_erases_trace` and
     `universal_horizon_preserves_safety_traces`, lines 545–576 of
     [ConcurrencySystemsStressTests.lean](support/ConcurrencySystemsStressTests.lean)):**
     As proved in `diverging_reactive_loop_erases_trace`, any non-terminating
     reactive server (`loop { select! { ... } }`) has `ReachesSafeTerminal = False`
     and produces only `EventualOut.diverges`—which carries **no `List Obs`
     trace**! Thus two non-terminating UB-free consensus nodes that emit
     completely different client commit histories would have identical
     `EventualBehaviorOf` (`{ .diverges }`) if run without a stopping horizon!
     As mechanized in `universal_horizon_preserves_safety_traces`, Anneal solves
     this **without changing `trusted/lean/`** via the **Universal Finite-Horizon
     Query Pattern**: parameterizing the reactive harness by `Query := InitState
     × (horizon : Nat)` causes every run to halt cleanly in `.terminated trace
     (.normal ())` after `horizon` events, so `Abstracts` and `ProductiveOn`
     quantify universally over all finite prefixes $K \in \mathbb{N}$!

| Tool / Framework | Primary Subject Pin | Verification / Testing Regime | Core Innovation | Anneal `trusted/` Primitive Mapping |
| :--- | :--- | :--- | :--- | :--- |
| **`IronFleet`** | `microsoft/Ironclad@2fe4dcdc323b` | Deductive Dafny + TLA+ liveness (`Paxos`/`KV`) | Layers local I/O refinement under global TLA+ spec | Two-tier `Compiles L_node L_mir` + `Abstracts L_smr L_net` |
| **`Verdi` & `Cheerios`** | `uwplse/verdi@7e1641b758d8` / `uwplse/cheerios@5c9318c269f9` | Coq Verified System Transformers (`Verdi-Raft`) | Compositional fault-model transformers + wire codecs | `BehaviorCodec` bijective wire serialization + `Abstracts` |
| **`Anvil`** | `anvil-verifier/anvil@e83ea0f5516c` | Verus (`verus-tla`) K8s controllers | Proves Eventually Stable Reconciliation (`ESR`) in Rust | Fair-schedule `Query` + `Universal Finite-Horizon` |
| **`Aneris` & `Grove`** | `logsem/aneris@59ae37946838` / `mit-pdos/grove@f3f405eaab25` | Coq/Iris distributed & crash-safe RPC (`GroveKV`) | Time-bounded leases + crash-idempotent RPCs | Ghost lease erasure in `theory/` $\to$ `L_net.ProductiveOn` |
| **`Ivy` & `Veil`** | `kenmcmil/ivy@8858a0241ed3` / `verse-lab/veil@eb458cb602d3` | Decidable `EPR` ($\exists^*\forall^*$) protocol invariants | Decidable SMT inductive invariant checking in Lean 4 | Certifies 1-step `SmallStepMachine` inductive invariants |
| **`Turmoil` / `MadSim` / `VOPR`** | `tokio-rs/turmoil@6a1f50223b5a` / `tigerbeetle/tigerbeetle@0450c32b2c3c` | Deterministic Simulation Testing (`DST`) | Single-thread seeded PRNG fault/corruption injection | Singleton `L_sim` + `ProductiveOn` proves strict determinism |
| **`Porcupine` / `Stateright`** | `anishathalye/porcupine@97cd067defd9` / `stateright/stateright@ab8c8be93415` | Linearizability history & explicit-state checking | $P$-compositional bitset history linearizability | Finite-horizon invocation/response `Obs` trace inclusion |
| **`Velisarios` / `ByMC` / `Apalache`** | `vrahli/Velisarios@6fb353b18610` / `apalache-mc/apalache@9a13950e0ebd` | Coq `PBFT` / threshold automata / symbolic TLA+ | Byzantine quorum intersection ($2f+1$ of $3f+1$) | `pre := |ByzantineSet| ≤ f` + `StepResult.choice .demonic` |

---

### 7. Category G: Authoritative ISA Semantics and Cycle-Accurate RTL Pipeline Co-Verification

Basis: normative + documentation + source + execution + derived

Category G covers 8 tool ecosystems addressing two Anneal use cases: bridging
authoritative vendor ISA specifications (`Sail`, Arm `ASL`, `L3`) to Anneal's
`Language` for inline assembly (`core::arch::asm!`) and intrinsics
(`anneal-isa-sail` / `5.20`), and cycle-accurate hardware RTL pipeline
refinement and speculative leakage verification (`anneal-rtl-pipe` / `5.17`,
`5.18` & `5.20`).

#### 7.1 Authoritative ISA Specification Languages and Symbolic Engines (`Sail`, `sail-riscv`, `sail-arm`, `Isla`/`Islaris`, Arm `ASL`, `L3`)

1. **Goals, Lineage, and Architecture of Each Tool:**
   - **`Sail` (`rems-project/sail@7e0e53d183cad75b8f36bfbbecc0ef75614a8418`,
     v0.20.3), `sail-riscv` (`riscv/sail-riscv@a83603b6995428b9df2c464f98e18a7b0ae488fe`),
     and `sail-arm` (`rems-project/sail-arm@7d0581642d0e3aaca367bbc5650aca7c53057543`):**
     Developed by Alasdair Armstrong, Thomas Bauereiss, Brian Campbell, Alastair
     Reid, Kathryn E. Gray, Robert M. Norton, Prashanth Mundkur, Mark Wassell,
     Jon French, Christopher Pulte, Shaked Flur, Ian Stark, Neel Krishnaswami,
     and Peter Sewell at Cambridge and Edinburgh (`REMS`, POPL 2019, DOI
     `10.1145/3290364`), `Sail` is a first-order imperative architecture
     definition language with lightweight dependent bitvector length types
     (`bits('n)`) that serves as the **official golden ISA reference** for
     RISC-V (`sail-riscv`) and translates Arm's authoritative `ASL` for
     `Armv8-A`/`Armv9.4-A` (`sail-arm`) and CHERI (`sail-cheri-riscv`,
     `sail-morello`). Crucially, `Sail 0.20.3` includes a **Lean 4 backend**
     (`sail -lean`, `src/sail_lean_backend/sail_plugin_lean.ml`, supported by
     `rems-project/lean-sail@01bb54c7c8a69e52ba11863c67e7c403a6cd198a` and
     `opencompl/sail-riscv-lean@51c635c460125ac87955d061fcd902ce03b8011f`) that
     compiles instruction semantics into a pure Lean 4 free monad `PreSailM`
     over register reads/writes, memory effects, nondeterministic choices, and
     exceptions.
   - **`Isla` (`rems-project/isla@e9b5d945394277656593a0d429466d7fa0a2b4b3`):**
     Symbolic execution and axiomatic concurrency engine for `Sail` IR (Bauereiss
     et al. CAV 2021) that evaluates compiled `Sail` instruction semantics over
     Z3 bitvectors and integrates with `.cat` concurrency models (`rems-project/archsem-lean@318583a5f2052c039c25dfd69a3beec0b0a27090`)
     and `Islaris` Coq proofs.
   - **Arm `ASL` (`alastairreid/asl-interpreter@16260979137c38339743a04b7fd5d9f0fa8a6ee5`)
     and `L3` (Anthony Fox, Cambridge, ITP 2012 / FMCAD 2015):**
     Alastair Reid developed Arm's internal machine-readable Architecture
     Specification Language (`ASL`, FMCAD 2016 / CAV 2016) used both to generate
     the Arm Architecture Reference Manual XML and to test RTL against ISA
     semantics. `L3` is a domain-specific ISA specification language that
     extracts clean monadic specifications into `HOL4` (`HOL-Theorem-Prover/HOL@166fd15df77be1f2e79dc8592a933b1a65540526`),
     powering the CakeML and seL4 binary lifters.

#### 7.2 Rule-Based Hardware HDLs, Pipeline Refinement, and RTL Formal Verification (`Kami`, `Kôika`, `SilverOak`/`Bedrock2`, `LeaVe`, `SymbiYosys`/`riscv-formal`/`UCLID5`)

1. **Goals, Lineage, and Architecture of Each Tool:**
   - **`Kami` (`mit-plv/kami@9217329eb4e1d751f28ab175ebab230b1e8fd4da`) and
     `Kôika` (`mit-plv/koika@8921e30434d9e351c49df84c9aa14e72b0456ad0`):**
     Developed at MIT PLV by Joonwon Choi, Muralidaran Vijayaraghavan, Benjamin
     Sherman, Adam Chlipala, and Arvind (`Kami`, ICFP 2017) and Clément
     Pit-Claudel, Thomas Bourgeat, Stella Lau, and Adam Chlipala (`Kôika`,
     PLDI 2020, DOI `10.1145/3385412.3385965`), these Coq frameworks formalize
     Bluespec-style guarded atomic actions (`Rules`). `Kami` proves modular
     trace refinement (`impl ⊑ spec`) of pipelined multi-core RISC-V processors
     with cache-coherence directories. `Kôika` introduces a dynamic conflict
     scheduler with **One-Rule-At-A-Time (`ORAAT`)** theorem preservation: even
     though the synthesized Verilog hardware executes multiple rules in parallel
     within a single clock cycle via bypasses (`read0`/`write0`/`read1`/`write1`
     Ehrhard-style Ephemeral History Registers), `Kôika`'s verified compiler
     proves that every single-cycle hardware transition equals a sequential
     atomic composition of rules!
   - **`SilverOak` (`project-oak/silveroak@cccfdb4e19c5906256d2ed4487bf1a0aa2fab99e`)
     and `Bedrock2` (`mit-plv/bedrock2@757f17c6083bf8d43b5293a0db545c8d0aa32a13`):**
     Developed by Google Research (`SilverOak` Cava monadic circuit DSL in Coq,
     PLDI 2021) and MIT PLV (`Bedrock2`, Erbsen et al. PLDI 2021, DOI
     `10.1145/3453483.3454061`), this joint stack proved end-to-end
     **hardware-software co-verification** for an **OpenTitan** silicon
     root-of-trust platform: C-like firmware (`Bedrock2`), RISC-V machine code
     (`riscv-coq@45dc8dfc17c77aabb433355b9d39edc6bfd429ae`), and cycle-accurate
     `Kami`/`SilverOak` AES/HMAC hardware accelerator RTL are composed into a
     single Coq theorem over external I/O pin traces!
   - **`LeaVe` (Wang, Mohr, von Gleissenthall, Reineke, Guarnieri, ACM CCS 2023,
     DOI `10.1145/3576915.3623135` / arXiv `2305.06979`):**
     Verifies open-source RISC-V RTL processor cores (`Ibex`, `CVA6`) against
     **ISA-level hardware-software leakage contracts** ($\mathcal{L}_{\text{contract}}$),
     proving via relational 2-safety invariants in Yosys/SMT that speculative/out-of-order
     microarchitectural state (pipeline buffers, branch predictors, data caches)
     leaks no more information on the attacker-observable trace than permitted
     by the ISA contract.
   - **`SymbiYosys` (`YosysHQ/sby@79fc9eddca5e33a28cc2f2cd19c9825efd9a7255`),
     `riscv-formal` (`YosysHQ/riscv-formal@c992aa61fdfe0846c5ed90324c596202a1c69b76`),
     and `UCLID5` (`uclid-org/uclid@a4e4e7a22780833c86d6a650af2fcf88a7d00a06`):**
     `SymbiYosys` (Claire Wolf / YosysHQ) orchestrates `Yosys` RTL synthesis into
     `SMT2`/`BTOR2`/`AIGER` checked by `Bitwuzla`, `Z3`, `ABC` (`PDR`/`IC3`), and
     `pono`. `riscv-formal` defines the industry-standard **RISC-V Formal
     Interface (`RVFI`)**: a tap bundle (`rvfi_valid`, `rvfi_order`, `rvfi_insn`,
     `rvfi_rd_addr`, `rvfi_rd_wdata`, `rvfi_mem_addr`) emitted whenever a
     pipelined core retires an instruction, checked against per-instruction golden
     models. `UCLID5` (Seshia, Subramanyan et al., CAV 2018) automates
     **Burch-Dill pipeline flushing** (Burch & Dill, CAV 1994) and hyperproperty
     verification of speculative processors and trusted execution environments.

2. **Mapping onto Anneal's Four `trusted/` Primitives and Architectural Insights:**
   - **Authoritative `Sail -lean` Bridge & Scratch-Register Quotienting
     (`anneal-isa-sail`):** `Sail 0.20.3`'s Lean 4 free monad maps directly to a
     `SmallStepMachine` (`L_sail_isa`), where architectural `UNDEFINED` or
     privilege faults emit `StepResult.failed .ub`. At an inline assembly
     `asm!(...)` boundary in MIR, `StepResult.externalCall` is discharged by
     refinement against `L_sail_isa`. As highlighted in `raw_graph_codec_impossible`,
     because caller-saved scratch registers (`r10`, `r11`, `NZCV`/`RFLAGS`) hold
     clobbered values at function return that do not appear in the high-level
     MIR return value, `L_sail_isa.Out` at the ABI boundary must project out dead
     caller-saved registers (or `decodeOut` must restrict to a canonical zeroed
     scratch representation).
   - **Mechanized Burch-Dill Pipeline Flushing & Stutter-Insensitive Trace
     Refinement (`burchDillCodec` and `burch_dill_rtl_refines_isa`, lines
     578–637 of [ConcurrencySystemsStressTests.lean](support/ConcurrencySystemsStressTests.lean)):**
     1. In `L_rtl` (`EventualBehaviorOf M_rtl`), the machine steps once per
        *clock cycle*, emitting `some (RetiredCommit ...)` (`RVFI` packet) only
        when the Writeback (`WB`) / Reorder Buffer (`ROB`) retires an
        instruction; pipeline stalls, cache misses, and branch-misprediction
        flushes step with `obs = none` (`ReachesSafeTerminal.stepNone`)!
     2. Because `EventualBehaviorOf` accumulates `trace : List Obs` only from
        `stepSome` transitions, multi-cycle hardware pipeline stalls ($k \text{
        cycles} \to 1 \text{ retired instruction}$) are **automatically
        stutter-equivalent** to single-step ISA execution in `L_isa`!
     3. As proved in `burchDillCodec` and `burch_dill_rtl_refines_isa`, the
        Burch-Dill pipeline flush abstraction (`robEmpty == true`) is encoded as
        a partial `decodeOut : PipeOut → Option IsaOut` that returns `some
        p.archReg` on flushed states and `none` otherwise, satisfying both
        `encode_of_decode_some` and `obs_decodeOut`!

---

### 8. Cross-Cutting Synthesis: Architectural Stress-Test Matrix for Anneal's Four Trusted Primitives

Basis: source + execution + derived

The table below synthesizes the six structural stress tests uncovered across all
78 tools in Categories A–G, their mechanized theorems in
[ConcurrencySystemsStressTests.lean](support/ConcurrencySystemsStressTests.lean),
and the exact design guidance they establish for Anneal's `trusted/lean/` TCB:

| Stress Test ID & Phenomenon | Categories & Representative Tools | Mechanized Theorem in `support/ConcurrencySystemsStressTests.lean` | How Anneal's 4 `trusted/` Primitives Handle It & TCB Guidance |
| :--- | :--- | :--- | :--- |
| **ST-1: Partial-Bijection Law on `BehaviorCodec` (`decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`)** | **Cat A, C, F, G:** `Herd7`/`GenMC`/`IMM` execution graphs, `CertiKOS`/`Sail` caller-saved scratch registers, `Verdi`/`Cheerios` wire formats, `UCLID5`/`Kami` pipeline ROB | `raw_graph_codec_impossible` (lines 298–313), `AxiomaticWmmModel.toLanguage` (lines 323–337), `burchDillCodec` (lines 604–630) | Any unobservable concrete witness in `L₂.Out` (e.g., `scheduleId` in an execution graph or clobbered `r11`) causes multiple `o₂ ≠ o₂'` to decode to `some o₁`, violating `encode_of_decode_some`. **Guidance:** Project/quotient internal schedule and scratch state inside `L₂.sem` before the codec boundary, or restrict `decodeOut` to canonical flushed terminal states (`robEmpty = true`, `storeBuf = []`). |
| **ST-2: Axiomatic Whole-Execution Graphs vs. Operational `SmallStepMachine` & Self-Refinement** | **Cat A, E:** `RC11`, `IMM`, `LKMM`, `Px86`, `PArm`, `Memorax`, `Musketeer`, `vsyncer` | `AxiomaticWmmModel.toLanguage` (lines 323–337), `sc_robustness_transfer` (lines 343–353) | Keeping `Language SemObs` (Primitive #1) independent of `SmallStepMachine` (Primitive #4) allows axiomatic graph models and operational machines to compose via `Compiles`/`Abstracts`. Weak-memory robustness and fence synthesis are expressed as self-refinement `Compiles L_SC L_WMM idCodec P P'`. |
| **ST-3: Fair Liveness & `LL/SC` Forward Progress Under Unfair `StepResult.choice .demonic`** | **Cat A, B, F:** `Promising-ARM` `ldxr`/`stxr`, `Fair-Iris`/`Trillium`, `LiLi`/`TaDA-Live`, `IronFleet`, `Anvil` | `unfair_demonic_admits_divergence` (lines 370–376), `fairSchedule_inhabited` (lines 386–388), `fair_schedule_in_query_starvation_free` (lines 398–453) | Pure `.choice .demonic` includes unfair infinite schedules that starve runnable threads or fail `stxr`/`sc` forever (`.diverges`). **Guidance:** Use the **Fair-Schedule-in-Query Pattern** (`Query := State × Schedule`, `pre := IsFairSchedule`, checked non-vacuous by `InhabitedPre`) so `SmallStepMachine` needs zero Büchi/Rabin fairness primitives. |
| **ST-4: Hardware Datasheet, DMA Ownership & TOCTOU Gates via `StepResult.externalCall`** | **Cat C, D:** `Kani` SVD, `Termite-2`, `Corral`/`SDV`, `SeKVM` SMMU, `embassy`/`embedded-dma`, `VeriSMo` VirtIO | `mmio_protocol_violation_is_ub` (lines 483–490), `mmio_valid_driver_productive` (lines 495–523) | `StepResult.externalCall boundaryInv branches` turns any SVD register protocol violation, un-cleaned cache line, or concurrent CPU/DMA borrow collision (`boundaryInv = false`) into `.failed .ub` (`defined = False`), while modeling untrusted device/host responses via `.choice .demonic branches`. |
| **ST-5: Multi-Crash Recovery Idempotence & Trace-Erasing `EventualOut.diverges` on Infinite Loops** | **Cat C, E, F, G:** `Perennial`/`FSCQ`/`VeriBetrKV`/`verified-storage`, `seL4`, `IronFleet`/`Verdi-Raft`, `Kami`/`Kôika` | `crash_recovery_idempotent_converges` (lines 532–543), `diverging_reactive_loop_erases_trace` (lines 563–565), `universal_horizon_preserves_safety_traces` (lines 571–576) | (a) Demonic crash transitions inside `SmallStepMachine` verify nested crash-recovery idempotence without a separate crash logic in the TCB. (b) Because `EventualOut.diverges` erases `List Obs`, non-terminating reactive loops (`loop { poll() }`) must use the **Universal Finite-Horizon Query Pattern** (`Query := State × Nat`) to preserve all finite prefix traces. |
| **ST-6: Positive Per-Obligation `VerificationResult` Isolation in Hybrid Systems Stacks** | **Cat B, C, D, F:** `Asterinas ostd`, `VeriSMo`, `seL4`, `Anvil`, `VSync` | `verificationResult_non_contamination` (lines 160–175) | Positive disjunction `ob.id ∈ waived ∨ ob.prop` allows systems crates to waive hardware/assembly boundary obligations under an explicit `TrustPolicy` without allowing `False.elim` to contaminate verified Rust obligations. |

### Phase-2 Long-Tail Ecosystem Additions and Primitive Mappings

Basis: documentation, derived — incorporates the Stage-2 exhaustive long-tail
tool discovery sweep (`agent_a_shard_*_tools.md`) into the package's tool
taxonomy and four-primitive `trusted/` mapping.

- **`rmem` (`rems-project/rmem`), Awamoche (OOPSLA 2023 / ASPLOS 2024), Deagle
  (`thufv/Deagle`), and Weakestmo (`weakmemory/weakestmo`, POPL 2019):**
  Operational ARMv8/RISC-V concurrency explorer, await-aware stateless model
  checking for spinlocks, and event-structure weak-memory compilation in Coq.
- **Diaframe (`iris/diaframe`, PLDI 2022 / OOPSLA 2023), Raven (`nyu-
  acsys/raven`, CAV 2024), Steel/Pulse (`FStarLang/pulse`), Anchor, and Plankton
  (`meyer-wolff/plankton`):** Automated Iris bi-abduction, SMT-backed first-
  order Iris concurrency verification, Lipton mover checking, and automated SMR
  hazard-pointer/EBR verification.
- **Velosiraptor (`velosiraptor/velosiraptor`, ASPLOS 2025), Sockeye
  (`Sockeye3`), Hyperkernel (`uw-unsat/hyperkernel`), Serval, and Nickel:**
  Declarative MMU/MPU page-table synthesizer/verifier, SoC MMIO/IOMMU decoding-
  net verifier, and symbolic kernel/monitor verifiers.
- **Flashix (KIV, TSE 2021), SibylFS (SOSP 2015), CrashMonkey/Ace (OSDI 2018),
  Agamotto (OSDI 2020), and Vinter (`kit-os/vinter`, ATC 2022):** Verified
  crash-safe flash/POSIX filesystems and persistent-memory (`clwb`/`sfence`)
  crash-consistency verifiers.
- **DuoAI (`OrderLab/DuoAI`, OSDI 2022), SWISS (`VMware-Research/swiss`, SOSP
  2021), `mypyvy`, Disel, and Twins (NSDI 2021):** Automated distributed
  inductive-invariant synthesizers, distributed separation logic, and Byzantine
  equivocation generators.
- **`sail_lean_backend` / `sail-riscv-lean` (`opencompl/sail-riscv-lean`),
  Sparkle (`Verilean/sparkle`), and Knox (`mit-pdos/knox`, OSDI 2022):**
  Official Lean 4 backends for Sail RV64GCV/ARM, native Lean 4 SystemVerilog RTL
  equivalence prover, and hardware-software co-verification.

---

### Part II — Historical Verification Failures, Root-Cause Postmortems, and Architectural Defenses

### 1. Weak-Memory Model & Atomic Compilation Failures

#### 1.1 C/C++11-to-Power and ARMv7/ARMv8 Atomic Compilation Failures (Manerkar et al. MICRO 2016; Lahav et al. PLDI 2017 `RC11`)

- **Historical Context and "Verified" Premise:**
  Following the formalization of the C/C++11 memory model by Batty et al.
  (*POPL 2011*), two families of compiler mappings for sequentially consistent
  (`memory_order_seq_cst` / `Ordering::SeqCst`) atomics on weakly ordered
  non-multi-copy-atomic architectures (IBM POWER and ARMv7) were widely deployed
  and believed to have been mathematically proven sound:
  1. **Leading-sync mapping** (used by GCC and described by Batty et al.):
     $$\mathsf{Load}_{\mathsf{sc}} \mapsto \texttt{hwsync; ld; cmp; bc; isync} \quad (\text{or } \texttt{dmb; ldr; dmb}), \qquad \mathsf{Store}_{\mathsf{sc}} \mapsto \texttt{hwsync; st}$$
  2. **Trailing-sync mapping** (proposed by McKenney & Silvera and implemented
     in LLVM/Clang for Power and ARMv7):
     $$\mathsf{Load}_{\mathsf{sc}} \mapsto \texttt{ld; cmp; bc; isync} \quad (\text{or } \texttt{ldr; dmb}), \qquad \mathsf{Store}_{\mathsf{sc}} \mapsto \texttt{lwsync; st; hwsync} \quad (\text{or } \texttt{dmb; str; dmb})$$
  Concurrently, ARMv8-A introduced dedicated load-acquire (`LDAR`) and
  store-release (`STLR`) instructions explicitly designed by architects so that
  `STLR` followed by `LDAR` would not reorder, enabling a fence-free mapping:
  $$\mathsf{Load}_{\mathsf{sc}} \mapsto \texttt{LDAR}, \qquad \mathsf{Store}_{\mathsf{sc}} \mapsto \texttt{STLR}$$

- **Technical Root-Cause Analysis:**
  1. **Manerkar et al. (*MICRO 2016*, DOI `10.1109/MICRO.2016.7783747`):**
     Using the `PipeCheck` and `CCICheck` tools, Manerkar et al. discovered two
     distinct classes of counterexamples:
     - **Standalone Trailing-Sync Unsoundness under Original C-2011 (`R` / `2+2W` /
       `Z6.U` litmus variants):** In the original C-2011 standard (ISO/IEC
       9899:2011 / 14882:2011), the total sequential consistency order $S$ on
       `SeqCst` operations was only required to be consistent with
       happens-before ($\mathsf{hb}$) and modification order ($\mathsf{mo}$)
       separately, without requiring $S \cup \mathsf{hb}$ or $S \cup \mathsf{eco}$
       to be acyclic across mixed release/acquire and `SeqCst` accesses. Under
       the trailing-sync mapping on Power/ARMv7, a `SeqCst` load has *no*
       leading heavyweight fence (`hwsync`/`dmb`) before the load instruction.
       Consequently, a prior non-`SeqCst` release store (`lwsync; st`) in the
       same thread is not ordered by a full barrier before the `SeqCst` load,
       allowing hardware store buffering and non-multi-copy-atomic write
       propagation to produce an execution forbidden by C-2011!
     - **The Original Proof Loophole:** Why had earlier hand-written proofs
       claimed trailing-sync was sound? Those proofs assumed a strengthened
       intermediate lemma—that every `SeqCst` store is immediately visible to
       all threads in a global order—or only checked pure `SeqCst` programs
       (DRF-SC) rather than mixed `SeqCst` + `Release`/`Acquire`/`Relaxed`
       programs (`Z6.U`).
     - **ABI Linking Hazard (Mixing Leading-Sync GCC and Trailing-Sync LLVM, or
       ARMv7 `dmb` and ARMv8 `LDAR`/`STLR`):** Even more catastrophically, if
       Thread 1 is compiled with a leading-sync compiler (`hwsync; st` for
       `Store(SeqCst)`) and Thread 2 is compiled with a trailing-sync compiler
       (`ld; isync` for `Load(SeqCst)`), then in the classic Store-Buffering
       (`SB`) litmus test:
       $$\text{Thread 1: } x_{\mathsf{sc}} := 1;\; r_0 := y_{\mathsf{sc}} \qquad \parallel \qquad \text{Thread 2: } y_{\mathsf{sc}} := 1;\; r_1 := x_{\mathsf{sc}}$$
       the compiled code has **zero** `hwsync`/`dmb` barrier *between* the
       `Store(SeqCst)` and the subsequent `Load(SeqCst)`! Both stores stay in
       local store buffers while both loads read $0$, yielding $(r_0 = 0, r_1 = 0)$
       and violating sequential consistency even for purely `SeqCst` programs!
       Similarly, on an ARMv8 processor running mixed ARMv7 (`dmb`) and ARMv8
       (`STLR`/`LDAR`) code—or when `STLR` to $x$ is followed by a relaxed/acquire
       read before `STLR` drains—mixing conventions breaks `SeqCst` restoration.
  2. **Lahav et al. (*PLDI 2017*, `RC11`, DOI `10.1145/3062341.3062352`):**
     Lahav et al. proved an even deeper impossibility result: under the
     published C-2011 specification (including Batty et al.'s 2016 strengthens),
     **even the standard leading-sync Power mapping (`hwsync` before every
     `SeqCst` access) was unsound** for the `Z6.U` litmus test! Specifically,
     C-2011 required $\mathsf{hb}$ edges and $\mathsf{mo}$ edges to constrain $S$
     in a way that effectively demanded a heavyweight `hwsync` on *both* sides
     of `SeqCst` accesses when interacting with `Release`/`Acquire` RMW chains.
     To repair this without doubling fence overhead on Power/ARM, Lahav et al.
     defined **RC11 (Repaired C-2011)**:
     - Weakened the overly strong C-2011 `SeqCst` axiom to require acyclicity of
       $\mathsf{psc} = \mathsf{psc}_{\mathsf{base}} \cup \mathsf{psc}_{\mathsf{f}}$
       (where $\mathsf{psc}_{\mathsf{base}}$ orders `SeqCst` accesses via
       $\mathsf{hb}|_{\text{same-loc}}$ and $\mathsf{eco}$, and `SeqCst` fences
       $\mathsf{F}_{\mathsf{sc}}$ enforce full cross-location ordering
       $\mathsf{hb}; [\mathsf{F}_{\mathsf{sc}}]; \mathsf{hb}; \mathsf{eco}; \mathsf{hb}; [\mathsf{F}_{\mathsf{sc}}]; \mathsf{hb}$).
     - Strengthened relaxed atomics by forbidding $(\mathsf{po} \cup \mathsf{rf})$
       cycles to rule out basic Out-of-Thin-Air (`OOTA`) executions.

- **Mechanized Canary & Repair in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 150–199), `canary_unrepaired_seqcst_mapping_allows_sb_zero_zero`
  exhibits the buffered `(r0 = 0, r1 = 0)` state when `Store(SeqCst)` followed
  by `Load(SeqCst)` lacks a store-to-load drain invariant, and
  `repaired_rc11_seqcst_mapping_forbids_sb_zero_zero` proves that enforcing the
  `RC11` / ARMv8 store-drain ordering guarantees `r0 = 1 ∨ r1 = 1`.
  `Basis: normative specification + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives:**
  - **Primitive 1 (`Language SemObs` + `Compiles`):** Separate the axiomatic
    source memory model (`L_RC11 : Language SemObs`) from the target ISA memory
    model (`L_ARMv8 : Language SemObs`). Compiler backend lowering of atomics
    must be certified as a **whole-mapping `Compiles L_RC11 L_ARMv8 codec`**
    theorem rather than per-instruction macro templates, because leading-sync
    and trailing-sync mappings are individually sound for pure `SeqCst` only
    when *every* translation unit in the linked crate uses the *same* convention!
  - **Primitive 4 (`StepResult.externalCall` at FFI/ABI Boundaries):** When a
    Rust crate links against external C/C++ or assembly object files via
    `StepResult.externalCall`, the ABI `boundaryInv` must record the target's
    atomic lowering convention (e.g., ARMv8 `STLR`/`LDAR` vs. ARMv8.3 `STLR`/`LDAPR`
    with `DMB ISH` vs. legacy `DMB` barriers) so incompatible leading/trailing
    sync conventions cannot be silently linked together.

---

#### 1.2 Out-of-Thin-Air (`OOTA`) Values and the `Promising 1.0` to `Promising 2.0` Global Optimization Failure (Kang et al. POPL 2017; Lee et al. PLDI 2020)

- **Historical Context and "Verified" Premise:**
  In C/C++11 and Rust (`Ordering::Relaxed`), allowing hardware and compiler
  load-store reordering on relaxed atomics (`x.load(Relaxed); y.store(42, Relaxed)`)
  while forbidding self-justifying "Out-of-Thin-Air" (`OOTA`) cyclic executions
  (such as Thread 1 executing `r1 = x.load(Relaxed); y.store(r1, Relaxed)` and
  Thread 2 executing `r2 = y.load(Relaxed); x.store(r2, Relaxed)` both producing
  `42` when `x = y = 0` initially) was a 15-year open problem.
  `RC11` solved OOTA by forbidding $\mathsf{po} \cup \mathsf{rf}$ cycles, which
  unfortunately *forbids* load-store reordering (`r1 = x.load(Relaxed); y.store(1, Relaxed)`
  cannot be reordered by the compiler or ARM/Power hardware if $\mathsf{po} \cup \mathsf{rf}$
  acyclicity is enforced!).
  To allow load-store reordering without OOTA, Kang et al. (*POPL 2017*,
  **Promising Semantics 1.0**) introduced an operational model in which a thread
  can *promise* a future relaxed write $(y := 1 \text{ at timestamp } t)$ early,
  provided that at every step the thread can **certify** in a thread-local sequential
  simulation against the current global memory that it will eventually fulfill
  all of its outstanding promises.

- **Technical Root-Cause Analysis (Lee et al. *PLDI 2020*, DOI `10.1145/3385412.3386010`):**
  Lee et al. discovered that **Promising 1.0 is unsound for global compiler
  optimizations**—specifically **Global Value-Range Analysis** and **Register
  Promotion** of non-escaping or single-thread-accessed locations:
  1. **Uncapped Thread-Local Certification Violates Global Invariants:**
     Suppose variable $x$ and $y$ are initially $0$, and across the entire
     program no thread ever writes a value outside $\{0, 1\}$ to $x$ unless it
     first reads $x > 1$. Globally, $x \in \{0, 1\}$ is an inductive invariant!
     However, in `Promising 1.0`, to certify an early promise on $y$, a thread's
     local certification run was allowed to make *new speculative promises* or
     interact with future timestamps unconstrained by the global invariant
     $x \le 1$. If a compiler used Global Value-Range Analysis ($x \le 1$) to
     simplify an `else` branch (`if x > 1 { ... }` $\mapsto$ dead code removal),
     a certification path that relied on the dead branch disappeared in the
     optimized program—or conversely, the optimized program enabled a promise
     certification that was impossible in the source program (`Compiles` failure:
     $\llbracket P_{\text{opt}} \rrbracket_{\text{PS1}} \not\subseteq \llbracket P_{\text{src}} \rrbracket_{\text{PS1}}$)!
  2. **ARMv8 Relaxed RMW Compilation Penalty in `Promising 1.0`:**
     In `Promising 1.0`, compiling a `Relaxed` Read-Modify-Write (`fetch_add(1, Relaxed)`)
     to ARMv8 `ldxr`/`stxr` required inserting an unintended control-dependency +
     `isb` or barrier to prevent promises from bypassing the RMW dependency.
  3. **The `Promising 2.0` Repair:**
     Lee et al. replaced uncapped certification with **capped memory
     certification** (restricting certification runs to a closed/capped view of
     existing memory messages so certification cannot invent unbounded future
     values outside the reachable value range) and introduced **release-sequence
     reservation tokens** that validate fence-free `ldxr`/`stxr` compilation of
     `Relaxed` RMWs on ARMv8.

- **Mechanized Canary & Repair in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 200–224), `canary_promising1_uncapped_promise_breaks_global_range_opt`
  and `promising2_capped_memory_preserves_global_range_opt` mechanize the
  distinction between uncapped promise certification and `Promising 2.0` capped
  certification under a global range invariant $v \le 1$.
  `Basis: documentation + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives:**
  - **Primitive 1 (`Compiles` Transitivity Across Mid-End & Back-End Passes):**
    In Anneal, a mid-end optimization pass (such as Sub-Domain 3's Global Value
    Numbering, Sparse Conditional Constant Propagation, or Correlated Value
    Propagation `CVP`) and a back-end atomic-lowering pass compose by plain
    preorder transitivity (`Preorder.le_trans` on `Compiles`). If the
    intermediate concurrency `Language` (`L_MIR_WMM`) were instantiated with
    `Promising 1.0`, `CVP` (`Compiles L_MIR_WMM L_MIR_WMM idCodec`) would be
    **unprovable**! Anneal must therefore instantiate its weak-memory `Language`
    either with `RC11` (when forbidding load-store reordering on `Relaxed`
    atomics in exchange for simpler axiomatic reasoning) or with `Promising 2.0` /
    `IMM` (when permitting hardware load-store reordering while preserving sound
    global value-range optimizations).

---

#### 1.3 Real-World Rust Concurrent Data Structure & Reclamation Failures (`crossbeam-epoch`, `std::sync::Arc`, `std::sync::mpsc`, `RwLockReadGuard`, `tokio`, `once_cell`, `arc-swap`)

- **Historical Context and Catalog of Failures:**
  Even in Rust—where safe code statically prevents data races via `Send` and
  `Sync`—the foundational concurrent libraries and standard-library primitives
  implemented in `unsafe` Rust have suffered repeated, high-severity soundness
  failures across three dimensions:
  1. **`crossbeam-epoch` Missing `SeqCst` Barriers, Premature Reclamation, and
     Stacked Borrows Aliasing Violations (`crossbeam-rs/crossbeam` issues `#462`,
     `#535`, and `RUSTSEC-2022-0040` / `CVE-2022-23639`):**
     - *Epoch-Based Reclamation (`EBR`) Barrier & Reclamation Bugs:* In
       `crossbeam-epoch`, a reader thread calling `pin()` writes the current
       global epoch `E` into its thread-local `Local`/`Participant` entry,
       executes a `SeqCst` fence, and then loads `Shared<'g, T>` pointers; a
       reclaimer thread calling `try_advance()` scans all registered
       `Participant` epochs and advances the global epoch (freeing garbage bags
       from 3 epochs prior) only if all pinned threads have caught up.
       Historical soundness audits (`#462`, `#535`, and model-checking with
       `CDSChecker`/`GenMC`/`Loom`) exposed cases where either (a) epoch
       advancement or participant registration/unregistration used `Acquire` /
       `Release` instead of a full `Ordering::SeqCst` fence—allowing Store
       Buffering (`SB`) between a thread pinning its local epoch and another
       thread unlinking and retiring a node—or (b) `clone_into_box` / unaligned
       bag drops (`CVE-2022-23639`) and `Guard::defer_unchecked` caused
       use-after-free or unaligned deallocation.
     - *Stacked Borrows vs. Tree Borrows Provenance Conflicts under `Miri`:*
       In `crossbeam-epoch` (`internal.rs`, `sync/list.rs`, `atomic.rs`), a
       participant thread holds a shared reference `&Local` or `&Collector`
       while concurrent threads or deferred destructors mutate intrusive linked
       list pointers or reclaim the containing struct via raw pointers cast from
       `usize`. Under `Miri`'s **Stacked Borrows** model (Jung et al. *POPL
       2020*), creating an intermediate `&T` or `&mut T` reference eagerly
       asserts exclusive or frozen access over the entire pointee span and pops
       aliased raw-pointer tags from the borrow stack, causing immediate UB
       when another thread or deferred closure accesses the same node. Fixing
       `crossbeam-epoch`, `once_cell`, `arc-swap`, and `tokio`'s intrusive task
       lists required systematically replacing `&mut T` / `&T` round-trips with
       raw pointer projections (`addr_of!`, `addr_of_mut!`, `UnsafeCell::raw_get`)
       and motivated **Tree Borrows** (Villani et al. *PLDI 2025*), which makes
       two-phase borrows and deferred writes lazy until an actual conflicting
       write occurs.
  2. **`std::sync::Arc::get_mut` Relaxed-Memory Synchronization Failure
     (Dang et al. *POPL 2020*, "RustBelt Meets Relaxed Memory", DOI
     `10.1145/3371102`):**
     - While mechanizing the soundness of `std::sync::Arc<T>` in the `iRC11`
       weak-memory separation logic on top of `ORC11`, Dang et al. discovered a
       **real weak-memory data-race bug in Rust's standard library
       `Arc::get_mut`**.
     - Specifically, `Arc::drop` decrements the strong reference count with
       `Ordering::Release` and, only when the strong count reaches `1`, executes
       an `Ordering::Acquire` fence before decrementing the weak count and
       deallocating. However, `Arc::get_mut` (which returns `Some(&mut T)` if
       both `strong == 1` and `weak == 1`) previously checked the strong count
       and weak count using `Ordering::Acquire` on the weak count *without*
       synchronizing with prior `Weak::drop` calls that had decremented the weak
       count using `Ordering::Release`! Under weak memory (`RC11` / ARMv8 /
       Power), a thread calling `Arc::get_mut` could obtain `&mut T` and write
       to `T` *without* a happens-before edge from a concurrent thread that had
       just inspected the `Weak` pointer and dropped it, causing a C-2011/Rust
       weak-memory race (`rust-lang/rust#51780`).
  3. **`RwLockReadGuard` and `MutexGuard` Unsound `Send`/`Sync` Bounds
     (`rust-lang/rust#41622`, `CVE-2018-1000810`):**
     - In Rust `< 1.26.0`, `std::sync::RwLockReadGuard<'a, T>` had:
       ```rust
       unsafe impl<'a, T: ?Sized + Sync> Sync for RwLockReadGuard<'a, T> {} // Correct
       // BUG in std: previously lacked `T: Sync` or allowed `Send`/`Sync` mismatch!
       ```
       Specifically, `RwLockReadGuard<'a, T>` implemented `Sync` without
       requiring `T: Sync` (or `MutexGuard<T>` implemented `Sync` when `T: Send`
       instead of `T: Sync`). Because `RwLockReadGuard<'a, T>` implements
       `Deref<Target = T>`, sharing `&RwLockReadGuard<'a, Cell<i32>>` across two
       threads allowed both threads to call `Deref::deref` concurrently and
       obtain two unsynchronized `&Cell<i32>` references to the same memory,
       triggering an immediate non-atomic data race (`Cell::set`) in 100% safe
       Rust!
  4. **Legacy `std::sync::mpsc` Soundness and Race Failures Leading to Complete
     Replacement (`rust-lang/rust#39364`, `#27700`, replaced in PR `#93563`):**
     - Rust's original `std::sync::mpsc` channel implementation attempted to
       dynamically upgrade a single-producer queue (`oneshot` $\to$ `stream`
       $\to$ `shared` multi-producer queue) in place. That state-machine upgrade
       protocol contained decades-long use-after-free, lost-wakeup, and
       dangling-pointer bugs (`#39364`: race condition during `shared` upgrade
       dropping messages or freeing an active queue while a sender was still
       enqueuing). After years of failed point fixes, `rust-lang/rust#93563`
       (Rust 1.67) deleted the entire legacy `mpsc` implementation and replaced
       it with `crossbeam-channel` (`std::sync::mpmc`).

- **Mechanized Canaries & Repairs in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 226–308):
  - `canary_epoch_pin_without_seqcst_allows_uaf` and
    `repaired_epoch_pin_seqcst_prevents_uaf` mechanize the `crossbeam-epoch`
    Store-Buffering reclamation race and prove that the `SeqCst` barrier
    eliminates `.failed .ub`.
  - `canary_rwlock_read_guard_send_only_permits_data_race` and
    `repaired_rwlock_read_guard_requires_t_sync` mechanize the
    `rust-lang/rust#41622` guard trait-bound bug and its repair.
  `Basis: normative specification + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives:**
  - **Primitive 4 (`SmallStepMachine` with Allocator Provenance + Weak-Memory
    Views + Tree Borrows):**
    Fraction arithmetic on reference counts (`count == 0` $\implies$ safe to
    free) is **unsound** under weak memory unless the reclaiming thread's view
    covers all prior accesses in every thread that held a fraction! In Anneal's
    `trusted/lean/` memory model (`MemState` in `Trusted/Memory.lean`),
    deallocation (`free` / `StorageDead`) must check that the deallocating
    thread's `curView` dominates both `naWriteTs loc` and `naReadTs loc` (matching
    `ORC11`'s `drf_pre_dealloc` rule), so missing `Acquire` fences in
    `Arc::drop` / `Arc::get_mut` or missing `SeqCst` fences in `crossbeam-epoch`
    immediately transition to `StepResult.failed .ub`.
  - **Primitive 4 (`StepResult.externalCall` for `unsafe impl Send / Sync` Soundness):**
    When a crate writes `unsafe impl<T: Send> Sync for MyGuard<T>`, Anneal must
    not treat `Send` and `Sync` as uninterpreted syntactic marker traits.
    Instead, `unsafe impl Sync for G` generates a positive semantic obligation
    in `VerificationResult` requiring that two concurrent threads holding
    shared `&G` references across `StepResult.externalCall` boundaries satisfy
    `ProductiveOn` (zero `.failed .ub` data races in `MemState`).

---

#### 1.4 Linux Kernel `qspinlock`, `seqlock`, `RCU`, and `VirtIO` Weak-Memory Failures (`VSync` ASPLOS 2021, `Herd7`/`LKMM`, `GenMC`)

- **Historical Context and Catalog of Failures:**
  Operating system kernels and hypervisor I/O rings aggressively avoid
  full memory barriers (`smp_mb()` / `dmb ish`) on hot paths, relying instead on
  asymmetric `Acquire`/`Release` pairs, control dependencies, and address
  dependencies. Automated weak-memory model checkers—specifically **VSync**
  (Oberhauser et al. *ASPLOS 2021*, DOI `10.1145/3445814.3446748`), **Herd7 /
  LKMM** (Alglave et al. *ASPLOS 2018*), and **GenMC** (Kokologiannakis &
  Vafeiadis *CAV 2021*)—uncovered critical correctness and liveness failures in
  production C and Rust systems code:
  1. **VirtIO Split/Packed Ring `VIRTIO_RING_F_EVENT_IDX` Lost-Wakeup Deadlock:**
     - In VirtIO split virtqueues (`drivers/virtio/virtio_ring.c` and Rust
       `virtio-drivers` / `vhost`), to avoid an expensive VM-exit doorbell kick
       on every packet, `VIRTIO_RING_F_EVENT_IDX` lets the host device publish
       `used_event` (the descriptor index at which it wants to be notified) in
       shared memory, while the guest driver publishes `avail.idx`.
     - **The Bug:** The guest driver writes `avail.idx = K` and then reads
       `used_event` to decide whether to kick; concurrently, the host VMM reads
       `avail.idx`, sees no new work, writes `used_event = K` to request a
       wakeup on the next packet, and goes to sleep. This is a textbook
       **Store-Buffering (`SB`)** pattern across guest-host shared memory! If
       either side omits a full `smp_mb()` (`fence(Ordering::SeqCst)` / `dmb ish`)
       between its store and its load—or uses only `smp_wmb()` (`dmb ishst`,
       which orders stores only with stores)—both stores sit in the respective
       CPU store buffers while both loads read the old values: the guest suppresses
       the kick *and* the host goes to sleep, causing a permanent I/O hang
       under high load on ARM64 and RISC-V.
  2. **Linux `qspinlock`, DPDK MCS Lock, and `seL4` CLH Lock Bugs Found by
     `VSync` (*ASPLOS 2021*):**
     - Applying `VSync`'s Adaptive Linear Relaxation (`ALR`) and Await Model
       Checking (`AMC`) under `IMM` / ARMv8 memory models to industrial locks:
       - In **seL4's user-space CLH lock (`libsel4sync`)** and **DPDK's MCS
         lock**, `VSync` discovered missing acquire/release barriers in lock
         handoff and node recycling that permitted critical-section instructions
         from two threads to overlap on ARM64 (mutual-exclusion violation) or
         caused an awaiting thread's spin loop to read a stale predecessor state
         forever (liveness/hang bug).
       - In the **Linux kernel queued spinlock (`qspinlock`)** on ARM64, weak
         ordering between setting the tail pointer via relaxed/release atomics
         and reading the previous holder's locked byte required careful
         `smp_cond_load_acquire` / `atomic_fetch_or_acquire` pairing; historical
         revisions of `qspinlock` suffered from tail-update vs. unlock races
         caught by `Herd7` (`LKMM`) litmus tests.
  3. **`seqlock` (`read_seqbegin` / `read_seqretry`) Reader-Writer Reordering:**
     - In a sequential lock (`Seqlock<T>`), a reader loads an even sequence
       number `seq1 = seq.load(Acquire)`, reads the payload fields `data`, and
       then checks `seq.load(Acquire) == seq1`. Two classic bugs recur in C and
       Rust `seqlock` implementations:
       - **Missing Trailing Read Barrier (`smp_rmb()`):** An `Acquire` load on
         the *second* `seq` check orders *subsequent* accesses after `seq2`, NOT
         *prior* reads of `data` before `seq2`! Without an explicit
         `fence(Ordering::Acquire)` (or `smp_rmb()`) *between* reading `data`
         and reading `seq2`, the CPU or compiler can reorder the read of `data`
         to occur *after* `seq2 == seq1` succeeds, observing torn writer data!
       - **Non-Atomic Reader Data Race UB in C-2011/Rust:** Even if `seq2 != seq1`
         causes the reader to discard the torn read and retry, in C-2011 and Rust's
         memory model a concurrent non-atomic read of `data` racing with a
         writer's write is **immediate Undefined Behavior (`StepResult.failed .ub`)**
         before `seq2` is even checked! Sound Rust `Seqlock<T>` implementations
         must therefore perform the optimistic payload read using atomic byte/word
         loads (`AtomicUsize::load(Relaxed)` or `read_volatile` only if mapped
         outside standard non-atomic aliasing rules).

- **Mechanized Canary & Repair in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 310–355), `canary_virtio_event_idx_missing_mb_deadlocks` proves that
  omitting `smp_mb()` on either side of the VirtIO `EVENT_IDX` handshake admits
  the `virtioDeviceAwake = false` lost-wakeup state, while
  `repaired_virtio_event_idx_smp_mb_prevents_lost_wakeup` proves that
  bidirectional `smp_mb()` guarantees `virtioDeviceAwake = true`.
  `Basis: documentation + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives:**
  - **Primitive 2 (`ProductiveOn` + `InhabitedPre`) & Primitive 4 (`EventualBehaviorOf`):**
    Notice how `VSync`'s Await Model Checking (`AMC`) distinguishes **safety**
    (mutual exclusion) from **await-loop termination** (no lost wakeups or
    spin-loop livelock under fair memory propagation). In Anneal, because
    `Partial.ub` is the top element and `EventualOut.diverges` is distinct from
    `.terminated`, a lost wakeup in `VirtIO` or `qspinlock` manifests either as
    an explicit deadlock state (`StepResult.failed .error`) or as an infinite
    spin loop (`EventualOut.diverges`). Parameterizing `Query := InitState × FairPropagationSchedule`
    with `InhabitedPre pre` and proving that `.diverges` is excluded from
    `(L.sem prog q).val` verifies both barrier safety and spin-loop liveness
    within Anneal's existing four primitives!

---

### 2. Verified OS Kernel, Hypervisor, and Crash-Safe Storage Boundary Failures

#### 2.1 Unverified Boot, Cache/TLB Maintenance, ARMv8 Break-Before-Make (`BBM`), and Unmodeled DMA/IOMMU Assumptions (`seL4`, `CertiKOS`, `Komodo`, `SeKVM`)

- **Historical Context and "Verified" Premise:**
  Landmark formally verified kernels and hypervisors—including **seL4** (`seL4/l4v`
  in Isabelle/HOL, Klein et al. *SOSP 2009* / *TOCS 2014*), **CertiKOS** (Gu et
  al. *OSDI 2016* in Coq + CompCert), **Komodo** (Ferrell et al. *SOSP 2017*
  verified ARM TrustZone monitor in Dafny), and **SeKVM** (Li et al. *USENIX
  Security 2021* verified Linux KVM hypervisor in Coq)—proved full functional
  correctness (`Abstracts` / refinement from C/assembly to an abstract state
  machine) and information-flow non-interference. Yet postmortems and boundary
  audits across all four systems revealed that the primary security and
  correctness failures occurred *at the boundary between the idealized hardware
  model and the physical SoC*:
  1. **Unverified Bootloader and Early MMU Turn-On Code:**
     In `seL4` (`seL4/l4v` at `6b4076aeb35f7803b7c232963e5f996545e3acb5`) and
     early `CertiKOS`/`SeKVM`, the main refinement theorem assumes the kernel
     starts in a post-boot state satisfying a complex global invariant
     (`invs s₀`: disjoint physical frames, valid initial kernel page tables,
     properly initialized capability derivation tree). The ELF loader, initial
     identity-to-high-virtual-address MMU switch, and `.bss`/stack setup were
     originally outside the proof boundary; overlapping linker-script regions or
     missing identity-map TLB invalidations after enabling paging could corrupt
     the initial state before the verified C entry point ever ran (rendering the
     precondition `invs s₀` false!).
  2. **TLB Shootdown Coherence and ARMv8 Break-Before-Make (`BBM`) Faults:**
     Functional kernel specifications model address translation as a pure
     mathematical function $\mathsf{translate}(\mathsf{CR3}/\mathsf{TTBR}, \mathit{va})$
     reading current RAM page tables. On real hardware:
     - **Stale Multi-Core TLB Entries:** When Core A unmaps or downgrades a Page
       Table Entry (`PTE`) and frees the backing physical frame to the kernel
       allocator, Core B's hardware Translation Lookaside Buffer (`TLB`) and
       intermediate paging-structure caches (`PWC`) may retain the old mapping
       until an Inter-Processor Interrupt (`IPI`) shootdown (`invlpg` on x86-64;
       `dsb ishst; tlbi vae1is; dsb ish; isb` on ARMv8-A) completes. Reallocating
       the physical frame before the `tlbi` + `dsb ish` barrier completes creates
       a catastrophic Use-After-Free in physical memory.
     - **ARMv8 Break-Before-Make (`BBM`):** The ARMv8-A architecture reference
       manual mandates that when changing a valid translation's block size (e.g.,
       splitting a 2 MiB huge page into 4 KiB pages or coalescing them), output
       physical address, or cacheability attributes, software *must* first write
       an invalid descriptor (`0`), execute `dsb` + `tlbi` + `dsb`, and only
       then write the new valid descriptor. Overwriting one valid descriptor
       directly with another (which is completely legal in an idealized Coq/Isabelle
       page-table map!) causes the ARMv8 MMU to raise a synchronous hardware
       **TLB Conflict Abort** when multiple TLB entries match the same VA!
  3. **Unmodeled Direct Memory Access (`DMA`), IOMMU/SMMU Bypass, and Non-Coherent
     Caches:**
     CPU-only kernel models assume that physical memory changes only when a CPU
     core executes a store instruction. In reality, PCIe and platform DMA
     controllers read and write physical RAM asynchronously:
     - Without a formally verified **IOMMU / Arm SMMU** page-table configuration
       (as added in `SeKVM` and `seL4`'s VT-d / SMMU extensions), any user-space
       driver granted MMIO access to a DMA-capable device can instruct the
       device to overwrite kernel code or capability tables in physical RAM,
       completely bypassing CPU MMU isolation.
     - On non-cache-coherent ARM/RISC-V buses, CPU caches are not snooped by DMA
       masters. If the kernel or driver fails to clean dirty CPU cache lines
       (`dc cvac`) before starting a device DMA read—or fails to invalidate
       speculative CPU cache lines (`dc ivac`) before reading a completed DMA
       receive buffer—the CPU observes stale data or evicts dirty cache lines on
       top of incoming DMA bytes.

- **Mechanized Canary & Repair in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 357–398), `canary_bbm_violation_or_rogue_dma_triggers_ub` and
  `repaired_external_call_boundary_inv_blocks_rogue_dma_and_bbm` mechanize how
  encoding ARMv8 `BBM` (`!(oldPteValidInTlb && writingNewIncompatiblePte)`) and
  DMA-borrow disjointness (`!dmaRangeOverlapsActiveCpuBorrow`) inside
  `StepResult.externalCall boundaryInv` turns unmodeled hardware hazards into
  explicit `.failed .ub` obligations.
  `Basis: normative specification + source + execution`.

---

#### 2.2 Speculative Execution Side Channels (`Meltdown`/`Spectre`) vs. Architectural ISA Non-Interference Proofs

- **Historical Context and "Verified" Premise:**
  Both `seL4` (Murray et al. *IEEE S&P 2013*) and `CertiKOS` / `Komodo` proved
  machine-checked **information-flow non-interference** (confidentiality) at the
  ISA/C level: secret kernel data or high-security partition state cannot
  influence any architectural observation (`obs`) of an unprivileged user
  process.
- **Technical Root-Cause Analysis (`Meltdown` CVE-2017-5754 & `Spectre` CVE-2017-5753 / CVE-2017-5715):**
  In 2018, `Meltdown` and `Spectre` demonstrated that **every one of those
  verified confidentiality theorems could be bypassed on physical x86-64 and
  ARMv8 out-of-order cores**:
  - In the formal ISA model (`L_isa`), a user-mode load from a supervisor-only
    kernel virtual address traps immediately (`StepResult.terminated` / fault
    handler), never loading the secret byte into a register. On Intel and ARM
    Cortex-A-75 cores (`Meltdown`), the load transiently forwarded the secret
    kernel byte from the L1 data cache to a dependent array load
    `probe_array[secret * 4096]` before retirement aborted the faulting
    instruction—leaving a secret-dependent footprint in the microarchitectural
    L1 cache state that user space recovered via `rdtsc` timing (`Flush+Reload`).
  - Similarly, `Spectre-v1` (bounds-check bypass) and `Spectre-v2` (branch
    target injection) caused speculative execution inside verified kernel
    syscalls to fetch secret-indexed cache lines along mispredicted branches
    that were architecturally dead in `L_isa`!
  - Defending `seL4` and Linux required Kernel Page-Table Isolation (`KPTI`,
    unmapping kernel memory while in user mode), speculative store-bypass and
    branch-predictor barriers (`lfence` / `csdb` / `sb`), and cycle/cache-flushing
    partition switches (`seL4` time-protection / `SwitchTo` cache-flush proof
    extensions by Ge et al. *EuroSys 2019*).
  `Basis: documentation + derived`.

---

#### 2.3 `seL4` Worst-Case Interrupt Latency Proofs and Explicit Preemption Points in Capability Revocation (`Blackham et al. RTSS 2011`)

- **Historical Context and Technical Root Cause:**
  To make formal verification of the C implementation tractable without general
  fine-grained kernel lock concurrency, `seL4` executes with **interrupts
  disabled inside kernel mode** (the big-kernel-lock / non-preemptible syscall
  model). While most microkernel fastpath syscalls (`seL4_Call`, `seL4_ReplyRecv`)
  execute in $O(1)$ instructions ($\sim 200$ cycles), **capability revocation
  (`seL4_CNode_Revoke`, `seL4_CNode_Delete`)** and untyped memory retyping must
  recursively traverse and destroy an arbitrarily large Capability Derivation
  Tree (`CDT`) of child capabilities!
  - When Blackham et al. (*RTSS 2011*, *"Timing Analysis of a Protected
    Operating System Kernel"*) and Sewell et al. (*RTAS 2017*) attempted to
    prove a hard real-time **Worst-Case Interrupt Latency (WCIL)** bound for
    `seL4`, they found that an unbounded `CNode_Revoke` loop with interrupts
    masked blocked timer and device interrupts for milliseconds, violating
    hard-real-time deadlines!
  - **The Repair (`preemptionPoint`):** `seL4` had to insert explicit
    **preemption points (`preemptionPoint()`)** inside every recursive step of
    `revoke` and `finaliseSlot`. At each `preemptionPoint()`, the kernel checks
    the hardware interrupt controller for a pending IRQ; if an IRQ is pending,
    the kernel **aborts the syscall mid-traversal** in a consistent intermediate
    invariant state (`invs`), returns an internal restart status so the user-space
    `CNode_Revoke` instruction will re-execute from the current program counter
    after the interrupt is serviced, and unmasks interrupts! Proving that every
    intermediate step before `preemptionPoint()` restores the full global kernel
    invariant (`invs`) and strictly decreases a well-founded measure of
    remaining `CDT` nodes became one of the most intricate parts of the entire
    `seL4/l4v` proof corpus.
  `Basis: documentation + source`.

---

#### 2.4 Crash-Safe Storage Failures: `FSCQ` vs. `Yggdrasil`, Unverified FUSE Bindings, and Non-Idempotent Recovery (`OSDI 2016`)

- **Historical Context and Technical Root Cause:**
  - **FSCQ** (Chen et al. *SOSP 2015*, *"Using Crash Hoare Logic for Certifying
    the FSCQ File System"*) was the first filesystem with a machine-checked Coq
    proof of crash safety, extracted from Coq to Haskell and mounted via
    Haskell-to-C **FUSE** (`Filesystem in Userspace`) bindings.
  - One year later, **Yggdrasil** (Sigurbjarnarson et al. *OSDI 2016*,
    *"Push-Button Verification of File Systems via Crash Refinement"*) introduced
    SMT-based **Crash Refinement** (verifying in Z3 that the set of post-crash +
    recovery disk images of an implementation is a subset of the atomic
    specification's disk images) and audited both `FSCQ`/`DFSCQ` and Linux
    filesystems (`ext4`, `btrfs`), exposing three critical failure modes:
    1. **Bugs in `FSCQ`'s Unverified Haskell/C FUSE Glue:** Because `FSCQ`
       verified its core logic in Coq but trusted the extracted Haskell runtime
       and FUSE C bindings, `Yggdrasil` authors and subsequent audits found bugs
       at the FUSE marshaling boundary (such as integer width mismatches, path
       resolution / error-code translation discrepancies, and FUSE callback
       panics when user-space passed out-of-range offsets that violated implicit
       preconditions of the extracted Haskell code).
    2. **Volatile Disk Write-Cache Reordering (`Flush` / `FUA` Omissions):**
       Naive crash models assume that if a program issues disk block writes
       $W(b_1), W(b_2)$ sequentially, a power failure leaves a *prefix* of those
       writes on disk. In reality, modern NVMe/SATA SSD controllers and OS block
       layers reorder uncommitted volatile write-cache blocks arbitrarily unless
       fenced by an explicit `SYNCHRONIZE CACHE` / `FLUSH` or Force Unit Access
       (`FUA`) barrier (`clwb` + `sfence` on persistent memory `Px86`/`PArm`). A
       write-ahead log that writes its commit header block $b_{\text{commit}}$
       without a prior barrier before flushing its log data blocks $b_{\text{data}}$
       can crash with $b_{\text{commit}}$ persisted on disk while $b_{\text{data}}$
       is lost—causing recovery to replay garbage blocks into the filesystem!
    3. **Non-Idempotent Recovery Under Nested Crashes During `recover()`:**
       Even if a recovery routine `recover()` is proven correct against a
       *single* crash during normal execution, a **second power loss occurring
       in the middle of running `recover()`** will corrupt the disk if
       `recover()` mutates metadata or log entries non-idempotently before
       clearing the log commit flag!

- **Mechanized Canary & Repair in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 400–448), `canary_nested_crash_during_non_idempotent_recovery_corrupts_disk`
  proves that a delta-based WAL recovery routine interrupted by a second crash
  applies the log delta twice (`10 + 5 + 5 = 20 ≠ 15`), while
  `repaired_idempotent_wal_recovery_survives_nested_crashes` proves that
  idempotent physical-state recovery converges to the exact same disk state
  across nested crashes (`repairedRecoverComplete (repairedRecoverInterruptedOnce d) = repairedRecoverComplete d`).
  `Basis: documentation + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives (Kernel & Storage):**
  - **Primitive 1 (`Language SemObs` with Microarchitectural Leakage `Obs`) &
    Primitive 4 (`SmallStepMachine`):**
    `Meltdown`/`Spectre` and `seL4` WCIL prove that when security or real-time
    latency matters, `Obs` in `SmallStepMachine` cannot be restricted to coarse
    syscall return values. Instantiating `Obs` with microarchitectural events
    (`UArchEvent`: `.pcStep`, `.memReadAddr`, `.cacheLineFetch`) and step-count
    ticks between `preemptionPoint` yields constant-time/leakage preservation and
    bounded interrupt latency directly via `Abstracts` and `Compiles`.
  - **Primitive 2 (`InhabitedPre pre` + `ProductiveOn`) for Boot & Linker State:**
    To prevent the "unverified bootloader assumption" trap where a kernel proof
    assumes an unreachable or violated post-boot invariant `invs s₀`, Anneal
    requires `InhabitedPre pre` (`∃ q, pre q`) and composes the ELF boot stub
    (`elfBootInit`) directly with `main` via `Compiles`/`Abstracts` (as mechanized
    in `canary_uninhabited_pre_vacuously_satisfies_ub_prog` and
    `inhabited_pre_and_productive_on_guarantee_witness` at lines 570–596 of
    `support/concurrency_systems_failure_canaries_probe.lean`).
  - **Primitive 4 (Multi-Crash Closure Inside `SmallStepMachine`):**
    By modeling power failure + volatile disk-buffer subset selection + jump to
    `recover()` as a demonic transition (`StepResult.choice .demonic`) enabled at
    *every* instruction step—**including inside `recover()` itself**—Anneal's
    `EventualBehaviorOf` and `Abstracts` automatically enforce recovery
    idempotence across arbitrary $k \ge 1$ nested crashes without adding any
    storage-specific primitives to `trusted/lean/`.

---

### 3. Distributed System Verification Failures (`Chord`, `IronFleet`, `Verdi`, `Chapar`)

#### 3.1 Pamela Zave's Alloy Refutation of the `Chord` Distributed Hash Table Protocol (`CCR 2012` / `IEEE TSE 2017`)

- **Historical Context and "Verified" Premise:**
  The **Chord** distributed hash table (Stoica et al. *SIGCOMM 2001* / *IEEE/ACM
  ToN 2003*, and Liben-Nowell, Balakrishnan, & Karger *PODC 2002*, which won top
  systems awards and over 15,000 citations) was famous for being accompanied by
  five mathematical theorems and seven published invariants claiming to prove
  that Chord's asynchronous periodic ring-maintenance operations (`join`,
  `stabilize`, `notify`, `fix_fingers`, and successor-list failure recovery
  `rectify`) guarantee **eventual reachability and single-ring connectivity**
  under concurrent node joins and failures (churn).
- **Technical Root-Cause Analysis (Pamela Zave, *ACM SIGCOMM CCR 2012* DOI
  `10.1145/2185376.2185383` & *IEEE TSE 2017* DOI `10.1109/TSE.2017.2655056`):**
  When Pamela Zave formalized the official Chord protocol pseudocode and failure
  assumptions in the **Alloy** relational model checker (checking bounded scopes
  of up to 6 nodes and successor list length $r$), the Alloy Analyzer found
  counterexample traces refuting **every single one of the seven published
  invariants**:
  1. **Ring Partition into Disjoint Sub-Rings ("Loopy" and Split Rings):**
     In a small network where node $A$ joins via node $B$ while node $C$ fails
     and `stabilize`/`notify` messages interleave with successor-list Failover,
     the ring can permanently split into **two disjoint cycles** (e.g., node $0$
     pointing to itself $0 \to 0$ while nodes $1 \leftrightarrow 2$ form a
     separate 2-cycle, or two 2-cycles in a 4-node network) from which `stabilize`
     can *never* recover!
  2. **Why the Original Paper Proofs Failed:**
     The original hand-written proofs reasoned locally ("every live node $n$
     maintains a valid live `successor` pointer in its successor list, and
     `stabilize` moves `predecessor` closer in identifier order") and implicitly
     assumed that local pointer validity implies global graph connectivity. As
     Zave proved in *IEEE TSE 2017* (*"Reasoning About Identifier Spaces: How to
     Make Chord Correct"*), local degree/ordering properties on a circular
     identifier space $\mathbb{Z}_{2^m}$ do *not* rule out multiple disjoint
     cycles or multi-winding "loopy" rings unless the protocol maintains a global
     **structured ring invariant** anchored by a minimum permanent/stable base of
     $r + 1$ nodes and a unified atomic `stabilize-from-successor-list` transition.

- **Mechanized Canary in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 450–482), `canary_chord_local_bijection_allows_partitioned_subrings`
  mechanizes a concrete 3-node Chord state (`0 → 0`, `1 → 2 → 1`) that satisfies
  the local bijective successor/predecessor invariant (`everyNodeHasValidSucc = true`)
  while violating global single-ring connectivity (`isConnectedSingleRing = false`).
  `Basis: documentation + source + execution`.

---

#### 3.2 `IronFleet`, `Verdi`, and `Chapar` Postmortems: The Marshaling Bottleneck (`Cheerios`) and Z3 Quantifier Instability ("The Butterfly Effect")

- **Historical Context and "Verified" Systems Examined:**
  - **IronFleet** (Hawblitzel et al. *SOSP 2015*, DOI `10.1145/2815400.2815428`):
    Verified a Multi-Paxos replicated state machine (`IronRSL`) and sharded
    key-value store (`IronKV`) in **Dafny** (backed by Z3), combining TLA+-style
    global protocol refinement with Floyd-Hoare imperative verification of
    single-node handlers compiled to C#/.NET.
  - **Verdi** (Wilcox et al. *PLDI 2015*, DOI `10.1145/2737924.2737958`; Woos et
    al. *CPP 2016*): Verified the **Raft** consensus protocol in **Coq** using
    Verified System Transformers (`VST`s) and extracted executable OCaml code.
  - **Chapar** (Lesani, Bell, & Chlipala *POPL 2016*, DOI `10.1145/2837614.2837622`):
    Verified causally consistent distributed key-value store algorithms in **Coq**
    with an operational causal-consistency interface extracted to OCaml.

- **Technical Root-Cause Analysis of Engineering & Boundary Failures:**
  1. **The Packet Serialization / Marshaling Bottleneck (Motivating `Cheerios`):**
     - In early **Verdi** (and **Chapar**), the Coq proof verified the abstract
       protocol state transitions over algebraic `Msg` inductive types, while
       the extracted OCaml shim originally relied on OCaml's unverified
       `Marshal.to_bytes` / `Marshal.from_bytes` (or slow s-expression text
       parsers) to convert `Msg` values to UDP wire packets!
     - Relying on unverified `Marshal.from_bytes` on untrusted network sockets
       is a **remote code execution / memory-safety vulnerability** (malformed
       network bytes crash or corrupt the OCaml runtime) and violates the
       refinement assumption that wire deserialization is a partial inverse of
       serialization ($\mathsf{deserialize}(\mathsf{serialize}(m)) = \mathsf{Some}(m)$).
       Conversely, in **IronFleet**, proving in Dafny/Z3 that recursive packet
       parsing and marshaling routines over byte sequences refined abstract message
       types consumed a disproportionate fraction of total proof lines and runtime
       CPU overhead (until `IronFleet` optimized UDP buffer pinning and the UW
       PLSE group developed **Cheerios**—a formally verified, compositional Coq
       serialization library enforcing prefix-free bit/byte stream round-trip
       theorems).
  2. **Z3 SMT Quantifier Instantiation Instability ("The Butterfly Effect"):**
     - In **IronFleet** (and subsequent Dafny/F*/Verus systems later studied in
       **Mariposa** [Zhou et al. *OSDI 2023*]), verification conditions for
       distributed protocols heavily nest universal and existential quantifiers
       over unbounded message histories, sequence slices (`s[..i] + s[i..]`),
       and quorum sets.
     - Because Z3 instantiates universally quantified axioms via heuristic
       **E-matching triggers**, the authors of `IronFleet` documented a severe
       proof-engineering failure mode they termed **solver instability / the
       butterfly effect**: renaming a local variable, reordering two `assert`
       statements, or adding a field to a struct in an unrelated module changes
       Z3's internal term-graph (`e-graph`) ordering and random/tie-breaking
       heuristics, causing a proof that previously verified in 2 seconds to
       trigger an exponential E-matching matching loop and time out after 60+
       seconds!
     - To survive Z3 instability, `IronFleet` had to wrap recursive definitions
       in `opaque` attributes (hiding bodies from Z3 until explicitly revealed
       via `reveal_Foo()`), manually tune `{:trigger ...}` annotations on every
       quantifier, and split proofs into isolated helper lemmas.
  3. **Extraction & Runtime Garbage-Collection Tail-Latency Spikes:**
     - Both `IronFleet` (compiling Dafny $\to$ C# on the .NET CLR) and `Verdi` /
       `Chapar` (extracting Coq $\to$ OCaml) suffered from unverified runtime
       garbage collection pauses and excessive heap allocation when copying
       immutable protocol history sequences, motivating zero-copy mutable Rust
       implementations (as subsequently explored in `Verus` / `IronSync` and
       targeted natively by Anneal).

- **Mechanized Canaries & Repairs in Anneal:**
  In [`support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
  (lines 484–569):
  - `canary_non_injective_packet_serializer_collides` and
    `repaired_length_prefixed_roundtrip` mechanize how a naive concatenation
    serializer maps two distinct messages `⟨[1], [2, 3]⟩ ≠ ⟨[1, 2], [3]⟩` to the
    same wire packet `[1, 2, 3]` (violating `BehaviorCodec`'s bijection law),
    and prove that a length-prefixed `Cheerios`-style serializer satisfies exact
    round-trip invertibility (`repairedDeserializeLengthPrefixed (repairedSerializeLengthPrefixed m) = some m`).
  - `canary_antecedent_verification_result_explodes_on_false_assumption` and
    `positive_verification_result_isolates_waived_obligation` prove that
    Anneal's positive per-obligation `VerificationResult` completely isolates a
    waived or timed-out SMT obligation (`obWaived`) so it can never contaminate
    or vacuously discharge any other verified obligation (`obSafe.prop`).
  `Basis: documentation + source + execution`.

- **Architectural Lessons for Anneal's 4 `trusted/` Primitives (Distributed Systems):**
  - **Primitive 1 (`BehaviorCodec` Partial-Bijection Law Enforces Wire-Format
    Soundness):**
    Look at the two round-trip laws in Anneal's `BehaviorCodec L_abstract L_wire`:
    $$\mathsf{decodeOut}(\mathsf{encodeOut}(o_1)) = \mathsf{some}\;o_1 \qquad \text{and} \qquad \mathsf{decodeOut}(o_2) = \mathsf{some}\;o_1 \implies \mathsf{encodeOut}(o_1) = o_2$$
    These two equations in `trusted/lean/` **are literally the `Cheerios` /
    `zerocopy` wire-format soundness specification**! Any non-injective serializer
    (where $m_1 \ne m_2$ serialize to the same wire bytes) makes it impossible to
    instantiate `BehaviorCodec`, structurally preventing `Verdi`/`IronFleet`
    marshaling bugs at the type-checking boundary!
  - **Primitive 3 (Positive Per-Obligation `VerificationResult` + Kernel
    Certificate Checking Defeats the Z3 "Butterfly Effect"):**
    Anneal defeats Z3 quantifier instability in two complementary ways:
    1. External SMT/SAT/LIA solvers (`Bitwuzla`, `CaDiCaL`, `cvc5`, `Z3`) are
       used as **untrusted certificate-producing oracles** (emitting `LRAT`,
       `Alethe`, Farkas, or ground instantiation witnesses checked in Lean 4's
       kernel; see Sub-Domain 2), so once a proof certificate is recorded or a
       Lean proof term is elaborated, downstream changes in another function can
       *never* break an existing `.olean` theorem via solver heuristic drift!
    2. Even during interactive development when an engineer temporarily waives a
       slow or timed-out obligation (`ob.id ∈ waived`), Anneal's positive
       disjunction `ob.id ∈ waived ∨ ob.prop` in `VerificationResult` guarantees
       that every non-waived obligation retains its unconditional kernel proof.

---

#### 3.3 Cross-Cutting Synthesis: Historical Failure Modes vs. Anneal's Four `trusted/lean/` Primitives

| Historical Failure Case | Primary Citation / CVE / Issue | Root Cause of Verification or Soundness Failure | Anneal `trusted/lean/` Primitive That Prevents It | Mechanized Canary & Repair Theorem (`support/concurrency_systems_failure_canaries_probe.lean`) |
| :--- | :--- | :--- | :--- | :--- |
| **C/C++11-to-Power & ARMv7/v8 `SeqCst` Compilation Bugs** | Manerkar et al. *MICRO 2016* (`10.1109/MICRO.2016.7783747`); Lahav et al. *PLDI 2017* (`10.1145/3062341.3062352`) | Trailing-sync (`ld; isync` / `ldr; dmb`) and leading-sync (`hwsync; st`) or `STLR`/`LDAR` mappings fail when mixed across ABI boundaries or with `Release`/`Acquire` RMWs (`Z6.U`/`R`/`SB`). | **Primitive 1 (`Language SemObs` + `Compiles`) & Primitive 4 (`externalCall`):** Whole-crate `Compiles L_RC11 L_arch codec` + FFI ABI convention check in `boundaryInv`. | `canary_unrepaired_seqcst_mapping_allows_sb_zero_zero` / `repaired_rc11_seqcst_mapping_forbids_sb_zero_zero` |
| **OOTA & `Promising 1.0` Global Optimization Unsoundness** | Kang et al. *POPL 2017*; Lee et al. *PLDI 2020* (`10.1145/3385412.3386010`) | Uncapped thread-local promise certification in `Promising 1.0` uses unreachable value ranges, breaking Global Value-Range Analysis and Register Promotion. | **Primitive 1 (`Compiles` Transitivity):** Instantiating `L_wmm` with `RC11` or `Promising 2.0` capped certification preserves `Preorder.le_trans` across mid-end `CVP` and backend lowering. | `canary_promising1_uncapped_promise_breaks_global_range_opt` / `promising2_capped_memory_preserves_global_range_opt` |
| **`crossbeam-epoch` Missing `SeqCst` & `Arc::get_mut` Weak-Memory Race** | `crossbeam#462`, `#535`, `CVE-2022-23639`; Dang et al. *POPL 2020* (`10.1145/3371102`, `rust#51780`) | Store buffering between epoch pin and pointer load (or missing `Acquire` sync on `Weak` count in `Arc::get_mut`) allows premature reclamation / UAF under weak memory. | **Primitive 2 (`ProductiveOn`) & Primitive 4 (`SmallStepMachine`):** View-aware deallocation (`curView` covering `naReadTs`/`naWriteTs`) + Tree Borrows tag checks transition UAF to `.failed .ub`. | `canary_epoch_pin_without_seqcst_allows_uaf` / `repaired_epoch_pin_seqcst_prevents_uaf` |
| **`RwLockReadGuard` / `MutexGuard` Unsound `Sync` & Legacy `mpsc`** | `rust#41622` (`CVE-2018-1000810`), `rust#39364`, `rust#93563` | `RwLockReadGuard<'a, T>` implemented `Sync` when `T: Send` (missing `T: Sync`), allowing concurrent `&Cell<T>` data races; `mpsc` state-upgrade races. | **Primitive 3 (`VerificationResult`) & Primitive 4 (`externalCall`):** Semantic multi-thread harness obligations for `unsafe impl Send / Sync` verified against `MemState` race detector. | `canary_rwlock_read_guard_send_only_permits_data_race` / `repaired_rwlock_read_guard_requires_t_sync` |
| **Linux Kernel `VirtIO` `EVENT_IDX`, `qspinlock` & `seqlock` Weak-Memory Bugs** | Oberhauser et al. *ASPLOS 2021* (`VSync`, `10.1145/3445814.3446748`); Alglave et al. *ASPLOS 2018* (`LKMM`) | Missing `smp_mb()` between `avail.idx` write and `used_event` read in VirtIO rings causes `SB` lost-wakeup deadlock; `seqlock` non-atomic read race and missing `smp_rmb()`. | **Primitive 2 (`ProductiveOn` + `InhabitedPre`) & Primitive 4 (`EventualBehaviorOf`):** Distinguishes `.failed .ub` (data race) and `.diverges` (spin/await hang) under fair propagation schedules in `Query`. | `canary_virtio_event_idx_missing_mb_deadlocks` / `repaired_virtio_event_idx_smp_mb_prevents_lost_wakeup` |
| **Verified Kernel Boot, ARMv8 `BBM` TLB, DMA/IOMMU & `Meltdown`/`Spectre` Gaps** | `seL4/l4v`, `CertiKOS` (*OSDI 2016*), `Komodo` (*SOSP 2017*), `SeKVM` (*USENIX Sec 2021*); Blackham et al. *RTSS 2011* | Idealized RAM page-table models omit bootloader setup, ARMv8 Break-Before-Make (`BBM`) TLB aborts, rogue DMA overlapping CPU borrows, speculative cache leakage, and IRQ latency in `CNode_Revoke`. | **Primitive 2 (`InhabitedPre`) & Primitive 4 (`externalCall` + `Obs`):** `boundaryInv` enforces `BBM` and IOMMU/DMA borrow disjointness; `InhabitedPre` + `elfBootInit` proves initial state realizability; `UArchEvent` `Obs` tracks leakage and WCIL ticks. | `canary_bbm_violation_or_rogue_dma_triggers_ub` / `repaired_external_call_boundary_inv_blocks_rogue_dma_and_bbm` / `inhabited_pre_and_productive_on_guarantee_witness` |
| **`FSCQ` / `Yggdrasil` FUSE Glue & Multi-Crash Non-Idempotent Recovery** | Chen et al. *SOSP 2015* (`FSCQ`); Sigurbjarnarson et al. *OSDI 2016* (`Yggdrasil`) | Unverified Haskell/C FUSE bindings panicked on edge-case offsets; non-idempotent WAL recovery corrupted disk blocks when a second crash occurred during `recover()`. | **Primitive 1 (`Abstracts`) & Primitive 4 (`SmallStepMachine`):** Demonic crash transitions enabled at every step (including inside `recover()`) + `externalCall` FFI boundary checks enforce multi-crash idempotence. | `canary_nested_crash_during_non_idempotent_recovery_corrupts_disk` / `repaired_idempotent_wal_recovery_survives_nested_crashes` |
| **`Chord` Ring Partition Under Churn, `Verdi`/`IronFleet` Marshaling & Z3 Instability** | Zave *CCR 2012* / *TSE 2017*; Hawblitzel et al. *SOSP 2015* (`IronFleet`); Wilcox et al. *PLDI 2015* (`Verdi`); Lesani et al. *POPL 2016* (`Chapar`) | Local pointer invariants in `Chord` allowed split sub-rings; unverified/slow packet marshaling (`Cheerios` motivation); Z3 E-matching "butterfly effect" timeouts. | **Primitive 1 (`BehaviorCodec`) & Primitive 3 (`VerificationResult`):** `BehaviorCodec` partial-bijection law requires injective round-trip wire serialization; positive per-obligation `VerificationResult` + kernel certificates isolate solver timeouts. | `canary_chord_local_bijection_allows_partitioned_subrings` / `canary_non_injective_packet_serializer_collides` / `repaired_length_prefixed_roundtrip` / `positive_verification_result_isolates_waived_obligation` |

---

## Boundaries

### Part I Boundaries — Real-World Verification Tools

Basis: source + execution + derived

To prevent future agents from over-generalizing these findings, the following
explicit boundaries apply:

1. **No External Upstream Tool Execution in This Package (`not examined`):**
   While the 53 external repositories in `REPORT.json` were resolved against
   upstream Git coordinates and literature specifications, their external
   C++/OCaml/Java/Isabelle/Coq/Dafny/Verus binaries (`herd7`, `genmc`, `dat3m`,
   `coqc`, `isabelle`, `verus`, `dafny`, `yosys`) were not built or executed
   during this report's authoring. Only Lean 4.34.1 (`lean
   -DElab.async=false -Ddebug.skipKernelTC=false`) was executed to verify
   [ConcurrencySystemsStressTests.lean](support/ConcurrencySystemsStressTests.lean).
2. **Infinite-Stream Hyperliveness vs. Universal Finite-Horizon Safety (`known
   not to apply` without `Query` Schedule Witnesses):**
   The Universal Finite-Horizon Query Pattern (`Query := State × Nat`,
   `universal_horizon_preserves_safety_traces`) captures every **safety**
   property (prefix-closed trace properties, including linearizability of
   completed operations and Byzantine agreement) of non-terminating reactive
   systems. However, true unbounded **liveness** properties (e.g., "every
   submitted Raft client request eventually commits") cannot be decided from
   finite prefixes alone unless paired with either a decreasing ranking/fuel
   measure in the Fair-Schedule-in-Query Pattern
   (`fair_schedule_in_query_starvation_free`) or a future coinductive `Stream
   Obs` extension to `EventualOut.diverges`.
3. **Out-of-Thin-Air (`OOTA`) Axiomatic Cycles in Full C++20 `memory_order_relaxed`
   (`unknown`):**
   While `RC11` (via `po ∪ rf` acyclicity) and `Promising 2.0` (via thread-local
   promise certification) avoid Out-of-Thin-Air values, neither Rust nor ISO
   C++20 has finalized a normative operational definition that forbids `OOTA`
   without forbidding load-to-store reordering on `Relaxed` accesses (`rf ∪
   po`-cycle litmus tests). Anneal's `Language` primitive accommodates both
   `RC11` and `Promising 2.0`, but choosing which model is normative for unsafe
   Rust `Ordering::Relaxed` remains an upstream Rust specification question.
4. **Analog/Electrical Bus Glitches and Sub-Cycle Metastability (`unsupported`):**
   Both `StepResult.externalCall` MMIO/DMA models (`Cat D`) and synchronous
   `SmallStepMachine` RTL models (`Cat G`, `Kami`/`Kôika`/`riscv-formal`) assume
   discrete digital clock boundaries and architectural bus transactions; analog
   clock-domain crossing (`CDC`) metastability and power-glitch fault injection
   are unsupported at this abstraction level.

### Part II Boundaries — Historical Verification Failures

- **Not examined (Silicon Execution of Litmus Tests and Full Kernel Boots):**
  This investigation did not execute hardware litmus tests on physical IBM
  POWER8/POWER9, ARMv8-A, or RISC-V cores, nor did it replay the full
  Isabelle/HOL `seL4/l4v`, Coq `CertiKOS`/`Verdi`/`FSCQ`/`Chapar`, or Dafny
  `IronFleet` build pipelines. The mechanized probe in
  `support/concurrency_systems_failure_canaries_probe.lean` formalizes the
  distilled mathematical counterexamples and repair invariants in Lean 4.34.1.
- **Known not to apply (`BehaviorCodec` Direct Instantiation on Unquotiented
  Target States):**
  As demonstrated in Section 1.1 and Section 3.2, `BehaviorCodec`'s strict
  partial-bijection law (`decodeOut o₂ = some o₁ → encodeOut o₁ = o₂`)
  intentionally rejects codecs where `L₂.Out` retains unquotiented concrete
  representation noise (such as full weak-memory execution graphs `G₁ ≠ G₂`
  with identical terminal heaps, or clobbered caller-saved scratch registers).
  When abstracting such languages in Anneal, the concrete `Language` must
  either quotient internal representation state in `Out` or first refine to an
  intermediate coarse-grained `Language` over the same `Out` carrier before
  applying `BehaviorCodec`.
- **Known not to apply (Safety on Infinite Reactive Loops via Bare
  `EventualOut.diverges`):**
  In `SmallStepMachine` with `EventualBehaviorOf`, `EventualOut.diverges`
  carries no `List Obs` trace. Consequently, verifying trace safety or
  linearizability of non-terminating event loops (such as OS kernels, VirtIO
  drivers, or Raft/Paxos servers) requires either the **Universal
  Finite-Horizon Query Pattern** (`Query := InitState × (horizon : Nat)`) or an
  explicit prefix-observation extension to `EventualOut`.
- **Not examined (Quantitative Probabilistic Distributed Consensus):**
  Randomized Byzantine consensus protocols (such as Ben-Or, HoneyBadgerBFT, or
  Algorand VRF leader election) require quantitative/probabilistic coupling
  beyond non-deterministic `StepResult.choice .demonic` and are outside the
  scope of this report.

---

## Evidence

### Part I Evidence — Real-World Verification Tools

Basis: normative + documentation + source + execution

### 1. Primary Mechanized Evidence in This Package (`execution` + `source`)

- **[ConcurrencySystemsStressTests.lean](support/ConcurrencySystemsStressTests.lean)**
  (639 lines, SHA-256
  `b42fce7d800c8190c456ca826ea945ad0fade66c7b4dcb697a19e9cb419063a3`), verified
  under `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`)
  using only `prelude` and `import Init.NotationExtra`:
  - Lines 30–281: Self-contained definitions of Anneal's 4 `trusted/` primitives
    (`Partial`, `Behavior`, `Language`, `BehaviorCodec`, `Compiles`,
    `Abstracts`, `InhabitedPre`, `Language.ProductiveOn`, `VerificationResult`,
    `verificationResult_non_contamination`, `StepResult.externalCall`,
    `SmallStepMachine`, `EventualBehaviorOf`).
  - Lines 283–337: `WmmExecGraph`, `raw_graph_codec_impossible`,
    `AxiomaticWmmModel.toLanguage` (Category A execution-graph quotienting).
  - Lines 339–353: `sc_robustness_transfer` (Category A weak-memory robustness
    and fence-insertion refinement transfer).
  - Lines 355–453: `M_unfair`, `unfair_demonic_admits_divergence`, `FairState`,
    `IsFairSchedule`, `fairSchedule_inhabited`, `M_fair`,
    `fair_schedule_in_query_starvation_free` (Categories A & B Fair-Schedule-in-Query
    liveness pattern).
  - Lines 455–523: `DriverState`, `M_driver`, `mmio_protocol_violation_is_ub`,
    `mmio_valid_driver_productive` (Categories C & D `StepResult.externalCall`
    MMIO/DMA datasheet gate).
  - Lines 525–576: `MultiCrashRecover`, `crash_recovery_idempotent_converges`,
    `M_reactive_infinite`, `diverging_reactive_loop_erases_trace`,
    `M_reactive_horizon`, `universal_horizon_preserves_safety_traces`
    (Categories E & F crash-recovery idempotence and Universal Finite-Horizon
    Query Pattern).
  - Lines 578–639: `PipeOut`, `L_isa_simple`, `L_rtl_simple`, `burchDillCodec`,
    `burch_dill_rtl_refines_isa` (Category G Burch-Dill pipeline flushing codec).

### 2. Pinned Upstream Repository Coordinates and Primary Literature Citations (`source` + `normative` + `documentation`)

- **Anneal & Toolchain Baselines:**
  - `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f` (`trusted/lean/Trusted/Refinement.lean`, `trusted/lean/Trusted/StepResult.lean`)
  - `joshlf/anneal@5fc1139f2208b3c9cfb513573c4a731cc32bb457` (`trusted/lean/Trusted/X86Semantics.lean`)
  - `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`)
  - `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`)
- **Category A (Weak Memory, Atomic Lowering & Fence Insertion):**
  - `herd/herdtools7@9574394fc4b2bcb1a7ba23dd7877f46bb28ebb34` (`7.58+1`; Alglave, Maranget, Tautschnig, TOPLAS 2014, DOI `10.1145/2627752`; Alglave et al. ASPLOS 2018 `LKMM`, DOI `10.1145/3173162.3177156`)
  - `MPI-SWS/genmc@fab5bba7d9efaf76990227c2f59d62c11c7ea2a3` (Kokologiannakis et al., PLDI 2019, DOI `10.1145/3314221.3314609`; POPL 2022 TruSt)
  - `nidhugg/nidhugg@845a14632ff33f27ba78e72e0693668219197bb2` (Abdulla et al., TACAS 2015, DOI `10.1007/978-3-662-46681-0_28`)
  - `hernanponcedeleon/Dat3M@b81ec6c55503e824bb0ddc4ebac6c6f0a63d56d8` (Gavrilenko et al., CAV 2019, DOI `10.1007/978-3-030-25540-4_21`)
  - `tokio-rs/loom@948c8cc78b178ede6eeff3afc7d97f2f4ea08559` & `CDSChecker` (Norris & Demsky, OOPSLA 2013, DOI `10.1145/2509136.2509514`)
  - `awslabs/shuttle@cee89eb23a6eb883a3d8002c018326d709f240b1` (Bornholt et al., OOPSLA 2021, DOI `10.1145/3485510`)
  - `MPI-SWS/kater@017fdbb530e421fd76cf39f2906354471b2ce96e` (Kokologiannakis, Lahav, Vafeiadis, POPL 2023, DOI `10.1145/3571235`)
  - `weakmemory/imm@4ca191b072df081dd3a6d9aa755959dc901b1bd0` (Podkopaev, Lahav, Vafeiadis, POPL 2019, DOI `10.1145/3290382`; Lahav et al. PLDI 2017 `RC11`, DOI `10.1145/3062341.3062352`)
  - `snu-sf/promising2-coq@6b70a57d10666ec66bfa96b7801dd870f9054da9` & `snu-sf/promising-arm@10291375ccd03152eadf739d280e2c59e10fa9af` (Lee et al., PLDI 2020, DOI `10.1145/3385412.3386010`; Pulte et al., POPL 2018 `ARMv8 Flat`, DOI `10.1145/3158107`)
  - `memorax/memorax@2f25c43f279bb315aba7ac3fcf7c37bbb7d1af5e` (Abdulla et al., TACAS 2013, DOI `10.1007/978-3-642-36742-7_37`; Alglave et al. CAV 2014 `Musketeer`, DOI `10.1007/978-3-319-08867-9_34`; Ševčík et al. JACM 2013 `CompCertTSO`, DOI `10.1145/2487241.2487248`; Batty et al. POPL 2011/2012, DOI `10.1145/1926385.1926394`)
- **Category B (Concurrent Data Structures, SMR & Liveness):**
  - `rocq-iris/iris@8e4909593a3a84f850d224a344cbd3a380672088`, `https://gitlab.mpi-sws.org/iris/gpfsl@48b7183f1b91f7cc53cfdab16e21387e9bfe9c14`, `https://gitlab.mpi-sws.org/iris/transfinite@dde9f193fb3d504be680480b2ca21052edae49df` (Jung et al., JFP 2018 / POPL 2020 Prophecies, DOI `10.1145/3371113`)
  - `kaist-cp/smr-verification@53fdc1648c17c5527c2499ed0ad10d55c01e1344` (Jung et al., POPL 2023, DOI `10.1145/3571219`; OOPSLA 2023)
  - `boogie-org/boogie@fcecf73a49d11ad3ab16729abd03169e5ecfd938` (`CIVL`, Kragl & Qadeer, CAV 2018 / POPL 2020)
  - `viperproject/voila@900470c4035812bde4f80defc5e4e2e79c1fcae6` (Wolf, Schwerhoff, Müller, OOPSLA 2021, DOI `10.1145/3485519`)
  - `verus-lang/verus@0141ebc6f14410dfc87fef1da57408578002eb7c` (Lattuada et al., OOPSLA 2023 / SOSP 2024)
  - `microsoft/armada@da7497dcf506417df1899ac58850706a31e3acd5` (Lorch et al., PLDI 2020, DOI `10.1145/3385412.3385971`)
  - `MattWindsor91/starling-tool@438fe7259e06aaf8433c259244fef2985de797a5` (Windsor et al., CAV 2017)
  - `verifast/verifast@0a83dba42db7ce0b445034ece5298afe980e57dc` (Jacobs et al., NFM 2011; Hamin & Jacobs, ECOOP 2018)
  - `open-s4c/libvsync@dd93f802704c9c941eb7397fa101039bf21118ff` & `open-s4c/vsyncer@76569f0d2ee9a688da95b8025116b3a202e67321` (Oberhauser et al., ASPLOS 2021, DOI `10.1145/3445814.3446748`)
- **Category C (Interrupts, Context Switch, MMU/TLB & Microkernel IPC):**
  - `goblint/analyzer@1463f411ce87edd49198033856b2946fc3366fb2`, `rtic-rs/rtic@f1797184d6168e54c345b17019c237eea70b9ed4`, `asterinas/asterinas@a5238eb6a965a4616ce07a48f5dfbc8042c4cd44`, `seL4/l4v@6b4076aeb35f7803b7c232963e5f996545e3acb5`, `microsoft/verismo@6bc6dd326d8b9ca30ffec57a544b13b5fadf3cb3`, `matthias-brun/verified-nrkernel@1c861090537664b78544cda5d53711b1fcfa05e2`, `rems-project/islaris@c978e10f50db5c40f0fdf113f5f76a779782c6f9`, `VeriGu/SeKVM-4.18@75e3591e663958c370c919aa36fbd484be341043`, `microsoft/komodo@de1865c8bd0d85cdfd9a980ad7131448acfaf136`, `mars-research/atmosphere@bd485f22f1d5e4d1623e133700dc233086059603`
- **Category D (Hardware Device Drivers, MMIO, DMA, IOMMU & VirtIO):**
  - `model-checking/kani@9461e07af7ec929f050aa4192f29363c9be07779`, `boogie-org/corral@33dd98eed1e2d5087c7c5df9a782652772af2b2e`, `ldv-klever/klever@49fef330955ea175fd73dd22f2670c68b811d51a`, `embassy-rs/embassy@14cf6a68ec0bfd0ecf873f7e3dbb2eb69013fa29`, `rust-embedded/embedded-dma@37deca203dc3281fb459f0da92d41b6743a62a48`
- **Category E (Crash Consistency, NVMe & Persistent Memory):**
  - `mit-pdos/perennial@d62b13ac1ff88e21e9f1fbc18cbfeab30cc9ca8e`, `mit-pdos/go-journal@1d09d436fcbd943296f43372c3896714254838c0`, `mit-pdos/daisy-nfsd@68530c3b62abe31ce280e71a2b0d40026a70e5ee`, `mit-pdos/fscq@2c7ef9c268fd79a81b26b44ef720f8e6a1e938a0`, `secure-foundations/veribetrkv-osdi2020@053dd16ab01939843a213e0590983fd22e2d0d4d`, `microsoft/verified-storage@afcc157f40a1381773daa8be7333f5d123e96739`, `NICTA/cogent@49b6ceb0d0337198a0ce26944b1ae11dd93fcb9a`, `locore/yggdrasil@e1de61d798acafb9ae2d8387d176c4b091773623`, `uci-plrg/jaaru@640e2ad4d9089d0ff8a4fa17e2f4347b8f31449b`
- **Category F (Distributed Consensus, DST & BFT):**
  - `microsoft/Ironclad@2fe4dcdc323b92e93f759cc3e373521366b7f691`, `uwplse/verdi@7e1641b758d8f0032aa7de63620bc115330e0a6b`, `uwplse/cheerios@5c9318c269f9cae1c1c6583a44405969ac0be0dd`, `anvil-verifier/anvil@e83ea0f5516ce2ece26740266165180018741e66`, `logsem/aneris@59ae37946838df77fb2c573803b68462a3af9d0f`, `mit-pdos/grove@f3f405eaab259c391906e1088aac35216bac11a4`, `kenmcmil/ivy@8858a0241ed37141757b7a051acc24c58e49c2f3`, `tokio-rs/turmoil@6a1f50223b5a1884bf8890053c85eec04a8af267`, `madsim-rs/madsim@519950efb4711464f300ed7edf2967ed62d5f502`, `apple/foundationdb@bcdefac96277de4a26d59cdf352d478391d347f9`, `tigerbeetle/tigerbeetle@0450c32b2c3c3ab6114f3402cc601341cc8192aa`, `anishathalye/porcupine@97cd067defd99df172053ba7f4ca5bbae57fe446`, `jepsen-io/knossos@14ead19fb3d24745429e367c8ae9779e147ff6cb`, `stateright/stateright@ab8c8be9341505e0f71edbe5dd88ed275bd976a4`, `vrahli/Velisarios@6fb353b18610cd79210755fcc90123536c367aaa`, `konnov/bymc@266366f738bce9dbd5d04336fd9123d85ae2bca1`, `apalache-mc/apalache@9a13950e0ebddcb3d7a79cb9e854b0866e1c5712`
- **Category G (Hardware ISA & RTL Pipeline Co-Verification):**
  - `rems-project/sail@7e0e53d183cad75b8f36bfbbecc0ef75614a8418` (`0.20.3`), `riscv/sail-riscv@a83603b6995428b9df2c464f98e18a7b0ae488fe`, `rems-project/sail-arm@7d0581642d0e3aaca367bbc5650aca7c53057543`, `rems-project/isla@e9b5d945394277656593a0d429466d7fa0a2b4b3`, `alastairreid/asl-interpreter@16260979137c38339743a04b7fd5d9f0fa8a6ee5`, `mit-plv/kami@9217329eb4e1d751f28ab175ebab230b1e8fd4da`, `mit-plv/koika@8921e30434d9e351c49df84c9aa14e72b0456ad0`, `project-oak/silveroak@cccfdb4e19c5906256d2ed4487bf1a0aa2fab99e`, `mit-plv/bedrock2@757f17c6083bf8d43b5293a0db545c8d0aa32a13`, `YosysHQ/sby@79fc9eddca5e33a28cc2f2cd19c9825efd9a7255`, `YosysHQ/riscv-formal@c992aa61fdfe0846c5ed90324c596202a1c69b76`, `uclid-org/uclid@a4e4e7a22780833c86d6a650af2fcf88a7d00a06`

### Part II Evidence — Historical Verification Failures

1. **Anneal Repository Sources (`joshlf/anneal`):**
   - `24367bd1a8c784f2578535954f9915e24894a56f` (`trusted/lean` branch):
     - `trusted/lean/Trusted/Refinement.lean` (lines 1–476): `Preorder`,
       `Partial`, `Partial.pure`, `Partial.ub`, `Behavior`, `Language`,
       `Language.SpecOn`, `Language.WellFormedOn`, `Compiles`, `Abstracts`,
       `Compiler.Verified`, `VerificationResultOn`, and `VerificationResult`.
     - `trusted/lean/Trusted/StepResult.lean` (lines 1–201): `StepResult`,
       `PrefixOutcome`, `ExecQuery`, `ExecOut`, `SmallStepMachine`,
       `ReachesPrefix`, and `BehaviorOf`.
   - `24367bd1a8c784f2578535954f9915e24894a56f` (`main` branch):
     - `trusted/lean/Trusted.lean` and `trusted/lean/Trusted/Attributes.lean`
       (lines 1–140): `@[vetted]` and `@[candidate <feature>]` trust-tier
       declaration attributes and `Trusted.candidate` marker.
2. **Rust Standard Library Sources (`rust-lang/rust` at
   `d8ef4f3fe7031514cbd7d056b7b058814987ecec`):**
   - `library/core/src/sync/atomic.rs` (lines 25–155): normative C++20-derived
     atomic memory model contract.
   - `library/alloc/src/sync.rs`: `Arc::drop` and `Arc::get_mut` acquire/release
     synchronization following `rust-lang/rust#51780`.
   - `library/std/src/sync/mpsc/mod.rs`: `crossbeam-channel`-backed (`mpmc`)
     replacement introduced in `rust-lang/rust#93563`.
3. **Standalone Lean 4.34.1 Mechanized Failure Canaries and Repairs Probe:**
   - **Path:**
     [`reports/anneal-concurrency-weak-memory-kernels-and-storage-survey/support/concurrency_systems_failure_canaries_probe.lean`](support/concurrency_systems_failure_canaries_probe.lean)
   - **Lines:** 678
   - **SHA-256:**
     `6e7eaf3daa9d1b427a53ef3a39335079e1dd54dec63e7fcec680962b09b88181`
   - **Toolchain:** `leanprover/lean4:v4.34.1`
     (`5045d0056413266e57c625dcd7c365b10e377c52`)
   - **Key Mechanized Theorems:**
     - `canary_unrepaired_seqcst_mapping_allows_sb_zero_zero` and
       `repaired_rc11_seqcst_mapping_forbids_sb_zero_zero` (lines 182–198)
     - `canary_promising1_uncapped_promise_breaks_global_range_opt` and
       `promising2_capped_memory_preserves_global_range_opt` (lines 215–223)
     - `canary_epoch_pin_without_seqcst_allows_uaf` and
       `repaired_epoch_pin_seqcst_prevents_uaf` (lines 258–278)
     - `canary_rwlock_read_guard_send_only_permits_data_race` and
       `repaired_rwlock_read_guard_requires_t_sync` (lines 296–307)
     - `canary_virtio_event_idx_missing_mb_deadlocks` and
       `repaired_virtio_event_idx_smp_mb_prevents_lost_wakeup` (lines 335–354)
     - `canary_bbm_violation_or_rogue_dma_triggers_ub` and
       `repaired_external_call_boundary_inv_blocks_rogue_dma_and_bbm` (lines
       380–397)
     - `canary_nested_crash_during_non_idempotent_recovery_corrupts_disk` and
       `repaired_idempotent_wal_recovery_survives_nested_crashes` (lines
       434–446)
     - `canary_chord_local_bijection_allows_partitioned_subrings` (lines
       476–482)
     - `canary_non_injective_packet_serializer_collides` and
       `repaired_length_prefixed_roundtrip` (lines 511–539)
     - `canary_antecedent_verification_result_explodes_on_false_assumption` and
       `positive_verification_result_isolates_waived_obligation` (lines
       554–572)
     - `canary_uninhabited_pre_vacuously_satisfies_ub_prog` and
       `inhabited_pre_and_productive_on_guarantee_witness` (lines 583–596)
   - **Axiom Audit:** Verified via `#guard_msgs in #print axioms` at lines
     600–678 to depend only on `propext` (or zero axioms), with zero `sorryAx`
     and zero custom axioms.
4. **Primary Literature & Postmortem Citations:**
   - Y. A. Manerkar, C. Trippel, D. Lustig, M. Pellauer, and M. Martonosi,
     *"Counterexamples and Proof Loophole for the C/C++ to POWER and ARMv7
     Trailing-Sync Compiler Mappings"*, MICRO-49, 2016, DOI
     `10.1109/MICRO.2016.7783747`.
   - O. Lahav, V. Vafeiadis, J. Kang, C.-K. Hur, and D. Dreyer, *"Repairing
     Sequential Consistency in C/C++11"*, PLDI 2017, DOI
     `10.1145/3062341.3062352`.
   - S.-H. Lee, M. Cho, A. Podkopaev, S. Chakraborty, C.-K. Hur, O. Lahav, and
     V. Vafeiadis, *"Promising 2.0: Global Optimizations in Relaxed Memory
     Concurrency"*, PLDI 2020, DOI `10.1145/3385412.3386010`.
   - H.-H. Dang, J.-O. Kaiser, J.-H. Jourdan, D. Dreyer, and V. Vafeiadis,
     *"RustBelt Meets Relaxed Memory"*, POPL 2020, DOI `10.1145/3371102`.
   - J. Oberhauser et al., *"VSync: Push-Button Verification and Optimization
     for Synchronization Primitives on Weak Memory Models"*, ASPLOS 2021, DOI
     `10.1145/3445814.3446748`.
   - B. Blackham, Y. Shi, S. Chattopadhyay, A. Roychoudhury, and G. Heiser,
     *"Timing Analysis of a Protected Operating System Kernel"*, RTSS 2011, DOI
     `10.1109/RTSS.2011.38`.
   - H. Sigurbjarnarson, J. Bornholt, E. Torlak, and X. Wang, *"Push-Button
     Verification of File Systems via Crash Refinement"*, OSDI 2016, ISBN
     `978-1-931971-33-1`.
   - P. Zave, *"Using Lightweight Modeling to Understand Chord"*, ACM SIGCOMM
     CCR 42(2), 2012, DOI `10.1145/2185376.2185383`, and *"Reasoning About
     Identifier Spaces: How to Make Chord Correct"*, IEEE TSE 43(12), 2017, DOI
     `10.1109/TSE.2017.2655056`.
   - C. Hawblitzel et al., *"IronFleet: Proving Practical Distributed Systems
     Correct"*, SOSP 2015, DOI `10.1145/2815400.2815428`.
   - J. R. Wilcox et al., *"Verdi: A Framework for Implementing and Formally
     Verifying Distributed Systems"*, PLDI 2015, DOI `10.1145/2737924.2737958`.
   - M. Lesani, C. J. Bell, and A. Chlipala, *"Chapar: Certified Causally
     Consistent Distributed Key-Value Stores"*, POPL 2016, DOI
     `10.1145/2837614.2837622`.

---

## Revalidation

### Part I Revalidation — Real-World Verification Tools

Basis: execution

To revalidate the mechanized Lean 4.34.1 stress tests and primitive encodings
in this report package:

1. **Kernel-check `support/ConcurrencySystemsStressTests.lean` under Lean 4.34.1:**

   ```console
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     reports/anneal-concurrency-weak-memory-kernels-and-storage-survey/support/ConcurrencySystemsStressTests.lean
   ```

   Confirm that the command exits with status `0` and zero warnings/errors, and
   verify that `sha256sum` matches
   `b42fce7d800c8190c456ca826ea945ad0fade66c7b4dcb697a19e9cb419063a3`.

2. **Check `Trusted/Refinement.lean` and `Trusted/StepResult.lean` against
   ST-1 through ST-6:**
   If Anneal's `trusted/lean/` definitions of `BehaviorCodec`, `EventualOut`,
   `StepResult.externalCall`, or `VerificationResult` change, diff the updated
   definitions against Section 1 of
   [ConcurrencySystemsStressTests.lean](support/ConcurrencySystemsStressTests.lean)
   and replay the six stress-test theorems (`raw_graph_codec_impossible`,
   `sc_robustness_transfer`, `fair_schedule_in_query_starvation_free`,
   `mmio_protocol_violation_is_ub`, `universal_horizon_preserves_safety_traces`,
   and `burch_dill_rtl_refines_isa`).

### Part II Revalidation — Historical Verification Failures

To typecheck the standalone Lean 4.34.1 failure-canaries and repairs probe and
verify that all theorems and `#guard_msgs in #print axioms` checks pass with
zero errors and zero warnings, run from the `reference` worktree root:

```bash
lean +leanprover/lean4:v4.34.1 \
  reports/anneal-concurrency-weak-memory-kernels-and-storage-survey/support/concurrency_systems_failure_canaries_probe.lean
```

Expected output: exit code `0` with empty stdout and stderr.

To verify the SHA-256 digest of the preserved Lean 4.34.1 probe:

```bash
sha256sum \
  reports/anneal-concurrency-weak-memory-kernels-and-storage-survey/support/concurrency_systems_failure_canaries_probe.lean
  # Expected:
  # 6e7eaf3daa9d1b427a53ef3a39335079e1dd54dec63e7fcec680962b09b88181  support/concurrency_systems_failure_canaries_probe.lean
```

*Authored by an AI agent acting on joshlf's behalf.*
