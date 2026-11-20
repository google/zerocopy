# Coinductive Divergence, Fair Scheduling, and Reactive Rust Event-Loop Liveness

## Summary

Verifying non-terminating reactive Rust systems—bare-metal idle/dispatch loops (`loop { wfi(); }`), `Tock` and `RTIC` kernels, `Embassy` async executors, and work-stealing `Tokio` runtimes—requires semantics and proof structures that separate well-formed infinite reactive streams from silent infinite spinning, scheduler starvation, and undefined-behavior (UB) divergence across FFI boundaries:

1. **Prefix safety + explicit trace divergence (`WellFormed` / `Diverges`):** Unlike C11 (§6.8.5p6) and C++20 (`[intro.progress]`), Rust does not treat side-effect-free infinite loops as UB (`rust-lang/reference@a286e1ecb8ce`, `src/behavior-considered-undefined.md`). In small-step MIR semantics (`joshlf/anneal@c131b320ee`, `Trusted/MirSemantics.lean:1646–1670`), `WellFormed p q` proves UB-freedom over all finite prefixes while permitting divergence, and `Diverges p q` exhibits a single coherent infinite path `∃ trace : Nat → State, trace 0 = s₀ ∧ ∀ n, Step p (trace n) (.step (trace (n + 1)))`—avoiding König's lemma / `Classical.choice` under infinite demonic branching. However, `Diverges` collapses all infinite behaviors into one unstructured `Prop`, erasing reactive I/O streams and finite internal stuttering.
2. **Constructive `Type 0` `PFunctor` M-types (`CTree`) without kernel coinduction or `Classical.choice`:** Lean `v4.34.1` (`leanprover/lean4@5045d0056413`) has no primitive coinductive kernel datatype, and `TrustedBoundary.lean:455–468` rejects `coinductive`, `partial`, `coinductiveFixpoint`, and `partialFixpoint`. Univariate polynomial functor terminal coalgebras `M P` (`leanprover-community/mathlib4@92b2a2cbdc`, `Mathlib/Data/PFunctor/Univariate/M.lean`; TLCA 2015 DOI `10.4230/LIPIcs.TLCA.2015.17`; ITP 2019 DOI `10.4230/LIPIcs.ITP.2019.6`) construct Choice Trees (`CTree E Resp R`, Chappe et al. POPL 2023 DOI `10.1145/3571254`) in `Type 0` via `@Nat.rec` projective approximations using only `[propext, Quot.sound]`, provided events `E : Type` stay first-order `Type 0` data rather than impredicative `Prop` predicates.
3. **Fuel-indexed `wp`/`wlp` vs. `CTree` and lexicographic fairness certificates:** Fuel-indexed `@Nat.rec` `wpOutcomeState` / `wlpOutcomeState` and functional big-step / omnisemantics triples (ESOP 2016 DOI `10.1007/978-3-662-49498-1_23`; TOPLAS 2023 DOI `10.1145/3579834`) verify terminating calls and finite `Future::poll` steps with `0` axioms (`[]`), whereas `CTree` serves `-> !` daemons needing weak bisimulation (`eutt`). Under demonic schedulers, Fair Operational Semantics (PLDI 2023 DOI `10.1145/3591253`) turns finite-task starvation-freedom into lexicographic fuel maps—exposing Tokio's `(event_interval, MAX_LIFO_POLLS_PER_TICK = 3, Budget(Some(128)))` hierarchy and `coop::unconstrained` hazard, Embassy's 4-state duplicate-enqueue guard, Tock's `with_interrupts_disabled` sleep barrier, async `core::mem::forget(Box::pin(fut))` breaking RAII invariants across `Poll::Pending`, and `-> !` FFI traps on fallible `sbi_system_reset` (`ControlFlow.lean:37–41`).

## Applicability

This report covers the combined verification semantics across eleven pinned specifications, proof systems, and Rust runtimes:

- **Formal Rust MIR semantics & Lean 4 trusted boundary:** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted.MirAst`, `Trusted.MirSemantics`, `Trusted.Correspondence`, `TrustedBoundary.lean`), `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), and `leanprover-community/mathlib4@92b2a2cbdc245d7e751a2ee681ea91f819fbab5e`. Lean 4 proofs target the monomorphic `Type 0` `prelude` + `Init.*` fragment admitted by `TrustedBoundary.lean` (`L442–596`).
- **Coinductive semantics baselines:** `DeepSpec/InteractionTrees@284d42248a3c5517cff9f582e335fcee2f6bdc1f` and `vellvm/ctrees@cabcf9bf24b0f459204a7da19ac01b7697ff04e3` (Coq primitive-projection coinductives contrasted against Lean 4 projective `M`-types).
- **Language & firmware specifications:** `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`, `rust-lang/reference@a286e1ecb8ce193d50056e4bb042eea9b23876ef`, and `riscv-non-isa/riscv-sbi-doc@8a545effe9b50484ff897d9815d7d9015cdef203` (`src/ext-sys-reset.adoc`).
- **Rust event-loop & async runtimes:** `tock/tock@ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec`, `rtic-rs/rtic@fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9`, `embassy-rs/embassy@0bf016d305431fcf6fb00be248ab608dca009168`, and `tokio-rs/tokio@3f0ffc85f51c71d97bce72e0f8b80ece9b8b4892`.

**Relation to sibling corpus reports:** Prior reports examine TCB recursion/fuel (`fuel-step-indexing-clocks-and-tcb-recursion`), fuel-free pure borrow lifting (`anneal-fuel-free-mir-lifting-and-alias-erasure`), Aeneas loop/recursion extraction (`aeneas-loops-recursion-termination-and-divergence`), and Iris/Simuliris transfinite liveness (`iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`). This package adds: (1) Lean 4 kernel-admissible `Type 0` `PFunctor` `CTree` coalgebras for infinite reactive loops; (2) concrete fairness and lost-wakeup mechanisms across `tock`, `rtic`, `embassy`, and `tokio`; (3) async `Poll::Pending` cancellation under `mem::forget`; and (4) `-> !` FFI divergence traps and ranked stutter bisimulation (`RankedBiAlign`).

## Findings

### 1. Rust Forward-Progress Semantics vs. Small-Step `WellFormed` and `Diverges`

Basis: normative + source + derived

C11 (ISO/IEC 9899 §6.8.5p6) and C++20 (`[intro.progress]`) permit compilers to assume that side-effect-free loops eventually terminate, lowering to LLVM's `mustprogress` function attribute. Rust omits any forward-progress requirement: side-effect-free infinite loops do **not** appear in `rust-lang/reference@a286e1ecb8ce` (`src/behavior-considered-undefined.md`). Bare-metal Rust kernels rely on this directly; for example, `rtic-rs/rtic@fed0fa5e9d` (`rtic-macros/src/codegen/main.rs:17–25, 41`) synthesizes `unsafe extern "C" fn main() -> ! { ... loop {} }` when no `#[idle]` task is provided.

In `joshlf/anneal@c131b320ee` (`Trusted/MirSemantics.lean:1646–1670`), small-step MIR operational semantics captures non-termination via three orthogonal predicates:

```lean
def WellFormed (p : Program) (q : Query) : Prop :=
  (∃ s₀ : State, initState p q = .ok s₀ ∧
    ∀ s : State, Reaches p s₀ s → ∃ c : Choice, ValidChoice p s c) ∧
  (∀ k : FaultKind, ¬ ReachesResult p q (.fault k))

def Behavior (p : Program) (q : Query) (out : TerminalOut) : Prop :=
  ReachesResult p q (.done out)

def Diverges (p : Program) (q : Query) : Prop :=
  ∃ s₀ : State,
    initState p q = .ok s₀ ∧
    ∃ trace : Nat → State,
      trace 0 = s₀ ∧
      ∀ n : Nat, Step p (trace n) (.step (trace (n + 1)))
```

Three design laws govern this encoding:

1. **UB-freedom permits divergence:** `WellFormed p q` rules out `.fault .undefined` (UB) and `.fault .unsupported` across all reachable finite prefixes while allowing `Diverges p q` (`MirSemantics.lean:1695–1699`).
2. **Coherent infinite traces avoid non-constructive König extraction:** Defining divergence via unbounded finite prefixes (`∀ n, ∃ s_n, ReachesN p s₀ n s_n`) fails to produce an infinite trace constructively when `Choice` (`Step`) is infinitely branching (e.g., arbitrary external MMIO values). Quantifying directly over `∃ trace : Nat → State` avoids `Classical.choice` while pairing cleanly with `RefDiverges` in `Trusted/Correspondence.lean:2478–2488` (`Diverges p q ↔ RefDiverges (encodeProg p) q`, `L2571`).
3. **Why `Diverges` alone cannot specify reactive liveness:** For `fn daemon(...) -> !`, `Behavior p q out` is identically `False`, while `Diverges p q` merely witnesses that *some* non-terminating trace exists—indistinguishable between `loop {}` and a responsive driver that echoes every external interrupt.

### 2. Constructive `Type 0` `PFunctor` M-Types and Choice Trees (`CTree`)

Basis: source + derived

In Coq, reactive nondeterministic semantics use negative primitive-projection coinductive records:
- **Interaction Trees (`DeepSpec/InteractionTrees@284d42248a`, `ITreeDefinition.v:30–42`; POPL 2020 DOI `10.1145/3371119`):** `Variant itreeF` (`RetF | TauF | VisF`) inside `CoInductive itree := go { _observe : itreeF itree }`.
- **Choice Trees (`vellvm/ctrees@cabcf9bf24`, `CTreeDefinitions.v:58–68`; POPL 2023 DOI `10.1145/3571254`):** extends `itreeF` with `StuckF`, productive `StepF`, transparent `GuardF`, and demonic/internal choice `BrF {X : Type} (c : B X) (k : X -> ctree)`.

Lean `v4.34.1` (`5045d0056413`) lacks native kernel `coinductive` primitives, and `TrustedBoundary.lean:455–468` rejects `coinductive`, `partial`, `partialFixpoint`, `coinductiveFixpoint`, and compiler-generated `._unsafe_rec` helpers (`MirAst.lean:77–89`). Following Ahrens–Capriotti–Spadotti (TLCA 2015, DOI `10.4230/LIPIcs.TLCA.2015.17`), Avigad–Carneiro–Hudon (ITP 2019, DOI `10.4230/LIPIcs.ITP.2019.6`), and `leanprover-community/mathlib4@92b2a2cbdc` (`Mathlib/Data/PFunctor/Univariate/M.lean:36–180, 560–566`), any univariate polynomial functor $P(X) = \Sigma (a : A),\; (B\; a \to X)$ constructs its terminal coalgebra `M P` in `Type 0` via `@Nat.rec` projective approximations:

```lean
prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.SimpLemmas

namespace CoinductiveCTree

structure PFunctor where
  A : Type
  B : A → Type

structure PObj (P : PFunctor) (X : Type) where
  head     : P.A
  children : P.B head → X

def PFunctor.Approx (P : PFunctor) (n : Nat) : Type :=
  @Nat.rec (fun _ => Type) PUnit (fun _ ih => PObj P ih) n

def PFunctor.trunc (P : PFunctor) (n : Nat) : P.Approx (n + 1) → P.Approx n :=
  @Nat.rec (fun k => P.Approx (k + 1) → P.Approx k)
    (fun _ => PUnit.unit)
    (fun _ ih x => ⟨x.head, fun b => ih (x.children b)⟩)
    n

structure M (P : PFunctor) where
  approx   : ∀ n : Nat, P.Approx n
  coherent : ∀ n : Nat, P.trunc n (approx (n + 1)) = approx n

def M.corecApprox {P : PFunctor} {S : Type} (step : S → PObj P S) (n : Nat) :
    S → P.Approx n :=
  @Nat.rec (fun m => S → P.Approx m)
    (fun _ => PUnit.unit)
    (fun _ ih s => ⟨(step s).head, fun b => ih ((step s).children b)⟩)
    n

theorem M.corecApprox_coherent {P : PFunctor} {S : Type} (step : S → PObj P S) :
    ∀ (n : Nat) (s : S),
      P.trunc n (M.corecApprox step (n + 1) s) = M.corecApprox step n s
  | 0, _ => rfl
  | n + 1, s => by
    dsimp [PFunctor.trunc, M.corecApprox]
    congr
    funext b
    exact M.corecApprox_coherent step n ((step s).children b)

def M.corec {P : PFunctor} {S : Type} (step : S → PObj P S) (s : S) : M P :=
  ⟨fun n => M.corecApprox step n s, fun n => M.corecApprox_coherent step n s⟩

structure DemonicIdx (arity : Nat) where
  idx     : Nat
  isBound : Nat.blt idx arity = true

inductive CTreeHead (E R : Type) where
  | ret (val : R) | tau | brD (arity : Nat) | vis (ev : E)

def CTreeChild {E R : Type} (Resp : E → Type) : CTreeHead E R → Type
  | .ret _     => PEmpty
  | .tau       => PUnit
  | .brD arity => DemonicIdx arity
  | .vis ev    => Resp ev

abbrev CTree (E : Type) (Resp : E → Type) (R : Type) : Type :=
  M ⟨CTreeHead E R, CTreeChild Resp⟩

def spin {E : Type} {Resp : E → Type} {R : Type} : CTree E Resp R :=
  M.corec (fun _ => ⟨.tau, fun _ => ()⟩) ()

end CoinductiveCTree
```

Three structural constraints govern this Lean 4 realization:

1. **`@Nat.rec` eliminates `._unsafe_rec`:** Defining `Approx`, `trunc`, and `corecApprox` via `@Nat.rec` rather than pattern-matching recursion prevents Lean from emitting `partial` `._unsafe_rec` symbols rejected by `TrustedBoundary.lean`.
2. **Purely constructive `[propext, Quot.sound]` axiom footprint:** `M.corecApprox_coherent` (and Lambek's `M.dest (M.corec step s) = P.map (M.corec step) (step s)`) uses only `funext` (`Quot.sound`) and `propext`, with zero `Classical.choice`. Notice that `mathlib4` (`M.lean:188–201`) defines `M.children` via `head_succ'` + `cast`; operating directly on `approx n` avoids `cast` transport on finite-depth unfoldings.
3. **Universe-monomorphic `Type 0` stratification:** Because `PFunctor.A : Type`, storing higher-order `Prop`-valued predicates (`Mem → Mem → Prop`) inside `E` lifts `PFunctor` to `Type 1`. Keeping `E` and `Resp` strictly first-order `Type 0` event tokens (e.g., `MmioRead addr | WfiSleep`, returning `Nat` / `Bool`) and placing Kripke/liveness invariants in the `Prop`-valued observer preserves `Type 0` monomorphism and per-crate demand staging (`CTree` need not be imported by finite verification crates).

### 3. Fuel-Indexed / Omnisemantics Approximations vs. Coinductive Choice Trees

Basis: source + derived

| Verification Paradigm | Axiom Profile | Safety (`WellFormed`) | Termination | `-> !` Reactive Streams & `eutt` |
| :--- | :--- | :--- | :--- | :--- |
| **Fuel-indexed `@Nat.rec` `wp`/`wlp`** (`MirWp.lean:343–414`) | `[]` (`0` axioms for `wpOutcomeState_mp`) | `∀ fuel, wlp ...` covers all prefixes incl. infinite loops | `∃ fuel, wpProg ...` proves `¬ Diverges` | **No:** collapses `-> !` to vacuous safety; misses `eutt` |
| **Functional Big-Step / Omnisemantics** (ESOP'16; TOPLAS'23) | `[propext]` | Inductively quantifies all nondeterministic futures | Natural under inductive `wp` | **No** without coinductive `wlp` / stream extension |
| **Projective `PFunctor` `CTree`** (`M (ctreePFunctor)`) | `[propext, Quot.sound]` | Coinductive `M.head` / `vis` invariant | Inductive `eventuallyRet` over finite `tau`/`brD` | **Yes:** `vis ev (fun r => ...)` + inductive `tau`-peeling `eutt` |

**Counterexample showing why levelwise `Approx n` equality fails weak bisimulation (`eutt`):**
By `M.ext'` (`mathlib4` `M.lean:167–171`), `∀ n, t₁.approx n = t₂.approx n` equals **strong** bisimilarity (`t₁ = t₂`). Weak equivalence up to silent `tau` steps (`eutt`) must equate $P_0 = \text{ret}(1)$ and $P_1 = \tau; \text{ret}(1)$ while **distinguishing** $P_k = \tau^k; \text{ret}(1)$ from $Q = \text{spin} = \tau; \text{spin}$. Yet:
- $P_0.\text{approx}\; 1 \neq P_1.\text{approx}\; 1$ (differ at `.ret` vs `.tau`), and
- for every fixed $n < k$, $P_k.\text{approx}\; n = Q.\text{approx}\; n$ (both expose $n$ `.tau` nodes!).

Therefore, `eutt` cannot be stated over matching depths of `approx n`; it must be defined as the greatest fixpoint (`gfp`) of a monotone relation whose single-step kernel performs **inductive (finite) `tau` stripping** (`EuttF`)—separating finite silent work from true `spin`. Similarly, sequential monadic composition (`bind` via `mathlib4` `M.corec'` on `CTree E Resp A ⊕ CTree E Resp B`, `M.lean:626–633`) preserves `bind spin k = spin` and commutes up to `eutt` across both terminating and silently diverging subcomputations.

### 4. Fair Scheduling & Starvation-Freedom Certificates Across Real Rust Runtimes

Basis: source + derived

Under unfair demonic `brD` nondeterminism, a multi-task loop can starve ready tasks forever. Following Lee et al. (*Fair Operational Semantics*, PLDI 2023, DOI `10.1145/3591253`), **strong fairness** and bounded-response liveness over a finite task/priority set mechanize constructively in Lean 4 (`0` `Classical.choice`, `0` transfinite ordinals) via a **lexicographic fairness map `imap : TaskId → Nat`**:
- At each scheduler step, every runnable task $i$ not dispatched strictly decreases `imap'(i) < imap(i)` (or hits an explicit starvation fault at `0`), while the dispatched task $j$ may refresh `imap'(j) ≤ H(j)` upon yielding;
- By `Nat.lt_wfRel` over the finite sum $\sum_i \text{imap}(i)$ (plus intra-task cooperative budget), no runnable task can be bypassed infinitely often.

Inspecting four production Rust runtimes exposes the concrete invariants enforcing—and the edge cases breaking—these certificates:

1. **Tokio work-stealing & cooperative budget (`tokio-rs/tokio@3f0ffc85f51c`):**
   - `worker.rs:828, 1084–1086` (`Core::maintenance`, `Context::next_task`) polls the global inject queue `next_remote_task()` every `event_interval` ticks (`core.tick % event_interval == 0`), bounding cross-worker starvation.
   - `worker.rs:272, 730–786` limits same-worker LIFO ping-ponging (`MAX_LIFO_POLLS_PER_TICK = 3`): if `lifo_polls >= 3`, `core.lifo_enabled = false`, forcing subsequent local wakeups onto `core.run_queue`.
   - `coop/mod.rs:97, 115–126` wraps every task poll in `coop::budget` (`Budget(Some(128))`, checked at `worker.rs:758`), forcing `Poll::Pending` after 128 cooperative synchronization polls.
   - **Starvation hazard (`coop::unconstrained`):** `coop/mod.rs:35–56, 120–122` installs `Budget(None)`, making `has_remaining()` return `true` unconditionally. Polling an always-ready channel inside `unconstrained` keeps `task.run()` (`worker.rs:725`) spinning infinitely without incrementing `core.tick`, defeating all three fairness tiers.
2. **Embassy lock-free embedded executor (`embassy-rs/embassy@0bf016d30543`):**
   - `embassy-executor/src/raw/mod.rs:75–112` encodes each static `TaskHeader` via 4 states (`SPAWNED × RUN_ENQUEUED`). Atomic `run_enqueue` inserts a node into the intrusive `RunQueue` iff `RUN_ENQUEUED` flips `0 → 1`, preventing duplicate linked-list cycles that would alias `&mut` and starve suffix tasks.
   - `RunQueue::dequeue_all` clears `RUN_ENQUEUED` (`transition 2`) *before* `TaskStorage::poll`, so any self-wake or ISR `Waker::wake` occurring mid-poll (`transition 3`) safely re-enqueues the task for the next drain without lost wakeups.
3. **Tock OS kernel loop & atomic sleep guard (`tock/tock@ba6aa7edc014`):**
   - `kernel/src/kernel.rs:374–451` runs `kernel_loop(...) -> !` calling `kernel_loop_operation`. When `scheduler.next()` chooses `SchedulingDecision::TrySleep` (`L405`), an unguarded race where an IRQ fires *between* `do_kernel_work_now` (`L388`) and `wfi` would permanently hang the MCU.
   - `L411–426` closes this lost-wakeup bug by wrapping `!chip.has_pending_interrupts() && !DeferredCall::has_tasks()` inside `chip.with_interrupts_disabled(|| { ... chip.sleep(); ... })`. Formal liveness requires coupling CPU `wfi` resume conditions directly to the hardware `pendingIrqMask`.
4. **RTIC Baker SRP ceilings (`rtic-rs/rtic@fed0fa5e9d74`):**
   - Hardware priority ceilings ($\text{ceil}(r) = \max\{\text{prio}(t) \mid r \in \text{uses}(t)\}$) enforced via `BASEPRI` / `PLIC.threshold` prevent priority inversion and spinlock deadlock completely (`&mut` disjointness holds because any preempting ISR satisfies $\text{prio}(t') > \text{sysCeil} \ge \text{ceil}(r)$). Liveness of `idle` (`loop {}`) reduces to bounded high-priority ISR arrival work.

### 5. Diverging `-> !` FFI, Inline Assembly, and Hardware Sleep/Reset Boundaries

Basis: normative + source

Declaring a Rust function `-> !` (`MirTy.never` in `Trusted/MirAst.lean:333`) lowers MIR `TerminatorKind::Call` with `target: None`. In `proofs-rs/lean-miri@c92d1d9754` (`Miri/Interpreter/ControlFlow.lean:37–41`), returning normally from a call with `target = none` triggers immediate UB:

```lean
def returnToBlock (target : Option BasicBlockId) (state : State) : StepResult State Unit :=
  match target with
  | some block => goToBlock block state
  | none => (state, .error (.undefinedBehavior "Unreachable"))
```

Meanwhile, `InlineAsm` unconditionally faults `.unsupported` (`ControlFlow.lean:151`). This creates a sharp real-world verification boundary for hardware resets and sleep instructions:
- **Concrete UB trap (`sbi_system_reset`):** `riscv-non-isa/riscv-sbi-doc@8a545effe9` (`src/ext-sys-reset.adoc:12–16, 66–78`) specifies `struct sbiret sbi_system_reset(uint32_t reset_type, uint32_t reset_reason)` as synchronous and non-returning *only if it succeeds*—returning `SBI_ERR_INVALID_PARAM`, `SBI_ERR_NOT_SUPPORTED`, or `SBI_ERR_FAILED` on error. Declaring the FFI shim as `-> !` (or `asm!(..., options(noreturn))`) causes immediate UB whenever firmware returns an error!
- **Verified recovery:** Typing the FFI boundary as `-> SbiRet` (`target = Some(fallback_bb)`) and branching on return into `loop { wfi(); }` (modeled via an explicit `Wfi` event in `CTree` or a non-faulting `goto` loop in MIR) makes fallible shutdown total (`WellFormed`) across both success (halting/resetting) and failure (parked divergence).

### 6. Async Cancellation vs. Event-Loop Invariants (`Poll::Pending` & `core::mem::forget`)

Basis: normative + source + derived

Event-driven Rust executors (`tokio::select!`, Embassy task shutdown) drop suspended `Future` state machines (`coroutine_drop_shim`, `TerminatorKind::Drop`) at `Poll::Pending` suspension points. Critically, because `core::mem::forget` is 100% safe and accepts `Pin<Box<F>>` without `'static` (`Pin`'s drop guarantee prohibits *reusing* storage before `Drop`, not leaking a heap `Box`), a safe caller can poll `Box::pin(async_op(&mut state))` once to `Poll::Pending` and invoke `core::mem::forget`, **skipping `coroutine_drop_shim` completely**.

Consequently, async state-machine verification must separate two invariants:
1. **`physInv` (Physical memory-safety invariant):** Must hold across all borrowed state at **every** `Poll::Pending` return, `Poll::Ready` return, and `.unwound` panic exit—never delegated to RAII `Drop` guards inside `async fn` locals.
2. **`cancelInv` (Logical/capacity invariant, e.g., releasing a queue token or waker slot):** May be held open across `Poll::Pending` and restored in `coroutine_drop_shim`, because `mem::forget` trades bounded resource leakage for zero memory-safety UB.

### 7. Compositional Relational Equivalence (`BiAlign`) Across Diverging Traces

Basis: source + derived

Proving equivalence between an optimized reactive loop `pImpl` and a reference specification `pSpec` (`SafeTwinEquiv`, generalizing `CorrespondenceClaim` in `Trusted/Correspondence.lean:2565–2571`) requires matching `WellFormed`, terminal `Behavior`s (`.returned`, `.unwound`, `.aborted`), **and** `Diverges pImpl q ↔ Diverges pSpec q`. Unranked asymmetric stutter steps (`leftStut` / `rightStut`) are unsound for `Diverges` equivalence because `pImpl` could stutter infinitely without advancing `pSpec`.

Equipping asymmetric steps with well-founded `Nat` ranking functions (`RankedBiAlign`: `syncStep | leftStut rank₁ | rightStut rank₂ | seq | branch`) requiring `rank₁ (f₁ s₁) < rank₁ s₁` on every unpaired step guarantees constructively (`[propext]` only) that every infinite `Diverges` trace visits infinitely many `syncStep` points—preserving both silent divergence and observable `vis` event equivalence compositionally.

## Boundaries

- **unsupported:**
  - Native kernel `coinductive` declarations, `partial`, `partialFixpoint`, and `coinductiveFixpoint` are **unsupported** in the Lean `v4.34.1` trusted boundary (`joshlf/anneal@c131b320ee`, `TrustedBoundary.lean:455–468`), requiring `@Nat.rec` projective `PFunctor` M-types.
  - Raw `TerminatorKind::InlineAsm` (`wfi`, `wfe`, `ecall`) is **unsupported** in `proofs-rs/lean-miri@c92d1d9754` (`Miri/Interpreter/ControlFlow.lean:151`), requiring `extern "C"` FFI or intrinsic abstractions.
- **known not to apply:**
  - C11/C++20 forward-progress UB (`mustprogress`) is **known not to apply** to Rust `loop {}` (`rust-lang/reference@a286e1ecb8ce`).
  - Levelwise `approx n` equality characterizes strong equality `t₁ = t₂` and is **known not to apply** to weak bisimulation (`eutt`) across finite `tau` stuttering vs silent `spin`.
  - RAII cleanup guards inside `async fn` locals are **known not to apply** to preserving `unsafe` memory-safety invariants across `Poll::Pending`, because safe `core::mem::forget(Box::pin(fut))` skips `coroutine_drop_shim`.
  - Tokio's `Budget(Some(128))` cooperative preemption bound is **known not to apply** inside `tokio::task::coop::unconstrained` (`coop/mod.rs:35–56, 120–122`).
- **unknown:**
  - Worst-case physical hardware interrupt latency and bus-arbitration starvation bounds on concrete microcontrollers remain **unknown** from MIR and executor-level semantics alone.
  - Future MIR lowering details for unstable `AsyncDrop` coroutine cleanup (`ControlFlow.lean:191`) across arbitrary executors remain **unknown**.
- **not examined:**
  - Probabilistic fairness bounds (e.g., Tokio's randomized work-stealing victim selection) were **not examined** (only deterministic / worst-case lexicographic fairness maps were analyzed).
  - Transfinite ($\omega_1$-indexed) step-indexing for higher-order impredicative concurrent heaps storing `Box<dyn FnMut()>` closures was **not examined** (covered separately by `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`).

## Evidence

### Primary Repositories & Specifications Inspected

| Subject | Exact 40-char Commit SHA | Path / Line Range | Verified Observation |
| :--- | :--- | :--- | :--- |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirSemantics.lean:1646–1699` | `WellFormed`, `Behavior`, `Diverges` (`∃ trace : Nat → State`) |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/correspondence/Trusted/Correspondence.lean:2478–2571` | `RefDiverges`, `CorrespondenceClaim` (`Diverges ↔ RefDiverges`) |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `theory/Anneal/MirWp.lean:389–414` | `not_infinite_trace_of_wpOutcomeState`, `not_diverges_of_wpProg` |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/audit/TrustedBoundary.lean:455–468` | Bans `coinductive`, `partial`, `partialFixpoint`, `coinductiveFixpoint` |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | Tag `v4.34.1` (`foundation-lock.json`) | Kernel axioms `{propext, Quot.sound, Classical.choice}` |
| `leanprover-community/mathlib4` | `92b2a2cbdc245d7e751a2ee681ea91f819fbab5e` | `Mathlib/Data/PFunctor/Univariate/M.lean:36–180, 560–634` | `CofixA`, `AllAgree`, `MIntl`, `M.corec`, `dest_corec`, `bisim`, `corec'` |
| `DeepSpec/InteractionTrees` | `284d42248a3c5517cff9f582e335fcee2f6bdc1f` | `theories/Core/ITreeDefinition.v:30–42` | `Variant itreeF`, `CoInductive itree` |
| `vellvm/ctrees` | `cabcf9bf24b0f459204a7da19ac01b7697ff04e3` | `theories/Core/CTreeDefinitions.v:58–68` | `Variant ctreeF` (`RetF \| StuckF \| StepF \| GuardF \| VisF \| BrF`) |
| `proofs-rs/lean-miri` | `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` | `Miri/Interpreter/ControlFlow.lean:37–41, 151` | `returnToBlock none => .undefinedBehavior`; `.InlineAsm => .unsupported` |
| `rust-lang/reference` | `a286e1ecb8ce193d50056e4bb042eea9b23876ef` | `src/behavior-considered-undefined.md:1–70` | Infinite side-effect-free loops are not UB |
| `tock/tock` | `ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec` | `kernel/src/kernel.rs:374–451` | `kernel_loop -> !`, `with_interrupts_disabled` sleep guard |
| `rtic-rs/rtic` | `fed0fa5e9d74c1f1fb27f06582d4387590cbf0a9` | `rtic-macros/src/codegen/main.rs:17–59` | Synthesized `main() -> !` falling into `idle` or `loop {}` |
| `embassy-rs/embassy` | `0bf016d305431fcf6fb00be248ab608dca009168` | `embassy-executor/src/raw/mod.rs:75–112` | 4-state `SPAWNED × RUN_ENQUEUED` lifecycle |
| `tokio-rs/tokio` | `3f0ffc85f51c71d97bce72e0f8b80ece9b8b4892` | `tokio/src/task/coop/mod.rs:35–126`, `worker.rs:272, 718–828, 1084` | `Budget(Some(128))`, `unconstrained`, `MAX_LIFO_POLLS_PER_TICK = 3`, `event_interval` |
| `riscv-non-isa/riscv-sbi-doc` | `8a545effe9b50484ff897d9815d7d9015cdef203` | `src/ext-sys-reset.adoc:12–16, 66–78` | `struct sbiret sbi_system_reset`, `SBI_ERR_*` return codes |

### Peer-Reviewed Literature Anchors

1. Xia et al., *"Interaction Trees: Representing Recursive and Impure Programs in Coq,"* POPL 2020, DOI `10.1145/3371119`.
2. Chappe et al., *"Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq,"* POPL 2023, DOI `10.1145/3571254`.
3. Ahrens, Capriotti, Spadotti, *"Non-Wellfounded Trees in Homotopy Type Theory,"* TLCA 2015, DOI `10.4230/LIPIcs.TLCA.2015.17`.
4. Avigad, Carneiro, Hudon, *"Data Types as Quotients of Polynomial Functors,"* ITP 2019, DOI `10.4230/LIPIcs.ITP.2019.6`.
5. Lee, Cho, Kim, Moon, Song, Hur, *"Fair Operational Semantics,"* PLDI 2023, DOI `10.1145/3591253`.
6. Owens, Myreen, Kumar, Tan, *"Functional Big-Step Semantics,"* ESOP 2016, DOI `10.1007/978-3-662-49498-1_23`; Charguéraud, Chlipala, Erbsen, Gruetter, *"Omnisemantics: Smooth Handling of Nondeterminism,"* TOPLAS 2023, DOI `10.1145/3579834`.

## Revalidation

1. **Lean 4 `PFunctor` `CTree` Kernel & Axiom Check:** Copy the `CoinductiveCTree` module from Finding 2 into `/tmp/check_ctree.lean`, append `theorem spin_head : M.head (spin : CTree PEmpty (fun e => nomatch e) Nat) = .tau := rfl` and `#print axioms spin_head` / `#print axioms CoinductiveCTree.M.corec`, and run:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false /tmp/check_ctree.lean
   ```
   Verify exit `0` with no `sorryAx` or `Classical.choice` (`[Quot.sound]` / `[propext]` only).
2. **`rustc` LLVM IR Forward-Progress Check:** Compile `pub fn spin() -> ! { loop {} }` via `rustc --crate-type=lib -O --emit=llvm-ir /tmp/spin.rs -o /tmp/spin.ll` and inspect `/tmp/spin.ll` to confirm the emitted `spin` definition does **not** carry `mustprogress`.
3. **Upstream Regression Diffs:** After bumping any pinned subject, diff `TrustedBoundary.lean` (`allowedDeclarationKinds`), `MirSemantics.lean` (`Diverges`), `tokio` `worker.rs`/`coop/mod.rs` (`MAX_LIFO_POLLS_PER_TICK`, `Budget::initial`), and `tock` `kernel/src/kernel.rs` (`with_interrupts_disabled` sleep guard).
