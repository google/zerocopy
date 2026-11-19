# Protocol Modeling Languages and Machine-Checked Distributed Implementation Refinement

## Summary

Design-level protocol modelers (`TLA+`/`PlusCal`, `Quint`/`Apalache`, `Alloy 6`/`Pardinus`, and `P`) eliminate architectural concurrency flaws in days using bounded explicit or symbolic search, yet leave an unverified spec-to-code gap whenever production systems are re-implemented manually in Rust, Go, C#, or C++. Machine-checked refinement stacks (`IronFleet`, `Verdi`/`Verdi-Raft`, `Disel`, `Aneris`, `Verus`/`IronSync`, and `Anvil`/`Welder`) close that gap by proving trace inclusion from low-level host code and network/API shims up to abstract state machines, subject to five structural invariants:

1. **Relational action modeling vs. static effect discipline (`TLA+` vs. `Quint` / `Alloy 6` / `P`):** Untyped `TLA+` treats primed updates (`x' = 1 /\ x' = 2`) as symmetric conjunctions; contradictory updates collapse an action to `FALSE` (`0` enabled steps) while stuttering closure `[Next]_vars` hides the deadlock from safety invariants. `Quint` prevents duplicate variable assignments statically (`MultipleUpdatesChecker.ts`, diagnostic `QNT202`) and compiles typed pure/update effects to `Apalache` symbolic SSA/SMT encoding (`TlaActionOper.scala`), whereas `Alloy 6`/`Pardinus` unrolls LTL traces into bounded Kodkod SAT lasso models (`<= 30`-bit integers, default `4`) and `P` compiles actor-queue state machines directly to executable C#/C/Java after systematic `PChecker` schedule fuzzing.
2. **Prophecy variables are structurally required when implementation concurrency commits late (`Abadi & Lamport 1991`):** When an abstract protocol picks a non-deterministic outcome early while an implementation exposes an intermediate prepared state before races resolve, **zero** pure forward refinement mappings (even augmented with arbitrary past history) preserve trace inclusion (`0 / 625` in the reproduced `prophecy_mover_refinement_probe.py` finite check). Sound completion requires finite-branching prophecy variables satisfying totality, initial correspondence, backward step lifting, and step simulation—or explicit `#![verifier::prophetic]` isolation restricting prophetic reads to `require`/`assert` guards (`Verus` `disallow_prophecy.rs`).
3. **Atomicity reduction replaces global interleaving proofs with local host obligations (`IronFleet` and `Verdi`):** `IronFleet` bridges asynchronous multi-host UDP execution to an atomic host step via a three-layer Dafny refinement (`AbstractService` -> `DistributedSystem` -> `HostNextImpl`) gated by a syntactic Lipton mover envelope (`Main.s.dfy`: `recvs + clocks + sends == ios` and `|clocks| <= 1`). An execution micro-probe confirms that `20/20` two-host `Receive · Clock · Send` schedules serialize cleanly, whereas reordering to `Send · Clock · Receive` creates `18/20` non-serializable ping-pong cycles. `Verdi` replaces explicit network reasoning with verified system transformers (`SeqNum`, `PrimaryBackup`) over `MultiParams` single-threaded event handlers (`Net.v`), while `Disel` and `Aneris` restore horizontal protocol composition and multi-threaded intra-node concurrency via separation logic.
4. **PCM-tokenized linear ghost state unifies specification and zero-cost execution (`Verus`, `IronSync`, `Anvil`):** Rather than maintaining an unverified .NET (`IronFleet`) or OCaml (`Verdi`) runtime extraction boundary over GC heaps, `Verus` `tokenized_state_machine!` and `IronSync` `PCM.s.dfy` compile sharded Partial Commutative Monoid invariants directly into linear ghost tokens erased at Rust/C++ compile time, while `Anvil`/`Welder` embed TLA `always`/`eventually`/`leads_to` proofs in Verus to verify safety and Eventually Stable Reconciliation (`ESR`/`CORE`) for live `kube-rs` Kubernetes controllers.
5. **Engineering trade-offs span all six lifecycle levels (`L1`–`L6`) and human trust roots (`C1`–`C2`):** Design checkers deliver sub-second counterexamples (`L3`) at low authoring cost (`L1`) but zero production binary guarantees (`L4`); SMT-backed verifiers (`IronFleet`, `Verus`/`Anvil`) lower `L1` proof-to-code ratios (`~2x–15x`) relative to tactic-heavy Rocq (`Verdi-Raft` `~94x`, `50,000` proof lines for `530` Raft lines) at the price of `L3` Z3 trigger tail latency (`rlimit` variance), whereas linear Rust tokens remove GC overhead at `L4`/`L6`.

## Applicability

These findings apply specifically to the primary specifications, pinned upstream revisions, and verified runtime traces inspected for this report:

- **Modeling and bounded/symbolic checking toolchains:**
  - `tlaplus/tlaplus` at `bc1b506bdcad80bb518bf3776a9161c34ff0fc4c` (`PlusCal` translator `pcal/trans.java`) and `tlaplus/tlapm` at `9a52fafb00245ace0877ec8d91c4a09a7caa8061` (`TLAPS` interactive prover).
  - `informalsystems/quint` at `07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0` (`quint/src/effects/MultipleUpdatesChecker.ts`) and `apalache-mc/apalache` at `78b8e72c982bca06507d7c1d9fc404cffc7cbb8e` (`tlair/.../TlaActionOper.scala`, Konnov et al. OOPSLA 2019, DOI `10.1145/3360549`).
  - `AlloyTools/org.alloytools.alloy` at `ed89fdb16c58aea17a55e312c44f99e31aa63ee1` (`TranslateAlloyToKodkod.java`) and `haslab/Pardinus` at `d3e7aeac73d052a28cff7f5946c85f745e3ad14c` (`TemporalTranslator.java`).
  - `p-org/P` at `6cbf558087c85bad94068947286a6ef4e7342eb5` (`TestingEngine.cs`, Desai et al. PLDI 2013, DOI `10.1145/2491956.2462184`).
- **Machine-checked distributed implementation frameworks:**
  - `microsoft/Ironclad` (`IronFleet`) at `2fe4dcdc323b92e93f759cc3e373521366b7f691` (`Main.s.dfy`, `DistributedSystem.s.dfy`, Hawblitzel et al. SOSP 2015, DOI `10.1145/2815400.2815428`).
  - `uwplse/verdi` at `7e1641b758d8f0032aa7de63620bc115330e0a6b` (`Net.v`, `SeqNumCorrect.v`, Wilcox et al. PLDI 2015, DOI `10.1145/2813885.2737958`) and `uwplse/verdi-raft` at `a3375e867326a82225e724cc1a7b4758b029376f` (`AllEntriesLogProof.v`, Woos et al. CPP 2016, DOI `10.1145/2854065.2854081`).
  - `DistributedComponents/disel` at `4ae4c207ef1a25010d63508f2bbda2d4c197d5ab` (`Protocols.v`, Sergey, Wilcox, Tatlock POPL 2018, DOI `10.1145/3158116`) and `logsem/aneris` at `59ae37946838df77fb2c573803b68462a3af9d0f` (`adequacy.v`, Krogh-Jespersen et al. ESOP 2020, DOI `10.1007/978-3-030-44914-8_13`).
  - `verus-lang/verus` at `c821149050c1269f32771a11582bee2fc58e5a8a` (`state_machines_macros/src/{lib,disallow_prophecy,check_birds_eye,token_transition_checks}.rs`, Lattuada et al. OOPSLA 2023, DOI `10.1145/3586037`), `secure-foundations/ironsync-osdi2023` at `7c912e29fd9e770d2fb9866606d0bf2a97629252` (`PCM.s.dfy`, Hance et al. OSDI 2023), and `anvil-verifier/anvil` at `e83ea0f5516ce2ece26740266165180018741e66` (`state_machine.rs`, `tla_demo.rs`, `shim_layer/mod.rs`, Sun et al. OSDI 2024; Welder SOSP 2026, DOI `10.1145/3830418.3843868`).
- **Refinement theory, industrial practice, and local execution control:**
  - Abadi and Lamport, *The Existence of Refinement Mappings*, TCS 1991 (DOI `10.1016/0304-3975(91)90222-U`), paired with AWS (`10.1145/2699417`, `10.1145/3477132.3483540`, `10.1145/3729175`), MongoDB (`10.14778/3397230.3397233`), and Cloudflare incident reports, plus standalone execution of `prophecy_mover_refinement_probe.py` on Python `3.13.15` (Linux `x86_64`).

Findings do not automatically generalize to unexamined Byzantine fault-tolerant state-machine transformers, non-stuttering real-time clock refinement, or unverified C/Rust FFI kernels below the runtime shims.

## Findings

### Relational and Temporal Protocol Modeling Substrates

#### TLA+, PlusCal, and Explicit (`TLC`) vs. Symbolic (`Apalache`) Checking

Basis: **source** + **documentation** + **execution** + **derived**

`TLA+` models distributed protocols as untyped Zermelo–Fraenkel set-theoretic temporal formulas of the canonical shape $\mathit{Spec} \triangleq \mathit{Init} \land \Box[\mathit{Next}]_{\mathit{vars}} \land \mathit{WF}_{\mathit{vars}}(A)$, where $\mathit{Init}$ constrains initial states, $\mathit{Next}$ relates unprimed pre-state variables $x$ to primed post-state variables $x'$, and $[\mathit{Next}]_{\mathit{vars}} \triangleq \mathit{Next} \lor (\mathit{vars}' = \mathit{vars})$ enforces invariance under arbitrary finite stuttering. `PlusCal` (`tlaplus/tlaplus@bc1b506bdcad`, `pcal/trans.java:30-120`) lowers imperative process-structured pseudocode with atomic `label:` blocks into a single-step `TLA+` `Next` disjunction by synthesizing an explicit program counter `pc` and emitting explicit `UNCHANGED` clauses for non-assigned variables; known parser/macro edge cases documented in `pcal/trans.java:32-53` include macro parameter non-substitution inside `with(v \in ...)` blocks and `if (...) call f(...); return` grouping ambiguities.

Because `TLA+` actions are Boolean predicates rather than imperative assignments, two subtle defects frequently arise in human- and LLM-authored models:

1. **Double-prime vacuous conjunction:** Writing `owner' = "NodeA" /\ owner' = "None"` inside composed sub-actions does not overwrite `owner'`; it conjoins contradictory constraints so the action evaluates to `FALSE` (`0` transitions). Because $\Box[\mathit{Next}]_{\mathit{vars}}$ always permits self-loop stuttering, safety properties (`[]Inv`) pass vacuously unless deadlock checking or `<>` liveness/action coverage is asserted (`prophecy_mover_refinement_probe.py` check 1: `vacuous_enabled_steps = 0`, `stutter_trace_valid_edges = 9`).
2. **Omitted `UNCHANGED` frame:** Leaving a state variable unconstrained in one disjunct causes `TLC` to fail with a missing successor assignment error, or worse, allows `Apalache`/`TLAPS` to pick arbitrary next-state values for that variable.

To evaluate large protocols without explicit state enumeration, `TLC` stores 64-bit state fingerprints (`FP64`) in memory-mapped disk queues (collision probability $\approx |S|^2 / 2^{65}$, roughly $10^{-6}$ near $2 \times 10^6$ distinct states and reaching $\approx 1\%$ near $6 \times 10^8$ states), whereas `Apalache` (`apalache-mc/apalache@78b8e72c982b`, `TlaActionOper.scala:15-74`, DOI `10.1145/3360549`) lowers `PRIME`, `STUTTER`, `ENABLED`, and `UNCHANGED` operators from typed TLA+ into bounded symbolic transition relations compiled to `Z3` via static single assignment (SSA) arenas, verifying bounded runs ($k \le 15$ steps) or inductive invariants (`--inv`) over wide integer/nonce domains where `TLC` explodes exponentially.

#### Quint Type-and-Effect Elimination of TLA+ Footguns

Basis: **source** + **execution**

`Quint` (`informalsystems/quint@07d7a1a69c20`, `quint/src/effects/MultipleUpdatesChecker.ts:23-65`) replaces untyped `TLA+` syntax with Hindley–Milner polymorphic types and an explicit algebraic effect system classifying expressions into `read`, `update`, `temporal`, and `pure` effects, compiling down to `Apalache` TLAIR (`apalache-mc/apalache`). Inspecting `MultipleUpdatesChecker.exitConcrete` (`lines 38-65`) confirms that `Quint` tracks every `update` effect entity within a `ConcreteEffect`, groups updated state variables by name, and rejects any branch attempting multiple updates to the same state variable with error `QNT202` (`Multiple updates of variable ...`) prior to model checking—converting the silent `TLA+` double-prime deadlock into an immediate compile-time error.

#### Alloy 6, Pardinus Bounded Lasso Traces, and Microsoft P

Basis: **source** + **documentation**

| Modeling Tool | Underlying Logic & Semantics | Bound / Decidability Strategy | Primary Failure Mode / Footgun |
| --- | --- | --- | --- |
| `TLA+` / `TLC` / `TLAPS` | Untyped ZF set theory + linear temporal logic of actions ($\Box[\mathit{Next}]_{\mathit{vars}}$) | Explicit BFS (`TLC`) or multi-backend deductive proofs (`TLAPS`: Zenon, Isabelle, SMT) | Contradictory primed equations masked by stuttering; `TLC` FP64 hash collisions or state explosion on sets of sets |
| `Quint` + `Apalache` | Typed functional/effect surface over `TLA+` IR (`TLAIR`) | Bounded symbolic SMT (`Z3`) via SSA arenas + inductive `--inv` | Non-inductive candidate invariants fail; bounded depth $k$ misses deep liveness cycles without inductive proof |
| `Alloy 6` / `Pardinus` | First-order relational logic (`^r`, `*r`) + past/future LTL (`after`, `always`, `eventually`) | Bounded scope (`N` atoms) + `steps` lasso trace to `Kodkod` SAT (or `Electrod`/`nuXmv` SMV) | Default integer `bitwidth = 4` (`[-8..7]`, cap `<= 30`); `var sig` blocks singleton folding (`TranslateAlloyToKodkod.java:276`); over-constrained `fact` vacuity |
| `Microsoft P` | Communicating asynchronous actor state machines (`send`, `defer`, `ignore`) + ghost `spec` monitors | Portfolio systematic concurrency scheduler (`PChecker` PCT/POS/QLearning) + C#/C/Java codegen | Incomplete state-space coverage under high event interleaving; unverified host OS/network wrappers around generated C# actors |

In `AlloyTools/org.alloytools.alloy@ed89fdb16c58` (`TranslateAlloyToKodkod.java:75-89, 176-310`) integrated with `haslab/Pardinus@d3e7aeac73d0` (`TemporalTranslator.java`), relational facts referencing mutable (`var`) signatures or fields are implicitly lifted inside `always` (`ff = ff.always()` at `lines 268-308`), and mutable singleton (`var one sig`) declarations explicitly opt out of static singleton relation elimination (`line 276`). Integer reasoning in Kodkod SAT is bit-blasted with strict bounds (`bitwidth <= 30`, default `4`, `lines 178-181`), making silent integer overflow wraparound a frequent false-positive/false-negative hazard unless `Int` overflow checks are explicitly enabled. Unlike pure spec languages, `P` (`p-org/P@6cbf558087c8`, `TestingEngine.cs:43-105`) executes the same state-machine handlers under controlled systematic schedulers (`Strategies/{Exhaustive,Feedback,Probabilistic}`) and emits production actor code directly.

#### Industrial Evidence: AWS, MongoDB, and Cloudflare

Basis: **documentation** + **normative**

Non-academic industrial reports establish both the leverage and the exact boundary of design-level modeling:

- **AWS (`Newcombe et al., CACM 2015`, DOI `10.1145/2699417`; `Bornholt et al., SOSP 2021`, DOI `10.1145/3477132.3483540`; `Brooker & Desai, CACM 2025`, DOI `10.1145/3729175`):** AWS engineers achieved practical TLA+/PlusCal competence in 2–3 weeks and uncovered a 35-step DynamoDB replication bug that escaped stress testing and code review (`10.1145/2699417`). At implementation time, AWS transitioned from static design checking alone to `P` state-machine modeling paired with deterministic simulation and lightweight property-based reference models (`ShardStore` in S3 validating real Rust storage code against an abstract spec, `10.1145/3477132.3483540`), because standalone `TLA+` specs drifted from production C++/Rust code during Day-2 feature evolution.
- **MongoDB (*"eXtreme Modelling in Practice"*, `PVLDB 2020`, DOI `10.14778/3397230.3397233`, and MongoDB Engineering Blog *"Conformance Checking At MongoDB"*):** Attempting **Model-Based Trace Checking (MBTC)**—replaying logged C++ `mongod` server traces against abstract `TLA+` Raft/replication specs—proved fragile and impractical because coarse server log checkpoints omitted unlogged internal interleavings and atomicity boundaries, forcing ad-hoc trace reconstruction guesses. Conversely, **Model-Based Test-Case Generation (MBTCG)**—emitting concrete test vectors from `TLC` state graphs to drive `MongoDB Realm Sync` C++ implementations—delivered high branch coverage without speculative log parsing.
- **Cloudflare Outage (*"A Byzantine failure in the real world"*, Nov 2, 2020):** A switch misconfiguration created an asymmetric partial partition where `etcd` `3.3` cluster members could not reach each other uniformly while retaining partial paths to third nodes. Repeated election timeouts with unreachable peers disrupted quorum stability for ~6 hours because the deployed Raft configuration lacked `PreVote` and `CheckQuorum` hardening—demonstrating how operational deployment assumptions (`"symmetric partition"` vs real asymmetric partial connectivity) invalidate protocol expectations unless explicitly modeled and enforced in production code.

### Machine-Checked Implementation Refinement Architectures

#### IronFleet: Layered Dafny Refinement and Lipton Mover Reduction

Basis: **source** + **documentation** + **execution** + **derived**

`IronFleet` (`microsoft/Ironclad@2fe4dcdc323b`, DOI `10.1145/2815400.2815428`) eliminates the spec-to-code gap in Dafny across three vertical layers:

1. **Abstract Service Specification (`AbstractService.s.dfy`):** Defines atomic client-visible linearizability and liveness (`Service_Init`, `Service_Next`, `Service_Correspondence`), completely decoupled from sockets or host implementations.
2. **Distributed Protocol Layer (`DistributedSystem.s.dfy:25-60`):** Models `DS_State(config, environment, servers)` where `DS_Next` interleaves physical network steps (`LEnvironment_Next`) with single-host transitions `DS_NextOneServer(s, s', id, ios)` calling `H_s.HostNext(s.servers[id], s'.servers[id], ios)`.
3. **Imperative Host & Verified Byte Marshaling (`Main.s.dfy:14-54`, `GenericMarshalling.i.dfy`):** The verified event loop `IronfleetMain` (`Main.s.dfy:28-53`) invokes `DS_s.H_s.HostNextImpl(env, host_state)` and enforces an explicit **Lipton reduction contract** (`lines 43-51`):
   - `assert recvs + clocks + sends == ios;`
   - `assert forall e :: (e in recvs ==> e.LIoOpReceive?) && (e in clocks ==> e.LIoOpReadClock? || e.LIoOpTimeoutReceive?) && (e in sends ==> e.LIoOpSend?);`
   - `assert |clocks| <= 1;`

Because network receives (`recvs`) commute right past independent host steps (messages remain in the network soup once received, or wait in the soup prior to consumption) and UDP sends (`sends`) commute left past independent host steps, constraining every implementation handler to perform all receives before at most one clock read (`|clocks| <= 1`, the single non-mover) followed by all sends allows `RefinementProof` (`Main.s.dfy:56-63`) to collapse interleaved fine-grained UDP I/O into atomic `DS_NextOneServer` protocol transitions. In `prophecy_mover_refinement_probe.py` (check 3), all `20 / 20` interleavings of two hosts executing `R · C · S` serialize to an equivalent serial host execution order, whereas reversing the phase to `S · C · R` produces `18 / 20` non-serializable mutual cross-host causal cycles (`Host0 Send -> Host1 Recv` interleaved with `Host1 Send -> Host0 Recv`). IronFleet's trusted computing base (`TCB`) still includes the `Dafny`->`Boogie`->`Z3` pipeline, ~1,800 lines of `.s.dfy` spec files, and the unverified .NET/C# UDP/timer shim (`NetClient`).

#### Verdi and Verdi-Raft: Network-Semantics Transformers in Rocq

Basis: **source** + **documentation** + **derived**

`Verdi` (`uwplse/verdi@7e1641b758d8`, DOI `10.1145/2813885.2737958`) takes an algebraic combinator approach in Rocq (`theories/Core/Net.v:12-136`): applications implement pure deterministic single-node handlers (`MultiParams` with `init_handlers`, `net_handlers : name -> name -> msg -> data -> list output * data * list (name * msg)`, and `input_handlers`, extended to `FailureParams` reboot hooks and `DiskOpMultiParams` append/write/delete disk ops). Reachable behaviors are defined inductively via `refl_trans_1n_trace` (`Net.v:105-111`) and proved inductive via `step_star_inductive` (`lines 130-136`).

Rather than verifying Raft or Paxos directly against duplicating, reordering, and crashing UDP networks, `Verdi` applies **Verified System Transformers (VSTs)**: higher-order functors mapping a `MultiParams` system into a transformed `MultiParams` system paired with a trace simulation theorem. For example, `SeqNum.v` / `SeqNumCorrect.v` (`lines 118-220`) tags every outbound packet via `processPackets` with strictly increasing sequence numbers (`tmNum < tdNum`), drops duplicates at `pDst`, and establishes `revertNetwork` (`lines 128-135`) projecting reachable states under `step_dup` back to the idealized `step_async` semantics. `uwplse/verdi-raft` (`a3375e867326`, DOI `10.1145/2854065.2854081`, `AllEntriesLogProof.v`) layers ghost state (`GhostSimulations`) and ~90 modular inductive invariants to prove linearizability of `vard` extracted to OCaml against `Cheerios` verified binary serialization and an unverified `verdi-runtime` event loop. VST composition excels at isolating safety proofs from fault models, yet remains single-threaded per node and lacks built-in liveness/fairness composition.

#### Disel and Aneris: Separation Logics for Composable Protocols and Sockets

Basis: **source** + **documentation**

`Verdi` compiles the entire distributed system into one global state-machine network; linking two independent verified protocols on the same node requires building a monolithic combined handler. Separation logic resolves horizontal protocol composition:

- **Disel (`DistributedComponents/disel@4ae4c207ef1a`, `theories/Core/Protocols.v:12-240`, DOI `10.1145/3158116`):** Shallowly embeds distributed protocols in Rocq using MathComp/PCM `unionmap` heaps (`dstatelet` pairing per-node `dstate` local heaps with a `dsoup` tagged-message soup). Each `protocol` (`lines 238-240`) bundles a `cohpred` coherence invariant (`CohPredMixin`, `lines 43-47`: valid state, valid soup, domain equals active `nodes d`) and dependent `SendTrans` / `ReceiveTrans` transitions (`lines 134-192`) carrying proof obligations `s_step_coh` and `r_step_coh` that every message send/consume preserves `coh`. Protocols compose horizontally across disjoint message tags (`t_snd`, `t_rcv`) and node heaps via `Worlds` framing without re-proving invariants of peer protocols.
- **Aneris (`logsem/aneris@59ae37946838`, `aneris/aneris_lang/adequacy.v:14-230`, DOI `10.1007/978-3-030-44914-8_13`):** Instantiates the step-indexed Iris separation logic (`Trillium` program logic) with a realistic multi-node, **intra-node multi-threaded** ML language (`aneris_lang`) featuring mutable local heaps (`l ↦[ip] v`), BSD-like socket handles (`sh ↪[ip] s.1`), `free_ports`, and higher-order socket-address group protocol predicates (`sag ⤳*[send_obs, recv_obs]`, `adequacy.v:43-66`). Its top-level `adequacy_multiple_strong_groups` (`lines 182-230`) proves safety and trace refinement (`aneris_to_trace_model Mdl`) down to concrete multi-node concurrent expressions provided the trace transition model satisfies `aneris_model_rel_finitary` (`line 14`: countable/finitary branching per model step). Unlike `Verdi` and `Disel`, `Aneris` handles concurrent worker threads sharing node RAM alongside asynchronous UDP sockets within one unified logic, though extraction to real OS sockets remains outside its Rocq core.

#### Verus, IronSync, and Anvil/Welder: Linear Ghost Tokens and TLA in Rust

Basis: **source** + **documentation**

`Verus` (`verus-lang/verus@c821149050c1`, DOI `10.1145/3586037`) and `IronSync` (`secure-foundations/ironsync-osdi2023@7c912e29fd9e`, `concurrency/framework/PCM.s.dfy:7-120`) turn the protocol-to-implementation refinement relation *inside out*: instead of checking whole-system global trace inclusion after writing code, developers declare a sharded state machine whose fields decompose over a Partial Commutative Monoid (`PCM.dot`, `PCM.valid`, `PCM.unit`, `PCM.transition_update`, `PCM.s.dfy:7-67`), and compile-time procedural macros (`verus-lang/verus`, `state_machines_macros/src/lib.rs:37-84`) synthesize **zero-runtime-cost linear Rust ghost tokens** (`tokenized_state_machine!`) and exchange functions.

Code inspects and mutates real Rust memory alongside linear ghost `Tracked<Token>` values; Rust's borrow/linearity checker plus Verus mode checking enforce ownership soundness (`token_transition_checks.rs:19-95` mandates `remove -> have -> add` ordering and forbids `SpecialOp` inside `if`/`match` conditionals or partial field `SubUpdate`s so the operational exchange method never diverges from the atomic transition relation). Furthermore, `Verus` guards subtle soundness traps directly in the macro AST:
- **`disallow_prophecy.rs:14-99`:** For `#![verifier::prophetic]` state machines, wraps every expression outside `require` and `assert` statements inside `vstd::prelude::prophecy_disallowed(...)` before simplification so executable logic can never branch on future-dependent prophecy values.
- **`check_birds_eye.rs:4-72`:** Prohibits `guard` or `require` statements inside `birds_eye let` bindings because guarded exchange outputs must be deterministic functions of concrete exchange inputs (`rule 3` prevents unsound ghost state leakage).

`Anvil` and `Welder` (`anvil-verifier/anvil@e83ea0f5516c`, `src/state_machine/state_machine.rs:24-89`, `src/tla_demo.rs:1-60`, `README.md:4-95`, OSDI 2024 / SOSP 2026 DOI `10.1145/3830418.3843868`) scale this paradigm to real Kubernetes cluster controllers written in Rust against `kube-rs`. Each controller implements a pure state-machine `Reconciler` trait (`reconcile_init_state`, `reconcile_core`, `reconcile_done`, `reconcile_error`, `README.md:25-36`) wrapped in `StateMachine<State, Input, ActionInput, Output, Step>` (`state_machine.rs:24-63`), while `verus-tla` encodes TLA safety and liveness (`Eventually Stable Reconciliation`, `ESR`, and compositional rely-guarantee `ControllerSpec` / `CORE`) over a formalized model of the Kubernetes API server, pod restarts, controller crashes, and network partitions.

### Refinement Completeness, Prophecy Variables, and Atomicity Splitting

#### Trace Inclusion, History Variables, and Prophecy Necessity

Basis: **normative** + **execution** + **derived**

Under Abadi and Lamport's canonical refinement theorem (*The Existence of Refinement Mappings*, `TCS 1991`, DOI `10.1016/0304-3975(91)90222-U`), implementation $\mathcal{I} = (\Sigma_{\mathcal{I}}, \mathit{Init}_{\mathcal{I}}, \mathit{Next}_{\mathcal{I}}, L_{\mathcal{I}})$ refines specification $\mathcal{S} = (\Sigma_{\mathcal{S}}, \mathit{Init}_{\mathcal{S}}, \mathit{Next}_{\mathcal{S}}, L_{\mathcal{S}})$ up to stuttering (written $\mathcal{I} \sqsubseteq \mathcal{S}$) if every externally observable behavior $\pi_{\mathrm{ext}}(\sigma)$ produced by a fair trace $\sigma$ of $\mathcal{I}$ equals (after removing finite/stuttering internal repeats) an observable behavior of $\mathcal{S}$. A pure **refinement mapping** $f : \Sigma_{\mathcal{I}} \to \Sigma_{\mathcal{S}}$ proves $\mathcal{I} \sqsubseteq \mathcal{S}$ when:
1. $f$ preserves external observation: $\mathrm{ext}_{\mathcal{S}}(f(s)) = \mathrm{ext}_{\mathcal{I}}(s)$;
2. $\mathit{Init}_{\mathcal{I}}(s) \implies \mathit{Init}_{\mathcal{S}}(f(s))$;
3. $\mathit{Next}_{\mathcal{I}}(s, s') \implies \mathit{Next}_{\mathcal{S}}(f(s), f(s')) \lor f(s) = f(s')$; and
4. $f$ maps fair $\mathcal{I}$-behaviors to fair $\mathcal{S}$-behaviors.

Refinement mappings are **incomplete** on their own for two dual reasons:
- **Forgotten past non-determinism (resolved by History Variables $\Sigma_{\mathcal{I}} \times H$):** When $\mathcal{S}$ records an earlier auxiliary event or original request ID that $\mathcal{I}$ discards for space efficiency, extending $\mathcal{I}$ with ghost history fields updated monotonically during $\mathit{Next}_{\mathcal{I}}$ restores determinism of $f$.
- **Deferred future non-determinism (resolved only by Prophecy Variables $\Sigma_{\mathcal{I}} \times \Pi$):** When $\mathcal{S}$ commits to an internal choice early (e.g., choosing `"Commit"` vs. `"Abort"` at `"Prepared"`), whereas $\mathcal{I}$ emits `"Prepared"` first and only resolves `"Commit"` vs. `"Abort"` in a subsequent racing step (`I_Prepared -> I_DoneCommit | I_DoneAbort`), no function of current or past implementation states can predict which branch $\mathcal{S}$ must pick. Executing `prophecy_mover_refinement_probe.py` (check 2, `probe_sha256: 5f6df71fb11a...`) exhaustively tests all $5^4 = 625$ candidate maps $f : \Sigma_{\mathcal{I}} \to \Sigma_{\mathcal{S}}$ on this 4-state vs. 5-state commit model and confirms `pure_forward_mappings_out_of_625 = 0`.

Adding a ghost prophecy variable $\pi \in \Pi$ constrained backward from future steps (`I_DoneCommit` forces $\pi = \text{"Commit"}$, `I_DoneAbort` forces $\pi = \text{"Abort"}$) makes the refinement mapping complete **if and only if** Abadi–Lamport's four structural obligations hold:
1. **(P1) Non-empty prophecy domain:** Every reachable implementation state admits at least one valid $\pi$;
2. **(P2) Initial agreement:** Augmented initial states project to valid $\mathcal{S}$-initial states;
3. **(P3) Backward step lifting:** Every concrete transition $u \to_{\mathcal{I}} v$ with valid target prophecy $\pi_2$ has at least one pre-state $\pi_1$ such that $(u, \pi_1) \to_{\mathcal{I}^{\Pi}} (v, \pi_2)$ (verified in the probe: `prophecy_p3_backward_lift = True`);
4. **(P4) Finite branching / non-blocking liveness preservation:** For each state $u$ and finite prefix, the set of admissible prophecy continuations predicting future choices must be finitely branching (or restricted to terminating/non-machine-closed fairness boundaries) so Koenig's Lemma ensures an infinite $\mathcal{I}$-trace lifts to an infinite $\mathcal{I}^{\Pi}$-trace without dead-ending. **Violating finite branching** (e.g., prophesying an unbounded infinite sequence of future arbitrary timestamps or failing to check backward lifting on abort paths) breaks trace soundness silently.

```text
Basis: execution (Python 3.13.15, Linux x86_64)
Probe: prophecy_mover_refinement_probe.py (sha256: 5f6df71fb11ac4032a053395c143ec1ee056523143786f3be126d5f17576f965)
Output:
  check_1_double_prime_and_qnt202: {'vacuous_enabled_steps': 0, 'stutter_trace_valid_edges': 9, 'quint_qnt202_duplicates': ['owner']}
  check_2_abadi_lamport_prophecy: {'pure_forward_mappings_out_of_625': 0, 'prophecy_p1_totality': True, 'prophecy_p2_init': True, 'prophecy_p3_backward_lift': True, 'prophecy_p4_step_sim': True}
  check_3_ironfleet_mover_reduction: {'rcs_interleavings': 20, 'rcs_non_serializable': 0, 'scr_interleavings': 20, 'scr_non_serializable': 18}
```

### Six-Level Performance, Verification, and Footprint Matrix (L1–L6)

Basis: **source** + **documentation** + **derived**

| System / Tool | (L1) Authoring Velocity & Proof Ratio | (L2) Toolchain Build Time & RSS | (L3) Checking / SMT / SAT Speed & Tail | (L4) Runtime Throughput & Latency | (L5) Certificate / Kernel Check Speed | (L6) RAM, Artifact & Binary Footprint |
| --- | --- | --- | --- | --- | --- | --- |
| `TLA+` / `TLC` / `TLAPS` | High velocity: `~100–500` LoC specs; 2–3 wk AWS onboarding (`10.1145/2699417`); zero impl linkage | Java `tla2tools.jar` (`~15 MB`); builds in seconds | `TLC`: `~10^5–10^7` states/min BFS; `TLAPS` interactive proof `s`–`min` | None (`0` production codegen; manual code rewrite required) | Explicit trace replay / `TLAPS` re-check | `TLC`: `~32–128 B`/state fingerprint table + multi-GB disk queue |
| `Quint` + `Apalache` | Typed/effected specs eliminate `QNT202` frame errors; `~0.8x–1.2x` `TLA+` LoC | Node.js `quint` + JVM `apalache` + `Z3` (`~300–500 MB` RSS) | `quint run` random trace `<1 s`; `Apalache` Z3 SSA bounded `k<=15` in `s`–`min`; high SMT variance on deep quantifiers | None (JSON trace export for MBTCG/conformance harnesses) | Re-run Z3 SMT or ITF trace replay | JVM heap `1–4+ GB` during symbolic unrolling |
| `Alloy 6` / `Pardinus` | Compact relational specs (`~50–300` LoC) | Java `org.alloytools.alloy` + JNI SAT (`MiniSat`/`Glucose`/`Lingeling`) | `<1 s`–`10s` for scopes `N <= 8–12`, `steps <= 20`; `Electrod`/`nuXmv` for unbounded | None (counterexample visualizer only) | SAT model / UNSAT core validation | `~100 MB–2 GB` JVM + CNF SAT clauses |
| `Microsoft P` | Executable state machines + ghost monitors; `~1x–2x` code LoC | `.NET 8` `p` compiler + `PChecker` (`<10 s` build) | `1,000–100,000` controlled schedules in `s`–`min` (bounded non-exhaustive) | Native C#/C/Java generated actor handlers (runtime queues + reflection) | Trace schedule seed replay (`<1 s`) | `PChecker` `.NET` process `~100–500 MB` RSS |
| `IronFleet` (`Dafny`) | `~37 KLoC` total across systems (`~8 KLoC` Multi-Paxos liveness/safety proofs); `3.7` person-years (`10.1145/2815400.2815428`) | `.NET` Dafny + Boogie + `Z3` | Module verification in `s`–`min`; **brittle Z3 trigger tails** (`rlimit` spikes on nested quantifiers) | `IronRSL` within `~2.4x` of unverified Go Multi-Paxos on `1 Gbps` (`10.1145/2815400.2815428`) | Re-verify Dafny/Z3 (large TCB: Boogie + Z3 + C# compiler) | Compiled `.NET` binaries + GC heap (`tens–hundreds MB`) |
| `Verdi` / `Verdi-Raft` (`Rocq`) | `530` LoC Raft core vs. `50,000` LoC Rocq proof (`~94x` proof-to-code ratio, `verdi-raft`) | Opam `coq-verdi` + `StructTact` + `Cheerios` (`~10–45 min` build) | Deterministic per-file `coqc` proof checking; zero SMT nondeterminism, high manual tactic repair cost | OCaml extracted `vard.native` (single-threaded per-node shim + GC) | Rocq CIC kernel `.vo` verification (`~10s–min` incremental) | Multi-hundred MB `.vo`/`.glob` build artifacts + OCaml GC binary |
| `Aneris` (`Iris` / `Rocq`) | High proof-to-code ratio (`~30x–100x`) with reusable `aneris_lang` node/socket libraries | Opam `coq-iris` + `trillium` + `stdpp` (`~20–60 min` cold build) | Interactive Rocq proof checking (`coqc`); Iris step-indexed invariants avoid SMT trigger flakiness | Research ML-like `aneris_lang` semantics (no production Rust/C++ backend) | Rocq kernel checking over Iris model | `.vo` proof files (`hundreds MB` with `stdpp`/`iris` deps) |
| `Verus` / `IronSync` / `Anvil` | Low-to-moderate ratio (`~3x–10x` for concurrent Rust/controllers); `Anvil` verifies 3 K8s controllers + RabbitMQ operator | `rustc` + `verus` + `Z3` (`~1–5 min` toolchain build) | Module checks in `<1 s–60 s` (`Anvil`); parallel per-function `Z3` queries with bounded `rlimit` | **Native zero-cost Rust**: ghost `Tracked<Token>` erased at compile time; zero GC pauses (`kube-rs` / native RAM) | Re-run `verus` SMT verification (`rustc` + `Z3` in TCB) | Small native Rust ELF (`~5–30 MB`); compiler Z3 RSS `~0.5–4 GB` |

Key cross-level synthesis (`Basis: derived`):
- **Design vs. implementation inversion at `L1`/`L3`/`L4`:** Design tools (`TLA+`, `Quint`, `Alloy`) optimize `L1` and `L3` (`< 10 s` feedback loops) by discarding `L4` code generation altogether, which creates Day-2 drift unless paired with MBTCG test synthesis (`MongoDB`) or `P`-style generated handlers.
- **SMT vs. tactic kernel split (`L1` vs. `L3`/`L5`):** Dafny (`IronFleet`) and `Verus` (`Anvil`, `IronSync`) compress `L1` proof-to-code ratios by `5x–10x` compared to `Verdi-Raft` (`~94x` Rocq LoC) by delegating linear arithmetic and framing to Z3 (`L3`), at the cost of `L3` Z3 quantifier-instantiation variance and a larger `L5` verification TCB (`Z3` vs. Rocq's CIC kernel).
- **Runtime elimination via linear ghost erasure (`L4`/`L6`):** Because `Verus` and `IronSync` erase linear `Tracked<PCM>` tokens at compilation, `L4` throughput and `L6` memory footprints match hand-written Rust without `IronFleet`'s .NET GC pauses or `Verdi`'s OCaml extraction marshaling allocations.

### Human Comprehensibility (C1) and Universal Conceptual Minimization (C2)

#### (C1) Human Comprehensibility, Trust Roots, and Diagnostic Legibility

Basis: **source** + **documentation** + **derived**

- **Working-memory budget and trust-root auditability:** A human auditor only trusts what fits in a small, inspectable boundary. `IronFleet`'s `.s.dfy` specification layer (`Main.s.dfy` `65` lines + `DistributedSystem.s.dfy` `76` lines + `AbstractService.s.dfy`) separates the trusted problem statement from tens of thousands of `.i.dfy` proof lines, letting reviewers inspect the `recvs + clocks + sends == ios` mover gate and UDP assumptions on one screen. Similarly, `Anvil`'s `ControllerSpec` (`README.md:49-65`) factors cluster rely/guarantee contracts into seven named predicates, whereas `Verdi-Raft`'s ~90 monolithic global network invariants and `Aneris`'s Iris ghost-ownership `adequate_multiple` preamble (`adequacy.v:182-210`) require deep domain familiarity with dependent separation-logic binders before a human can verify what was actually proved.
- **Counterexample and proof-failure legibility:** `Alloy 6`, `Quint`, and `PChecker` fail constructively with concrete, replayable state traces (`ITF` JSON or directed graph snapshots), directly isolating protocol flaws in human working memory. By contrast, Z3 `rlimit` timeouts in `IronFleet` and `Verus` yield opaque quantifier-instantiation loops that hide whether the invariant is false or merely unguided by triggers (`{:trigger ...}`), while Rocq tactic failures expose normalized unification terms requiring manual inversion lemmas.

#### (C2) Simplicity, Minimization, and Universal Representation

Basis: **source** + **derived**

Across the sixteen studied frameworks, accidental complexity repeatedly arises from maintaining **two disconnected worlds**—an abstract relational spec (`TLA+`/`Alloy`) and an ad-hoc imperative network program—connected only by manual prose, fragile log scrapers (`MongoDB MBTC`), or bespoke per-protocol network transformers (`Verdi` `SeqNum`/`PrimaryBackup`). Every layer in that adapter chain re-encodes the same invariants (`message delivery`, `epoch fencing`, `idempotency`, `linearizability`).

Two complementary universal representations eliminate those redundant encodings without pushing complexity into adapters:

1. **PCM-Tokenized Linear State Machines (`Verus` / `IronSync`) for Concurrency and Local State:** Modeling every shared or replicated protocol resource (locks, log entries, sequence numbers, quorum certificates) as elements of a single Partial Commutative Monoid (`PCM.s.dfy`) with linear ghost tokens unifies intra-node multi-threading, crash recovery, and inter-node protocol invariants inside one Rust/Dafny type system. Instead of separate `History`, `Prophecy`, `Network`, and `Mutex` proof layers, ordinary token exchange (`remove -> have -> add`) expresses protocol state evolution directly inside zero-overhead executable code—with `#![verifier::prophetic]` isolating prophecy strictly to specification assertions (`disallow_prophecy.rs`).
2. **Syntactic Lipton Mover Envelopes (`R* · C^{<=1} · S*`) for Network Atomicity:** `IronFleet`'s single structural discipline (`recvs + clocks + sends == ios`, `|clocks| <= 1`) turns arbitrary interleaved multi-host UDP execution into serial host transitions uniformly across Paxos (`IronRSL`), DHT (`LiveSHT`), and Lock services without protocol-specific network transformers (`Verdi` VSTs) or manual backward-simulation proofs for every new handler—provided the application never needs to send a synchronous RPC and wait for its reply inside a single atomic handler step (which breaks serializability, as verified in `prophecy_mover_refinement_probe.py`).

## Boundaries

- **not examined:**
  - Executable runs of `tlc`, `apalache`, `alloy`, `dafny`, `coqc`, or `verus` compilers locally on full `IronRSL`, `Verdi-Raft`, or `Anvil` controller suites; quantitative `L1`–`L6` figures for those suites come from primary-source repositories (`README.md`, `.dfy`/`.v`/`.rs` sources) and peer-reviewed empirical evaluations (`10.1145/2815400.2815428`, `10.1145/2854065.2854081`, `10.14778/3397230.3397233`, OSDI 2024 / SOSP 2026).
  - Real-time / clock-drift extensions (`TIOA` trajectories, bounded clock skew) inside `IronFleet` or `Verdi` beyond `|clocks| <= 1` single-step timestamps.
  - Unverified runtime wrappers beneath the extraction/verification seams (`IronFleet` C# `NetClient`, `Verdi` `verdi-runtime` OCaml loop, `Anvil` `kube-rs` serialization/HTTP client).
- **unknown:**
  - Exact Z3 `rlimit` sensitivity distribution across `Anvil` SOSP 2026 `Welder` multi-controller composition modules relative to standalone `Anvil` OSDI 2024 controllers (`not measured locally`).
- **known not to apply:**
  - `IronFleet`'s `R* · C^{<=1} · S*` single-step Lipton reduction does **not** generalize to multi-round synchronous RPC handlers that send a request and block for a peer reply mid-handler; `prophecy_mover_refinement_probe.py` confirms `18/20` interleaved `S · C · R` schedules are non-serializable.
  - `Verus`'s `tokenized_state_machine!` exchange macro explicitly forbids `SpecialOp` inside `if`/`match` branches and partial field `SubUpdate`s (`token_transition_checks.rs:19-85`).
  - `TLA+` pure forward refinement mappings **do not** hold without prophecy augmentation when abstract specs commit choices earlier than concrete implementation races (`0/625` mappings in check 2).
- **unsupported:**
  - `Alloy 6` / `Kodkod` strictly rejects integer bitwidths above `30` (`TranslateAlloyToKodkod.java:180-181`) and defaults to `4`-bit signed integers (`[-8..7]`).
  - `Verdi` VST network transformers (`Net.v`) model single-threaded sequential node handlers and do not natively verify intra-node shared-memory threads (handled instead by `Aneris` / `Verus` / `IronSync`).

## Evidence

### Primary Git Repositories and Inspected Source Locations

- **`tlaplus/tlaplus` (`bc1b506bdcad80bb518bf3776a9161c34ff0fc4c`):** `tlatools/org.lamport.tlatools/src/pcal/trans.java:1-120` (PlusCal-to-TLA+ `pc` translation, `with` macro substitution bug notes, `while(TRUE)` stuttering removal).
- **`tlaplus/tlapm` (`9a52fafb00245ace0877ec8d91c4a09a7caa8061`):** TLA+ Proof System upstream revision pinned via `git ls-remote`.
- **`informalsystems/quint` (`07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0`):** `quint/src/effects/MultipleUpdatesChecker.ts:23-66` (`exitConcrete` raising `QNT202` on duplicate variable updates).
- **`apalache-mc/apalache` (`78b8e72c982bca06507d7c1d9fc404cffc7cbb8e`):** `tlair/src/main/scala/at/forsyte/apalache/tla/lir/oper/TlaActionOper.scala:10-75` (`prime`, `stutter`, `nostutter`, `enabled`, `unchanged`, `composition`), alongside Konnov et al. OOPSLA 2019 (DOI `10.1145/3360549`).
- **`AlloyTools/org.alloytools.alloy` (`ed89fdb16c58aea17a55e312c44f99e31aa63ee1`) & `haslab/Pardinus` (`d3e7aeac73d052a28cff7f5946c85f745e3ad14c`):** `TranslateAlloyToKodkod.java:75-89, 176-310` (`bitwidth > 30` check, `always` temporal lifting, mutable singleton handling) and `TemporalTranslator.java`.
- **`p-org/P` (`6cbf558087c85bad94068947286a6ef4e7342eb5`):** `Src/PChecker/CheckerCore/SystematicTesting/TestingEngine.cs:43-118` (`ISchedulingStrategy` portfolio execution), alongside Desai et al. PLDI 2013 (DOI `10.1145/2491956.2462184`).
- **`microsoft/Ironclad` (`2fe4dcdc323b92e93f759cc3e373521366b7f691`):** `ironfleet/src/Dafny/Distributed/Common/Framework/Main.s.dfy:14-65` (`IronfleetMain`, `recvs + clocks + sends == ios`, `|clocks| <= 1`, `RefinementProof`) and `DistributedSystem.s.dfy:25-60` (`DS_State`, `DS_Init`, `DS_NextOneServer`, `DS_Next`), alongside Hawblitzel et al. SOSP 2015 (DOI `10.1145/2815400.2815428`).
- **`uwplse/verdi` (`7e1641b758d8f0032aa7de63620bc115330e0a6b`) & `uwplse/verdi-raft` (`a3375e867326a82225e724cc1a7b4758b029376f`):** `theories/Core/Net.v:12-136` (`MultiParams`, `FailureParams`, `DiskOpMultiParams`, `refl_trans_1n_trace`, `step_star_inductive`), `theories/Systems/SeqNumCorrect.v:9-220` (`processPackets`, `revertNetwork`, `sequence_sane`), `verdi-raft/README.md:1-217`, and `AllEntriesLogProof.v:1-100`, alongside PLDI 2015 (`10.1145/2813885.2737958`) and CPP 2016 (`10.1145/2854065.2854081`).
- **`DistributedComponents/disel` (`4ae4c207ef1a25010d63508f2bbda2d4c197d5ab`):** `theories/Core/Protocols.v:12-240` (`getLocal`, `Coherence.mixin_of`, `SendTrans`, `ReceiveTrans`, `Protocol`), alongside Sergey et al. POPL 2018 (DOI `10.1145/3158116`).
- **`logsem/aneris` (`59ae37946838df77fb2c573803b68462a3af9d0f`):** `aneris/aneris_lang/adequacy.v:14-230` (`aneris_model_rel_finitary`, `wp_group_proto_multiple_strong`, `adequacy_multiple_strong_groups`), alongside Krogh-Jespersen et al. ESOP 2020 (DOI `10.1007/978-3-030-44914-8_13`).
- **`verus-lang/verus` (`c821149050c1269f32771a11582bee2fc58e5a8a`), `secure-foundations/ironsync-osdi2023` (`7c912e29fd9e770d2fb9866606d0bf2a97629252`), & `anvil-verifier/anvil` (`e83ea0f5516ce2ece26740266165180018741e66`):** `state_machines_macros/src/{lib.rs:37-84, disallow_prophecy.rs:14-99, check_birds_eye.rs:4-72, token_transition_checks.rs:19-95}`, `concurrency/framework/PCM.s.dfy:7-120`, `anvil/src/state_machine/state_machine.rs:24-89`, `anvil/src/tla_demo.rs:1-60`, and `anvil/README.md:4-95`, alongside `10.1145/3586037` and `10.1145/3830418.3843868`.

### Normative Theory and Non-Academic Industrial Literature

- Abadi, M., & Lamport, L. (1991). *The Existence of Refinement Mappings*. Theoretical Computer Science, 82(2), 253–284. DOI `10.1016/0304-3975(91)90222-U`.
- Newcombe, C., Rath, T., Zhang, F., Munteanu, B., Brooker, M., & Deardeuff, M. (2015). *How Amazon Web Services Uses Formal Methods*. Communications of the ACM, 58(4), 66–73. DOI `10.1145/2699417`.
- Bornholt, J., et al. (2021). *Using Lightweight Formal Methods to Validate a Key-Value Storage Node in Amazon S3* (`ShardStore`). SOSP 2021. DOI `10.1145/3477132.3483540`.
- Brooker, M., & Desai, A. (2025). *Systems Correctness Practices at Amazon Web Services*. Communications of the ACM. DOI `10.1145/3729175`.
- Davis, A. J. J., Hirschhorn, M., & Schvimer, J. (2020). *eXtreme Modelling in Practice*. PVLDB 13(9). DOI `10.14778/3397230.3397233`, and MongoDB Engineering Blog (*"Conformance Checking At MongoDB: Testing That Our Code Matches Our TLA+ Specs"*).
- Cloudflare Engineering Blog (2020). *"A Byzantine failure in the real world"* (`https://blog.cloudflare.com/a-byzantine-failure-in-the-real-world/`).

### Preserved Standalone Executable Micro-Probe (`prophecy_mover_refinement_probe.py`)

Command: `python3 prophecy_mover_refinement_probe.py` (`Python 3.13.15`, Linux `x86_64`, observed `2026-11-19`, exit `0`, SHA-256 `5f6df71fb11ac4032a053395c143ec1ee056523143786f3be126d5f17576f965`).

```python
#!/usr/bin/env python3
"""Self-contained micro-probe for protocol modeling traps, prophecy mappings, and mover reduction."""
import hashlib
import itertools
from pathlib import Path


def check_double_prime_and_qnt202():
    """1. TLA+ double-prime vacuous conjunction vs Quint QNT202 duplicate-update detection."""
    owners = ("None", "NodeA", "NodeB")
    epochs = (0, 1, 2)
    states = [(o, e) for o in owners for e in epochs]

    # Buggy TLA+ macro composition: owner' = "NodeA" /\ owner' = "None" /\ epoch' = epoch + 1
    def buggy_next(s, s_next):
        _, e = s
        o2, e2 = s_next
        return (o2 == "NodeA") and (o2 == "None") and (e2 == (e + 1) % 3)

    # Stuttering closure [Next]_vars permits (s, s) even when Next has 0 enabled edges
    def stutter_next(s, s_next):
        return s_next == s or buggy_next(s, s_next)

    enabled_edges = sum(1 for s in states for s2 in states if buggy_next(s, s2))
    stutter_edges = sum(1 for s in states for s2 in states if stutter_next(s, s2))

    # Quint MultipleUpdatesChecker (QNT202) detects duplicate state-variable targets statically
    effect_updates = ["owner", "owner", "epoch"]
    seen = set()
    duplicates = sorted({v for v in effect_updates if v in seen or seen.add(v)})
    return {
        "vacuous_enabled_steps": enabled_edges,
        "stutter_trace_valid_edges": stutter_edges,
        "quint_qnt202_duplicates": duplicates,
    }


def check_abadi_lamport_prophecy():
    """2. Abadi-Lamport TCS 1991: late-choice implementation requires prophecy over pure forward map."""
    spec_states = [
        ("Idle", None),
        ("Prepared", "Commit"),
        ("Prepared", "Abort"),
        ("DoneCommit", "Commit"),
        ("DoneAbort", "Abort"),
    ]
    spec_init = {("Idle", None)}
    spec_next = set(
        [(s, s) for s in spec_states]
        + [
            (("Idle", None), ("Prepared", "Commit")),
            (("Idle", None), ("Prepared", "Abort")),
            (("Prepared", "Commit"), ("DoneCommit", "Commit")),
            (("Prepared", "Abort"), ("DoneAbort", "Abort")),
        ]
    )

    impl_states = ["I_Idle", "I_Prepared", "I_DoneCommit", "I_DoneAbort"]
    impl_obs = {
        "I_Idle": "Idle",
        "I_Prepared": "Prepared",
        "I_DoneCommit": "DoneCommit",
        "I_DoneAbort": "DoneAbort",
    }
    impl_init = {"I_Idle"}
    impl_next = [
        ("I_Idle", "I_Prepared"),
        ("I_Prepared", "I_DoneCommit"),
        ("I_Prepared", "I_DoneAbort"),
        ("I_DoneCommit", "I_DoneCommit"),
        ("I_DoneAbort", "I_DoneAbort"),
    ]

    valid_pure_maps = 0
    for assignment in itertools.product(spec_states, repeat=len(impl_states)):
        f = dict(zip(impl_states, assignment))
        if not all(f[u][0] == impl_obs[u] for u in impl_states):
            continue
        if not all(f[u] in spec_init for u in impl_init):
            continue
        if all((f[u], f[v]) in spec_next for (u, v) in impl_next):
            valid_pure_maps += 1

    # Prophecy variable pi in {"Commit", "Abort"} predicting future decision at Done*
    pi_vals = ("Commit", "Abort")
    aug_states = [
        ("I_Idle", "Commit"),
        ("I_Idle", "Abort"),
        ("I_Prepared", "Commit"),
        ("I_Prepared", "Abort"),
        ("I_DoneCommit", "Commit"),
        ("I_DoneAbort", "Abort"),
    ]
    aug_next = [
        ((u, p1), (v, p2))
        for (u, p1) in aug_states
        for (v, p2) in aug_states
        if (u, v) in impl_next and p1 == p2
    ]

    def f_prophecy(aug):
        u, pi = aug
        if u == "I_Idle":
            return ("Idle", None)
        if u == "I_Prepared":
            return ("Prepared", pi)
        if u == "I_DoneCommit":
            return ("DoneCommit", "Commit")
        return ("DoneAbort", "Abort")

    p1_totality = all(any(u == u0 for (u, _) in aug_states) for u0 in impl_states)
    p2_init = all(f_prophecy((u, pi)) in spec_init for (u, pi) in aug_states if u in impl_init)
    p3_backward_lift = all(
        any(((u, p1), (v, p2)) in aug_next for p1 in pi_vals if (u, p1) in aug_states)
        for (u, v) in impl_next
        for p2 in pi_vals
        if (v, p2) in aug_states
    )
    p4_step_sim = all((f_prophecy(a), f_prophecy(b)) in spec_next for (a, b) in aug_next)
    return {
        "pure_forward_mappings_out_of_625": valid_pure_maps,
        "prophecy_p1_totality": p1_totality,
        "prophecy_p2_init": p2_init,
        "prophecy_p3_backward_lift": p3_backward_lift,
        "prophecy_p4_step_sim": p4_step_sim,
    }


def check_ironfleet_mover_reduction():
    """3. IronFleet Main.s.dfy recvs + clocks + sends reduction vs non-reducible Send-before-Recv."""
    def serializable_schedules(seq_h0, seq_h1):
        # Host 0 executes (op0, op1, ...), Host 1 executes (op0, op1, ...)
        # Causal violation occurs if Host 0 sends m01 -> Host 1 recvs m01 AND Host 1 sends m10 -> Host 0 recvs m10
        schedules = []
        n0, n1 = len(seq_h0), len(seq_h1)
        for picks0 in itertools.combinations(range(n0 + n1), n0):
            s0 = set(picks0)
            i0 = i1 = 0
            sched = []
            for pos in range(n0 + n1):
                if pos in s0:
                    sched.append((0, seq_h0[i0]))
                    i0 += 1
                else:
                    sched.append((1, seq_h1[i1]))
                    i1 += 1
            schedules.append(sched)

        non_serial = 0
        for sched in schedules:
            idx_send_0 = next(i for i, x in enumerate(sched) if x == (0, "S"))
            idx_recv_0 = next(i for i, x in enumerate(sched) if x == (0, "R"))
            idx_send_1 = next(i for i, x in enumerate(sched) if x == (1, "S"))
            idx_recv_1 = next(i for i, x in enumerate(sched) if x == (1, "R"))
            # Mutual cross-host read-from dependency cannot occur in any serial host execution
            if idx_send_0 < idx_recv_1 and idx_send_1 < idx_recv_0:
                non_serial += 1
        return len(schedules), non_serial

    rcs_total, rcs_bad = serializable_schedules(("R", "C", "S"), ("R", "C", "S"))
    sr_total, sr_bad = serializable_schedules(("S", "C", "R"), ("S", "C", "R"))
    return {
        "rcs_interleavings": rcs_total,
        "rcs_non_serializable": rcs_bad,
        "scr_interleavings": sr_total,
        "scr_non_serializable": sr_bad,
    }


if __name__ == "__main__":
    digest = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print("probe_sha256:", digest)
    print("check_1_double_prime_and_qnt202:", check_double_prime_and_qnt202())
    print("check_2_abadi_lamport_prophecy:", check_abadi_lamport_prophecy())
    print("check_3_ironfleet_mover_reduction:", check_ironfleet_mover_reduction())
```

## Revalidation

To revalidate these findings against newer upstream commits or local runtime environments cheaply without repeating the full literature synthesis:

1. **Rerun the embedded micro-probe:** Save the Python source block above as `prophecy_mover_refinement_probe.py` and run `python3 prophecy_mover_refinement_probe.py`, confirming SHA-256 `5f6df71fb11ac4032a053395c143ec1ee056523143786f3be126d5f17576f965` and identical dictionary outputs (`0` pure forward mappings, `Prophecy P1–P4 = True`, `0/20` non-serializable `R·C·S` schedules, `18/20` non-serializable `S·C·R` schedules).
2. **Check `Quint` duplicate-update enforcement (`QNT202`):** Diff `quint/src/effects/MultipleUpdatesChecker.ts` against commit `07d7a1a69c2093b5bc656caf3b5dfefa0d766cd0` to verify `QNT202` still rejects repeated variable targets in a single `ConcreteEffect`.
3. **Check `IronFleet` Lipton mover contract and `Verus` prophecy/birds-eye AST gates:** Diff `microsoft/Ironclad@2fe4dcdc323b` (`Main.s.dfy:44-51`) for `recvs + clocks + sends == ios` and `|clocks| <= 1`, and diff `verus-lang/verus@c821149050c1` (`disallow_prophecy.rs`, `check_birds_eye.rs`, `token_transition_checks.rs`) for `prophecy_disallowed` wrapping and `remove -> have -> add` token order enforcement.
4. **Check `Anvil`/`Welder` TLA + Rust boundary:** Diff `anvil-verifier/anvil@e83ea0f5516c` (`src/state_machine/state_machine.rs` and `src/shim_layer/mod.rs`) to verify whether API server models or `ControllerSpec` relies/guarantees have changed across Kubernetes releases.
