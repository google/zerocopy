# Closing the TLA+ / Quint Protocol-to-Rust Implementation Seam in Lean 4: Comparative Architecture Trade-Offs, TLC Blindspots, and Blind-Holdout Generalization

## Summary

Bridging high-level distributed and concurrent protocol specifications (`TLA+`, `Quint`, and NDJSON / Quint ITF trace validation) to Rust/MIR operational semantics inside Lean 4 (`v4.34.1`) under Anneal's strict trusted-boundary discipline (`TrustedBoundary.lean`: `trustLevel := 0` fresh kernel replay, 3-axiom ceiling `{propext, Classical.choice, Quot.sound}`, `0` `sorry`/`opaque`/`._unsafe_rec`, and Statement-Origin Separation) reveals five concrete engineering findings from a controlled 3-architecture comparative evaluation across three shared benchmarks, six planted-bug negative controls, a data-layout refactor test, and an unseen blind-holdout protocol:

1. **Zero-Trusted-LOC Protocol Refinement Is Mechanically Viable:** All three architectures—(1) *Quint/TLA+→Lean Lowering*, (2) *Lean-Native Protocol DSL Exporting to TLC with Counterexample Back-Mapping*, and (3) *Three-Rung Monotonic Trace-Faithfulness Ratchet*—discharged full safety, wait-episode deadlock freedom, prophecy-backed crash-recovery refinement, and conditional fair liveness with **`0` new trusted Lean LOC** (`theory/`-only proofs of `10,522`–`12,243` LOC replayed in `45–55s`), `0` `._unsafe_rec`, and axioms strictly within `{propext, Classical.choice, Quot.sound}` (`Basis: execution`).
2. **Empirical TLC 2.15 Blindspots Closed Only by Lean/Static Checks:** Direct execution of `tlaplus/tlaplus` TLC `2.15` (`defe0c74915b`) empirically confirms two structural blindspots in unaugmented TLA+ model checking and trace validation:
   - **Contradictory-prime stuttering vacuity (`M5`):** An action asserting contradictory primed updates (`x' = 1 /\ x' = 2`) silently evaluates to `FALSE` and collapses into `[Next]_vars` stuttering, causing TLC to **pass vacuously** (`exit 0`, `2` generated / `1` distinct state) on an otherwise false safety invariant (`committed => x = 999`).
   - **Lying trace instrumentation (`M6`):** A trace logger that emits `FsyncOk` / `Commit` events when the concrete implementation skipped the durable write causes TLC trace validation (`TraceView == <<vars, l>>`, `TraceMatched`) to **pass blindly** (`exit 0`, `15` generated / `14` distinct states). Both defects are eliminated only when static duplicate-update checking (`Quint` `QNT202` / DSL linter) and Lean MIR-to-event faithfulness proofs bind emitted trace records to concrete state transitions (`Basis: execution`).
3. **Lean-Native DSL + Out-of-TCB TLA+ Export Dominates Pure Generalization (86/100 vs. 76/100 and 75/100):** Evaluating all three unmodified toolchains on an unseen blind-holdout protocol (*Lease-Fenced Reconfigurable Primary-Backup Replication*) exposed severe benchmark hardcoding in both the Quint/TLA+→Lean translator (`5` tool/core failures) and the hand-coded NDJSON/ITF codec (`--protocol` restricted to two hardcoded names), whereas the Lean-native DSL's out-of-TCB exporter ran end-to-end unmodified, matched the reference TLA+ state space exactly (`606,217` generated / `83,838` distinct states), caught the planted stale-primary bug (`404 / 198` states), and automatically back-mapped the 5-state TLC counterexample to Lean and Rust symbol names (`Basis: execution`).
4. **Why `verse-lab/veil` (Veil 2.0) Cannot Serve as the Pass-1 Authoritative Core:** Direct source inspection of `verse-lab/veil` (`02791b2d1576`) establishes four hard incompatibilities with `TrustedBoundary.lean`: (a) Lean `v4.32.0` + 9 external dependencies (`lean-smt`, `lean-cvc5`, `aesop`, `batteries`, `Loom`, `ProofWidgets4`) outside `foundation-lock.json`; (b) banned `module`/`public import`/`initialize`/macro/`@[grind]` syntax; (c) default `veil.smt.trust := true`; and (d) safety-only semantics lacking wait-episode deadlock freedom, fairness (`WeakFair`/`StrongFair`), open interaction traces, and prophecy simulation (`Basis: source`).
5. **Recommended Hybrid Synthesis (`D2 + D3 + D1-Inspired`):** Combining (a) a single-source `TrustedBoundary`-clean Lean `ProtocolDSL` + parameterized TLA+ exporter & counterexample back-mapper (fixing D2's dual-authoring drift and hardcoded node-parameter `ValidatePostState(n)` indexing bug), (b) a monotonic `Rung 0 → Rung 1 → Rung 2` trace-faithfulness ratchet (rejecting lying trace loggers as a Lean type error at Rung 0 and compiling per-action certificates directly into `SoundRefines` at Rung 2 with a schema-driven NDJSON↔ITF codec), and (c) a generalized out-of-TCB Quint/bounded-TLA+ front-end + `QNT202` linter + Pass-2 differential/correspondence validation yields the lowest TCB, fastest layout-refactor resilience (`0` protocol-spec diff, `595` LOC / `0.73s` repair), and immediate trace-validation adoption (`Basis: derived`).

## Applicability

This report applies to verifying Rust systems software against high-level concurrent or distributed protocol specifications in Lean 4 (`leanprover/lean4` `v4.34.1`) under `google/zerocopy` (`anneal/`, commit `d2f63ce1c3c04ffabb4442b028caf612c9508387`) `TrustedBoundary.lean` replay constraints:

- **Target verification boundary:** `prelude` + locked `Init.*` foundation (`foundation-lock.json`), `trustLevel := 0` kernel replay, axiom ceiling `{propext, Classical.choice, Quot.sound}`, `0` `sorry`/`opaque`/`isUnsafe`/`isPartial`/`._unsafe_rec`, and strict Statement-Origin Separation (external parsers, exporters, and model checkers never appear in theorem statement types `ci.type`).
- **Subjects relationship:** Evaluates `google/zerocopy`'s `TrustedBoundary.lean` audit rules and open-machine stuttering refinement pattern in combination with `tlaplus/tlaplus` TLC `2.15` (`defe0c74915b`) and `informalsystems/quint` (`659c210febdb`) ITF/typed-action conventions, while comparing `verse-lab/veil` (`02791b2d1576`) as a candidate Lean-native transition-system DSL.
- **Scope of concrete models examined:** All Lean proofs in the comparative study targeted concrete Lean-modeled Rust/MIR transition systems (ticket lock + bounded credit channel with demonic OS spurious `futex` wakeups; 2-phase commit / single-decree Lease-Raft over crash-`fsync` + adversarial network; `Vec`→`RingBuf 4` refactor; and Lease-Fenced Primary-Backup replication), rather than end-to-end `rustc`-captured multi-threaded crates.

## Findings

### 1. Shared Evaluation Matrix and Experimental Design

To prevent confirmation bias and surface hidden tool hardcoding, three genuinely distinct architectures were evaluated against an identical frozen benchmark suite, six planted-bug negative controls, a storage-layout refactor test, and an unseen blind holdout protocol (`Basis: execution`):

| Evaluation Artifact | Technical Scope & Required Properties |
| :--- | :--- |
| **T1 (Single-Node Synchronization)** | `TicketLock + BoundedCreditChannel(C)` coupled to a concurrent transition system separating enabled program steps (`progStepBy`) from demonic OS spurious `futex_wait` wakeups (`osSpuriousWakeBy`, tagged with `waitEpisodeId` and carrying **no** `acquire` clock synchronization). Required: mutual exclusion + credit slot conservation, multi-PC wait-episode subsystem deadlock freedom (`SubsystemDeadlockFreeWaitEpisode`), and per-thread `WeakFair` starvation freedom for bounded waiter `T0`. |
| **T2 (Crash-Recovery Consensus + Prophecy)** | Minimal 2PC / single-decree Lease-Raft slice over an open `EnvContract` combining an asynchronous adversarial network (drop, duplicate, reorder, partition) with volatile RAM wipe on crash and explicit `fsync` durability barriers. Concrete nodes commit upon receiving a quorum reply while the abstract spec commits atomically (requiring prophecy/backward simulation). Required: crash durability, agreement, `SoundRefines`, prophecy erasure adequacy, and non-vacuous conditional liveness. |
| **T2-Refactor (Zero-Spec-Diff Resilience)** | Replaces T2's dynamic `List`/`Vec` log representation with a fixed-capacity modular ring buffer (`RingBuf 4`, `head`/`len`/`cap`). Required: **`0` lines modified** in the protocol specification (Lean, `.qnt`, and `.tla`) while re-proving agreement, durability, and `SoundRefines`. |
| **T3 (NDJSON & Quint ITF Trace Conformance)** | Real `tlc2.TLC` (`2.15`) replay over flat NDJSON (`"event"` + mapped parameters + `ValidatePostState*` fields, `TraceView == <<vars, l>>`, `TraceMatched`) and Quint ITF JSON (`#meta`/`vars`/`states`/`#bigint`) traces, verifying valid traces pass and missing-`fsync` traces fail. |
| **M1–M6 (Six Planted-Bug Negative Controls)** | `M1`: omitted `fsync` before `PrepareAck` (crash split-brain); `M2`: missing term check on late commit; `M3`: multi-PC AB-BA `futex` retry loop that deadlocks while toggling `pc` on spurious wakes; `M4`: unfair spin-CAS lock claimed starvation-free under `WeakFair` (and `StrongFair ∧ ActionWeakFair`); `M5`: contradictory TLA+ prime (`x' = 1 /\ x' = 2`) collapsing into stuttering; `M6`: lying trace logger emitting `FsyncOk`/`Commit` without flushing. |
| **H1 (Unseen Blind Holdout)** | *Lease-Fenced Reconfigurable Primary-Backup Replication* (epoch fencing, stale-primary write rejection, async failover with epoch bump, volatile crash + `fsync`, plus planted stale-primary-accept bug `H1_Bug`), exercised cold without modifying any core framework file of the three architectures. |

### 2. Quantitative Comparison Across the Three Architectures

All three architectures were cold-audited from scratch via `TrustedBoundary.lean` (`trustLevel := 0`, Lean `v4.34.1`, `foundation-lock.json`) with SHA-256 manifest verification (`130/130` frozen implementation files matched, `0` mismatches) and zero `sorry`/`opaque`/`isUnsafe`/`isPartial`/`._unsafe_rec` (`Basis: execution`):

| Metric | Architecture 1 (`Quint`/TLA+ → Lean) | Architecture 2 (Lean DSL → TLA+ Export & Back-Map) | Architecture 3 (`Rung 0→1→2` Trace Ratchet) |
| :--- | :---: | :---: | :---: |
| **New Trusted LOC (`Trusted.*`)** | `0` | `0` | `0` |
| **Total `theory/` LOC (T1+T2+Refactor+M1–M6)** | `12,243` (10 modules) | `10,853` (8 modules) | `10,522` (6 modules) |
| **Cold `TrustedBoundary` Replay (`trustLevel := 0`)** | `4,723` decls / `302` thms / `45.15s` | `5,085` decls / `495` thms / `46.20s` | `4,910` decls / `264` thms / `54.64s` |
| **Axioms (Global Closure)** | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` | `{propext, Classical.choice, Quot.sound}` |
| **Mutant Kill Gate (`M1`–`M6`)** | `6/6` PASS | `6/6` PASS | `6/6` PASS |
| **T2-Refactor (`Vec` → `RingBuf 4`) Spec Diff** | `0` lines | `0` lines | `0` lines |
| **T2-Refactor Repair LOC / Standalone Compile** | `611` LOC / `0.763s` | **`595` LOC / `0.734s`** | `914` LOC / `0.904s` |
| **Blind Holdout H1 Boilerplate LOC / Cold Audit** | `1,176` LOC / `25.999s` | **`831` LOC / `24.150s`** | `871` LOC / `25.066s` |
| **Unmodified Out-of-TCB Tool on Blind Holdout H1** | **Failed (5 hardcoding defects)** | **Worked end-to-end (1 indexing bug)** | **Failed (`--protocol` hardcoded `{t1, t2}`)** |
| **Weighted 100-Point Rubric Score** | `76 / 100` | **`86 / 100` (Pure Winner)** | `75 / 100` |

*Rubric weight breakdown (`TCB 25 / UX 20 / Proof+Refactor 20 / Expressiveness 15 / Incremental Velocity 10 / Blind H1 + Mutants 10`):*
- **Architecture 1 (`76`):** `22 + 13 + 15 + 14 + 6 + 6`
- **Architecture 2 (`86`):** `23 + 16 + 18 + 13 + 7 + 9`
- **Architecture 3 (`75`):** `21 + 11 + 16 + 12 + 8 + 7`

### 3. Empirical TLC 2.15 Results and Structural Blindspots

Executing `tlaplus/tlaplus` TLC `2.15` (`defe0c74915b`) via `support/tla_probes/run_tlc_probes.py` yields the following deterministic baseline measurements (`Basis: execution`):

| Probe (`support/tla_probes/`) | Exit Code | States Generated | Distinct States | Observed Behavior |
| :--- | :---: | :---: | :---: | :--- |
| `T2Spec.tla` + `T2Spec.cfg` (`GuardFsync = TRUE`) | `0` | `6,308,555` | `1,322,446` | Exhaustive safety PASS. |
| `T2Spec.tla` + `MC_hunt_fsync.cfg` (`GuardFsync = FALSE`) | `12` | `8,396`–`8,461` | `2,699`–`2,731` | Caught `DurabilityInv` violation (`M1` negative control). |
| `T2Trace.tla` + `t2_valid.ndjson` / `t2_valid.itf.json` | `0` | `17` | `16` | Valid NDJSON & Quint ITF trace PASS (`TraceMatched`). |
| `T2Trace.tla` + `t2_m1_missing_fsync.{ndjson,itf.json}` | `11` | `11` | `11` | Caught missing-`fsync` trace via deadlock at cursor `l = 11`. |
| **`M5_ContradictoryAction.tla` (`x' = 1 /\ x' = 2`)** | **`0`** | **`2`** | **`1`** | **TLC BLINDSPOT:** `BadCommit` collapses to `FALSE`; `[Next]_vars` stuttering hides dead action so `committed => x = 999` passes vacuously. |
| **`T2Trace.tla` + `m6_lying_trace.ndjson`** | **`0`** | **`15`** | **`14`** | **TLC BLINDSPOT:** Fabricated trace claiming `FsyncOk`/`Commit` passes TLC validation because TLC cannot inspect concrete implementation state transitions. |
| `H1Spec.tla` + `H1Spec.cfg` (Holdout) | `0` | `606,217` | `83,838` | Exhaustive safety PASS. |
| `H1Trace.tla` + `h1_valid.ndjson` / `h1_valid.itf.json` | `0` | `18` / `10` | `17` / `9` | Valid holdout NDJSON & Quint ITF trace PASS. |
| `H1Trace.tla` + `h1_bug_stale_primary.ndjson` | `11` | `7` | `7` | Caught stale-primary write bug via trace deadlock. |

*(Minor state-count variance on `MC_hunt_fsync.cfg`, e.g. `8,396/2,699` vs. `8,461/2,731`, reflects TLC's early-stop check timing upon detecting the first `DurabilityInv` violation.)*

### 4. Blind-Holdout Generalization and Architectural Failure Modes

Exercising unmodified tools on unseen Holdout H1 exposed concrete engineering failure modes invisible on visible benchmarks (`Basis: execution`):

1. **Architecture 1 (`Quint`/TLA+ → Lean Lowering) — Parser/Translator Fragility:**
   - The ad-hoc translator failed on multi-line `VARIABLES` in `H1Spec.tla` (`rc=1`, undeclared variable error), crashed on idiomatic Quint `p.in(NODES)` (`NotImplementedError`), emitted ill-typed Lean `((in p NODES) = true)` for functional `in(p, NODES)`, triggered `-Dlinter.unusedVariables=true` on `NODES.mapBy(n => 0)`, and silently ignored `--eff H1Eff` (emitting `OpenMachine ClosedEff` because only T1/T2 effect signatures were wired).
   - Additionally, its prophecy bridge imported T2 directly instead of parameterizing over abstract machines.
   - *Takeaway:* Parsing surface TLA+/Quint directly into Lean is brittle unless built on a real typed AST (e.g., Quint's JSON IR) and kept strictly outside the trusted boundary.
2. **Architecture 2 (Lean-Native Protocol DSL → TLA+ Export & Back-Mapper) — Strongest Generality, Two Concrete Gaps:**
   - Unmodified export of H1 from Lean produced a TLA+ spec matching `H1Spec.tla`'s exact exhaustive state space (`606,217 / 83,838`), caught the planted `H1_Bug` (`404 / 198`, `exit 12`, `StalePrimaryFenced`), and automatically back-mapped the 5-state TLC trace back into Lean/Rust identifiers (`H1Bench.H1_StalePrimaryFenced`, `repl::stale_primary_fenced`, `repl::primary_write`, `repl::start_failover`, `storage::fsync`, `repl::backup_recv`).
   - *Two exposed defects:* (a) The prototype authored the Lean `ProtocolMachine` and its exportable `TlaModelIR` side-by-side rather than deriving both from one definition (creating drift risk); (b) generated `ValidatePostState(n)` hardcoded a single node parameter `(n)`, failing (`exit 150`, `Unknown operator: e`) when validating an epoch-indexed array `committed'[e]`.
   - *Additional gap:* T1 proved all three required T1 properties directly without instantiating an open `SoundRefines` witness on T1 (whereas T2, T2-Refactor, and H1 all proved `SoundRefines`).
3. **Architecture 3 (`Rung 0 → Rung 1 → Rung 2` Trace Ratchet) — Strongest Incremental Honesty, External Codec Fragility:**
   - Its `485`-LOC Lean `Ratchet` core was 100% protocol-agnostic (`0` benchmark imports) and instantiated cleanly on H1 (`871` LOC), rejecting lying trace instrumentation (`M6`) **at type-check time** (`¬ TraceFaithful` blocks constructing a Rung 0 certificate) and monotonically shrinking an explicit `TCBLog : List TCBItem` from Rung 1 (`[tlcInvariant, tlcFairness]`) to `[]` at Rung 2.
   - *Two exposed defects:* (a) Its external NDJSON↔ITF CLI hardcoded `--protocol ∈ {t1, t2}` and failed on H1 (`rc=2`); (b) its `ratchetRung1ToOpenRefinement` combinator accepted an external `KripkeStutterSim` rather than compiling `Rung1Cert.perActionCerts` directly into `KripkeStutterSim`.

### 5. Why `verse-lab/veil` (Veil 2.0) Was Rejected as the Pass-1 Authoritative Core

Direct inspection of `verse-lab/veil` (`02791b2d1576efc88fcbfcd417cbb2862c88a8ad`) against `google/zerocopy` (`d2f63ce1c3c0`) `TrustedBoundary.lean` establishes four disqualifiers for Pass-1 authoritative use (`Basis: source`):

1. **Toolchain & Dependency Isolation:** `lake-manifest.json` pins Lean `v4.32.0` and 9 external packages (`aesop`, `batteries`, `Qq`, `Loom`, `lean-smt`, `lean-cvc5`, `lean-auto`, `VerifiedHAMT`, `ProofWidgets4` + Node.js/npm widgets), whereas `TrustedBoundary.lean` locks Lean `v4.34.1` and 51 `Init.*` modules with zero native C++ solver FFI.
2. **Syntax Allowlist Rejection:** Veil relies on Lean `module` / `public import` / `public meta import` headers, `initialize` / `register_option` (`Veil/Base.lean:29–186`), custom commands/macros (`veil module`, `action`, `transition`, `#check_invariants`, `#model_check`), `@[grind]`, and `veil_smt` (`Veil/Frontend/DSL/Tactic.lean:21–44`). `TrustedBoundary.lean` (`L558–715`) restricts `allowedHeaderKinds` to `{header, prelude, import}`, bans `macro`/`syntax`/`elab`/`initialize`/`#eval`, and excludes `grind`/`smt` even from `allowedTheorySyntaxKinds`.
3. **SMT Oracle Trust Default:** `Veil/Base.lean:144–148` defaults `veil.smt.trust := true`, contradicting `trustLevel := 0` zero-SMT-axiom replay.
4. **Semantic Scope (Safety-Only):** `README.md:7–10` and `Veil/Core/Tools/ModelChecker/TransitionSystem.lean:25–156` model closed safety-only transition systems without wait-episode spurious-wakeup deadlock (`ConcSystem`), scheduler/action fairness (`WeakFair`/`StrongFair`), open interaction `EnvContract`s, or prophecy backward simulation. Veil remains viable only as an optional, strictly out-of-TCB counterexample-to-induction (CTI) discovery sidecar.

### 6. Subtle Specification Traps Discovered During Formalization

Two subtle protocol-specification defects surfaced during mechanization (without modifying frozen models) and serve as reusable design rules (`Basis: execution`, `derived`):

1. **Fairness-vs.-Fault Contradiction in Bounded-Term Consensus (`T2` Liveness):** Quantifying `ActionWeakFair` over *all* actions `act : Action` including `.crash n` while an `EventualSynchrony` premise forbids `.crash` after global stabilization time (`gst`) makes the liveness premise vacuous (`EventualSynchrony ∧ ActionWeakFair → False`). Furthermore, capping terms to `{1, 2}` when `restart` resets `volRole := .follower` permits an 8-step pre-GST prefix that exhausts both terms permanently. Sound liveness theorems must restrict `ActionWeakFair` to **protocol progress actions** (excluding adversarial fault actions), guard against pre-GST term exhaustion, and pair every conditional liveness theorem with a **constructive satisfiability witness** (`∃ run, ValidRun run ∧ Premise run`).
2. **Minimum Term Count for Raft Figure 8 Split-Brain (`M2`):** In a 3-node cluster with `GuardFsync = true` and `isValidTerm` capped at `{1, 2}`, a broken leader that omits the current-term commit check can violate the *same-term commit-quorum invariant* (committing via mixed-term acks `{ack(1, 1, 0), ack(2, 1, 2)}` in 19 steps) yet cannot split-brain two conflicting values `v₁ ≠ v₂` within 2 terms—classic Raft Figure 8 agreement violation requires **≥ 3 terms** (demonstrated in 41–44 steps in a 4-term extension).

### 7. Recommended Hybrid Synthesis Architecture

Combining the empirically strongest component of each architecture resolves every individual weakness (`Basis: derived`):

1. **Authoritative Core Spine (from Architecture 2, upgraded):** A single `0`-trusted-LOC `prelude` Lean `ProtocolDSL` unifying operational semantics (`OpenMachine` + `Trusted.Concurrency` fairness + prophecy/layout bridges) and export IR into **one** Lean definition (eliminating dual-authoring drift), paired with an out-of-TCB exporter generating `.tla`/`.cfg`/`*Trace.tla`/`.backmap.json` with dynamically parameterized `ValidatePostState(...)` bindings and automatic TLC counterexample back-mapping into Lean/Rust names.
2. **Monotonic `Rung 0 → Rung 1 → Rung 2` Trace Ratchet (from Architecture 3, upgraded):** A protocol-agnostic `ProtocolTraceSchema` layered directly onto the DSL spine so Rung 0 proves `TraceFaithful` (rejecting lying trace loggers `M6` as a Lean type error while TLC validates traces), Rung 1 attaches per-action simulation certificates with an explicit `TCBLog`, and Rung 2 compiles `Rung1Cert.perActionCerts` directly into `KripkeStutterSim` / `SoundRefines` with `tcbLog = []`, paired with a schema-driven NDJSON↔Quint-ITF codec derived from the DSL's IR metadata.
3. **Generalized Brownfield Front-End (from Architecture 1, strictly out-of-TCB):** A Quint JSON-IR / bounded-TLA+ front-end lowering existing `.qnt`/`.tla` specs into the unified Lean DSL with static `QNT202`/contradictory-prime checking (`M5`) and Pass-2 differential trace conformance against TLC/Apalache, keeping all parsing 100% outside `trusted/` and `ci.type`.

## Boundaries

- **Not examined — end-to-end `rustc` multi-threaded MIR capture:** All Lean proofs in this study refined Lean-modeled Rust state machines (`T1`, `T2`, `T2-Refactor`, `H1`) rather than MIR extracted directly by `anneal-rustc-capture` (`Trusted.MirSemantics.Crate`, which currently models single-threaded sequential crates). Wiring multi-threaded `MirSemantics` and `ResPCM` into live `CrateTheorem` remains separate work.
- **Not examined — `Apalache` symbolic model checking and `Quint` CLI execution:** Local verification executed `tlaplus/tlaplus` TLC `2.15` (`defe0c74915b`) directly and validated Quint ITF JSON (`#meta`/`#bigint`/`#set`/`#map`) and `.qnt` syntax structurally; invoking the `quint` TypeScript/Rust CLI or `apalache-mc` SMT engine directly was not measured.
- **Adapter boundary — TLC `2.15` without `CommunityModules-deps.jar`:** Because standalone `tla2tools.jar` `2.15` lacks `CommunityModules`'s `Json!ndJsonDeserialize`, `support/tla_probes/run_tlc_probes.py` parses and validates flat NDJSON and Quint ITF JSON in Python and compiles `TraceLog == << ... >>` into a temporary pure-TLA+ `TraceData.tla` module before running unmodified `tlc2.TLC`.
- **Known not to apply — Veil 2.0 inside `TrustedBoundary.lean`:** As established in Findings §5, `verse-lab/veil` (`02791b2d1576`) cannot pass `TrustedBoundary.lean` preflight or `foundation-lock.json` replay without violating Anneal's zero-external-dep / zero-SMT-axiom policy.
- **Unsupported / open in prototypes:** Unifying Architecture 2's `ProtocolMachine` + `TlaModelIR`, fixing `ValidatePostState` dynamic parameter binding, compiling Architecture 3's `Rung1Cert` directly into `KripkeStutterSim`, and building a schema-driven NDJSON↔ITF codec are derived design specifications from the evaluation rather than already-merged library code.

## Evidence

- **Upstream subjects inspected:**
  - `google/zerocopy` (`d2f63ce1c3c04ffabb4442b028caf612c9508387`): `anneal/trusted/audit/TrustedBoundary.lean` (SHA-256 `96a189dcd64213b77dd0090d12d492ab680306daff9fb3ae00987740b97af053`, syntax allowlists `L558–715`) and `anneal/trusted/lean/foundation-lock.json` (SHA-256 `37f780b6257d0bc99fd5d7d3d0a1f168ef066a2a01466f4076f080d3425d2`).
  - `leanprover/lean4` (`v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`): standalone `trustLevel := 0` kernel replay across all three candidate Lean implementations (`33,618` total `theory/` LOC + `2,878` total holdout LOC; `0` trusted LOC; `0` `._unsafe_rec`/`sorry`/`opaque`).
  - `tlaplus/tlaplus` (`2.15`, commit `defe0c74915b1c27c6af2fb55c8163f3574c8918`, `tla2tools.jar` SHA-256 `3325ab526b3dd40d292a6e8005a60ef1554f473cffa86dbaffc38cc954406d85`): live execution on OpenJDK 27.0.1 confirming all 12 baseline, mutant, and holdout probes in Findings §3.
  - `verse-lab/veil` (`02791b2d1576efc88fcbfcd417cbb2862c88a8ad`): `README.md:7–10`, `lakefile.lean:114–193`, `Veil/Base.lean:11–186`, `Veil/Frontend/DSL/Tactic.lean:21–44`, `Veil/Core/Tools/ModelChecker/TransitionSystem.lean:25–156`.
  - `informalsystems/quint` (`659c210febdb1c5ecfb3c6696d1d073d706c99c7`): ITF JSON schema (`#meta`/`#bigint`/`#set`/`#map`) and static duplicate-update checking (`QNT202`).
- **Preserved self-contained support artifacts (`support/tla_probes/`):**
  - `M5_ContradictoryAction.{tla,cfg}` — minimal 2-state / 1-distinct-state TLC stuttering-vacuity reproducer.
  - `T2Spec.{tla,cfg,qnt}`, `MC_hunt_fsync.cfg`, `T2Trace.{tla,cfg}`, `t2_valid.{ndjson,itf.json}`, `t2_m1_missing_fsync.{ndjson,itf.json}`, `m6_lying_trace.ndjson` — complete T2 crash-`fsync` model, negative control, valid/buggy traces, and `M6` lying-instrumentation reproducer.
  - `H1Spec.{tla,cfg}`, `H1Trace.{tla,cfg}`, `h1_valid.{ndjson,itf.json}`, `h1_bug_stale_primary.ndjson` — Lease-Fenced Reconfigurable Primary-Backup holdout model and traces.
  - `run_tlc_probes.py` — standalone Python 3.10+ stdlib revalidation driver executing all 12 TLC `2.15` probes.

## Revalidation

To independently reproduce all TLC `2.15` model-checking baselines, trace validations, and both empirical TLC blindspots (`M5` contradictory-prime stuttering vacuity and `M6` lying trace instrumentation), run the preserved driver with any `tla2tools.jar` (`2.15` or newer) and JDK:

```bash
python3 reports/tla-quint-to-lean-rust-protocol-refinement-tradeoffs-and-tlc-blindspots/support/tla_probes/run_tlc_probes.py \
  --tla2tools /path/to/tla2tools.jar
```

Pass `--skip-full-t2` to run the 11 fast probes (including `M5`, `M6`, `MC_hunt_fsync`, NDJSON/ITF trace validation, and `H1`) in `<15s`; omit it to also exhaustively check `T2Spec.tla` (`6,308,555` generated / `1,322,446` distinct states, `~96s` with `-workers 1`). Expected exit code is `0` with `"matched": true` on all 12 JSON lines (`M5_vacuous_pass`: `exit 0`, `2/1`; `m6_lying_ndjson_blind_pass`: `exit 0`, `15/14`; `MC_hunt_fsync_fail`: `exit 12`; `t2_m1_*_fail` and `h1_bug_ndjson_fail`: `exit 11`).

To revalidate the `verse-lab/veil` compatibility boundary against a newer `TrustedBoundary.lean` or Veil release, inspect `Veil/Base.lean` (`veil.smt.trust` default, `initialize`/`register_option`), `lake-manifest.json` (Lean toolchain and external dependencies), and `TransitionSystem.lean` (support for fairness/open effects) against `anneal/trusted/audit/TrustedBoundary.lean` (`allowedHeaderKinds`, `allowedTheorySyntaxKinds`) and `foundation-lock.json`.
