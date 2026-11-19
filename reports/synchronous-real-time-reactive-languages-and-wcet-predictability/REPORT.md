# Synchronous, Real-Time Reactive Languages, and WCET Predictability

## Summary

Hard real-time reactive systems require two invariants that general-purpose languages, optimizing compilers, and out-of-order (OoO) processors break: **deterministic, bounded-space logical causality** and **sound, compositional Worst-Case Execution Time (WCET) bounds**. Examining synchronous languages (`Esterel`, `Lustre`/`Vélus`), deterministic timed coordination (`Lingua Franca`), modal functional reactive programming (`Rattus`/`AsyncRattus`), verified cost-preserving compilers (`Quantitative CompCert`, `CerCo`), and time-predictable processors (`PRET`, `Patmos`) establishes four governing results:

1. **Strict synchronous causality hierarchy (`syntactic acyclicity ⊊ constructive causality ⊊ unique classical fixpoint`)**: Under the perfect synchrony hypothesis, instantaneous signal cycles can contradict (`present S then nothing else emit S`, 0 models), oscillate ambiguously (`present S then emit S else nothing`, 2 models), or form non-constructive classical tautologies (`present S then emit S else emit S`, 1 classical model $S=1$, yet physically unresolved). `Lustre` and `Vélus` reject all syntactic cycles (`Is_used_inst` + `AcyGraph` in `INRIA/velus`), trading expressiveness for polynomial-time checks; `Esterel` (Berry 1999) and cyclic combinational synthesis (Malik 1994) use monotone Kleene $K_3 = \{\bot, 0, 1\}$ (`Must`/`Can`) fixpoints to accept branch-guarded stabilizing cycles while rejecting tautologies (co-NP-complete in general).
2. **Dependent clock alignment and verified stream-to-assembly compilation (`Vélus`)**: Multi-rate synchronous dataflow requires identical dependent clocks (`Cbase | Con ck x (ty, b)` in `INRIA/velus:src/Clocks.v`) across combinational operations. `Vélus` proves deterministic coinductive trace bisimulation (`behavior_asm_velus_world_trace_node_and_nothing_else` in `src/VelusCorrectness.v`) from Lustre with `reset` and state machines through `CompCert` Clight to assembly—guaranteeing functional equivalence, **not** machine-level WCET compliance.
3. **Static elimination of FRP space and time leaks via Fitch-style modal types (`Rattus`/`AsyncRattus`)**: Higher-order FRP (`Elliott & Hudak 1997`) leaks memory and replay latency across dynamic `switch` closures. Fitch-style single-tick contexts (`Γ ✓ Γ'`), `O`/`Box` modalities, `Stable` strictness, and GHC plugin checks (`CheckClockCompatibility.hs` + `Strictify.hs`) statically guarantee causality, productivity, and absence of implicit space leaks across both single-clock (`Rattus`) and multi-clock asynchronous (`AsyncRattus`) streams.
4. **Microarchitectural timing anomalies break compositional WCET addition**: Dynamic OoO scheduling, speculative fetch, and non-LRU caches violate timing monotonicity (`Lundqvist & Stenström 1999`; `Reineke et al. 2006`). Locally speeding up one instruction (cache miss $\to$ hit) can *increase* total makespan, amplify miss penalties beyond local latency, or cause unbounded loop **domino effects** ($+k$ cycles over $k$ iterations). Sound WCET requires either conservative state-splitting abstract interpretation (`AbsInt aiT`; `Wilhelm et al. 2008`) or restoring timing compositionality via cost-preserving verified compilation (`Quantitative CompCert`, `CerCo`) and time-predictable silicon (`PRET`, `Patmos`).

All three formal claims (Kleene $K_3$ causality, dependent clock unification, and cycle-accurate OoO timing anomalies including a 2-FU `4c` miss $\to$ `1c` hit inversion from `12c` to `14c` plus Lundqvist & Stenström RTSS 1999 Figs. 2–3) are mechanically verified by [`support/verify_constructive_causality_and_wcet.py`](support/verify_constructive_causality_and_wcet.py).

## Applicability

This report covers the foundational language semantics, modal/dependent type systems, verified compilation chains, distributed timed runtimes, and microarchitectural timing properties underlying hard real-time reactive systems.

### Subject Relationships

The 25 subjects in `REPORT.json` pair normative literature with directly inspected pinned source revisions and executable verification:

| Layer | Normative Literature | Pinned Source / Executable Probe | Relationship |
| --- | --- | --- | --- |
| Constructive causality & cyclic logic | Berry (Draft Book v3.0, 1999); Malik (IEEE TCAD 1994) | `support/verify_constructive_causality_and_wcet.py` (Part 1) | Normative semantics + executable verifier |
| Synchronous dataflow & verified compilation | Halbwachs et al. (Proc. IEEE 1991); Bourke et al. (PLDI 2017, POPL 2020, EMSOFT 2023) | `INRIA/velus@27ba860c2624ba232816591290c6c119b9ead88a` (CompCert submodule `inria-parkas/CompCert@22c33b91d42c7df986c97b13b6cd630866a56494`) | Theory grounded directly in Coq proofs |
| Deterministic timed & distributed reactors | Lohstroh et al. (ACM TECS 2021) | `lf-lang/lingua-franca@0df8a987e37d6bc0cc8daa1c3e6167df14eaae59`; `lf-lang/reactor-c@abbf0aaf468af55f298e1ae4816156e9f7552784` | Semantics + Java graph + C federated runtime |
| Leak-free modal FRP | Elliott & Hudak (1997); Krishnaswami et al. (2012); Bahr et al. (2019); Bahr & Møgelberg (2023) | `pa-ba/Rattus@f8cfe7411ccebef78f74a73e1a6a2e57a106b256` (`v0.5.1.1`); `pa-ba/AsyncRattus@8043692908bb1d1f01cd0b1ad07bca06eb9df79f` (`v0.2.2`) | Modal calculi verified in GHC plugins |
| WCET, timing anomalies & cost preservation | Lundqvist & Stenström (1999); Reineke et al. (2006); Wilhelm et al. (2008); Carbonneaux et al. (2014); Amadio et al. (2013); Blazy et al. (2013) | `support/verify_constructive_causality_and_wcet.py` (Part 3) | Formal definitions + cycle-accurate simulator |
| Time-predictable processors | Edwards & Lee (DAC 2007); Schoeberl et al. (Real-Time Systems 2018) | `t-crest/patmos@4c72814972c8e19d69c987e3b29d764efb6a7d8c` | Architectural guarantees verified in Chisel RTL |

### Adjacent Corpus Cross-References

- **`anneal-cps-robotics-aerospace-eda-and-quantum-survey`**: Surveys industrial aerospace/PLC/EDA toolchains (`SCADE`, `Copilot`, `Kind 2`, `KeYmaera X`, `PLCverif`). This report complements it with deep PL semantics, constructive causality, dependent clock calculi, Vélus Coq internals, and reactor coordination.
- **`anneal-security-crypto-zkp-wcet-parsers-and-ffi-survey`**: Surveys constant-time cryptographic compilers (`Jasmin`, `CompCert-CT`, `FaCT`) and Rust-oriented WCET/stack-analysis integration. This report complements it with microarchitectural timing-anomaly theory, cost-preserving verified compilation, and time-predictable processor RTL (`Patmos`, `PRET`).

### Scope and Qualification Rules

- Source claims apply strictly to the pinned 40-character revisions above; semantic theorems apply to any system satisfying the stated formal hypotheses.
- `Rattus` / `AsyncRattus` guarantees hold **only** when compiled with `-fplugin=Rattus.Plugin` / `-fplugin=AsyncRattus.Plugin` and plugin strictification enabled.

## Findings

### 1. The Synchronous Hypothesis, Constructive Causality, and Separate Compilation

Basis: normative + source + execution + derived

Synchronous reactive languages (`Esterel`, `Lustre`, `SCADE`) achieve deterministic concurrency via the **perfect synchrony hypothesis**: execution advances in discrete logical instants (ticks) $n = 0, 1, 2, \dots$ within which computation and signal broadcast take zero logical time, while all state updates cross instant boundaries through explicit delays (`pause`, `pre`, `fby`).

#### 1.1 Causality Pathologies and Kleene $K_3$ Constructive Semantics

Allowing signals to be emitted and tested within one instant creates circular dependencies. A classical Boolean semantics requires a total assignment $\sigma : \mathcal{S} \to \{0, 1\}$ satisfying the **signal coherence law** ($\sigma(s) = 1 \iff s$ is emitted under $\sigma$). Classical coherence fails operationally in three cases (Berry 1999, Draft Book v3.0):

1. **Contradiction (0 models)**: `present S then nothing else emit S` forces $S \iff \neg S$ (an oscillating combinational inverter loop).
2. **Ambiguity (2 models)**: `present S then emit S else nothing` forces $S \iff S$, admitting both $\sigma(S) = 0$ and $\sigma(S) = 1$ (a bistable latch).
3. **Non-constructive tautology (1 unique classical model, yet causally stuck)**: `present S then emit S else emit S` has unique classical solution $\sigma(S) = 1$, yet a causal evaluator or gate demultiplexer $S = (1 \land S) \lor (1 \land \neg S)$ must know $S$ *before* activating either branch, leaving $S$ stuck at unknown ($\bot$).

Berry's **constructive semantics** (Berry 1999) and Malik's **cyclic combinational circuit analysis** (Malik 1994) evaluate signals over Kleene's flat 3-valued lattice $K_3 = \{\bot, 0, 1\}$ ($\bot \sqsubset 0, 1$) with monotone gate laws $0 \land \bot = 0$, $1 \lor \bot = 1$, $\neg \bot = \bot$:

- Given fixed Boolean inputs and local/output signals initialized to $\bot$, each iteration computes $\mathrm{Must}(P, \sigma)$ (guaranteed emissions) and $\mathrm{Can}(P, \sigma)$ (possible emissions).
- Crucially, when $\sigma(s) = \bot$, `present s then p else q` blocks both branches for `Must` while unioning `Can`:
  $$\mathrm{Must}(\text{present } s \text{ then } p \text{ else } q, \sigma) = \emptyset, \qquad \mathrm{Can}(\text{present } s \text{ then } p \text{ else } q, \sigma) = \mathrm{Can}(p, \sigma) \cup \mathrm{Can}(q, \sigma).$$
- Setting $\sigma'(s) = 1$ when $s \in \mathrm{Must}$ and $\sigma'(s) = 0$ when $s \notin \mathrm{Can}$ converges monotonically in $\le |\mathcal{S}| + 1$ steps to a unique least fixpoint $\sigma^*$. A program is **constructively causal** iff $\sigma^*(s) \in \{0, 1\}$ for every reachable state and input vector.

#### 1.2 Strict Inclusion Hierarchy and Complexity Trade-Off

Executing `support/verify_constructive_causality_and_wcet.py` (Part 1) verifies the strict hierarchy `syntactic acyclicity ⊊ constructive causality ⊊ unique classical model`:

| Program / Circuit | Syntactic Graph | Classical Models | $K_3$ Constructive Fixpoint | Lustre / Vélus | Esterel (Berry) |
| --- | --- | --- | --- | --- | --- |
| `present I then (present A then emit B \|\| emit A) else (present B then emit A \|\| emit B)` | Cyclic (`A <-> B`) | `[1, 1]` | Total (`A=1, B=1` for all `I`) | Rejected | **Accepted** |
| `present I then (present A then emit B) else (present B then emit A \|\| emit B)` | Cyclic (`A <-> B`) | `[1, 1]` | Total (`I=1 -> 0,0` via `Can`; `I=0 -> 1,1`) | Rejected | **Accepted** |
| Malik (1994) mux loop: $y_1 = (\neg c \land x_1) \lor (c \land y_2)$, $y_2 = (c \land x_2) \lor (\neg c \land y_1)$ | Cyclic (`y1 <-> y2`) | Unique (all 8 inputs) | Total (`y1=y2=x1` if $c=0$, else `x2`) | Rejected | **Accepted** |
| `present S then nothing else emit S` | Cyclic (`S -> S`) | `[0]` | Stuck (`S = ⊥`) | Rejected | Rejected |
| `present S then emit S else nothing` | Cyclic (`S -> S`) | `[2]` | Stuck (`S = ⊥`) | Rejected | Rejected |
| `present S then emit S else emit S` | Cyclic (`S -> S`) | `[1]` ($S=1$) | Stuck (`S = ⊥`) | Rejected | Rejected |

**Complexity vs. precision (derived)**: Deciding constructiveness over all $2^n$ input vectors is **co-NP-complete** (Malik 1994), requiring BDD/SAT solvers in Esterel compilers. `Lustre` and `Vélus` trade cyclic expressiveness for polynomial-time syntactic acyclicity. In `INRIA/velus@27ba860c` (`src/Lustre/LCausality.v` L31–73, L580–588):
- `Is_used_inst` tracks instantaneous dependencies: `IUIfby` (L48–50) examines *only* `e0s` in `e0s fby es` (breaking cycles across ticks), whereas `IUIarrow` (L51–54) examines both `e0s` and `es`.
- `node_causal n` (L585–587) demands an explicit `AcyGraph` witness for every node.

#### 1.3 Separate Compilation and Modular Causality Interfaces

Compiling a synchronous module $M(i_1, i_2) \to (o_1, o_2)$ into one monolithic step function `step_M(state, i1, i2)` erases intra-instant input-to-output dependencies. If $o_1 = i_1 + 1$ and $o_2 = \text{pre}(i_2)$, external feedback $i_2 = o_1$ is causally acyclic ($i_1 \to o_1 \to i_2$), yet opaque `step_M` creates a false cycle. In `INRIA/velus@27ba860c`, `LCausality.v` rule `IUIapp` (L68–72) conservatively links *every* output of a node call to *all* inputs `es` and reset signals `er`. Avoiding spurious cycles under separate compilation requires exposing a bipartite I/O dependency interface and splitting compiled modules into multiple statically scheduled step fragments (`step_M_1`, `step_M_2`).

---

### 2. Lustre Dependent Clock Calculus and End-to-End Verified Compilation in Vélus

Basis: normative + source + execution

#### 2.1 Dependent Clock Calculus

In `Lustre` (Halbwachs et al. 1991) and `Vélus` (Bourke et al. PLDI 2017 / POPL 2020 / EMSOFT 2023), every stream carries a **dependent clock** naming the base clock or a boolean/enum carrier stream controlling subsampling. Inspecting `INRIA/velus@27ba860c` (`src/Clocks.v` L17–31):

```coq
Inductive clock : Type :=
| Cbase : clock                                      (* base clock *)
| Con   : clock -> ident -> type * enumtag -> clock. (* subclock: ck on tag(x) *)

Fixpoint instck (bk: clock) (sub: ident -> option ident) (ck: clock) : option clock :=
  match ck with
  | Cbase => Some bk
  | Con ck x b =>
      match instck bk sub ck, sub x with
      | Some ck', Some x' => Some (Con ck' x' b)
      | _, _ => None
      end
  end.
```

`src/Lustre/LClocking.v` (L71–137) enforces exact clock alignment via `wc_exp`:

| Expression | Vélus Rule (`LClocking.v`) | Alignment Constraint | Output Clock |
| --- | --- | --- | --- |
| `op(e1, e2)` | `wc_Ebinop` (L76–81) | `clockof e1 = [ck]` and `clockof e2 = [ck]` | `ck` |
| `e0s fby es` | `wc_Efby` (L89–94) | Initial `e0s` and stepped `es` match `map snd anns` | `map snd anns` |
| `es when b(x)` | `wc_Ewhen` (L103–108) | `HasClock Γ x ck` and all `es` have clock `ck` | `Con ck x (ty, b)` |
| `merge x (...)` | `wc_Emerge` (L110–116) | `HasClock Γ x ck`; branch `i` has clock `Con ck x (tx, i)` | `ck` |
| `f(es) every er` | `wc_Eapp` (L130–137) | Formal clocks satisfy `WellInstantiated bck sub` via `instck` | Instantiated clocks |

**Lustre V4 `current` vs. Vélus/SCADE 6 `merge` + `fby`**: Classic Lustre V4 projected `Con ck x true` back to `ck` via `current(e)` (holding the last present value, which evaluates to undefined `nil` if `x` starts `false`). SCADE 6 and `Vélus` replace `current` with exhaustive `merge` over complementary subclocks plus initialized `fby`; `INRIA/velus@27ba860c` (`README.md` L11–12) explicitly omits uninitialized `pre e`, requiring `0 fby e`. Part 2 of `support/verify_constructive_causality_and_wcet.py` verifies both aligned expressions (`merge`, nested `when`, polymorphic `instck`, V4 `current`) and static rejection of five misaligned cases (`x + (x when c)`, `(x when c) + (y when not c)`, `(x when c) + (y when b)`, `(x when c) when b`, and `merge c (x when c) y`).

#### 2.2 Vélus Compilation Pipeline and End-to-End Correctness Theorem

Direct inspection of `INRIA/velus@27ba860c` (`src/Velus.v` L57–150) traces the verified lowering chain:

```text
LustreAst (unverified OCaml LustreParser2.ml)
  -> elab_declarations         [yields G + proof Gp : wc_global G /\ wt_global G]
  -> l_to_nl (src/Velus.v L88-106):
       complete_global -> is_causal -> auto_global (EMSOFT '23 state machines)
       -> switch_global -> inlinelocal_global -> unnest_global
       -> normlast_global -> normfby_global -> TR.Tr.to_global
  -> NLustre -> optional verified opts (exp_inlining, dce_global, remove_dup_regs)
  -> NL2Stc -> Stc (Synchronous Transition Systems)
       -> CutCycles (external cutting_points)
       -> schedule_program: external OCaml `schedule` VALIDATED by Coq `Stc.SchV.well_sch`
  -> Stc2Obc -> Obc (nested state structs with reset/step methods, POPL '20)
       -> optional verified opts (fuse_program, normalize_switches, deadcode_program)
       -> add_defaults -> ObcToClight.Generation.translate
  -> CompCert Clight -> add_builtins (Axiom add_builtins_spec, L128-132)
  -> transf_clight2_program (inria-parkas/CompCert@22c33b91) -> CompCert Asm
```

Key verification invariants in `src/Velus.v` and `src/VelusCorrectness.v`:
- **Translation-validated scheduling (`src/Velus.v` L32–33, L73–86)**: External OCaml heuristics `cutting_points` and `schedule` remain outside the proof; `schedule_program` validates every output schedule in Coq via `Stc.SchV.well_sch`, returning `Error` on any violation.
- **Deterministic coinductive trace bisimulation (`src/VelusCorrectness.v` L202–292)**: `Theorem behavior_asm` and `Corollary behavior_asm_velus_world_trace_node_and_nothing_else` prove that for any elaborated program `G` compiling via `lustre_to_asm (Some main) G = OK P` with well-typed base-clock inputs `ins` and dataflow semantics `Sem.sem_node G main (pStr ins) (pStr outs)`, **every** assembly behavior interacting with `velus_world G main ins` matches the unique infinite volatile-I/O trace `Reacts (trace_node node ins outs ...)` (relying on `Asm.semantics_determinate`).

#### 2.3 Vélus TCB Audit

At `27ba860c`, Vélus's TCB comprises: (1) unverified OCaml lexing/parsing (`LustreLexer.ml`, `Relexer.ml`, `LustreParser2.ml`, `Makefile` L35–38); (2) `Axiom add_builtins_spec` (`src/Velus.v` L128–132), assuming builtin injection preserves non-wrong `Clight.semantics2` behaviors; (3) Coq kernel, OCaml extraction, CompCert's unverified assembler/linker, and the volatile-I/O `velus_world` hardware assumption; and (4) **no timing/WCET semantics**—`Asm.semantics` proves functional trace equivalence only, leaving tick-deadline satisfaction to external WCET verification.

---

### 3. Deterministic Timed Concurrency Across Networks: Lingua Franca Reactors and Ptides STP Offsets

Basis: normative + source + documentation

**Reactors** and **Lingua Franca (LF)** (Lohstroh, Menard, Bateni & Lee, ACM TECS 2021) extend deterministic synchronous-reactive semantics to multicore and networked distributed systems without actor-model message nondeterminism.

#### 3.1 Superdense Logical Tags and Static Precedence Levels

Events carry a lexicographically ordered **superdense logical tag** $g = (t, m) \in \mathbb{T} \times \mathbb{N}$. Inspecting `lf-lang/reactor-c@abbf0aaf` (`tag/api/tag.h` L56–122; `core/tag.c` L48–95):

```c
// lf-lang/reactor-c@abbf0aaf: tag/api/tag.h L101-122
typedef int64_t instant_t;      // nanoseconds (NEVER = LLONG_MIN, FOREVER = LLONG_MAX)
typedef int64_t interval_t;     // nanosecond duration
typedef uint32_t microstep_t;   // superdense microstep index (0 .. UINT_MAX)
typedef struct {
  instant_t time;
  microstep_t microstep;
} tag_t;
```

- `core/tag.c` (L48–95) implements saturating arithmetic on `NEVER` and `FOREVER` in `lf_time_add`, `lf_time_subtract`, and `lf_tag_add`, preventing signed overflow from reversing tag order. Connections with `after d` advance $(t, m)$ to $(t+d, 0)$ if $d > 0$ or $(t, m+1)$ if $d = 0$ (breaking zero-delay loops via microstep increment).
- In `lf-lang/lingua-franca@0df8a987` (`core/src/main/java/org/lflang/graph/PrecedenceGraph.java` L40–100), Tarjan's SCC algorithm statically rejects zero-delay causality cycles and topologically partitions reactions into precedence levels; reactions within one level execute concurrently across cores with guaranteed sequential-equivalent determinism.

#### 3.2 Federated Coordination: Centralized RTI vs. Decentralized Ptides STP Offsets

Across distributed federates, logical time consistency trades off directly against network availability/latency. `lf-lang/reactor-c@abbf0aaf` implements two modes:

1. **Centralized RTI (`core/federated/RTI/`)**: Network input ports use three-valued status `typedef enum { absent = false, present = true, unknown } port_status_t;` (`include/core/lf_types.h` L120). Federates block until upstream ports resolve from `unknown` to `present`/`absent` via RTI tag-advance grants, preserving strict determinism at the cost of blocking indefinitely under partitions; tardy messages abort execution (`core/federated/federate.c` L690).
2. **Decentralized Ptides / Safe-To-Process (`STP_offset`)**: Using synchronized physical clocks (e.g., IEEE 1588 PTP) and a per-federate `STP_offset` / `STA_offset` (`include/core/federated/federate.h` L662–670; `core/reactor_common.c` L215–221):
   - A federate waits via `lf_wait_until_time(tag)` until physical time reaches $T_{\text{physical}} \ge t + \text{STP\_offset}$ (`core/federated/federate.c` L1336–1370), while incoming messages raise `lf_tag_advancement_barrier_t` (`include/core/lf_types.h` L72–87; `federate.c` L616) to freeze local tag advancement until message insertion completes.
   - **Soundness condition**: Whenever $E_{\text{clock}} + L_{\text{network}} + W_{\text{upstream}} \le \text{STP\_offset}$, assuming remaining `unknown` ports are `absent` at $t + \text{STP\_offset}$ yields exact global determinism with zero coordination traffic.
   - **Explicit violation recovery**: If a network fault breaks the bound and a message arrives with `lf_tag_compare(intended_tag, env->current_tag) <= 0` (`federate.c` L691–694), the runtime assigns `actual_tag = env->current_tag; actual_tag.microstep++;` and invokes the reaction's explicit **`STP_handler`** (`core/reactor_common.c` L984) for deterministic fault handling.

---

### 4. Functional Reactive Programming (FRP) Space/Time Leaks and Modal Type-Theoretic Cures

Basis: normative + source + derived

#### 4.1 Implicit Space and Time Leaks in Naive Higher-Order FRP

Classic higher-order FRP (`Fran`, Elliott & Hudak ICFP 1997) models continuous values as `Behavior a = Time -> a` and discrete occurrences as `Event a = [(Time, a)]`, supporting dynamic graph reconfiguration via `switch :: Behavior a -> Event (Behavior a) -> Behavior a`. Without temporal scoping restrictions, two failure modes arise:

- **Implicit space leak**: A closure created inside a `switch` captures a stream `s` rooted at $t_0$. Retaining that reference prevents garbage collection of all historical samples $t_0 \dots t_k$, growing heap usage as $\Theta(k)$ even when only the current sample is ever observed.
- **Implicit time leak**: Demanding a lazily switched behavior or stream accumulator at tick $t_k$ replays all $k$ prior transitions from $t_0$ inside one tick, causing an $O(k)$ deadline-violating latency spike.

#### 4.2 Guarded/Linear Capabilities vs. Fitch-Style Modal FRP (`Rattus` / `AsyncRattus`)

1. **Linear/Affine Guarded FRP (`Krishnaswami, Benton & Hoffmann, POPL 2012`)**: Combines a guarded "later" modality ($\bullet A$) with linear heap capabilities and region-based deallocation so each tick reclaims the prior tick's input heap in bounded space, at the cost of linear plumbing and dual-context syntax.
2. **Fitch-Style Modal Reactive Calculi (`Simply RaTT` ICFP 2019; `Rattus`; `AsyncRattus` ICFP 2023)**: Bahr, Graulund & Møgelberg use a single typing context containing at most one tick separator `✓`, two modalities (`O` = "later", `Box` = "time-invariant"), and a `Stable` predicate. Direct inspection of `pa-ba/Rattus@f8cfe741` (`src/Rattus/Primitives.hs` L20–88) gives the exact typing rules:

```text
  Γ ✓ ⊢ t :: τ                  Γ ⊢ t :: O τ                  Γ☐ ⊢ t :: τ                Γ ⊢ t :: Box τ
----------------- (delay)    --------------------- (adv)   ------------------ (box)    ------------------ (unbox)
 Γ ⊢ delay t :: O τ           Γ ✓ Γ' ⊢ adv t :: τ           Γ ⊢ box t :: Box τ          Γ ⊢ unbox t :: τ
```

- **Context stripping**: `delay` pushes `✓`, blocking access to pre-tick non-`Stable` bindings except inside `adv` (which discards `✓ Γ'`). `box` strips `✓` and every non-`Stable` variable (`Γ☐`).
- **`Stable` predicate (`Primitives.hs` L20–29)**: Requires strict data free of bare `O` or `->` outside `Box`. `Int`, `Box (a -> b)`, and `Box (Str a -> Str b)` are `Stable`; lazy `[Int]`, `Int -> Int`, `O Int`, and `Str Int` are rejected from crossing ticks.
- **Single-tick invariant + guarded recursion**: Forbidding nested ticks prevents `O (O a)` values from retaining multi-tick references (ensuring 1-tick heap reclamation), while requiring recursive calls under `delay` statically guarantees **productivity** and **causality**.

#### 4.3 Multi-Clock Asynchronous FRP (`AsyncRattus`) and GHC Plugin Enforcement

`pa-ba/AsyncRattus@80436929` (Bahr & Møgelberg, ICFP 2023) generalizes `Rattus` to independent asynchronous input channels (`src/AsyncRattus/InternalPrimitives.hs` L27–119; `src/AsyncRattus/Plugin/CheckClockCompatibility.hs` L26–85):

- **Clock-tagged delays & union `select`**: `data O a = Delay !Clock (InputValue -> a)` pairs each delayed thunk with the channel set waking it (`never = Delay IntSet.empty ...`). Eliminating two delayed computations requires a clock-union tick `✓cl(s)⊔cl(t)` via `select :: O a -> O b -> Select a b` (`data Select a b = Fst !a !(O b) | Snd !(O a) !b | Both !a !b`), recomputing only subgraphs whose channels actually ticked.
- **Compile-time rejection classes (`CheckClockCompatibility.hs` L26–85)**: The GHC plugin tracks `Ctx { current, hidden :: Map Var HiddenReason, earlier :: Maybe LCtx, recDef, stableTypes, allowGuardedRec }`, enforcing the single-tick invariant via `earlier :: Maybe LCtx` and raising a `TypeError` for: (1) non-stable capture across one `delay` (`earlier`), (2) across two `delay`s (`DelayApp`), (3) under `box` (`BoxApp`), (4) post-tick variable inside `adv` (`AdvApp`), (5) non-stable outer variable inside a lambda under `delay` (`FunDef`), and unguarded recursion (`"(Mutually) recursive call to ... must occur under delay"`).
- **Mandatory strictification (`Strictify.hs`)**: Both `Rattus` and `AsyncRattus` rewrite bindings to call-by-value strict evaluation because Haskell's default call-by-need thunks (`(((0 + x0) + x1) + ... + xk)`) would otherwise reintroduce $\Theta(k)$ space leaks inside `Stable` accumulators.

Unlike modal FRP's total, productive tick steps, mainstream `async`/`await` futures (e.g., Rust `Future` state machines) expose arbitrary compiler-generated suspension points with unmodeled implicit cancellation (`Drop` at any `.await`) and lack static space or causality bounds.

---

### 5. WCET Predictability, Microarchitectural Timing Anomalies, and Domino Effects

Basis: normative + execution + derived

Functional determinism (`Vélus`) and leak-free memory (`Rattus`) fail hard real-time requirements if any tick violates $T_{\text{exec}} \le T_{\text{tick}}$. Computing sound WCET upper bounds runs directly into undecidability and hardware non-monotonicity.

#### 5.1 Static WCET Analysis Architecture (`Wilhelm et al. 2008`, `AbsInt aiT`)

General WCET reduces to the halting problem (Wilhelm et al., ACM TECS 2008, §1). Hard real-time code restricts programs to bounded loops and bounded/absent recursion, analyzed in three phases (`AbsInt aiT`):
1. **Value & Flow Analysis**: Recovers address ranges, loop bounds, and infeasible paths (supplemented by AIS flow-fact annotations).
2. **Microarchitectural Abstract Interpretation**: Computes sound cache (`Must`/`May`/`Persistence`) and cycle-level pipeline abstract states across CFG edges.
3. **Implicit Path Enumeration Technique (IPET)**: Solves an Integer Linear Program maximizing $\sum_i c_i x_i$ subject to CFG flow conservation and loop bounds.

Testing-based measurement yields only a *lower bound* on WCET, never a sound upper bound, because worst-case inputs, initial cache/predictor states, and bus alignments rarely coincide in tests.

#### 5.2 Formal Definition and Classification of Timing Anomalies

Static WCET analysis would be compositional if hardware were **timing-monotonic** (assuming the local worst case—e.g., cache miss—always bounds global time). **Lundqvist & Stenström (RTSS 1999, Definition 1)** proved OoO processors violate monotonicity: if changing one instruction's latency by $+i$ (or $-d$) changes total execution time by $C$, a **timing anomaly** occurs whenever $C > i$ or $C < 0$ (resp. $C < -d$ or $C > 0$).

**Reineke et al. (WCET 2006, Definitions 1–7)** generalized this over an abstracted hardware transition system $T = (S, R)$ with convex micro-operation locality constraints $L$ and sequence labelling $\rho : V^* \to \mathcal{P}(L)$: a hardware model $C$ exhibits a **timing anomaly** (Definition 7) iff some program $P$, instruction sequence $\sigma$, and **non-local worst-case path** $\pi \in \Pi(T)|_\sigma^\rho$ satisfy $|\pi| > |\pi'|$ for *every* local worst-case path $\pi'$. Reineke et al. (§2, §4) distinguish three classes and document the **refutation** of Lundqvist & Stenström's original 1999 Condition 1 ("in-order resources only $\implies$ no timing anomalies"):

| Anomaly Class (Reineke et al. 2006) | Hardware Mechanism | Possible on In-Order Pipelines? | Static WCET Impact |
| --- | --- | --- | --- |
| **1. Scheduling** | OoO functional-unit / reservation-station allocation (or overlapping non-identical resources); faster completion lets an older dependent instruction seize an FU ahead of a critical-path instruction | Only with overlapping non-identical resources (Wenzel et al. 2005) | Must branch on both hit and miss ($O(k^n)$ state explosion) |
| **2. Speculation** | Branch misprediction + speculative fetch; a cache *miss* on the first mispredicted fetch stalls speculation before it pollutes the cache, whereas a *hit* evicts useful lines (Reineke et al. 2006, Fig. 2) | **Yes** (any in-order core with speculative fetch into a shared cache) | Must model wrong-path cache pollution on hits as well as misses |
| **3. Cache Replacement** | Non-LRU policies (specifically **Pseudo-Round-Robin** on the in-order **Motorola ColdFire 5307**, Thesing 2004): a miss leaves the replacement pointer in a state producing fewer future misses than a hit | **Yes** (refutes Lundqvist & Stenström 1999 Condition 1) | Breaks monotonic cache abstractions |

#### 5.3 Cycle-Accurate Verification of Timing Anomalies and Domino Effects

Executing `support/verify_constructive_causality_and_wcet.py` (Part 3) reproduces three canonical anomalies plus an in-order control:

1. **2-FU OoO Hit-Worse-Than-Miss (`A`: `4c` miss $\to$ `1c` hit increases makespan `12c` $\to$ `14c`)**:
   - Units: `FU1` (in-order), `FU2` (out-of-order, oldest-ready priority). Stream: `A` (`FU1`, disp `0`, `1c` hit / `4c` miss), `B` (`FU2`, disp `0`, `4c`, dep `A`), `C` (`FU2`, disp `1`, `1c`), `D` (`FU1`, disp `2`, `4c`, dep `C`), `E` (`FU1`, disp `3`, `4c`, dep `D`).
   - **Miss (`A=4c`)**: `A@FU1[0..4)` blocks `B`; `C@FU2[1..2)` runs OoO; `D@FU1[4..8)` and `B@FU2[4..8)` overlap; `E@FU1[8..12)`. **Makespan = `12c`.**
   - **Hit (`A=1c`)**: `A@FU1[0..1)` frees older `B` at cycle `1`, beating `C` for `FU2` (`B@FU2[1..5)`), delaying `C@FU2[5..6) -> D@FU1[6..10) -> E@FU1[10..14)`. **Makespan = `14c`** (`Δ_local = -3c`, `Δ_global = +2c`).
   - **Strict in-order control** (`FU1`, `FU2` both in-order): restores monotonicity (`hit = 14c <= miss = 17c`, `Δ_global = +3c <= +3c`).
2. **Lundqvist & Stenström (RTSS 1999, Fig. 2 — PowerPC LSU/IU/MCIU)**: `A` (`LD`, LSU, `2c` hit / `10c` miss), `B` (`ADD`, IU, `1c`, dep `A`), `C` (`ADD`, IU, `1c`), `D`/`E` (`MUL`, MCIU, `4c` each, `C -> D -> E`). Hit (`A=2c`) takes **`12c`** (`B` blocks `C` on IU at cycle 2); miss (`A=10c`) takes **`11c`** (`C` executes early on IU at cycle 2; `Δ_local = +8c`, `Δ_global = -1c`).
3. **Lundqvist & Stenström (RTSS 1999, Fig. 3 — Miss Penalty Amplification)**: `A` (`LD`, LSU, `2c`/`10c`) $\to$ `B` (`MUL`, MCIU, `4c`) $\to$ `C` (`LD`, LSU, `10c`), plus independent `D` (`MUL`, MCIU, disp cycle 9, `4c`). On `A` miss, `D` claims MCIU at `[9..13)` before `B` becomes ready at cycle 10, delaying `C`'s completion from **`16c` to `27c`** (`+11c` global delay from an `+8c` local miss!).
4. **Domino Effects (Lundqvist & Stenström RTSS 1999, Fig. 4)**: A 1-cycle initial delay to loop body instruction `A` causes prior-iteration `B` to collide with `A` on the IU in *every* iteration, adding **$+k$ cycles across $k$ iterations**—proving anomaly penalties can be unbounded in loop length and cannot be absorbed by constant per-block margins.

---

### 6. Restoring End-to-End Timing Predictability: Cost-Preserving Verified Compilation and Time-Predictable Hardware

Basis: normative + source + documentation + derived

#### 6.1 Cost-Preserving Verified Compilation and Certified Flow Facts

Mainstream compilers (`LLVM`, `GCC`) and standard `CompCert` omit quantitative execution cost from IR semantics, allowing transformations to scramble source loop bounds or worsen worst-case paths. Three verified compiler frameworks close this gap:

1. **Quantitative CompCert (`Carbonneaux, Hoffmann, Ramananandro & Shao, PLDI 2014`)**: Instruments Clight and assembly semantics with quantitative stack-allocation event traces, proves end-to-end stack-bound preservation down to x86 assembly in Coq, and pairs the compiler with a Quantitative Hoare Logic and certified stack analyzer.
2. **CerCo — Certified Complexity (`Amadio et al., FOPARA 2013`)**: Compiles C via a certified back-end that back-propagates exact machine cycle costs into concrete C source-level cost annotations, enabling source-level WCET proofs (e.g., in Frama-C) that soundly bound compiled object-code cycles on predictable targets.
3. **Verified Loop-Bound Estimation (`Blazy, Maroneze & Pichardie, VSTTE 2013`)**: Mechanizes loop-bound inference inside CompCert so certified flow facts (e.g., `aiT` AIS annotations) stay synchronized with compiled binaries without trusting unverified annotations.

#### 6.2 Time-Predictable Microarchitectures: `PRET` and `Patmos`

Time-predictable processors eliminate timing anomalies in hardware so memory, pipeline, and bus bounds compose additively:

1. **Precision Timed (`PRET`) / `FlexPRET` (`Edwards & Lee, DAC 2007`; Zimmer et al. 2014)**: Use hardware **thread-interleaved pipelines** (eliminating data hazards and branch speculation across pipeline stages), software-managed **scratchpads**, deterministic DRAM scheduling, and ISA-level **deadline instructions** (`deadi`/delay-until) making physical time an architectural semantic primitive.
2. **Patmos (`Schoeberl et al., Real-Time Systems 2018`; `t-crest/patmos@4c728149`)**: Direct inspection of the Chisel RTL at commit `4c72814972c8e19d69c987e3b29d764efb6a7d8c` verifies four timing-compositional mechanisms:
   - **In-order dual-issue 5-stage VLIW (`Patmos.scala` L66–70; `Constants.scala` L24)**: `Fetch`, `Decode`, `Execute`, `Memory`, `WriteBack` with static VLIW bundles (`PIPE_COUNT`), zero register renaming, zero reservation stations, and zero wrong-path speculation.
   - **Method Cache (`icache/MCache.scala` L18–70; `Patmos.scala` L658)**: Loads entire functions/sub-functions on call and return only, guaranteeing 1-cycle hits for every non-call/return instruction fetch and confining instruction-cache analysis to call-graph edges.
   - **Explicit Stack Cache (`stackcache/StackCache.scala` L51–85)**: Isolates stack traffic from data caches via a dedicated ring buffer controlled by compiler-emitted `sres`/`sspill`/`sfree`/`sens` instructions and a 7-state hardware FSM (`stackTopReg`, `memTopReg`).
   - **Scratchpads & Fixed-Slot TDM Bus (`Fetch.scala` L44–60; `ocp/TdmArbiter.scala` L14–80)**: Maps single-cycle `ISPM`/`DSPM` scratchpads (`0x00010000`, `Constants.scala` L60) and arbitrates multicore OCP burst memory with deterministic Time-Division Multiplexing:
     ```scala
     // t-crest/patmos@4c728149: hardware/src/main/scala/ocp/TdmArbiter.scala L19-31
     val period = cnt * (burstLen + 2)
     val slotLen = burstLen + 2
     cntReg := Mux(cntReg === (period - 1).U, 0.U, cntReg + 1.U)
     def slotTable(i: Int): UInt = { (cntReg === (i * slotLen).U).asUInt }
     ```
     Each of `cnt` cores gets a static non-work-conserving slot every `cnt * (burstLen + 2)` cycles, bounding multicore memory latency purely as a function of `cnt` and `burstLen` independent of peer-core workloads.

#### 6.3 Cross-Paradigm Comparison Matrix

| Paradigm / System | Time Model | Causality Rule | Space Guarantee | WCET / Timing Guarantee | Mechanization / TCB | Sync $\leftrightarrow$ Async Boundary |
| --- | --- | --- | --- | --- | --- | --- |
| **Esterel (Berry 1999)** | Perfect synchrony; single global tick | Kleene $K_3$ constructive (co-NP-complete) | Static finite-state registers | Bounded combinational depth; needs target WCET | Paper proofs (Draft Book v3.0) | External tick sampling |
| **Lustre / Vélus (`INRIA/velus@27ba860c`)** | Multi-rate dependent clocks (`Cbase`, `Con`) | Syntactic acyclicity (`AcyGraph`, black-box `IUIapp`) | Static nested `Obc` structs (no heap/GC) | Functional `Reacts` bisimulation only (no WCET in Coq) | Coq to CompCert Asm; unverified parser + `add_builtins_spec` | Volatile I/O `velus_world` |
| **Lingua Franca (`lf-lang/reactor-c@abbf0aaf`)** | Superdense tags $(t, m) \in \mathbb{Z}_{64} \times \mathbb{N}_{32}$ | Tarjan SCC zero-delay acyclicity (`PrecedenceGraph`) | Dynamic token queue in default C runtime | Deadlines + Ptides `STP_offset` & `STP_handler` | Unverified Java/C toolchain; TECS 2021 semantics | Physical actions + 3-valued ports |
| **Rattus / AsyncRattus (`pa-ba/*`)** | Global tick (`Rattus`) or channel-union clocks (`AsyncRattus`) | Guarded recursion + single-tick Fitch context | Zero implicit space leaks (with GHC plugin + `Strictify`) | Productivity/causality only (GHC GC pauses preclude hard WCET) | ICFP 2019/2023 + Coq (`Rattus-coq`); GHC plugin | `select` over `Delay !Clock` |
| **C + `aiT` (OoO CPU)** | Sequential / RTOS tasks | N/A | External stack analysis | Sound upper bound via abstract interp + IPET; anomaly state explosion | Commercial DO-178C tool; relies on HW model + flow facts | Interrupts analyzed externally |
| **Quant. CompCert / CerCo** | C (`Clight`) with quantitative cost traces | N/A | Coq-proved x86 stack bounds (`PLDI 2014`) | Source-level certified cycle bounds on simple cores (`CerCo`) | Coq/Matita cost preservation; HW model in TCB | Trusted FFI cost contracts |
| **PRET / Patmos (`t-crest/patmos@4c728149`)** | Hardware-enforced predictable execution | Strictly in-order / thread-interleaved | `ISPM`/`DSPM` + `StackCache` + `MCache` | Timing-compositional silicon; TDM period `cnt * (burstLen + 2)` | Chisel RTL + `platin` WCET tool (unverified synthesis) | Deterministic TDM / MMIO |

## Boundaries

- **not examined**: Continuous-time hybrid synchronous ODE/zero-crossing semantics (`Zélus`, `Simulink`, `Modelica`); commercial multicore SoC shared-L2/L3 cache partitioning, DRAM refresh/bank interference, and NoC WCET bounds beyond Patmos TDM; RTOS schedulability proofs (`Prosa`) and Rust `RTIC`; proprietary DO-178C qualification artifacts for Ansys `SCADE KCG` and `AbsInt aiT`; formal cancel-safety logics for Rust `async`/`await` futures.
- **unknown**: Whether full `-O2`/`-O3` pipelines in mainstream compilers (`LLVM`/`GCC`) can preserve tight cycle-level WCET bounds without disabling pass families or embedding target microarchitectural cost oracles; empirical worst-case interrupt-to-response latency jitter of `AsyncRattus` under GHC's stop-the-world garbage collector.
- **known not to apply**:
  - Lundqvist & Stenström's (1999) Condition 1 ("in-order resources only $\implies$ no timing anomalies") does **not** apply to in-order pipelines with speculative fetch into shared caches or non-LRU replacement policies (specifically refuted on the in-order Motorola ColdFire 5307 with Pseudo-Round-Robin replacement, Thesing 2004; Reineke et al. 2006).
  - `Vélus`'s `behavior_asm` and `behavior_asm_velus_world_trace_node_and_nothing_else` theorems (`INRIA/velus@27ba860c`) do **not** apply to physical timing or WCET bounds (`CompCert` `Asm.semantics` models functional volatile I/O traces, not execution cycles).
  - `Rattus` / `AsyncRattus` leak-freedom guarantees do **not** apply without their GHC plugins (`-fplugin=Rattus.Plugin` / `-fplugin=AsyncRattus.Plugin`) or across unstrictified lazy Haskell/FFI boundaries.
- **unsupported**:
  - `INRIA/velus@27ba860c` explicitly does not support uninitialized `pre` (`README.md` L11–12 requires initialized `0 fby e`), constructively causal syntactic cycles (`LCausality.v` demands `AcyGraph`), or cyclic feedback through a single node call (`IUIapp`).
  - `lf-lang/reactor-c@abbf0aaf` centralized RTI mode does not support tardy-message recovery via `STP_handler` (tardy messages abort, `core/federated/federate.c` L690); only decentralized Ptides mode bumps `actual_tag.microstep++` and invokes `STP_handler`.

## Evidence

All primary-source inspections and probe executions were acquired and verified on `2026-11-19`.

### Directly Inspected Upstream Repositories

| Repository | Pinned 40-Char SHA | Key Files & Line Ranges Inspected | Verified Anchors |
| --- | --- | --- | --- |
| `INRIA/velus` | `27ba860c2624ba232816591290c6c119b9ead88a` | `README.md` (L1–60), `Makefile` (L1–90), `src/Clocks.v` (L17–75), `src/Lustre/LClocking.v` (L71–138), `src/Lustre/LCausality.v` (L31–85, L580–588), `src/Velus.v` (L32–150), `src/VelusCorrectness.v` (L202–292), `src/ClightToAsm.v` (L59–222) | `pre` omitted; `clock`/`instck`; `wc_exp`; `Is_used_inst`/`AcyGraph`; `Stc.SchV.well_sch`; `Axiom add_builtins_spec`; `behavior_asm` + deterministic world corollary; submodule `inria-parkas/CompCert@22c33b91d42c7df986c97b13b6cd630866a56494` |
| `lf-lang/lingua-franca` | `0df8a987e37d6bc0cc8daa1c3e6167df14eaae59` | `README.md` (L1–40), `core/src/main/java/org/lflang/graph/PrecedenceGraph.java` (L40–100) | Polyglot targets; Tarjan SCC cycle detection & topological sorting |
| `lf-lang/reactor-c` | `abbf0aaf468af55f298e1ae4816156e9f7552784` | `tag/api/tag.h` (L56–122), `core/tag.c` (L48–95), `include/core/lf_types.h` (L72–125), `include/core/federated/federate.h` (L662–670), `core/reactor_common.c` (L215–221, L984), `core/federated/federate.c` (L419–487, L607–695, L1284–1435) | `tag_t`; saturating `NEVER`/`FOREVER` arithmetic; `port_status_t`; `lf_tag_advancement_barrier_t`; `STP_offset` wait + tardy microstep bump + `STP_handler` |
| `pa-ba/Rattus` | `f8cfe7411ccebef78f74a73e1a6a2e57a106b256` | `Rattus.cabal` (`v0.5.1.1`), `src/Rattus/Primitives.hs` (L1–106), `src/Rattus/Plugin/ScopeCheck.hs` (L1–50), `src/Rattus/Plugin/Strictify.hs` (L50–64) | Fitch-style `delay`/`adv`/`box`/`unbox` rules; `Stable` class; strictification pass |
| `pa-ba/AsyncRattus` | `8043692908bb1d1f01cd0b1ad07bca06eb9df79f` | `AsyncRattus.cabal` (`v0.2.2`), `src/AsyncRattus/Primitives.hs` (L1–19), `src/AsyncRattus/InternalPrimitives.hs` (L23–140), `src/AsyncRattus/Plugin/CheckClockCompatibility.hs` (L26–100) | `Delay !Clock`; `Select`/`select` (`✓cl(s)⊔cl(t)`); `never`; `Ctx` single-tick `earlier` & `HiddenReason` diagnostics |
| `t-crest/patmos` | `4c72814972c8e19d69c987e3b29d764efb6a7d8c` | `README.md`, `hardware/src/main/scala/patmos/{Patmos,Constants,Fetch}.scala`, `icache/MCache.scala` (L18–70), `stackcache/StackCache.scala` (L51–85), `ocp/TdmArbiter.scala` (L14–80) | 5-stage dual-issue in-order VLIW; `MCache`; `StackCache` 7-state FSM; `ISPM` (`0x00010000`); `TdmArbiter` period `cnt * (burstLen + 2)` |

### Verified Primary Literature Coordinates

Full bibliographic entries are pinned in `REPORT.json`; key primary-text verifications include:
- Berry (1999, Draft Book v3.0, 1999-07-02, CMA/INRIA) & Malik (IEEE TCAD 1994, `10.1109/43.298284`; ICCAD 1993, `10.1109/ICCAD.1993.580150`).
- Halbwachs, Caspi, Raymond & Pilaud (Proc. IEEE 1991, `10.1109/5.97300`); Bourke et al. (PLDI 2017 `10.1145/3062341.3062358`, POPL 2020 `10.1145/3371112`, EMSOFT 2023 `10.1145/3608102`).
- Lohstroh, Menard, Bateni & Lee (ACM TECS 2021, `10.1145/3448128`).
- Elliott & Hudak (ICFP 1997, `10.1145/258948.258973`); Krishnaswami, Benton & Hoffmann (POPL 2012, `10.1145/2103656.2103665`); Bahr, Graulund & Møgelberg (ICFP 2019, `10.1145/3341713`); Bahr & Møgelberg (ICFP 2023, `10.1145/3607847`).
- Lundqvist & Stenström (RTSS 1999, `10.1109/REAL.1999.818824`, full PDF inspected for Def. 1, Cond. 1, Figs. 1–4); Reineke et al. (WCET 2006, `10.4230/OASIcs.WCET.2006.671`, full PDF inspected for Defs. 1–7 and ColdFire 5307 analysis); Wilhelm et al. (ACM TECS 2008, `10.1145/1347375.1347389`, full PDF inspected).
- Carbonneaux et al. (PLDI 2014, `10.1145/2594291.2594332`); Amadio et al. (FOPARA 2013, `10.1007/978-3-319-12466-7_1`); Blazy, Maroneze & Pichardie (VSTTE 2013, `10.1007/978-3-642-54108-7_15`); Edwards & Lee (DAC 2007, `10.1145/1278480.1278545`); Schoeberl et al. (Real-Time Systems 2018, `10.1007/s11241-018-9300-4`).

### Executable Probe Verification

Executed under Python 3.10+ (stdlib only, exit code `0`):

```console
python3 -B reports/synchronous-real-time-reactive-languages-and-wcet-predictability/support/verify_constructive_causality_and_wcet.py
```

Verified outputs:
- **Part 1**: 6 constructive/classical/cyclic test cases passed (`cyclic_branch_guarded_emit`, `cyclic_with_absence_propagation`, `malik_1994_cyclic_mux_circuit` accepted; `contradictory_neg_feedback` [0 models], `self_fulfilling_ambiguous` [2 models], and `nonconstructive_tautology` [1 model] rejected as `⊥`).
- **Part 2**: 4 valid dependent clock expressions passed; 5 misaligned `when`/`merge` expressions raised `ClockError`.
- **Part 3**: 2-FU OoO anomaly (`A: 4c -> 1c` increased makespan `12c -> 14c`; in-order control `14c <= 17c`), LS99 Fig. 2 (`hit 2c = 12c > miss 10c = 11c`), and LS99 Fig. 3 (`+8c` miss $\to$ `+11c` global delay, `16c -> 27c`) all passed assertions.

## Revalidation

1. **Rerun the standalone probe** (`python3 -B reports/synchronous-real-time-reactive-languages-and-wcet-predictability/support/verify_constructive_causality_and_wcet.py`): exits `0` to re-verify Kleene $K_3$ causality, dependent clock unification, and OoO anomaly schedules (does not check upstream repo drift).
2. **Diff narrow upstream anchor files when pinned SHAs move**:
   - `INRIA/velus`: `src/Velus.v`, `src/VelusCorrectness.v`, `src/Clocks.v`, `src/Lustre/LCausality.v`, `README.md`, and the `CompCert` submodule SHA.
   - `lf-lang/lingua-franca` & `lf-lang/reactor-c`: `PrecedenceGraph.java`, `tag/api/tag.h`, `include/core/lf_types.h`, and `core/federated/federate.c` (`FEDERATED_DECENTRALIZED` / `STP_handler`).
   - `pa-ba/Rattus` & `pa-ba/AsyncRattus`: `Primitives.hs` / `InternalPrimitives.hs`, `Plugin/CheckClockCompatibility.hs`, and `Plugin/Strictify.hs`.
   - `t-crest/patmos`: `Patmos.scala`, `icache/MCache.scala`, `stackcache/StackCache.scala`, and `ocp/TdmArbiter.scala`.
3. **Full re-investigation required for new hardware**: Confirming absence of scheduling, speculation, and cache-replacement timing anomalies on a new silicon core cannot be done by a quick probe; it requires formal transition-system verification over the concrete RTL per Reineke et al. (2006).
