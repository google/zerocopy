# Path-sensitive ownership, typestate and memory analyses: what each keeps apart at control-flow joins, which branch correlations it captures, and what the precision costs (ESP, Saturn, Compass, Fink et al., access permissions, accumulation and the Resource Leak Checker, Pulse disjuncts, SafeDrop, MirChecker)

## Summary

- **The examined analyses differ in what they refuse to merge at a join.**
  - Dataflow typestate (Strom–Yemini lineage) merges everything.
  - ESP's *property simulation* merges execution states only when the property state agrees.
  - Saturn and Compass keep boolean guards, and Compass reduces them to necessary and sufficient conditions over observable variables.
  - Fink et al. stage verifiers of rising alias precision.
  - Bierhoff–Aldrich keep a linear-logic disjunction `⊕` of branch postconditions.
  - The Checker Framework Resource Leak Checker keeps separate (block, obligation-set) pairs, but intersects called-method facts at merges.
  - Pulse keeps up to `--pulse-max-disjuncts` (default 20) disjuncts per program point and drops the rest. Under its under-approximate semantics this is sound for bug finding.
  - SafeDrop enumerates paths with a fallback to a lattice join.
  - MirChecker joins numerical abstract states.

  Basis: documentation + source.
- **Published precision gains from path sensitivity are large where they were measured.**
  - Compass (PLDI 2008) cut null-dereference false positives from 1,344 to 37 on Linux 2.6.17.1, 356 → 25 on Samba and 20 → 2 on OpenSSH. Its baseline was intraprocedurally but not interprocedurally path-sensitive.
  - Fink et al.'s most precise verifier proved 93% of 4,878 potential failure points, against 30% for the flow-insensitive stage.
  - ESP verified all 646 `fprintf` calls in gcc (140,000 LOC) at 72.9 s and 49.7 MB average per file handle. It reports no measured comparison with path-insensitive analysis on gcc.

  Basis: documentation.
- **On a shared correlated-branch benchmark, the two runnable tools disagree in the direction their designs predict.**
  - The Resource Leak Checker (Checker Framework 4.4.0) reported 3 false positives on 4 safe correlated-close methods. It accepted the straight-line one and found the real leak.
  - Infer Pulse (release v1.3.0) reported none of the safe methods and found the leak.
  - On C, Pulse reported no false positive on any correlated-safe program at any bound from 1 to 256. It *missed* a reachable leak at bounds 1–2, and a parameter-dependent double free at bounds 1–2, finding them at ≥ 4.

  Basis: execution.
- **Not every Pulse miss is caused by the disjunct bound.** In two-branch programs whose conditions come from an unknown function, Pulse v1.3.0 reported the double free on the all-then and all-else paths. It never reported it on the two mixed paths, even at bound 256, while Infer's log showed `pulse_disjuncts_dropped= 0`. The cause was not established. The paper's latent/manifest distinction is a candidate but unverified explanation. Basis: execution.
- **Accumulation is the exact boundary for alias-free soundness.** Kellogg et al. (ECOOP 2022) prove (Theorem 9) that "A typestate system … is an accumulation typestate system if and only if there exists a typestate analysis with no aliasing information that can soundly check" it. 555 of 1,355 surveyed typestate specifications (41%) are accumulation. The Resource Leak Checker paper reports 49 leaks and 121 false positives over 427,858 LoC, with 286 annotations, and 100% recall against 13% (Eclipse) and 7% (Grapple). Basis: documentation.

## Applicability

The report compares independent analyses; it does not study their combination. Executed subjects:
- the Infer release `v1.3.0` Linux binary (`infer-linux-x86_64-v1.3.0.tar.xz`, SHA-256 `02be62ba931cb43e2d42bbf7abf4bd9a410cf8464cce5453934e25c90a825850`), whose tag points at the commit pinned in `REPORT.json`;
- the Checker Framework release `4.4.0` (`checker-framework-4.4.0.zip`, SHA-256 `8205c76033b2c2d21cd3fe800fff8b2a22a3ff552ec0fe7672638621e54bd8a2`), whose tag points at its pinned commit.

Source was read at each project's pinned HEAD revision and, where stated, at the release commit. `infer/src/absint/AbstractInterpreter.ml` lines 209–300 are identical at the v1.3.0 commit and at HEAD. `pulse-max-disjuncts` defaults to 20 in both (`Config.ml` line 2470 at v1.3.0, line 2504 at HEAD). The Resource Leak Checker's `MustCallConsistencyAnalyzer.java` differs between 4.4.0 (2,605 lines) and HEAD (2,716 lines). The structures quoted below occur in both, at the line numbers given for each.

SafeDrop (inside `Artisan-Lab/RAPx`) and MirChecker (`lizhuohua/rust-mir-checker`) were read at source only. They need specific nightly Rust toolchains with `rustc-dev`; MirChecker pins `nightly-2020-12-29`. The RAPx SafeDrop at the pinned revision is a re-implementation built on a path enumerator and a symbolic VM. It is not the code evaluated in the SafeDrop paper.

Execution host: x86-64 Linux 7.1.6, 96-core Intel Xeon @ 2.60 GHz, OpenJDK 25.0.5.1 (with `javac --release 11` for Infer's Java capture), and Infer's bundled clang. The benchmark programs are self-written (`support/c`, `support/java`). Their results characterise the tools on these inputs only.

## Findings

### 1. Merge rules at joins and the correlations each captures

| Analysis | Abstract path information | Merge at a join | Captures | Misses (documented or observed) |
|---|---|---|---|---|
| Typestate dataflow (Strom–Yemini) | Typestate per variable in a lattice | Meet (glb) of typestates. This comes from a secondary source; the paper's full text was not examined | Nothing path-specific | Any correlation |
| ESP property simulation | Pairs ⟨property state, execution state⟩; constant propagation as the execution domain | "if two symbolic states have the same property state, produce a single symbolic state by merging their execution states … Otherwise, process the symbolic states independently" | A branch whose arms drive the FSM to different states, and conditions of the form `x == c` | Fig. 7(a): "because neither branch of the first conditional changes the property state, the correlation between dump and flag is lost". Context-insensitive execution states needed function cloning in gcc |
| Saturn (POPL 2005 tool; numbers from CAV 2005 and thesis) | Bit-level boolean guards on every statement; BDD guard names at merges | Multiplexer of predecessor environments under guards (`MergeScalar`) | Bit-exact correlations within a function; summaries across calls | Loops unrolled (lock checker: "a maximum of two iterations"), so unsound by design |
| Compass (Dillig et al.) | Exact recursive constraints, reduced to strongest necessary / weakest sufficient conditions over observables | Disjunction of guards; unobservables eliminated by `φ[true/v] ∨ φ[false/v]` | Interprocedural correlations through observable variables | Completeness only for finite base domains |
| Fink et al. staged typestate | Per-object tuples ⟨o, unique, typestate, APmust, May, APmustNot⟩ | Per verifier stage; each stage is a filter for the next | Aliasing via must/must-not access paths | 7.5% of points remain warnings (365/4,878) |
| Bierhoff–Aldrich permissions | Linear-logic permissions (unique/full/share/pure/immutable, fractions) with state guarantees | `P-IF` yields `P1 ⊕ P2` (disjunction), not a lattice join | Correlation held in the disjunction while permissions are retained | No loops in the core language; annotation counts not reported |
| Resource Leak Checker | Must-alias sets of owned resources (Obligations); called methods from an accumulation checker | Worklist over distinct `BlockWithObligations`. Called-methods LUB is **set intersection** | Correlations that change *which resources are tracked* | Correlations that only change *which methods were called*, as in the measured false positives |
| Pulse (Infer) | List of disjuncts (under-approximate symbolic heaps with path conditions) | `join_up_to` keeps at most `limit` disjuncts, "Favors keeping states in [lhs]"; extra disjuncts are dropped | All correlations within the kept disjuncts | Paths beyond the limit, and (observed) some mixed-polarity paths whose cause is unknown |
| SafeDrop (paper, arXiv v2) | Meet-over-paths on a Tarjan-condensed spanning tree | Path enumeration; past "a large threshold value … SafeDrop will perform the traditional semi-lattice scheme" | Correlations along enumerated paths | Paths beyond the threshold |
| SafeDrop (RAPx source, pinned) | `PathTree` from a path enumerator; one `VmExecutor` (Z3 context) per path | No join across paths; enumeration is capped (`PATH_LIMIT = 256`, depth 256, SCC caps, `MAX_AUTO_REPEAT = 8`, `TRAIT_IMPL_LIMIT = 1`) | Per-path correlations, checked symbolically | Truncated paths and unrolls; the checker does not consult `is_truncated()` |
| MirChecker | Apron numerical domain (default interval) + symbolic memory | Join over all predecessors; branch exit conditions added as edge constraints before the join | Relational domains (octagon, polyhedra) keep linear correlations | Interval domain loses relations; FP rate "around 95.1%" (79.2% excluding two crates) |

Basis: documentation (papers) + source (Infer, Checker Framework, RAPx, MirChecker).

**1.1 Infer Pulse: the disjunct bound (source, pinned HEAD; identical region at v1.3.0).**
- **The option.** `infer/src/base/Config.ml` lines 2504–2507:

  ```ocaml
  and pulse_max_disjuncts =
    CLOpt.mk_int ~long:"pulse-max-disjuncts" ~default:20
      ~in_help:InferCommand.[(Analyze, manual_pulse)]
      "Stop exploring new paths after $(i,int) disjunctions in the domain"
  ```

  Lines 3027–3030 define `pulse-widen-threshold` (default 3, "Stop exploring new paths after $(i,int) loop iterations"). Lines 2785–2788 define `pulse-report-latent-issues` (default true, "when the latent issue itself is enabled").
- **Wiring into Pulse.** `infer/src/pulse/Pulse.ml` lines 1716–1719 set `join_policy = TransferFunctions.UnderApproximateAfter Config.pulse_max_disjuncts` and `widen_policy = TransferFunctions.UnderApproximateAfterNumIterations Config.pulse_widen_threshold`.
- **The capped join.** `infer/src/absint/AbstractInterpreter.ml` lines 274–284 (`join_up_to_with_leq`) are documented as "Ignore states in [lhs] that are over-approximated in [rhs] … Favors keeping states in [lhs]. Returns no more than [limit] disjuncts."
- **Dropped disjuncts.** These are counted (`DisjunctiveMetadata.dropped_disjuncts`, "how many disjuncts were discarded due to hitting the max disjuncts limit", lines 171–207). They are passed to `remember_dropped_disjuncts`, which folds them into the non-disjunctive state (`Pulse.ml` line 1690).
- **Loops.** `widen` stops after `max_iter` and increments `interrupted_loops` (lines 325–342).

The Pulse-X paper (Le et al. 2022) gives the rationale: "we simply cut after a certain number of loop iterations or paths are explored. This under-approximation is sound in Incorrectness Logic". It also gives a measured cost: an OpenSSL bug "only reachable after 20 conditional statements and 2 loops, and thus the disjunct limit was hit before that bug could be found". The paper names the `width`/`unrollings` parameters but gives no numeric values. The default of 20 is a fact about the open-source tool, not about the paper's configuration.

**1.2 Resource Leak Checker: path-separated obligations, intersected called methods (source).**
- **Worklist.** At HEAD, `MustCallConsistencyAnalyzer.java` `analyze` keeps `Set<BlockWithObligations> visited` (line 674). `BlockWithObligations.equals` compares `block.equals(that.block) && obligations.equals(that.obligations)` (line 2669). Two distinct obligation sets reaching one block are analysed separately.
- **The exit check.** It uses the called-methods store *after the last node of the block* (`cmStore = cmAtf.getStoreAfter(last);`, line 2235; `checkMustCall(obligation, cmStore, mcStore, …)`, line 2256). That store is computed by the Called Methods dataflow, whose least upper bound is intersection. `framework/.../accumulation/AccumulationAnnotatedTypeFactory.java` lines 462–505: "LUB in this type system is set intersection of the arguments of the two annotations, unless one of them is bottom", implemented by `a1Val.retainAll(a2Val); // intersection`.
- **Line numbers at 4.4.0.** The same anchors are at lines 592, 2558, 2156 and 2177.
- **Consequence (derived).** After `if (b) f.close();` the called-methods set for `f` at the join is `{close} ∩ {} = {}`, whatever the later branches do. The measured false positives in §3 follow.
- **Soundness of the design.** The class Javadoc states that the tracked Obligations over-approximate "the actual set of resources in the analyzed program with must-call obligations".

**1.3 SafeDrop and MirChecker (source).**
- **RAPx SafeDrop.** `rapx/src/check/safedrop.rs` (47 lines) obtains `path_analyzer.get_fn_paths(def_id)` and calls `vm::analyze`. `rapx/src/check/safedrop/vm.rs` lines 12–18 create one Z3 `Config`/`Context` and, `for path in paths.to_vecs()`, a fresh `VmExecutor`. The limits are centralised in `rapx/src/limit.rs`: `PATH_LIMIT: usize = 256` (line 21), `WHOLE_CFG_PATH_DEPTH_LIMIT = 256` (27), `SCC_MAX_DEPTH = 128` (33), `SCC_MAX_SEEN_PATHS = 128` (36) and `SCC_MAX_PATH_LEN = 200` (39). The file also documents `TRAIT_IMPL_LIMIT = 1` ("truncated to the first `n` (an under-approximation)", lines 58–61) and `MAX_AUTO_REPEAT = 8` ("bugs that only manifest after more iterations can be missed", lines 67–71). `PathTree` has a `truncated` flag "Set when enumeration stopped at a path or depth limit" (`rapx/src/analysis/path.rs` lines 71–73), set in `rapx/src/analysis/path/graph.rs` lines 2097–2124. The SafeDrop checker files do not reference `is_truncated()`.
- **MirChecker.** `src/analysis/option.rs` lines 35–38 set the defaults `domain_type: AbstractDomainType::Interval`, `widening_delay: 5` and `narrowing_iteration: 5`. `src/analysis/mir_visitor/body_visitor.rs` lines 913–945 (`get_state_from_predecessors`) add each predecessor's exit condition as linear constraints and then "Merge states using the join operator". `src/analysis/abstract_domain.rs` lines 168–176 define `join` as the numerical join plus the symbolic least upper bound. `src/analysis/memory/k_limits.rs` (adapted from MIRAI) caps `MAX_PATH_LENGTH = 30` and `MAX_REFINE_DEPTH = 9`.

Basis: source.

### 2. Published precision and cost

| Work | Benchmark / scale | Precision result | Cost | Notes |
|---|---|---|---|---|
| ESP (PLDI 2002) | gcc (SPEC95), 140,000 LOC, 2,149 functions; 15 file handles | All 646 `fprintf` calls verified | 72.9 s and 49.7 MB average, 170 s and 102 MB maximum per file handle; 1 GHz Pentium III. CFG construction excluded | Only one program; no measured comparison against dataflow or full path-sensitivity. Required hand-modelling one function and cloning three |
| Saturn lock checker (CAV 2005; thesis tables) | Linux 2.6.5, about 4.8 MLOC, 63,850 functions | 300 warnings, 179 bugs, 121 false positives (60% bug/warning) | 19h40m CPU; 67 LOC/s; 700 MB / 90 s per-function limits; 3.0 GHz Pentium IV | The POPL 2005 text itself was not examined |
| Saturn leak checker (FSE 2005) | 5 user-space programs (1.78 MLOC) and Linux 2.6.10 (5.04 MLOC) | User space 373 bugs / 14 FP (3.62%); Linux 82 bugs / 41 FP (33%); overall 10.8% FP | 12h46m single CPU (user space), 23h13m Linux; 50m34s on about 80 CPUs | FP% = FP/(bugs+FP) (derived check) |
| Compass (PLDI 2008) | Linux 2.6.17.1 (6,275,017 LOC), Samba (515,689), OpenSSH (155,660) | Null-dereference FP 37 / 25 / 2 vs 1,344 / 356 / 20 with the interprocedurally path-insensitive baseline; bugs 134 / 17 / 1 in both | "tens of minutes … up to more than ten hours" on 10–30 cores; memory not reported | Average necessary/sufficient condition sizes 0.45–2.82 connectives |
| Fink et al. (TOSEM 2008) | 17 Java benchmarks, 2,169,127 bytecode statements, 4,878 points | Verified share: FI 30%, LocalFocus 64%, Base 68%, Unique 72%, APMust 85%, APFocus 93% | Staged beats APFocus on 9 of 10 codes taking > 30 s (median −34%, up to −85%), +40% on l2j; "under 10 minutes" overall; 800 MB max heap | Per-stage times only as a bar chart |
| Bierhoff–Aldrich (OOPSLA 2007) | Java iterators and streams | Found a `BufferedInputStream` invariant break | not reported | Annotation counts not reported |
| Resource Leak Checker (FSE 2021, corrected author copy) | ZooKeeper, HDFS, HBase, plume-util; 427,858 LoC | 49 leaks, 121 FP; recall 100% vs Eclipse 13%, Grapple 7%; precision 26% vs 25% and 50% | 1m24s / 16m21s / 7m45s / 15s vs Grapple 1h07m / 1h54m / 33h51m (Grapple times from its authors) | 286 annotations (about 1 per 1,500 LoC). Ablations: FP 300 without lightweight ownership, 446 without resource aliasing |
| Accumulation (ECOOP 2022) | Literature survey | 41% of specifications are accumulation | No new timings; "often by an order of magnitude or more" cheaper (qualitative) | Decision procedure `O(max(n log n, en))` |
| Pulse-X (OOPSLA 2022) | OpenSSL 1.0.1h (2.83 MB of IR, 8,658 procedures); 10 programs | 26 reported, 19 fixed (73%) vs present-day Infer 39/80 (49%) | 4 min (OpenSSL 1.0.1h), 16 min (3.0.0); 4–900 min across 10 programs; 24-core machine | 306 issues found, 26 reported, by the manifest filter |
| SafeDrop (arXiv v2) | Known CVEs + 8 crates with new findings | All known bugs detected in its experiments | Compile-time overhead 1.0%–110.7% (abstract) | TOSEM version not examined |
| MirChecker (CCS 2021) | 12 crates | 33 bugs (16 memory-safety) | 10.56–11,315.82 CPU s; 126.47–923.61 MB peak | FP "around 95.1%" / 79.2% |

Basis: documentation. All values are quoted from the papers as read; see **Evidence** for versions and labels.

### 3. Shared correlated-branch benchmark (execution, real tools)

**3.1 Java (`support/java/Corr.java`, `support/run_java.sh`).**

| Method | Ground truth | Resource Leak Checker 4.4.0 | Pulse v1.3.0 |
|---|---|---|---|
| `corrCloseSafe`: open; `if (b) close; if (!b) close` | safe | `required.method.not.called` (line 10): **FP** | no report |
| `flagCloseSafe`: open; `if (b) {close; closed = true}`; `if (!closed) close` | safe | report (line 17): **FP** | no report |
| `corrOpenSafe`: `if (b) open; if (b) close` | safe | report (line 26): **FP** | no report |
| `plainSafe`: open; close | safe | no report | no report |
| `leakBug`: open; `if (b) close` | leak | report (line 38): TP | `PULSE_RESOURCE_LEAK` (line 39): TP |
| Wall time / peak RSS (whole run) | — | 3.06 s / 289,928 KiB | 3.24 s / 307,092 KiB (includes `javac` capture) |

The FPs are the outcome predicted by §1.2: the obligation persists while the called-methods fact is intersected away at the first join. Pulse keeps the `b`/`¬b` disjuncts apart. Basis: execution + source.

**3.2 C, Pulse bound sweep (`support/c/*.c`, `support/run_infer_c.sh`).** Each file was analysed with `infer run --pulse-only --pulse-max-disjuncts d -- clang -c f.c` for d ∈ {1, 2, 4, 8, 16, 20, 64, 256}. 160 runs took 0.20–0.51 s wall each (median 0.24 s), with 179,404–185,000 KiB peak RSS. "dropped" is the last `pulse_disjuncts_dropped=` value in Infer's log. Full output: `support/output/infer_pulse_c_sweep.txt`.

| Program (bug path) | Ground truth | Reported at bounds | Not reported at bounds | dropped at d ≥ 8 |
|---|---|---|---|---|
| `corr_free`, `corr_null`, `corr_flag` (correlated safe) | safe | — | all | 0 |
| `uaf_bug` (use after free when `b`) | bug | all | — | 0 |
| `leak_bug` (leak when `!b`) | bug | ≥ 4 | 1, 2 | 0 |
| `param2_one` (double free when exactly one parameter is non-zero) | bug | ≥ 2 | 1 | 0 |
| `param2_ft` (parameters `c0 = 0`, `c1 ≠ 0`) | bug | ≥ 4 | 1, 2 (dropped 2 and 3) | 0 |
| `param2_false` (both parameters zero) | bug | — | all | 0 |
| `nd2_tt`, `ndtrue_{2,6,10}` (all conditions from `nondet()` true) | bug | all | — | 0 |
| `nd2_ff`, `ndfalse_{2,6,10}` (all false; up to 1 of 1,024 paths) | bug | ≥ 2 | 1 | 0 |
| `nd2_tf`, `nd2_ft`, `ndmixed_{4,10}` (mixed polarity from `nondet()`) | bug | — | **all, including 256** | **0** |

What this shows (derived):
- **Bound-induced false negatives.** The correlated-safe programs never produced a false positive. The bound produced false negatives at d ≤ 2 for `leak_bug` and `param2_ft`, and these disappeared by d = 4. This is the documented cost of under-approximate bounding, observed on a two-branch program.
- **Join order matters.** The kept disjuncts are not a random sample. All-then paths survive even d = 1, and all-else paths survive d = 2 for 10 consecutive branches, consistent with "Favors keeping states in [lhs]".
- **Misses not attributable to the bound.** Mixed-polarity paths over `nondet()` results were never reported, and the log shows 0 dropped disjuncts at d ≥ 4. The equivalent parameter program (`param2_ft`) *was* reported at d ≥ 4. Conversely, `param2_false` was never reported, while the analogous `nd2_ff` was. Whether these are classification effects (manifest vs latent; the paper says Pulse-X "only report[s] bugs to developers if they are manifest") or analysis effects is **unknown**. `--pulse-report-issues-for-tests` ("Do not suppress any of the issues found by Pulse") did not change the `param2_false` or `nd2_ft` results in separate runs at the default bound.

Basis: execution.

### 4. Which protocols can skip alias analysis (accumulation)

Definitions from Kellogg et al. 2022:
- An *error-inducing sequence* drives the automaton into the error state for the first time.
- An *accumulation typestate system* is one in which "for any error-inducing sequence S = t1,…,ti, all subsequences … of S that end in ti also result in the typestate automaton being in the error typestate".

Results:
- Theorem 9 gives the if-and-only-if with "a typestate analysis with no aliasing information", meaning MustOracle and MayOracle return empty lists. Corollary 10: "An accumulation analysis, even without aliasing information, is sound."
- **Not accumulation.** "'disable x after y' properties … are never accumulation typestate systems". Resource release ("call `close` before the last reference dies") is accumulation. "Do not use after close" is not.
- **Decision procedure.** `O(max(n log n, en))` for n states and e edges.
- **Consequence for design (derived).** An ownership checker that needs only "every owned resource eventually receives its release call" can drop alias analysis and stay modular, as the RLC does. Every "no use after release" or "no double release" obligation needs aliasing or ownership information, because those are disable-after properties. That is the class SafeDrop, MirChecker and Pulse's use-after-free checks address with path-sensitive heap reasoning.

Basis: documentation + derived.

### 5. Performance and resource footprint (L1–L6)

Every cell is measured (host in **Applicability**), cited, derived, or `not measured`.

| Subject | L1 authoring / annotation / code size | L2 toolchain build | L3 analysis latency | L4 runtime effect | L5 checking of results | L6 memory / size |
|---|---|---|---|---|---|---|
| ESP | not measured | not measured | 72.9 s average, 170 s maximum per handle (cited) | n/a (static) | n/a | 49.7 / 102 MB (cited) |
| Saturn | Saturn about 25% of comparable BLAST code (cited, thesis) | not measured | 67 LOC/s lock checker; 39 LOC/s (user-space) leak checker (cited) | n/a | n/a | 700 MB per-function cap (cited) |
| Compass | not measured | not measured | tens of minutes to more than 10 h on 10–30 cores (cited) | n/a | n/a | not reported |
| Fink et al. | implementation about 200,000 lines of Java (cited) | not measured | under 10 min suite (cited) | n/a | n/a | 800 MB max heap setting (cited) |
| Bierhoff–Aldrich | annotation counts not reported | not measured | not reported | n/a | n/a | not reported |
| Resource Leak Checker | 286 annotations / 427,858 LoC, about 1 per 1,500 (cited); `MustCallConsistencyAnalyzer.java` 2,716 lines at HEAD, 2,605 at 4.4.0 (measured) | release zip 35,027,417 bytes (measured); build not measured | 15 s–16m21s per project (cited); 3.06 s on `Corr.java` (measured) | n/a | n/a | 289,928 KiB on `Corr.java` (measured) |
| Pulse | `AbstractInterpreter.ml` 963 lines, `Pulse.ml` 2,101 lines at HEAD (measured) | release tarball 275,901,768 bytes (measured); source build not measured | 4–900 min across 10 programs (cited); 0.20–0.51 s per C file here (measured) | n/a | n/a | 179,404–185,000 KiB per C file; 307,092 KiB Java (measured) |
| SafeDrop | RAPx `vm.rs` 150 lines, `path.rs` 431, `path/graph.rs` 2,257 (measured) | not measured | compile overhead 1.0%–110.7% (cited, arXiv v2) | n/a | n/a | not measured |
| MirChecker | 11,927 LOC Rust (cited) | not measured | 10.56–11,315.82 CPU s (cited) | n/a | n/a | 126.47–923.61 MB (cited) |

### 6. Human comprehensibility and conceptual simplicity (C1–C2)

- **What a user must hold in mind to predict a verdict (C1, derived).**
  - RLC: 3 concepts (owning references, must-call obligations, called-methods sets with an intersecting join). The FP explanation is local: "the close on this branch is forgotten at the join".
  - Pulse: 4 (disjunct list, limit and join order, manifest vs latent classification, widening threshold). Its false negatives are silent, and the only signal is a log counter.
  - Compass: 2 (necessary and sufficient conditions); the conditions themselves are machine-sized.
  - Bierhoff–Aldrich: 5 permission kinds plus fractions and state guarantees.
- **Diagnostic legibility (C1).** RLC reports a definite error that can be suppressed with an annotation. Pulse reports only what survives both the bound and the manifest filter. A missing report can mean "safe", "dropped by the bound" or "latent", and the user cannot tell which without the log.
- **Minimal universal abstraction (C2).** Property simulation is the unifying shape: group symbolic states by the *property-relevant* component and merge the rest. RLC's obligation-set keying is property simulation over *which resources are tracked*. Its called-methods merge is not, which is the source of the measured FPs. Pulse's disjunct list is property simulation with an identity grouping and a cap. Extending RLC's keying to include accumulated called methods would turn its FPs into separate worklist items, at the cost of more items per block. This is a derived design option, not implemented or measured.
- **Hidden complexity (C2).** Path caps (Pulse 20 disjuncts and 3 iterations; RAPx 256 paths, 8 unrolls, 1 trait impl; MirChecker k-limits; Saturn 2 unrolls) are encodings of soundness decisions as numeric constants. They make an analysis's guarantee configuration-relative.

### 7. How implementations and claims are validated (V1–V4)

- **V1: specification adequacy.**
  - RLC paper ablations (FP rises to 300 without lightweight ownership and 446 without resource aliasing) validate that each mechanism carries weight.
  - Accumulation's decision procedure classifies specifications mechanically.
  - The benchmark in §3 is a cheap differential oracle across tools on the same programs.
- **V2: checker soundness.**
  - Pulse's soundness argument is Incorrectness Logic's under-approximation theorem. Its "True Positives Property" holds for manifest errors in complete programs.
  - RLC's soundness rests on Theorem 9 and Corollary 10 over a core calculus. The implementation's soundness was validated by case studies, not by a proof.
  - No fuzzing of these analysers against reference semantics was examined.
- **V3: concurrency and physical effects.** n/a: all analyses here are sequential.
- **V4: human factors.**
  - Fix rates are used as a proxy for usefulness to engineers: Pulse-X 73%; the deployed Pulse "fix rate over 80%"; Saturn's bugs filed to LKML with confirmations (no count).
  - No controlled study of user comprehension was examined.

## Boundaries

- **Not examined:**
  - the full texts of Strom–Yemini 1986 (merge rule from secondary sources) and of the Saturn POPL 2005 paper (numbers from the CAV 2005 tool paper and the 2006 thesis);
  - the SafeDrop TOSEM 2023 full text (numbers from arXiv v2);
  - the Pulse-X artifact, including the numeric `width`/`unrollings` used;
  - running SafeDrop, RAPx or MirChecker;
  - building Infer or the Checker Framework from source;
  - Rust inputs for the correlated-branch benchmark.
- **Unknown:**
  - why Pulse v1.3.0 does not report mixed-polarity paths over unknown-call results (§3.2);
  - whether the HEAD revision behaves differently from v1.3.0 on the benchmark;
  - per-stage times in Fink et al. (bar chart only).
- **Known not to apply:**
  - The RAPx SafeDrop source is not the implementation evaluated in the SafeDrop paper, so the paper's numbers do not describe it.
  - The Infer defaults quoted are not necessarily the Pulse-X paper's configuration.
- **Unsupported:**
  - RLC does not check "no use after close" (not accumulation).
  - MirChecker's interval default cannot represent relations.
- **Attractive stronger conclusions not established:**
  - that Pulse has no false positives in general (only on these programs);
  - that RLC's FP rate on real code is driven by correlated branches (its paper attributes FPs to several causes, and §3 shows only the mechanism);
  - that raising `--pulse-max-disjuncts` makes Pulse complete (the mixed-polarity misses persist at 256);
  - that ESP is more precise than dataflow *as measured* (the paper gives only worked examples).

## Evidence

Observation date for all evidence: 2026-11-21 (UTC). Pinned revisions are in `REPORT.json`.

- **Infer:**
  - HEAD `facebook/infer` @ `2ebceff7ce3c93480bbc0e8d09d11aeec53595d8`: `infer/src/base/Config.ml` lines 2504–2507, 2785–2788, 3027–3030; `infer/src/pulse/Pulse.ml` lines 1690, 1716–1719; `infer/src/absint/AbstractInterpreter.ml` lines 171–207, 209–300, 325–342, 367–392.
  - Release tag `v1.3.0` → `410a6d9394b9c9794bf9469ee0e1aa8d3ae91031`: `Config.ml` lines 2470–2473; `AbstractInterpreter.ml` lines 209–300 identical to HEAD (diffed).
- **Checker Framework:**
  - HEAD `typetools/checker-framework` @ `dda43ee4bda793c37f869e0d1cc8f017ed6b0763`: `checker/src/main/java/org/checkerframework/checker/resourceleak/MustCallConsistencyAnalyzer.java` lines 93–147 (class Javadoc), 669–687, 2190–2256, 2640–2669; `framework/src/main/java/org/checkerframework/common/accumulation/AccumulationAnnotatedTypeFactory.java` lines 462–505.
  - Release tag `checker-framework-4.4.0` → `160337829f7bf7ecce26e6cebf3816f1549a57ab`: the same anchors at lines 592, 2156, 2177, 2529, 2558.
- **RAPx** (`Artisan-Lab/RAPx` @ `9f6ec20c48694037fc3835cd15bdc9791f4d027c`): `rapx/src/check/safedrop.rs`, `rapx/src/check/safedrop/vm.rs` lines 12–48, `rapx/src/limit.rs` lines 18–80, `rapx/src/analysis/path.rs` lines 55–76 and 124–145, `rapx/src/analysis/path/graph.rs` lines 2097–2124, `rust-toolchain.toml`.
- **MirChecker** (`lizhuohua/rust-mir-checker` @ `2a8c4632902497fc92b9b61f7fa5c4d4f52f578e`): `rust-toolchain.toml` (`nightly-2020-12-29`), `src/analysis/option.rs` lines 30–44, `src/analysis/abstract_domain.rs` lines 168–212, `src/analysis/mir_visitor/body_visitor.rs` lines 913–945, `src/analysis/memory/k_limits.rs`.
- **Execution artefacts** (text, in `support/`):
  - `c/*.c`, `java/Corr.java`, `run_infer_c.sh`, `run_java.sh`;
  - `output/infer_pulse_c_sweep.txt`, `output/infer_pulse_corr_java.txt`, `output/rlc_corr_java.txt`.

  Release archive SHA-256 values are in **Applicability**.
- **Literature** (DOIs verified against Crossref, or DataCite for LIPIcs, on 2026-11-21; version read in brackets):
  - Strom–Yemini, IEEE TSE SE-12(1):157–171, 1986, 10.1109/TSE.1986.6312929 [abstract + secondary].
  - Das–Lerner–Seigle, PLDI 2002, 10.1145/512529.512538 [full text].
  - Xie–Aiken, POPL 2005, 10.1145/1040305.1040334 [not examined; CAV 2005 tool paper and 2006 thesis used].
  - Xie–Aiken, ESEC/FSE 2005, 10.1145/1081706.1081728 [full text].
  - Bierhoff–Aldrich, OOPSLA 2007, 10.1145/1297027.1297050 [full text].
  - Dillig–Dillig–Aiken, PLDI 2008, 10.1145/1375581.1375615 [full text].
  - Fink et al., TOSEM 17(2), 2008, 10.1145/1348250.1348255 [full text].
  - Kellogg et al., ESEC/FSE 2021, 10.1145/3468264.3468576 [corrected author copy].
  - Li et al., CCS 2021, 10.1145/3460120.3484541 [full text].
  - Kellogg et al., ECOOP 2022, LIPIcs 222, 10.4230/LIPIcs.ECOOP.2022.10 [full text; DataCite].
  - Le et al., PACMPL 6(OOPSLA1), Article 81, 2022, 10.1145/3527325 [full text].
  - Cui et al., TOSEM 32(4), 2023, 10.1145/3542948 [abstract; numbers from arXiv:2103.15420v2].
- **Source facts vs. synthesis.** The tables in §1, §6 and the "derived" items are this report's synthesis. The quoted source lines and the tool outputs are the source facts.

## Revalidation

- **Pulse bound behaviour.** Run `support/run_infer_c.sh <infer> <dir>` with a new Infer. The discriminating rows are:
  - `leak_bug` and `param2_ft` (missed at d ≤ 2, found at d ≥ 4);
  - `nd2_ft`/`nd2_tf` (never found, 0 dropped);
  - the correlated-safe files (never reported).

  For the source, diff `join_up_to_with_leq` in `infer/src/absint/AbstractInterpreter.ml` and the `pulse_max_disjuncts` default in `Config.ml`.
- **RLC merge behaviour.** Run `support/run_java.sh <cf-dir> <infer> <dir>`. If `corrCloseSafe`, `flagCloseSafe` or `corrOpenSafe` stop being reported, check `BlockWithObligations` keying and `leastUpperBoundQualifiers` in `AccumulationAnnotatedTypeFactory.java` for a changed merge.
- **SafeDrop.** Grep `rapx/src/limit.rs` for the constants, and `rapx/src/check/safedrop/vm.rs` for `is_truncated`.
- **MirChecker.** Check `src/analysis/option.rs` defaults and `get_state_from_predecessors`.
- **Literature numbers.** These are fixed for the cited versions. Re-verify the DOIs through the Crossref and DataCite APIs. Before citing SafeDrop or Saturn POPL numbers as journal or POPL figures, re-examine those versions.
