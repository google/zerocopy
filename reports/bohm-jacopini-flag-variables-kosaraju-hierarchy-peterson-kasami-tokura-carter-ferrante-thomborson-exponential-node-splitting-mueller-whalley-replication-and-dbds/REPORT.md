# Code duplication versus run-time state for control-dependent decisions: auxiliary-variable structuring theorems, the exponential node-splitting lower bound, replication and simulation-based duplication, and the duplication budgets of LLVM and GCC

## Summary

- **The exchange.** A decision that depends on which path was taken can be made static by duplicating the code after the join, or it can be kept dynamic in a flag or selector variable that the join tests.
- **Structuring theorems.** Böhm–Jacopini (1966) make every flow diagram structured by adding a stack of auxiliary Boolean bits. Peterson–Kasami–Tokura (1973) show that if/repeat with *multi-level* exit expresses exactly the well-formed programs, that single-level exit does not suffice, and that any flowchart becomes well-formed by node splitting. A secondary source credits Kosaraju (1973/1974) with two results: no added variables are needed if breaks of arbitrary depth are allowed, and break depth forms a strict hierarchy.
- **Lower bound.** Carter–Ferrante–Thomborson (2003) prove that any reducible flow graph equivalent to the complete graph on n nodes has at least 2^(n−1) nodes. So without predicate variables, exponential duplication is unavoidable. They state explicitly that the result does not apply to adding predicate variables.
- **Selector variables.** LLVM's `FixIrreducible` routes the irreducible cycle through a hub of guard blocks that test N−1 Boolean predicates (or one integer). On the complete graph K_n (n = 3…10) it added n−2 guard blocks and n−2 `i1` phis, and grew machine code by 11–33% (136→168 bytes at n=3, 1000→1301 bytes at n=10), against the 2^(n−1)-node bound for predicate-free reducible equivalents.
- **Reported duplication costs.**
  - Straightforward node splitting: +235% code per procedure (+13.6% per program), against +3% (+0.2%) with controlled node splitting.
  - Hot-path duplication for data-flow analysis: +3–32% graph size, +1–7% after reduction, with one benchmark at +184%/+70%.
  - Dominance-based duplication simulation: up to 40% peak performance, mean +5.89%, at mean +9.93% code size and +18.44% compile time.
- **Production budgets.**
  - LLVM bounds tail duplication by instruction count (2; 4 at `-O3` for layout; 1 when optimizing for size; 20 for indirect branches) and by predecessor and successor counts (16). Jump threading is bounded at 6 (3 under `minsize`), and DFA jump threading by cost 50, path length 20, 200 paths and a cloned-instruction rate of 7.5.
  - GCC bounds jump threading at 15 statements (net path instructions × 2 must stay below 15 unless a multiway branch is threaded around a loop latch), FSM paths at 100 instructions and 64 searched paths, and trace formation at 100% code growth. `-ftracer` is off at `-O2`/`-O3`/`-Os` and is enabled by profile feedback.
- **Generator probe.** With conditionally owed releases from k independent conditions, full duplication needs 2^k tail copies, while flags need k bits. GCC 15.2 at `-O2` with its threading budget raised to 100 produced exactly 2^k copies (k = 6: 64 copies, 3,301–5,241 bytes against 464–470 bytes at the default budget). Its default stopped at 6/4/2 copies for tails of 1/2/4 calls, and `-Os` never duplicated. Clang 19.1.7 duplicated only the innermost condition (2 copies) for every k and kept the rest as re-tests. For nested (prefix-shaped) obligations it fully duplicated (k+1 copies) when the tail was 1 call.

## Applicability

| Role | Subject | Use |
| :--- | :--- | :--- |
| LLVM optimizer source | `llvm/llvm-project` @ `d71d3a9b75d9b21fc8fc8069cce2de71023b5b41` | source: thresholds and decision code |
| LLVM release tools | Debian clang/opt/llc 19.1.7 (`1:19.1.7-10.1+build1`, x86-64) | executed |
| GCC optimizer source | `gcc-mirror/gcc` @ `88f95ebe13064c5745d2571bf19b09ba641bf6fe` | source: parameters and decision code |
| GCC release | Debian gcc 15.2.0 (`15.2.0-14`, x86-64) | executed |
| Literature | DOIs in `REPORT.json` | published statements; access level noted per item |

The default threshold values come from the pinned sources. The probe results come from the released binaries, whose defaults were not separately read. The option names used in the probes (`-jump-threading-threshold`, `max-jump-thread-duplication-stmts`, `tracer-*`) were accepted by those binaries. All probes ran on x86-64 Linux under a 4 GiB cap and a 60 s timeout per run. The generator is a toy model in its cost counts and real in its compiler runs; the two are labeled separately.

## Findings

### 1. Terms

- *Duplication*: node splitting, tail duplication, jump threading, path or trace duplication. It replaces a run-time test with a code copy per reachable state.
- *State*: a flag, a selector or label variable, or a predicate. It keeps one copy and tests at run time.
- For k independent binary decisions that must be remembered across a join, duplication needs up to 2^k copies of the code after the join, and state needs k bits. When the decisions form prefixes (each decided only if the previous was taken), there are k+1 states, needing k+1 copies or ⌈log₂(k+1)⌉ bits. Basis: derived (counting).

### 2. Structuring theorems: auxiliary variables versus duplication

| Result | Program model | Auxiliary state | Duplication | Kind |
| :--- | :--- | :--- | :--- | :--- |
| Böhm–Jacopini 1966 | flow diagrams over mappings x→x′ | a stack of bits with boxes T, F, K and a predicate ω | not stated | constructive normal form; impossibility without bits only conjectured |
| Peterson–Kasami–Tokura 1973 | well-formed programs and flowcharts | none needed with multi-level exit | node splitting makes any flowchart well-formed | characterization plus an insufficiency result |
| Kosaraju 1973/1974 | structured programs with repeat-exit | none needed with arbitrary-depth breaks | – | strict hierarchy (secondary source only) |
| Ammarguellat 1992 | normalization to single-entry, single-exit while loops | (not found in abstract) | "avoids problems of code replication that are characteristic of node-splitting techniques" | algorithm plus complexity study |
| Erosa–Hendren 1994 | C abstract syntax tree, goto elimination | (not found in abstract) | – | algorithm, implemented in McCAT |

- **Böhm–Jacopini** (full text, scanned; OCR letter errors corrected in the quotes). "It is not possible to decompose all flow diagrams into a finite number of given base diagrams." The impossibility for the stronger notion is conjectured only: "We did not, however, succeed in finding a plain and sufficiently rigorous proof of this." The fix: "The proved unfeasibility is circumvented if a new predicate is added and if, among the elementary operations, some are assumed which either add one bit of information to the object of the computation or remove one from it. The extra bits have a stack structure." Their note: "A binary switch is the most natural interpretation of the added bit v." Basis: documentation.
- **Peterson–Kasami–Tokura** (abstract). "a program is well formed if and only if it can be written with if, repeat, and multi-level exit statements … if, while, and repeat statements with single-level exit do not suffice … any flowchart can be converted to a well-formed flowchart by node splitting." Basis: documentation, abstract only.
- **Kosaraju.** The primary text was not accessible. Wikipedia "Structured program theorem" (revision 1380706708, 2026-10-17) states two results. First, Kosaraju proved that additional variables can be avoided "as long as arbitrary-depth, multi-level breaks from loops are allowed". Second, "for every integer n, there exists a program containing a multi-level break of depth n that cannot be rewritten as program with multi-level breaks of depth less than n (without introducing additional variables)". The same page also states that "a program is reducible to a structured program (without adding variables) if and only if it does not contain a loop with two distinct exits". Basis: secondary documentation; treat as unverified against the primary.
- **Ramsey 2022** (abstract). The Peterson–Kasami–Tokura translation to loops, conditionals and multilevel exits "as published … takes three passes—which may explain why it was overlooked by Emscripten". Ramsey implements it in a single pass. What the paper says about Emscripten's label variable was not found.

### 3. Exponential lower bound for node splitting and the selector alternative

Carter–Ferrante–Thomborson 2003 (full text, author version). Basis: documentation.

- K_{Σ,e} is the complete directed graph on n = |Σ| labeled nodes with initial node e, so L(K_{Σ,e}) = eΣ*.
- "Theorem 4. If R is a reducible flow graph that is equivalent to K_{Σ,e} …, then R must have at least 2^(n−1) nodes."
- A bounded-degree family J_{Σ,e} has n(n−1) nodes of out-degree 2, and "Theorem 5 … R has at least 2^(n−1) nodes".
- The paper answers negatively both whether a node-splitting algorithm, and whether any equivalent reducible graph, can avoid exponential blowup.
- Footnote 1 says that predicate-variable restructuring "is not 'equivalent' in the technical sense … Thus, our results do not apply to such program restructuring techniques." The exponent was flattened in the extracted text and is rendered here as 2^(n−1), consistent with the paper's "exponential blowup".

Selector alternative in LLVM. Basis: source plus execution.

- **Mechanism.** `FixIrreducible.cpp` (header, lines 1–80) adds a new header N to each irreducible cycle and redirects all entry edges and all edges to the old header through N, implemented by a `ControlFlowHub` (`CHub.finalize(&DTU, GuardBlocks, "irr")`, `:395`). `ControlFlowUtils.cpp:218`–`228` gives the encoding choice: "When we are using an integer to record which target block to jump to, we are creating less live values … When we are using booleans to store the branching information, we need (N-1) boolean values, where N is the number of outgoing block". The booleans are used unless `MaxControlFlowBooleans` is set. `FixIrreducible` passes no limit (default `std::nullopt`, `ControlFlowUtils.h:120`–`122`).
- **Measurement** (`support/kn_fixirr.py`, opt/llc 19.1.7). K_n is generated as LLVM IR, with each node calling `@node(i)` and then branching to any node or exit by `@next()`. It is run through `opt -passes=lower-switch,fix-irreducible`, and the byte counts come from `llc -O2`.
- **Prerequisite.** Running `fix-irreducible` directly on the `switch` form crashed opt 19.1.7 (SIGSEGV). With `lower-switch` first it succeeded. The crash was not investigated further.

| n | blocks before → after | guard blocks | `i1` phis | `.text` bytes before → after | CFT lower bound for predicate-free reducible equivalents (nodes) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 3 | 17 → 18 | 1 | 1 | 136 → 168 | 4 |
| 5 | 37 → 40 | 3 | 3 | 307 → 367 | 16 |
| 7 | 65 → 70 | 5 | 5 | 464 → 544 | 64 |
| 10 | 122 → 130 | 8 | 8 | 1000 → 1301 | 512 |

The predicate cost grows linearly (n−2 Booleans, one per header beyond the first), where ⌈log₂(n−1)⌉ bits would suffice with the integer encoding. Machine code grew by 11.4–33.3% across n = 3…10. Basis: execution; the bound column is the theorem's value, not a measurement.

### 4. Measured node-splitting growth

- **Janssen–Corporaal 1997** (abstract). Controlled node splitting "results in a minimum number of splits and a minimum number of duplicates". Computing the optimum is expensive, so a heuristic is used. "Straightforward application of node splitting resulted in an average code size increase of 235% per procedure … CNS with the heuristic limits this increase to only 3% … 13.6% for a straightforward application … with the heuristic the average growth in code size of a complete program dramatically reduces to 0.2%". Benchmark identities were not found.
- **Unger–Mueller 2002** (abstract). Optimized node splitting "reduces the number of replicated nodes". The three methods (traditional splitting, optimized splitting, DJ-graph loop recognition) improve 1–40% over leaving irreducible loops unoptimized. DJ-graphs do "not significantly change the code size". Numeric growth was not found.

### 5. Benefits and growth reported for replication-based optimizations

| Work | Transformation | Benefit reported | Code growth reported | Growth bounded by construction? | Access |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Mueller–Whalley 1992 | replace unconditional jumps by replicated code | fewer executed instructions; less cache work "except for small caches" | "increases in code size" (no figure found) | yes: picks "the shortest sequence of instructions as a replacement" | abstract |
| Mueller–Whalley 1995 | replicate code where a branch outcome is known on a path | "reductions in both the number of instructions executed and total instruction cache work" | not found | not found | abstract |
| Bodík–Gupta–Soffa 1998 | restructuring for complete PRE | 73% of loop-invariant statements "cannot be eliminated from loops by code motion alone"; near-complete PRE | "very little code growth" (no figure found) | profile-guided selection of duplications | abstract |
| Hwu et al. 1993 | superblocks (trace selection plus tail duplication) | ILP along important paths | figure captions only ("Output code size expansion…") | not found | abstract |
| Ammons–Larus 1998 | hot-path graph, then reduction | 2–112× more non-local constants; 1–7% more dynamic instructions with constant results; 0.6–7% improvement at full coverage | graphs +3–32%, reduced +1–7%; go +184%/+70% (CFG size, not machine code) | reduction after analysis; coverage parameter | full text |
| Leopoldseder et al. 2018 (DBDS) | simulate duplication at merges, then pick by cost and benefit | peak performance up to 40%, mean 5.89% | mean +9.93% code; +18.44% compile time | yes: simulation plus budgeted trade-off | abstract |

Basis: documentation. Where a cell says "not found", the figure may exist in the full text, which was not accessible.

### 6. LLVM duplication budgets (pinned source)

| Decision | Parameter (default) | Location |
| :--- | :--- | :--- |
| Machine tail duplication, size | `tail-dup-size` (2); 1 if `shouldOptimizeForSize` | `CodeGen/CodeGenOptions.td:541`; `TailDuplicator.cpp:547`–`553` |
| … blocks ending in an indirect branch (pre-RA) | `tail-dup-indirect-size` (20) | `CodeGenOptions.td:535`; `TailDuplicator.cpp:578`–`579` |
| … computed goto, post-RA | ≥ 10 | `TailDuplicator.cpp:587`–`588` |
| … PHI-explosion guard | `tail-dup-pred-size` (16), `tail-dup-succ-size` (16) | `CodeGenOptions.td:538`, `:543`; `TailDuplicator.cpp:646` |
| Layout-time tail duplication | `tail-dup-placement-threshold` (2), `-aggressive-threshold` (4, "Used at -O3"); if unset, `TII->getTailDuplicateSize(OptLevel)`, which is `OptLevel >= Aggressive ? 4 : 2` (x86 does not override) | `MachineBlockPlacement.cpp:172`–`185`, `:3510`–`3533`; `TargetInstrInfo.h:2381`–`2383` |
| Layout profitability | `tail-dup-placement-penalty` (%), `tail-dup-profile-percent-threshold` (50) | `MachineBlockPlacement.cpp:188`–`203` |
| Jump threading | `BBDupThreshold` = 6 by default (`JumpThreadingPass(int T)`, `T == -1`); 3 under `minsize`; overridable by `jump-threading-threshold` | `JumpThreading.cpp:93`–`95`, `:289`–`294`, `:2273` |
| … other limits | `jump-threading-phi-threshold` (76), `jump-threading-implication-search-threshold` (3), `jump-threading-across-loop-headers` (false) | `ScalarOptions.td:186`–`193` |
| DFA (state-machine) jump threading | `dfa-cost-threshold` (50), `dfa-max-path-length` (20), `dfa-max-num-paths` (200), `dfa-max-num-visited-paths` (2500), `dfa-max-cloned-rate` (7.5), `dfa-max-out-use-blocks` (40) | `ScalarOptions.td:76`–`91`; `DFAJumpThreading.cpp:663`, `:981`, `:995`, `:1033` |
| Irreducible-flow repair | selector predicates (N−1 Booleans or one integer) | `FixIrreducible.cpp`, `ControlFlowUtils.cpp:218`–`228` |

Every budget is local: each counts instructions in the block or path being copied, not cumulative growth of the function. The probe in Finding 8 shows that the local limits stop exponential growth in practice. Basis: source plus execution.

### 7. GCC duplication budgets (pinned source)

| Decision | Parameter (default) | Location |
| :--- | :--- | :--- |
| Jump threading, block statements | `max-jump-thread-duplication-stmts` (15) | `params.opt:689`; `tree-ssa-threadedge.cc:223`; `tree-ssa-threadbackward.cc:748`–`760` |
| … scaling for paths not threading a loop | `fsm-scale-path-stmts` (2, range 1–10) | `params.opt:165` |
| … FSM paths when optimizing for speed | `max-fsm-thread-path-insns` (100) | `params.opt:609`; `tree-ssa-threadbackward.cc:712` |
| … search space | `max-jump-thread-paths` (64) | `params.opt:693` |
| … when optimizing for size | any path needing more than 1 instruction copied is rejected | `tree-ssa-threadbackward.cc:730`, `:815` |
| Trace formation (`pass_tracer`) | `tracer-max-code-growth` (100%), `tracer-dynamic-coverage` (75; 95 with feedback), `tracer-min-branch-probability` (50; 80 with feedback), `tracer-min-branch-ratio` (10) | `params.opt:1189`–`1211`; `tracer.cc:296`–`321` (`max_dup_insns = (ninsns * param_tracer_max_code_growth + 50) / 100`) |
| … gate | `optimize > 0 && flag_tracer && flag_reorder_blocks` | `tracer.cc:430` |
| … enabled by | `enable_fdo_optimizations` (profile use or AutoFDO) | `opts.cc:2137`–`2159` |
| Block copying during reordering | `max-grow-copy-bb-insns` (8, expansion factor); `max-goto-duplication-insns` (8) | `params.opt:621`, `:625`; `bb-reorder.cc:1375`, `:2980` |

Execution (gcc 15.2.0, `gcc -Q --help=optimizers`): `-ftracer` is `[disabled]` and `-fthread-jumps`/`-freorder-blocks` are `[enabled]` at each of `-O2`, `-O3` and `-Os`. Unlike LLVM's, GCC's tracer has a function-wide growth budget (100% of the function's instructions).

### 8. Generator: conditionally owed releases lowered by duplication and by flags

Graph family (`support/gen_owed.py`): k diamonds `if (c_i) { acquire(i); }`, then a shared tail of t opaque `body()` calls, then `release(i)` for each acquired i. In `indep` mode the conditions are independent (s = 2^k reachable obligation sets). In `nested` mode diamond i lies inside the then-arm of i−1 (s = k+1).

Toy-model costs, in abstract instructions with unit costs (`support/toy_table.tsv`). Basis: execution of a toy model, not of a compiler. F = flags, D = full duplication, C = prefix counter.

| Mode, k, t | Paths = s | ⌈log₂ s⌉ | F size / bits / mean executed | D size / copies / mean executed | C size / bits / mean executed |
| :--- | :--- | :--- | :--- | :--- | :--- |
| indep, 4, 1 | 16 | 4 | 25 / 4 / 19.0 | 78 / 16 / 9.0 | – |
| indep, 6, 16 | 64 | 6 | 52 / 6 / 43.0 | 1342 / 64 / 28.0 | – |
| indep, 8, 16 | 256 | 8 | 64 / 8 / 52.0 | 5630 / 256 / 32.0 | – |
| nested, 6, 1 | 7 | 3 | 37 / 6 / 17.92 | 40 / 7 / 4.94 | 27 / 3 / 7.92 |
| nested, 8, 16 | 9 | 4 | 64 / 8 / 36.98 | 196 / 9 / 19.98 | 50 / 4 / 22.98 |

In this cost model, duplication always executes fewer instructions (it saves k flag initializations, sets and tests), but its size grows with s × t. Flags grow linearly in k. Counters dominate flags in both size and bits when the obligation sets are prefixes.

Real compilers (`support/compile_owed.py`, then `compile_pivot.txt`). Each cell shows *tail copies* for t = 1, 2, 4, where copies are static `body()` call sites divided by t.

| Configuration | indep k=2 | indep k=3 | indep k=6 | nested k=3 | nested k=6 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| clang 19.1.7 `-O2` (also `-O3`, `-Os`; JT threshold 0 or 50) | 2,2,2 | 2,2,2 | 2,2,2 | 4,1,1 (JT 50: 4,4,4; JT 0: 1,1,1) | 7,1,1 (JT 50: 7,7,7; JT 0: 1,1,1) |
| gcc 15.2 `-O2` (= `-O3`) | 4,4,2 | 6,4,2 | 6,4,2 | 4,4,3 | 7,7,3 |
| gcc `-O2 --param max-jump-thread-duplication-stmts=0` | 2,1,1 | 2,1,1 | 2,1,1 | 2,1,1 | 2,1,1 |
| gcc `-O2 --param max-jump-thread-duplication-stmts=100` | 4,4,4 | 8,8,8 | 64,64,64 | 4,4,4 | 7,7,7 |
| gcc `-Os` | 1,1,1 | 1,1,1 | 1,1,1 | 1,1,1 | 1,1,1 |

Code bytes, same layout as the copies:

- gcc indep k=6: 464/434/470 at default against 3301/3937/5241 at budget 100.
- clang indep k=6: 248/268/312.
- clang nested k=6: 236/376/396 at default against 236/338/487 at JT 50.

Observations. Basis: execution plus derived.

1. GCC with an unbounded statement budget performs complete path specialization: 2^k copies, an exponential blowup of the kind Finding 3 describes, here driven by run-time state rather than irreducibility. Its default budget kept code size between 0.67× and 1.55× (median 1.08×) of the size with the statement budget set to 0, across all 30 generated graphs.
2. In Clang, the innermost condition's flag is removed by duplication even with jump threading disabled. For indep k=3, t=1, `-mllvm -jump-threading-threshold=0` alone or `-mllvm -simplifycfg-max-small-block-size=0` alone left 2 copies, and both together left 1 (`support/clang_pass_attribution.txt`). So either jump threading or SimplifyCFG's threading through small blocks performs it. The outer flags remain as re-tests of the original conditions held in registers, and no flag is stored to memory at `-O2` in these graphs.
3. For prefix-shaped obligations, both compilers duplicate fully when the tail is cheap and fall back to state as t grows, matching the toy model's point that duplication cost scales with t × s.
4. `-ftracer` (`support/tracer_probe.txt`) raised GCC's copies for indep k=3, t=4 from 2 to 4 (241 → 366 bytes), for indep k=6, t=1 from 6 to 8, and for nested k=4, t=4 from 3 to 5. Raising the tracer limits (growth 1000%, coverage 100%, minimum probability 0) changed no copy count, so those limits were not what bounded these cases. What did was not determined.
5. An EH edge can make duplication impossible regardless of budget. In a C++ conditional-cleanup probe on clang 19.1.7, a flag re-test across an `invoke` survived jump-threading thresholds 0–1000, while without exceptions the join was threaded at thresholds ≥ 4 (`support/jt_sweep.tsv`).

### 9. Synthesis: when state beats duplication

Basis: derived from Findings 2–8.

- **Worst case.** State is linear and duplication exponential in the number of independent remembered decisions. Carter–Ferrante–Thomborson make this a theorem for reducibility without predicates. The generator reproduces it for owed releases under an unbounded GCC budget.
- **Typical case.** Production compilers never chose the exponential option at default settings in these probes. Local per-block budgets (2–15 instructions) stop it after one or two levels, so flags survive for the remaining decisions.
- **Mixed outcome.** Neither compiler's budget is phrased as "copies per reachable state". The result is a mix: Clang duplicates once and keeps k−1 re-tests; GCC duplicates while blocks are small.
- **Optimization for size.** It disables duplication almost entirely: GCC `-Os` produced 1 copy and rejects threading paths that need more than one instruction copied; LLVM caps tail duplication at 1 instruction.
- **Selector encodings.** These differ by an exponential in bits: N−1 Booleans versus one ⌈log₂ N⌉-bit integer in LLVM's hub; k flags versus ⌈log₂(k+1)⌉ counter bits for prefixes.

### 10. Performance and footprint by level

| Level | Evidence |
| :--- | :--- |
| L1 authoring | not measured |
| L2 toolchain build | not measured |
| L3 compile time | DBDS: +18.44% mean compile time (cited). 300 compilations of the generator (`compile_owed.py`) finished inside one 60 s cap; per-compile time not measured |
| L4 generated code | DBDS +5.89% mean, up to 40%; Ammons–Larus 0.6–7%; Unger–Mueller 1–40% (all cited); toy-model executed counts (Finding 8); real-compiler run time of generated graphs not measured |
| L5 certificate checking | not applicable |
| L6 code size | node splitting +235%/procedure vs +3% (CNS); +13.6%/program vs +0.2% (cited); DBDS +9.93% (cited); FixIrreducible +11–33% on K_n (measured); GCC 2^k copies at budget 100 (measured) |

### 11. Comprehensibility and model refinement (C1, C2)

- **C1.** Duplicated code is locally readable, since each copy is straight-line for its path. Its review cost and diagnostic noise (repeated line numbers) grow with copies. Flag code is compact but needs nonlocal reasoning about which assignment reaches each test. Böhm–Jacopini's bit stack and Kosaraju's hierarchy formalize how much control information structured code must carry. Peterson–Kasami–Tokura's multi-level exit removes the need for auxiliary variables at the price of exits that cross several nesting levels.
- **C2.** The production compilers implement one decision, copy or test, with five independently tuned mechanisms (tail duplication, layout tail duplication, jump threading, DFA threading, tracer) that use different size metrics, thresholds and size-optimization rules. A single budget expressed in copies per reachable state, with the state encoding chosen by s (Booleans, integer, or copies), would make the probe's mixed outcomes predictable. It is a design hypothesis, not an observed implementation.

### 12. Validation of the transformations (V1–V4)

- **V1.** Janssen–Corporaal compare against an optimum ("minimum number of splits"). DBDS validates its simulation by benchmark suites (DaCapo, Scala DaCapo, Octane, micro-benchmarks). No specification-mutation work was found for these passes.
- **V2.** The generator is a differential harness: the same graph at several budgets, checked by counting call sites. It checks no semantics. Combining it with an execution oracle, running all 2^k inputs and comparing release traces, is a cheap extension that was not run.
- **V3–V4.** Not examined.

## Boundaries

- **Not examined:**
  - Full texts of Kosaraju, Ammarguellat, Erosa–Hendren, Mueller–Whalley (both), Bodík–Gupta–Soffa, Hwu et al., Unger–Mueller, Janssen–Corporaal, DBDS and Ramsey: their theorems and figures beyond the abstracts.
  - Graal's DBDS implementation source.
  - Trace scheduling (Fisher 1981) beyond its metadata.
  - Builds of the pinned trunks.
  - Run time of the generated graphs on real hardware.
  - Non-x86 targets.
  - The cause of the opt 19.1.7 crash on `fix-irreducible` without `lower-switch`.
- **Unknown:**
  - Whether Kosaraju's hierarchy statement matches the secondary paraphrase exactly.
  - Whether Böhm–Jacopini's impossibility conjecture was later proved in their exact model. Peterson–Kasami–Tokura and Kosaraju address related but different models.
- **Known not to apply:** the Carter–Ferrante–Thomborson bound does not cover predicate-variable restructuring (their footnote 1), so it is no lower bound for flag-based lowering.
- **Stronger conclusions not established:**
  - That GCC's default budget is near-optimal.
  - That Clang's single duplication generalizes to other graph shapes.
  - That the toy-model executed-instruction advantage of duplication becomes a run-time win; instruction-cache effects, which Mueller–Whalley discuss, were not modeled.
  - That the default thresholds of the pinned sources equal those of the probed binaries. Only option acceptance and observed behavior were checked.
- **Not measured:** L1, L2, L5; per-compile latency; run time of generated code.

## Evidence

Observed 2026-11-21 (UTC). Commit pins resolved via the GitHub commits API on the same day.

- **LLVM** (`llvm/llvm-project` @ `d71d3a9b75d9b21fc8fc8069cce2de71023b5b41`):
  - `llvm/lib/CodeGen/CodeGenOptions.td:535`–`546`;
  - `llvm/lib/CodeGen/TailDuplicator.cpp:540`–`660`;
  - `llvm/lib/CodeGen/MachineBlockPlacement.cpp:171`–`204`, `:3480`–`3533`;
  - `llvm/include/llvm/CodeGen/TargetInstrInfo.h:2379`–`2383`;
  - `llvm/lib/Transforms/Scalar/JumpThreading.cpp:93`–`95`, `:284`–`306`, `:2260`–`2280`;
  - `llvm/lib/Transforms/Scalar/ScalarOptions.td:76`–`92`, `:186`–`194`;
  - `llvm/lib/Transforms/Scalar/DFAJumpThreading.cpp:655`–`680`, `:960`–`1045`;
  - `llvm/lib/Transforms/Utils/FixIrreducible.cpp:1`–`80`, `:395`;
  - `llvm/lib/Transforms/Utils/ControlFlowUtils.cpp:60`–`231`;
  - `llvm/include/llvm/Transforms/Utils/ControlFlowUtils.h:118`–`122`.
- **GCC** (`gcc-mirror/gcc` @ `88f95ebe13064c5745d2571bf19b09ba641bf6fe`):
  - `gcc/params.opt:165`–`167`, `:609`–`627`, `:689`–`695`, `:1189`–`1211`;
  - `gcc/tracer.cc:290`–`330`, `:420`–`431`;
  - `gcc/tree-ssa-threadbackward.cc:705`–`765`, `:810`–`852`;
  - `gcc/tree-ssa-threadedge.cc:223`–`270`;
  - `gcc/bb-reorder.cc:1360`–`1376`, `:2980`;
  - `gcc/opts.cc:2137`–`2159`.
- **Literature.** Every DOI was checked against Crossref (`api.crossref.org/works/<doi>`) on 2026-11-21, and title, authors, venue, volume and pages matched. MICRO and ICCL records carry no Crossref date; their years come from the proceedings.
  - Böhm, Jacopini, CACM 9(5):366–371, 1966, DOI 10.1145/355592.365646. Full text, scanned.
  - Peterson, Kasami, Tokura, CACM 16(8):503–512, 1973, DOI 10.1145/355609.362337. Abstract.
  - Kosaraju, JCSS 9(3):232–255, 1974, DOI 10.1016/S0022-0000(74)80043-7. Not accessible; secondary: en.wikipedia.org "Structured program theorem", revision 1380706708.
  - Ammarguellat, IEEE TSE 18(3):237–251, 1992, DOI 10.1109/32.126773. Abstract.
  - Hwu et al., J. Supercomputing 7(1–2):229–248, 1993, DOI 10.1007/BF01205185. Abstract.
  - Erosa, Hendren, ICCL 1994, pp. 229–240, DOI 10.1109/ICCL.1994.288377. Abstract.
  - Mueller, Whalley, PLDI 1992, pp. 322–330, DOI 10.1145/143095.143144. Abstract.
  - Mueller, Whalley, PLDI 1995, pp. 56–66, DOI 10.1145/207110.207116. Abstract.
  - Janssen, Corporaal, TOPLAS 19(6):1031–1052, 1997, DOI 10.1145/267959.269971. Abstract.
  - Bodík, Gupta, Soffa, PLDI 1998, pp. 1–14, DOI 10.1145/277650.277653. Abstract.
  - Ammons, Larus, PLDI 1998, pp. 72–84, DOI 10.1145/277650.277665. Full text.
  - Unger, Mueller, TOPLAS 24(4):299–333, 2002, DOI 10.1145/567097.567098. Abstract.
  - Carter, Ferrante, Thomborson, POPL 2003, pp. 106–114, DOI 10.1145/604131.604141. Full text, author version.
  - Leopoldseder, Stadler, Würthinger, Eisl, Simon, Mössenböck, CGO 2018, pp. 126–137, DOI 10.1145/3168811. Abstract.
  - Ramsey, PACMPL 6 (ICFP), 2022, DOI 10.1145/3547621. Abstract.
- **Probes** (`support/`):
  - `gen_owed.py table` → `toy_table.tsv`;
  - `compile_owed.py <clang> <gcc> <dir>` → `compile_table.tsv`, `compile_pivot.txt`;
  - `kn_fixirr.py <opt> <llc> <dir>` → `kn_fixirr.tsv`;
  - `tracer_probe.sh` → `tracer_probe.txt`;
  - `clang_pass_attribution.sh` → `clang_pass_attribution.txt`;
  - `jt_sweep.sh` and `cond_cleanup.cpp` → `jt_sweep.tsv`.

  Toolchain binary hashes (sha256):
  - clang-19: `652e82bfb8c2b0881693501a9643e3106d5f22aa18da3b0697888c2d0fc995ae`;
  - gcc-15: `9a5248796bf632e9ca737f8e707978dc87f8d5aeedb7dd17a75c4e262d0855c0`.

## Revalidation

- **Budgets.** Grep the pinned files for the parameter names in Findings 6–7, specifically `tail-dup-size`, `BBDupThreshold`, `max-jump-thread-duplication-stmts` and `tracer-max-code-growth`, and compare the defaults.
- **Exponential behavior.** Run `python3 compile_owed.py <clang> <gcc> <dir>`. The discriminating rows are gcc `max-jump-thread-duplication-stmts=100` at indep k=6 (64 copies means full path specialization), gcc default at indep k=3, t=1 (6 copies), and clang default at indep k=6 (2 copies).
- **Selector encoding.** Run `kn_fixirr.py`. `i1` phis equal to n−2 means the Boolean encoding is in use; one integer phi would indicate `MaxControlFlowBooleans` was set.
- **Literature.** The quoted statements are immutable. The open items need the full texts listed under Boundaries.
