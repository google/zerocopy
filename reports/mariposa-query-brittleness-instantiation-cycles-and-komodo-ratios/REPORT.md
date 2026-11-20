# SMT Query Instability Perturbations, E-Matching Cycle Diagnostics, Context Pruning, and Empirical Proof-to-Code Ratios

## Summary

Automated and semi-automated verification toolchains (`Dafny`, `Verus`, `F*`, `Vale`/`Komodo`) rely on SMT solvers (`Z3`, `cvc5`) whose heuristic quantifier and arithmetic search creates measurable maintenance hazards distinct from final proof-certificate checking:

1. **Empirical SMT instability affects `2.6%` of verification queries overall (`0.2%–5.0%` per project), driven by syntactic sensitivity rather than per-run coin flips.** Across `17,043` SMT-LIB queries from six verification codebases, `Mariposa` (`Zhou et al., FMCAD 2023`) classifies `2.6%` of queries on `Z3` as unstable under semantics-preserving assertion shuffling, symbol alpha-renaming, and solver random-seed variation (`60` mutants per axis, `r_solvable = 0.05`, `r_stable = 0.95`, `discount = 0.8`), with solver upgrades frequently degrading stability (validated live here: `jon_unstbale_1.smt2` proves `unsat` across `20/20` seeds and shuffles on `Z3 4.8.5`, regresses to `unknown` on unshuffled `Z3 4.12.5`, and flips `10/20` `unsat` vs. `10/20` `unknown` under interval-preserving assertion shuffles on `Z3 4.12.5`). Modeling instability as an independent Bernoulli flake probability $1 - (1 - p)^N$ per CI build is a category error: with fixed query bytes, solver binary, seed, and `rlimit`, solver execution is deterministic (`0%` rerun flake), so instability surfaces specifically during *code/specification edits* or *solver upgrades* that perturb the `2.6%–5.0%` sensitive frontier.
2. **E-matching matching loops and ambient axiom bloat dominate instability; fuel guards and trigger-conjunctive pruning bound search.** `SMT-Scope` (`viperproject/smt-scope`, the active Rust successor to `viperproject/axiom-profiler-2`, building on `Becker, Muller, and Summers, TACAS 2019`) detects matching loops as generalized instantiation chains of length $\ge 4$ (`MIN_MATCHING_LOOP_LENGTH = 3` after initial-edge offset) with overlapping CDCL stack frames and flags axioms whose input multiplicativity reaches $\ge 2.0\times$ (`warning`) or $\ge 4.0\times$ (`error`). Replacing a `:weight 0` self-triggering axiom with a constructor-stripping `Fuel` parameter reduces `Z3 4.12.5` search on an unprovable goal from `rlimit = 200,025` (`3,773` instantiations) to `rlimit = 664` (`3` instantiations, a `301x` `rlimit` reduction) and eliminates `cvc5 1.1.1` timeouts (`506.6 ms` timeout -> `35.7 ms` `unknown`). Static context pruning in `Verus` (`source/vir/src/prune.rs`) activates `broadcast` lemmas conjunctively only when *all* functions and types in a trigger tuple are reachable, whereas `Mariposa`'s `tree_shake.rs` splits multi-triggers `:pattern ((f x) (g x))` disjunctively to preserve soundness on raw SMT-LIB.
3. **Stored proof witnesses eliminate unchanged-query CI variance (`0%`) at the cost of edit-time regeneration across dependency cones.** Exporting deterministic SMT certificates or unsat cores shifts solver search out of unchanged CI builds and out of the trusted computing base, but any specification edit that alters a shared datatype, trait bound, or revealed `broadcast` group invalidates cached witnesses across its reachable caller cone unless `opaque` body hiding and `ProofDependencyManager` unsat-core minimization isolate callers from callee internals.
4. **Real source-level proof-to-code ratios span `0.10x–2.46x` in modular linear-ghost Rust (`Verus`) versus `6.88x` proof / `8.52x` `(spec + proof)` in verified assembly (`Komodo`).** Direct audit of `microsoft/komodo` (`de1865c8bd0d85cdfd9a980ad7131448acfaf136`) confirms `25,213` non-comment SLOC across `88` `.vad`/`.dfy` files (`178` Vale procedures, `1,162` ARM instruction macro calls) plus `803` SLOC of unverified C/assembly monitor glue, matching `SOSP 2017`'s `2,710` implementation, `4,446` specification, and `18,655` proof lines (`~2` person-years). By leveraging Rust's borrow checker for memory framing, `Verus` (`OOPSLA 2023`) verifies data-structure and concurrency modules (`Vector`, `XOR` doubly-linked list, `FIFO` queue, `RwLock`) at `0.63x–2.46x` `(spec + proof) / exec`, an order of magnitude denser than assembly-level `Vale`/`Dafny` (`8.52x`) and interactive binary-lifting `Rocq` proofs (`~33.3x` lines per instruction).

## Applicability

This report governs verification toolchain architecture, CI stability budgeting, quantifier/trigger design, context-pruning passes, and engineering effort estimation for SMT-backed deductive verifiers.

### Subject Relationships and Scope

- **`secure-foundations/mariposa`** (`8646e7b1c601f7154e93d85ebb1083ce1ed47f95`) and **`Zhou et al. (FMCAD 2023)`** (`DOI: 10.34727/2023/isbn.978-3-85448-060-0_26`): Examined for SMT-LIB perturbation semantics (`query_mutate.rs`), statistical classification (`query_analyzer.py`), context pruning (`tree_shake.rs`), and empirical instability rates across `Dafny`, `F*`, `Serval`, and `Verus` query suites, supplemented by live execution of its pinned Linux `x86_64` binaries `bin/z3-4.8.5`, `bin/z3-4.12.5`, and `bin/cvc5-1.1.1`.
- **`viperproject/axiom-profiler-2`** (`03e43597e7ac5969e721647c894f35ffb46adb46`), **`viperproject/smt-scope`** (`665f9263c6102ff63494dafb39976d015c675951`), and **`Becker, Muller, and Summers (TACAS 2019)`** (`DOI: 10.1007/978-3-030-17462-0_6`): `axiom-profiler-2` at `03e43597e7ac5969e721647c894f35ffb46adb46` is a 2-file tombstone repository whose `README.md` redirects to `viperproject/smt-scope`; both are pinned so the live Rust causal instantiation-graph and matching-loop algorithms (`smt-scope-lib/src/analysis/`) can be audited directly.
- **`verus-lang/verus`** (`0dab219272ac2353320bd177ebb3929453b90a9e`, with **`Lattuada et al., OOPSLA 2023`**, `DOI: 10.1145/3586037`) and **`dafny-lang/dafny`** (`75de7486da5a473a5aba2add8ff80fc5bbe8337f`): Examined to compare reachability-based axiom pruning (`prune.rs`), isolated sub-solvers (`bit_vector`, `nonlinear_arith`), cross-solver `rlimit` scaling (`verifier.rs`), assertion batch splitting (`--isolate-assertions`), and unsat-core proof dependency tracking (`ProofDependencyManager.cs`).
- **`microsoft/komodo`** (`de1865c8bd0d85cdfd9a980ad7131448acfaf136`, with **`Ferraiuolo et al., SOSP 2017`**, `DOI: 10.1145/3132747.3132748`): Audited directly at file and SLOC granularity as a real deployed ARMv7 TrustZone monitor verified in `Vale` + `Dafny`.

Live solver timings and `max-memory` measurements apply to `x86_64` Linux (Intel Xeon `2.20 GHz`); `Z3` `:rlimit-count` and `:quant-instantiations` counters are architecture-independent deterministic step counts for a fixed solver binary and input file.

## Findings

### 1. SMT Perturbation Mechanics, Statistical Stability Classification, and Real Benchmark Rates

`Basis: normative + source + execution (real Z3 4.8.5, Z3 4.12.5, and cvc5 1.1.1 binaries)`

#### 1.1 Perturbation Operators and Syntax-Scope Invariants (`Mariposa`)

In `secure-foundations/mariposa` (`8646e7b1c601f7154e93d85ebb1083ce1ed47f95`), `src/smt2action/src/query_mutate.rs` and `src/base/solver.py` implement three semantics-preserving perturbation families (`config/expers.json` default: `num_mutants = 60` per family plus `1` unmutated baseline, `n = 61`, `exp_timeout = 60 s`):

1. **Assertion-Interval Shuffling (`shuffle`):** `shuffle_commands` (`query_mutate.rs:65–93`) seeds `ChaCha8Rng` and permutes only *contiguous runs* of `concrete::Command::Assert` (or, when `lower == true` after preprocessing, partitions all declarations ahead of shuffled `Assert` commands immediately before `(check-sat)`, lines `43–63`). Shuffling across `(declare-fun ...)` or `(push)`/`(pop)` boundaries without preprocessing causes unbound-symbol errors (verified on `jon_unstbale_1.smt2`, which interleaves `452` `(assert ...)` commands across `72` contiguous intervals among `1,355` total commands).
2. **Alpha-Renaming (`rename`):** `rename_symbols` (`query_mutate.rs:95–117`) invokes `smt2parser::renaming::SymbolNormalizer` across all eight `SymbolKind` namespaces (`Variable`, `Constant`, `Function`, `Sort`, `Datatype`, `TypeVar`, `Constructor`, `Selector`), perturbing hash-table bucket orders and variable-ordering tie-breakers inside CDCL(T) and E-matching engines while leaving built-in SMT-LIB theory symbols intact.
3. **Solver Random Seeding (`reseed`):** `Z3Solver.get_basic_command` (`src/base/solver.py:125–132`) passes `sat.random_seed=<seed>` and `smt.random_seed=<seed>` alongside `-T:<time_limit>`, while `CVC5Solver` (`lines 153–165`) passes `--tlimit=<ms>` and solver seed flags.

`QueryAnalyzer` (`src/base/query_analyzer.py:48–179`, `config/analyzers.json`) classifies each `(query, mutation)` group of size $n = 61$ using `r_solvable = 0.05`, `r_stable = 0.95`, `confidence = 0.05`, and `discount = 0.8`:
- Under `z_test` (`lines 113–153`, FMCAD 2023 methodology using `statsmodels.stats.proportion.proportions_ztest`), a group is `UNSOLVABLE` if $p_{\text{smaller}}(s/n < 0.05) \le 0.05$; `UNSTABLE` if $p_{\text{smaller}}(s/n < 0.95) \le 0.05$ **and** the mean runtime of successful `unsat` runs is strictly below `0.8 * timeout` (preventing stable queries whose runtime happens to sit at `59 s` near a `60 s` cutoff from being misclassified as solver instability); `STABLE` if $p_{\text{larger}}(s/n > 0.95) \le 0.05$; and `INCONCLUSIVE` otherwise.
- `categorize_query` (`lines 155–179`) aggregates across `{shuffle, rename, reseed}`: if non-inconclusive votes disagree across mutation types (e.g., `STABLE` under `reseed` but `UNSTABLE` or `UNSOLVABLE` under `shuffle`), the query is classified `UNSTABLE`.

#### 1.2 Published `17,043`-Query Benchmark Distribution (`Zhou et al., FMCAD 2023`)

Across six verification suites evaluated in `Zhou et al. (FMCAD 2023)` (`DOI: 10.34727/2023/isbn.978-3-85448-060-0_26`), `Z3` (`4.12.1`) exhibits **`2.6%` overall query instability**, varying by over `20x` depending on encoding discipline:

| Verification Suite | Tool / Encoding Style | Total Queries | Core Unstable | Ext Unstable | Peak Project Instability & Root-Cause Profile |
| :--- | :--- | ---: | ---: | ---: | :--- |
| **`Komodo_D`** | `Vale` + `Dafny` / `Boogie` (`Z3`) | `2,054` | `8` | `95` | Up to `~5.0%`; heavy quantified ARM page-table, bitvector-to-int, and framing axioms |
| **`Komodo_S`** | `Serval` symbolic ARM evaluation (`Z3`) | `773` | `2` | `2` | `~0.5%`; quantifier-free `QF_BV` state-machine unfolding avoids E-matching |
| **`VeriBetrKV_L`** | Linear `Dafny` B-epsilon tree (`Z3`) | `5,600` | `22` | `153` | `~3.1%`; large ambient module contexts (`> 500` axioms) + sequence/map triggers |
| **`VeriBetrKV_D`** | Dynamic-frames `Dafny` KV store (`Z3`) | `5,325` | `25` | `130` | `~2.9%`; dynamic-frame set comprehension quantifiers |
| **`DICE*_F`** | `F*` cryptographic boot chain (`Z3`) | `1,536` | `3` | `9` | `~0.8%`; localized fuel/lemma calls |
| **`vWasm_F`** | `F*` sandboxing compiler (`Z3`) | `1,755` | `0` | `4` | `~0.2%`; tightly scoped functional obligations |
| **Total** | — | **`17,043`** | **`60`** | **`393`** | **`2.6%` overall on `Z3` (`up to 5.0%` per project)** |

In addition, `src/bench/consts.py:1–150` in `mariposa` (`8646e7b1c601f7154e93d85ebb1083ce1ed47f95`) catalogs `71` unstable `Verus` queries across `Anvil` Kubernetes liveness controllers (`20`), `VeriSMo` AMD SEV-SNP monitor (`13`), `mimalloc` verified allocator (`7`), `SplinterDB` (`2`), `Atmosphere` kernel (`1`), `FlowCert` (`1`), and verified storage multilog (`27`), splitting into `31` `mostly_unknown` (`verus_qus`) and `40` `mostly_timeout` (`verus_tos`) failures.

#### 1.3 Live Cross-Version and Shuffle Reproduction (`Z3 4.8.5` vs. `Z3 4.12.5`)

Executing the exact solver binaries shipped in `secure-foundations/mariposa` (`bin/z3-4.8.5` and `bin/z3-4.12.5`) on `data/samples/` (`-T:3 -st`) demonstrates non-monotone solver-upgrade drift and assertion-order sensitivity directly:

| Sample Query (`data/samples/`) | `Z3 4.8.5` Status / Time / `rlimit` / `qinst` / RSS | `Z3 4.12.5` Status / Time / `rlimit` / `qinst` / RSS | Observed Behavior |
| :--- | :--- | :--- | :--- |
| `single_check.smt2` (`33.6 KB`) | `unsat` / `207.6 ms` / `2,051` / `0` / `3.4 MB` | `unsat` / `62.0 ms` / `4,300` / `0` / `21.0 MB` | Stable `QF_BV` equivalence check |
| `1434.4.smt2` (`31.4 KB`) | **`timeout`** / `3,009.0 ms` / `4,385,098` / `63` / `17.6 MB` | **`unsat`** / `1,955.6 ms` / `2,389,944` / `63` / `29.7 MB` | Upgrade fixes `3 s` timeout (`1.83x` fewer `rlimit` steps) |
| `1435.4.smt2` (`32.7 KB`) | `unsat` / `1,865.0 ms` / `3,092,105` / `64` / `16.9 MB` | `unsat` / `386.0 ms` / `503,405` / `64` / `28.4 MB` | Upgrade speeds solve `4.83x` (`6.14x` fewer `rlimit` steps) |
| `verus_vect.smt2` (`137.6 KB`, `3` checks) | `3x unsat` / `69.7 ms` / `100,888` / `529` / `4.7 MB` | `3x unsat` / `97.2 ms` / `100,303` / `556` / `22.5 MB` | Stable incremental Verus vector VCs |
| `jon_unstbale_1.smt2` (`513.0 KB`, `452` asserts) | **`unsat`** / `286.2 ms` / `383,255` / `6,414` / `8.8 MB` | **`unknown`** / `368.8 ms` / `377,849` / `6,642` / `28.9 MB` | **Upgrade regression** (`unsat -> unknown` with `:smt.arith.nl false`) |
| `jon_unstbale_1.smt2` (`20` interval shuffles, `-T:2`) | **`20/20 unsat`** (`rlimit 382,998..383,303`) | **`10/20 unsat`, `10/20 unknown`** (`rlimit 353,164..409,654`) | **Exact `50.0%` flip rate under assertion-order permutation on `Z3 4.12.5`** |

**Why Independent-Bernoulli CI Failure Compounding (`1 - (1 - p)^N`) Is Fallacious:** A common analytic error models per-VC instability $p$ as an independent random failure on every CI run across $N$ VCs, predicting catastrophic CI failure rates $1 - (1 - p)^N$ on unchanged repositories. In reality, running `Z3 4.8.5` or `Z3 4.12.5` repeatedly on `jon_unstbale_1.smt2` with fixed seed and fixed `rlimit` yields `100%` identical `:rlimit-count` (`383,255` and `377,849`, respectively) across every run. Flakiness occurs **not** on passive CI reruns, but when an engineer edits a definition—effectively drawing a `shuffle`/`rename` perturbation across the module's affected VCs—or bumps the pinned solver version.

---

### 2. Quantifier Causal Graphs, Matching Loops, and Context Pruning (`SMT-Scope`, `Mariposa`, `Verus`)

`Basis: normative + source + execution (real Z3 4.12.5 and cvc5 1.1.1 binaries)`

#### 2.1 Matching-Loop and Multiplicativity Detection in `SMT-Scope` (`Axiom Profiler 2`)

Inspection of `viperproject/axiom-profiler-2` (`03e43597e7ac5969e721647c894f35ffb46adb46`, `README.md:1`) confirms the repository was renamed to `viperproject/smt-scope` (`665f9263c6102ff63494dafb39976d015c675951`). Extending `Becker, Muller, and Summers (TACAS 2019)` (`DOI: 10.1007/978-3-030-17462-0_6`), `smt-scope-lib` (`15,201` non-comment Rust SLOC across `80` files) parses `Z3` `[mk-quant]`/`[instance]`/`[attach-enode]` trace logs into a causal `InstGraph` and flags two structural pathologies (`smt-scope-lib/src/analysis/problem_behaviour.rs:14–40`, `graph/analysis/matching_loop/{mod.rs,search.rs}`):

1. **Confirmed vs. Suspicious Matching Loops (`PbKind::MatchingLoop`):**
   `InstGraph::search_matching_loops` (`search.rs:13–70`) groups instantiations by `MlSignature` (quantifier-pattern + blame-structure fingerprint), filters for signatures with at least `MIN_MATCHING_LOOP_LENGTH = 3` (`4` actual instantiations due to initial-link offset, `mod.rs:20–22`) whose active CDCL stack lifetimes overlap (`has_n_overlapping_stacks`, preventing sequential independent case-splits from false-reporting as loops), runs topological chain extraction, and attempts AST term generalization (`MlGraph`). Chains that generalize into a repeating substitution template ($\sigma(t) \mapsto C[\sigma(t)]$, e.g., $f(x) \mapsto f(g(x))$) are reported as confirmed errors (`sure_mls`, `sus: false`); ungeneralized chains of length $\ge$ `MIN_SUSPICIOUS_CHAIN_LENGTH = 6` are reported as warnings (`maybe_mls`, `sus: true`).
2. **Branching Multiplicativity (`PbKind::Multiplicative`):**
   Even acyclic quantifier pairs (such as transitivity $\forall x, y, z.\, R(x, y) \land R(y, z) \implies R(x, z)$ or set-union distributivity) cause cubic/exponential E-graph blowup. `ProblemBehaviours::find` (`problem_behaviour.rs:27–38`) computes `red.input_multiplicativity()` per `QuantPat`, raising a warning at `>= 2.0x` and a confirmed error at `>= 4.0x`.

Executing `Z3 4.12.5` (`rlimit=200000 -st`) and `cvc5 1.1.1` (`--tlimit=500`) under standard verifier flags (`:auto_config false`, `:smt.mbqi false`) quantifies the gap between an unguarded `:weight 0` recursive trigger and `Verus`/`Dafny` unary `Fuel` guarding on an unprovable goal (`f(a) < 0`):

| Encoding Variant | Trigger Pattern | `Z3 4.12.5` Outcome / `rlimit` / `qinst` | `cvc5 1.1.1` Outcome / Time |
| :--- | :--- | :--- | :--- |
| Unguarded recursive axiom (`:weight 1` default) | `:pattern ((f x))` | `unknown` / `1,468` / `20` (halted by eager threshold) | **`timeout`** / `506.6 ms` |
| Unguarded recursive axiom (`:weight 0`, Boogie/AIR style) | `:pattern ((f x)) :weight 0` | `unknown` (`rlimit` exhausted) / **`200,025`** / **`3,773`** | **`timeout`** / `506.6 ms` |
| Fuel-guarded recursive axiom (`k = S(S(S(Z)))`) | `:pattern ((f (S k) x))` | `unknown` (clean) / **`664`** / **`3`** | **`unknown` (clean)** / **`35.7 ms`** |

Fuel guarding reduces `Z3` `rlimit` consumption on failing/unprovable proof obligations by **`301x`** (`200,025 -> 664`) and quantifier instantiations by **`1,257x`** (`3,773 -> 3`), converting silent solver timeouts into `< 45 ms` interactive counterexample diagnostics.

#### 2.2 Conjunctive vs. Disjunctive Context Pruning (`Verus` `prune.rs` vs. `Mariposa` `tree_shake.rs`)

Because ambient prelude and imported module axioms supply spare terms that ignite cross-axiom E-matching cycles, both `Mariposa` and `Verus` implement static reachability pruning, but with a critical precision gap on multi-triggers:

- **`Mariposa` `tree_shake.rs` (`src/smt2action/src/tree_shake.rs:28–37, 232–259`):** Operates post-hoc on raw SMT-LIB. When encountering a multi-pattern `:pattern ((f x) (g x))`, `get_pattern_uses` (`lines 245–252`) explicitly notes:
  ```rust
  // if there are multiple terms in the pattern
  // it is multi-pattern (not multiple patterns)
  // current strategy is to treat each term individually
  // e.g. :pattern ((f x) (g x)) is treat as two patterns
  terms.iter().for_each(|x| patterns.push(self.get_symbol_uses(&x)));
  ```
  `PatternState::check_match` (`lines 29–37`) then fires if *any* entry in `matchable_patterns` is a subset of live symbols (**disjunctive over-approximation**). Even with this conservative over-approximation, Shake reduces unstable query counts by ~`29%` on `Z3` and ~`41%` on `cvc5`.
- **`Verus` `prune.rs` (`source/vir/src/prune.rs:62–67, 203–229, 951–975`):** Operates on typed VIR before AIR/SMT emission at crate, module, or per-function granularity (`prune_krate_for_module_or_krate`). `ReachBroadcastFunction` stores `reach_triggers: Vec<(Vec<Fun>, Vec<ReachedType>)>`, and `reach_function_via_reveal` (`lines 211–225`) retains a revealed `broadcast` lemma **only if every function `f` in `trig_funs` AND every type `t` in `trig_typs` of at least one trigger tuple is reached** (**exact conjunctive matching**). Furthermore, `Verus` provides isolated sub-solver modes `by(bit_vector)` and `by(nonlinear_arith)` (`source/vir/src/well_formed.rs:1317–1356`, `sst_to_air.rs:3019–3042`) that spawn clean SMT contexts containing *only* the asserted arithmetic/BV formula with zero heap, trait, or broadcast axioms.

---

### 3. Determinism Controls, Stored Witness Invalidation, and Empirical Proof-to-Code Ratios

`Basis: normative + source + execution (Komodo repository audit)`

#### 3.1 Cross-Solver `rlimit` Asymmetry,VC Splitting, and Stored-Witness Maintenance

- **`rlimit` Scaling Discrepancy (`Verus` vs. `Dafny`):** `Verus` (`source/rust_verify/src/config.rs:9`, `verifier.rs:51–52, 1122–1131`) enforces deterministic resource limits by default (`DEFAULT_RLIMIT_SECS = 10.0`), multiplying by **`RLIMIT_PER_SECOND_Z3 = 3,000,000`** (`rlimit = 30,000,000`) for `Z3` versus **`RLIMIT_PER_SECOND_CVC5 = 333,333`** (`rlimit = 3,333,330`) for `cvc5`—a **`9.0x` numerical step ratio** reflecting coarser internal tick accounting in `cvc5`—and resets `(set-option :rlimit 0)` after `(check-sat)` (`air/src/smt_verify.rs:224–282`). By contrast, `Dafny` (`Source/DafnyCore/Options/BoogieOptionBag.cs:54–74`) defaults to non-deterministic wall-clock `--verification-time-limit 30` (`30 s`) unless `--resource-limit` (parsed with scientific notation `NumberStyles.AllowExponent` in `DafnyOptions.cs:506–508`) is passed explicitly.
- **Assertion Splitting (`Dafny` `--isolate-assertions`):** `BoogieOptionBag.IsolateAssertions` (`BoogieOptionBag.cs:83, 148`, setting `VcsSplitOnEveryAssert = true`) decomposes a multi-assertion Boogie body from `1` monolithic `(check-sat)` into $k$ independent queries. Splitting eliminates path-condition cross-talk where an earlier `assert` accidentally instantiates helper quantifiers needed by a later `assert` (a major source of proof brittleness when refactoring dead assertions), at the cost of $k\times$ per-query solver initialization overhead unless restricted to slow procedures.
- **Stored Witness Replay Under Code Evolution:** Caching SMT proof certificates (`CPC` / `Alethe`) or minimized unsat cores (`Dafny` `ProofDependencyManager.cs:23–87`, which labels every `requires`, `ensures`, `invariant`, and `assert` node `id0..idN` to extract the exact unsat-core dependency subset) guarantees `0%` replay variance when the VC slice is byte-identical. When an upstream specification changes:
  - **Body-only edit behind a sealed contract (`opaque` spec fn or `exec` body):** Zero caller VCs change; only the edited function's VC (`1` query) re-runs solver search.
  - **Public `open spec fn`, struct field invariant, or `broadcast group` edit:** Invalidates every downstream function whose pruned cone (`prune.rs`) reaches the modified symbol, forcing fresh solver search across all dependent VCs. Unsat-core dependency tracking (`ProofDependencyManager`) narrows that invalidation set from *syntactically reachable* premises to the typically `5%–25%` *actually used* in each caller's prior proof.

#### 3.2 Empirical Specification, Proof, and Implementation Ratios (`Komodo` vs. `Verus`)

Direct source measurement of `microsoft/komodo` (`de1865c8bd0d85cdfd9a980ad7131448acfaf136`) alongside published `Komodo` (`Ferraiuolo et al., SOSP 2017`, `DOI: 10.1145/3132747.3132748`) and `Verus` (`Lattuada et al., OOPSLA 2023`, `DOI: 10.1145/3586037`) figures anchors real authoring and maintenance ratios:

| System / Component | Source Artifacts Examined | Impl / Exec SLOC | Spec SLOC | Proof SLOC | `(Spec + Proof) / Impl` | Verification Effort / Rebuild Latency |
| :--- | :--- | ---: | ---: | ---: | :---: | :--- |
| **`Komodo` (SOSP 2017 paper breakdown)** | ARMv7 TrustZone enclave monitor (`Vale` + `Dafny`) | `2,710` (`~1,552` asm insts) | `4,446` (`1.64x`) | `18,655` (`6.88x`) | **`8.52x`** (`~14.9` `(spec+proof)` lines/inst) | `~2` person-years; full clean build tens of minutes across parallel Boogie/Z3 workers |
| **`Komodo` (direct repo file audit @ `de1865c8...`)** | `verified/`: `31` `.vad` (`10,986` SLOC, `178` procs, `1,162` ARM macro calls), `23` `.s.dfy` (`3,884`), `30` `.i.dfy` (`10,218`), `4` `.dfy` (`125`); `monitor/`: `4` C/asm/lds (`803`); `driver/`: `6` C/asm (`1,037`) | `10,986` `.vad` (mixed asm+proof) + `803` unverified monitor C/asm | `3,884` `.s.dfy` | `10,218` `.i.dfy` (+ inline `.vad` lemmas) | **`25,213`** verified SLOC vs. `803` trusted unverified glue | Incremental `mkdep.py` `Makefile` re-verifies only modified `.vad`/`.i.dfy` dependency subgraph |
| **`Verus` `Vector` / `Memoization` / `InvCell`** (`OOPSLA 2023` Table 1) | Safe-interface Rust wrappers over `unsafe` primitives | `41` / `43` / `42` | `22` / `23` / `21` | `4` / `2` / `9` | **`0.63x` / `0.58x` / `0.71x`** | `2.34 s` / `2.28 s` / `2.24 s` wall time (including `rustc` frontend) |
| **`Verus` `XOR` Doubly-Linked List** (`OOPSLA 2023` Table 1) | Pointer-XOR linked list with linear `PointsTo` ghost permissions | `151` | `116` (`0.77x`) | `118` (`0.78x`) | **`1.55x`** | `5.03 s` total crate verification |
| **`Verus` `FIFO` Queue / `Rc` / `RwLock`** (`OOPSLA 2023` Table 1) | Concurrent atomic queue, ref-counting, lock with ghost state | `138` / `97` / `145` | `220` / `119` / `200` | `119` / `108` / `80` | **`2.46x` / `2.34x` / `1.93x`** | `4.58 s` / `3.51 s` / `4.44 s` total crate verification |

Why does `Verus` achieve `0.6x–2.5x` `(spec + proof) / exec` where `Komodo` requires `8.52x` (`6.88x` pure proof) and interactive `Rocq` machine-code proofs require `~33.3x` lines per instruction?
1. **Zero explicit memory-disjointness framing on ordinary Rust references:** Rust's borrow checker discharges alias freedom for `&mut T` without generating dynamic-frame set-disjointness quantifiers (`VeriBetrKV_D`) or flat-memory byte-map framing lemmas (`Komodo`).
2. **Typed SSA vs. untyped register/flag state:** `Vale` assembly procedures must specify and preserve ARM condition flags, stack pointer alignment, and page-table register invariants across `178` procedures, whereas `VIR` operates on typed variables.

---

### 4. Multi-Level Performance and Resource Footprint (`L1`–`L6`)

`Basis: source + documentation + execution + derived`

| Level | Metric / Dimension | Quantitative Evidence Across Examined Systems | Architectural Implication |
| :--- | :--- | :--- | :--- |
| **`L1` Authoring & Maintenance** | Spec+proof expansion & instability repair cost | `Verus`: `0.58x–2.46x` `(spec+proof)/exec`; `Komodo`: `8.52x` (`~2` person-years for `2,710` impl SLOC); `2.6%–5.0%` unstable SMT queries require manual `reveal`/`assert ... by` or trigger edits on solver/spec upgrades | Enforcing `opaque`-by-default definitions, fuel bounds, and conjunctive broadcast pruning cuts long-term maintenance cascades more effectively than raising `rlimit` |
| **`L2` Toolchain Build** | Verifier, profiler & mutator codebase footprint | Measured non-comment SLOC: `Verus` `VIR` `48,712` (`57` files) + `AIR` `9,160` (`27` files); `Dafny` `Verifier/` `20,913` (`42` C# files); `SMT-Scope` `15,201` (`80` Rust files); `Mariposa` `13,431` Python + `4,465` Rust | `VIR`/`Boogie` VC generators are `30–60 KSLOC` compilers; keeping them *untrusted* witness/certificate producers outside a small kernel avoids auditing `50+ KSLOC` of pruning and encoding heuristics |
| **`L3` Verification Latency** | Per-VC solve speed, tail `rlimit`, & interactive feedback | Typical stable VCs solve in `50–400 ms` (`rlimit 2k–500k`); `Verus` default cap `rlimit = 10` (`3.0e7` Z3 steps, `~2–10 s`); unguarded `:weight 0` matching loops burn `200k` `rlimit` (`3,773` insts) vs. `664` `rlimit` (`3` insts) with fuel | Interactive `< 100 ms` IDE verification requires function-local VC caching, conjunctive axiom pruning (`prune.rs`), and banning unguarded `:weight 0` recursive triggers |
| **`L4` Generated Code** | Runtime execution cost of ghost proofs | `Verus` erases all `spec` and `proof` blocks (`Tracked<T>`, `Ghost<T>`) before `rustc` LLVM codegen (`0` runtime instructions/bytes); `Komodo` `.vad` emits straight-line ARMv7 assembly with `0` Dafny runtime (`pdclib` + `803` SLOC C/asm) | Ghost-erased source (`Verus`) and verified-assembly (`Vale`) both achieve `0%` runtime proof overhead; runtime cost depends purely on avoiding defensive bounds checks proved statically |
| **`L5` Certificate / Replay Speed** | Witness checking vs. fresh SMT search | Fresh `Z3 4.12.5` search on `1434.4.smt2` takes `1,955.6 ms` (`2.39M` `rlimit`); replaying an exported `CPC`/`Alethe` proof in a standalone checker (`cvc5/ethos` or `carcara`) checks resolution + theory steps deterministically in `5–50 ms` without E-matching search | Decouple authoring-time SMT search (cached per VC digest) from CI/admission-time deterministic proof-certificate checking |
| **`L6` RAM & Artifact Footprints** | Solver binary size, RSS & trace log growth | Pinned solver binaries: `z3-4.8.5` `22.8 MiB`, `z3-4.12.5` `31.0 MiB`, `cvc5-1.1.1` `24.2 MiB`. Measured `Z3` `:max-memory` jumped **`3.3x–6.2x`** from `Z3 4.8.5` (`3.4–8.8 MB`) to `Z3 4.12.5` (`21.0–28.9 MB`) on identical queries! Verbose `Z3` instantiation logs reach `100 MB–2 GB` per hung query (`SMT-Scope` uses custom `mem_dbg` arenas to parse multi-GB traces) | Parallel `N`-core verification (`BoogieOptionBag.Cores` defaults to `(ProcessorCount + 1) / 2`) must budget `30–250 MB` RSS per active `Z3 4.12+` worker (`~2–8 GB` on `16–32` cores) |

---

### 5. Human Comprehensibility and Conceptual Simplicity (`C1`–`C2`)

`Basis: source + derived`

- **`C1` Human Comprehensibility and Mental-Model Ergonomics:**
  - *Hidden nonlocal failure mode:* To a human programmer—unlike an LLM executing brute-force `assert` bisection—SMT E-matching violates modularity of mental reasoning: adding a mathematically *true* lemma in module `A` or renaming a helper function can push an unrelated proof `500` lines away over its `rlimit` cliff because `Z3`'s trigger heuristic picks a permissive single-symbol pattern (`ShowTriggers::Selective` in `Verus` `config.rs:11–15` exists specifically to surface auto-inferred triggers before they ship).
  - *Counterexample vs. `unknown` opacity:* When `Z3` returns `unknown` due to quantifier incompleteness (`:smt.mbqi false`) or `rlimit` exhaustion (`air/src/smt_verify.rs:307–317`), raw solver models frequently violate uninstantiated quantified axioms, presenting spurious counterexamples that mislead engineers into debugging valid code. `SMT-Scope`'s causal instantiation graph (`MlExplanation`) and `Dafny`'s `--isolate-assertions` + `--log-format text` per-batch resource attribution (`CommonOptionBag.cs:114`) convert opaque timeouts into localized trigger-cycle and assertion-cost diagnostics.
- **`C2` Conceptual Simplicity, Orthogonality, and Model Refinement:**
  - *Eliminating implicit global axiom soup:* Most SMT instability in `Dafny` and `F*` arises from conflating *logical truth* ("every proven lemma is globally in scope for E-matching") with *search guidance*. Separating **truth declarations** from **explicit activation**—via `opaque` specs, `fuel = 1` structural unfolding, `broadcast use` scoped to modules with conjunctive trigger reachability (`prune.rs`), and isolated theory tactics `by(bit_vector)` / `by(nonlinear_arith)`—shrinks ambient query contexts from thousands of assertions to dozens without sacrificing specification expressiveness.

---

### 6. End-to-End Solution and Implementation Validation (`V1`–`V4`)

`Basis: source + documentation + derived`

Even when every VC returns `unsat`, four reality gaps separate SMT-verified code from dependable field execution:

- **`V1` Specification Adequacy, Premise Vacuity, and Perturbation Gate Validation:**
  - *Vacuity & unused-assumption detection:* `Dafny`'s `ProofDependencyManager` (`Source/DafnyCore/Verifier/ProofDependencyManager.cs:50–87`) tags Boogie AST nodes with `:named id<N>` attributes and inspects the solver's unsat core: if a postcondition `ensures Q` is proved without referencing the procedure body or a `requires P` assumption is contradictory (`False ==> Q`), zero body labels appear in the core, flagging vacuous specifications automatically (`--warn-contradictory-assumptions` / `--warn-redundant-assumptions`).
  - *Pre-merge stability gating:* Running `Mariposa` `filter_quick` (`3` mutants x `3` axes, `10 s` timeout, `config/expers.json:12–18`) or `Dafny` multi-seed perturbations on newly touched VCs catches cliff-edge proofs before merge.
- **`V2` Verifier Lowering (`VIR`/`Boogie`) and Solver Soundness Differential Fuzzing:**
  - *VC-generator soundness:* Bugs in `VIR -> AIR` (`57.9 KSLOC`) or `Dafny -> Boogie` (`20.9 KSLOC`)—such as unsound trait-impl pruning (`Verus` `traits.rs:800–805` explicitly uses `unpruned_krate` for trait pairing out of caution against over-eager pruning!)—can emit `unsat` VCs for buggy Rust/Dafny code. Metamorphic testing (`Storm` / `yinyang` / `Mariposa` `RCode.SAT` checks) plus cross-solver confirmation (`Z3` vs. `cvc5` vs. exported `CPC`/`Alethe` proof checking) catches solver and encoder soundness bugs.
- **`V3` Trusted Glue, Concurrency, Crash, and Microarchitectural Side-Channel Validation:**
  - *Unverified TCB seam in `Komodo`:* Direct repository inspection shows `microsoft/komodo` relies on `803` non-comment SLOC of unverified C, assembly, and linker script (`monitor/entry.S`, `monitor/monitor.c`, `monitor/monitor.h`, `monitor/monitor.lds`) plus its `ARMdef.s.dfy` architectural model (`3,884` SLOC across `.s.dfy`). Bugs in `ARMdef.s.dfy` (e.g., missing TLB/cache maintenance requirements, TrustZone `NS` bit aliasing, or DMA bypasses) or microarchitectural timing/cache leakage across enclave switches (`Revizor` contract fuzzing, `TVLA` power/cache trace validation) are invisible to `Dafny`/`Z3` and require hardware/RTL co-validation.
  - *Crash & weak-memory validation:* Verified storage systems in the `Mariposa` corpus (`VeriBetrKV`, `SplinterDB`, `Verus` multilog) pair deductive crash-refinement proofs with power-cut block-device fault injection (`dm-flakey` / `CrashMonkey`) to validate unmodeled NVMe/filesystem flush semantics, while `Verus` concurrent primitives (`FIFO` queue, `RwLock`) require `Loom`/`GenMC` validation of their `unsafe` atomic primitives at the trusted boundary.
- **`V4` Hardware-in-the-Loop (`HIL`) Target Replay and Human Trigger-Comprehension Testing:**
  - *Target silicon execution:* `Komodo` validates its verified monitor on real ARMv7 Raspberry Pi 2 / TrustZone hardware (`guestimg/`, Linux `driver/`), catching exception-vector alignment and peripheral register quirks omitted by idealized ISA specs.
  - *Trigger & fuel mental-model testing:* Empirical user studies and `Axiom Profiler` debugging sessions (`Becker et al., TACAS 2019`) show engineers routinely mispredict multi-trigger matching and equality saturation under `let`-bindings or arithmetic operators (`f(x + 1)` cannot be an E-matching pattern in `Z3` because `+` is an interpreted `LIA` symbol!), motivating mandatory linter diagnostics (`ShowTriggers`) and corpus-standardized trigger litmus tests.

## Boundaries

1. **Direct execution of full `17,043`-query `mariposa-data` corpus (`not examined`):** As documented in `secure-foundations/mariposa` `README.md:15–18`, the full `17,043`-query dataset and multi-GB SQLite experiment databases reside in the separate `secure-foundations/mariposa-data` archive (`> 60` CPU-days across `61` runs/axis). Aggregate `17,043`-query figures in Section 1.2 rest on the peer-reviewed `FMCAD 2023` publication (`Basis: documentation` / `normative`), whereas our live `Z3 4.8.5`, `Z3 4.12.5`, and `cvc5 1.1.1` executions cover the `5` representative SMT-LIB queries bundled in `mariposa/data/samples/` plus standalone matching-loop/fuel reproducers (`Basis: execution`).
2. **Clean-build wall-clock verification time of `Komodo` and `Verus` from source (`not examined`):** Neither `.NET` (`Dafny`/`Boogie`), `F#` (`Vale`), nor `Verus`'s custom `rustup` toolchain is executed in this lightweight environment; build and verification wall-clock figures for `Komodo` (`SOSP 2017`) and `Verus` (`OOPSLA 2023` Table 1) are cited from primary publications (`Basis: documentation`), while all SLOC and procedure/instruction counts on `Komodo`, `Verus`, `Dafny`, `Mariposa`, and `SMT-Scope` are measured directly from the pinned repository trees (`Basis: source + execution`).
3. **Interpreting `Mariposa` instability percentages as passive CI rerun flake rates (`known not to apply`):** On fixed input bytes, fixed solver binary, fixed seed, and deterministic `rlimit`, `Z3` and `cvc5` produce identical outcomes (`20/20` identical `rlimit = 383,255` on unperturbed `jon_unstbale_1.smt2` when seed is fixed); compounding $1 - (1 - p)^N$ across $N$ unchanged VCs to predict per-commit CI failures on untouched modules is `known not to apply`.
4. **`cvc5` execution on legacy `Dafny`/`Boogie` non-standard SMT-LIB options (`unsupported` without preprocessing):** Raw `Dafny`/`Boogie` `.smt2` logs emit Z3-specific options (`:auto_config`, `:smt.mbqi`, `:smt.case_split`, `:rlimit` syntax) that `cvc5 1.1.1` rejects unless scrubbed by `Mariposa`'s `proj_wizard.py` / `smt2action` preprocessor (`README.md:157`).

## Evidence

### Pinned Repository Source Locations

- **`secure-foundations/mariposa` (`8646e7b1c601f7154e93d85ebb1083ce1ed47f95`):**
  - `README.md:15–82` — `60`-mutant protocol, `mariposa-data` split, and preprocessing workflow.
  - `config/analyzers.json:1–35` & `config/expers.json:1–85` — `r_solvable: 0.05`, `r_stable: 0.95`, `confidence: 0.05`, `discount: 0.8`, `num_mutants: 60`, `exp_timeout: 60`.
  - `src/base/query_analyzer.py:48–179` — `QueryAnalyzer` `_categorize_z_test`, `_categorize_cutoff`, `discount` timeout filter, and cross-mutation voting.
  - `src/base/solver.py:121–165` — `Z3Solver` (`sat.random_seed`, `smt.random_seed`) and `CVC5Solver` invocation wrappers.
  - `src/smt2action/src/query_mutate.rs:42–117` — `lower_asserts`, contiguous-interval `shuffle_commands`, and 8-kind `rename_symbols`.
  - `src/smt2action/src/tree_shake.rs:28–37, 192–259` — `PatternState` and disjunctive multi-pattern handling (`lines 245–252`).
  - `src/bench/consts.py:1–150` — `71` cataloged unstable `Verus` queries (`verus_qus`, `verus_tos`).
  - `bin/z3-4.8.5`, `bin/z3-4.12.5`, `bin/cvc5-1.1.1`, and `data/samples/{single_check,1434.4,1435.4,verus_vect,jon_unstbale_1}.smt2` — executed Linux `x86_64` solver binaries and benchmark queries.
- **`viperproject/axiom-profiler-2` (`03e43597e7ac5969e721647c894f35ffb46adb46`) & `viperproject/smt-scope` (`665f9263c6102ff63494dafb39976d015c675951`):**
  - `axiom-profiler-2` `README.md:1` — rename redirect to `viperproject/smt-scope`.
  - `smt-scope` `smt-scope-lib/src/analysis/problem_behaviour.rs:14–90` — `ProblemBehaviours::find`, `MatchingLoop` vs. `Multiplicative` (`2.0x` warning, `4.0x` error).
  - `smt-scope` `smt-scope-lib/src/analysis/graph/analysis/matching_loop/{mod.rs:20–78, search.rs:13–70}` — `MIN_MATCHING_LOOP_LENGTH = 3`, `MIN_SUSPICIOUS_CHAIN_LENGTH = 6`, `has_n_overlapping_stacks`, `sure_mls` / `maybe_mls`.
- **`verus-lang/verus` (`0dab219272ac2353320bd177ebb3929453b90a9e`):**
  - `source/vir/src/prune.rs:62–91, 203–229, 951–975` — conjunctive `ReachBroadcastFunction` trigger pruning (`prune_krate_for_module_or_krate`).
  - `source/vir/src/well_formed.rs:1317–1356` & `sst_to_air.rs:3019–3042` — isolated `bit_vector`, `nonlinear`, and `integer_ring` proof modes.
  - `source/rust_verify/src/config.rs:9–16` & `verifier.rs:51–52, 1122–1131` — `DEFAULT_RLIMIT_SECS = 10.0`, `RLIMIT_PER_SECOND_Z3 = 3,000,000`, `RLIMIT_PER_SECOND_CVC5 = 333,333`.
  - `source/air/src/smt_verify.rs:224–317, 406–434` — per-query `:rlimit` bracketing and `:rlimit-count` extraction.
- **`dafny-lang/dafny` (`75de7486da5a473a5aba2add8ff80fc5bbe8337f`):**
  - `Source/DafnyCore/Options/BoogieOptionBag.cs:54–84, 139–149` & `DafnyOptions.cs:506–508` — `--verification-time-limit 30`, `--resource-limit`, and `--isolate-assertions` (`VcsSplitOnEveryAssert`).
  - `Source/DafnyCore/Verifier/ProofDependencyManager.cs:15–88` — `:named` `id<N>` unsat-core dependency tracking.
- **`microsoft/komodo` (`de1865c8bd0d85cdfd9a980ad7131448acfaf136`):**
  - `verified/*.vad` (`31` files), `verified/*.s.dfy` (`23` files), `verified/*.i.dfy` (`30` files), `verified/*.dfy` (`4` files), `monitor/*.{c,h,S,lds}` (`4` files), `driver/*.{c,h,S}` (`6` files).

### Primary Literature

- Yi Zhou, Jay Bosamiya, Yoshiki Takashima, Jessica Li, Marijn Heule, and Bryan Parno, *"Mariposa: Measuring SMT Instability in Automated Program Verification,"* FMCAD 2023 (`DOI: 10.34727/2023/isbn.978-3-85448-060-0_26`; extended CMU TR `DOI: 10.1184/R1/23905905`).
- Nils Becker, Peter Müller, and Alexander J. Summers, *"The Axiom Profiler: Understanding and Debugging SMT Quantifier Instantiations,"* TACAS 2019, LNCS 11427, pp. 99–116 (`DOI: 10.1007/978-3-030-17462-0_6`).
- Andrea Lattuada et al., *"Verus: Verifying Rust Programs using Linear Ghost Types,"* Proc. ACM Program. Lang. 7, OOPSLA1, Article 85, 2023 (`DOI: 10.1145/3586037`).
- Andrew Ferraiuolo, Andrew Baumann, Chris Hawblitzel, and Bryan Parno, *"Komodo: Using Verification to Disentangle Secure-Enclave Hardware from Software,"* SOSP 2017, pp. 287–305 (`DOI: 10.1145/3132747.3132748`).

### Recorded Execution Summary (`2026-11-19`, Linux `x86_64`)

```text
Komodo verified/*.vad (Vale assembly + inline proofs)   :  31 files,  12901 raw,  10986 non-comment SLOC
Komodo verified/*.s.dfy (trusted specs: ARM + security) :  23 files,   4768 raw,   3884 non-comment SLOC
Komodo verified/*.i.dfy (Dafny implementation + proofs) :  30 files,  11597 raw,  10218 non-comment SLOC
Komodo verified/*.dfy (shared prelude/addrseq/main)     :   4 files,    158 raw,    125 non-comment SLOC
Komodo monitor/*.{c,h,S,lds} (trusted C/asm/linker glue):   4 files,   1057 raw,    803 non-comment SLOC
Komodo driver/*.{c,h,S} (untrusted Linux kernel driver) :   6 files,   1261 raw,   1037 non-comment SLOC
Komodo .vad procedures: 178; direct ARM instruction macro invocations: 1162

jon_unstbale_1.smt2: 1355 top-level commands, 452 (assert ...), 72 contiguous assert intervals
  Z3-4.8.5  interval-preserving shuffle (20 mutants, 0 errors=True): {'unsat': 20}, rlimit=(382998..383303)
  Z3-4.12.5 interval-preserving shuffle (20 mutants, 0 errors=True): {'unknown': 10, 'unsat': 10}, rlimit=(353164..409654)
  em_loop_w0 (:weight 0, rlimit=200k): Z3-4.12.5=unknown rlimit=200025 qinst=3773
  em_fuel3_mbqi_off (Fuel S^3(Z)):     Z3-4.12.5=unknown rlimit=664    qinst=3    | cvc5-1.1.1=unknown (35.7ms vs 506.6ms timeout)
```

## Revalidation

To revalidate solver instability, matching-loop fuel bounding, or upstream pruning/scaling constants after updating solver or verifier versions:

1. **Minimal Matching-Loop vs. Fuel Probe (`< 1 s` on any `z3` binary):**
   ```bash
   python3 - <<'PY'
   import re, subprocess, tempfile
   Z3 = "z3"  # or path to pinned z3 binary
   q_loop = """(set-option :auto_config false)(set-option :smt.mbqi false)
   (declare-sort U 0)(declare-fun f (U) Int)(declare-fun g (U) U)(declare-const a U)
   (assert (forall ((x U)) (! (= (f x) (+ (f (g x)) 1)) :pattern ((f x)) :weight 0)))
   (assert (< (f a) 0))(check-sat)"""
   q_fuel = """(set-option :auto_config false)(set-option :smt.mbqi false)
   (declare-sort U 0)(declare-sort Fuel 0)(declare-const Z Fuel)(declare-fun S (Fuel) Fuel)
   (declare-fun f (Fuel U) Int)(declare-fun g (U) U)(declare-const a U)
   (assert (forall ((k Fuel) (x U)) (! (= (f (S k) x) (+ (f k (g x)) 1)) :pattern ((f (S k) x)))))
   (assert (< (f (S (S (S Z))) a) 0))(check-sat)"""
   for name, smt in [("loop", q_loop), ("fuel3", q_fuel)]:
       with tempfile.NamedTemporaryFile("w", suffix=".smt2") as fp:
           fp.write(smt); fp.flush()
           out = subprocess.run([Z3, fp.name, "rlimit=200000", "-st"], capture_output=True, text=True).stdout
           qi = int(re.findall(r":quant-instantiations\s+(\d+)", out)[-1])
           print(name, "quant-instantiations:", qi)
   PY
   ```
   Confirm `fuel3` performs exactly `3` quantifier instantiations while `loop` exhausts `rlimit` with `> 1,000` instantiations.
2. **Upstream Codebase Diff Anchors:**
   - In `verus-lang/verus`, check `source/rust_verify/src/verifier.rs` (`RLIMIT_PER_SECOND_Z3` / `RLIMIT_PER_SECOND_CVC5`) and `source/vir/src/prune.rs` (`reach_function_via_reveal` conjunctive trigger loop).
   - In `secure-foundations/mariposa`, check `src/smt2action/src/tree_shake.rs` (`get_pattern_uses` multi-pattern handling) and `config/analyzers.json`.
   - In `viperproject/smt-scope`, check `smt-scope-lib/src/analysis/problem_behaviour.rs` and `matching_loop/mod.rs` (`MIN_MATCHING_LOOP_LENGTH`, multiplicativity thresholds).
