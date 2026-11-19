# Proof Fragility, SMT Solver Instability, and Verification Scaling Walls

## Summary

Machine-checked verification degrades superlinearly at scale along four coupled engineering walls, each admitting verified architectural mitigations:

1. **SMT solver instability and context pollution**: Across 17,043 queries from six Dafny, F*, and Serval systems, Mariposa (FMCAD 2023) measured **2.6%** of queries unstable on Z3 4.12.1 (up to **5.01%** on `KomodoD` vs. **0.52%** on decidable `KomodoS`), with assertion shuffling catching **36.9%** of unstable `KomodoD` queries uniquely vs. **3.9%** for PRNG reseeding. Between Z3 4.8.5 and 4.8.8, **67.4%** of 285 stability regressions traced to two commits totaling **26 added lines** altering flattened-disjunction sort order. SHAKE (FMCAD 2024) established that **96%–99%** of query assertions are absent from unsat cores and irrelevant context causes **78%** of observed instability; lazy pattern-aware $O(DN)$ pruning cuts instability by **29%** on Z3 4.12.5 and **41%** on cvc5 1.1.1 while boosting cvc5 solved queries by **+8.92%** (default) to **+18.10%** (oracle).
2. **E-matching loops and verifier-layer isolation**: Z3's `qi_queue` schedules matches via default cost `(+ weight generation)` against an eager threshold, leaving equal-cost ties sensitive to assertion order and PRNG state. Local single-quantifier filters (e.g., Verus's `remove_obvious_potential_loops`) catch direct self-loops (`P(x) -> P(succ(x))`) but miss mutual cycles (`f(x) -> g(succ(x))`, `g(y) -> f(h(y))`). Verifier-layer controls—Peano fuel (`default = 1`), `#[verifier::opaque]`/`reveal`/`hide`, minimal conservative triggers, module reachability pruning (`prune.rs`), `#[verifier::spinoff_prover]`, `assert(F) by { P }`, and isolated `by(nonlinear_arith)`/`by(bit_vector)`/`by(compute)` modes—shrank Verus SOSP 2024 SMT payloads **20.7×–93.8×** and accelerated single-core verification **10.9×–64.1×** over Dafny baselines.
3. **Interactive proof fragility and repair**: Procedural tactic scripts break under definition/IR edits because they target implicit proof states (generated hypothesis names, subgoal indices, global `simp` sets; *QED at Large*, 2019). Declarative milestones (`Isar`, `have`/`calc`), Why3's checksum + formula-shape XML proof sessions (VSTTE 2013), `iCoq` regression proof selection (ASE 2017), and PUMPKIN Pi's axiom-free proof-term transport across type equivalences `((DepConstr, DepElim), (Eta, Iota))` with Ltac decompilation (PLDI 2021) contain refactoring blast radius without enlarging the kernel.
4. **Operational state-plumbing vs. soundness-proved functional lifting**: Verifying directly against small-step imperative/MIR states couples proofs to compiler noise (`StorageLive`/`StorageDead`, spill temps, step fuel). Aeneas (ICFP 2022) removes memory plumbing for safe Rust via LLBC loans and forward/backward functions, but places `Charon` and its OCaml translator inside the TCB. AutoCorres (PLDI 2014) keeps its five-stage local-variable, heap, word, and monad lifting **outside the TCB** via per-function kernel-checked `ac_corres` proofs (25%–53% fewer spec lines, 40%–61% smaller terms). Combining alias-erasing lens lifting with per-function refinement validation preserves a small-step TCB while achieving **100%** proof invariance under benign IR churn (`support/verify_trigger_loops_and_lifting.py`).

## Applicability

This report covers scaling walls and architectural mitigations across SMT verifiers (Dafny, F*, Verus, Why3, Z3, cvc5) and interactive theorem provers (Isabelle/HOL + AutoCorres, Coq/Rocq + PUMPKIN Pi, Lean/F*/Coq + Aeneas). The pinned subjects in `REPORT.json` relate as follows:

- **SMT instability & pruning**: `Mariposa` (FMCAD 2023), `SHAKE` (FMCAD 2024), and `secure-foundations/mariposa` (`8646e7b1c601f7154e93d85ebb1083ce1ed47f95`) provide statistical instability definitions, Z3 bisection data, Verus system reports (`doc/reports/`), and SMT-LIB mutation/pruning source.
- **SMT internals & profiling**: `Z3Prover/z3` (`437536cd64a544a1c329fc57d83e56e294fdf47c`) documents `mam.cpp` and `qi_queue.cpp`; `viperproject/smt-scope` (`665f9263c6102ff63494dafb39976d015c675951`, successor to Axiom Profiler 2) covers instantiation-trace debugging.
- **Verifier-layer mitigations**: `Verus` (OOPSLA 2023, SOSP 2024) and `verus-lang/verus` (`a95764f23c6876b47500beda6118e2d142a87cc3`) document fuel, opacity, conservative triggers, reachability pruning, solver spinoff, and theory isolation.
- **Proof fragility, repair & sessions**: *QED at Large* (FnTPL 2019), `PUMPKIN Pi` (PLDI 2021) + `uwplse/pumpkin-pi` (`a7743d4665d8c7a0ebfd9d39e1247ee7804d402b`), and `Why3` proof sessions (VSTTE 2013).
- **Functional lifting vs. TCB boundary**: `AutoCorres` (PLDI 2014) + `seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`) contrasted with `Aeneas` (ICFP 2022) + `AeneasVerif/aeneas` (`8f4466db9f0d59267b8e76b54473a21a005cf7be`), plus executable verification in `support/verify_trigger_loops_and_lifting.py`.

### Cross-References to Adjacent Corpus Packages

Consult adjacent packages for non-overlapping domain details: `verified-compiler-effort-precedents-and-agent-proof-productivity` (CompCert/CakeML/seL4 effort baselines), `compcert-sel4-everest-pass-composition-and-proof-maintenance` (multi-pass refinement composition & maintenance), `dafny-boogie-viper-fstar-why3-and-vc-obligation-architectures` (VC-generation & error-localization architectures), `anneal-fuel-free-mir-lifting-and-alias-erasure` (Rust-MIR fuel-free lens lifting & Tree Borrows pinning), `smt-sat-alethe-carcara-and-numerical-proof-certificate-reconstruction` (Alethe/Carcara & LRAT replay), and `typeclass-insulated-layer0-coremir-and-automated-lean-proof-repair` (Lean 4 automated repair). Source-code claims apply strictly to pinned revisions; architectural principles generalize subject to **Boundaries**.

## Findings

### 1. The SMT "Butterfly Effect": Quantifying Solver Instability Across Production Corpora (Mariposa & SHAKE)

Basis: documentation + source + derived

Automated verifiers such as Dafny, F*, Boogie, Why3, and Verus compile source procedures, invariants, and ambient axioms into SMT-LIB verification condition (VC) queries discharged via refutation (`unsat`). Because first-order logic combined with arithmetic, arrays, datatypes, and quantifiers is undecidable, solvers rely on heuristic search orderings that exhibit chaotic sensitivity to semantically irrelevant query edits—a phenomenon quantified systematically by Mariposa (Zhou et al., FMCAD 2023) and diagnosed causally by SHAKE (Zhou et al., FMCAD 2024).

#### 1.1 Perturbation Mechanics and Statistical Stability Classification

In `secure-foundations/mariposa` (`8646e7b1c601f7154e93d85ebb1083ce1ed47f95`), query stability is quantified by generating semantics-preserving mutants of an SMT-LIB query $Q$ and measuring $r = \Pr[\text{solver returns }\texttt{unsat}\text{ within }T_{\text{limit}}]$:

- **Perturbations** (`src/smt2action/src/query_mutate.rs:42–117`, `config/expers.json`):
  - `shuffle` (`shuffle_commands`, `lower_asserts`): Uses `ChaCha8Rng::seed_from_u64(seed)` to permute assertions within contiguous `(assert ...)` blocks or globally immediately before `(check-sat)`.
  - `rename` (`rename_symbols`): Alpha-renames across eight SMT-LIB symbol kinds (`Variable`, `Constant`, `Function`, `Sort`, `Datatype`, `TypeVar`, `Constructor`, `Selector`) via `SymbolNormalizer` (`randomization_space = usize::MAX`).
  - `reseed`: Perturbs only the solver's PRNG seed (e.g., `smt.random_seed`).
  - `quake` (`config/expers.json:19–35`): Repeats incremental `check-sat` calls within one solver session (mirroring F*'s `--quake`).
- **Four-way classification** (`src/base/query_analyzer.py:27–180`, `config/analyzers.json`, Mariposa §III-C–E): Classifies `(Q, S)` into `unsolvable` ($r < r_{\text{solvable}}$), `unstable` ($r_{\text{solvable}} \le r < r_{\text{stable}}$), `stable` ($r \ge r_{\text{stable}}$), or `inconclusive`, using default $r_{\text{solvable}} = 0.05$, $r_{\text{stable}} = 0.95$, $\alpha = 0.05$, tolerance discount $\omega = 0.8$ (filtering queries whose passing mean exceeds $0.8 \cdot T_{\text{limit}}$), and **$60$ mutants per mutation family** (+ original = 61 runs). Under one-sided proportion z-tests (`_categorize_z_test`, lines 114–154), $n = 60$ suffices for $0/60$ to reject $r \ge 0.05$ and $60/60$ to reject $r < 0.95$ at $\alpha = 0.05$ (whereas $r_{\text{solvable}} = 1\%$ requires 269 mutants). Across mutation families (`categorize_query`, lines 156–179), `inconclusive` votes are dropped and any disagreement among remaining labels yields **`unstable`**. Mariposa uses wall-clock $T_{\text{limit}}$ (default `60s`) rather than `rlimit` because resource counters omit some theory-solver work and are incomparable across solver versions or solvers (Mariposa §III-D).

#### 1.2 Empirical Instability Across Verification Systems and Solver Upgrades

Mariposa evaluated **17,043** SMT queries across six verified systems over 578 CPU-days using Z3 4.12.1 and seven legacy Z3 versions (back to 2015), supplemented by repository reports for four newer Verus systems evaluated on Z3 4.13.0 (`secure-foundations/mariposa/doc/reports/*.txt`):

| System | Verifier / Logic Style | Source LoC | Queries | Solver & Timeout | Unstable (Core + Ext. or Count) | Key Diagnostic Observation |
| :--- | :--- | ---: | ---: | :--- | :--- | :--- |
| **KomodoD** | Dafny (general quantified VC) | 26K | 2,054 | Z3 4.12.1 (60s) | **5.01%** (8 core + 95 ext. = 103) | Excluding attestation queries absent from KomodoS: **4.27%** unstable |
| **KomodoS** | Serval / Rosette (decidable fragment) | 4K | 773 | Z3 4.12.1 (60s) | **0.52%** (2 core + 2 ext. = 4) | ~8× lower instability than comparable KomodoD subset |
| **VeriBetrKVD** | Dafny (dynamic frames B$\varepsilon$-tree) | 44K | 5,325 | Z3 4.12.1 (60s) | **2.91%** (25 core + 130 ext. = 155) | High sensitivity to assertion order and Z3 4.8.5 $\to$ 4.8.8 upgrade |
| **VeriBetrKVL** | Linear Dafny (linear heap types) | 49K | 5,600 | Z3 4.12.1 (60s) | **3.13%** (22 core + 153 ext. = 175) | Faster average queries than KVD, yet comparable instability ratio |
| **DICE\*** | F\* (measured boot protocol) | 25K | 1,536 | Z3 4.12.1 (60s) | **0.78%** (3 core + 9 ext. = 12) | F\* historically pinned to 4-year-old Z3 4.8.5 due to upgrade regressions |
| **vWasm** | F\* (Wasm sandboxing compiler) | 15K | 1,755 | Z3 4.12.1 (60s) | **0.23%** (0 core + 4 ext. = 4) | Consistently lowest instability; original query runtime tracks mutant median |
| *FMCAD'23 Total* | *6 legacy systems* | *163K* | *17,043* | *Z3 4.12.1 (60s)* | ***2.66%** (453 / 17,043; paper reports 2.6%)* | *Overall unstable ratio; up to 5.0% per project* |
| **Verus Systems** (`vsystemsnew`) | Verus (storage log, page table, mimalloc, NR) | — | 2,082 | Z3 4.13.0 (10s / 60s) | **1.59%** (33) at 10s; **1.39%** (29) at 60s | Many unstable Verus queries fail via fast `mostly_unknown` (0.04–0.21s) under `shuffle` while passing 61/61 under `rename`/`reseed` |
| **Anvil** | Verus (Kubernetes controllers) | — | 1,831 | Z3 4.13.0 (60s) | **0.05%** (1 / 1,831) | Single timeout-unstable query (`shuffle`: 11 unsat / 2 unknown / 48 timeout; `rename`/`reseed`: 61/61) |
| **SplinterDB** | Verus (verified B$\varepsilon$-tree) | — | 1,215 | Z3 4.13.0 (60s) | **0.16%** (2 / 1,215) | Both unstable queries exhibit `mostly_unknown` on `shuffle` (`0.27s`) with 61/61 pass on `rename`/`reseed` |
| **VeriSMo** (dedup) | Verus (confidential VM security monitor) | — | 2,143 | Z3 4.13.0 (60s) | **0.23%** (5 / 2,143; +3 unsolvable) | `arch__ptram__ptram_p2.smt2`: `shuffle` 32/61, `rename` 60/61, `reseed` 13/61 |

Four non-obvious failure modes emerge from this corpus:

1. **Seed randomization misses most instability**: On `KomodoD` at $T_{\text{limit}} = 60\text{s}$, **36.9%** of unstable queries were uniquely detected by `shuffle`, **6.8%** uniquely by `rename`, and only **3.9%** uniquely by `reseed` (Mariposa §IV-D). The Verus repository reports confirm an even sharper skew: across `noderep-smt-spec__cyclicbuffer.5.smt2`, `verified-storage-smt-...log__inv_v.{2,4,5,17}.smt2`, and `splinterdb/...LikesBetree.3.smt2`, `rename` and `reseed` passed `61/61` while `shuffle` flipped `20%–72%` of runs to immediate `unknown` (`0.04s–0.27s`), demonstrating that heuristic quantization/trigger search order can terminate prematurely with `unknown`—not merely timeout.
2. **Solver upgrades actively degrade stability via tiny AST-ordering changes**: Across the 1,453 git commits between Z3 4.8.5 and Z3 4.8.8, **285** previously stable queries became unstable. Automated `git bisect` with Mariposa (Mariposa Table II) blamed **115/285 (40.4%)** on a single 2-file commit (`5177cc4`, `"change lt"`, 8 additions / 2 deletions) and **77/285 (27.0%)** on a single 1-file commit (`1e770af`, `"local sort"`, 18 additions / 3 deletions). Both commits merely changed the internal sorting order of flattened disjunctions—accounting for **67.4%** of all stability regressions across 1,453 commits and explaining why F* and Dafny remained pinned to Z3 4.8.5 for roughly four years.
3. **Ecosystem overfitting blocks cross-solver migration**: In Mariposa §IV-C, cvc5 could not parse or solve any raw Dafny or F* queries due to Z3-specific SMT-LIB extensions and encoding assumptions; even after format conversion and developer-guided tuning, cvc5 solved only ~14% of `KomodoD` queries.
4. **Latent variance inside "stable" queries**: Even among queries passing 61/61 mutants within 60s, Mariposa identified **302** stable-extension queries whose mutant response-time standard deviation exceeded `6s` (and some exceeding `10s`), indicating fragility lurking just beneath the timeout cliff.

#### 1.3 Context Pollution as the Dominant Root Cause and SHAKE Pruning

In SHAKE (Zhou et al., FMCAD 2024; `secure-foundations/mariposa/src/smt2action/src/tree_shake.rs`), unsat-core analysis across Mariposa queries established that **96%–99% of assertions are absent from the unsat core** and **irrelevant context accounts for 78% of observed instability**. Rather than building an $O(N^2)$ axiom-dependency graph, SHAKE runs an $O(DN)$ ($D \le 20$ in practice) pattern-aware breadth-first layering pass (`tree_shake.rs:14–392, 410–582`, SHAKE §IV Algorithms 1–2):

1. **Lazy pattern-gated expansion** (`UseTracker`, `PatternState::check_match`, `TRYEXPAND`/`FORMULARELEVANT`): Each assertion splits top-level unquantified symbols $\phi.S_{\text{visible}}$ from outermost quantifier states $\omega$ hiding $\omega.\phi_{\text{hidden}}$ behind trigger symbol sets $\omega.\text{patterns}$. Starting from the goal's symbols $S_{\text{ctx}}$ (layer 0), an assertion activates at layer $d$ only if $\phi.S_{\text{visible}} \cap S_{\text{ctx}} \neq \emptyset$ OR some pattern group $S \in \omega.\text{patterns}$ satisfies **$S \subseteq S_{\text{ctx}}$** (mirroring E-matching's requirement that all trigger symbols appear).
2. **IDF filtering of ubiquitous symbols** (`tree_shake_idf.rs`, §IV-C): Symbols with document frequency $\text{freq}(x) = |\{\phi_i \mid x \in \text{SYMBOLS}(\phi_i)\}| / |\Gamma| > \theta$ (such as F*'s `ApplyTT`) are treated as built-ins so they cannot collapse all layers in one hop.
3. **Oracle distance cutoff** (§IV-D): Caching the unsat core's maximum layer distance from a prior passing run as a per-procedure attribute (invariant under renames/shuffling) prunes deeper irrelevant layers.

Measured impact across the five quantified Mariposa projects (SHAKE §V, Fig. 14, Z3 4.12.5 and cvc5 1.1.1):

| Metric | Z3 4.12.5 | cvc5 1.1.1 | Notes |
| :--- | :---: | :---: | :--- |
| **Instability reduction (SHAKE)** | **-29%** | **-41%** | Measured on Mariposa unstable query suites |
| **Queries solved: Baseline** | 15,479 | 7,960 | Across KomodoD, VeriBetrKVD/L, DICE\*, vWasm |
| **Queries solved: Default SHAKE** | **-0.45%** | **+8.92%** | `+73.36%` (+190 queries) on DICE\* for cvc5 |
| **Queries solved: Oracle SHAKE** | **-0.18%** | **+18.10%** | `+163.71%` (+424 queries) on DICE\* for cvc5; `+21.64%` on KomodoD |

### 2. E-Matching Internals, Matching Loops, and Trigger-Budget Pathology (Simplify, Z3, Axiom Profiler / SMT Scope)

Basis: normative + documentation + source + execution

#### 2.1 How Z3 Compiles and Schedules Quantifier Instantiations

Verification SMT solvers inherit Simplify's E-matching paradigm (Detlefs, Nelson, and Saxe, JACM 2005) compiled into code-trees inside Z3's Matching Abstract Machine (de Moura and Bjørner, CADE 2007; `Z3Prover/z3` @ `437536cd64a544a1c329fc57d83e56e294fdf47c`, `src/smt/mam.cpp`). Candidate matches flow through `smt::qi_queue` (`src/smt/qi_queue.h:42–90`, `src/smt/qi_queue.cpp:46–252`):

1. **Generation cost** (`qi_queue.cpp:46–134`): Input ground terms have generation `0`; instantiating over bindings of generation $g$ produces terms of incremented generation (`get_new_gen`). Candidate cost is evaluated over 15 runtime features (`weight`, `generation`, `instances`, `depth`, `size`, `pattern_width`, `cs_factor`, etc.), defaulting to `(+ weight generation)` (line 55).
2. **Eager/delayed thresholding & tie-breaking** (`qi_queue.cpp:164–185`): Candidates with `m_cost <= m_eager_cost_threshold` (or immediate conflicts when `m_qi_promote_unsat` is enabled) instantiate eagerly; costlier matches wait in `m_delayed_entries`. When ambient prelude axioms tie at identical `(weight, generation)`, assertion order (`m_new_entries`), E-graph representative choice, and SAT branching decide which terms fire before `resource_limits_exceeded()` (checked every 100 instantiations, lines 178–183) or `m_qi_max_instances` halts search—producing `timeout` or premature `unknown`.

#### 2.2 Formal Anatomy of Matching Loops and Trigger-Selection Asymmetries

A **matching loop** occurs when quantifier instantiation yields strictly larger ground terms that re-trigger the cycle indefinitely:

- **Direct self-amplifying loop**: $\forall x.\ \{!P(x)\}\ P(x) \implies P(\mathrm{succ}(x))$ generates $P(a), P(\mathrm{succ}(a)), \dots$ without bound; in `verus-lang/verus/source/docs/guide/src/profiling.md:13–36`, triggering on `f(x, y)` with two recursive calls `f(x+1, 2*y)` and `f(2*x, y+x)` causes $2^g$ branching.
- **Mutual multi-quantifier loop**: $\forall x.\ \{!f(x)\}\ f(x) \implies g(\mathrm{succ}(x))$ paired with $\forall y.\ \{!g(y)\}\ g(y) \implies f(h(y))$ loops via $f(a) \to g(\mathrm{succ}(a)) \to f(h(\mathrm{succ}(a))) \to \dots$ even though neither body mentions its own trigger head.
- **Multi-triggers vs. multiple triggers** (`multitriggers.md:30–106`): Adding patterns to one **multi-trigger** (`#![trigger s[i], s[j]]`) conjoins match requirements and *restricts* instantiation; adding **multiple triggers** disjoins them and *widens* fanout.
- **Why local filters miss mutual cycles**: `verus-lang/verus/source/vir/src/triggers_auto.rs:569–620` (`remove_obvious_potential_loops`) only checks single-quantifier self-matching via `structure_matches(ctxt, pure, term)` (explicitly noting at line 598: `// REVIEW: we could attempt more sophisticated cycle detection`). It catches direct self-loops but misses inter-quantifier 2-cycles; catching those requires global trigger-graph SCC analysis (Section 6) or trace profilers such as **Axiom Profiler** (Becker, Müller, and Summers, TACAS 2019), its Rust successor **SMT Scope** (`viperproject/smt-scope`), and Verus `--profile --rlimit 1`.

### 3. Architectural SMT Mitigations at the Verifier Layer (Verus, Dafny, IronFleet, F*)

Basis: documentation + source + derived

Rather than expecting SMT solvers to behave predictably on unconstrained encodings, scalable SMT-based verifiers enforce strict query hygiene at the compiler-to-SMT boundary. IronFleet (Hawblitzel et al., SOSP 2015, DOI `10.1145/2815400.2815428`) and Dafny (Amin, Leino, and Rompf, TAP 2014) pioneered fuel-bounded recursion and `{:opaque}`/`reveal` encapsulation; Verus (Lattuada et al., OOPSLA 2023 & SOSP 2024; `verus-lang/verus` @ `a95764f23c6876b47500beda6118e2d142a87cc3`) systematizes five interacting defenses directly in its VIR-to-AIR/SMT-LIB lowering:

#### 3.1 Peano Fuel Stratification and Opacity (`sst_to_air_func.rs`, `prelude.rs`)

Unconstrained recursive function axioms (`forall x. f(x) == body[f(x-1)]`) are textbook matching loops. Verus encodes every recursive `spec fn f` with a Peano `Fuel` sort (`zero`, `succ`) and a per-function boolean gate `fuel_bool(fuel%f)` (`source/vir/src/sst_to_air_func.rs:305–410`, `source/vir/src/prelude.rs:180–188`):

```smt2
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(axiom (=> fuel_defaults
  (forall ((id FuelId)) (! (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))))))

;; Recursive function f lowered with fuel stratification (sst_to_air_func.rs:338-343):
(declare-const fuel_nat%f Fuel)
(axiom (forall (... fuel) (= (rec%f ... fuel) (rec%f ... zero))))
(axiom (forall (... fuel) (= (rec%f ... (succ fuel)) body[rec%f ... fuel])))
(axiom (=> (fuel_bool fuel%f)
           (forall (...) (= (f ...) (rec%f ... (succ fuel_nat%f))))))
```

Because `rec%f ... (succ fuel)` unfolds strictly to `rec%f ... fuel`, each unfolding strips one `succ` constructor; absent a `reveal_with_fuel(f, n)` statement, default fuel is **1** (`reference-reveal-hide.md:28–32`). Marking a non-recursive or recursive specification function `#[verifier::opaque]` suppresses the global `(axiom (fuel_bool_default fuel%f))`, leaving `f` completely uninterpreted until locally revealed via `reveal(f)` or `reveal_with_fuel(f, n)`—distinct from `closed spec` (which controls module-boundary abstraction rather than intra-module solver unfolding; `opaque.md:11–16`). Conversely, `hide(f)` suppresses unfolding within a proof scope.

#### 3.2 Conservative Trigger Inference (`triggers.rs`, `triggers_auto.rs`)

Whereas Dafny historically defaults to selecting multiple broad triggers to maximize out-of-the-box automation on small examples, Verus explicitly chooses **as few triggers as possible** (Verus SOSP 2024 §3.1) to prevent instantiation blowup at scale:

- `compute_triggers` (`source/vir/src/triggers_auto.rs:648–706`) solves a minimum-set-cover problem over bound variables, first preferring triggers with the fewest pattern terms, then breaking ties via a 5-tuple lexicographic `Score` (`triggers_auto.rs:170–186, 635–646`): `(num_operators, num_special, no_calls, depth, size)` (preferring pure function calls adjacent to logical operators/`==` over arithmetic/bit-ops and smaller terms).
- When `AutoType::Auto` relies on the heuristic `Score` to break a tie between distinct minimal covers, Verus sets `low_confidence = true` (`triggers_auto.rs:630–632, 829`) and emits an advisory prompting the user to inspect or manually pin `#![trigger ...]`.
- Manual triggers are stored in a `BTreeMap<Option<u64>, Vec<Exp>>` (`source/vir/src/triggers.rs:21–22`) specifically for deterministic sortedness stability across runs.

#### 3.3 Context Pruning, Solver Spinoff, and Scoped Subproofs (`prune.rs`, `spinoff_prover.md`, `assert_by.md`)

- **Static module-level reachability pruning** (`source/vir/src/prune.rs:69–90, 966–1387`): Before emitting AIR/SMT-LIB for a module, Verus executes a fixed-point reachability worklist over `function_map`, `datatype_map`, `trait_impl_map`, `reveal_group_map`, `opaque_ty_map`, and `fun_revealed_broadcast_map`, stripping unreachable definitions, unrevealed opaque bodies (`lines 1146–1156`), and broadcast lemmas whose trigger functions/types are never reached.
- **Per-function solver isolation** (`source/docs/guide/src/spinoff_prover.md:5–21`): By default, Verus runs one SMT solver process per Rust module, exposing every function in the module to sibling functions' facts and risking cross-function flakiness. Annotating a function with `#[verifier::spinoff_prover]` launches a fresh solver instance pruned to that function alone—improving stability and enabling function-level parallelism (e.g., running one 1.0s function alongside nine 0.1s functions cuts module wall time from 1.9s to ~1.0s) at the cost of repeating shared prelude setup.
- **Lexically scoped proof hiding** (`source/docs/guide/src/assert_by.md:14–34`): `assert(F) by { P }` encodes `(A && B ==> F) && (A ==> G)` rather than leaking `P`'s intermediate quantifiers `B` into subsequent obligations `G`, achieving local context isolation without manually factoring out helper lemmas and threading `requires` parameters.

#### 3.4 Theory Isolation: Disabling Ambient Nonlinear Arithmetic, Bit-Vectors, Compute, and EPR

Mixing undecidable nonlinear integer arithmetic (`*`, `div`, `mod` over symbolic variables) or bit-vector theories with quantified axioms causes severe Z3 instability. Verus isolates expensive theories behind explicit boundaries (`source/vir/src/prelude.rs:773–855`, `nonlinear.md`, `reference-prover-mode-bit-vector.md`, `reference-prover-mode-compute.md`, Verus SOSP 2024 §3.2–3.3):

1. **Default linear mode (`smt.arith.nl=false`)**: Verus disables Z3's nonlinear arithmetic engine globally and wraps `*`, `div`, and `mod` behind uninterpreted functions `Mul`, `EucDiv`, `EucMod` (with minimal axioms such as `0 <= x && 0 <= y ==> 0 <= Mul(x, y)`), noting in `prelude.rs:773–775` that raw `smt.arith.nl=false` can otherwise fail even on `P ==> P` when `*`/`div`/`mod` appear.
2. **Isolated sub-queries**:
   - `assert(Q) by(nonlinear_arith) requires P;`: Sends only `P ==> Q` (stripped of ambient context) to Z3 with nonlinear arithmetic enabled.
   - `assert(Q) by(bit_vector) requires P;`: Encodes fixed-width integers (`u64`, `i64`, `usize`, plus bitwidth-bounded `int`/`nat` expressions like `u64 + u64` in 65 bits) directly into SMT bit-vectors; all ambient `let` bindings are hidden unless explicitly passed in `requires P`. For architecture-dependent `usize`/`isize` without a `global` size directive, Verus generates separate 32-bit and 64-bit queries (`reference-prover-mode-bit-vector.md:61–65`).
   - `assert(Q) by(compute_only);` / `by(compute);`: Discharges ground or statically reducible obligations (e.g., precomputed CRC-32 lookup tables that caused SMT solvers to choke) via an internal symbolic interpreter with optional `#[verifier::memoize]` caching (`reference-prover-mode-compute.md:11–55`).
   - **Selective EPR sub-queries** (Verus SOSP 2024 §3.2): Isolates acyclic first-order uninterpreted-function obligations into the decidable Effectively Propositional (EPR) fragment with Z3's MBQI, though SOSP 2024 §4.1 notes that manual EPR abstraction boilerplate (~100 lines for a ~25-line simple inductive proof) pays off mainly on complex data structures such as delegation maps.

#### 3.5 Quantitative Scaling Payoff (Verus SOSP 2024 Macrobenchmarks)

Direct comparison from Verus SOSP 2024 Figure 9 (ports of IronFleet's IronKV from Dafny and Node Replication from Linear Dafny, plus three greenfield Rust systems):

| System | Verifier | Trusted LoC | Proof LoC | Code LoC | Proof:Code | Time (1 core) | Time (8 cores) | Total SMT Payload |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **IronKV** | Verus | 1,613 | 4,509 | 1,533 | 2.9:1 | **41 s** | **18 s** | **17 MB** |
| **IronKV** | Dafny | 1,205 | 8,070 | 1,923 | 4.2:1 | 445 s | 201 s | 352 MB |
| **Node Replication (NR)** | Verus | 369 | 5,237 | 736 | 7.1:1 | **17 s** | **9 s** | **22 MB** |
| **Node Replication (NR)** | Linear Dafny | 104 | 7,828 | 730 | 10.7:1 | 1,089 s | 228 s | 2,063 MB |
| **OS Page Table** | Verus | 1,117 | 5,329 | 400 | 13.3:1 | 63 s | 34 s | 37 MB |
| **Mimalloc Allocator** | Verus | 282 | 13,703 | 3,178 | 4.3:1 | 262 s | 55 s | 152 MB |
| **Persistent Log** | Verus | 1,284 | 2,913 | 739 | 3.9:1 | 12 s | 6 s | 9 MB |
| **Verus Suite Total** | Verus | **4,692** | **31,231** | **6,119** | **5.1:1** | — | — | — |

On the two ported systems, Verus's linear ownership encoding plus aggressive context pruning, conservative triggers, and theory isolation shrank total Z3 SMT input by **20.7×** (`IronKV`) and **93.8×** (`NR`) and accelerated single-core end-to-end verification by **10.9×** and **64.1×**, respectively, while reducing proof lines by **44%** (`IronKV`) and **33%** (`NR`).

### 4. Proof Fragility, Maintenance Economics, and Automated Proof Repair (QED at Large & PUMPKIN Pi)

Basis: documentation + source + derived

Even when SMT solvers are eliminated entirely in favor of kernel-checked interactive theorem provers (Coq/Rocq, Isabelle/HOL, Lean 4), verification hits a second scaling wall: **proof fragility across program, specification, and library evolution**.

#### 4.1 Structural Sources of Tactic-Script Brittleness (*QED at Large*)

Ringer, Palmskog, Sergey, Gligoric, and Tatlock (*QED at Large: A Survey of Engineering of Formally Verified Software*, FnTPL 5(2–3), 2019, DOI `10.1561/2500000045`, §5–§7) synthesize why interactive proof scripts are systematically more fragile than conventional software:

| Fragility Axis | Fragile Procedural Anti-Pattern | Resilient Engineering Alternative | Why the Failure Occurs |
| :--- | :--- | :--- | :--- |
| **Proof-state addressing** | Auto-generated hypothesis names (`H`, `H0`, `H1`), numeric subgoal selectors (`2: apply ...`), unnamed `∧` projections | Explicit named hypotheses (`intros x h_bounds`), named record fields / obligation labels, declarative milestones (`Isar`, `have`/`calc`) | Adding a precondition or reordering a constructor shifts every downstream generated name and goal index |
| **Automation scope** | Unbounded `simp` / `auto` / `crush` over global hint databases | Scoped `simp only [...]`, domain-specific decision procedures, reflective checkers | Adding one upstream `@[simp]` lemma silently rewrites an intermediate goal into a form subsequent tactics no longer match |
| **Operational coupling** | Proof scripts stepping raw interpreter `pc` / stack-frame indices | Abstract algebraic interfaces, lens projections, verified lifting layers | Benign compiler refactorings (temp locals, basic-block splitting) invalidate every concrete step index |
| **Coarse re-verification** | Re-running monolithic proof files on every edit | Regression proof selection (`iCoq`, Celik et al. ASE 2017, DOI `10.1109/ASE.2017.8115630`), per-goal session caches (`Why3`), per-function proof shards | O(file) or O(project) check latency breaks interactive iteration and hides local regressions |

Empirical user-study instrumentation in **REPLica** (Ringer et al., CPP 2020, DOI `10.1145/3372885.3373823`) further showed that proof engineers spend substantial effort performing repetitive, small structural repairs after datatype or specification edits (such as swapping or adding constructors in AST definitions).

#### 4.2 Equivalence-Based Proof-Term Transport and Decompilation (PUMPKIN Pi)

**PUMPKIN Pi** (Ringer, Porter, Yazdani, Leo, and Grossman, PLDI 2021, `arXiv:2010.00774`; `uwplse/pumpkin-pi` @ `a7743d4665d8c7a0ebfd9d39e1247ee7804d402b`) replaces text-level script patching with **axiom-free proof-term transport across type equivalences $A \simeq B$**, followed by decompilation to editable Ltac scripts:

1. **Configuration quadruple `((DepConstr, DepElim), (Eta, Iota))`** (`plugin/src/automation/lift/liftconfig.ml:49–66`, PLDI 2021 §4.1): Rather than assuming Univalence (which blocks computation and retains references to the deleted type $A$), `DepConstr`/`DepElim` wrap $B$'s constructors and eliminators to match $A$'s inductive arity, while `Eta`/`Iota` reduce transported eliminations (`lift.ml:45–73`) to erase all references to $A$ and emit kernel-checkable Gallina terms with zero extra axioms.
2. **Automatic search vs. manual configuration** (`README.md`, `GUIDE.md`, PLDI 2021 Table 1): Automates configuration discovery for four refactoring classes—(i) **algebraic ornaments** (`list T` $\leftrightarrow$ `Σ n. vector T n`), (ii) **unpacking sigma types**, (iii) **records and nested tuples** (applied industrially to SAW-Core/Coq interop, `GUIDE.md` #18), and (iv) **permuting/renaming constructors** (REPLica PL benchmarks). Other refactorings (adding/factoring constructors, permuting hypotheses, unary-to-binary `nat -> N`, vector-to-finite-set) use a once-written manual Coq configuration.
3. **Two-pass decompilation & structural limits** (`plugin/src/frontend.ml:64–81`, `decompiler.ml`, §5–§6.2, `GUIDE.md` #6/#9/#12): `suggest_tactic_script` translates CIC proof terms into a core tactic AST (`Qtac`: $\lambda \to \texttt{intros}$, app $\to \texttt{apply}$, elim $\to \texttt{induction}/\texttt{rewrite}$, let $\to \texttt{pose}$) and lifts to Ltac. To produce concise human-readable scripts, the prototype deliberately forfeits completeness (Coq re-checks the suggested Ltac), relies on heuristic termination checks (`liftrules.ml`), and requires marking unrelated constants `opaque` (`lift.ml:76–81`) to prevent runaway $\delta$-unfolding—the interactive analogue of SMT opacity discipline.

### 5. Incremental Proof Sharding, Shape-Based Session Replay, and Trusted vs. Untrusted Functional Lifting (Why3, AutoCorres, Aeneas)

Basis: documentation + source + derived

#### 5.1 Fine-Grained Incremental Sharding and Why3 Shape-Based Proof Sessions

Monolithic proof files impose $O(\text{file})$ re-checking latency on 1-line edits, while text-hash caches miss whenever specification edits perturb VC syntax. **Why3** (Bobot et al., VSTTE 2013; Filliâtre and Paskevich, ESOP 2013) resolves VC-identity churn by storing every module's proof tree in `why3session.xml` with two keys per goal: (1) an exact normalized-task **checksum** for instant unchanged-goal skipping, and (2) an alpha-invariant structural **shape** stripping bound names and local literal tweaks so modified VCs reattach to their prior transformation subtrees (`split_vc`, `induction`) and interactive scripts by minimum shape distance. Paired with AST-dependency regression proof selection (`iCoq`, ASE 2017) and per-function proof shards, incremental verification bounds both latency and memory (see `dafny-boogie-viper-fstar-why3-and-vc-obligation-architectures` and `compcert-sel4-everest-pass-composition-and-proof-maintenance`).

#### 5.2 Raw Small-Step Operational States vs. Soundness-Proved Functional Lifting

Verifying directly against raw small-step IR states (C-parser SIMPL or `rustc` MIR) explodes proof size via manual framing and breaks whenever a compiler inserts benign `StorageLive`/`StorageDead`, scratch locals, or dead stores. Two architectures eliminate raw operational plumbing with opposite TCB boundaries:

| Architecture Dimension | **Aeneas** (`ICFP 2022`, `AeneasVerif/aeneas`) | **AutoCorres** (`PLDI 2014`, `seL4/l4v/tools/autocorres`) | **Hybrid Validated Functional/Lens Lifting** (Synthesis) |
| :--- | :--- | :--- | :--- |
| **Source & IR input** | Safe Rust $\to$ Charon LLBC (from `rustc` MIR) | C $\to$ Norrish C-to-Isabelle parser $\to$ SIMPL | Imperative/MIR small-step IR inside proof assistant |
| **Target proof surface** | Pure lambda-calculus (forward + backward functions) in Lean / F\* / Coq / HOL4 | Simplified monadic HOL (pure / option / nondet monad) with split typed heaps & mathematical `int`/`nat` | Fuel-free pure/lens functional surface over disjoint regions + spatial fallback for raw pointers |
| **Memory & aliasing handling** | Eliminated via value-based LLBC loan semantics & region-end backward functions | Eliminated via `LocalVarExtract` + `HeapLift` split-heap abstraction (`TypHeapSimple`) | Eliminated on safe borrows via alias-erasing lenses (`GetPut`/`PutGet`/`PutPut`); pinned regions for `unsafe` |
| **Is the lifter in the TCB?** | **YES** (`Charon` + OCaml `Aeneas` translator + stdlib models are trusted; no kernel refinement proof to MIR) | **NO** (Isabelle/HOL kernel checks a per-function `ac_corres` refinement theorem linking SIMPL to lifted output; C parser remains in TCB) | **NO** (untrusted lifter emits per-function kernel-checked refinement certificate back to small-step IR) |
| **Support for `unsafe` / raw pointers / interior mutability** | Excluded in ICFP 2022 design (`arXiv:2206.07185` §1, §3: safe sequential Rust without `unsafe` or interior mutability) | Supported (falls back selectively via `no_heap_abs` / `skip_word_abs` per function without breaking composition) | Supported via selective spatial pinning / fallback to underlying small-step TCB semantics |
| **Documented simplification payoff** | Eliminates memory reasoning entirely for safe Rust data structures (e.g., resizing hash table) | **25%–53%** fewer specification lines; **40%–61%** smaller logical terms vs. raw SIMPL (`PLDI 2014`) | Combines functional proof ergonomics with zero TCB expansion (see `anneal-fuel-free-mir-lifting-and-alias-erasure`) |

#### 5.3 Inside AutoCorres's Kernel-Checked Five-Stage Refinement Chain

Direct inspection of `seL4/l4v` (`b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`) in `tools/autocorres/autocorres.ML:386–390, 586–625`, `AutoCorres.thy:78–98`, `L2Defs.thy:11–50`, and `local_var_extract.ML:45–73` shows how AutoCorres keeps its SML abstraction heuristics *completely outside* Isabelle/HOL's TCB:

1. **L1 (`SimplConv`, `L1corres`)**: Converts structured C-parser SIMPL statements into a monadic exception representation (`L1_monad`).
2. **L2 (`LocalVarExtract`, `L2corres`)**: Abstracts local variables out of the global state record (`convert_local_vars` replaces state-projected `a_' s` with pure HOL bound variables) and eliminates compiler-generated temporaries via peephole simplification (`L2_folded_gets_bind: L2_seq (L2_folded_gets (\<lambda>_. x) name) f = f x`, `L2Defs.thy:45–49`).
3. **HL (`HeapLift`, `L2Tcorres`)**: Lifts the flat byte-level C heap (`t_hrs`) into separate typed partial-function heaps per C type (`HeapLift.thy:17–42`), proving `abs_guard`, `abs_expr`, and `abs_modifies` correspondence rules. Functions that perform type-unsafe pointer casts can selectively opt out via `no_heap_abs`, substituting trivial `L2Tcorres_id` (`AutoCorres.thy:61–63`).
4. **WA (`WordAbstract`, `corresTA`)**: Abstracts fixed-width two's-complement machine words (`word32`/`word64`) into unbounded mathematical `int`/`nat` while preserving overflow guards (`WordAbstract.thy:14–53`).
5. **TS (`TypeStrengthen`, `L2_call c_WA = A`)**: Strengthens each function into the weakest monad it actually needs—down to pure HOL functions (`TS_return`, `TypeStrengthen.thy:63–65`), option monads, or state monads—eliminating exception and nondeterminism plumbing wherever unused.
6. **End-to-end composition** (`AutoCorres.thy:78–85`):
   ```isabelle
   lemma ac_corres_chain:
     "\<lbrakk> L1corres check_termination Gamma c_L1 c;
        L2corres st_L2 rx_L2 (\<lambda>_. ()) P_L2 c_L2 c_L1;
        L2Tcorres st_HL c_HL c_L2;
        corresTA P_WA rx_WA ex_WA c_WA c_HL;
        L2_call c_WA = A
      \<rbrakk> \<Longrightarrow>
      ac_corres (st_HL o st_L2) check_termination Gamma (rx_WA o rx_L2)
                (P_L2 and (P_WA o st_HL o st_L2)) A c"
   ```

Because every stage produces an Isabelle theorem checked by the kernel and chained via `ac_corres_chain`, any bug in `local_var_extract.ML`, `heap_lift.ML`, or `word_abstract.ML` can only cause lifting to **fail loudly**—it can never prove a false theorem about the underlying C program. That architectural separation—*untrusted heuristic lifting + small-kernel per-function refinement certificate*—is the direct antidote to both raw operational proof fragility and Aeneas-style frontend TCB inflation (see `anneal-fuel-free-mir-lifting-and-alias-erasure` for its application to Rust MIR).

### 6. Executable Verification Probe Results (`support/verify_trigger_loops_and_lifting.py`)

Basis: execution + derived

Running the standalone Python 3.10+ probe `support/verify_trigger_loops_and_lifting.py` (`python3 -B`) empirically reproduces both core walls and their mitigations deterministically (~2.3s wall time, zero third-party dependencies):

#### 6.1 Part A: Trigger-Graph Cycle Detection, Bounded Budget Instability, and SHAKE Pruning

| Experiment Scenario | Local Filter (Verus-style) | Global SCC Trigger Graph | Budgeted E-Matching (60 Mutants, `budget=32`) |
| :--- | :--- | :--- | :--- |
| **Stratified DAG** (`in_bounds -> valid_idx -> safe_read`) | 0 hits | `[]` (0 amplifying cycles) | Terminating, bounded ground closure |
| **Direct self-loop** (`P(x) -> P(succ(x))`) | `{'direct_loop': 1}` (**caught**) | `[['direct_loop']]` (**caught**) | Unbounded growth if triggered |
| **Mutual 2-cycle** (`f(x) -> g(succ(x))`, `g(y) -> f(h(y))`) | `{}` (**missed**) | `[['mut_f_to_g', 'mut_g_to_f']]` (**caught**) | Demonstrates why single-quantifier filters are insufficient |
| **Peano fuel-guarded recursion** (`rec_f(x, succ(k)) -> rec_f(step(x), k)`) | 0 hits | `[]` amplifying (`[['rec_f_unfold']]` stratified) | Terminates in $\le k$ unfoldings |
| **Unpruned polluted query** (3 goal rules + 6 ambient distractor loops) | — | 6 distractor loops present | `shuffle`: **33.3%** pass (`unstable`/`unstable`, mean `29.82` insts); `reseed`: **40.0%** pass (`unstable`/`unstable`, mean `29.77` insts) |
| **SHAKE-pruned query** (lazy pattern-subset expansion from `{goal_ok, init}`) | — | 0 distractor rules retained (`layers={'ax_step1':1, 'ax_step2':2, 'ax_step3':3}`) | `shuffle`: **100.0%** pass (`stable`/`stable`); `reseed`: **100.0%** pass (`stable`/`stable`); mean `3.0` insts (**9.9×** fewer) |

Both Mariposa's cutoff classifier and one-sided proportion z-test ($\alpha = 0.05$, $r_{\text{solvable}} = 0.05$, $r_{\text{stable}} = 0.95$) classify the unpruned polluted query as `unstable` under both assertion-order shuffling and PRNG reseeding, and classify the SHAKE-pruned query as `stable` (`60/60`) across both perturbations.

#### 6.2 Part B: AutoCorres-Style Validated Local-Var & Heap-Lens Lifting Invariance

Over an imperative small-step IR with explicit `StorageLive`, `StorageDead`, local assignments, and flat address-indexed `HeapLoad`/`HeapStore` (`*p_cnt += delta; return *p_cnt` with disjoint untouched slot `p_other`):

| IR Variant | Stmt Count | Raw Small-Step Proof (Fixed Fuel/PC/Temps) | Validated Lifted Proof (Lens Surface) | Per-Function Refinement Grid Checked | Canonical Lifted IR Equal to `v0` |
| :--- | ---: | :---: | :---: | ---: | :---: |
| `v0_baseline` | 5 | **PASS** | **PASS** | 30 / 30 | `True` |
| `v1_scratch_storage_live` (`+StorageLive(_scratch)`, copy) | 8 | **FAIL** | **PASS** | 30 / 30 | `True` |
| `v2_ptr_copy_dead_temp` (`+alias ptr`, `+0`, dead `mul`) | 17 | **FAIL** | **PASS** | 30 / 30 | `True` |
| `v3_nops_and_slot_reuse` (`+Nop`, renamed temp slot) | 8 | **FAIL** | **PASS** | 30 / 30 | `True` |
| **Negative canary** (buggy untrusted lifter dropping `+ delta`) | 5 | — | **REJECTED** (`AssertionError` in validator) | Rejected | — |

- **Raw small-step proof churn survival**: `0/3 (0.0%)` across benign compiler-churn variants `v1..v3`.
- **Validated lifted proof invariance**: `4/4 (100.0%)`, with bidirectional lens laws (`GetPut`, `PutGet`, `PutPut`, pairwise disjoint framing) verified and a buggy-lifter negative canary rejected—demonstrating proof invariance without admitting the lifter into the TCB.

## Boundaries

- **not examined**:
  - Live execution of Z3, cvc5, Verus, Coq, or Isabelle/HOL binaries on the 17,043-query Mariposa or seL4 corpora (empirical numbers come from cited peer-reviewed papers and pinned `secure-foundations/mariposa/doc/reports/*.txt`; `support/verify_trigger_loops_and_lifting.py` executes self-contained models of the underlying algorithms).
  - SMT proof-certificate reconstruction (`smt-sat-alethe-carcara-and-numerical-proof-certificate-reconstruction`), Lean 4 proof-repair automation (`typeclass-insulated-layer0-coremir-and-automated-lean-proof-repair`), and Rust-MIR Tree Borrows lens lifting (`anneal-fuel-free-mir-lifting-and-alias-erasure`).
  - Why3's OCaml session-merger source (no official GitHub mirror at `Why3/why3`; findings derive from the VSTTE 2013 and ESOP 2013 papers).
- **unknown**:
  - Whether Z3 > 4.13.0 or cvc5 > 1.1.1 resolves the fast `shuffle`-induced `unknown` failures observed in `verus_systems.60sec.txt`.
  - Comparative upgrade-breakage rates of LLM-authored vs. human-authored interactive tactic scripts across Mathlib or `rustc` MIR bumps.
  - Marginal stability gain of layering SHAKE context pruning *after* Verus's existing VIR-level `prune.rs` reachability pass (SHAKE FMCAD 2024 evaluated Dafny and F* corpora).
- **known not to apply**:
  - **AutoCorres still trusts the C parser**: `ac_corres` excludes AutoCorres's five abstraction passes from the TCB, but Norrish's C-to-Isabelle parser, Isabelle/HOL's kernel, and C-to-binary correspondence remain trusted unless discharged separately.
  - **SHAKE is not strictly monotonic on Z3 solved count**: Default SHAKE slightly reduced Z3 4.12.5 solved queries (`-0.45%`; `-0.18%` oracle), and cached oracle distance limits fail if a legitimate edit increases shortest core depth.
  - **Verus isolated sub-solvers hide ambient locals**: `by(bit_vector)` and `by(nonlinear_arith)` do not see outer `let` definitions unless passed via `requires P`; `by(bit_vector)` rejects unbounded `int`/`nat` free variables (`reference-prover-mode-bit-vector.md:37–60`).
  - **Probe refinement validation is a bounded model**: Part B's 30-case Cartesian validator demonstrates the architectural split between an untrusted lifter and an independent checker, not a universal deductive proof.
- **unsupported**:
  - **Aeneas (ICFP 2022)** explicitly excludes `unsafe` blocks, raw pointer arithmetic, and interior mutability (`arXiv:2206.07185` §1, §3).
  - **PUMPKIN Pi** (`uwplse/pumpkin-pi` @ `a7743d4665d8c7a0ebfd9d39e1247ee7804d402b`) targets Coq 8.9.1 (`README.md`), automates configuration search only for four equivalence classes, and intentionally forfeits completeness in its prototype Ltac decompiler.
  - **Unmodified Z3-specific Dafny/F* SMT-LIB queries** are unsupported directly by cvc5 without syntax translation and option tuning (`Mariposa` §IV-C, `SHAKE` §V).

## Evidence

### Primary Publications Verified

| Short Name | Citation & Venue | Immutable ID / URL & Sections Inspected |
| :--- | :--- | :--- |
| **Mariposa** | Zhou, Bosamiya, Takashima, Li, Heule, Parno (FMCAD 2023) | DOI `10.34727/2023/isbn.978-3-85448-060-0_26`, `andrew.cmu.edu/user/bparno/papers/mariposa.pdf` (§I, §III-C–E, §IV-C–D Tables I–II, §V Table III) |
| **SHAKE** | Zhou, Bosamiya, Li, Heule, Parno (FMCAD 2024) | DOI `10.34727/2024/isbn.978-3-85448-065-5_12`, `cs.cmu.edu/~mheule/publications/shake.pdf` (§I, §III, §IV Algs. 1–2, §V Fig. 14) |
| **Verus (OOPSLA'23)** | Lattuada, Hance, Cho, Brun, Subasinghe, Zhou, Howell, Parno, Hawblitzel (PACMPL 7, 2023) | DOI `10.1145/3586037`, `arXiv:2303.05491` (fuel, `reveal_with_fuel`, triggers, linear ghost types) |
| **Verus (SOSP'24)** | Lattuada, Hance, Bosamiya, Brun, Cho, LeBlanc, Srinivasan, Achermann, Chajed, Hawblitzel, Howell, Lorch, Padon, Parno (SOSP 2024) | DOI `10.1145/3694715.3695952`, `chajed.io/papers/verus:sosp2024.pdf` (§3.1–3.3, §4.1–4.2 Fig. 9) |
| **QED at Large** | Ringer, Palmskog, Sergey, Gligoric, Tatlock (FnTPL 5(2–3), 2019) | DOI `10.1561/2500000045`, `arXiv:2003.06458` (§5–§7 proof fragility & evolution) |
| **PUMPKIN Pi** | Ringer, Porter, Yazdani, Leo, Grossman (PLDI 2021) | DOI `10.1145/3453483.3454033`, `arXiv:2010.00774` (§4–§7, Table 1) |
| **AutoCorres** | Greenaway, Lim, Andronick, Klein (PLDI 2014) | DOI `10.1145/2594291.2594296` (abstract, word/heap lifting, Schorr-Waite & spec/term reductions) |
| **Aeneas** | Ho, Protzenko (PACMPL 6(ICFP), 2022) | DOI `10.1145/3547647`, `arXiv:2206.07185` (Abstract, §1–§4 LLBC & backward functions) |
| **Why3 & Supporting** | Bobot et al. (VSTTE 2013, `10.1007/978-3-642-54108-7_10`); Filliâtre & Paskevich (ESOP 2013, `10.1007/978-3-642-37036-6_8`); Detlefs, Nelson & Saxe (JACM 2005, `10.1145/1066100.1066102`); de Moura & Bjørner (CADE 2007, `10.1007/978-3-540-73595-3_13`); Becker, Müller & Summers (TACAS 2019, `10.1007/978-3-030-17462-0_6`); Amin, Leino & Rompf (TAP 2014); Hawblitzel et al. (SOSP 2015, `10.1145/2815400.2815428`); Celik, Palmskog & Gligoric (ASE 2017, `10.1109/ASE.2017.8115630`); Ringer et al. (CPP 2020, `10.1145/3372885.3373823`) | Verified DOIs, venues, and technical scope |

### Pinned Source Repositories Inspected (`observed_at: 2026-11-19`)

- `secure-foundations/mariposa` @ `8646e7b1c601f7154e93d85ebb1083ce1ed47f95`: `src/base/query_analyzer.py:27–215`, `config/{analyzers,expers}.json`, `src/smt2action/src/{query_mutate.rs:42–117,tree_shake.rs:14–392,410–582}`, `doc/reports/{mariposa_systems,verus_systems.10sec,verus_systems.60sec,anvil.60sec,splinterdb.60sec,verismo.dedup.60sec}.txt`.
- `verus-lang/verus` @ `a95764f23c6876b47500beda6118e2d142a87cc3`: `source/vir/src/{triggers.rs:15–90,triggers_auto.rs:138–186,569–706,829,sst_to_air_func.rs:164–211,305–410,prelude.rs:180–188,773–855,prune.rs:29–90,966–1387}`, `source/docs/guide/src/{assert_by,multitriggers,nonlinear,opaque,profiling,reference-prover-mode-bit-vector,reference-prover-mode-compute,reference-prover-mode-nonlinear,reference-reveal-hide,spinoff_prover,breaking_proofs_into_pieces}.md`.
- `Z3Prover/z3` @ `437536cd64a544a1c329fc57d83e56e294fdf47c`: `src/smt/{mam.cpp:1–80,qi_queue.h:42–90,qi_queue.cpp:46–252}`.
- `viperproject/smt-scope` @ `665f9263c6102ff63494dafb39976d015c675951` (confirmed successor to `viperproject/axiom-profiler-2` @ `03e43597e7ac5969e721647c894f35ffb46adb46`).
- `uwplse/pumpkin-pi` @ `a7743d4665d8c7a0ebfd9d39e1247ee7804d402b`: `README.md`, `GUIDE.md`, `plugin/src/{frontend.ml:64–88,automation/lift/lift.ml:1–95,automation/lift/liftconfig.ml:49–95}`.
- `seL4/l4v` @ `b0fe7693ca5943e08c49e038d33fd64dc7dfa72e`: `tools/autocorres/{README.md,autocorres.ML:26–90,386–392,586–625,AutoCorres.thy:55–172,L2Defs.thy:11–75,local_var_extract.ML:45–80,HeapLift.thy:17–65,WordAbstract.thy:14–65,TypeStrengthen.thy:37–65}`.
- `AeneasVerif/aeneas` @ `8f4466db9f0d59267b8e76b54473a21a005cf7be`: `README.md`, `src/` pipeline layout.

### Probe Execution Record

Command run on `2026-11-19` (Python 3 stdlib only, exit code `0`, ~2.3s wall time):

```console
python3 -B reports/proof-fragility-smt-instability-and-verification-scaling-walls/support/verify_trigger_loops_and_lifting.py
```

Observed output:

```text
=== Part A: E-Matching Trigger-Graph & SHAKE Context-Pruning Analysis ===
Stratified DAG amplifying cycles:       []
Direct self-loop amplifying cycles:     [['direct_loop']] (local hits: {'direct_loop': 1})
Mutual 2-cycle local-filter hits:       {} (MISSED by single-rule filter)
Mutual 2-cycle SCC amplifying cycles:   [['mut_f_to_g', 'mut_g_to_f']] (CAUGHT by trigger-graph SCC)
Fuel-guarded rec_f amplifying cycles:   [] (stratified: [['rec_f_unfold']])
Unpruned query (9 rules, budget=32, 60 mutants each):
  shuffle: cutoff/z_test=('unstable', 'unstable'), pass_rate=33.3%, mean_insts=29.82
  reseed:  cutoff/z_test=('unstable', 'unstable'), pass_rate=40.0%, mean_insts=29.77
SHAKE-pruned query (3 rules, budget=32, 60 mutants each):
  shuffle: cutoff/z_test=('stable', 'stable'), pass_rate=100.0% | reseed: cutoff/z_test=('stable', 'stable'), pass_rate=100.0% | mean_insts=3.0, layers={'ax_step1': 1, 'ax_step2': 2, 'ax_step3': 3}

=== Part B: AutoCorres-Style Validated Local-Var & Heap-Lens Lifting ===
  v0_baseline              stmts= 5 | raw_proof=PASS | lifted_proof=PASS | refinement_checked=30 | canonical=True
  v1_scratch_storage_live  stmts= 8 | raw_proof=FAIL | lifted_proof=PASS | refinement_checked=30 | canonical=True
  v2_ptr_copy_dead_temp    stmts=17 | raw_proof=FAIL | lifted_proof=PASS | refinement_checked=30 | canonical=True
  v3_nops_and_slot_reuse   stmts= 8 | raw_proof=FAIL | lifted_proof=PASS | refinement_checked=30 | canonical=True
Raw small-step proof churn survival:    0/3 (0.0%)
Validated lifted proof invariance:      4/4 (100.0%)
Buggy untrusted lifter canary rejected: True

ALL CHECKS PASSED
```

## Revalidation

To cheaply verify whether the core findings still hold after upstream tool or solver updates without repeating the full literature and codebase crawl:

1. **Rerun the bundled executable probe**:
   ```console
   python3 -B reports/proof-fragility-smt-instability-and-verification-scaling-walls/support/verify_trigger_loops_and_lifting.py
   ```
   A `0` exit code and `ALL CHECKS PASSED` confirm that the trigger-graph SCC detector, SHAKE lazy pattern-subset pruner, Mariposa cutoff/z-test classifier, and AutoCorres-style validated lens lifter remain self-consistent.
2. **Check Verus trigger-loop detection and fuel/pruning shifts**: Diff `source/vir/src/triggers_auto.rs` (`remove_obvious_potential_loops`, `Score`), `source/vir/src/sst_to_air_func.rs` (fuel axioms), `source/vir/src/prelude.rs` (`Mul`/`EucDiv`/`EucMod` wrapping), and `source/vir/src/prune.rs` against `verus-lang/verus@a95764f23c6876b47500beda6118e2d142a87cc3`. In particular, check whether Verus has replaced single-rule `remove_obvious_potential_loops` with inter-quantifier SCC cycle detection.
3. **Check Z3 E-matching queue defaults and Mariposa solver reports**: Diff `Z3Prover/z3/src/smt/qi_queue.cpp` (`setup`, default cost formula `(+ weight generation)`, `m_eager_cost_threshold`) against `437536cd64a544a1c329fc57d83e56e294fdf47c`, and check `secure-foundations/mariposa/doc/reports/` for newer Z3/cvc5 stability baselines beyond Z3 4.13.0.
4. **Check AutoCorres2 and Aeneas TCB status**: Compare `seL4/l4v/tools/autocorres/AutoCorres.thy` (`ac_corres_chain`) against Isabelle AFP's `AutoCorres2` entry noted in `tools/autocorres/README.md`, and check `AeneasVerif/aeneas` (`src/`) for whether Aeneas has added either `unsafe`/interior-mutability support or kernel-checked translation validation back to MIR.
5. **Revalidating empirical solver-instability percentages**: No cheap probe establishes instability rates for a new solver binary or verifier corpus; to measure a new `(verifier, solver)` pair, extract SMT-LIB queries and run `secure-foundations/mariposa` (`exper_wizard.py`) with 60 mutants across `shuffle`, `rename`, and `reseed`.
