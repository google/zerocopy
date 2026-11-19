# SAT Inprocessing, DRAT/LRAT/FRAT/LPR/VeriPB Proof Checkers, Certified MaxSAT, and QBF/DQBF Skolem Strategy Certificates

## Summary

Modern Boolean reasoning systems—conflict-driven clause-learning (CDCL) SAT solvers, core-guided MaxSAT optimizers, and quantified Boolean formula (QBF/2QBF) engines—rely on equisatisfiable formula transformations that **do not preserve logical equivalence or satisfying model sets** ($F \not\equiv F'$), creating a strict separation between *solving*, *model reconstruction*, and *independent proof certification*:

1. **Equisatisfiable Inprocessing & Witness Stacks:** In `CaDiCaL 3.1.0` (`arminbiere/cadical`), passes such as bounded variable elimination (`elim=1`), congruence closure (`congruence=1`), SAT sweeping (`sweep=1`), vivification (`vivify=1`), blocked-clause elimination (`block=0` default), and bounded variable addition / factoring (`factor=0` default, generalizing `SBVA`'s 3-hop bipartite incidence tie-breaking) mutate clauses in ways that can drop satisfying models or add new ones. Satisfiable runs must unwind an internal witness/reconstruction stack (`External::extend`) to flip witness literals back into valid models of the original CNF; unsatisfiable runs must emit clausal or pseudo-Boolean redundancy certificates.
2. **Proof Format Hierarchy & Complexity Separation (`DRAT` vs. `FRAT` vs. `LRAT`/`LPR` vs. `VeriPB`):**
   - **DRAT** (`drat-trim`) omits clause IDs and propagation hints; verification requires reverse-pass unit propagation and global RAT-candidate search, making unverified elaboration the bottleneck and precluding direct kernel reflection.
   - **FRAT** (`digama0/frat`) decouples solver tracing from elaboration by carrying clause IDs, literal-carrying deletions (`d <id> <lits>`), original (`o`) and final (`f`) clauses, and optional LRAT hint chains (`l`), enabling a fast two-pass backward-trim + forward-elaborate pipeline to LRAT/LPR.
   - **LRAT / LPR** (`lrat-check`, `cake_lpr`, Lean 4 `bv_decide`) embeds explicit positive RUP hint IDs and negated RAT/PR candidate IDs so each RUP step checks in $O(\sum |H_i|)$ literal visits independent of total active clause count. **Propagation Redundancy (PR)** (`LPR` in `cake_lpr`) strictly generalizes RAT via multi-literal witness assignments $\omega$, enabling polynomial-size refutations (e.g., Pigeonhole Principle symmetry breaking) without fresh extension variables.
   - **VeriPB** (`pseudo-Boolean proof version 3.0`, emitted natively by `CaDiCaL 3.1.0` and verified by `VeriPB` / `CakePB`) lifts clausal checking to cutting planes (`pol`), redundancy (`red`), dominance breaking (`dom`), objective-bound logging, and **checked core deletions** (`core id` / `delc`) required for soundness in MaxSAT and combinatorial optimization.
3. **Verification Trust Boundaries (`cake_lpr` vs. Lean 4 `bv_decide`):** `tanyongkiam/cake_lpr` compiles its HOL4-verified LPR checker through the verified CakeML compiler to x86-64/ARMv8 assembly (`check_unsat_semantics`), leaving only HOL4's kernel, the small C FFI wrapper (`basis_ffi.c`), and hardware/assembler in the TCB—and natively supports both UNSAT checking and equisatisfiable transformation checking (`mindel` protection). By contrast, Lean 4's `bv_decide` verifies a bit-blasted AIG-to-CNF pipeline plus a proven-sound `LRAT` (RUP + RAT only, no PR) checker in Lean, but discharges the reflection equality via `nativeEqTrue` (`Lean.ofReduceBool`), which **adds the Lean compiler and native evaluator to the TCB**.
4. **QBF / 2QBF / DQBF & Certified Skolem Extraction:** Propositional RAT is **unsound** for QBF—adding a valid propositional RAT clause on a universal pivot turns a true QBF into a false one. Sound QBF certification requires quantifier-aware systems: `QRAT` (`qrat-trim` + `cheskol`) restricts resolution candidates to outer clauses $O(D, l)$ at quantifier level $\le \text{lv}(l)$ and forbids universal pivots in `QRATA`; `DepQBF 6.03` must disable its default standard dependency scheme (`--dep-man=simple`), lazy QPUP (`--no-lazy-qpup`), and incremental mode to emit `QRP` proofs; `CADET` solves 2QBF ($\forall\exists$) via incremental determinization and directly synthesizes AIGER Skolem circuits from unique-consequence antecedents; general Henkin-quantified `DQBF` jumps from `PSPACE`-complete to `NEXPTIME`-complete, where standard Q-resolution with arbitrary dependency schemes loses soundness unless restricted or lifted to specialized calculi.

---

## Applicability

This report synthesizes direct source inspection across twelve pinned upstream repositories, peer-reviewed proof-system specifications, and self-contained Python execution probes collected on `2026-11-19`:

- **CDCL SAT Inprocessing & Proof Tracers:** `arminbiere/cadical` @ `6b3d70b9ce00ecbce3f829bab76d185f0e92618c` (`v3.1.0`) and `hgarrereyn/SBVA` @ `35e74d02aa1b0970d53fef1c86171e596d0da453`. Findings apply to non-incremental and incremental CDCL CNF solving, proof tracing (`drat`, `lrat`, `frat`, `veripb`, `idrup`/`lidrup`), and witness reconstruction. Note that CaDiCaL's default configuration disables `block` (`0`) and `factor` (`0`) while enabling `elim`, `congruence`, `vivify`, `sweep`, `decompose`, `ternary`, `subsume`, and `probe` (`1`); behavior changes materially when `--factor=1` (emitting RAT/ER steps) or `--veripb=1..4` (checked deletions) is selected.
- **Clausal Proof Elaborators & Verified Checkers:** `marijnheule/drat-trim` @ `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, `digama0/frat` @ `aa18581497830b49a6ab6cbc9e0dc778c14885b5`, `tanyongkiam/cake_lpr` @ `033aad53d1733bd4b8ca41cf6f1b5fb5d84f8de2` (built from `HOL4` `9783a49979c94c401ff8c0e51b2eefae7ea95ae3` and `CakeML/cakeml` @ `665f9b21712ad093e10a404ccc2f78e64a34aeef`), and `leanprover/lean4` @ `0171678607a54e5a72c6a4ab6409286ba5002b05` (`Std.Tactic.BVDecide` and `Lean.Meta.Tactic.BVDecide`). Findings compare proof formats, algorithmic checker complexity, supported inference rules (RUP vs. RAT vs. PR), and trusted computing bases (TCBs).
- **Pseudo-Boolean & Core-Guided MaxSAT Certification:** `StephanGocht/VeriPB` @ `01b7b5088c8a67f1611427174501191bc5f5b365` (covering format versions 1.x–2.x rules documented in its tree) contrasted with `CaDiCaL 3.1.0`'s `VeripbTracer` (emitting `pseudo-Boolean proof version 3.0`) and `pysathq/pysat` @ `ff051b57496492822a52c510bbd082f840bd792f` (`examples/rc2.py`, uncertified OLL core-guided MaxSAT) alongside the published VeriPB/CakePB certified MaxSAT methodology (Berg et al., CADE 2023; Gocht et al., AAAI 2024).
- **QBF / 2QBF / DQBF Solvers & Skolem Extraction:** `markusrabe/cadet` @ `40f9683261013780b5c6cddf9cb3112d0f71d187` (strictly 2QBF $\forall\exists$ in QDIMACS/QAIGER), `lonsing/depqbf` @ `2ad3995a21b8ca2831be2534b1cb80df342b3bdf` (`v6.03`, arbitrary prenex QBF in QDIMACS), and `marijnheule/qrat-trim` @ `5d6a1b60c1108755975b47b15d3676afeb3dbb65` (`qrat-trim.c`, `cheskol.c`), together with complexity/soundness theory for Henkin DQBF and dependency schemes.

Claims about specific solver defaults, tracer wire formats, and TCB axioms apply strictly to the pinned revisions listed above. Broader proof-theoretic separations (e.g., $\text{RUP} \subsetneq \text{RAT} \subsetneq \text{PR}$, $\text{QBF} \in \text{PSPACE-complete}$, $\text{DQBF} \in \text{NEXPTIME-complete}$, and QBF unsoundness of unconstrained propositional RAT) are mathematical theorems independent of solver revision.

---

## Findings

### 1. CDCL Equisatisfiable Inprocessing, Factoring (`SBVA`), and Witness Reconstruction

`Basis: normative + source + execution`

Classical resolution and CDCL conflict learning derive only logically entailed clauses ($F \models C$), which leave the model set $\mathcal{M}(F)$ invariant. Modern inprocessing SAT solvers go strictly beyond entailment by applying **redundancy-preserving** (equisatisfiable) clause additions and deletions (Järvisalo, Heule, Biere, IJCAR 2012, `DOI: 10.1007/978-3-642-31365-3_28`). A clause $C$ is *redundant* with respect to CNF $F$ iff $F$ and $F \cup \{C\}$ are equisatisfiable—even when $F \not\models C$.

#### 1.1 Redundancy Hierarchy in Propositional Proof Systems

Let $F|_ \alpha$ denote the formula obtained by removing clauses satisfied by partial assignment $\alpha$ and removing literals falsified by $\alpha$, and let $F \vdash_1 \bot$ denote that unit propagation derives a conflict from $F$. For a clause $C$, let $\bar{C} = \{\neg l \mid l \in C\}$ be the blocking assignment that falsifies $C$.

| Proof Rule | Formal Side Condition for Adding $C$ to $F$ | Fresh Variables Required? | Preserves Models $\mathcal{M}(F)$? | Checkable by `LRAT` (`bv_decide`)? | Checkable by `LPR` (`cake_lpr`)? | Checkable by `VeriPB` (`red`/`pol`)? |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **AT / RUP** (Reverse Unit Propagation) | $(F \wedge \bar{C}) \vdash_1 \bot$ | No | Yes ($F \models C$) | Yes | Yes | Yes (`rup` / `pol`) |
| **BC** (Blocked Clause) on pivot $l \in C$ | $\forall D \in F$ with $\neg l \in D$: $(C \setminus \{l\}) \cup (D \setminus \{\neg l\})$ is tautological | No (or fresh $l$ for ER) | **No** (equisatisfiable only) | Yes (special case of RAT) | Yes (special case of PR) | Yes (`red ... : x_l -> 1/0`) |
| **RAT** (Resolution Asymmetric Tautology) on $l \in C$ | $\forall D \in F$ with $\neg l \in D$: $(F \wedge \bar{C} \wedge \overline{D \setminus \{\neg l\}}) \vdash_1 \bot$ | No (fresh $l$ gives ER) | **No** (equisatisfiable only) | Yes | Yes | Yes (`red ... : x_l -> 1/0`) |
| **PR** (Propagation Redundancy) with witness $\omega$ | $\omega \models C$, $\omega$ consistent, and $(F \wedge \bar{C}) \vdash_1 F|_{\omega}$ (i.e., $\forall D \in F$ touched by $\bar{\omega}$, either $\omega \models D$ or $(F \wedge \bar{C} \wedge \overline{D|_{\omega}}) \vdash_1 \bot$) | **No** (short PHP proofs without new vars) | **No** (equisatisfiable only) | **No** (`IntAction` has no witness) | **Yes** (`is_PR`) | Yes (`red ... : \omega`) |
| **DRAT / LRAT Deletion** | Deleting any clause $D \in F$ (weakens $F \to F \setminus \{D\}$) | N/A | **No** (may enlarge $\mathcal{M}(F)$) | Yes (`del`) | Yes (`Delete`, guarded by `mindel`) | Checked (`delc` vs `del id` in v3.0) |
| **VeriPB Cutting Planes + Dominance (`pol` + `dom`)** | Linear integer combinations + division + saturation; dominance $\omega$ strictly improves preorder $\preceq$ on $F_{\text{core}}$ | Optional | **No** (preserves optimal objective value) | **No** | **No** (needs `CakePB`) | **Yes** |

*Key proof-theoretic separation:* Heule, Kiesl, and Biere (CADE 2017, `DOI: 10.1007/978-3-319-63046-5_9`) proved that PR admits polynomial-size refutations of the Pigeonhole Principle ($\text{PHP}_n^{n+1}$) **without introducing fresh extension variables**, by expressing symmetry-breaking swaps directly as multi-literal witnesses $\omega$. In our executable micro-probe (`PROBE 2`), adding the symmetry-breaking clause $C = (\neg p_{1,1} \vee \neg p_{2,2})$ to $\text{PHP}_3^2$ fails both RUP and single-literal RAT (`ERR_MISSING_PR_HINT_1`), yet passes exact CakeML-semantics `check_PR` with witness $\omega = [\neg p_{1,1}, p_{1,2}, p_{2,1}, \neg p_{2,2}]$ and two clause hints (`{6: [5], 8: [9]}`).

#### 1.2 Inprocessing Passes and Proof Interactions in `CaDiCaL 3.1.0`

`Basis: source` (`arminbiere/cadical` @ `6b3d70b9ce00ecbce3f829bab76d185f0e92618c`)

Inspection of `src/options.hpp` (L37–310), `src/proof.hpp`, `src/proof.cpp`, `src/elim.cpp`, `src/block.cpp`, `src/vivify.cpp`, `src/factor.cpp`, and `src/extend.cpp` establishes how CaDiCaL 3.1.0 orchestrates inprocessing and proof tracing:

1. **Default Active Inprocessing (`src/options.hpp`):** Enabled by default (`1`): bounded variable elimination (`elim`, `fastelim`, with AND/ITE/equivalence gate extraction `elimands`, `elimites`, `elimequivs`, `elimsubst`), congruence closure (`congruence`, extracting AND/ITE/XOR gates up to XOR arity 4), clause vivification (`vivify`, `vivifyirred`), SAT sweeping (`sweep`), SCC/equivalent-literal decomposition (`decompose`), hyper-ternary resolution (`ternary`), subsumption/self-subsuming resolution (`subsume`, `subsumestr`, `otfs`), failed-literal probing (`probe`, `probehbr`), and transitive reduction (`transred`). Disabled by default (`0`): blocked-clause elimination (`block`, L38), bounded variable addition / factoring (`factor`, L126), and variable instantiation (`instantiate`, L164).
2. **Bounded Variable Elimination (`src/elim.cpp`) & Blocked Clause Elimination (`src/block.cpp`):**
   - `elim.cpp` resolves all positive and negative occurrences of pivot $x$ (or gate-substituted subsets when `elimsubst=1`), emits every non-tautological resolvent with explicit LRAT chains (`lrat_chain.push_back(d->id); lrat_chain.push_back(c->id);`, L377–379), and then calls `proof->weaken_minus(...)` (L658, L682) before deleting the eliminated clauses.
   - `block.cpp` similarly calls `proof->weaken_minus(...)` (L274, L410, L626) to move blocked clauses onto the reconstruction stack while removing them from the active solver formula.
3. **Bounded Variable Addition / Factoring (`src/factor.cpp`) & `SBVA` (`hgarrereyn/SBVA`):**
   - Standalone `SBVA` (`hgarrereyn/SBVA` @ `35e74d02aa1b0970d53fef1c86171e596d0da453`, Haberlandt, Green, Heule, SAT 2023, `DOI: 10.4230/LIPIcs.SAT.2023.11`) eliminates BVA's fragility under variable permutation by selecting co-occurring literal partners via `tiebreaking_heuristic(lit1, lit2)` (`sbva.cc` L235–257), which computes the **3-hop walk count** in the variable-incidence graph using `Eigen::SparseVector<int>` dot products (`total_count += count * vec3->dot(*vec1)`). `SBVA` emits **unhinted ASCII DRAT** (`to_proof`, `sbva.cc` L272–283), requiring a downstream elaborator (`drat-trim` or `frat-rs`) before verified LRAT checking.
   - `CaDiCaL 3.1.0`'s internal `factor.cpp` implements bounded variable addition (including XOR and ITE gate factoring via `apply_xorite_factoring`, L1186) **with direct LRAT and VeriPB proof emission**:
     1. `add_factored_divider` (L881) adds binary clauses $(\text{fresh} \vee f_i)$ for each factor literal $f_i$. Because `fresh` has no negated occurrences yet, these clauses are **pure/blocked** (empty LRAT chain).
     2. `blocked_clause` (L897–909) emits the definition clause $(\neg\text{fresh} \vee \bigvee_i \neg f_i)$ via `proof->add_derived_rat_clause(new_id, true, externalize(not_fresh), ..., mini_chain)` where `mini_chain` contains the **negated clause IDs** of the divider clauses added in step 1.
     3. `add_factored_quotient` (L916–944) derives each replacement clause $(\neg\text{fresh} \vee C_j)$ via standard **RUP** resolving `q->bid` with the matched original clauses, then deletes the original clauses.
   - *Source-comment discrepancy observed:* `src/lrattracer.cpp` L116 still carries an outdated inline comment `// since cadical has no rat-steps`, whereas `src/factor.cpp` L907 (`add_derived_rat_clause`), `src/lratchecker.cpp` L321–452 (`check_blocked` handling negative hint IDs for ER/blocked clauses), and `src/veripbtracer.cpp` L190–217 (`red ... : x<w> -> 0|1`) all actively handle RAT steps introduced by factoring!
4. **Witness Stack & Model Reconstruction (`src/extend.cpp` L634–710):**
   - Every equisatisfiable removal (BVE, BCE, factoring) pushes `(ewit, clause)` entries onto `External::witness_data`. When `internal` finds a model of the simplified formula, `External::extend()` copies internal assignments to `vals` and iterates `witness_data` in **reverse order** (`while (p != begin)`): if the stored clause is currently falsified under `vals` (checked via blocking literal `blit` fast path then full literal scan), it flips `vals[abs(ewit)] = !vals[abs(ewit)]` (L700–709).
   - *Empirical verification (`PROBE 1`):* On $F = \{(1 \vee 2), (\neg 1 \vee \neg 2 \vee 3), (\neg 1 \vee \neg 2 \vee \neg 3), (2 \vee 3), (\neg 2 \vee \neg 3)\}$, deleting the blocked clause $(1 \vee 2)$ increases the satisfying model count from 2 to 3, introducing the invalid model $\{1 \mapsto \bot, 2 \mapsto \bot, 3 \mapsto \top\} \not\models F$. Unwinding the witness entry `(1, (1, 2))` deterministically flips variable `1` to $\top$, recovering valid $F$-models for 3/3 assignments.

---

### 2. DRAT, FRAT, LRAT, and LPR Proof Formats, Elaboration Pipelines, and Checkers

`Basis: normative + source + execution`

#### 2.1 Format Wire Semantics & Complexity Comparison

| Format | Clause IDs? | Propagation Hints? | Deletions Carry Literals? | Supported Rules | Wire Encoding | Reference Tools | Checking Cost per RUP Step |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **DRAT** | No | No | Yes (required to locate clause) | RUP, RAT | ASCII or binary (`a`/`d` + LEB128 zigzag `2*abs(l)+(l<0)`) | `drat-trim` (`drat-trim.c`), `CaDiCaL` `DratTracer` | $O(\text{BCP work})$ + global scan for RAT candidates |
| **FRAT** | Yes (`u64`) | Optional (`l <chain> 0`) | **Yes** (`d <id> <lits> 0`) + final (`f <id> <lits> 0`) + orig (`o`) + `r` reloc + `t` todo | RUP, RAT, PR | ASCII or binary (`Parser::Bin`, LEB128) | `digama0/frat` (`frat-rs`), `CaDiCaL` `FratTracer` (`--frat=1\|2`) | Elaborated in 2 passes (backward trim + forward LRAT/LPR emit) |
| **LRAT** | Yes (monotone) | **Required** (positive RUP IDs; negated RAT candidate IDs followed by sub-RUP IDs) | No (`<id> d <id1> <id2> ... 0`) | RUP, RAT | ASCII or binary (`a`/`d` + LEB128 zigzag on IDs and lits) | `lrat-check.c`, `CaDiCaL` `LratTracer`/`LratChecker`, Lean 4 `bv_decide`, `cake_lpr` | $O(\sum_{h \in H} |C_h|)$ — **independent of $|F|$** for RUP |
| **LPR** | Yes (monotone) | **Required** (same as LRAT + witness literal block between clause and hints) | No (`<id> d <ids> 0`) | RUP, RAT, **PR** | ASCII or binary (`cake_lpr` native since Mar 2024) | `tanyongkiam/cake_lpr`, `frat-rs elab` | $O(\sum |C_h|)$ for RUP; $O(|F| + \sum |C_h|)$ for PR/RAT candidate scan |
| **IDRUP / LIDRUP** | No / Yes | No / Yes | Yes / No | Incremental assumption-aware RUP | ASCII or binary | `CaDiCaL 3.1.0` (`--idrup`, `--lidrup`) | Incremental multi-query traces |

#### 2.2 Backward Elaboration in `drat-trim` vs. Two-Pass Elaboration in `FRAT-rs`

`Basis: source` (`marijnheule/drat-trim/drat-trim.c`, `digama0/frat/src/parser.rs`, `src/elab.rs`)

- **`drat-trim` (`drat-trim.c`):** Performs a forward pass to replay additions/deletions and record conflict/unit state, then runs **backward checking** (`verify`, L769) from the empty clause backwards through the proof. Only clauses marked active (`analyze`, L164) are verified by `redundancyCheck` (L616) and `checkRAT` (L551), and their recorded dependencies are emitted in LRAT format via `printLRATline` (L293) and `printDependenciesFile` (L459). Because DRAT deletions omit IDs and solvers frequently emit duplicate or unused clauses, `drat-trim` must maintain watchlists and perform full Boolean constraint propagation (BCP) during elaboration—often rivaling or exceeding solver runtime on hard UNSAT formulas.
- **`FRAT` (`digama0/frat`, Baek, Carneiro, Heule, TACAS 2021 `DOI: 10.1007/978-3-030-72016-2_4`, LMCS 2022 `DOI: 10.46298/lmcs-18(2:3)2022`):** `src/parser.rs` (L79–88) defines the `Segment` vocabulary: `Orig(id, lits)` (`o`), `Add(id, lits)` (`a`) with optional `LProof(hints)` (`l`), `Del(id, lits)` (`d`), `Final(id, lits)` (`f`), `Reloc(pairs)` (`r`), `Todo(id)` (`t`), and `Comment` (`c`).
  - Including the literals on every `d` (delete) and `f` (final) record allows `frat-rs elab` (`src/elab.rs` L917, `trim` L1041) to **stream the FRAT file strictly backwards in O(1) extra lookup work** to reconstruct the exact active clause set at every step, prune dead proof steps (unless `--full` is passed), elaborate only missing hints (falling back from bad `l` hints unless `-s`/`-ss` strict mode is enabled), and emit a trimmed `LRAT` or `LPR` proof directly streamable to `cake_lpr`.
  - In `CaDiCaL 3.1.0`, `--frat=1` emits FRAT with full LRAT `l` antecedent chains (`FratTracer::frat_add_derived_clause` L113–142), while `--frat=2` omits `l` chains (DRAT-like solver overhead with FRAT's fast backward structural framing).
- **Direct LRAT Checking Complexity (`PROBE 2`):** On an implication chain $x_1 \to x_2 \to \dots \to x_{10} \to \bot$ embedded after $N \in \{50, 200, 1000\}$ unrelated distractor clauses, our CakeML-semantics LRAT checker visits **exactly 20 literals** regardless of $N$, while an unhinted linear-scan RUP loop scales $120 \to 420 \to 2020$ literal visits ($6\times \to 21\times \to 101\times$). Note that watch-list DRAT checkers like `drat-trim` avoid touching non-watched distractors during unit propagation, but still pay watchlist maintenance and full-database scans on RAT pivots—and crucially, **hint-indexed LRAT checking eliminates search/watchlists entirely**, making formal verification of the checker trivial in HOL4 and Lean 4.

---

### 3. Machine-Checked SAT Proof Checkers: `cake_lpr` (CakeML/HOL4) vs. Lean 4 `bv_decide`

`Basis: source + normative`

#### 3.1 `cake_lpr` End-to-End Machine-Code Verification (`HOL4` + `CakeML`)

Inspection of `tanyongkiam/cake_lpr` (`033aad53d1733bd4b8ca41cf6f1b5fb5d84f8de2`) and its pinned `CakeML/cakeml` submodule (`665f9b21712ad093e10a404ccc2f78e64a34aeef`, `examples/lpr_checker/lprScript.sml` and `array/lpr_arrayFullProgScript.sml`, Tan, Heule, Myreen, TACAS 2021 `DOI: 10.1007/978-3-030-72013-1_12`) reveals the exact verified logic:

1. **Core Logical Specification (`lprScript.sml` L50–259):**
   - `is_AT fml (i::is) C` (L76–86): looks up clause `i` in `sptree` `fml`, computes `delete_literals Ci C`: returns `SOME (INL ())` on empty residual (conflict), recurses with `(-l :: C)` on unit `[l]`, and fails (`NONE`) if `i` is missing or leaves $\ge 2$ literals.
   - `overlap_assignment w C = w ++ flip (delete_literals C w)` (L105–108): formalizes the witness-overridden assignment $\tau = \omega \cup (\bar{C} \setminus \text{dom}(\omega))$.
   - `check_PR fml w C ik (i, Ci)` (L144–163): for every active clause `(i, Ci)` touched by `flip w`:
     - If `i` is absent from hint alist `ik`: requires `check_overlap Ci w` (clause satisfied directly by witness $\omega$).
     - If `i` maps to empty hint `[]`: requires `check_overlap Ci (overlap_assignment w C)` (clause satisfied by $\tau$).
     - If `i` maps to non-empty hints `is`: requires `is_AT fml is (C ++ delete_literals Ci (flip (overlap_assignment w C))) = SOME (INL ())`.
   - `is_PR` (L165–179): checks `is_AT` first; if not AT, checks `p ≠ 0`, dispatches `NONE => check_RAT`, and for `SOME w` enforces **witness consistency** `¬(check_overlap w (flip w))` before `EVERY (check_PR fml w D ik) iCs`.
   - `check_lpr_step mindel step fml` (L186–199): enforces `mindel < n` on every `PR` addition and `EVERY ($< mindel) cl` on every `Delete`, protecting clause indices $\le \text{mindel}$ from deletion or overwrite.
2. **Transformation & Two-Level Parallel Checking (`lprScript.sml` L1076–1282, `cake_lpr/README.md` L37–50):**
   - Beyond UNSAT checking (`check_lpr_unsat_sound`, L1076), the `mindel` guard proves **equisatisfiable formula transformation soundness** (`check_lpr_sat_equiv_fml`, L1134: `cake_lpr <in.cnf> <proof.lpr> <out.cnf>`), used to certify preprocessors/reencodings like `SBVA` independently of the downstream SAT solver.
   - `check_lpr_range_sound` (L1282) supports **two-level parallel checking** (`cake_lpr <cnf> <summary> i-j <slice.lpr>` followed by `-check`), allowing massive multi-gigabyte proofs to be verified across parallel slices with a verified interval-coverage check.
3. **Machine-Code TCB (`array/lpr_arrayFullProgScript.sml` L1667–1775):**
   - `check_unsat_spec` and `check_unsat_whole_prog_spec2` connect the mutable array-backed imperative CakeML implementation (`lpr_arrayFullProgScript.sml`) to the abstract `sptree` specification via separation logic (`COMMANDLINE cl * STDIO fs`), and `check_unsat_semantics` (L1772) composes this with the verified CakeML compiler to produce audited assembly (`cake_lpr.S` for x86-64, `cake_lpr_arm8.S` for ARMv8, checksummed in `cake_lpr.sha256`).
   - Operational caveat from `tanyongkiam/cake_lpr/README.md` (L16–22, L97–105): as of `2026-07-22`, heap/stack sizing moved from environment variables to CLI flags `--CML_HEAP_SIZE=<MiB>` / `--CML_STACK_SIZE=<MiB>` (default `4096` MiB each, parsed in `basis_ffi.c`); binary LPR/LRAT is supported natively (`2024-03-11`); and the `2026-11-01` release marks the final planned `cake_lpr` update prior to a successor checker.

#### 3.2 Lean 4 `bv_decide` Pipeline, LRAT Checker, and Reflection TCB

`Basis: source + normative` (`leanprover/lean4` @ `0171678607a54e5a72c6a4ab6409286ba5002b05`; Böving et al., PACMPL/OOPSLA, `DOI: 10.1145/3763167`)

Inspection of `src/Lean/Elab/Tactic/BVDecide.lean`, `src/Lean/Meta/Tactic/BVDecide/{Main,External,Prover/Bitblast,LRAT/Trim}.lean`, and `src/Std/Tactic/BVDecide/{Reflect,LRAT/Checker,LRAT/Actions,LRAT/Internal/Checker,LRAT/Internal/Rat}.lean` establishes the exact architecture and trust boundary:

1. **8-Stage End-to-End Architecture (`BVDecide.lean` L46–64, `External.lean` L158–239):**
   1. Proof by contradiction (`false_or_by_contra`) + Bitwuzla-derived normalization (`bv_normalize` + `seval` simp sets + EPR quantifier normalization in `Main.lean` L38–40).
   2. Reification into `BVLogicalExpr` -> verified bit-blasting into an And-Inverter Graph (`Std.Sat.AIG`, `bv.bitblast.relabelNat`) -> verified Tseitin conversion (`AIG.toCNF`, proven equisatisfiable via `AIG.toCNF_equisat`, `Reflect.lean` L198).
   3. External SAT invocation (`External.lean` L158–226): invokes shipped `cadical` (or `sat.solver`) with `--<unsat|sat|default> --lrat --quiet --binary=<0|1> --shrink=0` (default `sat.binaryProofs = true`, `sat.timeout = 10` s). In incremental CEGAR mode (`addIncremental`, L180–188), also passes `--ilb=2 --lucky=0` because CaDiCaL's `lucky` phase is quadratic across incremental calls.
   4. Optional LRAT trimming (`Lean/Meta/Tactic/BVDecide/LRAT/Trim.lean`, default `sat.trimProofs = true`), implementing Pollitt, Fleury, and Biere's linear-time backward LRAT trimmer (SAT 2023, `DOI: 10.4230/LIPIcs.SAT.2023.21`) to drop unused steps and compact clause IDs before reflection.
   5. Verified LRAT checking (`Std.Tactic.BVDecide.LRAT.Internal.check`, `Checker.lean` L21–86): supports `addEmpty`, `addRup`, `addRat`, and `del` (`Actions.lean` L26–30), proved sound via `unsat_of_check : check proof formula → CNF.Unsat formula`.
2. **Critical Trust-Boundary Distinction (`Bitblast.lean` L27–59, `BVDecide.lean` L42–44 & L65–67):**
   - `LratCert.toReflectionProof` (`Bitblast.lean` L40) discharges `verifyBVExpr reflectedExpr certExpr = true` via `nativeEqTrue \`bv_decide reflectionTerm`, which compiles the term to native code and emits an axiom (`Lean.ofReduceBool` / native evaluation). Therefore, **unlike `cake_lpr` (which verifies the compiler down to machine code) or pure kernel-reduced reflection (`decide`), `bv_decide` places the entire Lean 4 compiler, runtime, and native code generator inside the TCB!**
   - Furthermore, setting `debug.skipKernelTC = true` disables LRAT checking altogether and silently trusts the external SAT solver (`BVDecide.lean` L42–44).
   - **Rule & Performance Boundary:** Lean 4's `IntAction` (`Actions.lean` L26–30) supports **RUP and RAT only—no PR witness steps**—and `checkRat` (`Rat.lean` L20–49) scans the entire active clause database (`checkRatHintsExhaustive`) and copies `Assignment` non-linearly on each RAT candidate, explicitly noting that RAT steps are expected to be rare (`Rat.lean` L41–44). Thus enabling `--factor=1` or external PR preprocessors can degrade or break `bv_decide` certificate checking unless elaborated to pure LRAT.

| Verification Dimension | `cake_lpr` (`CakeML`/`HOL4`) | Lean 4 `bv_decide` (`Std.Tactic.BVDecide`) | `drat-trim` / `lrat-check` (C) | `VeriPB` / `CakePB` |
| :--- | :--- | :--- | :--- | :--- |
| **Input Format** | DIMACS CNF + ASCII/binary LPR/LRAT | Lean `BitVec`/`Bool` goal $\to$ AIG $\to$ CNF + binary/ASCII LRAT | DIMACS CNF + DRAT / LRAT | OPB / WCNF + VeriPB v1–v3 |
| **Inference Rules Verified** | RUP, RAT, **PR** (with arbitrary witness $\omega$) | RUP, RAT (no PR) | RUP, RAT (no PR in `lrat-check`) | Cutting planes (`pol`), RUP, `red` (witness), `dom` (preorder), objective bounds |
| **Trusted Computing Base (TCB)** | HOL4 kernel + `basis_ffi.c` + assembler/OS/HW (CakeML compiler verified) | Lean 4 kernel + **Lean 4 compiler & native runtime (`Lean.ofReduceBool`)** | Unverified C code (~1.5k LOC `drat-trim`, ~500 LOC `lrat-check`) | `VeriPB`: unverified Python/C++ + GMP; `CakePB`: HOL4 + CakeML verified binary |
| **Transformation / Equisat Mode** | Yes (`mindel` + canonical clause set check) | No (UNSAT refutation only) | No | Yes (core/derived split + output check) |

---

### 4. Pseudo-Boolean `VeriPB` Proofs, Checked Core Deletion, and Certified Core-Guided MaxSAT

`Basis: normative + source + execution`

Clausal proof systems (`DRAT`/`LRAT`/`LPR`) cannot naturally express cardinality constraints ($\sum a_i l_i \ge k$), linear-arithmetic cutting planes, symmetry breaking via preorders, or **optimization optimality** (proving both an upper bound via a concrete feasible solution and a matching lower bound across all assignments).

#### 4.1 `VeriPB` Calculus and Checked Core Deletion (`pseudo-Boolean proof version 3.0`)

Inspection of `StephanGocht/VeriPB/README.rst` (L144–620) and `arminbiere/cadical/src/veripbtracer.cpp` (L190–380) establishes the VeriPB proof calculus:

1. **Normalized 0–1 Pseudo-Boolean Constraints:** Every constraint is stored as $\sum_i a_i \ell_i \ge d$ with $a_i, d \in \mathbb{Z}_{\ge 0}$ and $\ell_i \in \{x_i, \bar{x}_i\}$. A CNF clause $(x_1 \vee \neg x_2)$ encodes as `1 x1 1 ~x2 >= 1 ;`.
2. **Cutting Planes (`pol`) & RUP (`rup`):** Reverse-Polish operations (`+` addition, `*` positive scalar multiplication, `d` division with ceiling rounding $\lceil \cdot / k \rceil$, `s` Boolean saturation clamping coefficients to $d$, literal axioms `x1`/`~x1`, and `w` weakening). In `CaDiCaL 3.1.0` (`veripbtracer.cpp` L219–254), each LRAT antecedent chain is translated directly into cutting-planes resolution via `pol <c_n> <c_{n-1}> + s ...;` followed by syntactic equality check `e <clause> >= 1 : <id>;`.
3. **Redundance (`red`) & Dominance (`dom`) Strengthening (`Bogaerts, Gocht, McCreesh, Nordström, AAAI 2022, DOI: 10.1609/aaai.v36i4.20283`):**
   - `red C ; \omega` checks $F \wedge \neg C \models (F \wedge C)|_\omega$ (plus objective non-worsening $f(\omega) \le f(x)$ in optimization mode), strictly generalizing PR and supporting explicit cutting-planes `subproof` / `proofgoal` blocks (`README.rst` L382–414).
   - `dom C ; \omega` certifies symmetry and dominance breaking against a user-declared transitive preorder (`pre_order ... transitivity ... load_order`) by proving $\omega$ maps any falsifying model of $C$ to a strictly better ($\prec$) model of $F_{\text{core}}$, without losing optimal solutions.
4. **Why Checked Core Deletions (`core id` / `delc`) Are Mandatory for Soundness (`PROBE 2`):**
   - In pure UNSAT SAT refutation, deleting any clause weakens $F$ and can never turn a SAT formula into an UNSAT one—*unless* combined with an optimization objective or dominance preorder!
   - **Concrete Counterexample (`PROBE 2`):** Consider $\min(x_1 + x_2)$ subject to core constraint $C_1: (x_1 \vee x_2)$ (`1 x1 1 x2 >= 1`), whose true minimum is `1`. If an unchecked deletion removes $C_1$, the remaining database is empty, making both $(\neg x_1)$ and $(\neg x_2)$ vacuously RAT/redundancy-valid (`red`). Adding them forces $x_1 = x_2 = 0$ and falsely certifies optimal cost `0`!
   - VeriPB 3.0 (tracked in `CaDiCaL 3.1.0` `veripbtracer.cpp` L212–292 via `checked_deletions`, `--veripb=1|3`) therefore partitions the database into **core** (`F_core`, moved via `core id`) and **derived** (`F_derived`) sets: `del id` removes derived constraints freely, whereas deleting a core constraint (`delc`) requires proving the deleted constraint is still redundant with respect to the remaining core (or keeping it tracked via `weaken_minus` / `strengthen`).

#### 4.2 Core-Guided MaxSAT (`RC2`/OLL) and Certified Proof Logging

`Basis: source + normative` (`pysathq/pysat/examples/rc2.py` L682–1250; Berg et al., CADE 2023 `DOI: 10.1007/978-3-031-38499-8_1`; Gocht et al., AAAI 2024 `DOI: 10.1609/aaai.v38i8.28642`)

In weighted partial MaxSAT, an instance specifies hard clauses $H$ and weighted soft clauses $\{(w_i, S_i)\}$ with objective $\min \sum_i w_i \cdot b_i$ where relaxation/blocking literal $b_i$ is falsified iff $S_i$ is violated.

1. **Core-Guided OLL Algorithm (`pysat/examples/rc2.py`):**
   - `RC2.compute_()` queries an incremental CDCL oracle under assumptions asserting all soft selectors (`core_sels`) and current totalizer output literals (`core_sums`).
   - When the oracle returns an UNSAT core $K$ with minimum weight $w_{\min} = \min_{l \in K} w(l)$, `process_core()` (L770–817) increases the lower bound `self.cost += w_min`, splits weights exceeding $w_{\min}$, encodes the cardinality sum $\sum_{l \in K} \neg l$ via an incremental unary Totalizer network (`create_sum` L1169 / `update_sum` L1223), optionally probes tight bounds via `exhaust_core` (L1054), and adds the next bound literal $\neg o_b$ back to assumptions. Intrinsic `AtMost1` cliques (`adapt_am1`, L819) are collapsed before solving to tighten bounds early.
   - `PySAT`'s `RC2` implementation (`ff051b57496492822a52c510bbd082f840bd792f`) emits **no proof logs**—the reported optimum trusts both the incremental SAT oracle and the totalizer/weight-splitting bookkeeping.
2. **Certified Core-Guided MaxSAT in VeriPB / CakePB (Berg et al., CADE 2023):**
   - Each UNSAT core $K$ returned by the SAT oracle is justified in VeriPB as a derived clause $\bigvee_{l \in K} \neg l$ (via `rup` or `pol` from the SAT solver's proof trace), which translates directly into the pseudo-Boolean lower-bound inequality $\sum_{l \in K} \neg l \ge 1$.
   - Totalizer auxiliary output variables $o_1, \dots, o_k$ are introduced via **reification** (`red` steps defining $o_j \leftrightarrow (\sum_{l \in K} \neg l \ge j)$), and the objective function is **reformulated** in-place (`obju` / cutting-planes combination) by subtracting $w_{\min} \cdot (\sum_{l \in K} \neg l - \sum_{j=2}^{|K|} o_j - 1) \ge 0$, raising the constant offset of the objective by $+w_{\min}$!
   - When the SAT oracle finally returns a satisfying assignment $\rho$ matching the accumulated constant offset, logging `soli`/`o` (`README.rst` L594–620) records $\rho$ as upper bound $U$ and adds $f(x) \le U - 1$; adding that bound to the reformulated objective inequality $f(x) \ge U$ yields an immediate 1-step cutting-planes contradiction $0 \ge 1$, certifying global optimality!
   - Replacing VeriPB's unverified Python/C++ checker with **`CakePB`** (Gocht, McCreesh, Myreen, Nordström, Oertel, Tan, AAAI 2024, `DOI: 10.1609/aaai.v38i8.28642`) closes the TCB down to CakeML-verified machine code, mirroring `cake_lpr`'s guarantee for pseudo-Boolean and MaxSAT proofs.

---

### 5. QBF / 2QBF / DQBF Solving, Dependency Schemes, and Certified Skolem Extraction

`Basis: normative + source + execution`

Quantified Boolean Formulas generalize SAT by prefixing a CNF matrix $\phi$ with alternating universal ($\forall$) and existential ($\exists$) quantifiers. Complexity jumps sharply with quantifier structure:

| Logic Class | Quantifier Structure | Decision Complexity | Winning Witness (TRUE) | Refutation Witness (FALSE) | Primary Examined Tools |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **SAT** | $\exists X.\, \phi(X)$ | $\text{NP}$-complete | Assignment $\alpha : X \to \{0,1\}$ | DRAT / LRAT / LPR / VeriPB refutation | `CaDiCaL`, `cake_lpr`, `bv_decide` |
| **2QBF** | $\forall U\,\exists E.\, \phi(U, E)$ | $\Pi_2^P$-complete | **Skolem functions** $f_e(U)$ (e.g., AIGER circuit) | Concrete universal assignment $\alpha_U$ + SAT UNSAT proof of $\phi(\alpha_U, E)$ | `CADET` (`markusrabe/cadet`) |
| **Prenex QBF** | $Q_1 X_1 \dots Q_k X_k.\, \phi$ (linear prefix) | $\text{PSPACE}$-complete | Skolem functions $f_e(\{u \mid u <_P e\})$ (AIGER) | Herbrand functions $g_u(\{e \mid e <_P u\})$ or Q-Res / LDQ-Res / QRAT proof | `DepQBF`, `qrat-trim` + `cheskol` |
| **Henkin DQBF** | $\forall U\,\exists e_1(D_1)\dots\exists e_m(D_m).\, \phi$ (arbitrary $D_i \subseteq U$) | $\text{NEXPTIME}$-complete (Peterson, Reif, Azhar 2001) | Skolem functions $f_{e_i}(D_i)$ respecting non-linear information sets | Fork-resolution / DQBF-expansion / Herbrand strategy | Theoretical boundary (see `## Boundaries`) |

#### 5.1 Incremental Determinization & AIGER Skolem Synthesis in `CADET` (2QBF)

`Basis: source + normative + execution` (`markusrabe/cadet` @ `40f9683261013780b5c6cddf9cb3112d0f71d187`; Rabe & Seshia, SAT 2016 `DOI: 10.1007/978-3-319-40970-2_23`)

Rather than searching over partial assignments to $U \cup E$ (as in QCDCL), `CADET` searches over **partial Skolem functions**—maintaining a set of currently *deterministic* variables $\mathcal{D}$ (initialized to all universal variables $U$, `src/skolem.c` L87) whose behavior is uniquely fixed as Boolean functions of $U$:

1. **Unique-Consequence Propagation (`src/skolem.c` `skolem_propagate` L573, `skolem_check_for_unique_consequence` L194):**
   - A clause $C$ has **unique consequence** $l \in C$ ($l$ existential) if every other literal $k \in C \setminus \{l\}$ belongs to $\mathcal{D}$ (already deterministic). Intuitively, $C$ forces $l = \top$ whenever $\bigwedge_{k \in C \setminus \{l\}} \neg k$ holds.
   - `CADET` checks via an internal incremental SAT solver (`s->skolem`, `skolem.c` L38) whether the positive-forcing and negative-forcing unique-consequence antecedents of an existential variable $e$ can ever be simultaneously satisfied under $U$.
   - If conflict-free, $e$ becomes deterministic with Skolem function $f_e = \bigvee_{C \in \text{UC}(+e)} \bigwedge_{k \in C \setminus \{+e\}} \neg k$ (and symmetrically for $\neg e$); if a conflict occurs (`s->conflict_var_id`), `CADET` runs **conflict analysis over Skolem dependencies** (`src/skolem_conflict_analysis.c`, `cadet2.c` L373–388) to learn a new 2QBF clause eliminating the conflicting universal assignment—or concludes `UNSAT` if a universal counterexample assignment (`c2->examples`) falsifies all existential extensions (`src/certify_UNSAT.c`, L20).
   - When propagation stalls before all existentials are deterministic, `CADET` makes a **determinization decision** (e.g., setting remaining choices to a constant or selecting a clause's polarity) and backtracks on conflict (`c2_backtrack_to_decision_lvl`, `cadet2.c` L213).
2. **Direct AIGER Skolem Circuit Emission (`src/certify_SAT.c` L40–180):**
   - `cert_setup_AIG` (L40–60) creates one AIGER primary input per original universal variable.
   - `cert_encode_unique_antecedents` (L107–140) walks each determinized existential variable in determinization order, builds an AND-gate chain (`aigeru_AND`) for the negated non-consequence literals of each unique-consequence clause (`cert_get_unique_consequence(unique_consequences, c) == lit`), and combines all clauses with `aigeru_multiOR` (L133), negating the output when `lit < 0`.
   - For CEGAR / case-split branches (`cert_encode_CEGAR`, L163–180), `CADET` multiplexes per-case decision-level functions guarded by `cert_encode_c2_cube` (L149–160). Because the raw AIGER circuit can be redundant, `CADET`'s `README.md` (L51–55, L130–132) notes that standard `Certcheck` certificates can be simplified via `abc -c "read result.aig; dc2; write result.aig"`, whereas `--qbfcert` ASCII `.aag` certificates must not be ABC-minimized.
   - *Empirical verification (`PROBE 3`):* Running the exact unique-consequence determinization loop on $\forall u_1, u_2\,\exists e_1, e_2.\, (e_1 \leftrightarrow u_1 \wedge u_2) \wedge (e_2 \leftrightarrow e_1 \oplus u_2)$ determinizes in topological order `[e1=3, e2=4]`, emits the AIG definitions `e3 = (u1 ∧ u2)` and `e4 = (e3 ∧ ¬u2) ∨ (¬e3 ∧ u2)`, and passes exhaustive verification over all $2^2$ universal assignments.

#### 5.2 QCDCL, Dependency Schemes, Long-Distance Q-Resolution, and `DepQBF 6.03` Proof Boundaries

`Basis: source + normative` (`lonsing/depqbf` @ `2ad3995a21b8ca2831be2534b1cb80df342b3bdf`; Slivovsky & Szeider, TCS 2016 `DOI: 10.1016/j.tcs.2015.10.020`)

`DepQBF 6.03` (`README` L19–165, `qdpll.c`, `qdpll_dep_man_qdag.c`) implements conflict-driven clause and solution-driven cube learning (`QCDCL`) enhanced with:

- **Standard Dependency Scheme ($D_{\text{std}}$) (`qdpll_dep_man_qdag.c`):** Computes a compact directed acyclic dependency graph (`QDAG`, `extract_dependencies_from_lits` L2047, transitive reduction L2213) capturing when an existential variable $e$ and an outer universal variable $u$ are connected via an existential resolution path. Whenever $(u, e) \notin D_{\text{std}}$, `DepQBF` may decide $e$ before $u$ and perform universal reduction of $u$ even in the presence of $e$.
- **Long-Distance Q-Resolution (`LDQ-Res`) (`qdpll.c` L1181, L6184; `README` L109–114):** Standard Q-resolution forbids merging complementary universal literals ($u$ and $\neg u$) when resolving on an existential pivot $e$; `LDQ-Res` permits merged universal literals $u^*$ provided $u$ is quantified to the **right** of the pivot $e$ ($e <_P u$).
- **Generalized Axioms & Dynamic QBCE (`README` L19–45, L115–125):** `DepQBF 6.03` embeds `PicoSAT` and `Nenofex` as sub-oracles for generalized axioms, enables dynamic QBF blocked-clause elimination (`QBCE`) by default, and uses lazy QPUP clause learning (`--traditional-qcdcl` disables it).
- **Mandatory Proof-Logging Restrictions (`README` L147–150):** To emit machine-checkable `QRP` / binary `bqrp` traces (`--trace=qrp|bqrp` for `QBFcert`), `DepQBF 6.03` explicitly **forbids** incremental solving, **requires `--dep-man=simple`** (disabling `D_std` in favor of the linear quantifier prefix), and **requires `--no-lazy-qpup`**.
- **Dependency-Scheme Soundness Boundary (Slivovsky & Szeider, TCS 2016):** While $D_{\text{std}}$ is sound for Q-resolution (`Q(D_std)-Res`), more aggressive dependency schemes such as the reflexive resolution-path dependency scheme ($D_{\text{rrs}}$) are **unsound** when combined naively with `LDQ-Res` or standard universal reduction—allowing false refutations of true QBFs unless paired with a restricted calculus.

#### 5.3 `QRAT` Unified Proof System and Certified Skolem Extraction (`qrat-trim` + `cheskol`)

`Basis: normative + source + execution` (`marijnheule/qrat-trim` @ `5d6a1b60c1108755975b47b15d3676afeb3dbb65`; Heule, Seidl, Biere, IJCAR 2014 `DOI: 10.1007/978-3-319-08587-6_7`, JAR 2017 `DOI: 10.1007/s10817-016-9390-4`)

1. **Why Propositional RAT Fails on QBF (`PROBE 3`):** Consider the **TRUE** QBF $\exists x\,\forall u.\, (x \vee u) \wedge (x \vee \neg u)$ (witnessed by $x = \top$). Propositionally, adding $C = (\neg u)$ on pivot $\neg u$ is a valid RAT step: the sole clause containing $+u$ is $(x \vee u)$, whose resolvent with $(\neg u)$ is $(x)$, and $(x)$ is RUP from $(x \vee u) \wedge (x \vee \neg u)$ (`PROBE 3`: `SAT-RAT accepts (-u): True`). Yet adding $(\neg u)$ turns the QBF into $\exists x\,\forall u.\, (x \vee u) \wedge (x \vee \neg u) \wedge (\neg u)$, which is **FALSE** (setting $u = \top$ falsifies $(\neg u)$ regardless of $x$).
2. **`QRAT` Rules Enforced in `qrat-trim.c` (L237–305, L830–972):**
   - For any clause $D$ and literal $l$, define the **outer clause** $O(D, l) = \{k \in D \mid \text{lv}(k) \le \text{lv}(l)\}$ (implemented at `qrat-trim.c` L864 and L891: `if (S->level[abs(lit)] > thisLevel) continue;`).
   - **`QRATA` (Clause Addition):** Adding $C$ on pivot $l \in C$ requires $l$ to be **existential** (`if (!uni && thisLevel % 2) return FAILED;`, L830–832) and requires every resolution candidate $D \in F$ with $\neg l \in D$ to satisfy $F \wedge \overline{C} \wedge \overline{O(D, \neg l) \setminus \{\neg l\}} \vdash_1 \bot$.
   - **`QRATE` (Clause Elimination):** Symmetric existential clause deletion on existential pivot $l \in C$ (validates QBCE and existential variable elimination).
   - **`QRATU` (Universal Literal Elimination, `u` prefix):** Removing a **universal** literal $u$ from clause $C$ requires $u$ to satisfy the QRAT check (`EURcheck` / universal QRAT on `u`, L252–302, L968–970), generalizing standard universal reduction (`URcheck`, L237–250).
3. **Certified Skolem Extraction & Independent AIG Verification (`qrat-trim.c` L522–770, `cheskol.c` L127–255):**
   - For a **TRUE** QBF reduced to the empty formula by a QRAT preprocessing/solving proof (sequence of `QRATE` / `QRATU` steps), `qrat-trim` constructs a Skolem AIG (`printSkolem`, L522, emitting AND gates via `printAND`, L369–400) by unwinding the deleted existential clauses in reverse order—the exact quantified analogue of `CaDiCaL`'s `External::extend` witness stack, except each witness flip becomes a conditional Boolean gate conditioned on outer literals!
   - The `BLUEVERSION` optimization (`qrat-trim.c` L841–946) tests whether inner literals (`lv > thisLevel`) can be dropped from candidate checks so the extracted Skolem circuit depends only on required outer clauses (`outerrequired` vs. `inneronly`).
   - `cheskol.c` (L193–255) independently checks the resulting AIGER Skolem circuit against the original QDIMACS formula by verifying that: (i) every AIG input is a universal variable (`if (Q[idx] > 0) die(...)`, L204), (ii) every AIG output corresponds to a valid existential variable (`Q[idx] < 0` rejected, L217), (iii) each existential gate respects prefix quantifier order (acyclic dependency check), and (iv) conjoining the Tseitin encoding of the AIG with the negated QBF matrix yields a propositional CNF whose UNSAT status (checked via a SAT solver + LRAT/cake_lpr!) certifies the Skolem strategy with zero trust in the QBF solver!

---

## Boundaries

- **Known not to apply — Propositional DRAT/LRAT/LPR checkers to QBF or MaxSAT Optimization:** Standard `drat-trim`, `lrat-check`, `cake_lpr`, and Lean 4 `bv_decide` cannot check universal quantifier reduction, outer-clause QRAT rules, or pseudo-Boolean objective bounds. Applying propositional RAT to QBF is provably unsound (`PROBE 3`), and unchecked clause deletion under optimization objectives is provably unsound (`PROBE 2`).
- **Unsupported — PR Steps in Lean 4 `bv_decide` (`leanprover/lean4` @ `0171678607a54e5a72c6a4ab6409286ba5002b05`):** `Std.Tactic.BVDecide.LRAT.Action` only models `addEmpty`, `addRup`, `addRat`, and `del`. Proofs containing Propagation Redundancy witnesses (`LPR`) or VeriPB cutting-planes steps cannot be ingested by `bv_check` / `bv_decide` without first compiling PR to DRAT/LRAT (e.g., via `frat-rs from-pr`, which may incur exponential blowup on PR-only short proofs).
- **Unsupported — `QRP` Proof Tracing with `D_std`, Lazy QPUP, or Incremental Mode in `DepQBF 6.03`:** `lonsing/depqbf` explicitly prohibits combining `--trace` with `--dep-man=qdag` (default), lazy QPUP (default), or incremental push/pop/clause-group solving (`README` L147–150).
- **Unsupported — Generalized Prenex QBF ($\ge 3$ alternations) in `CADET`:** `markusrabe/cadet` (`40f9683261013780b5c6cddf9cb3112d0f71d187`) implements incremental determinization exclusively for 2QBF ($\forall\exists$) formulas.
- **Not examined — Native Binary Compilation / Wall-Clock Benchmarking:** No C/C++/Rust/CakeML binaries (`cadical`, `cake_lpr`, `frat-rs`, `cadet`, `depqbf`, `qrat-trim`) were compiled or benchmarked on SAT Competition / QBFEVAL corpora during this investigation; runtime scaling claims rely on source inspection, published complexity theorems, and our Python micro-probe literal-visit measurements.
- **Not examined — Concrete DQBF Solvers & `CakePB` HOL4 Scripts:** Standalone DQBF solvers (e.g., `HQS`, `DQBDD`, `pedant`) and the HOL4 source repository for `CakePB` (`Gocht et al., AAAI 2024`) were not fetched at commit-pinned source level; DQBF coverage is grounded in published complexity and dependency-scheme soundness theorems (Peterson, Reif, Azhar 2001; Slivovsky & Szeider 2016).
- **Unknown — Exact Successor Checker Replacing `cake_lpr`:** `tanyongkiam/cake_lpr/README.md` (L16, dated `2026-11-01`) states that `cake_lpr` is at its final release and will be superseded by a new checker in the repository, but the successor's interface and verified rule set are not yet present at commit `033aad53d1733bd4b8ca41cf6f1b5fb5d84f8de2`.

---

## Evidence

### 1. Inspected Upstream Source Revisions (2026-11-19)

- **`arminbiere/cadical` @ `6b3d70b9ce00ecbce3f829bab76d185f0e92618c` (`v3.1.0`):**
  - `VERSION`: `3.1.0`.
  - `src/options.hpp` L37–310: default flags (`binary=1`, `block=0`, `congruence=1`, `decompose=1`, `elim=1`, `factor=0`, `frat=0`, `idrup=0`, `lidrup=0`, `lrat=0`, `probe=1`, `subsume=1`, `sweep=1`, `ternary=1`, `veripb=0`, `vivify=1`).
  - `src/proof.hpp` L80–116 & `src/proof.cpp` L295, L370–392, L563–575: `add_derived_rat_clause`, `weaken_minus`, `weaken_plus`, `strengthen`.
  - `src/lrattracer.cpp` L40–147: LEB128 zigzag encoding (`2*abs(x)+(x<0)`), lazy deletion batching, stale comment at L116 (`// since cadical has no rat-steps`).
  - `src/frattracer.cpp` L71–185: FRAT `o`, `a` (with optional `l`), `d` (with literals), `f` emitters.
  - `src/veripbtracer.cpp` L190–380: VeriPB `pseudo-Boolean proof version 3.0`, `red ... : x<w> -> 0|1`, `pol ... + s` + `e`, `rup`, `core id`, `delc` vs `del id`, `weaken_minus`/`strengthen`.
  - `src/lratchecker.cpp` L305–515: online LRAT verification including `check_blocked` (L391–452) for negative-ID ER/blocked chains.
  - `src/factor.cpp` L881–945, L1153–1205: `add_factored_divider`, `blocked_clause` (calls `add_derived_rat_clause` L907), `add_factored_quotient`, `apply_xorite_factoring`.
  - `src/elim.cpp` L377–379, L658, L682; `src/block.cpp` L274, L410, L626; `src/extend.cpp` L634–710 (`External::extend` reverse witness unwinding).
- **`hgarrereyn/SBVA` @ `35e74d02aa1b0970d53fef1c86171e596d0da453`:**
  - `sbva.cc` L235–257 (`tiebreaking_heuristic` 3-hop sparse-vector dot product), L272–283 (`to_proof` ASCII DRAT emitter), L331–464 (`run` matched-literal/clause factoring loop).
- **`tanyongkiam/cake_lpr` @ `033aad53d1733bd4b8ca41cf6f1b5fb5d84f8de2` & `CakeML/cakeml` @ `665f9b21712ad093e10a404ccc2f78e64a34aeef`:**
  - `cake_lpr/README.md` L6–52, L97–105: pinned `HOL4` (`9783a49979c94c401ff8c0e51b2eefae7ea95ae3`) & `CakeML` (`665f9b21712ad093e10a404ccc2f78e64a34aeef`), CLI modes (UNSAT, transformation, two-level parallel), `--CML_HEAP_SIZE`/`--CML_STACK_SIZE` flag change (`2026-07-22`), binary LPR support (`2024-03-11`), final release notice (`2026-11-01`).
  - `examples/lpr_checker/lprScript.sml` L50–259, L563–1282: `is_AT`, `overlap_assignment`, `check_RAT`, `check_PR`, `is_PR` (witness consistency check L176), `check_lpr_step` (`mindel` guard L186–199), `check_lpr_unsat_sound` (L1076), `check_lpr_sat_equiv_fml` (L1134), `check_lpr_range_sound` (L1282).
  - `examples/lpr_checker/array/lpr_arrayFullProgScript.sml` L1667–1775: `check_unsat_spec`, `check_unsat_whole_prog_spec2`, `check_unsat_semantics`.
- **`leanprover/lean4` @ `0171678607a54e5a72c6a4ab6409286ba5002b05`:**
  - `src/Lean/Elab/Tactic/BVDecide.lean` L20–68, L166–195: architecture, options (`sat.trimProofs`, `sat.binaryProofs`, `debug.skipKernelTC`), compiler TCB disclosure (L65–67).
  - `src/Lean/Meta/Tactic/BVDecide/External.lean` L158–239: CaDiCaL flags (`--lrat --quiet --binary=... --shrink=0`, incremental `--ilb=2 --lucky=0`).
  - `src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean` L27–59: `LratCert.toReflectionProof` invoking `nativeEqTrue \`bv_decide` (L40) to construct `unsat_of_verifyBVExpr_eq_true`.
  - `src/Lean/Meta/Tactic/BVDecide/LRAT/Trim.lean` L15–120: linear-time LRAT proof trimming citing SAT 2023.
  - `src/Std/Tactic/BVDecide/Reflect.lean` L174–202 (`verifyCert`, `verifyBVExpr`, `unsat_of_verifyBVExpr_eq_true`); `LRAT/Actions.lean` L26–30 (`Action` constructors); `LRAT/Internal/Checker.lean` L21–86 (`check`, `unsat_of_check`); `LRAT/Internal/Rat.lean` L20–75 (`checkRat`, `checkRatHintsExhaustive`, non-linear `Assignment` copy note).
- **`digama0/frat` @ `aa18581497830b49a6ab6cbc9e0dc778c14885b5` & `marijnheule/drat-trim` @ `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`:**
  - `frat/README.md` L26–108; `frat/src/parser.rs` L79–129 (`Segment` variants & binary LEB128); `frat/src/elab.rs` L917, L1041 (`elab`, `trim`).
  - `drat-trim/drat-trim.c` L164, L293, L551, L616, L769; `drat-trim/lrat-check.c` L88–155 (`checkRedundancy`, `checkClause`, `DELETED` detection).
- **`StephanGocht/VeriPB` @ `01b7b5088c8a67f1611427174501191bc5f5b365` & `pysathq/pysat` @ `ff051b57496492822a52c510bbd082f840bd792f`:**
  - `VeriPB/README.rst` L144–620 (`f`, `pol`, `rup`, `del`, `red`, `dom`, `subproof`/`proofgoal`, `core id`, `v`/`ov`/`o`).
  - `pysat/examples/rc2.py` L157, L682–1250 (`RC2`, `compute_`, `process_core`, `adapt_am1`, `exhaust_core`, `create_sum`, `update_sum`).
- **`markusrabe/cadet` @ `40f9683261013780b5c6cddf9cb3112d0f71d187`, `lonsing/depqbf` @ `2ad3995a21b8ca2831be2534b1cb80df342b3bdf`, `marijnheule/qrat-trim` @ `5d6a1b60c1108755975b47b15d3676afeb3dbb65`:**
  - `cadet/README.md` L43–133; `src/cadet2.c` L213, L337–388; `src/skolem.c` L38–87, L194, L573; `src/certify_SAT.c` L40–180 (`cert_setup_AIG`, `cert_encode_unique_antecedents`, `cert_encode_CEGAR`); `src/certify_UNSAT.c` L20.
  - `depqbf/README` L19–165, L275–301; `qdpll_dep_man_qdag.c` L1497, L2047, L2213; `qdpll.c` L1181, L1529–1623, L6184.
  - `qrat-trim/qrat-trim.c` L237–305, L369–400, L522–770, L830–972 (`URcheck`, `EURcheck`, `printSkolem`, `BLUEVERSION`, existential-pivot guard L830, outer-clause filter L864/L891); `cheskol.c` L193–255.

### 2. Primary Peer-Reviewed Literature Verified

- Järvisalo, Heule, Biere (IJCAR 2012), *Inprocessing Rules*, `DOI: 10.1007/978-3-642-31365-3_28`.
- Haberlandt, Green, Heule (SAT 2023), *Effective Auxiliary Variables via Structured Reencoding* (`SBVA`), `DOI: 10.4230/LIPIcs.SAT.2023.11` (`arXiv:2307.01904`).
- Cruz-Filipe, Heule, Hunt, Kaufmann, Schneider-Kamp (CADE 2017), *Efficient Certified RAT Verification* (`LRAT`), `DOI: 10.1007/978-3-319-63046-5_14`.
- Heule, Kiesl, Biere (CADE 2017), *Short Proofs Without New Variables* (`PR`), `DOI: 10.1007/978-3-319-63046-5_9`.
- Baek, Carneiro, Heule (TACAS 2021 / LMCS 2022), *A Flexible Proof Format for SAT Solver-Elaborator Communication* (`FRAT`), `DOI: 10.1007/978-3-030-72016-2_4`, `DOI: 10.46298/lmcs-18(2:3)2022`.
- Tan, Heule, Myreen (TACAS 2021), *cake_lpr: Verified Propagation Redundancy Checking in CakeML*, `DOI: 10.1007/978-3-030-72013-1_12`.
- Pollitt, Fleury, Biere (SAT 2023), *Faster LRAT Checking Than Solving with CaDiCaL*, `DOI: 10.4230/LIPIcs.SAT.2023.21`.
- Böving, Bhat, Cicolini, Keizer, Frénot, Mohamed, Stefanesco, Khan, Clune, Barrett, Grosser (PACMPL / OOPSLA), *Interactive Bitvector Reasoning using Verified Bit-Blasting* (`bv_decide`), `DOI: 10.1145/3763167`.
- Bogaerts, Gocht, McCreesh, Nordström (AAAI 2022), *Certified Symmetry and Dominance Breaking for Combinatorial Optimisation* (`VeriPB`), `DOI: 10.1609/aaai.v36i4.20283`.
- Berg, Bogaerts, Nordström, Oertel, Vandesande (CADE 2023), *Certified Core-Guided MaxSAT Solving*, `DOI: 10.1007/978-3-031-38499-8_1`.
- Gocht, McCreesh, Myreen, Nordström, Oertel, Tan (AAAI 2024), *End-to-End Verification for Subgraph Solving* (`CakePB`), `DOI: 10.1609/aaai.v38i8.28642`.
- Rabe, Seshia (SAT 2016), *Incremental Determinization* (`CADET`), `DOI: 10.1007/978-3-319-40970-2_23`.
- Heule, Seidl, Biere (IJCAR 2014 / JAR 2017), *A Unified Proof System for QBF Preprocessing* / *Solution Validation and Extraction for QBF Preprocessing* (`QRAT`), `DOI: 10.1007/978-3-319-08587-6_7`, `DOI: 10.1007/s10817-016-9390-4`.
- Slivovsky, Szeider (TCS 2016), *Soundness of Q-resolution with dependency schemes*, `DOI: 10.1016/j.tcs.2015.10.020`.
- Peterson, Reif, Azhar (Comput. Math. Appl. 41(7):957–992, 2001), *Lower Bounds for Multiplayer Non-cooperative Games of Incomplete Information* (`DQBF` `NEXPTIME`-completeness).

### 3. Reproducible Execution Evidence (Python 3.13.15, 2026-11-19)

Executing the standalone probe script below (`python3 /tmp/probe_sat_qbf_certs.py`) produced the exact deterministic output:

```text
=== PROBE 1: Equisatisfiable BCE vs Entailment & CaDiCaL-Style Witness Reconstruction ===
|Models(F)| = 2, |Models(F_after_BCE)| = 3, extra_models_violating_F = 1
Reconstructed valid F-models: 3/3; example flip: {1: False, 2: False, 3: True} -> {1: True, 2: False, 3: True} (flips=1)

=== PROBE 2: DRAT Unhinted Scan vs Hint-Indexed LRAT/LPR (and PR without new variables) ===
  N_distractors=  50: LRAT ok=True lit_visits=  20 | Unhinted-DRAT ok=True lit_visits=   120 (ratio=6.0x)
  N_distractors= 200: LRAT ok=True lit_visits=  20 | Unhinted-DRAT ok=True lit_visits=   420 (ratio=21.0x)
  N_distractors=1000: LRAT ok=True lit_visits=  20 | Unhinted-DRAT ok=True lit_visits=  2020 (ratio=101.0x)
  PHP(3,2) symmetry-breaking clause C=(-1, -4): RUP/RAT=False (ERR_MISSING_PR_HINT_1), PR(w=[-1, 2, 3, -4])=True (PR, visits=22)
  Soundness rejections: inconsistent_witness=False (ERR_INCONSISTENT_WITNESS), non_unit_hint=False (ERR_NOT_UNIT)
  Unchecked core deletion in MaxSAT/PB: true min(x1+x2)=1, after del(1) + RAT(-1)=True + RAT(-2)=True -> fake min=0 (UNSOUND)

=== PROBE 3: 2QBF AIG Skolem Synthesis & QRAT Outer-Clause Soundness Boundary ===
  CADET-style determinization order=[3, 4], verified=True
  AIG definitions: e3=('OR', (('AND', (1, 2)),)), e4=('OR', (('AND', (3, -2)), ('AND', (-3, 2))))
  Truth table (u1,u2)->(e1,e2): [((0, 0), (0, 0), True), ((0, 1), (0, 1), True), ((1, 0), (0, 0), True), ((1, 1), (1, 0), True)]
  SAT-RAT unsoundness on QBF [exists x forall u. (x v u) & (x v -u)]:
    SAT-RAT accepts (-u) with hint {1:[1,2]}: True (RAT); QBF truth: True -> False (UNSOUND; QRATA rejects universal pivot)
```

---

## Revalidation

1. **Rerun the Self-Contained Proof-System & QBF Soundness Probe:** Save the script below to `/tmp/probe_sat_qbf_certs.py` and run `python3 /tmp/probe_sat_qbf_certs.py` to reproduce every quantitative output and counterexample in `## Evidence` (BCE witness reconstruction, LRAT vs. unhinted-scan visit scaling, $\text{PHP}_3^2$ PR-vs-RAT separation, MaxSAT unchecked-deletion unsoundness, 2QBF AIG Skolem synthesis, and propositional-RAT unsoundness on QBF):

```python
#!/usr/bin/env python3
from itertools import product

def eval_clause(c, a):
    return any((a[abs(l)] if l > 0 else not a[abs(l)]) for l in c)

def all_models(n, cs):
    return [{i+1: b[i] for i in range(n)} for b in product((False, True), repeat=n)
            if all(eval_clause(c, {i+1: b[i] for i in range(n)}) for c in cs)]

print("=== PROBE 1: Equisatisfiable BCE vs Entailment & CaDiCaL-Style Witness Reconstruction ===")
F_orig = [(1, 2), (-1, -2, 3), (-1, -2, -3), (2, 3), (-2, -3)]
F_after_bce = F_orig[1:]
m_orig, m_bce = all_models(3, F_orig), all_models(3, F_after_bce)
extra = [m for m in m_bce if m not in m_orig]
print(f"|Models(F)| = {len(m_orig)}, |Models(F_after_BCE)| = {len(m_bce)}, extra_models_violating_F = {len(extra)}")
ok_cnt, ex_fix = 0, None
for m in m_bce:
    a, flips = dict(m), 0
    for piv, cl in reversed([(1, (1, 2))]):
        if not eval_clause(cl, a):
            a[abs(piv)] = not a[abs(piv)]; flips += 1
    assert all(eval_clause(c, a) for c in F_orig)
    ok_cnt += 1
    if flips and ex_fix is None: ex_fix = (m, a, flips)
print(f"Reconstructed valid F-models: {ok_cnt}/{len(m_bce)}; example flip: {ex_fix[0]} -> {ex_fix[1]} (flips={ex_fix[2]})")

print("\n=== PROBE 2: DRAT Unhinted Scan vs Hint-Indexed LRAT/LPR (and PR without new variables) ===")
def is_at(fml, hints, cl):
    f = set(cl); v = 0
    for cid in hints:
        if cid not in fml: return ("ERR_MISSING_ID", f, v)
        rem = []
        for l in fml[cid]:
            v += 1
            if l not in f: rem.append(l)
        if not rem: return ("AT", f, v)
        if len(rem) == 1: f.add(-rem[0])
        else: return ("ERR_NOT_UNIT", f, v)
    return ("INCOMPLETE", f, v)

def check_pr(fml, cl, w, rup_h, pr_h):
    st, ext, v = is_at(fml, rup_h, cl)
    if st == "AT": return (True, "RUP/AT", v)
    if st != "INCOMPLETE" or not cl: return (False, st, v)
    w = w if w is not None else [cl[0]]
    ws, fw = set(w), {-l for l in w}
    if ws & fw: return (False, "ERR_INCONSISTENT_WITNESS", v)
    ov_t = ws | {-l for l in ext if l not in ws and -l not in ws}
    ov_f = {-l for l in ov_t}
    for cid, ci in fml.items():
        v += len(ci)
        if any(l in fw for l in ci):
            if cid not in pr_h:
                if any(l in ws for l in ci): continue
                return (False, f"ERR_MISSING_PR_HINT_{cid}", v)
            sh = pr_h[cid]
            if not sh:
                if any(l in ov_t for l in ci): continue
                return (False, f"ERR_NOT_SAT_BY_OVERLAP_{cid}", v)
            st2, _, v2 = is_at(fml, sh, list(ext | {l for l in ci if l not in ov_f}))
            v += v2
            if st2 != "AT": return (False, f"ERR_PR_SUBHINT_{cid}_{st2}", v)
    return (True, "PR" if w != [cl[0]] else "RAT", v)

def drat_unhinted(active, cl):
    f, v, ch = set(cl), 0, True
    while ch:
        ch = False
        for ci in active:
            rem = []
            for l in ci:
                v += 1
                if l not in f:
                    rem.append(l)
                    if len(rem) > 1: break
            if not rem: return True, v
            if len(rem) == 1 and (-rem[0]) not in f: f.add(-rem[0]); ch = True
    return False, v

for N_dist in (50, 200, 1000):
    fml, cid = {}, 1
    for j in range(N_dist):
        fml[cid] = (100+j, 101+j, -(102+j)); cid += 1
    cs = cid
    fml[cid] = (-10,); cid += 1
    for k in range(9, 0, -1):
        fml[cid] = (-k, k+1); cid += 1
    fml[cid] = (1,); cid += 1
    ok_l, _, vl = check_pr(fml, (), None, list(range(cid-1, cs-1, -1)), {})
    ok_d, vd = drat_unhinted(list(fml.values()), ())
    print(f"  N_distractors={N_dist:4d}: LRAT ok={ok_l} lit_visits={vl:4d} | Unhinted-DRAT ok={ok_d} lit_visits={vd:6d} (ratio={vd/vl:.1f}x)")

php32 = {1:(1,2), 2:(3,4), 3:(5,6), 4:(-1,-3), 5:(-1,-5), 6:(-3,-5), 7:(-2,-4), 8:(-2,-6), 9:(-4,-6)}
ok_r, m_r, _ = check_pr(php32, (-1,-4), None, [], {})
ok_p, m_p, vp = check_pr(php32, (-1,-4), [-1,2,3,-4], [], {6:[5], 8:[9]})
ok_bw, m_bw, _ = check_pr(php32, (-1,-4), [1,-1], [], {})
ok_bh, m_bh, _ = check_pr(php32, (10,), None, [1], {})
print(f"  PHP(3,2) symmetry-breaking clause C=(-1, -4): RUP/RAT={ok_r} ({m_r}), PR(w=[-1, 2, 3, -4])={ok_p} ({m_p}, visits={vp})")
print(f"  Soundness rejections: inconsistent_witness={ok_bw} ({m_bw}), non_unit_hint={ok_bh} ({m_bh})")
orig_opt = min(int(m[1])+int(m[2]) for m in all_models(2, [(1,2)]))
r1, _, _ = check_pr({}, (-1,), None, [], {})
r2, _, _ = check_pr({2:(-1,)}, (-2,), None, [], {})
fake_opt = min(int(m[1])+int(m[2]) for m in all_models(2, [(-1,), (-2,)]))
print(f"  Unchecked core deletion in MaxSAT/PB: true min(x1+x2)={orig_opt}, after del(1) + RAT(-1)={r1} + RAT(-2)={r2} -> fake min={fake_opt} (UNSOUND)")

print("\n=== PROBE 3: 2QBF AIG Skolem Synthesis & QRAT Outer-Clause Soundness Boundary ===")
qbf = [(-1,-2,3), (1,-3), (2,-3), (-3,-2,-4), (-3,2,4), (3,-2,4), (3,2,-4)]
def eval_aig(n, env):
    t = n[0]
    if t == "IN": return env[n[1]]
    if t == "AND": return all((env[abs(l)] if l > 0 else not env[abs(l)]) for l in n[1])
    return any(eval_aig(ch, env) for ch in n[1])
det, aig, order, rem = {1, 2}, {1:("IN",1), 2:("IN",2)}, [], [3, 4]
while rem:
    for e in list(rem):
        pa, na = [], []
        for c in qbf:
            if e in c or -e in c:
                oth = [l for l in c if abs(l) != e]
                if all(abs(l) in det for l in oth):
                    (pa if e in c else na).append(tuple(-l for l in oth))
        if not pa and not na: continue
        conf = False
        for u1, u2 in product((False, True), repeat=2):
            env = {1: u1, 2: u2}
            for p in order: env[p] = eval_aig(aig[p], env)
            if any(all((env[abs(l)] if l>0 else not env[abs(l)]) for l in a) for a in pa) and \
               any(all((env[abs(l)] if l>0 else not env[abs(l)]) for l in a) for a in na):
                conf = True; break
        if not conf:
            aig[e] = ("OR", tuple(("AND", a) for a in pa))
            det.add(e); order.append(e); rem.remove(e)
tbl, vok = [], True
for u1, u2 in product((False, True), repeat=2):
    env = {1: u1, 2: u2}
    for e in order: env[e] = eval_aig(aig[e], env)
    ok = all(eval_clause(c, env) for c in qbf); vok = vok and ok
    tbl.append(((int(u1), int(u2)), (int(env[3]), int(env[4])), ok))
print(f"  CADET-style determinization order={order}, verified={vok}")
print(f"  AIG definitions: e3={aig[3]}, e4={aig[4]}")
print(f"  Truth table (u1,u2)->(e1,e2): {tbl}")
ok_sr, m_sr, _ = check_pr({1:(1,2), 2:(1,-2)}, (-2,), None, [], {1:[1,2]})
eval_ea = lambda cs: any(all(all(eval_clause(c, {1:x, 2:u}) for c in cs) for u in (False, True)) for x in (False, True))
print(f"  SAT-RAT unsoundness on QBF [exists x forall u. (x v u) & (x v -u)]:")
print(f"    SAT-RAT accepts (-u) with hint {{1:[1,2]}}: {ok_sr} ({m_sr}); QBF truth: {eval_ea([(1,2),(1,-2)])} -> {eval_ea([(1,2),(1,-2),(-2,)])} (UNSOUND; QRATA rejects universal pivot)")
```

2. **Check Upstream Drift in Narrow Implementation Regions:**
   - **CaDiCaL:** Diff `arminbiere/cadical` `src/options.hpp` (`block`, `factor`, `veripb`), `src/factor.cpp` (`add_derived_rat_clause`), `src/lrattracer.cpp`, and `src/veripbtracer.cpp` to verify whether `factor` becomes default-enabled or VeriPB format advances beyond `3.0`.
   - **Lean 4 `bv_decide`:** Diff `leanprover/lean4` `src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean` (`nativeEqTrue`), `src/Std/Tactic/BVDecide/LRAT/Actions.lean` (whether `addPr` is added), and `src/Lean/Meta/Tactic/BVDecide/External.lean` (CaDiCaL flags) to check whether `bv_decide` changes its compiler-in-TCB reflection boundary or adds PR support.
   - **`cake_lpr`:** Check `tanyongkiam/cake_lpr/README.md` and `CakeML/cakeml/examples/lpr_checker/lprScript.sml` for the announced successor checker replacing `cake_lpr`.
   - **DepQBF / CADET / qrat-trim:** Diff `lonsing/depqbf/README` for changes to `--trace` / `--dep-man=simple` restrictions and `marijnheule/qrat-trim/qrat-trim.c` for outer-clause `QRATA`/`QRATU` rules.
