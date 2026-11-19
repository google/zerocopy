# Zero-knowledge proof checking, verifiable ML inference, and conformal assurance: what each certificate certifies

## Summary

Three kinds of certificate let a party rely on a computation it cannot inspect. Each proves a
precise statement that is narrower than its usual one-line description, and each moves trust to
a place that must be audited separately.

1. **Zero-knowledge proof checking** (zkPi for Lean, ZKUNSAT for propositional resolution, ZKSMT
   for SMT refutations) proves: *the prover knows a derivation that an arithmetised checker
   accepts for a public claim*. In all three systems the **dimensions of the derivation are
   public**. In zkPi at the pinned revision the public inputs are the ten size constants, the
   term graph of the *normalised* theorem statement, the types of **all axioms** made available
   to the proof, and the inductive declarations (including recursor bodies) the proof uses; the
   rule graph, the remaining terms and the typing contexts are private. The circuit types *uses*
   of inductive declarations but contains no check that the public declarations are admissible,
   so axiom hygiene and declaration validity are verifier-side duties performed in the clear. The
   checker is a bespoke rule system (rule tags 1–38) compiled to R1CS — not the Lean kernel —
   and it rejects or cannot express `Quot.sound`, eta expansion, and some inductive families.
   The repository's own result tables record 585 of 1000 sampled Lean standard-library theorems
   and 143 of 1000 sampled mathlib theorems proved, with medians of about 2.8 × 10^5 and 3.0 × 10^5
   R1CS constraints and a maximum proving time of 270 s among successes.
2. **Verifiable ML inference (zkML)** proves the execution of a **fixed-point circuit**, not of
   the floating-point model that was trained and evaluated. EZKL quantises with
   `round(2^scale · x)` (library default scale 7) and its README states that "outputs in python
   and ezkl may differ slightly"; its security notes describe quantisation-activated backdoors.
   A probe in this report shows 80 of 20 000 inputs changing predicted class at scale 7 for a
   small ReLU network, with flips up to a float margin of 0.012.
3. **Conformal prediction** gives a distribution-free, finite-sample guarantee
   `P(Y ∈ C(X)) ≥ 1 − α` that is **marginal** over calibration and test data and requires
   **exchangeability**. It is not conditional on the input, and conditional on a given
   calibration set the coverage is a random quantity (Beta-distributed). When the system's own
   actions change the data distribution, static conformal sets lose coverage (31.6 % miscoverage
   against a 10 % target in the probe); adaptive conformal inference restores only the *long-run
   frequency* (bound `(max{α₁, 1−α₁} + γ)/(Tγ)`), not a per-step probability.

Composed for runtime assurance, the honest end-to-end statement is: *with probability at least
`1 − α` over an exchangeable calibration-plus-test draw, the set computed by the quantised model
whose execution was proved contains the truth; given that event, the logically verified
controller is safe.* The zero-knowledge layers add soundness error and hide inputs; they do not
change the probability space, repair a shifted distribution, or connect the quantised model to
the float model.

## Applicability

The report combines the subjects in `REPORT.json` into one analysis of certificate semantics;
it does not benchmark them against each other.

- **zkPi**: source of `emlaufer/zkpi@c65fc44373306106b741069f7d3cbc8224b21a74` (no README at
  that revision), including its circuit `zok/eval.zok`, exporter `src/zk/mod.rs`, driver
  `driver.py` and the result tables under `scripts/`. Nothing was built or run. The associated
  paper (Laufer, Ozdemir, Boneh, ACM CCS 2024, DOI 10.1145/3658644.3670322, ePrint 2024/267) was
  available only as abstract and metadata; statements about protocol design are therefore drawn
  from the code, and may not match the paper's final presentation.
- **ZKUNSAT**: source of `PP-FM/ZKUNSAT@9970d3d3f838425e04d0266b0ce84a55202d9c5b` (no README);
  the paper (Luo, Antonopoulos, Harris, Piskac, Tromer, Wang, ePrint 2022/206) only as abstract.
- **ZKSMT**: full text of the USENIX Security 2024 paper (Luick, Kolesar, Antonopoulos, Harris,
  Parker, Piskac, Tromer, Wang, Luo); its implementation was not examined.
- **EZKL**: source and bundled documentation of
  `zkonduit/ezkl@e196b111c1bafaa61b92ae431cd3c3fe9371da05`; not built or run.
- **zkML at scale**: full text of Kang, Hashimoto, Stoica, Sun (arXiv 2210.08674v1).
- **Conformal prediction**: full texts of Tibshirani, Barber, Candès, Ramdas (arXiv
  1904.06019v3), Gibbs and Candès (arXiv 2106.00170v3), Angelopoulos, Bates, Fisch, Lei, Schuster
  (arXiv 2208.02814v4) and Vovk (arXiv 1209.2673v2). Two frequently cited works — Angelopoulos
  and Bates, "A Gentle Introduction to Conformal Prediction…" (arXiv 2107.07511) and Lindemann,
  Cleaveland, Shim, Pappas, "Safe Planning in Dynamic Environments using Conformal Prediction"
  (arXiv 2210.10254) — were available only as abstracts.
- **Executable evidence**: one standard-library Python program reproduced in Findings §9 (CPython
  3.13.15). Its three parts are *models* of the mechanisms (a prime-field analogue of the
  resolution check, a generic fixed-point network, synthetic conformal experiments); none runs
  any of the subject systems.

Findings marked *derived* hold for any system with the stated interface, not only the examined
revisions; findings marked *source* are claimed only for the pinned revisions.

## Findings

### 1. The common shape of a zero-knowledge proof-checking certificate

Basis: derived from §2–§4.

Every system instantiates the relation *R(public x; private w) = "checker accepts derivation w
for claim x"* and proves knowledge of `w`. What differs is the object logic, how the checker is
arithmetised, and what ends up in `x`.

| | zkPi | ZKUNSAT | ZKSMT |
|---|---|---|---|
| Object logic | dependent type theory of Lean: evaluation and typing judgments, inductive types with recursors, proof irrelevance, structure projections | propositional resolution with weakening, chain-structured | SMT refutations: Boolean logic, equality with uninterpreted functions, linear integer arithmetic |
| Checker | one circuit over a table of `PROOF_SIZE` rule nodes; every rule's check is evaluated at every node and selected by the node's tag | loop over derived clauses; each fetches its support clauses from a ZK random-access memory and checks polynomial identities | virtual machine: read-only expression table and step table; one "checking instruction" per proof rule; steps grouped by rule |
| Argument system | zkSNARK: Z# circuit → R1CS (vendored CirC) → `mirage` backend with two commitment epochs and verifier randomness | interactive, EMP-toolkit, VOLE-based MACs over GF(2^128) | interactive VOLE-based ZK via EMP-toolkit over GF(2^128) |
| Public (leaked) | ten size constants; normalised statement; axiom types; inductive declarations | number of clauses, number of derived clauses, maximum clause width, length of every resolution chain | five size parameters; "the number of occurrences (but not the order) of each proof rule" |
| Private | rule graph, non-prefix terms, lifts, contexts | every clause (input and derived), supports, pivots | formula and proof ("without revealing the underlying formulas or their proofs") |
| Derivation source | Lean export file → Rust exporter that normalises statement and proof term and emits a typing derivation | PicoSAT 965 TraceCheck proof → sorted → unfolded chains | SMTInterpol proof → compiler; 1–7× more steps |
| Scale evidence | 585/1000 and 143/1000 sampled theorems; ≤ 2.96 × 10^6 constraints; ≤ 270 s proving | not examined | 200,000 proof steps in about 3 hours |

Three structural facts follow.

- **Size is always public.** A fixed circuit or protocol transcript has a size determined by the
  derivation's dimensions. Hiding them requires padding to a public upper bound, at
  proportional cost.
- **The claim must be bound to something the verifier understands.** A hidden derivation of a
  hidden claim proves nothing (§3 shows a code path where this is the case). The binding is
  either a public claim or a public commitment to the claim together with a proof about the
  committed value.
- **The trusted base moves, it does not shrink.** The verifier no longer runs the proof checker;
  it trusts (i) that the arithmetised checker is sound for the logic, (ii) the circuit compiler,
  (iii) knowledge soundness of the argument system and any setup, (iv) the translation from the
  human-readable claim to public inputs, and (v) whatever the public inputs delegate to it
  (axioms, declarations).

### 2. zkPi at the pinned revision

Basis: source (`emlaufer/zkpi@c65fc443…`), except where marked.

**Pipeline** (`driver.py`):

1. Optional export from Lean source. The driver runs `lean --version` and exits unless the
   output contains `version 3.` ("The tool only works for Lean3"); alternatively an existing
   export file is passed with `-e`. The repository also contains a `lean4export` submodule and
   `Lean4Examples/lean-toolchain` = `leanprover/lean4:v4.8.0-rc1`; the evaluation harness passes
   `-e Lean4Examples/<library>.out`. Circuit constants are annotated "Lean4 extensions"
   (`EXPR_PROJ`, projection rules).
2. `cargo run --release <export> count <theorem>` prints ten sizes.
3. The driver writes them into `zok/meta.zok` as the compile-time constants `PROOF_SIZE`,
   `NUM_TERMS`, `CONTEXT_SIZE`, `NUM_LIFTS`, `NUM_INDS`, `NUM_PUB_TERMS`, `NUM_RULES`, `NUM_NNRS`,
   `NUM_NRS`, `NUM_AXIOMS`.
4. `cargo run --release <export> export <theorem>` writes the prover input file.
5. `circ --language Zsharp eval.zok r1cs --proof-system mirage --action oneshot --inputs …`.

The circuit is therefore **specialised per theorem** by ten public sizes; with a preprocessing
argument system that implies per-shape key generation (the evaluation harness records a
per-theorem `Setup` time alongside `Prove` and `Verify`).

**Statement proved** (`zok/eval.zok`, signature of `main`):

```text
def main(
    private ExpRule[PROOF_SIZE] proof,
    private ExpTerm[NUM_TERMS] terms,
    private ExpLift[NUM_LIFTS] lifts,
    private field proving_rule,
    private HashLists<CONTEXT_SIZE> contexts,
    random field alpha,
    random field beta,
    ExpInd[NUM_INDS] inductives,
    ExpTerm[NUM_PUB_TERMS] public_terms,
    field expected_type,
    HashLists<NUM_RULES> rules,
    HashLists<NUM_NNRS> rule_nnrs,
    HashLists<NUM_NRS> rule_nrs,
    field[NUM_AXIOMS] axioms
) -> bool
```

Top-level assertions: the first `NUM_PUB_TERMS` private terms equal `public_terms` field by
field; `proof[proving_rule].result_term_idx == expected_type`; `is_type_rule(proof[proving_rule]
.rule)`; that rule's context is the empty context; `check_terms(terms)`. Then, for every node of
`proof`, each rule checker is applied under `if node.rule == RULE_X then check_x(…) else true`.

In words: *there is a private table of terms extending the public prefix, and a private graph
of evaluation ("⇒") and typing ("::") judgments closed under the circuit's rules, containing a
typing judgment in the empty context whose type is the public term `expected_type`.*

**What is public, concretely** (`src/zk/mod.rs`):

- `Exporter::with_axioms` first exports the type of every supplied axiom, then the expected
  type, and copies *all terms exported so far* into `public_terms`. The public prefix is thus
  the term graph of **every axiom's type** plus the **statement**; the `axioms` array holds
  indices into it, and `check_type_ax` types a use of axiom `i` by `axioms[i]`.
- The statement is the exporter's **normal form**: `simplified_ty = eval.eval(theorem.ty)`; the
  proof term is likewise evaluated (`simplified_val`) before a typing derivation is emitted. A
  verifier must reproduce this normalisation from the surface statement to know what was proved.
- `inductives` is public and is used as given: `check_type_ind` compares against
  `inductives[i].ty`, `check_type_ind_ctor` looks the constructor type up in the public rule
  list, `check_type_ind_rec` reads `num_params` and `rec_body`. No function in `eval.zok` checks
  that a declaration is admissible (the string "positiv" does not occur in the file).
- Constants whose name starts with `Quot` are exported as **axioms**, except `Quot.sound`, which
  is rejected: `Err("We don't support Quot.sound: …")` (`src/lean.rs`). Quotient computation
  rules are therefore unavailable and the quotient primitives appear in the public axiom list.

**Rule system** (`zok/constants.zok`): expression kinds `VAR, SORT, APP, LAM, PI, AX, IND,
IND_CTOR, IND_REC, PROJ`; rule tags 1–38 (16 commented out): evaluation rules (`EVAL_ID`,
`EVAL_VAR`, `EVAL_APP`, `EVAL_APP_LAM`(+`_SUB`), `EVAL_APP_PI`, `EVAL_LAM`, `EVAL_PI`, `EVAL_AX`,
`EVAL_IND`(+2 sub-rules), `EVAL_TRANSITIVE`, `EVAL_PROJ`, `EVAL_PROJ_SIMPL`), typing rules
(`TYPE_VAR`, `TYPE_SORT`, `TYPE_APP`(+`_SUB`), `TYPE_LAM`, `TYPE_PI`(+`_SUB`), `TYPE_AX`,
`TYPE_IND`, `TYPE_IND_CTOR`, `TYPE_IND_REC`, `TYPE_PROJ`), conversion (`EVAL_TYPE`: from
`a :: T` and `T ⇒ T'` conclude `a :: T'`), `PROOF_IRREL`(+sub-rule), and eliminator plumbing
(`APPLY_ELIM`, `GET_ARG`, `APPLY_ELIM_EVAL`, `IND_PREFIX`, `WALK_PROJ`, `CONSTR_PROJ`).
`check_type_sort` requires `input_term.name + 1 == result_term.name`, i.e. sorts carry concrete
numeric levels; the exporter names inductives with their universe instantiation
(`ind_name + ".{" + universe_inst_string + "}"`).

**Contexts and lookups** (`zok/hashlist.zok`): typing contexts and the inductive rule lists are
linked lists hashed as multisets, node hash `= (alpha − value − beta·key) · hash(prev)`.
Membership is a product identity `hash(list) == (alpha − value − beta·key) · hash(quotient)`
with a prover-supplied quotient list. `alpha`, `beta` are declared `random`; the vendored CirC
backend asserts "May only have 2 epochs for mirage!". Soundness of every context lookup thus
rests on the challenges being drawn after the witness is committed.

**Unsupported constructs observed**: `panic!("eta unsupported")` (two sites in
`src/zk/mod.rs`); "Recursing on inductive families with recursive params are unsupported" and
"Projection only supported on singletons" (`src/term.rs`); `Quot.sound` as above.

**Cost model** (`scripts/param_sweep.csv`, one parameter varied, others 1):

| Parameter | 10 | 100 | 1000 | ≈ constraints per unit |
|---|---|---|---|---|
| `PROOF_SIZE` (rule nodes) | 16,267 | 160,807 | 1,606,207 | 1,606 |
| `NUM_TERMS` | 2,623 | 10,723 | 91,723 | 90 |
| `CONTEXT_SIZE` | 2,937 | 16,612 | 197,667 | 201 |
| `NUM_LIFTS` | 4,189 | 27,949 | 265,549 | 264 |
| `NUM_AXIOMS` | 1,903 | 2,803 | 11,803 | 10 |

The dominant term is ≈ 1.6 × 10^3 constraints per derivation node, a direct consequence of
evaluating every rule checker at every node.

**Recorded evaluation** (`scripts/stdlib_times_new_complete.csv`,
`scripts/mathlib_times_new_complete.csv`; 1000 rows each; times read as nanoseconds; return-code
legend from `scripts/commander.py`, which runs each theorem with an 1800 s limit):

| | stdlib sample | mathlib sample |
|---|---|---|
| return code 0 (proved and verified) | 585 | 143 |
| −1000 (harness time limit) | 169 | 81 |
| −1235 (`Quot`) | 22 | 205 |
| −1236 (eta) | 16 | 4 |
| −1234 (inductive families) | 11 | 3 |
| −1237 (typing error in exporter) | 6 | 11 |
| 247 (not decoded by the legend) | 185 | 545 |
| other (101, 255, 1) | 6 | 8 |
| R1CS constraints, successes: median / 90th pct / max | 275,831 / 1,841,753 / 2,875,369 | 297,160 / 1,737,910 / 2,961,381 |
| proving time, successes: median / 90th pct / max | 22.4 s / 157.5 s / 270.3 s | 22.0 s / 147.4 s / 246.2 s |
| verification time, successes: median / max | 0.37 s / 9.73 s | 0.37 s / 6.32 s |

The paper's abstract reports 57.9 % and 14.1 % "within 4.5 minutes per theorem" (Basis:
documentation); the tables above give 58.5 % and 14.3 % with a 270 s maximum. The two sources
agree to within a few theorems; which table produced the published figures was not determined.

### 3. ZKUNSAT at the pinned revision

Basis: source (`PP-FM/ZKUNSAT@9970d3d3…`), plus the ePrint abstract where marked.

- **Encoding.** A literal is a 61-bit value (`VAL_SZ 61`); negation flips one fixed bit
  (`get_negate(e) = constant ^ e`, `constant = 1 << (VAL_SZ − 2)`). A clause is the monic
  polynomial over GF(2^128) whose roots are its literals (`get_GF2EX_with_roots`), padded to a
  public degree `DEGREE`. Coefficients are committed by the prover with VOLE-based MACs
  (`polynomial::polynomial`: the prover sends `d ^ coefficient`, the verifier adjusts the MAC
  with its global key).
- **Resolution step** (`check_xres`). For support clauses `c0`, `c1`, resolvent `res` and pivot
  `p`, the prover supplies witness polynomials `w0`, `w1` and the protocol checks
  `c0·w0 = res·(X − p)` and `c1·w1 = res·(X − ¬p)` (as inner-product equalities), plus a check
  (`ConverseCheck`, by evaluation at a transcript-derived point) that the second pivot
  polynomial is the first with the negation bit flipped. Meaning: every literal of `c0` other than
  `p`, and every literal of `c1` other than `¬p`, occurs in `res`. This is resolution **with
  weakening**: any superset of the resolvent is accepted, and so is a step where the pivot does
  not occur (then `res ⊇ c0`). Both are sound; the probe in §9 confirms 0 unsound among 3600
  accepted steps in an exhaustive two-variable model.
- **Chains and memory** (`check_chain`, `clauseRAM`). Each derived clause is obtained by a chain
  of resolutions over support clauses fetched by *private* index from a ZK RAM; the only thing
  revealed about an index is the bit `index ≥ current position` ("cheat!" if true), which
  enforces that only earlier clauses are used. The chain's final clause must equal the clause
  stored at the current position; the last clause must equal the empty clause.
- **Leakage.** The prover sends in the clear `nres`, `ncls`, `DEGREE` and, per derived clause,
  `chain_length` (`io->send_data(&chain_length, 8)`). The abstract's "Only the proof's
  dimensions are revealed" corresponds to these values (Basis: documentation + source).
- **No binding to a public formula in this code path.** `main.cpp` reads clauses only on the
  prover side (`readproof`), feeds *all* of them — input clauses and derived clauses alike —
  through the committing constructor, and the verifier allocates empty vectors of the announced
  length. Nothing compares the first `ncls − nres` clauses with a formula known to the verifier.
  As run, the program therefore establishes "some clause set with these dimensions has a
  resolution refutation", which is vacuous on its own (`{x}`, `{¬x}` suffices). A deployment
  needs an additional step that fixes the input clauses, by opening them or by proving a relation
  between the committed clauses and a public object.
- **Derivation source** (`prover_backend/preprocess.sh`): `picosat-965/ex1` emits
  `proof.TRACECHECK`, post-processed by `Sort.py` and `unfold_proof.py`.

### 4. ZKSMT

Basis: normative for the design (USENIX Security 2024 paper).

- **Scope stated by the authors.** A secrecy-preserving program verifier needs a witness
  comprising "(a) a high-level program that satisfies the specification, (b) a proof that it does
  so, and (c) a proof that the secret high-level program is observationally equivalent to the
  public binary executable"; "This paper focuses on proving component (b)".
- **Machine.** `ZKSMT[T](π, χ, µ, α, ρ)`: `π` maximum proof steps, `χ` maximum expressions, `µ`
  maximum premises of a rule, `α` maximum argument-list size, `ρ` number of distinct rules. An
  expression table and a step table are read-only memories; the main checker fetches each step's
  rule and premises and dispatches to the rule's checking instruction; at the end it checks that
  the list of validated step identifiers is a permutation of `[0, …, π−1]`. Expressions are
  type-checked by public type rules and checked for cycles.
- **Theorems.** Soundness: a machine validates `φ` only if `φ` is *boundedly verifiable* (has a
  derivation within the size parameters); completeness is the converse.
- **Leakage and its reason.** "Our system does reveal some size parameters of the proof (e.g.,
  the number of proof steps)" and "the number of occurrences (but not the order) of each proof
  rule". The second is the price of *group checking*: steps using the same rule are verified
  consecutively by that rule's instruction alone, avoiding a multiplexer over all rules — the
  design choice zkPi does not make (§2 cost model).
- **Instantiation.** Boolean logic, EUF and LIA; EMP-toolkit; arithmetic field GF(2^128);
  32-bit step indices. Benchmarks: verification conditions from Boogie's test suite and a
  Wisconsin Safety Analyzer instance "with 200,000 proof steps in about 3 hours"; proofs from
  SMTInterpol are converted by a compiler, increasing step counts "by a factor from 1 to 7"
  because some rules, "particularly the LIA rules, must be broken down into simpler rules".

### 5. Verifier obligations that zero knowledge does not remove

Basis: derived from §2–§4.

| Obligation | Why it remains | Where it shows in the examined systems |
|---|---|---|
| Inspect the axiom set | a proof from an inconsistent or unintended axiom proves anything | zkPi publishes every axiom type; quotient primitives are among them |
| Validate declarations | an inadmissible inductive type or a wrong recursor body makes the logic inconsistent | zkPi takes `inductives` (types, constructor lists, `rec_body`) as public input without in-circuit admissibility checks |
| Recompute the public claim | the circuit sees a normalised, numerically indexed term graph | zkPi exports `eval.eval(theorem.ty)`; ZKSMT proves validity of a formula whose link to a program is component (c), out of scope |
| Bind hidden inputs | a hidden claim with a hidden proof is vacuous | ZKUNSAT code path commits input clauses without tying them to a public formula |
| Audit the arithmetised checker | it replaces the reference checker | zkPi: 1,366 lines of Z# rules (`zok/eval.zok`) plus a 5,875-line exporter (`src/zk/mod.rs`) that must agree with them; neither is the Lean kernel |
| Account for leakage | sizes and rule histograms are public | all three |
| Trust the argument system | soundness is computational or statistical, possibly with setup | zkPi: verifier randomness after commitment (two epochs); ZKUNSAT/ZKSMT: interactive, designated verifier |

A private-source deployment ("ship a binary, a public specification and a zero-knowledge
certificate") needs all three components (a)–(c) of §4. The examined systems address the
derivation-checking component only; none of them relates a hidden source program to a public
binary.

### 6. Verifiable ML inference: the proved object is a fixed-point circuit

Basis: source + documentation (`zkonduit/ezkl@e196b111…`); normative for Kang et al.

- **Quantisation** (`src/graph/utilities.rs`): `quantize_float(elem, shift, scale)` returns
  `(2^scale · elem + shift).round()` as `IntegerRep` (`i128`), failing with
  `SigBitTruncationError` beyond the representable range; `dequantize` divides by `2^scale`.
  Field elements above `i128::MAX` decode as negatives using the low 128 bits
  (`felt_to_integer_rep`, `src/fieldutils.rs`).
- **Library defaults** (`impl Default for RunArgs`, `src/lib.rs`): `input_scale: 7`,
  `param_scale: 7`, `lookup_range: (-32768, 32768)`, `logrows: 17`, `decomp_base: 16384`,
  `decomp_legs: 2`, `input_visibility: Public`, `output_visibility: Public`,
  `param_visibility: Fixed`, `check_mode: CheckMode::UNSAFE`. (The command-line constant
  `DEFAULT_CHECKMODE` is `"safe"`; in `src/pfsys/mod.rs` safe mode makes the prover verify its
  own proof as a "sanity check".)
- **Calibration** (`src/commands.rs`, `src/execute.rs`): `CalibrationTarget` is `Resources` or
  `Accuracy` ("Optimizes for numerical accuracy given the fixed point representation"); an
  `AccuracyResults` tear-sheet reports mean/median/max error between original and calibrated
  predictions. Accuracy is thus *measured on calibration data*, not proved.
- **Stated semantics** (README): provable statements include "I ran this publicly available
  neural network on some private data and it produced this output"; and "Because operations are
  quantized when they are converted from an onnx file to a zk-circuit, outputs in python and
  ezkl may differ slightly."
- **Quantisation-activated backdoors** (`docs/advanced_security/quantization_backdoors.md`): a
  backdoor can be "active in the resulting model and circuit but not in the full-precision model
  supplied to EZKL"; mitigation: evaluate the quantised model (`ezkl gen-witness`) rather than
  the original. `public_commitments.md` warns that commitments to low-entropy data can be
  brute-forced.
- **Kang et al.**: "Neural network inference is typically done in floating-point arithmetic,
  which is extremely expensive to emulate in the prime field… we focus on DNNs quantized in int8
  and uint8"; addition and multiplication are native, "but the division cannot", hence custom
  division gates and lookup arguments for non-linearities; the reported ImageNet result is for a
  quantised MobileNet v2 with 79 % top-5 accuracy.

Derived consequences:

- The certificate's subject is the function `f_q` computed by the fixed-point circuit. Any
  property established for the float model `f` (test accuracy, robustness certificate,
  calibration) transfers only through a bound on `|f − f_q|` *on the inputs of interest*, or by
  re-establishing the property for `f_q` directly. Class decisions are discontinuous, so a small
  logit error gives no bound on disagreement near decision boundaries (§9B).
- Scale trades accuracy against range: products at scale `s` live at `2s`; larger scales push
  intermediates out of lookup/range tables (completeness failure) or, absent range constraints,
  past the field modulus (soundness failure of the integer reading; §9B last line).
- Hiding inputs does not establish that the inputs came from the claimed sensor or that the
  committed model is the trained one; those are provenance facts outside the proved relation.

### 7. Conformal prediction: exact statements

Basis: normative (statements as given in the cited papers).

| Guarantee | Statement | Assumption | Source |
|---|---|---|---|
| Marginal coverage | `P(Y_{n+1} ∈ Ĉ_n(X_{n+1})) ≥ 1 − α`; if scores are almost surely distinct, also `≤ 1 − α + 1/(n+1)` | `(X_i, Y_i)`, `i = 1..n+1`, exchangeable; any score function | Tibshirani et al., Theorem 1 (attributed there to Vovk et al. 2005 and Lei et al. 2018) |
| Training-conditional (PAC) | an inductive conformal predictor run at level `ε` is `(E, δ)`-valid — with probability ≥ `1 − δ` over the calibration set its error probability is ≤ `E` — whenever `E ≥ ε + sqrt(−ln δ / (2n))`; exactly, iff `δ ≥ bin_{n,E}(⌊ε(n+1) − 1⌋)` for continuous scores | i.i.d. data, calibration size `n` | Vovk, Propositions 2a, 2b |
| Covariate shift | weighted quantile with weights `p_i^w(x) = w(X_i) / (Σ_j w(X_j) + w(x))`, `p_{n+1}^w(x) = w(x) / (Σ_j w(X_j) + w(x))` gives coverage ≥ `1 − α` | test covariates from `P̃_X ≪ P_X`, same conditional `Y∣X`, likelihood ratio `w = dP̃_X/dP_X` **known** (up to normalisation) | Tibshirani et al., Corollary 1, Remark 3 |
| Online, arbitrary shift | with update `α_{t+1} = α_t + γ(α − err_t)`: `∣(1/T) Σ err_t − α∣ ≤ (max{α₁, 1 − α₁} + γ)/(Tγ)` with probability one | none on the data ("puts no constraints on the data generating distribution") | Gibbs and Candès, Proposition 4.1 |
| Risk control | with `λ̂ = inf{λ : (n/(n+1)) R̂_n(λ) + B/(n+1) ≤ α}`: `E[L_{n+1}(λ̂)] ≤ α` | exchangeable losses, each non-increasing and right-continuous in `λ`, bounded by `B`, `L_i(λ_max) ≤ α` | Angelopoulos et al., Theorem 1; for non-monotone losses the algorithm "does not control the risk" |

Reading notes (derived):

- All probabilities in the first, third and fifth rows are over the *joint* draw of calibration
  and test data. For a deployed system the calibration set is fixed, so the relevant statement
  is the second row; with continuous scores the conditional coverage is distributed as
  `Beta(k, n + 1 − k)`, `k = ⌈(n+1)(1−α)⌉` (the probe evaluates its tail exactly).
- None of the rows is conditional on the input `x`. A 90 % set may cover 100 % of easy inputs
  and far less of a rare, safety-critical class.
- The online guarantee is a statement about a *frequency along the realised sequence*. It holds
  even for adversarial data precisely because it says nothing about any individual step; it
  cannot be multiplied into a per-step probability of safety.
- Exchangeability fails by construction when the predictor's output feeds a controller whose
  actions influence the next observation. The planning framework of Lindemann et al. obtains
  valid prediction regions from "offline trajectory data" and makes "no assumptions on the
  underlying trajectory-generating distribution" (abstract); the body of that paper, and hence
  its precise assumption on the dependence between the ego agent and the predicted agents, was
  not examined.

### 8. Composing the layers for runtime assurance

Basis: derived from §1–§7.

Consider a monitored loop: sensor input → ML model → prediction set → verified controller or
shield whose safety proof assumes "truth ∈ set".

| Layer | Certificate | Adds to the error budget | Does **not** establish |
|---|---|---|---|
| Controller / shield | machine-checked proof (optionally under zero knowledge, §1–§5) | soundness error of the argument system; nothing if checked in the clear | that its assumption "truth ∈ set" holds |
| Prediction set | conformal calibration | `α` marginally; or `E` with confidence `1 − δ` given the calibration set | coverage for this input, this time step, or a shifted distribution |
| Model execution | zkML proof | soundness error | that the executed function is the float model; that inputs are authentic |
| Model provenance | commitment / fixed parameters | — | absence of backdoors, including quantisation-activated ones |

- **Budgets add by the union bound.** Over a horizon of `T` decisions with per-step marginal
  level `α`, the guaranteed probability that *all* sets cover is only `1 − Tα` (useful only if
  `α ≪ 1/T`), and this still presumes exchangeability across steps and calibration.
- **Calibrate the function that runs.** Conformal scores must be computed with the quantised
  model `f_q`; calibrating with `f` and deploying `f_q` breaks exchangeability of the scores in a
  way no later layer detects. Conversely, calibrating on `f_q` makes the quantisation gap
  irrelevant to coverage: conformal validity holds for any score function.
- **Zero knowledge is orthogonal to validity.** Proving in zero knowledge that a calibration
  quantile was computed correctly from committed calibration data shows the arithmetic was
  right; it cannot show the data were exchangeable with deployment.
- **Closed loop.** If actions depend on set size, use an online method and state the guarantee
  as a long-run frequency with the explicit finite-`T` bound, plus an independent fallback for
  the steps that miss; or enforce by design that the calibrated quantity is not influenced by
  the controlled system.

### 9. Executable probes

Basis: execution.

```python
#!/usr/bin/env python3
"""Stdlib-only probes: (A) resolution steps checked as polynomial identities,
(B) fixed-point versus floating-point inference, (C) split-conformal coverage,
distribution shift, a closed loop, and adaptive conformal inference (ACI)."""
import math
import random
from itertools import combinations, product

# ---------- A. clause = monic polynomial whose roots are its literals ----------
P = (1 << 61) - 1                       # a prime; literal 2v is v, literal 2v+1 is not-v


def poly(roots):                         # coefficients, low degree first
    p = [1]
    for r in roots:
        p = [((p[i - 1] if i else 0) - r * (p[i] if i < len(p) else 0)) % P
             for i in range(len(p) + 1)]
    return p


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return out


def divides(d, n):                       # does the monic d divide n over GF(P)?
    n = n[:]
    for k in range(len(n) - len(d), -1, -1):
        q = n[k + len(d) - 1]
        for j, c in enumerate(d):
            n[k + j] = (n[k + j] - q * c) % P
    return not any(n)


def step_ok(c0, c1, res, pivot):         # c0 | res*(X-pivot)  and  c1 | res*(X-not pivot)
    return (divides(poly(c0), mul(poly(res), poly([pivot]))) and
            divides(poly(c1), mul(poly(res), poly([pivot ^ 1]))))


a, na, b, nb, c = 2, 3, 4, 5, 6
print("A: valid step {a,b},{~a,b} |- {b}:", step_ok([a, b], [na, b], [b], a))
print("A: weakened resolvent {b,c} accepted:", step_ok([a, b], [na, b], [b, c], a))
print("A: bogus resolvent {} rejected:", not step_ok([a, b], [na, b], [], a))
print("A: wrong pivot rejected:", not step_ok([a, b], [na, b], [b], b))
print("A: refutation of (a|b)(~a|b)(a|~b)(~a|~b):",
      step_ok([a, b], [na, b], [b], a) and step_ok([a, nb], [na, nb], [nb], a)
      and step_ok([b], [nb], [], b))
LITS = [a, na, b, nb]
CLAUSES = [list(s) for r in range(5) for s in combinations(LITS, r)]


def holds(cl, m):                        # m: variable -> bool
    return any(m[l >> 1] == (l & 1 == 0) for l in cl)


accepted = unsound = 0
for c0, c1, res in product(CLAUSES, repeat=3):
    for pv in LITS:
        if step_ok(c0, c1, res, pv):
            accepted += 1
            unsound += any(holds(c0, m) and holds(c1, m) and not holds(res, m)
                           for m in ({1: x, 2: y} for x in (0, 1) for y in (0, 1)))
print(f"A: exhaustive over 16^3 clause triples x 4 pivots: accepted={accepted} unsound={unsound}")

# ---------- B. fixed-point (scale 2^s) versus float64 for a small ReLU network ----------
rng = random.Random(1)
D, H, K, N = 4, 8, 3, 20000
W1 = [[rng.uniform(-1, 1) for _ in range(D)] for _ in range(H)]
B1 = [rng.uniform(-1, 1) for _ in range(H)]
W2 = [[rng.uniform(-1, 1) for _ in range(H)] for _ in range(K)]
B2 = [rng.uniform(-1, 1) for _ in range(K)]
XS = [[rng.uniform(-1, 1) for _ in range(D)] for _ in range(N)]


def rnd(x):                              # round half away from zero
    return int(math.copysign(math.floor(abs(x) + 0.5), x))


def net_float(x):
    h = [max(0.0, sum(w * v for w, v in zip(row, x)) + bb) for row, bb in zip(W1, B1)]
    return [sum(w * v for w, v in zip(row, h)) + bb for row, bb in zip(W2, B2)]


def net_fixed(x, s):                     # inputs/weights at scale s, biases at 2s
    q = lambda v, sc: rnd(v * (1 << sc))
    xi = [q(v, s) for v in x]
    pre = [sum(q(w, s) * v for w, v in zip(row, xi)) + q(bb, 2 * s) for row, bb in zip(W1, B1)]
    h = [max(0, (v + (1 << (s - 1))) >> s) for v in pre]          # rescale 2s -> s, ReLU
    out = [sum(q(w, s) * v for w, v in zip(row, h)) + q(bb, 2 * s) for row, bb in zip(W2, B2)]
    return out, max(abs(v) for v in pre + out)


argmax = lambda v: max(range(len(v)), key=v.__getitem__)
FL = [net_float(x) for x in XS]
for s in (4, 7, 10, 13):
    flips, err, big, margin = 0, 0.0, 0, None
    for x, f in zip(XS, FL):
        o, m = net_fixed(x, s)
        big = max(big, m)
        err = max(err, max(abs(u / (1 << (2 * s)) - v) for u, v in zip(o, f)))
        if argmax(o) != argmax(f):
            flips += 1
            top = sorted(f)
            margin = max(margin or 0.0, top[-1] - top[-2])
    print(f"B: scale={s:2d} argmax flips={flips}/{N} max|logit err|={err:.5f} "
          f"largest float margin among flips={margin if margin is None else round(margin, 5)} "
          f"max|intermediate|={big} (2^{big.bit_length()})")
PF = (1 << 31) - 1                       # toy prime field without range constraints
signed = lambda z: z if z <= PF // 2 else z - PF
print("B: 2^16 * 2^16 in GF(2^31-1), read back as signed:", signed((1 << 16) * (1 << 16) % PF))

# ---------- C. split conformal: exact coverage, conditional spread, shift, feedback ----------
rng = random.Random(0)
ALPHA = 0.1


def threshold(sorted_cal, alpha):        # ceil((n+1)(1-alpha))-th smallest score
    n = len(sorted_cal)
    k = math.ceil((n + 1) * (1 - alpha) - 1e-12)
    return math.inf if k > n else (-math.inf if k < 1 else sorted_cal[k - 1])


for n in (8, 9, 19, 20, 99):
    k = math.ceil((n + 1) * (1 - ALPHA) - 1e-12)
    trials = 100000
    hit = sum(rng.random() <= threshold(sorted(rng.random() for _ in range(n)), ALPHA)
              for _ in range(trials))
    print(f"C: n={n:3d} k={k:3d} exact min(k/(n+1),1)={min(k / (n + 1), 1):.4f} "
          f"simulated={hit / trials:.4f}")
for n in (19, 199, 1999):                # coverage given the calibration set ~ Beta(k, n+1-k)
    k = math.ceil((n + 1) * (1 - ALPHA) - 1e-12)
    tail = lambda cov: sum(math.comb(n, j) * cov ** j * (1 - cov) ** (n - j)
                           for j in range(k, n + 1))
    print(f"C: n={n:4d} P(conditional coverage < 0.85)={tail(0.85):.4f} "
          f"P(< 0.80)={tail(0.80):.6f}")
CAL = sorted(abs(rng.gauss(0, 1)) for _ in range(999))
Q0 = threshold(CAL, ALPHA)
for scale in (1.0, 1.25, 1.5, 2.0):
    cov = sum(abs(rng.gauss(0, scale)) <= Q0 for _ in range(50000)) / 50000
    print(f"C: test noise scale {scale:4.2f} -> coverage {cov:.4f} (target {1 - ALPHA})")


def closed_loop(adaptive, steps=20000, gamma=0.01):
    at, errs = ALPHA, []
    for _ in range(steps):
        r = threshold(CAL, min(max(at, 0.0), 1.0)) if 0 < at < 1 else (math.inf if at <= 0 else -math.inf)
        aggress = min(1.0, max(0.0, 1.5 - r / 2))          # smaller region -> bolder action
        err = abs(rng.gauss(0, 1 + 0.8 * aggress)) > r     # bolder action -> noisier world
        errs.append(err)
        if adaptive:
            at += gamma * (ALPHA - err)
    worst = max(sum(errs[i:i + 200]) / 200 for i in range(0, steps - 200, 50))
    return sum(errs) / steps, worst, at


for name, ad in (("static split conformal", False), ("ACI gamma=0.01", True)):
    rate, worst, at = closed_loop(ad)
    bound = (max(ALPHA, 1 - ALPHA) + 0.01) / (20000 * 0.01)
    print(f"C: closed loop, {name}: miscoverage={rate:.4f} worst 200-step window={worst:.3f} "
          f"final alpha_t={at:.4f}" + (f" |rate-alpha|={abs(rate - ALPHA):.5f} <= bound {bound:.5f}: "
                                       f"{abs(rate - ALPHA) <= bound}" if ad else ""))
```

Output of `python3 assurance_probes.py` (exit status 0, about 20 s, deterministic):

```text
A: valid step {a,b},{~a,b} |- {b}: True
A: weakened resolvent {b,c} accepted: True
A: bogus resolvent {} rejected: True
A: wrong pivot rejected: True
A: refutation of (a|b)(~a|b)(a|~b)(~a|~b): True
A: exhaustive over 16^3 clause triples x 4 pivots: accepted=3600 unsound=0
B: scale= 4 argmax flips=757/20000 max|logit err|=0.25298 largest float margin among flips=0.12915 max|intermediate|=1279 (2^11)
B: scale= 7 argmax flips=80/20000 max|logit err|=0.03654 largest float margin among flips=0.01211 max|intermediate|=83557 (2^17)
B: scale=10 argmax flips=20/20000 max|logit err|=0.00465 largest float margin among flips=0.00211 max|intermediate|=5326607 (2^23)
B: scale=13 argmax flips=1/20000 max|logit err|=0.00057 largest float margin among flips=2e-05 max|intermediate|=340991585 (2^29)
B: 2^16 * 2^16 in GF(2^31-1), read back as signed: 2
C: n=  8 k=  9 exact min(k/(n+1),1)=1.0000 simulated=1.0000
C: n=  9 k=  9 exact min(k/(n+1),1)=0.9000 simulated=0.8995
C: n= 19 k= 18 exact min(k/(n+1),1)=0.9000 simulated=0.9010
C: n= 20 k= 19 exact min(k/(n+1),1)=0.9048 simulated=0.9060
C: n= 99 k= 90 exact min(k/(n+1),1)=0.9000 simulated=0.8997
C: n=  19 P(conditional coverage < 0.85)=0.1985 P(< 0.80)=0.082866
C: n= 199 P(conditional coverage < 0.85)=0.0159 P(< 0.80)=0.000051
C: n=1999 P(conditional coverage < 0.85)=0.0000 P(< 0.80)=0.000000
C: test noise scale 1.00 -> coverage 0.8857 (target 0.9)
C: test noise scale 1.25 -> coverage 0.7979 (target 0.9)
C: test noise scale 1.50 -> coverage 0.7081 (target 0.9)
C: test noise scale 2.00 -> coverage 0.5725 (target 0.9)
C: closed loop, static split conformal: miscoverage=0.3155 worst 200-step window=0.425 final alpha_t=0.1000
C: closed loop, ACI gamma=0.01: miscoverage=0.1003 worst 200-step window=0.140 final alpha_t=0.0300 |rate-alpha|=0.00035 <= bound 0.00455: True
```

Reading:

- **A.** The two divisibility identities accept exactly sound inferences in the exhaustive model
  (3600 accepted, 0 unsound), including weakened resolvents; they reject a non-implied resolvent
  and a wrong pivot. The probe uses a prime field and literal encoding `2v`/`2v+1`; the examined
  implementation uses GF(2^128) and a bit flip, and checks the identities through committed
  witness polynomials rather than by division.
- **B.** Class disagreement between float and fixed-point evaluation falls with scale but does
  not vanish: 757, 80, 20, 1 of 20 000 at scales 4, 7, 10, 13, while the largest intermediate
  grows from 2^11 to 2^29. At scale 7 disagreement occurs for inputs whose float margin is as
  large as 0.012 although the maximum logit error is 0.037. The last line shows a product
  exceeding a field modulus being read back as a small number when no range constraint
  intervenes. The network and rescaling scheme are generic, not EZKL's circuit.
- **C.** (i) Marginal coverage equals `k/(n+1)` exactly (and is 1 when `k > n`: with 8
  calibration points a 90 % set must be the whole space). (ii) Given the calibration set,
  coverage below 0.85 has probability 0.20 for `n = 19`, 0.016 for `n = 199`, and is negligible
  for `n = 1999`. (iii) The single calibration set of 999 scores used afterwards happens to give
  0.886 on unshifted data — an instance of (ii) — and 0.80, 0.71, 0.57 when the test noise scale
  grows by 25 %, 50 %, 100 %. (iv) In the feedback loop, where a smaller region makes the
  controller bolder and the world noisier, static calibration miscovers 31.6 % of the time; ACI
  returns the long-run rate to 10.0 % within the deterministic bound, with its worst 200-step
  window at 14 % and its internal level driven from 0.10 to 0.03.

## Boundaries

- **Not examined:** the full text of the zkPi paper (only abstract and ePrint metadata were
  retrievable). Design rationale, the security proof, proof sizes, and the exact evaluation
  protocol are therefore not reported; the code-derived description in §2 may include
  post-publication changes (the repository contains Lean 4 extensions and several generations of
  result tables).
- **Not examined:** the full text of the ZKUNSAT paper, including how the published protocol
  treats a public or committed input formula. The "no binding" finding in §3 is about the
  examined `main.cpp` only.
- **Not examined:** ZKSMT's implementation; EZKL's circuit layouts, lookup tables and rescaling
  logic beyond the quoted functions and defaults; the Trail of Bits review that the EZKL README
  cites; the Halo2 proof system itself.
- **Not examined:** the bodies of Angelopoulos and Bates (arXiv 2107.07511), Lindemann et al.
  (arXiv 2210.10254) and Barber et al., "Conformal prediction beyond exchangeability" (arXiv
  2202.13415). No statement about their theorems is made beyond the quoted abstract phrases.
- **Not examined:** any execution of zkPi, ZKUNSAT or EZKL. All performance numbers are those
  recorded by the upstream authors.
- **Unknown:** the meaning of return code 247, the largest failure class in the zkPi result
  tables (it is not in the harness legend). Unknown: which Lean versions and library snapshots
  the "new_complete" tables were produced from.
- **Unknown:** whether zkPi's rule system is sound and complete relative to Lean's kernel on the
  supported fragment; no mechanised or written argument was among the examined material.
- **Unknown:** whether the multiplexed per-node design or the group-checking design leaks less
  in practice for a given proof corpus; they leak different things (sizes only, versus sizes plus
  a rule histogram).
- **Known not to apply:** conformal marginal guarantees to an individual input, to a fixed
  calibration set without the PAC correction, or to data affected by the predictor's own
  downstream actions; the ACI bound to any single time step; conformal risk control to
  non-monotone losses.
- **Known not to apply:** a zkML proof to properties of the unquantised model; a zero-knowledge
  proof-checking certificate to the question of whether the public axioms and declarations are
  acceptable.
- **Unsupported (by the subject):** in zkPi at the pinned revision — `Quot.sound`, eta
  expansion, recursion on inductive families with recursive parameters, projections on
  non-singleton structures; in the driver, Lean source export for anything but Lean 3.
- **Stronger conclusions not established:** that "zero-knowledge proof of a Lean theorem" means
  the Lean kernel accepted the proof; that hiding a proof hides its size or shape; that a
  proved inference is a correct inference; that a 90 % conformal set makes a controller safe
  with probability 0.9 per step in closed loop.

## Evidence

All evidence was acquired on 2026-11-19.

**Repositories** (revision = commit of the default branch head on that date; inspected from the
revision's source archive).

| Repository @ revision | Paths and anchors |
|---|---|
| `emlaufer/zkpi@c65fc44373306106b741069f7d3cbc8224b21a74` | `driver.py` (Lean version check, `count`/`export`, `meta.zok` template fill, `circ … --proof-system mirage --action oneshot`); `zok/eval.zok` (`check_type_sort` l.382, `check_type_ind` l.686, `check_type_ind_ctor` l.705, `check_type_ind_rec` l.735, `check_type_ax` l.998, `main` l.1230 ff.); `zok/hashlist.zok` (`compute_hashes`, `hash_list_contains`); `zok/constants.zok`; `zok/structs.zok`; `zok/meta.zok.template`; `src/zk/mod.rs` (`Exporter::with_axioms` l.2338–2360, `simulate` l.2424 ff., `export` l.2458 ff., `add_axiom_term` l.3269 ff., `panic!("eta unsupported")` l.3054, l.3075); `src/lean.rs` l.917–922 (`Quot` handling); `src/term.rs` l.1721, l.1814; `circ/src/target/r1cs/mirage.rs` l.126–128; `Lean4Examples/lean-toolchain`; `.gitmodules`; `scripts/commander.py` l.108–158 (command line, 1800 s limit, return-code legend); `scripts/param_sweep.csv`; `scripts/stdlib_times_new_complete.csv`; `scripts/mathlib_times_new_complete.csv` |
| `PP-FM/ZKUNSAT@9970d3d3f838425e04d0266b0ce84a55202d9c5b` | `main.cpp` (party setup, `readproof` on the prover only, `send_data` of `nres`, `ncls`, `DEGREE`, `chain_length`); `clause.h` (`get_negate`, `witness_generator`, `check_xres`, `get_res_f2k`); `polynomial.cpp` (committing constructors; `ConverseCheck` l.157–177); `clauseRAM.h` (`init` l.60, `check_chain` l.340–392); `utils.h` (`VAL_SZ`, `readproof` l.306 ff.); `prover_backend/preprocess.sh` |
| `zkonduit/ezkl@e196b111c1bafaa61b92ae431cd3c3fe9371da05` | `src/graph/utilities.rs` l.53–90 (`quantize_float`, `dequantize`, `scale_to_multiplier`); `src/fieldutils.rs` l.6, l.35–49; `src/lib.rs` l.168, l.199–284 (`RunArgs` fields), l.294–322 (defaults); `src/circuit/ops/chip.rs` l.36–40 (`CheckMode`); `src/commands.rs` l.45, l.83–91; `src/execute.rs` l.792 ff. (`AccuracyResults`); `src/pfsys/mod.rs` l.469–479; `README.md` (statements, quantisation note, audit pointer); `docs/advanced_security/quantization_backdoors.md`; `docs/advanced_security/public_commitments.md` |

**Papers read in full text.**

- D. Luick, J. C. Kolesar, T. Antonopoulos, W. R. Harris, J. Parker, R. Piskac, E. Tromer,
  X. Wang, N. Luo, "ZKSMT: A VM for Proving SMT Theorems in Zero Knowledge", 33rd USENIX Security
  Symposium, 2024 (proceedings ISBN 978-1-939133-44-1), pp. 3837 ff.;
  `https://www.usenix.org/conference/usenixsecurity24/presentation/luick`.
- D. Kang, T. Hashimoto, I. Stoica, Y. Sun, "Scaling up Trustless DNN Inference with
  Zero-Knowledge Proofs", arXiv:2210.08674v1.
- R. J. Tibshirani, R. Foygel Barber, E. J. Candès, A. Ramdas, "Conformal Prediction Under
  Covariate Shift", arXiv:1904.06019v3.
- I. Gibbs, E. Candès, "Adaptive Conformal Inference Under Distribution Shift",
  arXiv:2106.00170v3.
- A. N. Angelopoulos, S. Bates, A. Fisch, L. Lei, T. Schuster, "Conformal Risk Control",
  arXiv:2208.02814v4.
- V. Vovk, "Conditional validity of inductive conformal predictors", arXiv:1209.2673v2 (arXiv
  comment: "to appear in the ACML 2012 Proceedings").

**Abstract and metadata only.**

- E. Laufer, A. Ozdemir, D. Boneh, "zkPi: Proving Lean Theorems in Zero-Knowledge", Cryptology
  ePrint 2024/267 ("Published elsewhere. Major revision. ACM CCS 2024", DOI
  10.1145/3658644.3670322). Quoted: "zkPi successfuly proves 57.9% of the theorems in stdlib,
  and 14.1% of the theorems in mathlib, within 4.5 minutes per theorem"; "a prover can convince
  a verifier that a Lean theorem is true, while revealing little else".
- N. Luo, T. Antonopoulos, W. Harris, R. Piskac, E. Tromer, X. Wang, "Proving UNSAT in Zero
  Knowledge", Cryptology ePrint 2022/206. Quoted: "represent formula clauses as low-degree
  polynomials, combined with ZK random-access arguments. Only the proof's dimensions are
  revealed."
- A. N. Angelopoulos, S. Bates, "A Gentle Introduction to Conformal Prediction and
  Distribution-Free Uncertainty Quantification", arXiv:2107.07511 (v6 listed).
- L. Lindemann, M. Cleaveland, G. Shim, G. J. Pappas, "Safe Planning in Dynamic Environments
  using Conformal Prediction", arXiv:2210.10254 (v2 listed).

**Derived statistics.** The result-table rows in §2 were computed from the two CSV files with
Python's `csv` module: successes are rows with `returncode == 0`; times are the `prove_time` and
`verify_time` columns divided by 10^9; percentiles are order statistics at index
`⌊p·(m−1)⌋` of the sorted successes. The per-unit costs are differences between the 100 and 1000
rows of `scripts/param_sweep.csv` divided by 900.

**Execution.** CPython 3.13.15 on Linux, standard library only; the program in §9 is reproduced
verbatim; SHA-256 of the file as run:
`8abec6a5f0308a5a55b850b24602cc0346f2280bf6de7d8e649739dec76f603c`. Random streams are seeded
(`random.Random(1)`, `random.Random(0)`); two consecutive runs produced identical output.

## Revalidation

- **zkPi public/private boundary** (most consequential, cheapest): at a new revision, read the
  parameter list of `main` in `zok/eval.zok` and `Exporter::with_axioms` in `src/zk/mod.rs`.
  A change in which parameters carry `private`, or in what is copied into `public_terms`,
  changes §2 and §5. `grep -n "Quot\|eta unsupported\|only supported" src/*.rs src/zk/*.rs`
  re-derives the unsupported list; `grep -ci positiv zok/eval.zok` re-checks the absence of
  in-circuit declaration checks.
- **zkPi numbers**: recompute the table of §2 from the two CSV files as described under
  "Derived statistics"; compare `scripts/param_sweep.csv` rows. If the circuit is rebuilt,
  CirC's reported "Final R1cs size" for a theorem should match the corresponding CSV row.
- **ZKUNSAT**: in `main.cpp`, check every `send_data` call (leakage) and whether anything on the
  verifier side now constrains the first `ncls − nres` clauses (binding). In `clause.h`, re-read
  `check_xres` to confirm the two identities.
- **ZKSMT**: the leakage paragraph ("Information Leakage") and the size-parameter list in
  Section 3.1 of the paper are the statements relied upon.
- **EZKL**: `grep -n "input_scale\|param_scale\|lookup_range\|check_mode" src/lib.rs` for the
  defaults; `sed -n '53,70p' src/graph/utilities.rs` for the quantisation formula; `grep -n
  "quantized" README.md` for the semantics note. To measure the float/fixed gap for a concrete
  model, compare the framework's outputs with the outputs of `ezkl gen-witness` on the intended
  input distribution — per §6 this is a measurement, not a guarantee.
- **Conformal statements**: the theorem numbers in §7 identify the exact statements; re-read
  them if a later arXiv version is used.
- **Mechanism probes**: copy the program of §9 to `assurance_probes.py` and run it; output must
  match the block above byte for byte. To explore another feedback law, edit the two lines in
  `closed_loop` that define `aggress` and the noise scale; to explore another network or
  rescaling scheme, edit `net_fixed`. A passing probe says nothing about any deployed model or
  environment.
- **No cheap revalidation exists** for soundness of zkPi's rule system relative to Lean, for
  authenticity of zkML inputs, or for exchangeability of a deployment; each needs its own
  argument or measurement campaign.
