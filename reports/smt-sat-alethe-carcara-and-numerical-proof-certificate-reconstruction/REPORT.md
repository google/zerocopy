# SMT, SAT, Alethe/Carcara, and Numerical Proof Certificate Reconstruction and Checking Boundaries

## Summary

Across SMT (Alethe/Carcara, SMTCoq, LFSC, `lean-smt`, Isabelle SMT, Why3), SAT and pseudo-Boolean (DRAT, FRAT, LRAT, GRAT, CakeML `lpr_array`/`npbc_full`, VeriPB), and exact or rounded numerical certificate systems (Mathlib `linarith`, HOL Light `SOS`, FloVer, Gappa), external solvers and certificate elaborators earn verification authority only through a specific checking endpoint bound to the consumer's exact root obligation:

1. **Strict Alethe Expansion and Native Carcara Checking for Guarded Byte Laws**: All four fixed finite byte-law roots (`into_bytes`, `byte_write`, `bool_validate`, and `array_validate`, anchored to `ByteLaws.lean`) have complete certificates accepted (`valid\n`, exit `0`) by the unchanged native Carcara `1.1.0` checker (`ufmg-smite/carcara@20bf49c5ce31089ac83118574c888669355aaae1`) after actual `cvc5 1.4.2` (`cvc5/cvc5@282d5e0c84baf49c780704c532f87ba66d8b513d`) proof generation (`--proof-format-mode=alethe --proof-granularity=dsl-rewrite-strict`) and an untrusted local expansion (`translate.py`) of five exported `rare_rewrite` names (`array-read-over-write`, `eq-refl`, `eq-symm`, `bool-double-not-elim`, and `arith-elim-lt`). Three raw unexpanded `cvc5` exports fail before translation; ten negative rejection controls and five fresh SAT-to-Lean refutations (`final-run/SolverWitnesses.lean`, checked by Lean `4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`) preserve the initializedness, alias/frame, validity, stability, array-coverage, and full-domain distinctions.
2. **SMT Certificate Root Binding, Carcara Configuration Contracts, and Elaboration Diagnostics**: A Boolean certificate checker with a soundness theorem (SMTCoq `MainChecker.v` / `Euf_Checker.checker_correct`), proof reconstruction into the host assistant (`ufmg-smite/lean-smt` `Smt/Reconstruct.lean` and Isabelle `smt_solver.ML`), and LFSC signature checking (`cvc5/LFSC` `src/check.cpp`) impose distinct trust and root-binding obligations. In Carcara (`src/checker/mod.rs`), `Config.allowed_rules` permits named rules without checking them while still returning `Valid`, and `hole` or `lia_generic` steps return `holey` with process exit code `0` (as observed when encoding an outside-cell `QF_AUFBV` array frame premise with `distinct` instead of `(not (= changed framed))`). A closed-certificate consumer must pin an empty `allowed_rules` set, reject `holey` verdicts despite exit `0`, strip Carcara `elaborate`'s leading `valid\n` verdict line before rechecking with `--check-granularity elaborated`, and distinguish false source claims (with concrete safe Rust counterexample replay via `diagnostic_witness.rs`) from proof holes or root mismatches.
3. **SAT, Pseudo-Boolean, and Bitvector Certificate Endpoints**: DRAT (`marijnheule/drat-trim`) and FRAT (`digama0/frat`) producers/elaborators remain outside the trusted search path when a final LRAT or GRAT (`IsaFoL` `Unsat_Check.thy`) or pseudo-Boolean (`StephanGocht/VeriPB` and CakeML `npbc_fullProofScript.sml`) certificate is checked against the consumer's original input. Lean `4.34.1` provides proved LRAT and bitvector reflection theorems (`LRAT.check_sound`, `Reflect.verifyCert_correct`, `unsat_of_verifyBVExpr_eq_true`), but its examined `bv_decide` frontend (`LratCert.toReflectionProof` in `src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean`) discharges checking via `nativeEqTrue` (`Lean.ofReduceBool`). CakeML (`CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`) supplies x64 machine-code soundness theorems (`lpr_arrayProofScript.sml`, `npbc_fullProofScript.sml`) with explicit CLI, filesystem, installed-code, and resource-limit premises.
4. **Exact vs. Rounded Numerical Proof Witnesses and Checking Paths (Farkas, SOS, FloVer, Gappa, Why3)**: Mathlib4's `proveFalseByLinarith` (`Mathlib/Tactic/Linarith/Verification.lean`) and HOL Light's `SOS_CONV` / `PURE_SOS_TAC` (`Examples/sos.ml`) treat external numerical/LP/SDP output purely as untrusted search hints, reconstructing exact algebraic identities and strict-inequality or sum-of-squares sign proofs inside the host logic. For finite-precision rounding, FloVer (`gitlab.mpi-sws.org/AVA/FloVer@2b846b7242db7435c97ba694393db47842b19860` and FMCAD 2018) requires explicit error-map (`DeltaMap`), environment (`approxEnv`), SMT query unsatisfiability (`unsat_queries Qmap`), no-subnormal (`IEEEevalAvoidsSubnormals` / `eval_expr_valid`), and no-downcast/no-`Inv`/no-`Fma` premises (`IEEE_connection.v`). Gappa (`gitlab.inria.fr/gappa/coq@e4f093c3f8fef4bb163e5b29c92d95514a4c9bdf`) constructs Rocq terms over Flocq real rounding models while discharging computational side conditions via `Constr.VMcast` and `refine_no_check` (`src/gappatac.c:793-843`). Why3 (`gitlab.inria.fr/why3/why3@d0a8072e157935d0d80a7a2156ecf5a98a2aae3e`) applies unverified OCaml task transformations (`src/core/trans.ml`, `src/driver/driver.ml`) and regex driver classification (`drivers/smt-libv2.gen`, `call_provers.ml`), meaning a Why3 `Valid` status is not a kernel proof of the pre-transformation source obligation.

## Applicability

This report synthesizes six primary-source and empirical investigations observed on `2026-10-14` across SMT, SAT/PB, and numerical certificate checking paths:

1. **Strict Alethe Expansion and Native Carcara Checking on Fixed Guarded Byte Laws**:
   - Executed on Darwin `arm64` using `cvc5 1.4.2` (`cvc5/cvc5@282d5e0c84baf49c780704c532f87ba66d8b513d`, binary SHA-256 `74a9c8ab076ed0dbced2aef27de675846e4a8937e3f3d49125721f2d91bdcf4d`), `Carcara 1.1.0` (`ufmg-smite/carcara@20bf49c5ce31089ac83118574c888669355aaae1`, binary SHA-256 `4016f1129baf0b82b1a4ee9c64ec2f4f0376cabe75cb07674fdd452847f8963f`), and `Lean 4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, shared library SHA-256 `6588b7e38450ea749006dcd90bbaea9393a5ca1b64727a2e7138f3c9427c2b50`, `Init.olean` SHA-256 `e350f457fb746028d5761304fd7df55a83b46ea56cdd7702fdee32600b57db22`). Note that the Lean launcher hash alone is not a version identity; exact executable, shared-library, and `Init.olean` hashes are bound in `tool-locks.json`.
   - The fixed semantic fixture is `ByteLaws.lean` (SHA-256 `275e5f09043bc8091f3b962aada7e6a1b2d24876d9aeca0b323d5e38ac983acc`), where bytes range over `Fin 256`, addresses are two Boolean indices, and byte values, initializedness, read authority, and write authority are separate fields. The corresponding SMT roots retain the original `QF_AUFLIA` integer/array encoding and every original assertion (`root-locks.json`, `predicate-map.json`), with untrusted rewrite expansion performed by `translate.py` (SHA-256 `34f43a206b1a3756004fbc0e37bfb3914208460eaad68333b20ff9b2be19f684`).
2. **SMT Certificate Checkers, Reconstruction Interfaces, and Root Binding**:
   - Source-level interface audit at six immutable pins: `SMTCoq/smtcoq@7b870140f2ff7e4547a7db614a305d8b2945afa3`, `ufmg-smite/carcara@20bf49c5ce31089ac83118574c888669355aaae1`, `cvc5/LFSC@5a127dbbcf9a0f822768e783dbf892ee90c435d5`, `cvc5/cvc5@f0bc3373ef032a3fc5006f22778aaae7b274f429`, `ufmg-smite/lean-smt@9abdd01c13dc7ac2bac4d68d17ee661c63ed0894`, and `isabelle-prover/mirror-isabelle@39c77411f67871f5a8f06140c588e196a9aa9ca8`.
3. **SMT Frame Diagnostics, Alethe Elaboration, and Phase-Separated Checking Costs**:
   - Executed on `aarch64-apple-darwin` using `cvc5 1.4.2` (`282d5e0c84baf49c780704c532f87ba66d8b513d`, official macOS `arm64` static archive SHA-256 `24397f7d022e755876ca836193d4c5f9c1d4326f0f6c01f7d7fc1ddd6bc5096c`), `Carcara` (`20bf49c5ce31089ac83118574c888669355aaae1`, built with Rust `1.99.0` at `rust-lang/rust@b940084d7eb6a299eb4bfeb8e34901bc051e7ac4` in release mode from locked dependencies), and SMT-LIB `ArraysEx` version `2.7` (`2024-07-21`) over `QF_AUFBV` (8-bit indices and values, one store, a second read, and an outside-cell premise), with owned input bundle SHA-256 `f6db0f454be824e8bd7a48a6a4434afd963d3dac9edac3ac447c4dbec77f6f09`.
4. **SAT, Pseudo-Boolean, and Bitvector Certificate Endpoints**:
   - Source comparison across `marijnheule/drat-trim@2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, `digama0/frat@aa18581497830b49a6ab6cbc9e0dc778c14885b5`, `IsaFoL/IsaFoL@1475076cea603c64d3dfe70c91014a5264e0479b`, `CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `StephanGocht/VeriPB@01b7b5088c8a67f1611427174501191bc5f5b365`, and the VeriPB proof format version `3` specification (`https://veripb.org/overview.html`), paired with Lean `4.34.1` execution of `LratControls.lean` on Darwin `arm64`.
5. **Exact and Rounded Numerical Proof Witnesses and Checking Paths**:
   - Source and primary-literature evaluation across `leanprover-community/mathlib4@b16cf9ed26f2e49057943824f2f74f9783b7cb40`, `jrh13/hol-light@233b83c3202370e03c54de2bd090e4d34f677e91`, `ufmg-smite/carcara@20bf49c5ce31089ac83118574c888669355aaae1`, `SMTCoq/smtcoq@7b870140f2ff7e4547a7db614a305d8b2945afa3`, the FloVer FMCAD 2018 paper (*A Verified Certificate Checker for Finite-Precision Error Bounds in Coq and HOL4*), FloVer upstream source `https://gitlab.mpi-sws.org/AVA/FloVer` (`2b846b7242db7435c97ba694393db47842b19860`), Gappa Rocq support library `https://gitlab.inria.fr/gappa/coq` (`e4f093c3f8fef4bb163e5b29c92d95514a4c9bdf` and `gappalib-coq-1.11.0.tar.gz` SHA-512 `654d4787998ce085b8ce7e6f6c266e826e9581b34002c1c0995972a3927800e5732f8e6205ea63047aca84327413f4e2f774e2c5627fe7b98fba809250c0b857`), and Why3 upstream `https://gitlab.inria.fr/why3/why3` (`d0a8072e157935d0d80a7a2156ecf5a98a2aae3e`).

## Findings

### 1. Strict Alethe Rule Expansion and Native Carcara Checking for Fixed Guarded Byte Laws

#### 1.1 Unchanged Whole-Law Semantic Roots (`ByteLaws.lean` and `roots/*.smt2`)

`Basis: source + execution`

| Original root | SHA256 | Required consequence |
| --- | --- | --- |
| `roots/into_bytes.smt2` | `3f775009794160d1c56006f39c8cf8fd687cd438723e799204b1a37922c784e9` | All four initialization/read flags required by observation hold. The existing `observe_success_iff` connects these flags to successful byte-pair observation. |
| `roots/byte_write.smt2` | `6046a6c9cd3101bd01b1ca67afa39ec57d5daaaaaa2c9f2aa826298827258e70` | At the write index, value becomes replacement and initialization becomes true; at the distinct frame index, both value and initializedness remain unchanged. Write authority and disjointness remain asserted. |
| `roots/bool_validate.smt2` | `e85da6710cea19f811a8e431b34bec7b1125f445d8ba5e26667f5b92b56292d2` | Under snapshot/current readiness, equality and snapshot validity, current readiness and `not(current[0] >= 2)` hold. |
| `roots/array_validate.smt2` | `746f9d38906c183189a7195f1248f3f97a387dc001cfc6edd207f9058766cdb2` | Under readiness, equality and validity at both indices, all current readiness flags and validity at both indices hold. |

Every root includes the original full byte domain `0 <= b < 256`, replacement domain, and two-address domains; arbitrary SMT array entries outside indices `0` and `1` are unobserved by the quoted fixture. A proof need not use every asserted premise, and unused premises are not removed from the consumer's root. The write certificate refutes the negation of its complete four-conjunct target (including the outside initialization frame) rather than a byte-frame-only projection. In `ByteLaws.lean`, the guarded `writeByte` and `observe` operations relate to pure SMT store/read terms through the explicit finite predicate map (`predicate-map.json`) and mapping lemmas.

#### 1.2 Five Local `rare_rewrite` Expansions Repair Raw `cvc5` Exports

`Basis: source + execution + derived`

Fresh `cvc5 1.4.2` executions use `--proof-format-mode=alethe --proof-granularity=dsl-rewrite-strict` on the exact roots, returning `unsat` and Alethe proof text. Raw exports pass Carcara for `IntoBytes` and fail for the other three whole laws because named `rare_rewrite` rules are not recognized by native Carcara (`final-run/*.raw.check.stderr`). `translate.py` replaces only these five observed rewrite steps:

| Exported name | Checked replacement | Precise reason |
| --- | --- | --- |
| `array-read-over-write` | `arrays_idx` | The original conclusion is exactly `select(store A i v, i) = v`. |
| `eq-refl` | `eq_simplify` | The original conclusion is `(t = t) = true`. |
| `eq-symm` | `eq_symmetric` | The original conclusion is `(t = u) = (u = t)`. |
| `bool-double-not-elim` | `not_simplify` | The original conclusion removes a double negation. |
| `arith-elim-lt` | Four helper steps using `comp_simplify`, `cong`, `symm`, then the original step using `trans` | `< a b` and `not(>= a b)` are each proved equal to `not(<= b a)`. |

In the arithmetic expansion, Carcara's `comp_simplify` rule produces `not(<= b a)` from `< a b` and `<= b a` from `>= a b`; congruence under `not`, symmetry, and transitivity derive the exact original conclusion without introducing any new arithmetic assumption. `translate.py` preserves every original assumption line, every original step identifier and conclusion, and all non-rewrite lines in order, verified independently by `verify_preservation.py` across all 15 final comparisons (`translation-preservation.json`). Boolean and array proofs each gain eight native helper steps. Unknown rewrite names or unexamined syntax/arity trigger an explicit producer error (`producer-boundary-control.json`). Because `translate.py` is untrusted, native `carcara --no-color check PROOF ROOT` checks the resulting proof against the original SMT root without patches, custom rules, ignored rules, `allowed_rules`, or holes.

#### 1.3 Strict Acceptance Results, Ten Negative Controls, and Five SAT-to-Lean Refutations

`Basis: execution`

Strict acceptance requires native `carcara --no-color check PROOF ROOT` to exit with status `0` and stdout bytes `valid\n`:

| Whole-law root | Raw cvc5 certificate | Locally expanded cvc5 certificate | Final samples |
| --- | --- | --- | --- |
| IntoBytes | `valid`, exit 0 | `valid`, exit 0 | 3/3 |
| Byte writing, all four conjuncts | `invalid`, exit 1 | `valid`, exit 0 | 3/3 |
| Boolean validation | `invalid`, exit 1 | `valid`, exit 0 | 3/3 |
| Array validation, both indices | `invalid`, exit 1 | `valid`, exit 0 | 3/3 |

The narrowed local-domain claim also has a complete expanded proof accepted in `3/3` samples as a negative consumer-binding control (and an independent bounded reconstruction `reconstruct.py` of each of the five roots also passes once as diagnostic evidence for the native rule interface). `final-run/results.json` binds each accepted proof hash, root hash, verdict, exit status, rewrite count, and phase capture.

The consumer executes ten negative checks, all rejected:

| Offered proof or corruption | Consumer result |
| --- | --- |
| IntoBytes proof attached to root missing initialization at index 0 | `invalid`, exit 1 |
| Whole write proof attached to root allowing frame aliasing | `invalid`, exit 1 |
| Boolean proof attached to widened `< 3` guard, allowing byte 2 | `invalid`, exit 1 |
| Boolean proof attached to root lacking snapshot/current stability | `invalid`, exit 1 |
| Array proof attached to root lacking index-1 snapshot validity | `invalid`, exit 1 |
| Valid narrowed-domain proof attached to full-domain widened-guard root | `invalid`, exit 1 |
| A native array step replaced by `hole` | `holey`, exit 0; consumer rejects |
| Array step's conclusion corrupted to `false` | `invalid`, exit 1 |
| Unmatched global assumption `false` inserted | `invalid`, exit 1 |
| Old outside-byte-frame-only proof attached to whole write root | `invalid`, exit 1 |

Fresh `cvc5` queries for the five incorrect laws return `sat`. The owned finite interpreter (`countermodels.py`) evaluates every exact assertion to `true` under each returned scalar/selected-array valuation (`11`, `9`, `14`, `13`, and `19` assertions respectively) without filling missing model entries, and emits the literal valuations to `final-run/SolverWitnesses.lean`. Lean `4.34.1` checks all five refutations with exit code `0`, empty stderr, zero `sorryAx`, and only standard axioms (`propext`, plus `Classical.choice`/`Quot.sound` in shared fixture mapping helpers). Across three sequential timing samples per fixed root, expanded proof sizes are `834` bytes (`IntoBytes`), `4,280` bytes (`byte_write`), `11,684` bytes (`bool_validate`), and `11,953` bytes (`array_validate`), with process-inclusive `cvc5` proof generation taking `10.803–18.745 ms`, in-process translation `0.047–0.565 ms`, and process-inclusive Carcara checking `3.986–5.469 ms`.

---

### 2. SMT Certificate Checkers, Host Reconstruction Interfaces, and Root Binding

#### 2.1 Certificate Roots vs. Host Theorem Statements (`SMTCoq`)

`Basis: source + derived`

In `SMTCoq/smtcoq@7b870140f2ff7e4547a7db614a305d8b2945afa3`, [`theories/checker/MainChecker.v`](https://github.com/SMTCoq/smtcoq/blob/7b870140f2ff7e4547a7db614a305d8b2945afa3/theories/checker/MainChecker.v) defines a generic trace checker folding a step operation over a clause state and testing a selected conflicting clause (`_checker__correct` at lines 83–102; step constructors at lines 379–396; `checker` from line 541; `checker_correct` at lines 725–729). While `Euf_Checker.checker_correct` proves invalidity of the selected root formula under the concrete interpretation (and the constructors `Hole` and `ForallInst` in the proof-bearing `Euf_Checker` carry explicit proof arguments rather than acting as unchecked escape hatches), the extraction-oriented `Checker_Ext.checker_ext_correct` (lines 893–900, 1072–1086) quantifies over a semantic type/function interpretation satisfying `Atom.wt` and leaves existence of a well-typed evaluation as an explicit `TODO`. Root formula arrays, used-root selection, atom interpretation, and host quotation must therefore be explicitly bound to the consumer's intended hypotheses and negated goal.

#### 2.2 Alethe Printing, `Carcara` `Config.allowed_rules`, and Elaboration Pipelines

`Basis: source`

- **`cvc5` Alethe Proof Graph (`alethe_printer.cpp`)**: In [`src/proof/alethe/alethe_printer.cpp`](https://github.com/cvc5/cvc5/blob/f0bc3373ef032a3fc5006f22778aaae7b274f429/src/proof/alethe/alethe_printer.cpp) (`printStep` and `printInternal`, lines 95–117, 213–226, 269–290, 332–343), `cvc5` emits `assume` commands for root assertions, `step` commands with rule/premise references, and `anchor`/discharge scopes for subproofs.
- **Carcara `check_with_stats` and `Config.allowed_rules` Bypass (`checker/mod.rs`)**: In [`src/checker/mod.rs`](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/mod.rs) (`Config.allowed_rules` at lines 123–130, `check_with_stats` at lines 160–266, `check_step` at lines 327–352), Carcara requires an empty clause in the outer context (an empty clause inside a subproof alone is insufficient) and returns `Holey` if any step marked holes (`ignore_unknown_rules`, `hole`, or `lia_generic`), else `Valid`. Crucially, `Config.allowed_rules` allows named rules **without checking them**: `check_step` returns `Ok` immediately before collecting premises or checking discharge, and **does not mark the proof `Holey`**. Any consumer relying on `Valid` must therefore fix `allowed_rules` to empty and audit any custom rule delegation.
- **Carcara `Elaborator` (`elaborator/mod.rs`)**: In [`src/elaborator/mod.rs`](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/elaborator/mod.rs), the elaboration pipeline can fill holes via an external solver, localize coarse steps, uncrowd, and reorder. Elaboration is an untrusted transformation whose output must be independently rechecked against the consumer-selected roots under a locked checker configuration.

#### 2.3 LFSC Signatures and Side-Condition Programs (`cvc5/LFSC`)

`Basis: source + derived`

In `cvc5/LFSC@5a127dbbcf9a0f822768e783dbf892ee90c435d5`, [`src/check.cpp`](https://github.com/cvc5/LFSC/blob/5a127dbbcf9a0f822768e783dbf892ee90c435d5/src/check.cpp) (`call_run_code` from line 71; `PI`/`RUN` application at lines 641–660) and [`tests/tests/sugar_provided.plf`](https://github.com/cvc5/LFSC/blob/5a127dbbcf9a0f822768e783dbf892ee90c435d5/tests/tests/sugar_provided.plf) embed side-condition computations inside dependent function domains (`PI` with `RUN`), executing `call_run_code` and comparing the result by definitional equality. A type-correct LFSC proof depends on the semantic adequacy of the signature's constants/rules, the soundness of its side-condition programs, and the C++ evaluator.

#### 2.4 Host Proof Reconstruction (`ufmg-smite/lean-smt` and Isabelle `smt_solver.ML`)

`Basis: source`

- **Lean SMT (`ufmg-smite/lean-smt@9abdd01c13dc7ac2bac4d68d17ee661c63ed0894`)**: In [`Smt/Reconstruct.lean`](https://github.com/ufmg-smite/lean-smt/blob/9abdd01c13dc7ac2bac4d68d17ee661c63ed0894/Smt/Reconstruct.lean) (context lines 30–46, reconstructor loading lines 61–76, `skipStep`/`addTrust`/`reconstructProof` lines 177–225, solve interfaces from line 335) and [`Smt/Tactic/Smt.lean`](https://github.com/ufmg-smite/lean-smt/blob/9abdd01c13dc7ac2bac4d68d17ee661c63ed0894/Smt/Tactic/Smt.lean) (`evalSmtCore` lines 310–320), fallback `addTrust` creates a metavariable and `skipStep` abstracts it over current assumptions, appending the open subgoal to `skippedGoals` rather than inserting `sorryAx`. Thus solver `unsat` and a closed Lean theorem are distinct: the consumer must verify that all returned goals are closed and inspect final theorem axioms. Both `Reconstruct.Context.native` and `Config.native` default to `false` because native reconstruction components add compiled code execution to the trust boundary.
- **Isabelle SMT (`isabelle-prover/mirror-isabelle@39c77411f67871f5a8f06140c588e196a9aa9ca8`)**: In [`src/HOL/Tools/SMT/smt_solver.ML`](https://github.com/isabelle-prover/mirror-isabelle/blob/39c77411f67871f5a8f06140c588e196a9aa9ca8/src/HOL/Tools/SMT/smt_solver.ML) (`replay` lines 253–263, `add_solver` oracle registration lines 273–289; see also Blanchet et al., [*Hammering towards QED*](https://isabelle.in.tum.de/~blanchet/h4qed.pdf), §§3–4), the dispatcher runs proof replay when `smt_oracle` is `false` and invokes the registered oracle (asserting `False` in the translated context) when `smt_oracle` is `true`.

---

### 3. SMT Frame Diagnostics, Alethe Elaboration CLI Contracts, and Phase-Separated Checking Costs

`Basis: source + execution + derived`

1. **Direct `(not (= changed framed))` vs. `distinct` on `QF_AUFBV` Array Frame Obligations**:
   - Under the [SMT-LIB `ArraysEx` 2.7 specification](https://smt-lib.org/theories-ArraysEx.shtml) (`2024-07-21`), encoding an 8-bit array read-over-write outside-cell frame obligation with the direct premise `(not (= changed framed))` causes `cvc5 1.4.2` to emit `unsat` and a `281`-byte Alethe proof using `arrays_row` that Carcara accepts as `valid` (exit `0`).
   - Replacing `(not (= changed framed))` with the logically equivalent `(distinct changed framed)` causes `cvc5` to emit an additional rewrite step with rule `hole` and argument `untranslated rewrite`. Carcara ([`src/bin/cli/main.rs`](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/bin/cli/main.rs), `src/lib.rs:77-89`, `src/checker/mod.rs:380-407`) prints `holey` and exits with status `0`. A consumer checking only process exit code `0` would falsely accept an incomplete proof.
2. **Carcara `elaborate` Verdict-Prefix CLI Contract and Strict Rechecking**:
   - Carcara's `elaborate` subcommand checks the input proof, prints a 6-byte verdict line (`valid\n`) to stdout, and then prints the `265`-byte elaborated proof (with explicit resolution pivots). Passing the unstripped stdout directly to `carcara check` fails (`exit 1`, rejecting token `valid`). A narrow consumer reader must require exit `0`, verify and strip the `valid\n` prefix, require a non-empty proof payload, and re-invoke `carcara check --check-granularity elaborated` against the original SMT root.
3. **Separating Claim Mismatch, Invalid Proof Rules, and Concrete Counterexamples (`diagnostic_witness.rs`)**:
   - Attaching the valid frame proof to a problem missing the outside-cell premise fails (`exit 1`, unmatched assumption); mutating `arrays_row` to `refl` fails as a semantic rule error.
   - Without the outside-cell premise, `cvc5` returns `sat` with model `changed = framed = 255`, initial value `254`, and replacement `255`. `diagnostic_witness.rs` replays this exact witness on a concrete 256-byte safe Rust array (`254` before store, `255` after store), separating genuine source counterexamples (`binding.json`) from incomplete solver proof support (`holey`) or reader errors.
   - Across three samples on this obligation, median process-inclusive times were `5.65 ms` (`cvc5` generation), `2.95 ms` (initial Carcara check), `3.00 ms` (Carcara elaboration), and `2.87 ms` (strict `--check-granularity elaborated` recheck).

---

### 4. SAT, Pseudo-Boolean, and Bitvector Certificate Endpoints

#### 4.1 DRAT, LRAT, FRAT, and GRAT Proof-Checking Contracts

`Basis: normative + documentation + source + derived`

- **DRAT (`marijnheule/drat-trim@2e3b2dc0ecf938addbd779d42877b6ed69d9a985`)**: The [DRAT specification](https://github.com/marijnheule/drat-trim/blob/2e3b2dc0ecf938addbd779d42877b6ed69d9a985/README.md) requires each added clause to satisfy Resolution Asymmetric Tautology (RAT) on its first literal (or Reverse Unit Propagation, RUP/AT, as a special case), preserving satisfiability, while clause deletion weakens the working formula and preserves satisfying assignments.
- **Lean `CompactLRATChecker` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`)**: In [`CompactLRATChecker.lean`](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Std/Tactic/BVDecide/LRAT/Internal/CompactLRATChecker.lean) (`compactLratChecker.go`, lines 27–59), LRAT checking dispatches `addEmpty`, `addRup`, `addRat`, and deletion actions, succeeding only when `addEmpty` passes its RUP check.
- **FRAT (`digama0/frat@aa18581497830b49a6ab6cbc9e0dc778c14885b5`)**: In [`FRAT README`](https://github.com/digama0/frat/blob/aa18581497830b49a6ab6cbc9e0dc778c14885b5/README.md), FRAT elaboration can reconstruct missing hints and trim irrelevant steps before emitting a final LRAT proof checked against the original DIMACS input.
- **GRAT (`IsaFoL/IsaFoL@1475076cea603c64d3dfe70c91014a5264e0479b`)**: In [`Unsat_Check.thy`](https://github.com/IsaFoL/IsaFoL/blob/1475076cea603c64d3dfe70c91014a5264e0479b/GRAT/gratchk/Unsat_Check.thy) (RAT candidate checks lines 307–331, `export_code` from line 3098, `verify_unsat_impl_wrapper_correct` from line 3167) and [`Dimacs_Format.thy`](https://github.com/IsaFoL/IsaFoL/blob/1475076cea603c64d3dfe70c91014a5264e0479b/GRAT/gratchk/Dimacs_Format.thy), Imperative HOL separation-logic theorems establish that a non-error return from the verified checker wrapper implies `verify_unsat_spec` for the modeled input database.

#### 4.2 Lean `4.34.1` Bitvector Reflection (`unsat_of_verifyBVExpr_eq_true`) vs. `nativeEqTrue` and Empirical LRAT Probes

`Basis: source + execution`

- **Logical Soundness vs. Execution Policy**: In Lean `4.34.1`, [`Checker.lean`](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Std/Tactic/BVDecide/LRAT/Checker.lean) (`check` and `check_sound`, lines 30–47) and [`Reflect.lean`](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Std/Tactic/BVDecide/Reflect.lean) (`verifyCert`, `verifyCert_correct`, and `unsat_of_verifyBVExpr_eq_true`, lines 173–205) compose bitblast soundness, AIG relabeling equivalence, CNF equisatisfiability, and LRAT checking into a theorem about `BVLogicalExpr`. However, [`Bitblast.lean`](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean) (`LratCert.toReflectionProof`, lines 26–46) discharges `verifyBVExpr = true` via `nativeEqTrue` (`Lean.ofReduceBool`), placing native C evaluation in the theorem's axiom footprint.
- **Empirical `LratControls.lean` Probe**: On source clauses `x` and `¬x` with a one-step `addEmpty` certificate, Lean's checker accepts both hints `[1, 2]` and the shortened hint `[1]` because [`Formula/Implementation.lean`](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Std/Tactic/BVDecide/LRAT/Internal/Formula/Implementation.lean) (`ofArray` lines 78–95, `performRupCheck`/`performRupAdd` lines 208–238) preloads root unit assignments, making `[1]` sufficient to trigger conflict. When the formula is mutated to `x` and `¬y` with the same certificate, the checker returns `false`, and a kernel-reduced theorem (`changedSatWitness`, depending only on `propext`) proves that `x = true, y = false` satisfies the mutated formula (`LratControls.lean.first-failed` preserves the earlier blocked `decide` diagnostic).

#### 4.3 CakeML Verified x64 Executable Checkers and VeriPB Pseudo-Boolean Outcomes

`Basis: normative + source + derived`

- **CakeML LPR and Pseudo-Boolean Compilation Endpoints (`CakeML/cakeml@f73189499bb295f0859dec7ee38c169c48da682c`)**: In [`lpr_arrayProofScript.sml`](https://github.com/CakeML/cakeml/blob/f73189499bb295f0859dec7ee38c169c48da682c/examples/lpr_checker/array/compilation/proofs/lpr_arrayProofScript.sml) (lines 14–35, 86–118), `machine_code_sound` assumes `cake_lpr_run` (well-formed CLI/filesystem, standard streams/free file descriptor, and `installed_x64` checker code) and proves that printing `VERIFIED UNSAT` in 3-argument mode implies `unsatisfiable (interp fml)` (modulo resource-limit outcomes). Similarly, [`npbc_fullProofScript.sml`](https://github.com/CakeML/cakeml/blob/f73189499bb295f0859dec7ee38c169c48da682c/examples/pseudo_bool/array/compilation/proofs/npbc_fullProofScript.sml) (lines 60–99, over [`npbcScript.sml`](https://github.com/CakeML/cakeml/blob/f73189499bb295f0859dec7ee38c169c48da682c/examples/pseudo_bool/npbcScript.sml)) ties printed pseudo-Boolean conclusions to `pbc.sem_concl` and `pbc.sem_output`.
- **VeriPB Conclusion Taxonomy (`StephanGocht/VeriPB@01b7b5088c8a67f1611427174501191bc5f5b365` and Format Version 3)**: The [VeriPB version 3 overview](https://veripb.org/overview.html) separates `NONE`, `SAT`, `UNSAT`, and `BOUNDS` (requiring both a derived lower bound and a feasible upper-bound witness to certify optimality). In the historical Python checker ([`veripb/rules.py`](https://github.com/StephanGocht/VeriPB/blob/01b7b5088c8a67f1611427174501191bc5f5b365/veripb/rules.py) lines 364–426, 437+, 486+; [`veripb/verifier.py`](https://github.com/StephanGocht/VeriPB/blob/01b7b5088c8a67f1611427174501191bc5f5b365/veripb/verifier.py) lines 55–71), `OriginalSolution.compute` checks the original formula's constraints (unlike `Solution`), and `VerificationResult` can print `"Verification succeeded."` alongside warnings for unjustified assumptions or absent contradiction unless the semantic conclusion is inspected explicitly.

---

### 5. Exact and Rounded Numerical Proof Witnesses and Checking Paths (Farkas, SOS, FloVer, Gappa, Why3)

#### 5.1 Farkas Linear-Arithmetic and Sum-of-Squares (SOS) Host Proof Reconstruction

`Basis: source`

- **Farkas Witnesses (`mathlib4`, `Carcara`, `SMTCoq`)**:
  - In `leanprover-community/mathlib4@b16cf9ed26f2e49057943824f2f74f9783b7cb40`, [`Mathlib/Tactic/Linarith/Verification.lean`](https://github.com/leanprover-community/mathlib4/blob/b16cf9ed26f2e49057943824f2f74f9783b7cb40/Mathlib/Tactic/Linarith/Verification.lean) (`proveFalseByLinarith`, lines 179–255) queries an untrusted `CertificateOracle` for natural-number coefficients, constructs a weighted sum of hypothesis proof terms (plus `-1 < 0` and negated equalities), proves the sum equals `0` via a ring discharger and is strictly negative (`< 0`) via ordered-semiring lemmas, and derives `False` via `lt_irrefl`.
  - In `Carcara`, [`src/checker/rules/linear_arithmetic.rs`](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/rules/linear_arithmetic.rs) (`process_disequality` lines 215–326; `bounded_farkas` and `la_generic_partial` lines 338–392) normalizes rational combinations in Rust, while `SMTCoq`'s [`theories/checker/small-checkers/lia/LIA.v`](https://github.com/SMTCoq/smtcoq/blob/7b870140f2ff7e4547a7db614a305d8b2945afa3/theories/checker/small-checkers/lia/LIA.v) proves quotation-building soundness (`build_clause_correct`) in Coq.
- **Sum-of-Squares Reconstruction (`jrh13/hol-light@233b83c3202370e03c54de2bd090e4d34f677e91`)**:
  - In [`Examples/sos.ml`](https://github.com/jrh13/hol-light/blob/233b83c3202370e03c54de2bd090e4d34f677e91/Examples/sos.ml) (`REAL_SOS` from line 1311, rational recovery and exact polynomial subtraction check lines 1561–1598, `SOS_CONV` and `PURE_SOS_TAC` lines 1605–1638), `sumofsquares_general_symmetry` rationalizes a floating-point SDP vector, requires exact polynomial difference zero (else raising `Sanity`), proves polynomial equality via `REAL_POLY_CONV` + `TRANS`/`SYM`, and proves nonnegativity via real ordered-field inference (`PURE_SOS_TAC`).

#### 5.2 FloVer Finite-Precision Error-Bound Certificates (`FloVer@2b846b7242db7435c97ba694393db47842b19860` and FMCAD 2018)

`Basis: source + documentation`

- **Published FMCAD 2018 Theorems**: In the [FloVer FMCAD 2018 paper](https://www.cs.utexas.edu/~hunt/FMCAD/FMCAD18/papers/paper2.pdf), Theorem 1 (p. 5) relates a real expression and its finite-precision counterpart under a precondition, precision map, range map, and error bound; Theorem 2 (p. 6) specializes to `IEEE64` under the explicit premise `IEEEevalAvoidsSubnormals` (every subexpression evaluates to a normal number or zero) and excludes casts/mixed precision on the HOL4/CakeML route.
- **Current Upstream Rocq Endpoints (`2b846b7242db7435c97ba694393db47842b19860`)**:
  - `CertificateChecker.v`: `Certificate_checking_is_sound_general` and `Certificate_checking_is_sound` require a valid type map, a bounded-error `DeltaMap`, the real precondition, explicit SMT query unsatisfiability premises (`unsat_queries Qmap` and subdivision query maps), successful `ResultChecker`/`SubdivsChecker` execution, and `approxEnv` in the conclusion.
  - `SMTValidation.v`: `validSMTIntervalbounds_sound` retains SMT query unsatisfiability as an explicit hypothesis rather than discharging it inside the Boolean checker.
  - `IEEE_connection.v`: `IEEE_connection_expr` requires `is64BitEval`, `is64BitEnv`, `noDowncast` (rejecting casts), `eval_expr_valid` (finiteness and normal-or-zero side conditions), SMT query premises, precondition, and certificate success over Flocq `binary64`; `Inv` and `Fma` return `None`.

#### 5.3 Gappa Rocq Library and VM-Cast Plugin Boundary (`gappa/coq@e4f093c3f8fef4bb163e5b29c92d95514a4c9bdf`)

`Basis: source + documentation + derived`

- **Exact Dyadic Interval and Flocq Rounding Theorems**: In `Gappa_pred_bnd.v` (`constant2`), `Gappa_float.v` (wrapping Flocq's real-valued `Generic_fmt.round` for `rounding_fixed` and `rounding_float`; see also the [Gappa integration documentation](https://gappa.gitlabpages.inria.fr/gappa/tools.html)), and `Gappa_tactic.v`, Gappa models real-valued interval enclosures and rounding without by itself establishing NaN/infinity propagation, hardware instruction semantics, or finite exponent overflow.
- **Native Plugin VM Casts (`src/gappatac.c`)**: At `src/gappatac.c:793-817`, `call_gappa` invokes `gappa -Bcoq-lambda` and parses the returned proof term; at lines 830–843, `evars_to_vmcast` turns remaining proof obligations into reflexivity casts via `Constr.VMcast` and constructs the term with `refine_no_check`. While final kernel checking still validates the theorem, this path places Rocq's bytecode VM reduction engine inside the verification trust boundary.

#### 5.4 Why3 Task Transformations and Driver Output Regex Classification (`why3@d0a8072e157935d0d80a7a2156ecf5a98a2aae3e`)

`Basis: source + derived`

- **Unverified Task Transformations (`src/core/trans.ml`, `split_goal.ml`, `src/driver/driver.ml`)**: Why3 registers task transformations as ordinary OCaml functions (`trans.ml`, `split_goal.ml`) and applies driver-selected transformation pipelines (`driver.ml:prepare_task`, `drivers/z3.drv`)—including definition unfolding, inductive elimination, epsilon elimination, algebraic type encoding, and simplification—without emitting per-step equivalence certificates.
- **Regex Result Parsing (`drivers/smt-libv2.gen`, `call_provers.ml`, `drivers/coq.drv`)**: `drivers/smt-libv2.gen` maps solver stdout `unsat` to `Valid`, and `call_provers.ml` classifies regex/exit-code matches into `Valid`, `Unknown`, failure, or resource outcomes without checking a proof certificate. Even when `drivers/coq.drv` exports a Rocq obligation after preliminary transformations, checking the exported Rocq lemma does not automatically verify the preceding Why3 task transformations or Creusot source-to-Coma-to-VC lowering steps.

## Boundaries

- **Established for the executed byte-law, frame-diagnostic, and LRAT configurations**:
  - Exact fixed `ByteLaws.lean` and `roots/*.smt2` roots, all four complete translated `cvc5 1.4.2` Alethe certificates accepted by native `Carcara 1.1.0`, the narrowed-domain control, ten negative corruption/misbinding controls, and five finite countermodels checked in Lean `4.34.1` (`final-run/SolverWitnesses.lean`).
  - Phase-separated `cvc5 1.4.2` generation, `Carcara 1.1.0` checking, elaboration (`valid\n` prefix stripping), and `--check-granularity elaborated` rechecking on the `QF_AUFBV` outside-cell array frame obligation, plus the `distinct` `holey` (exit `0`) diagnostic and concrete Rust counterexample (`diagnostic_witness.rs`).
  - Lean `4.34.1` execution of `LratControls.lean` demonstrating unit-preloaded hint shortening (`[1, 2]` vs. `[1]`) and rejection of a reused certificate on a mutated satisfiable formula (`changedSatWitness`).
- **Known not to apply**:
  - Raw unexpanded `cvc5 1.4.2` Alethe exports for `byte_write`, `bool_validate`, and `array_validate` are rejected by native Carcara (`rare_rewrite` rules not found).
  - Carcara's `Valid` status does not certify all proof steps if `Config.allowed_rules` is non-empty, and process exit code `0` alone does not exclude `holey` proofs.
  - Lean `4.34.1`'s `LratCert.toReflectionProof` (`bv_decide`) invokes `nativeEqTrue` (`Lean.ofReduceBool`) rather than pure kernel reduction.
  - Real-number interval, Farkas, or SOS proofs do not certify IEEE 754 floating-point or modular machine-word arithmetic without an explicit rounding/overflow bridge (such as FloVer's `IEEE_connection_expr`, which itself excludes subnormals, downcasts, `Inv`, and `Fma`).
  - Why3's ordinary `Valid` status (`drivers/smt-libv2.gen`, `call_provers.ml`) is a regex classification of solver output over an unverified OCaml task-transformation pipeline, not a kernel-checked proof of the source obligation.
- **Not examined**:
  - Formal verification of the native `Carcara` or `cvc5` binaries, general `cvc5` `rare_rewrite` coverage beyond the five expanded rules, Rocq-to-Lean proof transport, fresh compilation/execution of SMTCoq, LFSC, DRAT-trim, FRAT, GRAT, CakeML, VeriPB Rust, HOL Light, Gappa, FloVer, or Why3, and whole-crate SMT/SAT scalability benchmarks.

## Evidence

- **Strict Alethe Expansion and Guarded Byte Laws (`byte-laws-strict-alethe-expansion-cvc5-carcara-2026`)**:
  - Primary fixtures and locks: `ByteLaws.lean`, `roots/*.smt2`, `root-locks.json`, `predicate-map.json`, `projection-only.alethe`, `tool-locks.json`, `INVARIANTS.md`, and `upstream-source-identity.json`.
  - Producers, validators, and execution logs: `translate.py`, `reconstruct.py`, `countermodels.py`, `replay.py`, `verify_preservation.py`, `translation-preservation.json`, `producer-boundary-control.json`, `countermodel-parser-control.json`, `final-run/results.json`, `final-run/SolverWitnesses.lean`, and `final-run/*.{alethe,json,stdout,stderr}`.
  - Carcara `20bf49c5ce31089ac83118574c888669355aaae1` rules inspected: [`src/checker/rules/arrays.rs`](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/rules/arrays.rs), [`src/checker/rules/simplification.rs`](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/rules/simplification.rs), [`src/checker/rules/extras.rs`](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/rules/extras.rs), [`src/checker/rules/congruence.rs`](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/rules/congruence.rs), and [`src/checker/mod.rs`](https://github.com/ufmg-smite/carcara/blob/20bf49c5ce31089ac83118574c888669355aaae1/src/checker/mod.rs).
- **SMT Frame Diagnostics and Elaboration (`smt-frame-diagnostics-elaboration-and-checking-costs`)**:
  - Preserved in `support/smt-frame-diagnostics-elaboration-and-checking-costs/` (and top-level `support/`): `support/measure.py`, `diagnostic_witness.rs`, `binding.json`, `downloads.json`, `build-observation.json`, `carcara-Cargo.lock`, and `artifact-identities.json`.
- **SMT, SAT/PB, and Numerical Certificate Audits**:
  - Preserved in `coverage.json`, `support/evidence.json`, `support/observations.json`, `support/sat-pb-and-bitvector-certificate-endpoints/`, `support/smt-certificates-reconstruction-and-root-binding/`, `support/exact-and-rounded-numerical-proof-witnesses/`, and `support/gappa-flover-and-why3-checking-paths/`.

## Revalidation

1. **Re-run the four guarded byte-law Alethe generation, expansion, Carcara checking, and Lean countermodel suite**:
   ```sh
   python3 -B replay.py --cvc5 "$CVC5" --carcara "$CARCARA" --lean "$LEAN" --output "$OUT" --samples 3
   python3 -B verify_preservation.py --original final-run/bool_validate.0.raw.alethe --translated final-run/bool_validate.0.translated.alethe
   ```
   Require `valid\n` with exit code `0` on all four expanded whole-law roots, rejection on all ten negative controls, and exit code `0` with zero `sorryAx` on `final-run/SolverWitnesses.lean`.
2. **Re-run the `QF_AUFBV` frame elaboration, verdict-prefix stripping, `distinct` holey diagnostic, and safe Rust counterexample witness**:
   ```sh
   python3 support/measure.py "$CARCARA" "$CVC5" "$OUT_FRAME"
   ```
   Verify that `(not (= changed framed))` passes both raw check and `--check-granularity elaborated` recheck, `(distinct changed framed)` is rejected by the consumer as `holey` despite exit `0`, and `diagnostic_witness.rs` reproduces the `254 -> 255` aliasing store witness.
3. **Re-verify the Lean `4.34.1` LRAT binding probe and upstream source coordinates**:
   - Run `lean support/LratControls.lean` with Lean `4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) and confirm that `changedSatWitness` depends only on `propext` while the checker equality theorems expose `Lean.ofReduceBool`.
   - Diff the pinned upstream source coordinates recorded in `support/evidence.json` and `upstream-source-identity.json` before changing any solver, elaborator, or checker version pin.
