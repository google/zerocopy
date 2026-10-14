# Current Gappa, FloVer and Why3 checking paths

## Summary

These paths remove different trusted computations. Gappa reconstructs a Rocq term and uses VM casts for computational obligations. FloVer's inspected soundness theorem composes numerical validators but retains explicit unsatisfiability premises for SMT queries. Why3's ordinary prover path transforms and prints tasks, then interprets prover output through driver rules; a `Valid` result is not inherently a kernel proof of the original source claim.

## Applicability

Official repository metadata was resolved on 2026-10-14: Gappa support library `e4f093c3f8fef4bb163e5b29c92d95514a4c9bdf`; FloVer default branch `2b846b7242db7435c97ba694393db47842b19860` (last commit 2022); Why3 `d0a8072e157935d0d80a7a2156ecf5a98a2aae3e`. FloVer source was fetched through the mirror carrying that same upstream commit after its raw web endpoint returned HTTP 429. An official Gappa 1.11.0 source archive was also hash-verified; current-library findings below concern the later exact repository pin.

No Gappa, Rocq, FloVer or Why3 installation/build/run is claimed. Current source inspection is not continuity from the earlier FMCAD 2018 paper or a claim that the current Creusot checkout executes this exact Why3 revision.

## Findings

### Gappa checks exact numerical propositions through generated terms

Basis: **source**.

Current `Gappa_pred_bnd.v:constant2` proves that successful exact dyadic endpoint comparisons imply the real interval predicate `BND`. Other interval rules compose these arithmetic facts. `Gappa_float.v` defines rounding through Flocq's real-valued `Generic_fmt.round` with specified exponent and precision functions. These are real rounding models; NaN, infinity, target floating-point instructions and finite exponent overflow do not follow simply from a real-number interval theorem.

`Gappa_tactic.v` defines reflected expressions/trees, their interpretation and normalization/transformation correctness theorems. Its tactic prepares a quoted goal and invokes the native plugin. This supplies an explicit quotation/interpretation interface, but its implementation and exact original-goal attachment still need the assistant's final checking contract.

### The plugin's VM casts are a separate execution boundary

Basis: **source**, **derived** trust accounting.

At `src/gappatac.c:793–817`, `call_gappa` invokes `gappa -Bcoq-lambda`, checks its exit status, parses a returned term and removes temporary files. At 830–843, `evars_to_vmcast` turns remaining proof evars into casts of reflexivity using `Constr.VMcast`. `gappa_internal` then builds the term and uses `refine_no_check`; quotation similarly uses a no-check conversion operation.

These operations defer checking; their names are not evidence that final Rocq checking is bypassed. They also show why this path must not be summarized as only pure kernel reduction of exact arithmetic: the chosen Rocq VM-conversion path and final proof validation are material. A generated script/term can avoid trusting Gappa's numerical search when checked under the intended theorem, permitted assumptions and enabled checking configuration. This report did not execute the plugin or audit the current Rocq VM implementation.

### FloVer's current theorem exposes its SMT and environment premises

Basis: **source**.

`CertificateChecker.v` obtains a valid type map, then selects `ResultChecker` or `SubdivsChecker`. `Certificate_checking_is_sound_general` and the specialized `Certificate_checking_is_sound` require a bounded-error `DeltaMap`, the real precondition, `unsat_queries Qmap`, unsatisfiability of query maps used by subdivisions, and successful checking. The conclusion additionally requires `approxEnv` before relating real and finite-precision evaluations and their error bound.

`SMTValidation.v` only uses query-provided interval tightening when precondition and expression checks match; its `validSMTIntervalbounds_sound` retains unsatisfiability as a premise. This version does not discharge that premise merely by receiving a Boolean certificate-checker success. An independent solver-proof path or separately checked arithmetic argument must supply it; an empty query map may make a particular premise trivial, but this was not instantiated here.

### The IEEE64 endpoint still has explicit unsupported cases

Basis: **source**.

`IEEE_connection.v:IEEE_connection_expr` requires `is64BitEval`, `is64BitEnv`, `noDowncast`, `eval_expr_valid`, SMT-query premises, precondition and certificate success. Its finite evaluation supports the defined arithmetic operations and lets; `Inv` and `Fma` return `None`. `noDowncast` rejects casts. `eval_expr_valid` uses finiteness checks for constants and normal-or-zero real arithmetic side conditions for binary expressions; the FMA validity branch explicitly lacks support. The resulting relation uses Flocq binary64, not an arbitrary mixed-precision host execution.

These source definitions refine the older paper-level limitation with actual current endpoints. They do not prove a new theorem about the analyzer, C/Rust arithmetic, compiler contraction of multiply-add, subnormal-flush modes or a supplied executable checker binary.

### Why3's transformation API does not require a proof certificate

Basis: **source**.

Official `src/core/trans.ml` defines transformations as OCaml functions on tasks and registers them in a lookup table. The ordinary API accepts a transform or task list, without requiring a companion semantic theorem or proof term. `split_goal.ml` builds and registers concrete goal-splitting transformations. Their soundness depends on those implementations and the semantics of generated tasks; absence of a certificate field is not evidence that no transformation has ever been proved elsewhere.

`src/driver/driver.ml:prepare_task` updates tasks and applies the driver's ordered transformation list before printing. `drivers/z3.drv` chooses SMT-LIB printing and a pipeline including definitions, inductives, epsilon, algebraic types, simplification and SMT encoding. Consequently, checking a proof of the printed formula must still connect that formula to the pre-transformation task.

### Result classification and interactive export have different contracts

Basis: **source**, **derived**.

`drivers/smt-libv2.gen` maps an `unsat` output line to `Valid`. `call_provers.ml` analyzes driver-configured regular expressions/exit results into `Valid`, `Unknown`, failure and resource outcomes. This ordinary result parser is not a proof checker. Solver proof-production/reconstruction may be added by a different configured route; it cannot be inferred from the status alone.

`drivers/coq.drv` prints Rocq material after its own preliminary transforms. Checking the emitted theorem can remove trust in that proof search, while leaving task generation, transformation, encoding and source-specification meaning to justify. For Creusot, the previously inspected Coma/MIR/session boundaries remain distinct: source-to-Coma and Coma-to-VC adequacy do not become kernel checked because a Why3 session replays successfully.

For Anneal, retain the original numerical expression/program claim, rounding/exceptions/domain policy, all range/query witnesses, exact transformed task and the consumer's theorem connecting them. Choose explicitly between trusted solver status, reconstructed proof, reflected checker, and VM/native computation. The completed comparison identifies these boundaries; building an adapter is future engineering.

## Boundaries

**Not examined:** executing numerical witnesses, full imported arithmetic-library assumptions, current Rocq VM correctness, every Why3 transformation/driver, or the combined current Creusot/Why3 build. **Unknown:** the cheapest complete certificate path for a representative Anneal floating-point obligation. No success result for an unsupported FMA/cast/exception case is manufactured.

## Evidence

support/evidence.json records exact repositories/commits/paths, inspected symbols, normalized-text hashes and the Gappa archive SHA-512. Source inspection and primary theorem endpoints support the claims; there are no numerical execution results in this package.

## Revalidation

Diff FloVer's checker theorem premises together with its concrete IEEE evaluator, query map interpretation and environment relation. Inspect Gappa's quotation, returned-term parser and VM cast construction under the chosen Rocq checking mode. Trace the exact Why3 driver list through printing to result classification, and require separate correspondence for any replacement transformed task or solver-proof consumer.

*Authored by an AI agent acting on joshlf's behalf.*
