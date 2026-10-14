# A native checker generated from a proved Lean 4.31 logical definition

## Summary

A proved data-only correspondence checker was compiled through Lean 4.31's C backend and `leanc` into a runnable macOS aarch64 executable. It accepted the consumer-selected arithmetic program, rejected nine invalid/different inputs, and passed a 2,000-input acceptance/rejection batch. Kernel replay proved the same validator's generic soundness and its selected positive and typed negative cases.

This establishes an actual logical-source-to-native experiment and measured integration costs. It does not establish a proof-produced binary: the Lean C/native compiler, linker, runtime, parser, and IO remain trusted. Running the native executable instead of the kernel adds that artifact bridge to the acceptance TCB unless a separate verified code-generation theorem is supplied.

## Applicability

The compiler/checker environment is Lean 4.31.0 revision `68218e876d2a38b1985b8590fff244a83c321783`, on macOS 27.0.1 arm64. `tool-identities.json` pins `lean`, `leanc`, bundled clang/linker, logical/runtime archives, host observation, and produced executable. The actual executable SHA-256 is `78e73da1f985cf584b7e3c443d06c820ffefe33d2adf5bc59e53f78ad295b173`. The package preserves its generated C and all logical source; the binary itself remains a reproducible intermediate, rather than a published platform artifact.

The source model reuses the report-owned arithmetic prototype, adapting only module/export headers needed for independent compilation/import reduction in Lean 4.31. It is separate from the companion Charon/Aeneas pair specimens. No Rust-to-this-DSL import claim is made. The independently selected logical source is fixed in the executable:

```text
Byte = Fin 256
selectedSource(x) = (((x wrapping_add 3) wrapping_mul 5) wrapping_add 7)
property = equality of source and candidate IR evaluations for every Byte input
```

The input is a JSON encoding of an IR tree; producer input does not select the source/property/domain, import proof code, or declare a successfully run stage. Consumer-owned logical definitions and source selection determine the challenge. The standard library imports and compiled modules remain part of the execution/checking environment.

## Findings

Basis: source + execution + derived.

`ArithmeticModel.lean` defines source trees, IR trees, wrapping byte operations, evaluators, and `decode : IR → Source`. `decode_eval` proves that decoding preserves evaluation by structural induction. `checkPosthoc s p = decide (decode p = s)` is sound:

```lean
checkPosthoc s p = true → ∀ x : Byte, evalIR p x = evalSource s x
```

`CheckerMain.lean` fixes the selected source and exposes `validate`; its `validate_sound` specializes that generic theorem. `KernelReplay.lean` confirms actual assumptions `[propext]` for the generic/specialized soundness theorems, accepted selected IR, and rejected changed-op/literal cases. There is no `sorryAx`, `Lean.ofReduceBool`, or added producer axiom in those endpoints. The selected proof derives the same all-byte evaluation equality, rather than a proof of a caller-selected weaker predicate.

The checker compares decoded structure, not arbitrary extensional equivalence. Semantically equivalent reordered/reassociated programs can be rejected; that is an intentional incompleteness of this cheap certificate language. Soundness holds for all IR trees at the logical function boundary, including nested operators and byte literals.

The executable parser recognizes exactly four array forms:

```json
["param"]
["imm", 7]
["add", ["param"], ["imm", 3]]
["mul", ["param"], ["imm", 5]]
```

Literal values must be natural numbers below 256; constructor arities and names must match. Recursive parsing consumes a fuel budget of 32 and rejects deeper trees. Its JSON, parsing/IO, EOF loop, and error-string behavior are ordinary executable code without a parser-correctness theorem. An accepted parsed `IR` has the proved logical guarantee, conditional on the native artifact faithfully implementing those definitions and accepting the intended input bytes.

The actual build invokes `lean -o ... -c ... ArithmeticModel.lean` and similarly for `CheckerMain.lean`, then `leanc -O2 -o checker ArithmeticModel.c CheckerMain.c`, with working directory set to the copied support module root. This matters: an initial build with full filesystem module names produced a linker error for `runtime_initialize_ArithmeticModel`; compiling from the proper module root resolved it without changing checker semantics. A missing `/usr/local/lib` search-directory warning remained nonfatal. Neither issue was an unsupported semantic input or a kernel acceptance.

`otool -L` lists system `libc++` and `libSystem` dependencies for the produced binary. Exact provided Lean runtime/archive identities are retained. The binary therefore relies on native compiler/runtime/OS behavior even though the Boolean validator has a logical soundness theorem. No compiler theorem in this experiment relates its machine code or IO interpretation to Lean evaluation.

Ten actual standalone fixtures produced one accept and nine rejects: exact selected IR; changed outer operation; changed byte literal; out-of-range/negative literals; missing operand; unsupported call-like node; wrong-subject envelope; truncated JSON; depth excess. Parser errors were distinct from well-formed candidate rejections. All processes exited 0 with verdicts, without panic; rejection is data, not a misleading producer-success label. The full fixture inputs, expected verdicts, outputs/statuses, and batch output are preserved.

Seven fresh-process single-input samples, after the first launch with warm OS/filesystem caches, had median wall times 21.763 ms for native JSON input/check/output and 480.933 ms for Lean elaboration/import/kernel replay of one selected acceptance proposition. The first native fixture process took 1.013 s, so startup/cache state materially affects these observations. One process checked 2,000 alternating valid/changed-op inputs in 25.353 ms, producing exactly 1,000 accepts and 1,000 rejects. These timings compare concrete operational routes: the kernel route includes elaboration and proof validation; the native route includes parser/IO/runtime startup. They are seven samples on one host, not solver benchmarks or a general checker-performance ratio. Concurrent fresh-scratch revalidation also passed and is recorded separately.

For Anneal, this suggests a concrete split: a small proved data checker can avoid re-elaborating large candidate-generated proof programs for supported grammar, while general kernel replay can validate richer proofs without trusting a new compiled checker bridge. A consumer can retain kernel replay as authority and use the native result as a fast precheck. Making native acceptance authoritative requires an explicit compiler/runtime/parser trust policy or a verified derivation endpoint; faster observations alone do not reduce those assumptions.

## Boundaries

- **Known not to establish:** proof-producing compilation, machine-code equivalence, verified parser/IO, OS isolation, or arbitrary Rust/Charon/Aeneas source adequacy. Same-user private scratch paths do not provide sandboxing.
- **Not examined:** an available verified Lean/native code-generation tool, proof-produced native binary, broad certificate languages, adversarial resource/OS containment, or representative large proof costs. The experiment installs no additional tool.
- **Unsupported by the executable input grammar:** alternate source/property/domain/configuration envelopes, calls, variable references beyond the parameter, and tree depth above 32. Logical soundness of the checker does not itself prove that malformed external data reaches the intended IR.

P120 has a completed bounded exploration of deriving and executing a checker from verified logical definitions with a named artifact bridge. T112 has a concrete comparison of the proved logical validator/native execution route with kernel replay; the compiled validator's missing machine-code proof remains explicit. P136 remains partial because the requested *proof-produced executable* was not available or exercised. Future implementation of a verified bridge is distinct from the completed observations above. Exact scopes appear in `support/coverage.json`.

## Evidence

The package preserves all Lean source/proofs, generated C, exact tool and binary hashes, compiler/linker outputs, fixtures, all verdict/batch output, statuses, timings, dependency inspection, and fresh-scratch reproduction results. `SingleReplay.lean` states the consumer-selected positive proposition; `KernelReplay.lean` preserves the assumption interface and typed negative propositions. All evidence was observed on 2026-10-14. The published evidence contains source and generated C; the platform binary remains a reproducible intermediate.

## Revalidation

Run `python3 -B support/revalidate.py --lean-root /path/to/lean-4.31 --out /new/task/scratch`. It compiles copied logical modules, checks kernel replay, regenerates C, links a new native checker, and checks all fixture verdicts. It writes only the new scratch. Compare source/property/domain constants, theorem assumptions, generated C/tool identities, parser behavior, and exit/verdict distinctions. A new native artifact needs a new bridge assessment even when the logical proof is unchanged.

*Authored by an AI agent acting on joshlf's behalf.*
