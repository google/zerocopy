# Lean 4.34.1 admissions, native computation, and compiled imports

## Summary

Six bounded commands distinguish Lean theorem validity, axiom dependencies, checking configuration, executable computation, and imported-artifact freshness. Ordinary kernel checking rejected a proof body of the wrong type. With `debug.skipKernelTC` enabled, the same declaration was accepted and its axiom audit was empty. A native proof using an `implemented_by` substitution depended on a generated native-evaluation axiom, while its kernel-reduced counterpart did not. A consumer imported the previously compiled producer after the producer's source changed.

These observations show why “no reported axioms,” “Lean exited successfully,” and “the source file is current” are different claims. They are exact Lean 4.34.1 fixture results; they do not establish behavior for Anneal's 4.31 pin or a production acceptance service.

## Applicability

The executed binary reports Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, Release, target `arm64-apple-darwin24.6.0`. Its SHA-256 is retained in `support/observations.json` and the subject metadata. The host was Darwin 27.0.0 arm64. Each command used fixture-local `LEAN_PATH`, a fixture-local working directory, and a 30-second timeout. Commands called the installed binary directly; no new package, dependency, or toolchain was installed.

The fixtures are authored data in owned scratch. The bypass fixture deliberately invokes the documented checking-disabled path to create an invalid declaration; it is not presented as a soundness defect in the ordinary checked path. The stale-source fixture compiles `Producer.lean` once, changes its source without rebuilding, and imports the retained artifact. No malformed binary artifact, unowned file, external network effect, or concurrent writer was involved.

Directly inspected primary source is the same Lean commit. The earlier corpus package about 4.30.0-rc2 supplied narrow research leads; this report reexamines the relevant 4.34.1 definitions and adds fresh execution evidence rather than assuming version continuity.

## Findings

### A clean axiom set describes global logical dependencies, not the entire proposition

The `logical-and-assumed` command exited 0. `ordinary`, proved by `decide`, and `localHyp`, whose statement takes a `False` hypothesis and returns `False`, both had empty axiom lists. `viaHelper` depended on `assumedFalse`, even though the assumption was reached through a private helper.

`localHyp` proves an implication under a local argument; it is not a closed proof of `False`. Its empty axiom list is therefore expected. This control distinguishes local premises from global axiom declarations and demonstrates that an audit must inspect the full expected theorem type as well as its global assumptions.

The source collector looks up declarations in the checked environment, traverses declaration types and available bodies, and records `.axiomInfo` dependencies. Imported declarations can use precomputed axiom sets stored in an environment extension. Those cached summaries are themselves interpreted as imported artifact data; the collector does not independently replay every imported proof body.

Basis: **execution**, `support/probes/logical-and-assumed.lean` and its stdout; **source**, `Lean/Util/CollectAxioms.lean`, `collect`, `exportedAxiomsExt`, `collectAxioms`; **derived** proposition/dependency distinction.

### Logical reduction and native evaluation can observe different implementations

The native fixture defines a logical Boolean function returning `false` and marks a function returning `true` as its compiled implementation using `implemented_by`. The kernel-reduced theorem `logicalResult` proves the logical function equals `false` and reports no axioms. `nativeResult`, proved by `native_decide`, states that the same function equals `true`; it is accepted with dependency `nativeResult._native.native_decide.ax_1_1`.

This is a controlled witness that the logical definition and compiled implementation are separate subjects. The native path is visibly conditional on its introduced computation assumption. The fixture does not show that kernel reduction derives contradictory statements without assumptions.

`Lean.Meta.nativeEqTrue` compiles and evaluates a closed Boolean expression, checks that execution returns `true`, then introduces a non-unsafe axiom stating that the expression equals `true`. The returned proof references that new axiom. Kernel acceptance of this final term does not independently justify the preceding compiler/runtime computation.

Basis: **execution**, `support/probes/native-implementation.lean` and stdout; **source**, `Lean/Meta/Native.lean`, `nativeEqTrue`; **derived** separation of logical and compiled behavior.

### Checking configuration is independent from the axiom audit

`checked-rejection` constructs a core theorem declaration named `forged`, gives it type `False`, and supplies `True.intro` as its body. Ordinary insertion exited 1 with a kernel declaration-type mismatch. `kernel-bypass` performs the same insertion after enabling `debug.skipKernelTC`; it exited 0, printed a theorem of type `False` with body `True.intro`, and reported an empty axiom list.

`Lean/AddDecl.lean` dispatches the checking-disabled option to `addDeclWithoutChecking`; the corresponding C++ entry inserts a declaration with the check flag disabled. The collector records axioms in the resulting expression graph, not a certificate that the declaration traversed a sound checking configuration. The bypass result therefore cannot satisfy a consumer promise of kernel-checked proof validity simply because the audit is empty.

Basis: **execution**, `support/probes/checked-rejection.lean`, `kernel-bypass.lean`, and their stdout; **source**, `Lean/AddDecl.lean`, `Kernel.Environment.addDecl`; `src/kernel/environment.cpp`, `lean_add_decl_without_checking`; **derived** acceptance-policy consequence.

### An ordinary import follows the compiled artifact in this fixture

`compile-producer` compiled a producer whose `exportedFalse` theorem depends on `oldAssumption`. The harness then replaced the producer's source with a version using `newAssumption`, without compiling again. `stale-source-import` imported the retained `Producer.olean` and reported `oldAssumption` as the theorem's dependency. Both commands exited 0.

This isolates artifact freshness from logical dependency reporting: the imported theorem can faithfully report the dependency of the selected compiled artifact while that artifact no longer describes the visible source file. The result concerns a direct Lean invocation; it does not establish that Lake, editor orchestration, or every configured build system misses such changes.

Basis: **execution**, the two producer specimens, final `Producer.lean`, retained `Producer.olean`, `Consumer.lean`, and observations; **derived** scope of the freshness control.

### Artifact loading, environment initialization, and fresh proof replay have different contracts

The inspected `readModuleDataParts` reads compacted module data through unsafe runtime operations. `finalizeImport` constructs constant maps from this data, checks import conflicts, and initializes environment state; this function does not call the theorem insertion check once per imported proof. `importModules` can load plugins; loading environment extensions can invoke interpreted initialization code when enabled.

This does not classify ordinary `.olean` files as incorrect. It identifies the imported environment, parser/loader, initialization, runtime memory, and artifact-selection path that a consumer relies on. A data-only export followed by fresh checker replay can move the proof-validity boundary, but the export's statement identity, serialization, primitive definitions, assumption policy, and exact subject still require checks. The companion authority report directly audits one such comparator path without executing it.

Basis: **source**, `Lean/Environment.lean`, `readModuleDataParts`, `finalizeImport`, `importModules`; **derived** comparison with fresh logical replay.

### Native trust reduction requires an executed checking theorem, not a label

There are three distinct ways to establish a computational conclusion. Kernel reduction can check a proof term using the logical definitions. Reflection can reduce an executable decision procedure whose soundness theorem connects its result to the proposition, while quotation and input identity remain obligations. A separately verified executable checker additionally requires a justified extraction/compilation/runtime path. The observed native mechanism instead introduces an assumption after compiled execution.

The probe supplies a discriminator between the first and last routes. The companion verified-checker report identifies concrete conditional checking/erasure theorem endpoints; neither package establishes a verified native replacement for Anneal or benchmarks the routes. These distinctions allow a consumer to state an explicit native-computation policy without confusing an allowed assumption with a discharged obligation.

Basis: **source** + **execution** for the observed kernel/native paths; **derived** conditional interface requirements; companion package for the specific checker/erasure theorem endpoints.

## Boundaries

- **Exact version only:** no execution or source audit of Anneal's selected Lean 4.31, and no inferred continuity from 4.30.0-rc2 or to later releases.
- **Not established:** correctness of Lean's kernel, compiler, garbage collector, FFI, filesystem loader, OS, or hardware. Source inspection and this six-command suite are not a verification of those components.
- **Not examined:** every admission/escape hatch, malformed `.olean` loading, adversarial parser behavior, native extension injection, independent kernel diversity, concurrent imports, or complete environment-policy enforcement.
- **The native result has an explicit extra assumption.** It is not evidence of contradictory ordinary kernel derivations without axioms.
- **The bypass result is deliberate.** It confirms the documented disabled-check path and cannot be interpreted as an unexpected failure of enabled checking.
- **The stale import used direct Lean.** Build-system freshness behavior and correspondence to source capture remain separate obligations.
- **Not established:** Rust-to-Lean correspondence, completeness of mandatory obligations, consumer-selected proposition identity, or an aggregate Anneal acceptance theorem.
- Run durations record this fixture execution only. They are not comparative performance measurements.

## Evidence

- `support/observations.json` records binary identity, host, exact arguments, exits, durations, output, and fixture/artifact hashes.
- `support/probes/` retains all six command inputs, stdout/stderr, the two producer sources, final changed source, consumer, and compiled producer artifact.
- `support/run-probes.py` recreates the same sequence using an explicitly supplied Lean binary. It writes only its adjacent fixture directory and observations.
- [Lean native evaluation](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Meta/Native.lean), `nativeEqTrue`.
- [Lean axiom collection](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Util/CollectAxioms.lean), `collect`, imported extension entries, `collectAxioms`.
- [Lean insertion dispatch](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/AddDecl.lean#L22) and [checking-disabled entry](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/kernel/environment.cpp#L297).
- [Lean module and environment loading](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Lean/Environment.lean), `readModuleDataParts`, `finalizeImport`, `importModules`.
- `support/source-index.json` binds the inspected primary sources to immutable revision and retrieved-content hashes.

Execution evidence was acquired on 2026-10-14. The successful/failed controls were inspected individually; no result relies on a producer's success string without its command exit and specific output.

## Revalidation

Invoke `python3 -B support/run-probes.py --lean /absolute/path/to/selected/lean` in a disposable copy of this package. Check that ordinary and native axiom sets differ, the enabled-check control rejects, the disabled-check control accepts only as deliberately untrusted evidence, and the stale import retains the old compiled dependency. Inspect outputs, not just exits.

For an acceptance service, additionally pin the checking options and independently selected theorem/definition identities, re-establish all imported artifact families, and either trust the loader/build closure explicitly or replay a validated export in a fresh checker. These fixture controls do not discharge the remaining correspondence, serialization, or runtime obligations.

*Authored by an AI agent acting on joshlf's behalf.*
