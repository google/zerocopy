# Actual Coq replay of modular effects, HeapLang and Islaris adequacy

## Summary

A fresh build of the selected **Program Logics à la Carte v2 artifact** passed, followed by observation-only audits of 25 actual result constants and a recursive native `coqchk` of 542 libraries. This checks proof objects freshly compiled from the actual artifact sources and their imported dependency closure, rather than an owned replacement model. The selected results split into six closed under the global context, three using strong-bisimulation equality, twelve additionally using UIP, and four additionally using functional choice.

The checked results retain their explicit handler, interpretation, WP, state/resource and execution premises. They do not instantiate MiniRust's coupled byte/provenance/alias/race semantics or establish a Rust frontend, machine-code or safe-client theorem. This completes the selected modular-artifact replay slice of milestone E03; E03's other Rust-logic and ISA artifact replays remain separate work.

*Authored by an AI agent acting on joshlf's behalf.*

## Applicability

The subject is [Zenodo artifact 14180355, v2](https://zenodo.org/records/14180355), specifically the 1,480,438-byte `the_artifact.zip` with SHA256 `bf5d86d5fef425b6031640391dddda4f60b3b029d680019ddaedefd17e4d3378`. All 476 regular source files, totalling 5,420,269 bytes, matched that archive before execution and after execution. The archive contains no prebuilt Coq proof objects. Its 51-file `iris-itree` subtree is the actual source compiled here; vendored stdpp and Iris supplied the installed dependencies. The complete archive is preserved in [support/the_artifact.zip](support/the_artifact.zip).

Execution used Linux arm64, Coq 8.19.2, OCaml 4.14.4, ITree 5.1.2, Paco 4.2.1, coq-elpi 2.2.3, coq-ext-lib 0.13.2 and coq-record-update 0.3.6. Dune 3.17.2 was installed. The exact archive stdpp/bitvector/unstable and Iris/HeapLang trees were installed by the parent before this run, without substituting current development versions. The package manager labels these vendored packages `dev`; their immutable source identity is the archive and its file manifest, not that label. The archive's stdpp and Iris subtree manifest hashes are respectively `39a9f21debfea2d9a92f9198ed35338b7ad0dfa2c2267b1c623373ffda333335` and `1628dd123871e6d6aa6f2efa5be7433b1f4bf672faaa072e3d15a8a63a319a4e`.

The isolated container had two CPUs and a 3 GiB memory limit. Builds used one Coq worker and the original `_CoqProject` flags, including `-Q src iris.itree` and `-Q islaris isla`. The generated Makefile selected Coq's `-native-compiler no`; no upstream source was changed. Three owned annotation files contain only imports, printing configuration, `Check` and `Print Assumptions`. They add no definitions, axioms or proofs. The dependency-object hash manifest binds the exact installed objects actually loaded during checking; this report does not independently reconstruct their package-manager provenance from upstream release source.

## Findings

### 1. Fresh proof objects and recursive checking both passed

Basis: source + execution.

The build requested these nine original seed targets, letting the generated dependency graph select their closure:

- `src/exec.vo`, `src/heap.vo`, `src/threadpool/exec.vo`, `src/threadpool/interleaving.vo`, `src/examplelang/adequacy.vo`;
- `src/heaplang/adequacy.vo`, `src/heaplang/opsem_adequacy.vo`;
- `islaris/adequacy.vo`, `islaris/adequacy_itree.vo`.

This produced 38 original `.vo` files and three audit `.vo` files. Native `coqchk` then recursively checked the nine seed modules, the three audits and their imports. The command used `-o -m`, with **no `-admit` or `-norec` bypass**. Its trace records exactly 542 loaded objects and 542 checked libraries, exit 0, and `Modules were successfully checked`.

The checker reports predicative `Set`, no constants or inductives relying on type-in-type, no unsafe (co)fixpoints, and no inductives with assumed positivity. Its global context lists 62 axiom or primitive declarations from imported modules, including standard classical declarations, Coq integer/float primitives and ITree declarations. That global import context is broader than the dependencies of an individual selected proof. It must not be replaced by a claim that the whole loaded environment has only three axioms. Conversely, declarations merely present in that context must not be attributed to every selected theorem. The complete context is in [support/kernel-context.json](support/kernel-context.json).

| Phase | Exit | Elapsed seconds |
| --- | ---: | ---: |
| Core, state/heap, threadpool and ExampleLang build | 0 | 68.383 |
| Core annotation audit | 0 | 8.129 |
| HeapLang and operational bridge build | 0 | 44.292 |
| HeapLang annotation audit | 0 | 8.117 |
| Original and ITree Islaris build | 0 | 46.262 |
| Islaris annotation audit | 0 | 4.095 |
| Recursive native checker | 0 | 60.373 |

The final task directory held 21,891,326 apparent bytes according to `du -sb`; the copied regular-file payload was 21,885,246 bytes in 264 files. The checker printed `total heap size = 576280 kbytes`; this is its own heap statistic, not a measured peak resident-set value. No phase reached its time or disk cap. All copied files match the final container hash inventory.

### 2. Actual per-constant assumptions differ at important interfaces

Basis: execution; full types and complete `Print Assumptions` output.

Let **B** denote `ITree.Eq.EqAxiom.bisimulation_is_eq`, which identifies *strongly* bisimilar ITrees; **U** denote the artifact's `iris.itree.axioms.Ax.eq_rect_eq` UIP-related axiom; and **C** denote `iris.itree.axioms.AxChoice`, functional choice. The three axiom statements themselves were also printed. No selected result reported an additional declared axiom.

The following names are fully qualified in [support/actual-assumptions.json](support/actual-assumptions.json). Short names below are grouped by their source module.

| Actual result constants | Reported assumptions |
| --- | --- |
| `exec.handler_adequate_from_simple`, `exec.sumEH_adequate`, `exec.sumSEH_adequate` | Closed under the global context |
| `state.stateEH_adequate`, `threadpool.exec.threadpoolEH_adequate` | Closed under the global context |
| `heap.wpi_load`, `heap.wpi_store`, `heap.wpi_allocN` | B |
| `exec.wpi_adequate`, `exec.wpi_adequate_pure` | U, B |
| `state.state_adequacy`, `heap.heap_adequacy` | U, B |
| `threadpool.interleaving.threadpool_adequacy`, `examplelang.adequacy.wp_adequacy_irel` | U, B |
| `heaplang.adequacy.wp_adequacy_irel`, `wp_adequacy_eval`, `wp_partial_soundness`, `wp_total_soundness` | U, B |
| `heaplang.opsem_adequacy.execution_from_opsem_trace`, `partially_adequate_opsem_adequate`, `wp_later_opsem_adequate`, `wp_total_opsem_adequate` | U, B, C |
| `isla.adequacy.isla_adequacy` | Closed under the global context |
| `isla.adequacy_itree.isla_exec_adequate`, `isla.adequacy_itree.isla_adequacy` | U, B |

“Closed under the global context” concerns declared axiom dependencies of that proof term. Ordinary quantified premises, typeclass parameters and resource hypotheses still constrain its use. The operational HeapLang bridge's extra functional-choice dependency and the difference between the original and ITree Islaris proofs are observed dependency differences, not judgments about relative implementation trustworthiness.

### 3. Handler composition preserves established component contracts

Basis: source + actual theorem types + checked proofs.

`src/exec.v:555` converts an already established `seHandlerAdequate H EH` into `eHandlerAdequate H EH`. `sumEH_adequate` at line 805 and `sumSEH_adequate` at line 882 require adequacy of each component and conclude adequacy of the sum handler. Their invariants retain the separate component structure. Their checked proof terms being closed does not discharge the input adequacy instances for a newly designed effect.

`wpi_adequate` at line 707 additionally requires an `exec EH t s C` witness, an adequate concrete handler, WP and its handler invariant. It yields the execution predicate, updated invariant and continuation/threadpool WP obligations through the stated modal update. `wpi_adequate_pure` at line 727 extracts a pure proposition only under its credit, invariant, handler, WP and post-extraction premises.

For a proposed MiniRust extension, a component that changes byte contents and a component that changes alias permissions can interact through shared state. These generic sum results supply a checked composition rule once the relevant adequacy and invariants have been established. They do not themselves prove that the proposed components observe a consistent byte/provenance/alias/race state. This replay supplies no new such instance.

### 4. The state, value-heap and scheduling results retain relational premises

Basis: source + actual theorem types + checked proofs.

`state_adequacy` (`src/state.v:244`) transports WP through an explicit `state_irel` under `Sequential H` and state interpretation resources. `heap_adequacy` (`src/heap.v:527`) specializes this structure to the artifact's heap of values and `heap_irel`. The second textual `heap_adequacy` at line 537 is in a commented-out sketch and was not treated as a second theorem. Load/store/allocation rules require their stated points-to, invariant-mask, handler-inclusion and continuation premises. This is not a byte/provenance allocator model.

`threadpool_adequacy` (`src/threadpool/interleaving.v:1556`) assumes `Sequential H` and a `threadpool_irel` witness. WP for the concurrent ITree implies WP for every interleaving satisfying that relation. Its postcondition permits `LastThreadKilled` with `True`; it does not promise a returning final value for every scheduling outcome.

ExampleLang's `wp_adequacy_irel` (`src/examplelang/adequacy.v:27`) assumes the explicit threadpool → UB → state → demonic interpretation relation, state interpretation and WP. Its outcome distinguishes successful return, last-thread death and UB; the UB branch yields false. These are actual checked relations, not a proof that an arbitrary external interpreter implements them. Weak-memory atomics and Rust alias/race interaction are outside these instantiated models.

### 5. HeapLang's operational bridge has a specific direction

Basis: source + actual theorem types + checked proofs.

`src/heaplang/adequacy.v:15–50` defines the relational execution chain and adequacy predicates. `wp_partial_soundness` at line 147 uses the `Later` WP and finite step bounds. `wp_total_soundness` at line 167 uses `Identity` and relational adequacy with no step bound. The relational outcome still includes the explicitly represented last-thread-death case; it must be read from the definition rather than inferred solely from the word “total”.

`execution_from_opsem_trace` (`src/heaplang/opsem_adequacy.v:1521`) starts with an operational `nsteps` derivation **and** a terminal-or-UB `tp_termination` witness. It constructs a related HeapLang ITree execution with the corresponding outcome. This is an operational-to-relational construction under those premises. It is not an unconditional bidirectional equivalence between arbitrary executions.

`partially_adequate_opsem_adequate` at line 1558 then derives Iris operational `adequate NotStuck` from relational partial adequacy. Both `wp_later_opsem_adequate` at line 1584 and `wp_total_opsem_adequate` at line 1594 conclude that same `adequate NotStuck` shape, with a value postcondition. The latter accepts the stronger `Identity` WP premise and weakens it in its proof; its name does not turn the conclusion into an operational termination theorem.

### 6. Islaris safety is conditional on the supplied architecture, traces and resources

Basis: source + actual theorem types + checked proofs.

The archive's original `islaris/adequacy.v:91` quantifies over a list of register maps. Given `Arch`, pre-ghost state, `Pκs []`, the instruction table, backed-memory domain, trace specification, memory/register resources and the stated assembly WP proof, each supplied finite `nsteps` execution yields not-stuckness of every remaining thread and `Pκs κs`.

The ITree adaptation's `isla_exec_adequate` at `islaris/adequacy_itree.v:265` constructs the specified handler-execution witness from a single initial register map and finite operational execution. Its `isla_adequacy` at line 273 also needs `statePreG`; it combines that relation with the supplied ITree WP/resource proof to establish finite-step not-stuckness and the trace postcondition. This is the archive's conditional theorem about its trace language. It does not certify that traces originated from Sail, that executable bytes decode to those traces, or that resuming Rust satisfies its ABI, validity or aliasing contracts.

## Boundaries

- **Selected replay, not the entire artifact build:** six original `.v` files were outside the compiled closure: `src/angelic_choice.v`, `src/interpreter.v`, `src/heaplang/interpreter.v`, `src/heaplang/tactics.v`, and the HeapLang `join.v`/`spinlock.v` examples. The dependency install and this recursive check also do not imply that every module in vendored Iris/stdpp was a selected theorem subject.
- **Not examined in this replay:** RustBelt, lambdaTB and its extended protectors/interior mutability; newer upstream Islaris/Sail bridges; concrete ISA decoding; Rust translation and library contextual soundness. Their absence here is a scope boundary, not evidence that the corresponding systems lack results.
- **Unestablished extension:** no actual coupled MiniRust byte/provenance/alias/race handler instance, frontend correspondence, open-client linking theorem, ABI or machine-byte theorem was constructed. The checked composition interfaces identify obligations for such work; this run does not discharge them.
- **Trust boundary:** `coqchk` accepts declared axioms and primitive interfaces as context. It does not prove them, the consistency of Coq, the checker executable, compiler, plugins, operating system or hardware. Hashes bind observed bytes; they are not a correctness proof of those tools. This is an author execution report, not independent review of itself.

Operational failures were classified separately from proof outcomes. The first read-only harness preflight found no Python executable in the container (exit 127), so existing shell tools were used. `coqchk --help` printed usage and exited 1. An explicit `--user opam` Makefile generation failed with `Sys_error("Makefile.coq: Permission denied")`; numeric ownership and absence of `Makefile.coq` were confirmed before using the container's authorized default root user. A subsequent all-source hash check ran after root generation/core launch, and the final check again verified all 476 files. No source-byte or permission correction was made by this agent. A guessed package metadata filename was absent; read-only directory inspection located `switch-state`. These are preserved operational diagnostics, not failed theorem checks.

Separately, the parent's prerequisite dependency installation had initially failed because earlier ZIP materialization lost executable mode on two `make-package` scripts. The original archive marks both executable; the parent restored only their modes and freshly installed the dependencies before this replay. Source bytes remained unchanged. That earlier setup failure is not a defect in the checked proof terms. A later report-coordinate extractor initially omitted the source keyword `Corollary`; adding it corrected metadata extraction only. A subsequent exact-name check separated `wpi_store` at line 356 from the primed lemma at line 332. Neither correction changed source/proof bytes or reran the proofs.

## Evidence

Evidence was acquired on 2026-10-14. The following package material makes the load-bearing observations recoverable:

- [support/source-identity-proposal.json](support/source-identity-proposal.json): all 476 archive/source file identities; exact archive and subtree manifests. [support/source-coordinates.json](support/source-coordinates.json) maps every selected result to its source path, line and file hash.
- [support/logs/final-source-check.stdout](support/logs/final-source-check.stdout): final 476-file match. [support/execution-summary.json](support/execution-summary.json): copied-output reconciliation and all 542 loaded/checked library identities. [support/logs/loaded-object-hashes.stdout](support/logs/loaded-object-hashes.stdout) hashes the exact loaded `.vo` files.
- [support/AuditCore.v](support/AuditCore.v), [support/AuditHeapLang.v](support/AuditHeapLang.v), [support/AuditIslaris.v](support/AuditIslaris.v), and their complete `audit-*.stdout` logs: actual types and assumptions for all 25 selected results plus the three explicit axiom observations. [support/actual-assumptions.json](support/actual-assumptions.json) retains each complete observation block and its hash.
- [support/logs/recursive-coqchk.json](support/logs/recursive-coqchk.json), [stdout](support/logs/recursive-coqchk.stdout), [stderr](support/logs/recursive-coqchk.stderr): exact checker command, exit status, complete recursive trace and global context. `coqc` SHA256 is `73e0ac064f017c4c00e4f5a40c458c2bb4c3ef159b6a7e9680dd97272b7d38c6`; `coqchk` SHA256 is `9c2be314b44dd7f8e874dad47e885c8861ba50b8e0a506500b025b5f051057fb`. Tool hashes, installed switch metadata and container/image/resource identity are preserved in the corresponding logs.
- [support/completed-task-tree.tar.gz](support/completed-task-tree.tar.gz): all 264 copied files, including all 41 actual `.vo` objects, original source bytes, audits and generated dependency Makefile. Transport tar metadata normalizes UID/GID/mtime only; regular-file bytes and modes are preserved. It is evidence for this environment; native checking elsewhere requires compatible matching dependencies.
- [support/successful-phases.json](support/successful-phases.json) and the phase logs retain every command/result. [support/operational-diagnostics.json](support/operational-diagnostics.json) and [support/parent-mode-diagnosis.json](support/parent-mode-diagnosis.json) separate harness/setup diagnostics from proof outcomes.

Three copy-command receipts and the two host mount-source fields in the container-inspection stdout contain an explicit public display-path projection, documented with original/public SHA256 receipts in [support/public-path-projection.json](support/public-path-projection.json). Only exact private host prefixes were replaced with `<TASK_SCRATCH>` or `<TASK_FORMAL_TOOLS>`. Raw originals were retained privately. Process statuses, source/proof bytes and every other stdout/stderr byte remain unchanged; container runtime paths remain literal.

## Revalidation

First verify [package-manifest.json](package-manifest.json), the source ZIP hash, annotation hashes and captured object manifest. The cheap semantic check is to recompile the three observation-only audits in the recorded dependency environment and compare all 25 actual theorem types and assumption sets, then run the same recursive `coqchk` command. A successful file-integrity check alone is not a fresh kernel check.

For a fresh source build, [support/REPLAY.md](support/REPLAY.md) gives the selected commands. Use the exact archive stdpp/Iris trees and recorded external dependency versions; preserve executable ZIP modes when preparing dependencies. Generate `Makefile.coq` from the original `_CoqProject`, build only the named seeds at `-j1`, then compile the audits and recursively check the nine seed modules plus all three audits. Recheck the 476 source hashes and loaded-object identities. The archive's `build_source.sh`, default broad builds, package wrappers, installs and cleanup are unnecessary for this selected replay once dependencies are ready.

On a changed artifact, compare the actual premises and theorem directions as well as assumption dependencies. In particular, preserve the `Sequential`/interpretation and resource hypotheses, last-thread-death and step-exhaustion outcomes, both `adequate NotStuck` conclusions, and the original-versus-ITree Islaris initial-state distinction. A new MiniRust or ISA instantiation requires its own proof and source/representation correspondence; repeating this artifact replay cannot supply it.
