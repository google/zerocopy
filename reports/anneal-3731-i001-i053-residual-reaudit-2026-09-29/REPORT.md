# Independent I001–I053 residual challenge at reference `75fa78c1b623ab8db9d9acb4f31ec7958bfb9110`

## Summary

At reference `75fa78c1b623ab8db9d9acb4f31ec7958bfb9110`, I046 and I049 answer their narrow issue questions; I001–I045, I047–I048, and I050–I053 remain partial with explicit gates. A new local ABA double-collect probe supplies a distinct I010/I011 counterexample, and one cited historical re-review checker fails against eight current-file hashes. No #3731 status is changed.

## Applicability

### Method and decision rule

This is a local follow-up to the [v22 row challenge](../anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support/row-challenge-v22.json), not a replacement for its 333-row ledger. I compared each I001–I053 `requested_scope` with the cumulative package list and v22 residual in [the investigation CSV](../anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support/investigation-final-v22.csv); read the cited packages' report findings and boundaries (including raw transcripts, result records, probes, and checker code for the decisive cases); ran the v22 checker and every available `support/check.py` cited by these 53 rows; and searched the current corpus for an unaccounted local-only cell. The issue text is frozen in [the v22 snapshot](../anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support/issue-scope-snapshot.json). No upstream dependency was fetched, installed, or authenticated.

**Answered** means the precise bounded investigation in the issue is resolved by retained evidence. **Partial** means a concrete part is established but another part of that question is not. A **gate** is the input needed to finish the partial answer; it does not erase the established component result. This independent challenge preserves v22's two narrow complete rows and 51 partial rows. Several requested investigations could be considered answered at a design/model level, but their reports explicitly limit the result to invented fixtures; this recheck does not promote them to an implemented Anneal claim.

## Findings

### Row dispositions

The evidence handle is the v22 CSV's cumulative package list. Each line below states the *exact remaining question* rather than treating the general absence of a product as a universal substitute. `P` = partial with the stated gate; `A` = answered at its stated narrow scope.

| ID | Verdict | What the retained evidence answers; exact residual and gate |
| --- | --- | --- |
| I001 | P | The proposed semantic witness distinguishes accepted claims/imports from incidental diagnostics and timing. Agreement for the same actual Rust/Charon/Aeneas subject across Anneal batch and live paths awaits those paths. |
| I002 | P | Pinned compiler/editor architecture and Lean API boundaries are compared. Matched editor and fresh compiler results across Rust extraction, projection, and Lean remain absent; product adapter gate. |
| I003 | P | Pinned Volar edit paths and an adversarial source-map model expose ambiguous/cross-segment edits. A real two-service embedded client and its applied edits are uncached; external-client gate. The issue asks for a representative reproduction, so the model is useful but cannot establish client behavior. |
| I004 | P | Nine identical toy requests and a two-project Lean router compare process and isolation mechanisms. Real combined-stage one-shot/project/broker economics under bounded representative concurrency await an integrated workload and resource headroom. |
| I005 | P | Finite/fake-stage schedules reject stale publication. The requested *identical* edit, cancellation, and dependency-change comparison between a minimal snapshot engine and a versioned scheduler has not been completed; an actual dependency graph is also a product gate. |
| I006 | P | JSON request echo and separate logs demonstrate a fake subprocess boundary. Real Charon, Aeneas, and Lean request/result/error/progress contracts shared by batch/live adapters remain untested; integrated adapter gate. |
| I007 | P | A shared real Cargo job and toy consumers establish that one cancellation need not kill the other. Ownership/reuse across Charon, Aeneas, Lean, LSP, and MCP and late publication await orchestration. |
| I008 | P | Pinned call sites and adapter/patch decision table identify likely upstream hooks and conservative fallbacks. No common measured adapter-versus-patch acceptance oracle or implemented patch exists; product/upstream gate. |
| I009 | P | Feature, build-script environment, and included bytes change Charon LLBC with fixed main source. A complete consumed production key including target/profile/dependencies/model/options remains undefined; product gate. |
| I010 | P | The 256-source capture records rename, symlink, generated-output, and mutable-generation controls. New [ABA double-collect evidence](support/aba-double-collect-results.json) shows that even two identical full scans can accept an impossible mixed A/B pair unless selection is fenced. A coherent arbitrary live-tree capture protocol and full closure still require an owner/epoch or protected snapshot. |
| I011 | P | Finite alias, version-reset, and content ABA counterexamples exist; the new pointer ABA is a filesystem analog. Actual Anneal document/workspace/model/worker/request identities through restart remain untested; product gate. |
| I012 | P | Saved versus private Rust inputs are compared. Open-buffer authority across save, external overwrite, disappearance, rename, and reopen needs an editor host; product gate. |
| I013 | P | Two-writer finite CAS prevents one abstract lost update. Concurrent queries during an atomic proof/helper or two-module change and matching batch snapshot need real workspace documents; product gate. |
| I014 | P | Two candidate Lean writers give one CAS winner. The four independent writer classes, fork semantics, and transport-independent lost-update policy await an Anneal owner; product gate. |
| I015 | P | One stale saved/private-source mismatch is rejected. Sound dependency-scoped acceptance versus global invalidation needs a discovered dependency graph and clean oracle; product gate. |
| I016 | P | Saved Lean restart and symbolic identity controls exist. Reconnection with unsaved editor buffers and outstanding-result classification after an Anneal restart is missing; product gate. |
| I017 | P | Invented markers survive selected malformed Rust while compiler attachment fails. No chosen Anneal annotation grammar/parser is available for unfinished Rust/Lean and nesting cases; product gate. |
| I018 | P | A build-script/include counterexample disproves unconditional comment-only skipping. A sound classifier needs actual annotation syntax and complete Cargo closure; product gate. |
| I019 | P | Charon span and marker ambiguities are measured. Authoritative annotation-to-item attachment across cfg, traits, locals, and generated items needs the parser and selected compiler subject; product gate. |
| I020 | P | Default/feature/test and wrong-unit controls distinguish subjects; current V2 enumeration is not CLI-connected. A complete selected compilation-unit key plus Charon invocation and proof/model mismatch rejection remain; product gate. |
| I021 | P | Marker moves and alias counterexamples exist. In-flight proof ownership across move, duplicate, split, reorder, and delete needs live annotation identities; product gate. |
| I022 | P | A five-marker illustrative helper fixture exposes ordering and collision questions. Actual parsed annotations, generated visibility, and recursive dependency policy remain; product gate. |
| I023 | P | A real Charon-failing intermediate generation leaves a previous Lean model usable with explicit stale labeling in a disposable prototype. UI/agent comprehension, signature changes, and Anneal last-good scheduling remain; product and consenting-human gate. |
| I024 | P | Comment markers survive one regeneration fixture. Unsaved authored proof bytes, unsupported text, external ownership, and override behavior through actual regeneration remain; product/editor gate. |
| I025 | P | Unicode/CRLF boundaries and real tool coordinates have component controls. Byte/scalar/negotiated LSP round trips through an Anneal Rust-hosted map, including invalid boundaries, remain; product gate. |
| I026 | P | Illustrative inverse maps reject synthetic/cross-segment edits. Actual Anneal prefix removal, escaping, scaffolding, and zero-width ownership remain; product gate. |
| I027 | P | Copied-payload attribution demonstrates navigation/edit ambiguity. An authenticated one-to-many/many-to-one obligation map and routed diagnostics/edits await a generator; product gate. |
| I028 | P | One captured Rust comment is projected to equal live/batch Lean bytes in a disposable prototype; a separate shared-sink model covers more plans. Production shared generation, import edits, source-map/declaration equality, and actual syntax remain; product gate. |
| I029 | P | Stale host/version/model CAS and shift/multi-range controls reject bad patches. Atomic editor WorkspaceEdit and cross-file concurrent commit need Anneal ownership; product gate. |
| I030 | P | Direct Lean import action and completion responses are retained. Snippet/additional/multifile edits across generated regions need server-authored Rust-hosted projection and atomic rejection; product gate. |
| I031 | P | Rustc, Charon, Aeneas, and Lean raw diagnostic specimens distinguish error origins. Mapping exact/approximate ranges and responsibility through one authenticated Anneal map remains; product gate. |
| I032 | P | Invented incremental projector checks regenerated ground truth and cost. Useful-scale fuzz/latency on the real grammar and incremental map remains; product gate. |
| I033 | P | Direct/Lake Lean servers exercise file, custom, and untitled unsaved URIs; setup-file exposes a physical path requirement. Anneal URI ownership and editor lifecycle remain; product gate. |
| I034 | P | Same-URI history, separate old URI, close/reopen, and fresh server are tested. Safe stable identity across Anneal generation changes still needs a routing/worker policy; product gate. |
| I035 | P | Three Lean/Lake layouts compare identical small proofs, worker counts, rebuilds, and failure isolation. Real annotation grouping with representative imports/options/plugins is needed for product choice. |
| I036 | P | Direct Lean prefix edits and cancellation show one real reuse boundary. Generated wrapper changes and Anneal invalidation costs await a generated workspace; product gate. |
| I037 | P | Lean local instance, macro, and autoImplicit controls show context sensitivity. Real Rust-to-Lean wrappers and proposition/dependency attestation remain; product gate. |
| I038 | P | Direct Lean distinguishes an open unsaved producer from its compiled import. Anneal's supported two-open-document materialization/import contract remains; product gate. |
| I039 | P | Direct mutual import fails. Legal generated annotation grouping and cycle rejection in the proof dependency graph remain; product gate. |
| I040 | P | A missing-import scratch negative control shows context loss. An authoritative fork replaying exact module, options, imports, and prefix awaits Anneal generation; product gate. |
| I041 | P | Old-version wait and duplicate-ID races demonstrate that response version labels are insufficient. Exact source/import envelopes and client fences need an Anneal broker; product gate. |
| I042 | P | Wait `{}`, empty diagnostics, missing import, and local goals separate readiness signals. A causal parse/import/elaboration/async readiness protocol remains; product gate. |
| I043 | P | Nested/unsaved 28-position grids and a real tactic macro establish direct Lean position behavior. Generated proof/source-map and adapter selection semantics remain; product gate. |
| I044 | P | Rich RPC dereference/release and 42-second idle expiry (`-32900`) establish bounded reference lifetime. Many-reference retention and generation-scoped recovery policy remain; product gate. |
| I045 | P | Same request ID on separate transports and killed-worker recovery are controlled. Late success across internal worker replacement on one transport needs watchdog/owner policy; product gate. |
| I046 | A | Four actual Lean failures (unfinished, unknown tactic, timeout, syntax recovery) leave valid before/after local goals while batch fails; diagnostics and axiom checks prevent whole-file acceptance inference. This answers the exact bounded investigation. |
| I047 | P | Eight-proof two-worker direct/Lake fanout shows stale import and fresh oracle differences. Exact historical/latest service semantics and attributable retention cost require broker and equivalent workload; product/resource gate. |
| I048 | P | Setup paths, OLean hashes, option diagnostics, and initializer markers are observable but not complete loaded-environment attestation. Worker-reported complete environment or equivalent trusted adapter needs upstream/product work. |
| I049 | A | Imported-definition refresh was repeated under `lake serve`, `lake env lean --server`, and direct prepared Lean; watcher/reopen/worker/server controls are compared with fresh batch at the pinned fixture. Exact launch-mode matrix is answered. |
| I050 | P | Transitive macro/plugin/option, external model with fixed generated text, and instance/notation worker split are retained. Complete generated-import invalidation through Anneal remains; product gate. |
| I051 | P | Real retained LLBC/Lean/OLean A/B family shows private staging, mixed in-place failure, and SIGKILL before/after pointer. Actual Anneal publisher/readers, setup/native artifacts, concurrent publishers and durability remain; product/platform gate. |
| I052 | P | The real-artifact fixture validates B before final selection. Final-location preparation versus relocation under Lake manifests, traces, native lookup, and retained workers has not been compared; product/fixture gate. |
| I053 | P | A gated old Lean result finishes after B selection and is rejected. Independent obsolete Charon/Aeneas source/artifact/cache/diagnostic completions under one owner remain; product gate. |

### Distinct local result

The v22 flag `v22_new_distinct_cached_only_experiment_available=false` is too broad for **I010** (and its I011 ABA connection). Prior [snapshot-capture evidence](../anneal-3730-snapshot-capture-jobs-2026-09-29/REPORT.md) gated a *per-file* read/revalidate sequence; this follow-up gates **two complete collections** under `A→B→A→B→A`. Both collections equal `[A-x, B-y]`, so a naive equal-collections test accepts a pair that neither immutable generation contains. Pinning A once gives `[A-x, A-y]`. [Probe](support/aba_double_collect.py), [raw events](support/aba-double-collect-results.json), and [checker](support/check_aba_double_collect.py) are retained. This falsifies only unfenced double collection; a protocol with a monotonic epoch, immutable selection, or filesystem snapshot can still be sound. It uses two invented files on APFS, not an Anneal subject or arbitrary mutable live tree.

The experiment needed no installation and did not alter v22's product statuses. A further local fixture for I052 (final path versus relocation under installed Lean/Lake) might be useful, but it cannot settle native/plugin/setup relocation without a representative product archive. No other *closure* experiment was found among the currently cached assets for these rows.

## Boundaries

This is a coverage judgment over the frozen issue question and locally retained evidence, not an Anneal implementation test or status change. The ABA probe uses two invented files on one APFS host and establishes only a bounded bad schedule for an unfenced algorithm. The checker sweep validates retained records; it does not replay expensive compiler, Lean, or editor experiments. The historical re-review checker failure remains unresolved in this package.

## Evidence

### Checker integrity

The v22 builder/checker passed. Of 25 cited package checkers present for these rows, **24 passed and one failed**. The failure is the historical `anneal-3730-five-original-packages-rereview-2026-09-29/support/check.py`: its second-pass hash manifest no longer matches eight current files. The exact paths are:

1. `aeneas-concurrent-generation-determinism-nightly-2026-06-03/REPORT.md`
2. `aeneas-concurrent-generation-determinism-nightly-2026-06-03/support/check.py`
3. `anneal-interactive-model-probes-2026-09-29/REPORT.md`
4. `anneal-interactive-model-probes-2026-09-29/support/check.py`
5. `lean-import-refresh-cross-version-v4-29-to-v4-30-rc2/support/check.py`
6. `lean-same-server-dependency-generation-v4-30-0-rc2/REPORT.json`
7. `lean-same-server-dependency-generation-v4-30-0-rc2/REPORT.md`
8. `lean-same-server-dependency-generation-v4-30-0-rc2/support/check.py`

The stale manifest is a current revalidation failure, not a refutation of the underlying raw runs. It must be repaired or explicitly scoped to its historical checkout before claiming that re-review checker passes at this HEAD. The other cited packages with no checker were read at report/evidence level; they are not recorded as check passes. The [checker run log](support/checker-runs.json), [68-package evidence inventory](support/package-evidence-index.json), and [eight expected/current hash pairs](support/stale-hashes.json) are retained here.

## Revalidation

Run `python3 ../anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support/check.py` and `python3 support/check_aba_double_collect.py` from this package. To rerun the OS probe, use `python3 support/aba_double_collect.py --scratch <owned-existing-directory> --output support/aba-double-collect-results.json`. A new report package requires catalog regeneration before publication; this task explicitly leaves CATALOG unchanged.
