# Independent #3731 I054–I106 evidence and residual review

## Summary

A fresh audit of the 53 #3731 investigations I054–I106 against the v22 ledger and their 85 cited report packages found **51 partial, one not-run (I072), and one conditional (I081)** at the requested scopes. One distinct local component cell was missing: two Charon jobs sharing a writable Cargo target. The new [I080 package](../anneal-3731-i080-shared-cargo-target-two-process-2026-09-29/REPORT.md) executed that bounded cell, without completing the representative resource and cleanup question.

Seven v22 dependency-gated rows have a misleading generic next-prerequisite sentence claiming OCaml/Dune/opam are absent: **I065, I071, I077, I089, I094, I101, and I103**. That absence is relevant to some Aeneas library questions, but it is not the missing MCP, Charon Rust, archive, or later Lean/Lake input in those seven rows. This report provides exact replacements for the next ledger; it does not rewrite v22's frozen snapshot or change issue statuses.

## Applicability

The review point is `reference` HEAD `75fa78c1b623ab8db9d9acb4f31ec7958bfb9110`, v22's frozen #3731 issue scope and investigation ledger, and the cited report packages in that tree. The separate I080 probe used cached Charon/Cargo binaries on this host; its tool and fixture identities are in its own report. This is an evidence-coverage review, not an Anneal production acceptance run.

The [row review](support/row-review.csv) preserves each exact requested scope, status, gate, reviewed remaining delta, next prerequisite and cited package list. The [package inventory](support/package-inventory.csv) identifies all 85 cited packages, report bytes and checker dispositions. Every cited package has `REPORT.md` and `REPORT.json`; the 85 packages contain 3,044 files, and all 86 literal Markdown `support/` links that could be resolved without a glob exist. The current-source report was checked for actual CLI reachability; its `setup` and target/lock helpers do not implement the missing verifier, editor, MCP or generation owner.

## Findings

### Item-by-item disposition

The table is a compact retrieval view; `support/row-review.csv` retains the full question and package mapping for every ID. “Partial” here means the cited experiments answer a bounded component of the issue question, not that the current Anneal V2 product implements it.

| ID | Status / gate | Specific remaining test |
| --- | --- | --- |
| I054 | partial / product | SIGKILL immediately before/after fixture pointer replacement left exact A/B selected respectively; tool-stage failure rollback, visible last-good status and actual Anneal generation-owner behavior remain untested. |
| I055 | partial / product | Real Aeneas output-set shrink was observed, but selected obligation ownership and fresh verifier after deletion/rename need an Anneal publisher. |
| I056 | partial / product | Eight-proof and two-worker stale-import controls already ran; authenticated full graph invalidation and generated producer routing require Anneal. |
| I057 | partial / product | Rust/editor extension and LSP proxy coexistence require an editor host and implementation absent from this checkout. |
| I058 | partial / product | Multi-origin push/pull diagnostic routing and rename clearing require the absent Rust editor projection. |
| I059 | partial / product | Direct Lean navigation responses exist; generated-to-authored mappings and editor feature routing require Anneal projection. |
| I060 | partial / product | Direct Lean two-file rename edits and guards exist; applying projected Rust edits requires the absent host transaction. |
| I061 | partial / product | Marker projection and direct RPC/InfoView queries already ran; real InfoView UI and Anneal transport are absent. |
| I062 | partial / product | Capability/version harness controls already ran; representative real editor clients against a Rust-hosted projection are absent. |
| I063 | partial / product | Direct Lean and hash watcher save/format controls already ran; actual editor and Anneal watcher/generator ordering are absent. |
| I064 | partial / product | Divergent disk/buffer reconnect requires editor ownership coupled to a live projected Lean worker. |
| I065 | partial / dependency | Two stdlib/current-wire toy MCP models exist; independent SDK/client interoperability and an existing Anneal adapter are absent. |
| I066 | partial / product | Manual hash-gated cross-layer joins exist; typed Anneal subject/snapshot/edit/verify API and agent trial are absent. |
| I067 | partial / product | Local broker models one edit response; durable MCP retry/dedup/CAS across real edit, create and check operations requires the adapter. |
| I068 | partial / product | Single authority shared by MCP and editor is an unimplemented Anneal workspace service. |
| I069 | partial / product | Executed tier/path isolation requires actual MCP tools and generated-to-authored mutation authority. |
| I070 | partial / product | Two-process CAS and crash controls already ran; real subject IDs, RPC, proposition oracle and GC lease policy require implementation. |
| I071 | partial / dependency | Lean-backed cancellation forwarding and toy wire lifecycle exist; actual MCP client/broker task lifecycle remains absent. |
| I072 | not-run / adapter, product | No installed existing Lean MCP adapter was exercised. The current-wire plus actual Lean goal bridge is still standard-library toy code with a raw test client; two real clients sharing an Anneal workspace remain unrun. |
| I073 | partial / product | Saved/private materialized Charon comparison exists; an actual unsaved editor/rustc overlay extractor is absent. |
| I074 | partial / product | Bounded build-script/proc-macro/include/env closure exists; faithful arbitrary side effects and shadow policy require implementation. |
| I075 | partial / product | Selected Cargo unit graphs exist and V2 has unconnected target enumeration; extraction attestation for warm skip and alternate target invocations still needs an invoked wrapper policy. |
| I076 | partial / product | The wrong binary-unit negative exists; V2's target/kind enumeration and LLBC filename helper do not supply a complete compilation-unit key or collision-rejecting produced output selection. |
| I077 | partial / dependency | Pinned Charon CLI is one-shot; same-process library reset/cancel API and equivalence oracle are unavailable. |
| I078 | partial / product | Private LLBC and interruption controls exist; V2's run-root lock primitive is not a schema-validated transactional Charon set publisher with a producer owner. |
| I079 | partial / product | R42/R43 short-name permutation and identical Lean oracle already ran; general normalization and provenance-safe key policy need schema support and Anneal. |
| I080 | partial / resource | Two private Charon jobs sharing one fresh Cargo target now show overlap, a Cargo build-lock wait, bounded RSS/disk samples and companion completion after peer cancellation; representative sustained workload, incremental-on and many-worker cleanup remain untested. |
| I081 | conditional / dependency, decision | OCaml/Dune/opam toolchain not installed; same-process Aeneas needs user-approved non-local dependency scope. |
| I082 | partial / dependency | External Lean model mutation leaves Aeneas text fixed; compiled registry/normalization and second compatible Aeneas binary are unavailable. |
| I083 | partial / product | Trait body/signature and Types.olean reuse oracles already ran; item-level Aeneas reuse and authenticated graph require producer support. |
| I084 | partial / product | New pinned namespace-move cell changes generated helper identity while a fresh caller proof still succeeds; broader automatic annotation migration and arbitrary signatures remain product work. |
| I085 | partial / product | Oracle-guided Types.olean reuse already ran; producer-level multi-file reuse and cross-crate cache keys need Aeneas/Anneal changes. |
| I086 | partial / dependency | File versus Python-buffer route and controls already ran; genuine same-process OCaml/structured-stream handoff is unavailable from the pinned CLI. |
| I087 | partial / dependency | Charon IDs/spans and generated ranges are retained, but pinned output lacks an authenticated item-to-declaration map; newer compatible schema is unavailable. |
| I088 | partial / dependency | One-shot partial sorryAx failure is captured; repeated same-process Aeneas reset and structured provenance need a callable translator worker. |
| I089 | partial / dependency | V2 exposes setup and a feature-gated Lake archive fixture, but the scoped inventory found no actual prepared Anneal archive; the fixture was not executed and cannot substitute for a fresh consumer first-goal run. |
| I090 | partial / product | Frozen index collision control already ran; complete multi-identity preparation key and real archive need Anneal producer/consumer. |
| I091 | partial / product | Saved-file plugin/OLean/option setup was traced; exact unsaved header/import attestation needs generated workspace and worker API. |
| I092 | partial / product | Selected no-build/no-cache hashes stayed unchanged; full archive/native/plugin/server contract needs real prepared product. |
| I093 | partial / product | Dynamic Lean run_cmd environment input and TOML/static contrasts already ran; additional graph permutations without a declared policy repeat the same hidden-input risk. |
| I094 | partial / dependency | Only cached compatible pinned Lean/Lake tuple is 4.30-rc2; later compatible tuple needed for frozen-consumer replay. |
| I095 | partial / platform, product, resource | Selected Lake libc-call provenance now exists: the unprivileged observer recorded a positive 88-byte lakefile.olean read, source/trace/hash opens and a transient-to-final OLean rename on a tiny private fixture. It omits direct syscalls, pread/mmap, other paths and complete absence proofs. A representative prepared Anneal consumer still needs complete process/read/write attempt tracing and parallelism controls. |
| I096 | partial / product | One Lake plugin/server discovery path ran; V2 setup resolves toolchain paths, while actual editor/MCP/CI launchers and their configuration discovery remain unexercised. |
| I097 | partial / product | Selected plugin/OLean/option mix exists; sufficient cross-layer key and object validation require full consumer implementation. |
| I098 | partial / product | Same-pin artifact family succeeds in tiny graph; broader incompatible mixes need actual generated Anneal consumer. |
| I099 | partial / product | Clean/mixed tiny theorem and plugin controls exist; complete equivalence needs actual Anneal workspace. |
| I100 | partial / product | M06 real generated small graph already varied no-op, mtime and byte-different comments; larger graph/separated path-span perturbations only matter against selected normalization policy. |
| I101 | partial / dependency | Local pair relocation exists; producer-removed prepared Anneal archive is unavailable. |
| I102 | partial / product | Lake metadata replacement and writer fixtures exist; same-key artifact/map interruption and durability need selected cache publication design. |
| I103 | partial / dependency | Same-name local generation replacement exists; actual archive installation and interruption semantics need an archive. |
| I104 | partial / platform, product | The earlier prepared-contract fixture already ran relocated no-build/setup/batch under sandbox-exec network denial and a loopback EPERM control. The new observer records selected private-root file calls only. Trace attempted network and all relevant filesystem access for producer and consumer, and test environmental closure of an actual Anneal archive. |
| I105 | partial / product | Eight actual CLI stop/kill/retry cells plus direct Lean processed cancellation already ran; remaining editor/Anneal lifecycle and deeper phase ownership require product. |
| I106 | partial / product | Direct Lean cancel-control transcripts already show real fileProgress and publishDiagnostics after explicit cancellation, plus old replies after edits; publication fences and worker correlation require Anneal scheduler. |

### Seven prerequisite corrections

| IDs | Exact missing input for a later audit |
| --- | --- |
| I065 | Select a real MCP SDK/client pair and a versioned Anneal adapter/workspace contract; exercise independent negotiation and fallback. Current-wire reports explicitly use standard-library toy bridges. |
| I071 | Select a real MCP client/broker task implementation and Anneal-backed long operation; exercise dropped responses, reconnect, cancellation, progress and backpressure. The Lean-backed bridge is still a toy. |
| I077 | Obtain a callable pinned **Charon Rust** library or worker boundary and a fresh CLI oracle for A/B/A, error and cancellation reset. Existing runs used one-shot processes. |
| I089, I101 | Supply a content-identified built Anneal omnibus archive and matching generated consumer locally. The scoped archive inventory found none; the small Lake controls do not substitute for real fresh-first-goal or producer-removed relocation runs. |
| I094 | Select a later compatible Lean/Lake tuple and coupled toolchain for frozen-consumer replay. Only 4.29.0 and 4.30.0-rc2 are cached locally; consult before acquiring a non-local dependency. |
| I103 | Supply at least two content-identified permitted Anneal archives under one nominal version and an installation consumer for replacement/interruption tests. The local same-name generation fixture is narrower. |

These corrections change prerequisite wording only. I065/I071 remain partial, I077 remains partial, I089/I094/I101/I103 remain partial, and no dependency was fetched or installed.

### Checker and resource recheck

Twenty-five cited package checkers passed read-only. Three were left unrun because each writes `support/summary.json` in place: `anneal-3730-lean-transitive-import-rpc-matrix-2026-09-29`, `anneal-3730-mcp-shaped-async-task-lifecycle-2026-09-29`, and `anneal-3730-pinned-cross-layer-navigation-boundary-2026-09-29`. Two initially screened out by a simple token scan were inspected separately: `anneal-3730-m06-generated-lake-source-order-trace-2026-09-29` only opens a tar for reading and passed; `anneal-3730-five-original-packages-rereview-2026-09-29` uses read-only `git` subprocesses and failed its historical second-pass SHA check because a concurrently edited `aeneas-concurrent-generation-determinism-nightly-2026-06-03/REPORT.md` no longer matched that old review record. That failure does not falsify this slice's technical experiments, but the review package needs reconciliation before it is described as a current-file check.

The scoped local inventory found installed Lean 4.29.0 and 4.30.0-rc2 only, no built Anneal omnibus archive within the checked `.anneal-local-tools` paths, and no likely Lean MCP adapter, `dune`, `ocamlc`, or `opam` on `PATH`. These are availability observations, not proofs of global absence. I080's new two-process control used a private target and had a fresh 49-GB disk preflight plus conservative RSS/disk guards. Its component result does not justify promoting I080 from partial.

## Boundaries

- No real current Anneal V2 extraction-to-verification service, editor host, MCP adapter, or prepared omnibus archive was run. The V2 source report's offline Cargo build stopped during missing pinned Charon dependency resolution before compilation.
- The checkers validate retained outputs and varied in design. The 25 passing scripts are not a full replay of their toolchain experiments; the three summary-writing scripts were not run in the shared worktree. The historical reviewer checker failure concerns moved report bytes, not a new technical experiment.
- The 85 cited packages collectively cover source, component executions and finite models, but do not answer all 53 issue questions at production scope. There was no approved non-local dependency installation, no high-memory benchmark, and no privileged complete filesystem trace.
- No other distinct cached-only closure experiment was found after comparing the exact row residuals with their cited package evidence and the current local cache. This does not rule out useful future experiments after a product contract, archive, adapter, compatible later toolchain, representative workload or tracing surface becomes available.

## Evidence

- `anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support/investigation-final-v22.csv` SHA-256 `2b7e31ba897abbbdd6c1268c0ed278baa7e6ccdc29dce504380d22e79195b5d6`; `row-challenge-v22.json` SHA-256 `7e458e97a57e6757742ab221881fa69d7e374994593477b68b81bd4ecb1bf4d7`; frozen issue scope snapshot SHA-256 `5c261d44e788ac96a0cb2d347752d01bbc51ffb03697a6a08a76e02f55469a6d`.
- `support/row-review.csv` contains the full 53-row decision trace and seven corrected prerequisites. `support/package-inventory.csv` contains the 85 cited package identities and checker notes. `support/check.py` validates these against the frozen v22 source, package files and the new I080 report.
- The new [I080 report](../anneal-3731-i080-shared-cargo-target-two-process-2026-09-29/REPORT.md) retains its exact observed probe, raw process/lock transcript, LLBC specimens, cleanup record and checker.
- Representative package boundaries checked directly include the [real archive gate](../anneal-3730-real-archive-manifest-gate-2026-09-29/REPORT.md), [current V2 source surface](../anneal-v2-current-source-surface-main-bd0956b-2026-09-29/REPORT.md), [Aeneas process contract](../anneal-3730-aeneas-process-contract-2026-09-29/REPORT.md), [Charon concurrency control](../anneal-3730-charon-concurrency-interruption-2026-09-29/REPORT.md), [MCP current-wire bridge](../anneal-3730-mcp-2026-lean-goal-wire-composition-2026-09-29/REPORT.md), [Lean cross-version equivalence](../anneal-3730-lean-cross-version-equivalence-v4-29-v4-30-rc2-2026-09-29/REPORT.md), and [Lake file observer](../anneal-3730-lake-unprivileged-file-event-observability-2026-09-29/REPORT.md).

## Revalidation

The package inventory was refreshed after the later cross-report review changed cited report bytes; it now pins the current hashes and file count (3,044). The underlying 85-package selection and checker dispositions are unchanged.


Run `python3 support/check.py` for the retained 53-row audit and `python3 ../anneal-3731-i080-shared-cargo-target-two-process-2026-09-29/support/check.py` for its new execution evidence. A later coverage audit should carry the seven exact prerequisite corrections, retain I080 partial, and run the three in-place summary writers only in disposable package copies. Recheck the historical reviewer package against the final reconciled corpus bytes. Revisit the local-only experiment search when an actual V2 verification path, content-identified archive, adapter, compatible later toolchain, representative workload or complete trace facility is available.
