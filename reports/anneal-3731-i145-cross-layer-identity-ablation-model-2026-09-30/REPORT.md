# I145 bounded cross-layer identity ablation model

## Result

This package answers a narrow version of #3731 I145: **which separately observable fields are necessary under three declared symbolic policies?** A Python standard-library checker exhaustively enumerated all `2^16 = 65,536` binary snapshots and held five locators constant. It tested all sixteen candidate fields against each policy: 31 tests actually removed a field present in that policy, and 17 were absent-field controls that left its key unchanged. The full keys were sound against their own declared oracles. Each field required by an oracle had a one-field collision when removed; fields outside that oracle could be omitted without a collision. This is a finite **model result**, not an Anneal run, a proof of globally minimum identity, or a correctness result for a real cache or server.

| Policy | Minimum fields within this model | Required fields | One-at-a-time result |
|---|---:|---|---|
| Elaboration content | 3 | Lake environment, imported artifact, proof document bytes | All 3 removals collide; 13 other fields are irrelevant to this equivalence. |
| Strict cross-stage lineage | 12 | Source subject/bytes/revision; Charon config; LLBC bytes; Aeneas config; generated tree/generation; Lake environment; imported artifact; proof bytes/generation | All 12 removals collide; 4 execution fields are irrelevant. |
| Current-request admission | 16 | Strict lineage plus worker epoch, file-worker epoch, RPC session, RPC request | All 16 removals collide. |

The **content** policy asks whether two goal computations have equal modeled elaboration inputs. It permits reuse across different source and generation histories when the document, Lake environment, and imported artifact match. The **lineage** policy asks whether a result can be attributed to the same modeled producer fields, even when outputs happen to be equal. The **admission** policy asks whether a response belongs to the exact current query and worker incarnations. A single composite token could encode these fields; the numbers count independent distinctions, not required database columns or hash strings.

## Exact abstraction

The sixteen fields are independent binary axes in the exhaustive matrix. Values `0` and `1` mean distinguishable symbolic identities, not literal bytes or cryptographic hashes. The source path `src/lib.rs`, LLBC path `out/Probe.llbc`, generated path `generated/Probe/`, module `Probe.Funs`, and proof URI `file:///work/Proof.lean` are fixed in every state. `source_subject` can differ at that same source path. The model deliberately permits an upstream identity to change while later outputs remain equal, and a downstream artifact to change without an upstream edit. Such combinations cover cache replacement, nondeterminism, stale publication, and output convergence as *possibilities*, but they are not asserted to be reachable in Anneal.

The three oracle labels are explicit projections of the state: content uses the three elaboration inputs; lineage uses the first twelve producer/document fields; admission uses all sixteen. A key is sound when every state sharing it has the same oracle label. The checker groups all 65,536 states for each full key and for each of its sixteen one-field ablations. A counterexample is the first pair in enumeration order with equal ablated key and different oracle label. These oracles encode policy requirements, so the checker establishes internal necessity/sufficiency for *those requirements*. It cannot independently validate whether those are the right requirements for Anneal. In particular, treating every upstream configuration or generation as lineage-critical is a strict provenance choice, not a discovery forced by Lean's answer semantics.

`source_revision`, `generated_generation`, and `document_generation` are distinct from their payload fields. A revision distinguishes a return to equal bytes after intervening work; a generated generation distinguishes equal tree bytes published through different build histories; a document generation distinguishes an equal proof after close/reopen or replacement. Worker, file-worker, RPC session, and RPC request identities fence delivery and routing. They are absent from the content key because a completed computation can in principle be reused after separate validation.

## Named controls

The retained JSON includes ten named traces with exact changed fields and three policy verdicts:

- **A→B→A:** source bytes return to `0`, while source revision advances `0→1→2`. The endpoints have equal modeled elaboration content, different strict lineage, and different request identity. The exhaustive matrix itself uses binary values; this three-state control extends revision to `2` solely to expose the return.
- **Equal outputs, distinct histories:** source revision, Charon config, and generated generation change while generated tree, imported artifact, and proof bytes remain equal. Content reuse is permitted by the content oracle; lineage attribution is different.
- **Unchanged proof, changed import:** document bytes stay `0`, imported artifact changes `0→1`; all three policies distinguish the endpoints. The Lake-environment-only control does the same.
- **Constant locator, changed payload or generation:** separate controls change source bytes, source revision, and document generation without changing any path, module name, or URI.
- **Reused transport identifiers:** worker or file-worker epoch changes while RPC request stays `0`; another control changes RPC session with the same request number. Content and lineage agree, but current-request admission rejects the old response.

Every required-field ablation in `results.json` gives an explicit pair differing only in that field. For example, omitting `import_artifact` from the content key admits a response based on artifact `0` under artifact `1` with the same proof and Lake environment. Omitting `source_subject` from strict lineage conflates two symbolic Cargo subjects at the same path. Omitting `rpc_request` from request admission conflates separate requests in one session.

## Relation to prior evidence and residual

This model builds on the published [bounded response-identity model](../anneal-3730-identity-state-mutation-model-2026-09-29/REPORT.md), which explored a transition graph and four weak composite guards but explicitly left one-dimension-at-a-time cross-layer ablation open. The [real generation publication fixture](../anneal-3731-real-generation-publication-v4-30-0-rc2/REPORT.md) retained seven-file A/B families and observed mixed LLBC/Lean source/OLean states during an in-place update; this package does not rerun that fixture. The [I076 profile/config witness](../anneal-v2-profile-cfg-subject-slug-collision-2026-09-29/REPORT.md) directly found different Charon model bodies under one source path and unchanged V2 slug; its outcomes are not inferred from this symbolic checker. The [postpublication residual audit](../anneal-3731-i107-i159-postpublication-residual-audit-2026-09-29/REPORT.md) says complete cross-layer ablation and implemented Anneal service remain open.

The open I145 question remains empirical and architectural: map actual Cargo subject and Charon/config identity to LLBC; map LLBC and Aeneas/config to the generated tree; map that tree through Lake environment and imported OLean bytes to an opened proof; then exercise worker/file-worker/RPC races and output-identical rebuilds. This model does not establish that those fields are independently observable in the implementation, that a specific hash is collision-resistant, that a real Lean worker reloads an import on mutation, or that provenance must always be included in a computation cache key. It also does not price false misses, durable cache reuse, or causal constraints between stages. The independent Cartesian space intentionally over-approximates real pipeline histories.

## Replay and files

Run `python3 check.py` from this directory. It recomputes all 65,536 states, three full-policy checks, 31 present-field removals, 17 absent-field controls, and named controls, then compares its deterministic output byte-for-byte with [`results.json`](results.json). `python3 check.py --write` regenerates the JSON. [`check.py`](check.py) and the report are the complete model package. No external package, service, translator, Lean process, or fixture mutation is required.
