# Bounded identity and two-writer state mutation model

## Summary

A finite symbolic response model explored 2,710 reachable states and 11,060 enabled transitions through seven events. Its full captured response stamp had no invalid reuse in that bound. Four weaker policies each had a one-event counterexample: URI plus version missed an unnoticed source replacement, path alone missed a different Cargo subject for the same physical file, stage generation alone missed an editor source edit, and cancellation alone missed an imported artifact replacement. Separate preserved schedules exercise source A→B→A, artifact X→Y→X, close/reopen with document version reset, path/URI aliases, worker and RPC replacement, and combined source/artifact changes.

A second finite patch model enumerated all six orderings of two clients' capture and apply actions. In the four overlapping orders, a URI/version-only patch guard accepted a second stale patch; a full compare-and-swap rejected it. Four actual Python two-thread runs forced both clients to capture the same state before applying in each writer order. They reproduced zero invalid accepts under the full guard and one per run under URI/version-only. These are **model verdicts only**. No Anneal, Lean server, Cargo, filesystem watcher, MCP process, or production editor was run by this package.

## Applicability and exact model

[`support/model.py`](support/model.py) is new Python-standard-library code executed with CPython 3.14.7 on macOS 26.6.2 arm64. It is a response-provenance model, not a claim that the listed tuple is the minimal safe computation-cache key. A response is permitted to represent the *current* request only when its captured source revision and digest, imported-artifact revision and digest, Cargo subject, physical path, logical URI, open epoch and document version, stage generation, worker incarnation, and RPC incarnation all equal the current state and the request is not cancelled. The initial symbolic values are source `(revision 0, digest A)`, artifact `(revision 0, digest X)`, subject `lib`, version 1, generation 0, worker 0, RPC 0.

The finite actions are editor write to B, external unnoticed replacement to B at unchanged revision/version, agent write back to A, independent artifact replacement to Y (either incremented or same revision), artifact restore to X, same-path `lib`→`test` subject selection, same-physical-file URI alias, close/reopen with version 1, new stage generation, worker restart, RPC reconnect, and cancellation. Each change has a stated one- or two-step bound: source/artifact revisions at most 2, subject and alias each at most one switch, and open/generation/worker/RPC/cancellation each at most one switch. No unbounded edit stream, actual process ID, or byte content exists in this model. The physical path remains one symbolic file; a different subject at that path represents the alias control.

Breadth-first search retains one shortest witness path to each reached state and checks every enabled outgoing edge from states at depth below seven. [`support/state-space.json`](support/state-space.json) preserves every reached state, its minimum depth, and every checked edge. The depth histogram is 1, 10, 49, 156, 357, 610, 783, and 744 states at depths 0–7. This is exhaustive **within this transition system and bound**, not an unbounded correctness proof. The reference predicate and mutant guards share one Python program, so a shared specification mistake remains possible.

## Response-identity mutations

| Guard allowed to reuse the initial response | Shortest selected counterexample | Unsafe states / accepted states in graph |
|---|---|---:|
| Full captured stamp plus cancellation | None | 0 / 1 |
| URI and document version plus cancellation | `external-replace-B-unnoticed` changes source digest while URI/version stay fixed | 451 / 452 |
| Physical path plus cancellation | `same-path-subject-alias-test` changes the Cargo subject | 1,519 / 1,520 |
| Stage generation plus cancellation | `editor-write-B` changes source before generation advances | 823 / 824 |
| Cancellation status alone | `artifact-replace-Y` changes imported bytes without cancelling | 1,519 / 1,520 |

Each selected counterexample has depth one; depth zero is safe. Several depth-one witnesses tie for a guard, so the script selects a diagnostic witness at the same proven minimum depth rather than presenting a unique schedule. The entire state graph and policy counts are retained in [`support/results.json`](support/results.json). A weaker key can also cause harmless false misses; this suite's verdict is limited to **unsafe acceptance of an old response as current**.

The named negative controls make the cross-layer distinctions explicit:

- `editor-write-B → agent-write-A` returns source digest A but source revision 2. Path, generation, and cancellation-only keys would reuse the initial response; the full stamp rejects it.
- Adding `close-reopen-version-1` to that A→B→A trace resets the URI's version to 1 under a new open epoch and worker. URI/version-only now also accepts the initial response, although source revision and worker incarnation differ.
- `artifact-replace-Y → artifact-restore-X` returns artifact digest X at artifact revision 2. Even content restoration does not make a previously issued response current without renewed provenance. The same-revision artifact-replacement control changes digest while revision stays 0.
- The source-only, artifact-only, same-path different-subject, URI-alias, and worker/RPC controls are separate. Combined `editor-write-B → artifact-replace-Y` demonstrates that a source edit and imported-artifact transition are independent axes, rather than one implicit “generation” event.
- Cancellation alone rejects the cancelled initial response, but cancellation-only policy accepts unchanged-request-status responses after unrelated source/artifact changes. This model does not assert that content computation can never be reused after revalidation.

## Two-client patch schedules

Client 0 proposes B and client 1 proposes C. `begin_i` captures current source/revision/URI/version/open epoch/generation. `apply_i` compares that capture with the current state, then changes the source and increments its revision if accepted. The adapter patch is modeled as external to the editor session, so URI document version remains 1. Exactly six action permutations satisfy each client's begin-before-apply dependency. In four, both clients begin before either applies. A full compare-and-swap accepts the first apply and rejects the second; URI/version-only accepts both and overwrites the first writer's value. The other two orders are serial: the second client begins after the first apply and can validly apply its own patch. No explicit fork, multi-file atomic edit, or retry algorithm is modeled.

The four thread controls use two real Python threads, a barrier, a lock for each state transition, and gates that force capture order 0 then 1 while both captures precede application. Both apply orders are tested under each policy. They corroborate the finite patch schedule at the model implementation level: zero invalid accepts for full CAS and two across the URI/version-only runs. This is a deterministic local race harness, not an operating-system interleaving proof or test of an actual editor/MCP patch endpoint.

## Agenda coverage and remaining work

| #3731 item | This model's slice | Essential residual |
|---|---|---|
| I011 | Distinct revision/digest, generation, reopen/version reset, A→B→A | Real workspace recreation, reused transport IDs, content-cache reuse with revalidation, actual concurrent callbacks. |
| I013–I014 | Two-writer overlapping capture/apply and symbolic source/artifact axes | Real atomic multi-document edits, editor/MCP/generator/filesystem writers, forks, lost-update recovery. |
| I016 | Open and worker epochs as expiry conditions | Actual Anneal restart/reconstruction from disk or client buffers. |
| I018 | Source and artifact identities can change independently | Real proof-only classifier with macros, includes, build scripts and extraction inputs; see the separate direct Rust fixture. |
| I020–I021 | Same physical path under distinct subject; stale response after return to A | Real Charon attachment and item move/duplicate/split identity; no annotation parser here. |
| I034 | Stable logical URI can coexist with changed generation and reopened worker | Real generated import paths, module identities, incremental reuse and close/reopen publication. |
| I045 | Worker and RPC incarnations fenced symbolically | Delayed real Lean/RPC response, request-ID reuse, clean/forced shutdown and crash recovery. |
| I145 | Four weak composite guards and full symbolic stamp compared | One-dimension-at-a-time ablation of actual Cargo→Charon→Aeneas→Lake→Lean identity, false-miss costs, persistent cache versus response provenance. |
| I147 | Independent source/artifact changes including unchanged revisions and restored digests | Real `.olean` replacement/timestamp and worker/fresh-batch matrix, including output-identical rebuild. |

The report does not attribute a failing schedule to Anneal. It specifies conditions for a proposed response authority check inside this finite model. A production design could encode several fields in one authenticated immutable snapshot token, or legitimately reuse computation after rechecking all relevant content; the model does not rule that out.

## Evidence and replay

- [`support/model.py`](support/model.py) SHA-256 `ef8be2fe88cd027bcdc36cfcabc9b2ebb70fd8317a5525a2d1872afa8fd604ed`: finite transitions, BFS, policy guards, named controls, all patch permutations, and forced two-thread races.
- [`support/results.json`](support/results.json) SHA-256 `0be6d62ae0fbbecdb7f776453001c9120d23df1fdd5f58a8bd62de686869c758`: graph counts, shortest traces with full pre/post states, named control schedules, six patch-order traces, and four thread event logs.
- [`support/state-space.json`](support/state-space.json) SHA-256 `1b663b5157d593e70475105e1810760ca6e0f4fe7c7885eb57e63700a30ca6e5`: 2,710 explicit states and 11,060 checked transitions. [`support/check.py`](support/check.py) verifies edge endpoints and transitions, histogram, policy counts, replay of shortest and named controls, minimality, all patch outcomes, and forced thread ordering; it passed.

From this package run `python3 support/model.py` and `python3 support/check.py`. The first command rewrites only `support/results.json` and `support/state-space.json`. The retained files were byte-identical across two consecutive runs on this host. Expand the event alphabet or depth, or compare with an independent formalization, before using the model to claim stronger invariants. Test a selected schedule against real Anneal request, patch, generation, worker, and artifact APIs before calling it an implementation result.
