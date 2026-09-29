# Bounded fault model for shared proof jobs and complete generation publication

## Summary

A new finite event model checked a small orchestration contract with two consumers, at most two jobs, separate source revision and digest, stage generation, worker and RPC incarnations, cancellation, partial stage output, and publication. Breadth-first exploration found no safety violation in 76,502 reachable baseline states through seven events. Removing each of eleven individual guards produced a shortest counterexample, including an unobserved external edit, a cancelled shared consumer, late old results, incomplete output, and a wrong request echo. A selected late-result schedule was replayed with two real gated Python subprocesses using the existing fake-stage harness: the newer result published, and the old result completed later but was rejected.

These are **model and fake-backend results**, not evidence that Anneal implements the guards or has any of the mutated failures.

## Applicability

The model is [`support/model.py`](support/model.py), run with CPython 3.14.7 and the Python standard library on the same macOS host as the adjacent reports. It is a separate model from `anneal-interactive-model-probes-2026-09-29`; this package adds job ownership, cancellation, process/session incarnations, stage completeness, result echo, external-state reconciliation, and failure status. The source was written for this investigation and verified by the retained execution results, not assumed correct because it is a model.

The bounded state contains an authoritative `(revision, digest)`, a watcher-maintained observed pair, a stage generation, worker and RPC epochs, zero to two jobs, and a selected publication pointer. A job captures those five identities at start, owns a set drawn from `{editor, agent}`, accumulates three stage pieces (`source`, `model`, `proof`), and has an `active`, `cancelled`, `failed`, or `timeout` status. Results may arrive late even after cancellation, failure, restart, or edit. The model's `published` pointer is last selected output; after a later edit it is only last-known-good, not a claim about the new source.

The graph bound is seven events, two jobs, revisions and worker/RPC epochs in `{0,1}`, digests in `{A,B}`, and three stage bits. Each unique state reached at depth at most seven was retained; every enabled outgoing transition at depth less than seven was checked. The actions include starting/joining, individual cancellation, ordinary and external edits, same-revision digest replacement, same-source regeneration, worker restart, RPC reconnect, reconciliation, piece completion, failure/timeout, and valid or wrong-echo delivery. This graph does not encode the actual Rust, Charon, Aeneas, Lake, Lean, LSP, MCP, or filesystem implementations.

## Findings

### Explicit publication invariants

The baseline authorizes an atomic pointer selection only when **all** conditions below hold at delivery time. [`support/results.json`](support/results.json) stores the graph counts, shortest counterexample schedules and states, and positive/negative control traces.

| Invariant | Required condition |
| --- | --- |
| Authoritative input | Job revision and digest equal the current authoritative pair; the observed pair has been reconciled with it. A watcher notification alone is not authoritative. |
| Stage and process identity | Job's stage generation, worker incarnation, and RPC incarnation equal the current values. Old responses may still be retained under their old identity but cannot select current output. |
| Ownership and cancellation | At least one consumer still owns the job and the job remains active. Cancelling one of two consumers does not kill the other's job. |
| Complete, correlated result | All source/model/proof pieces are present and the result echo matches the request. Failed or timed-out work cannot publish even if a late result is delivered. |
| Selection | Only a result passing all preceding checks changes the selected pointer; a rejected or incomplete result leaves the old pointer alone. |

These are **specified model properties**. The model's reference predicate checks them independently of each mutant's authorization logic, but both are in one Python program; a shared specification error remains possible.

The baseline search reached 76,502 states and checked 305,537 enabled edges through depth seven with no invalid selection. The seven direct controls showed complete publication and shared-consumer survival as positive cases, while late completion after edit, a partial generation, wrong echo, timeout, and a lost watcher event left the pointer unselected. The controls are deliberately small and do not claim full state-space coverage beyond the stated bound. Basis: **execution** of the finite model.

### One-fence mutation controls

Each row removes one check or changes one cancellation rule. Breadth-first order makes the retained schedule the shortest within this graph and action ordering; it is not a shortest real-system execution.

| Mutant | Shortest failing schedule, abbreviated | Violation |
| --- | --- | --- |
| No revision fence | start → revision bump → all three pieces → deliver | Old revision selected. |
| No digest fence | start → same-revision digest replacement → pieces → deliver | Different bytes under reused revision selected. |
| No generation fence | start → regenerate same source → pieces → deliver | Old stage generation selected. |
| No worker fence | start → worker restart → pieces → deliver | Old worker result selected. |
| No RPC fence | start → RPC reconnect → pieces → deliver | Old session response selected. |
| No owner fence | start → last owner cancels → pieces → deliver | Unowned result selected. |
| No status fence | start → pieces → fail → late deliver | Failed job selected. |
| No completeness fence | start → deliver | Empty generation selected. |
| No echo fence | start → pieces → wrong-echo deliver | Misattributed result selected. |
| No reconciliation | start → external edit with lost notice → pieces → deliver | Watcher-maintained old identity selected against changed authoritative input. |
| Cancel on any owner | start → join second owner → cancel first | Shared job killed while one owner remains. |

The first ten mutants each found an invalid publication. The cancellation mutant found an ownership violation before publication. State counts ranged from 72,060 to 107,870 and checked-edge counts from 285,605 to 403,466. The full schedules, failed predicate names, and pre/post states remain in `results.json`. This shows that the fixture is sensitive to each intentionally removed condition and distinguishes the failure modes; it does **not** prove all conditions are minimal for a real engine. For example, a stronger epoch or immutable snapshot token could encode several fields together. Basis: **execution** for the counterexamples; **derived** for architectural interpretation.

### Controlled subprocess replay

[`support/replay.py`](support/replay.py) loaded the unchanged `probe.py` from `anneal-3730-snapshot-capture-jobs-2026-09-29` and invoked its `start_stage`, `finish_stage`, and `Engine` functions. The existing backend launched two real Python child processes, each paused on its own gate. The old request had epoch 1 and model/source A. A new request with changed model/source B advanced the engine to epoch 2. The new gate was released first and its complete structured result published; the old gate was released afterward and its successful, semantically different result was classified `stale-generation`. Last-completion-wins would have selected the old digest. The raw request echoes, child stdout/stderr, exit codes, process IDs, dispositions, and digests are in [`support/replay-results.json`](support/replay-results.json).

This is a causally gated **execution** of the fake subprocess adapter, not an Anneal replay. It supports the narrow claim that the previously recorded fake adapter applies its epoch fence after actual late completion. It does not validate the model's other predicates against real subprocess, OS cancellation, or compiler behavior.

### Issue coverage and simple alternative

This informs [issue #3731](https://github.com/google/zerocopy/issues/3731) I005/I007 and I133–I135 by making ownership and acceptance rules executable, exhausting a stated finite graph, and replaying one schedule with gated subprocesses. It gives only symbolic slices of I105–I112: cancellation is subscriber removal, failures are state labels, restart increments an epoch, and lost watcher delivery is modeled as observed state lag. It does not perform the OS, resource, deadlock, fairness, or crash-reconstruction experiments those items request. For I159, the simpler alternative “trust observed state and last successful result” fails under the preserved external-edit and late-output schedules; a simpler one-shot scheduler with these fences remains viable under the bounded model. This is a **derived design constraint**, not an adopted Anneal architecture.

## Boundaries

- **Not examined:** actual Anneal orchestration, Charon/Aeneas/Lean stages, real Lake artifacts, proof propositions, obligation coverage, or Rust-to-Lean soundness. The model's digests are symbolic `A`/`B` values.
- **Not examined:** descendant process cleanup for I105, locks/deadlocks for I108, OS time/memory/disk exhaustion for I109, crash-state reconstruction for I110, edit-storm fairness for I111, or real watcher/transport loss for I112. A state label is not an OS fault injection.
- **Not established:** unbounded safety, liveness, starvation freedom, optimal scheduler design, a minimal identity tuple, or production conformance. The graph is finite and the reference predicate and implementation share one source file.
- **Not established:** that a pointer change is crash durable or that consumers pin a coherent multi-file generation. The model's publication is one abstract atomic action; the adjacent APFS fixture studies one concrete pointer-read hazard separately.
- **Known scope of replay:** the subprocess adapter checks its own epoch and semantic echo, but not every model fence. It changes source and model together; it is an analog of the stale-completion schedule, not a step-for-step replay of symbolic `bump_revision`.

## Evidence

- Executable model [`support/model.py`](support/model.py), SHA-256 `aa91033fd3965c7da9e79dfd933c2d614bd4845c720e9007a07441135d9e37fa`; machine results [`support/results.json`](support/results.json), SHA-256 `fcc130e4f9dc3e4b7a33899f81b0559e3f4e4fb6f486db969d9f468054d04d72`.
- Replay script [`support/replay.py`](support/replay.py), SHA-256 `d97040b0f59fc94a9c6d756b26fe4584ecea5b06b72a2ed9e421543d3fe3d81d`; transcript [`support/replay-results.json`](support/replay-results.json), SHA-256 `f7252d7c603b8dcf148deac516e2a2997a456de9e5cdc82bfd0479f89c80a85a`.
- Reused harness [`../anneal-3730-snapshot-capture-jobs-2026-09-29/support/probe.py`](../anneal-3730-snapshot-capture-jobs-2026-09-29/support/probe.py), SHA-256 `fb1a7cbdff9cdb7b66a0f36234756af52c4862508dc5010735d4263d5a1995da`, was read and called without changing its package. Its own report gives the fake-stage protocol and prior late-completion result.
- Primary scope source: [google/zerocopy issue #3731](https://github.com/google/zerocopy/issues/3731), especially I005/I007/I105–I112/I133–I135/I159, viewed 2026-09-29. Its agenda does not adopt this model as implementation.

## Revalidation

From this package run `python3 support/model.py` and inspect its asserted baseline, all eleven mutation counterexamples, and seven direct control traces. Run `python3 support/replay.py` to start the two gated child processes; verify new-first publication, old-late rejection, and distinct semantic digests. Revalidate exact file hashes before comparing runs. For actual Anneal conformance, adapt the schedule to real stage APIs and capture source/import/proof identities, process descendants, and selected complete artifacts; compare every accepted claim with a fresh proof oracle. Expand the model bound or use a separate formalization before making claims about longer schedules.
