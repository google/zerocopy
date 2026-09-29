# Two scratch writers, crash boundaries, and pinned-generation recovery

## Prototype and direct Lean work

This extends the preceding I070 scratch-candidate **contract prototype**. Two separate local client processes copied the same canonical proof/import snapshot, ran pinned Lean 4.30.0-rc2 `lean --json` on different valid tactic candidates, and waited at one process barrier. Each then attempted a file-lock-protected CAS against the same `CURRENT.json` pointer. Exactly one candidate published generation 2; the other observed the changed proof preimage and was rejected as `stale_proof`. The winner is nondeterministic; the retained run names it in `support/results.json`. No loser bytes became canonical.

Canonical generations are immutable directories containing `Proof.lean`, `ProbeEnv.lean`, compiled `ProbeEnv.olean`, and a complete manifest with their hashes and Lean binary identity. The only active-generation selection is an `os.replace` of a temporary `CURRENT.json` pointer after a full generation is written. Recovery validates that the pointer targets a complete manifest and that every listed file matches its hash, then runs a fresh batch Lean check.

## Crash boundaries and controls

Four child processes used `os._exit` at explicit boundaries:

| Injected process exit | Retained recovery result |
| --- | --- |
| 71 after candidate materialization | Pointer remained on complete generation 2; fresh batch check passed. |
| 72 after candidate Lean check | Pointer remained on complete generation 2; fresh batch check passed. |
| 73 after a complete next generation was written, immediately before `CURRENT` replacement | Pointer remained on generation 2; the complete orphan generation was ignored. Its manifest is retained under `support/artifacts/`. |
| 74 immediately after `CURRENT` replacement | Pointer selected the new complete generation 3; fresh batch check passed despite the publisher's exit. |

After those trials, a batch-successful candidate whose proof was modified after checking was rejected as `candidate_proof_mutated`; changing the copied import source after checking was rejected as `candidate_import_mutated`. A separate reader process opened the old `Proof.lean` before another valid candidate published generation 4. It then read the old bytes and verified the old path still existed. The final pointer targeted generation 4, and fresh Lean batch checking succeeded. The old generation was deliberately retained; no garbage collection or lease reclamation algorithm was tested.

The retained run had five generation directories: bootstrap, the competing writer's winner, a complete pre-swap orphan, a post-swap accepted generation, and the final accepted generation. The package stores initial/final source snapshots plus orphan/final manifests; `support/verify.py` checks them against the transcript.

## [#3731](https://github.com/google/zerocopy/issues/3731) row coverage and residuals

| Rows | Added evidence | Remaining boundary |
| --- | --- | --- |
| I014 | Two real local client processes and Lean checks crossed a barrier; one CAS winner and one stale loser. | Four writers, actual Anneal workspace ownership/fork controls, cross-host contention and full lost-update matrix. |
| I070 | Candidate proof/import mutation rejection and fresh batch check after accepted CAS. | Elaborated target/assumption/axiom comparison, real Rust annotation provenance, Anneal scratch service and authority model. |
| I105 | Four prototype publisher process exits at controlled boundaries. | Actual Lean worker cancellation during elaboration and cross-tool process groups; the preceding CLI report covers narrower stage controls. |
| I110 | Recovery from process exits before/after pointer replacement, with authoritative file hashes and fresh Lean check. | Actual server/watchdog/Anneal process restart, filesystem durability and lost-event reconstruction. |
| I121 | A live reader kept access to an old immutable proof across a pointer swap. | GC leases for later opens, pending queries and scratch forks; safe reclamation was not attempted. |
| I134 | Causal barrier and process IDs for two Lean-backed candidate clients. | Actual in-flight Charon/Aeneas/Lake rebuild/edit interleavings and an Anneal scheduler's request/worker identities. |

This is a **local prototype**, not an Anneal service. `os._exit` simulates process failure at named source-code boundaries; it is not power-loss, disk-flush, kernel-crash, or atomic-directory durability evidence. The Python file lock and JSON pointer are not a production distributed transaction.

## Replay and verification

With the pinned Lean binary already available, run from this package directory:

```sh
python3 support/probe.py --work /Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/r26-replay-new
python3 support/verify.py
```

The work path must be absent and owned. The probe uses at most two concurrent Lean-backed clients, one Lean thread per process, a 15 GiB free-disk guard, and 20-second Lean command timeouts. It overwrites this package's retained results/artifacts. The verifier reads the retained evidence without launching Lean. Client winner and generated names may vary on replay; the one-winner and recovery invariants must hold.
