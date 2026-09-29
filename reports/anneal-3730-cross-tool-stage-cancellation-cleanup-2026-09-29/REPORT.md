# Cross-tool CLI cancellation, descendant cleanup, retry, and a synthetic fence

## Direct component trials

Eight sequential private-output trials launched actual pinned CLIs in new process groups: Cargo, Charon, Aeneas, Lake, and Lean at the invocation boundary, then delayed cold Cargo, Charon, and Lake controls after 80 ms. After process launch, the harness sent `SIGSTOP` to the group, inspected its members with `ps`, sent `SIGKILL` to the group, waited for the parent, checked the group and recorded PIDs again, inventoried the output, and retried the same command in the same private directory. Every stopped process exited `-9`; every recorded group and PID was absent after cancellation; all eight retries exited 0.

The invocation-boundary controls stopped only the CLI leader and left no output files. The delayed Cargo control stopped `cargo` and `rustc` with six partial target files. Delayed Charon stopped `charon`, `cargo`, and `charon-driver` with no destination LLBC in this run. Delayed Lake stopped `lake` with one build-tree file. These differences show that cancellation can leave stage-specific partial state before a retry. The observed same-directory retries yielded 43 Cargo target files, parseable Charon `app_closure` LLBC, three Aeneas Lean source files, and a Lake `Probe.olean`. The direct Lean `--json` retry exited 0 with no file artifact. Representative successful Cargo metadata, LLBC, Aeneas source, and `.olean` files are retained under `support/artifacts/` with SHA-256s in `support/results.json`.

This is **component CLI evidence**, not an Anneal pipeline. The stages used independent tiny fixtures and did not pass the Charon output to Aeneas or the Aeneas output to Lake. The signals were delivered to process groups that existed in the observed snapshots; they do not prove cleanup of a future daemonized child that escapes the process group, a watcher, or a remote worker. The delayed cases use an 80 ms wall-clock barrier, not a particular compiler phase marker. Aeneas and direct Lean were stopped only at launch, so no in-flight child or partial-output claim is made for those tools.

## Synthetic generation fence

`support/fence_oracle.py` is a separate **model** using the successful CLI inventory digests as payload identifiers. For each of eight stage labels, it makes generation 2 current, offers a late result from cancelled generation 1, verifies the pointer bytes do not change, then accepts generation 2 through a temporary JSON file and `os.replace`. All eight late results were rejected in `support/fence-results.json`. This tests the model's comparison rule and local atomic pointer replacement only. No actual CLI callback or Anneal scheduler/API passed through the fence; no crash-durability guarantee follows from the exercise.

## Issue coverage and residuals

This package adds bounded evidence for [#3731](https://github.com/google/zerocopy/issues/3731) I073–I080, I105 and I134 and related [#3730](https://github.com/google/zerocopy/issues/3730) cancellation/publication crosswalk rows.

| Rows | Added evidence | Remaining boundary |
| --- | --- | --- |
| I073–I074 | Private source, target, and output roots for actual Cargo/Charon and explicit fixture identities. | Saved-versus-unsaved overlay fidelity and complete path/build-script/proc-macro closure are addressed elsewhere only within fixture limits; this cancellation package does not test overlay equivalence. |
| I075–I076 | Charon retry produced a parseable output with checked crate name in a private target. | Warm Cargo omission, multi-unit collisions and complete production compilation-unit keys remain outside this run. |
| I077 | Fresh Charon process after stop/kill succeeded. | Same-process Charon library reset and A/B/A after cancellation remain untested. |
| I078 | No output at the two Charon stop points; same-destination retry produced a parseable LLBC. | Output-write-phase interruption, completeness proof, and atomic last-good publication require the separate output-phase evidence and a real wrapper. |
| I079 | Tool and fixture hashes plus successful artifacts retained. | LLBC normalization and source metadata across semantic variants/revisions were not exercised here. |
| I080 | Delayed Cargo/Charon child groups were observed and cleared; partial private target files were retried. | Shared targets, parallel snapshots, peak resource use and daemonized descendant cleanup. |
| I105 | Five actual CLI launch-boundary cancellations plus three delayed cold controls; group/PID absence and retries. | Per-phase active cancellation for Aeneas/Lean, richer Lake phases, graceful cancellation, timeout escalation, external workers and Anneal lifecycle state. |
| I134 | Eight modelled late-result rejects tied to CLI output digests. | Real concurrent request/worker identities, causal barriers, edits/rebuilds and cross-tool publication through an Anneal scheduler. |

## Reproduce and verify

The probe uses a 15 GiB free-disk guard, one Cargo job, one Lean thread, private directories, at most one CLI trial at a time, and a 60-second retry timeout. No installation or network access is required for the pinned local tools and offline Cargo fixture. From this package directory:

```sh
python3 support/probe.py --work /Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/r17-replay-new
python3 support/fence_oracle.py --work /Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/r17-fence-replay-new
python3 support/verify.py
```

Each `--work` path must be absent and owned for that replay. The first command overwrites retained successful artifacts and results; the second requires the new results. The verifier checks retained process observations, artifact hashes, parsed Charon identity, and synthetic fence invariants without relaunching any CLI. Child timing and partial-file counts can vary on replay.
