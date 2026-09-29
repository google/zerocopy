# Imported-generation refresh behavior across Lean 4.29 and 4.30-rc2

## Summary

The direct `lean --server` imported-generation probe produced the same old/new-document contrast under Lean 4.29.0 and Lean 4.30.0-rc2: an already-open proof document continued to report “no goals” after its imported `.olean` changed; a newly opened or closed/reopened document in the same server process reported the remaining goal; fresh batch Lean failed on the same proof text. In both versions, a second old-document query after the new document was ready and a further 0.5-second delay still returned “no goals.”

This is a two-version, one-launch-mode comparison. It shows that the observed behavior is present in both pinned binaries, not that every refresh path or later toolchain has the same behavior.

## Applicability

- Lean 4.29.0: `leanprover/lean4@98dc76e3c0a9b856c9b98726b713fb04fab16740`; local executable SHA-256 `2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37`.
- Lean 4.30.0-rc2: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`; local executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`.
- Both runs use direct `lean --server`, `LEAN_PATH` set to a local module directory, one imported definition, `LEAN_NUM_THREADS=1`, `textDocument/waitForDiagnostics`, and `$/lean/plainGoal`.
- This package now retains fresh 4.29 and 4.30 runs using byte-identical copies of the same script, including the delayed old-document query. The earlier, separately preserved `lean-same-server-dependency-generation-v4-30-0-rc2` report supplies an independent 4.30 core-sequence observation without that extra query.

## Findings

### Both binaries retained stale imported state in an existing worker

In both runs, the proof `sharedValue = 3 := by rfl` initially produced no goals with `Dep.olean` built from `sharedValue := 3`. After rebuilding that artifact from `sharedValue := 4`, the old open document still returned no goals. Each new artifact hash differs from its own old hash in the transcript; both old and new artifacts are retained per version, while the proof bytes remained identical.

An identical newly opened document in the same server process reported `⊢ sharedValue = 3` and an `rfl` diagnostic. After that document's readiness barrier and an additional 0.5-second wait, a fresh readiness request and goal query on the still-open original document again returned no goals in **both** versions. Closing and reopening the original URI produced the remaining goal. Batch Lean exited 1. The earlier independent 4.30-rc2 report records the same immediate contrast. The transcripts do not record child process PIDs; “worker” identifies the server's per-document elaboration behavior, not a separately attested process identity.

Basis: **execution** in `support/v429/transcript.json` and `support/v430/transcript.json`. The linked earlier 4.30-rc2 report independently supports the core old/new-document contrast.

### The cross-version result supports a conservative refresh boundary, not a universal rule

For these two direct-server binaries and the same minimal fixture, opening a new document or closing/reopening the old one loaded the rebuilt import while leaving the server process alive. Document URI/text/version alone did not reveal that the old document retained its prior environment. A consumer should bind query results to imported-environment and worker generation, or use a refresh transition shown reliable for its exact server mode. The experiment does not establish a complete minimal identity tuple.

Basis: **derived** from two pinned executions.

## Boundaries

- Only Lean 4.29.0 and 4.30.0-rc2 were examined. No 4.31 candidate or broader upgrade matrix was run.
- Both runs use direct `lean --server`; they do not compare `lake serve`, `lake env lean --server`, or `lake setup-file` behavior.
- The imported source and artifact change together. No valid different artifact from byte-identical source/configuration was produced.
- The fixture has one imported definition and two open proof documents. It does not identify worker child PIDs or test many open proofs, rich InfoView RPC handles, same-document concurrent requests, plugins, Mathlib, crashes, or resource scaling.
- The 0.5-second delayed old-document query ran under both pins. Timing and a readiness reply do not establish all possible filesystem-watch processing semantics, nor prove that the notification itself caused or failed to cause a refresh.
- This does not establish that every Lean release or every editor notification sequence requires close/reopen. It records the behavior observed under these exact subjects and procedure.

## Evidence

- `support/v429/probe.py` and `support/v430/probe.py` — byte-identical direct-server procedures with delayed-query control. They acknowledge server-initiated JSON-RPC requests before matching client replies.
- The probe scripts generate the fixture at run time; their SHA-256 digests in `REPORT.json` identify that procedure. The two Lean revisions and executable hashes identify the observed toolchains.
- `support/v429/transcript.json` and `support/v430/transcript.json` — versions, artifact hashes, LSP messages, goals, diagnostics, and batch exits.
- `support/v429/fixture/` and `support/v430/fixture/` — final proof sources and each version's pre/post-rebuild `Dep.olean` artifacts.
- `support/check.py` — read-only checks of both retained runs, exact local binary/script identities, proof text in the open messages, URI/version-bound goal exchanges, delayed queries, and the earlier independent 4.30 transcript.
- `lean-same-server-dependency-generation-v4-30-0-rc2/REPORT.md` — the paired v4.30-rc2 observation.

Issue alignment: partial evidence for #3730 C03–C05 and #3731 I049, I131, I147, I158, and I159 N03. The related rows in the coverage audit retain their other untested dimensions.

## Revalidation

Run `python3 support/check.py` from the package directory to validate the retained evidence without changing it. To replay each version, set `LEAN_BIN` to that version's exact executable:

```console
LEAN_BIN=/absolute/path/to/lean-v4.29.0/bin/lean python3 support/v429/probe.py
LEAN_BIN=/absolute/path/to/lean-v4.30.0-rc2/bin/lean python3 support/v430/probe.py
```

Each script rebuilds only its own fixture and transcript in place, including `Dep.old.olean`; the executable hashes in `REPORT.json` distinguish the pins. Compare the two outputs and the earlier v4.30-rc2 report while preserving launch mode and separate artifact hashes. Re-run against another Lean/Lake tuple only as a separate subject, and do not generalize from version adjacency.
