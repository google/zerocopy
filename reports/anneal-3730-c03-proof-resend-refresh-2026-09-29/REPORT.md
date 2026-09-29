# Resending a proof does not refresh its imported Lean artifact in one pinned worker

## Summary

In a direct Lean 4.30.0-rc2 server, an open proof continued to return `no goals` after its imported `Dep.olean` and `Dep.lean` changed from `selected = 7` to `selected = 9`. Watched-file notifications, resending identical proof text as document version 2, and appending a newline as version 3 did not refresh that worker's imported environment. Closing/reopening the URI and starting a fresh server exposed `⊢ selected = 7` with an `rfl` error. Fresh batch Lean exited 1 with the same mismatch. This supplies the missing proof-resend cell for #3730 C03, so C03's v22 `complete` classification is too broad for its enumerated refresh matrix.

## Applicability

The fixture used the cached Lean executable at revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` with two separately compiled valid `Dep.olean` files. The open `Proof.lean` text stayed `theorem checked : selected = 7 := by rfl`; the selected `.olean` was replaced with the variant defining `selected := 9`, and `Dep.lean` was updated to the matching source. The language server was launched as direct `lean --server` with one private `LEAN_PATH` and one file worker. Both Lean builds and all server/batch processes ran inside a macOS `sandbox-exec` profile that denied network access. All inputs and outputs were under a private Meta Data scratch root except the retained result JSON.

The [earlier three-launch-mode matrix](../anneal-3730-lean-launch-refresh-matrix-v4-30-0-rc2/REPORT.md) already tested watcher notification, new file, close/reopen and fresh server. Its probe defined a `didChange` helper but did not call it after the imported change. This report reuses only that prior package's LSP client class by compiling selected AST nodes; it does not import or rerun the prior package's module-level probe. An initial unsafe import attempt did execute the prior probe and failed under the sandbox; the prior tracked files were restored from HEAD before this retained experiment. The [invalid first result](support/attempt1-invalid-path.json) is kept because it revealed an incorrect artifact path and did not provide usable refresh evidence.

## Findings

| Phase | Exact result |
| --- | --- |
| Initial artifact 7, proof version 1 | `no goals`. |
| Artifact/source replaced with 9 and both watched-file notifications sent | Existing worker still `no goals`. |
| Same proof bytes resent as version 2; `waitForDiagnostics` returned `{}` | Existing worker still `no goals`. |
| One appended newline sent as version 3; wait returned `{}` | Existing worker still `no goals`. |
| Same URI closed and reopened at version 1 | Goal `⊢ selected = 7`; diagnostic `Tactic rfl failed`. |
| Fresh server and fresh batch on the same selected artifact 9 | Fresh server gave the same open goal/error; batch exited 1 and evaluated `selected` as 9. |

The A and B OLean SHA-256 values differ and are retained in [results.json](support/results.json), along with both source hashes, the proof hash, raw 86-event client/server transcript, waits, diagnostics, goal replies and batch output. The existing worker's local success was stale relative to the selected imported artifact. A document version increment and a proof-text edit did not prove imported-environment freshness in this schedule. **Basis: execution.**

## Boundaries

This is one direct-server worker, one imported definition, and one artifact replacement. It does not cover `lake serve`, `lake env lean --server`, transitive imports, plugins, options, an explicit dependency-refresh API, a supervisor killing and replacing only the file worker, or a new workspace generation. It does not establish a universal refresh rule for all Lean versions or Anneal. The batch proof fails intentionally; its output is the fresh oracle for this specific changed import, not a verification success. The source-only and different launch-mode controls remain in the earlier report.

The sandbox denied network operations; this report did not test network attempts. The initial invalid-path acquisition had an unknown-module diagnostic and was excluded from the retained comparison.

## Evidence

- [Probe](support/probe.py), [raw result](support/results.json), [offline checker](support/check.py), and [invalid first attempt](support/attempt1-invalid-path.json).
- Cached Lean executable SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; probe SHA-256 is recorded in `REPORT.json`. No dependency was fetched or installed.
- The source #3730 C03 question is frozen in the [v22 issue snapshot](../anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support/issue-scope-snapshot.json).

## Revalidation

Run `python3 support/check.py` for the retained evidence. To reacquire with the cached Lean pin, create an empty private scratch directory and run `sandbox-exec -p '(version 1)(allow default)(deny network*)' python3 support/probe.py --scratch <empty-private-directory>`; this overwrites only this package's `support/results.json` and writes temporary compiler artifacts under the supplied scratch directory. Compare result hashes, versioned wire sequence, goal/diagnostic split, and fresh batch exit before reinterpreting C03.
