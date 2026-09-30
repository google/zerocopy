# Lake-launched nested constructor and `have` goal positions

## Summary

One pinned Lean/Lake 4.30.0-rc2 server returned matching `$/lean/plainGoal` and `Lean.Widget.getInteractiveGoals` goal categories and displayed contexts at 13 exact positions in a successful imported proof. `constructor` exposed two goals, the first bullet selected the left goal, an inner `have ... := by` proof exposed its own equality goal, and the following outer `exact` saw the new `hz` hypothesis. The second bullet selected the right `True` goal. Three positions had empty goal lists and EOF returned null. A fresh batch process accepted the same source text and reported no theorem axioms.

This is a bounded component result for #3731 I043 and #3730 C02. It combines a local Lake import, a branched/nested proof, and both goal APIs. It does not establish Anneal source projection or rich RPC reference lifecycle behavior.

## Applicability

The subject is installed `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` Lean/Lake 4.30.0-rc2 on macOS arm64. The local `probe_dep` package defines `depValue : Nat := 7`; `position_probe` imports `Dep` and proves `(depValue = 7) ∧ True` from `h : depValue = 7`. The proof runs `constructor`, uses an inner `have hz : depValue = 7 := by exact h` in the left bullet, closes that bullet with `exact hz`, and closes the right bullet with `trivial`. The exact source opened in the Lake server matched the on-disk proof; a separate fresh batch file contained identical source bytes under the same prepared import but had a different filename.

The clean Lake build and `lake --no-cache setup-file Proof.lean` prepared and identified the local `Dep.olean`. One `lake --no-cache serve` process opened document version 1, completed `textDocument/waitForDiagnostics`, then answered 13 sequential plain/rich query pairs through one RPC session. The positions are zero-based UTF-16 coordinates. No document edit, worker restart, or RPC reconnect occurred.

The probe used installed local tools only, `LEAN_NUM_THREADS=1`, `LAKE_NO_NET=1`, an empty test home/cache, and `/usr/bin/sandbox-exec` with network denied. Immediate preflight observed 25.74% reclaimable memory and 24,636,727,296 free disk bytes. Across 27 samples during a 5.79-second run, process-group RSS reached at most 808,208 KiB. The guard enforced a sampled 1.5 GiB cap and a five-minute wall deadline; its samples cannot exclude a shorter transient peak.

## Findings

| Position in `Proof.lean` | Zero-based `(line, character)` | Plain and rich result |
| --- | ---: | --- |
| Before `constructor` | `(3,2)` | One outer goal, `h : depValue = 7 ⊢ depValue = 7 ∧ True` |
| End of `constructor` and first bullet marker | `(3,13)`, `(4,2)` | Two goals: `case left ⊢ depValue = 7` and `case right ⊢ True` |
| Start of outer `have` | `(4,4)` | Left goal only |
| Inner `by` and start of `exact h` | `(4,30)`, `(5,6)` | Inner equality goal, without a case label |
| End of inner `exact h` | `(5,13)` | Empty goal list |
| Outer `exact hz` start | `(6,4)` | Left goal with `h hz : depValue = 7` |
| End of outer `exact hz` | `(6,12)` | Empty goal list |
| Second bullet and `trivial` start | `(7,2)`, `(7,4)` | Right goal, `h : depValue = 7 ⊢ True` |
| End of `trivial` | `(7,11)` | Empty goal list |
| EOF after `#eval` | `(10,0)` | JSON null |

At all 13 positions, both APIs agreed on goal availability and goal count: nine positions had one or two goals, three had empty lists, and one returned null. The rich goal `userName`, displayed target, and hypothesis names/types matched each corresponding plain goal; two positions exposed both left and right goal objects. The case label disappears at the inner `by` position, then the outer left case resumes with `hz` available. These are exact selection results for this source and cursor grid, not a universal rule for all nested syntax. **Basis: execution**, `support/results.json` retains 26 requests and replies and `support/check.py` checks every position and displayed context.

The clean build and setup-file exited 0, with `Dep.olean` in the local import artifacts. A fresh `lake --no-cache env lean --json Batch-nested.lean` exited 0 and emitted informational results that `nested` depends on no axioms and `depValue` evaluates to 7. The live diagnostics contained only information messages and no errors; the server shut down with exit 0. Batch success is a whole-file control for this exact text, separate from local position guidance. **Basis: execution**, retained build, setup, batch, diagnostics and ordered server events.

## Boundaries

- This is one hand-written Lean theorem with a constructor, two bullets and one inner `have`. It does not sample combinator branches, macro expansion, changed whitespace, malformed syntax, unsaved edits, term-proof positions or a broad cursor grid.
- The two APIs were compared for goal count and displayed names/types/targets. Opaque rich RPC `ctx`, `info`, and `mvarId` dereference or expiry, worker restart/reconnect, RPC reconnect, widget actions and simultaneous clients were not tested. The retained events are a single successful protocol run, not lifecycle coverage.
- The fixture does not use an Anneal launcher, generated/projected proof, Rust annotation source map, editor/MCP transport, or exact-version/import fence. It does not close I043/C02's product gate.
- The batch file and opened proof contain identical source text but have different filenames. Their successful elaborations under the same local import do not establish equal module identity for arbitrary files.
- Sampled RSS and admission checks bound the observed run, not instantaneous physical memory or representative product workloads.

## Evidence

- `support/probe.py` creates the local packages, runs a clean build, setup and fresh batch, launches one Lake server, queries both APIs at 13 fixed positions, records ordered protocol events, samples process-group RSS, and stops the server. It uses Python's standard library and installed pinned binaries without download or installation.
- `support/results.json` retains normalized exact commands and outputs, source text and hashes, artifact digests, complete plain/rich replies, diagnostics, resource readings and cleanup. `$WORK`, `$WORK_URI`, and `$TOOLCHAIN` replace local absolute paths in retained text.
- `support/fixture/Dep.lean` and `support/fixture/Proof.lean` retain the exact source bytes. `support/check.py` checks them, the pinned binary hashes, import/batch oracles, all 13 plain/rich pairs, diagnostics, guards and clean shutdown offline.
- The recorded Lake and Lean binary SHA-256 values are `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` and `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The retained probe/result SHA-256 values are `1ef7547483edd5cf5830a62f1275c7fd356ad8fd50e76d5484a7f235a3f9dc43` and `821402691c13066d19146d766eae67666c2ce3c018e208aa5e640d80bbefa881`.

## Revalidation

Run `python3 -B support/check.py` from this package to verify the retained result without starting Lake or Lean. To repeat on the same installed pin under the stated resource gates, run `python3 -B support/probe.py --work /new/absent/private/path --output /new/results.json`, then compare the binary/source digests, build/setup/batch outcomes, all 13 exact position categories and contexts, diagnostics, and server shutdown. A later toolchain or Anneal-generated proof requires a new subject-specific run; product coverage also needs the launcher, source map, exact-version/import fence and lifecycle controls.
