# Lake-launched unsaved macro and error goal positions

## Summary

In one pinned Lean/Lake 4.30.0-rc2 server, `$/lean/plainGoal` and `Lean.Widget.getInteractiveGoals` returned the same goal, empty, or null category at 20 paired positions across four versions of an imported proof. The disk file stayed valid while the open buffer changed from a solved tactic macro to an unresolved placeholder, a syntax error, and back to the valid text. At the syntax-error version, one position returned *no goals* even though the current buffer failed the fresh batch check. A local empty goal list therefore cannot serve as a whole-file verification result.

This adds a Lake-launched import plus unsaved macro/error combination to the direct Lean macro and recovery controls and the prior valid-only Lake position grid. It gives bounded component evidence for #3731 I043 and #3730 C02, not an Anneal product integration result.

## Applicability

The observed subject was the installed macOS arm64 Lean and Lake `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` toolchain. The local `probe_dep` package defined `depValue : Nat := 7`; the `position_probe` package imported `Dep` and declared a tactic macro `solve_macro term` expanding to `exact term`. The valid theorem proves `depValue = 7` from an `h : depValue = 7` hypothesis. A clean local Lake build prepared both packages; `lake --no-cache setup-file Proof.lean` named the compiled `Dep.olean` import.

The proof file on disk remained the valid source. Full-text LSP `didChange` notifications supplied versions 2–4 to the same URI and server. Separate fresh `lake --no-cache env lean --json Batch-*.lean` processes checked the exact solved, unresolved, and syntax-error bytes against the prepared local import. Every live version completed `textDocument/waitForDiagnostics` before position queries. One RPC session served the rich calls. Positions are zero-based UTF-16 coordinates; this fixture is ASCII.

The probe used the already installed binaries, `LEAN_NUM_THREADS=1`, `LAKE_NO_NET=1`, an empty test home/cache, and `/usr/bin/sandbox-exec` with network denied. The immediate resource preflight observed 22.41% reclaimable memory and 36,792,500,224 free disk bytes. Its monitor sampled the probe and server process groups 40 times in 8.8 seconds, observed at most 830,720 KiB RSS, and enforced a 1.5 GiB sampled cap and five-minute wall deadline. This sampled maximum cannot rule out a shorter transient peak between samples.

## Findings

| Open-buffer version | Fresh batch for these bytes | Incoming `(4,2)` | Macro body `(4,8)` | Later `(4,16)` / `(5,0)` | EOF `(5,2)` | Final live errors |
| --- | --- | --- | --- | --- | --- | --- |
| 1 solved, `solve_macro h` | Exit 0 | One `h : depValue = 7 ⊢ depValue = 7` goal | No goals | No goals / no goals | Null | 0 |
| 2 unresolved, `solve_macro ?_` | Exit 1 | Same goal | Same goal | Same goal / same goal | Null | 2 |
| 3 syntax error, `solve_macro )` | Exit 1 | Same goal | No goals | Null / null | Null | 1 |
| 4 restored, `solve_macro h` | Same bytes as version 1 | Same goal | No goals | No goals / no goals | Null | 0 |

Both query APIs gave the same category for all 20 pairs: seven one-goal pairs, seven empty-list pairs, and six null pairs. In each one-goal pair, the rich RPC hypothesis name and displayed type and target rendered to the corresponding plain goal. The syntax-error version's empty result at `(4,8)` coexists with an `unexpected token ')'` diagnostic and a failing fresh batch. Its empty result is local position selection, not a proof-completion signal. The unresolved version retained a goal through the next line and produced placeholder and unsolved-goal errors. **Basis: execution**, retained wire events, four diagnostic versions, and three separate batch outputs in `support/results.json`.

The clean build exited 0 and reported `Built Dep` and `Built Proof`; `setup-file` pointed to the local dependency OLean. The fresh solved batch exited 0. The server's three full-text changes, 40 goal requests and matched replies, and orderly shutdown all completed without a protocol error. **Basis: execution**, build/setup/batch outputs and ordered events in `support/results.json`. The checker verifies the retained identities, fixture bytes, exact positions, goal categories and displayed contexts, diagnostics, resource readings, request/reply count, and shutdown.

## Boundaries

- This is one hand-written imported Lean theorem and one simple tactic macro. Its five positions per version lie on a flat, single-goal tactic line or just after it. This run does not test nested goals or tactics, tactic combinators, changes to whitespace positions, nested macro expansion, or positions inside term proofs. It did not call `plainTermGoal`. Separate direct-Lean and valid-only Lake reports cover some of those position classes under different fixtures; they do not make them observations of this combined Lake/unsaved/macro cell.
- The two APIs were compared for availability, goal count, and displayed hypothesis/target text. Opaque RPC `ctx`, `info`, and `mvarId` reference lifetime, dereference behavior, expiry, and widget actions were not tested. The run used one worker and one initial RPC connection: it did not restart or reconnect the worker, reconnect RPC, or challenge reference use after either event.
- This run did not use an Anneal launcher, generated or projected proof document, Rust annotation source map, or integrated editor/MCP transport. It cannot establish which authored position maps to the queried Lean position in that product.
- `waitForDiagnostics` indicates elaboration readiness for a version, not whole-file success. The fresh batch files have the same source text as each buffer variant but different filenames from the open `Proof.lean`; this is a source-text oracle under the same prepared import, not an assertion of identical module identity.
- The server was queried sequentially after each version's readiness response. The experiment does not test late responses, an exact-version query fence, multiple imported modules, plugin loading, or cross-version toolchain behavior.
- The process monitor used periodic RSS samples. Its successful cap observation does not prove an unsampled instantaneous memory maximum.

## Evidence

- `support/probe.py` creates the local packages, invokes clean build/setup and separate batch controls, opens the proof through one Lake server, sends versioned full-text edits, queries both APIs at five exact positions per version, records every protocol event, and measures resources. It requires only installed local tools and Python's standard library; it does not download or install anything.
- `support/results.json` preserves the normalized full commands and outputs, source text and artifact digests, complete plain/rich replies, diagnostics, 40 requests and their replies, preflight and sampled process-group memory, and clean shutdown. `$WORK`, `$WORK_URI`, and `$TOOLCHAIN` replace local absolute paths in retained text.
- `support/fixture/Dep.lean` and `support/fixture/Proof.lean` preserve the exact dependency and on-disk proof bytes. The other buffer variants are preserved in `support/results.json`.
- `support/check.py` checks the retained evidence offline and printed: `PASS: Lake import, batch controls, 20 plain/rich unsaved macro/error pairs, diagnostics, resource bounds, shutdown`.
- The recorded Lake and Lean binary SHA-256 values are `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` and `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, respectively.

## Revalidation

Run `python3 -B support/check.py` from this report package to verify the retained observations without starting Lean or Lake. To reacquire the cell with the same installed toolchain, run `python3 -B support/probe.py --work /new/absent/private/path --output /new/results.json` under the stated resource gates, then compare source and binary digests, build/batch exits, all exact position categories and displayed contexts, diagnostics, and shutdown. Treat a later Lean/Lake release or an Anneal-generated proof as a new subject. The remaining I043/C02 product question calls for paired plain/rich queries through the actual Anneal launcher and generated source map, including before/after, nested-goal, combinator, whitespace, macro/error, term-proof, and EOF positions as applicable to the generated proof. It also needs worker and RPC reconnect controls for rich goal references, an exact-version/import fence, and fresh batch verification of the complete proof. This package supplies only its five-position, four-version component cell.
