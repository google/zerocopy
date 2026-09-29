# Tiny Lake project: final-path build versus staging build and rename

## Summary

This paired local experiment covers the small cached-only part of #3730 F15. The same four-source Lean/Lake project was built once directly at a final pathname, then built at a staging pathname and renamed to that **same** final pathname. In both cases, `lake setup-file Proof.lean` returned the final-path `Dep.olean`, `lake serve` reported `no goals` for a valid proof and the same two informational diagnostics, fresh batch Lean exited 0, and `lake --no-build build Dep` said all targets were up to date. The moved build retained seven staging-path strings in `Dep.trace`; the direct build's trace contained seven final-path strings. The other nine inspected `.lake` files, including `Dep.olean`, had equal hashes, and neither setup nor the server/no-build check rewrote the trace. **Basis: execution.**

The narrow fixture therefore shows that stale location text can persist in Lake trace metadata while these particular setup, batch, and LSP oracles agree. It does not select a publication strategy for a real Anneal prepared generation with external dependencies, generated modules, plugins, richer queries, or concurrent consumers.

## Subject and protocol

- Cached Lean/Lake `v4.30.0-rc2`, Lean revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, on macOS. No dependency was fetched or installed.
- Private scratch root held `final`, `stage`, and an archived direct-build control. The direct project was moved aside after its complete oracle, then identical source bytes were prepared at `stage` and renamed to the now-vacant `final` path. The two conditions therefore used the same final pathname sequentially.
- `lakefile.lean` declares one default Lean library `Dep`; `Dep.lean` defines `selected : Nat := 7`; `Proof.lean` imports it, evaluates `selected`, proves `selected = 7` by `rfl`, and prints the theorem axioms. Source hashes are in the raw result.
- Each build used explicit cached binaries, `--keep-toolchain --no-cache`, a single Lean library module, `LEAN_NUM_THREADS=1`, and bounded command timeouts. Lake reported three internal jobs for each tiny build/check despite the one-module fixture and `LAKE_JOBS=1` environment variable. The full probe ran under `sandbox-exec` with `(deny network*)`.
- After each build, the probe inventoried every `.lake` file with size, SHA-256, and occurrences of either absolute path. It then ran `lake setup-file`, a fresh `lake serve` LSP session with `waitForDiagnostics` and `plainGoal`, `lake env lean --json`, and `lake --no-build build Dep`, followed by another inventory. Raw LSP requests, replies, diagnostics, and server lifecycle are retained.

## Results

| Observation | Built at final path | Built at stage, renamed to final |
| --- | --- | --- |
| `lake build Dep` | Exit 0; 3 jobs | Exit 0; 3 jobs |
| `lake setup-file Proof.lean` | Exit 0; import artifact at `final/.lake/build/lib/lean/Dep.olean` | Same |
| Fresh `lake serve` goal at `rfl` | `no goals` | `no goals` |
| LSP diagnostics | `7`; `checked` has no axioms | Same |
| Fresh `lake env lean --json Proof.lean` | Exit 0; `7`, no axioms | Same |
| `lake --no-build build Dep` | Exit 0; all targets up to date | Same |
| Location-bearing `.lake` file | `Dep.trace`: 7 final-path occurrences | `Dep.trace`: 7 stage-path occurrences, still present at final path |
| `.lake` inventory | 10 files; nine byte-identical to moved build | 10 files; `Dep.trace` alone differed |
| Setup/server/no-build rewrite of `.lake` inventory | None | None |

The stale trace strings occur in Lake's logged compiler command and `Dep.lean` input pathname. The trace also contains content-derived output and dependency hashes; the corresponding non-trace outputs match byte for byte. Lake's up-to-date response on the moved project is an observation for this fixture, not evidence that all uses of the stale trace are safe.

## Scope against F15 and destination investigations

The exact #3730 F15 question is final stable path versus staging preparation followed by rename. This experiment executes that contrast for a local core-only project and records path-bearing state. It fills a cell omitted from the #3730 crosswalk's cited package list, although the prior [prepared-contract report](../anneal-3730-lake-prepared-contract-2026-09-29/REPORT.md) had already explored other relocation schedules. The #3731 destination questions about actual prepared-generation publication, cache identity, source/model environment identity, and interactive parity remain partly gated by an Anneal archive and a real generated workload. The result should narrow F15, not mark those destination rows complete.

The two conditions ran sequentially, so there is no race evidence. This fixture has no external dependency, archive extraction, generated Aeneas model, plugin, dynamic library, concurrent reader, crash window, or navigation/reference query. No production path was moved or modified.

## Evidence and revalidation

- [Probe](support/probe.py), [raw results and 82-event LSP transcript](support/results.json), [offline checker](support/check.py).
- Probe SHA-256 `9db4cc17e93ea169d893c20cd04fec63b8e3e45cee471fead2a49fb7cb553d78` and result SHA-256 `a51334657934e866f35d635a0076d18f2a760127a045c49fb9dbe6d8b02b41f8` are pinned in `REPORT.json`.
- Run `python3 support/check.py` against the retained result. To reacquire, create an empty private scratch directory and run `sandbox-exec -p '(version 1)(allow default)(deny network*)' python3 support/probe.py --scratch <empty-private-directory>`. The probe writes `support/results.json` and temporary artifacts only in the supplied scratch directory.
