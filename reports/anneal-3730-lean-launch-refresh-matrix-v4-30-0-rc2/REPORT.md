# Imported-definition refresh across three Lean server launch modes

## Summary

In a tiny Lake workspace at Lean/Lake `v4.30.0-rc2`, direct `lean --server`, `lake env lean --server`, and `lake serve` showed the same bounded imported-generation split. The already open proof worker kept evaluating `selected` as 7 after either a source-only change or a valid `.olean`-only replacement. A newly opened file saw 9, while the old file still saw 7 **after** the new file was ready; closing and reopening the old file made it see 9. An `.olean`-only fresh-server control also saw 9. The source-only case rebuilt its dependency artifact by the time the new file completed readiness, even under direct launch from a Lake workspace. Thus launch spelling alone did not provide a fresh imported environment for an existing worker in this fixture.

`lake setup-file` returned an import path but no artifact digest. It returned exit 0 with empty `importArts` for a missing import, including when given an explicit unsaved-header override. The LSP wait likewise returned `{}` for an unsaved missing import while diagnostics reported the import failure and goal queries returned JSON `null`. These outputs must be interpreted separately from proof acceptance and imported-environment attestation.

## Applicability

The direct subject is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, release `v4.30.0-rc2` on arm64 macOS. SHA-256: `lean` `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`; `lake` `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`. Six independent Lake workspaces were prepared with a local `Dep` module and identical proof documents. The three launch commands were `lean --server` with local `LEAN_PATH`, `lake env lean --server`, and `lake serve`, one server session at a time. Lake commands used `--keep-toolchain --no-cache`; environment settings included `LEAN_NUM_THREADS=1` and disabled Lake artifact cache access. No external package, plugin, Mathlib, generated Anneal module, or MCP adapter was present.

The host reported 8 GiB RAM. `memory_pressure -Q` was 44% free at the start, at least 38% at session boundaries, and 38% at the end. The largest sampled server-tree RSS was 1,667,055,616 bytes, below the probe's 3 GiB query-point cap. This is not a continuously sampled peak, and a Lake setup subprocess could exist between samples. The script starts one server session at a time; its compiler prebuilds and post-session `setup-file` commands are sequential.

## Findings

### Imported source and artifact transition

The baseline `Dep.lean` defines `selected : Nat := 7`; `Proof.lean` imports it, evaluates `selected`, proves `selected = 7` by `rfl`, and has a separate unfinished scratch proof. Baseline Lake-built `Dep.olean` SHA-256 was `c363ec99438400519e766fea241aaee6b7bafc2d593f5db9fd740bb5b7e69f62`. The source-only variant changed `Dep.lean` to value 9 while leaving that OLean in place. The `.olean`-only variant left source value 7 and copied a separately valid value-9 OLean with SHA-256 `3b0254045f93c2516915e7a26e2d3928d0472535fd876db2b81312725f8ea008` over the built artifact; the `.olean.hash` sidecar stayed byte-identical and the replacement had an **older** mtime than the original. These are distinct tests, not two names for one source-and-artifact rebuild.

| Condition, in each of three launch modes | Already open `Proof` | Newly opened `New` | Old `Proof` queried again while `New` remains open | Closed/reopened `Proof` |
| --- | --- | --- | --- | --- |
| Source changed to 9; OLean initially 7 | `#eval` 7; `rfl` has no remaining goal | `#eval` 9; `rfl` fails; OLean now `696d7ea3…` | Still `#eval` 7; `rfl` has no remaining goal; disk OLean is now 9 | `#eval` 9; `rfl` fails |
| OLean replaced with valid 9; source remains 7 | `#eval` 7; `rfl` has no remaining goal, despite disk OLean 9 | `#eval` 9; `rfl` fails; replacement OLean unchanged | Still `#eval` 7; `rfl` has no remaining goal | `#eval` 9; `rfl` fails |

The rebuilt source-9 OLean SHA-256 was `696d7ea3fda9c4e8c0c02c84ac8d158e4a4774bb2d0f9e8ab2da6cdf2a2d7ab5`. A fresh batch Lean invocation after each session evaluated 9 and exited 1 with the failed `rfl` and unfinished scratch proof; for the `.olean`-only variant, a fresh watchdog also evaluated 9 and returned the remaining `rfl` goal. Every mode and variant produced these qualitative outcomes, with all nine server processes shutting down cleanly. **Basis: execution**, exact OLean/source hashes, diagnostics, goal replies, and wire chronology in [`support/transcript.json`](support/transcript.json); assertions in [`support/summarize.py`](support/summarize.py).

`workspace/didChangeWatchedFiles` plus a query of the existing worker did not change its imported environment. In the source-only case the OLean still had its baseline hash at that point; by the time `New.lean` completed `waitForDiagnostics`, the OLean had been rebuilt to source value 9. The subsequent re-query of the old worker establishes a genuine same-process split after the disk artifact transition. The transcript does not pinpoint the server's internal build-trigger instruction; the observed boundary is completion of the new-file open/wait. In the `.olean`-only case, the changed OLean was on disk before either the old or new worker query. **Basis: execution**.

This direct-launch result is specific to a directory with a Lake configuration. It should not be merged with a bare direct `lean --server`/`LEAN_PATH` case that has no Lake workspace without preserving that setup difference. The earlier [direct-server dependency report](../lean-same-server-dependency-generation-v4-30-0-rc2/REPORT.md) and [Lake-env V1 report](../anneal-v1-interactive-dependency-invalidation-2026-09-28/REPORT.md) have separate fixtures and constraints.

### Exact positions, readiness, and missing imports

For every valid-import sample, `plainGoal` at zero-based `(line 3, column 2)` on `rfl` returned the input goal `⊢ selected = 7`. At `(3,5)`, baseline/old-worker success returned an empty `goals` array, while a worker using value 9 returned the remaining goal. The scratch proof's `(5,2)`, `(5,4)`, `(5,10)`, and EOF `(6,0)` all returned `⊢ selected = 7`; the placeholder errors in diagnostics show that these goal payloads do not imply a valid file. This is a fixed six-position grid, not general tactic-position semantics. **Basis: execution**.

After the `.olean`-only transition, the probe sent an unsaved `didChange` for `Proof.lean` from `import Dep` to `import Missing`. `waitForDiagnostics(version=2)` returned `{}` in all three modes, but the diagnostics reported `unknown module prefix 'Missing'`; each of the six queried positions returned JSON `null`. The persisted `Proof.lean` still imported `Dep`, so a later fresh-server control over the on-disk text again evaluated 9. A successful wait is therefore a completion/readiness signal for this attempted state, not success of module import or whole-file proof. **Basis: execution**.

### `lake setup-file` controls

The pinned Lake source contains the [hidden CLI `setup-file` dispatch](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/CLI/Main.lean#L920-L934) and accepts an optional JSON [`ModuleHeader`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lean/Lean/Setup.lean#L58-L64). The probe invoked it only **after** live sessions, because it may build dependencies. For normal on-disk `Proof.lean`, `setup-file` returned exit 0 with an `importArts.Dep` path to the local OLean and empty `plugins`/`options` in this fixture. In the source-only cases, that artifact had already rebuilt to 9; in `.olean`-only cases, ordinary `setup-file` left the replacement value-9 OLean unchanged.

For on-disk `Bad.lean` (`import Missing`) and for `Proof.lean` with an explicit unsaved-header JSON override naming `Missing`, `setup-file` returned exit 0 with `importArts: {}`. The override changed the setup output even though the file on disk still imported `Dep`. Thus a consumer must use the **current document header** for file-specific setup and still check subsequent Lean diagnostics; exit 0 plus empty `importArts` does not certify that the import will elaborate. A post-session `lake --rehash setup-file Proof.lean` also returned 0 without changing the copied value-9 OLean in any of the three `.olean`-only fixtures. This narrow result does not mean `--rehash` never detects output corruption; it establishes that this particular file setup invocation did not repair or reject the tampered artifact. **Basis: source + execution**, `setup_file`, `setup_file_header_override`, and `setup_file_rehash` events.

`ModuleSetup` here names artifact paths but does not carry the OLean SHA-256 observed by the harness, a loaded worker incarnation, or a proof-source hash. The `#eval` and failed-`rfl` sentinels establish which definition was used in this specific worker, but are test instrumentation, not a general attestation API. **Basis: execution + derived implication**.

### Issue coverage and exact residuals

| #3731 item | Evidence added here | Remaining condition |
| --- | --- | --- |
| I041 | Same-source goal queries expose two imported environments | Version-bound goal operation and edit/query interleavings |
| I042 | Wait succeeds for a missing import with error diagnostics | Import/setup delays and permanent-failure classification |
| I043 | Six exact positions around `rfl`, `exact ?_`, and EOF | Nested/combinator/macro positions and interactive RPC comparison |
| I044 | None; plain goals only | RPC handle lifetime across these import transitions |
| I045 | Close/reopen and fresh-server controls | Delayed response and request-ID reuse across worker replacement |
| I046 | Missing import yields null goals and diagnostics | Broad partial-file recovery matrix (separate [partial-elaboration report](../anneal-3730-partial-elaboration-queries-v4-30-0-rc2/REPORT.md)) |
| I047 | Old worker remains resident after new artifact visible | Explicit historical-query contract, retention cost, expiry |
| I048 | `ModuleSetup` path and semantic sentinels | Worker-reported loaded artifact/options/plugin identity |
| I049 | Three launch modes, watcher, new file, reopen, fresh watchdog | More import graphs, concurrency schedules, and real generated project |
| I050 | Direct import only | Transitive imports, options, macros, plugins, native code |
| I091 | Explicit unsaved-header `setup-file` override plus LSP missing-import edit | Instrument actual per-request server setup identity |
| I147 | Source-only and OLean-only decoupling with older artifact mtime | Same-mtime and byte-identical rebuilds; external model with unchanged output |

## Boundaries

- **Not examined:** transitive imports, plugin/native code changes, options, package-configuration edits, real generated Anneal modules, MCP transport, worker crashes, and concurrent edits during in-flight goal requests. I050 and much of I041/I045/I048 remain open.
- **Not examined:** a changed source producing a byte-identical semantic artifact, a same-mtime artifact replacement, changed external Rust model with unchanged generated Lean, or multiple timestamp schedules. The `.olean`-only copy here had an older mtime and an unchanged Lake hash sidecar. I147 remains partial.
- **Not established:** exact-version goal queries or historical queries. The goal responses do not include a source/artifact digest or worker incarnation. The grid samples only six positions in one simple proof; rich RPC goals and context handles are outside this report.
- **Not established:** that `lake setup-file` exit 0 means import or theorem acceptance. The missing-import controls are explicit counterexamples in this fixture. The hidden command's JSON header override was run in a separate process; the probe did not instrument the language server's own internal setup-file invocation arguments.
- **Unknown:** whether other Lake flags, cache states, toolchain layouts, or larger import graphs alter the rebuild boundary. The direct mode here ran inside a Lake project, so its source-only rebuild cannot be generalized to bare Lean without that workspace.
- **Not measured:** exact transient memory peaks during setup, physical memory/PSS, or startup throughput across repetitions. The 3 GiB RSS cap was enforced at recorded query points; one server ran at a time and the largest sampled tree was 1.67 GiB.

## Evidence

- Replayable standard-library harness: [`support/probe.py`](support/probe.py), SHA-256 `d20a5c7b20b71d7fdfec608144934f227c6a48678fc4ebff3487d1d18a7b5a01`.
- Full sanitized record: [`support/transcript.json`](support/transcript.json), SHA-256 `c9bfdc571bfb555729514b548fcab4a747bab839a26c0f7463a5ec1b23a3e0b2`; 1,504 ordered events preserve launch argv, requests/replies/diagnostics, commands and outputs, source/artifact/sidecar hashes and mtimes, process trees, and setup-file JSON. Local paths are tokenized as `$WORK_URI`, `$WORK`, `$LEAN_BIN`, and `$LAKE_BIN`.
- [`support/summarize.py`](support/summarize.py) asserts each mode/variant's old/new/reopened/fresh semantic sentinel, exact goal positions, missing-import diagnostic, setup-file outputs, batch control, source/OLean hash transitions, and resource bound. The passing digest is [`support/summary.json`](support/summary.json); final tiny workspaces and prebuilt artifacts are under [`support/work`](support/work).
- Lake primary source at the pinned revision: [`Serve.lean` setup-file handling](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/CLI/Serve.lean#L35-L84), [`Module.lean` edited/external module setup](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L1267-L1320), and Lean [`ModuleHeader`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lean/Lean/Setup.lean#L58-L64). These source links explain the available interface; the execution transcript is the basis for the observed mode comparison.

## Revalidation

On the same pinned Lean/Lake tuple, run `LEAN_BIN=/absolute/path/to/pinned/bin/lean python3 support/probe.py`, then `python3 support/summarize.py`. The probe replaces only its own `support/work`, prepares prebuilt value-7/value-9 imports, and runs one server session at a time after a system free-memory check. Check the binary identities and pressure/cap events before interpreting a replay. A changed mode result, artifact hash, diagnostic, or `setup-file` output should be reported as a new exact-version observation; do not infer Anneal behavior from this direct Lean/Lake matrix.
