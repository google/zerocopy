# Aeneas One-Shot CLI Process Contract, Request Identity, Cross-Layer Handoff Manifests, and Declaration-Block Invalidation

## Summary

Six execution experiments and cross-revision source inspections across Aeneas (`nightly-2026.06.03` at `ac9f1bc5262a` and `nightly-2026.09.30` at `0855ce1b8ed3`), Charon (`0.1.210`), Lean 4 / Lake (`v4.30.0-rc2`), and Rust (`nightly`) define the process isolation, request-identity closure, output-directory ownership, file-versus-buffer handoff, and declaration-level invalidation behavior of the Aeneas translator:

1. **Batch single-shot CLI architecture and mutable global state across Aeneas revisions (`support/aeneas-process-contract/`):**
   - Across both `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`) and `AeneasVerif/aeneas@0855ce1b8ed3958512b6c19de6bf3035b7acb552` (`nightly-2026.09.30`), `compiler/Driver.ml` / `src/Main.ml` and `compiler/ExtractBase.ml` / `src/Translate.ml` operate strictly as a batch single-shot CLI translator from `.llbc` files to generated `.lean` module files without a persistent daemon/RPC server mode or a built-in JSON output manifest.
   - Although `src/dune` exposes a public OCaml library (`Aeneas.Translate.translate_crate`), `src/Config.ml` stores backend, namespace, split-file, and parallelism settings in mutable process-global `ref`s, `src/Errors.ml` accumulates `error_list` and `unique_errors` in global `ref`s without per-request reset in the entry path, and `src/Parallel.ml` initializes a persistent domain pool torn down only at process exit.
   - Launching 1, 2, and 4 concurrent `aeneas` OS processes into **private** `-dest` directories produced outputs byte-identical to sequential clean oracles (`A` and `B`), whereas sharing a destination directory across concurrent inputs (`A` and `B`), across flag changes (`-split-files` to unsplit), or across a failing raw-pointer translation (`exit 1`) left mixed entry files (`A.lean` and `B.lean`), stale `Types.lean`/`Funs.lean` modules, or partial `Funs.lean` files containing `sorry`.
2. **Request-identity closure and runtime library coupling (`support/aeneas-identity-manifest/`, `support/aeneas-manifest-batch-oracle/`, `support/charon-aeneas-boundary/`):**
   - Holding the input `.llbc` byte-identical while varying `-namespace Alternate`, `-split-files`/`-gen-lib-entry`, or `-max-heartbeats 500000` changed emitted `.lean` file sets or file digests, whereas clearing LLBC `translated.short_names` (or permuting `short_names` across `A1`/`A2`/`A3`) and toggling `-impl-namespace` or `-tuple-nested-proj` left the emitted Lean bytes unchanged on these fixtures.
   - Forging `charon_version: "0.1.999"` in the input LLBC caused Aeneas to exit `1` before writing files. Copying the `aeneas` executable without its relative `libs/libgmp.10.dylib` (`1b0ae619…`) caused macOS `dyld` to abort with exit `-6` (`Library not loaded: @executable_path/libs/libgmp.10.dylib`).
3. **Whole-file versus lexical declaration-block invalidation (`support/aeneas-identity-manifest/`, `support/aeneas-declaration-block-diff/`, `support/aeneas-manifest-batch-oracle/`):**
   - Mutating a single Rust function body (`step` or `inc`), struct field layout (`Wrap`), trait impl body (`Bump`), or recursive-group member (`even`) changed the whole `Funs.lean` digest (and `Types.lean` for `Wrap`).
   - Lexical declaration-block decomposition across 83 generated blocks in `support/aeneas-declaration-block-diff/` showed that unchanged callers (`use_step`, `use_bump`, `odd`) remained **textually identical** inside `Funs.lean` when their callees changed, yet fresh Lean batch evaluation in `support/aeneas-manifest-batch-oracle/` proved that unchanged caller `twice 0` changed its semantic value from `ok 2` to `ok 4` when `inc` changed from `wrapping_add(1)` to `wrapping_add(2)`. Per-declaration caching therefore cannot rely on unchanged Rust or Lean item text without a transitive call/type/trait dependency graph and external-model closure.
4. **File versus byte-buffer and `lean --stdin` handoffs (`support/aeneas-handoff-memory-vs-files/`):** Because the Aeneas CLI requires a `FILE` argument, an in-memory Python buffer handoff still requires materializing a temporary `.llbc` file (~67 µs median write+`fsync` for 6.7 KiB vs ~209–211 ms Aeneas execution). Feeding generated `Types`, `Funs`, and root Lean source texts via `lean --stdin` avoided writing `.lean` files to disk and passed proof checks, but altered all three `.olean` digests and degraded diagnostic source locations from `CheckWrong.lean:2:52` to `<stdin>:2:52`.

## Applicability

The findings in this report apply to the following subjects from `REPORT.json`:

- **Aeneas `nightly-2026.06.03`** (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, macOS `aarch64-apple-darwin` binary SHA-256 `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`, bundled `libs/libgmp.10.dylib` SHA-256 `1b0ae61990da7a4661f2c8c601f55f6c9950279bbfef12453dd5bb0c01e4b0df`, `ExtractBuiltinLean.ml` SHA-256 `f0ef34854fb4634303ff70f32d51f43e615b36880e3864975e6d62041470a2a8`) and **Aeneas `nightly-2026.09.30` source** (`AeneasVerif/aeneas@0855ce1b8ed3958512b6c19de6bf3035b7acb552`);
- **Charon `0.1.210`** (`AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`);
- **Lean 4 and Lake `v4.30.0-rc2`** (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`, prebuilt `Aeneas.olean` SHA-256 `67701a9e…`);
- **Rust compiler `1.98.0-nightly` (`nightly`)** (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, binary SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`).

**Shared behavior versus cross-version deltas:** All runtime executions ran the `nightly-2026.06.03` (`ac9f1bc5262a`) Aeneas executable with Charon `0.1.210` and Lean `v4.30.0-rc2` on macOS `arm64`. Source comparison between `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`nightly-2026.06.03`) and `AeneasVerif/aeneas@0855ce1b8ed3958512b6c19de6bf3035b7acb552` (`nightly-2026.09.30`) across `compiler/Driver.ml` (`src/Main.ml`) and `compiler/ExtractBase.ml` (`src/Translate.ml`) establishes that both revisions share the same batch single-shot CLI execution model: neither revision implements a persistent RPC/daemon loop or emits a built-in JSON declaration/file manifest, and both write generated `.lean` files directly into `-dest` without transactional directory replacement.

## Findings

### Process Isolation, Global Mutable Refs, and Shared-Destination Hazards (`support/aeneas-process-contract/`, `support/charon-aeneas-boundary/`)

Source inspection of `AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727` (`support/aeneas-process-contract/source-api-evidence.txt`, SHA-256 `8c30b9b43825131b067f979929d6d2fa41fceec8c74e9f1741210dbc801429ab`) and `0855ce1b8ed3958512b6c19de6bf3035b7acb552` identified exact state boundaries across key OCaml modules:

- `src/dune:1-29` and `src/Translate.ml:2121-2136` define `translate_crate_to_pure`, `extract_translated_crate`, and `translate_crate`.
- `src/Main.ml:257-267,535-576,725-746` parses a single `.llbc` path, clears `short_names`, runs pre-passes, calls `Aeneas.Translate.translate_crate`, and exits `1` if `!Errors.error_list` is non-empty.
- `src/Config.ml:17-38,218-224,454-472` holds backend, namespace, split-file, and parallel flags in mutable process-global `ref`s; `src/Errors.ml:75-98` accumulates errors in global `error_list` and `unique_errors` `ref`s that are not cleared by `translate_crate`; and `src/Parallel.ml:18-36` creates a persistent worker pool torn down at process exit, with no cancellation token or deadline API.

Executable process-boundary tests in `support/aeneas-process-contract/` and `support/charon-aeneas-boundary/` using safe input `A` (LLBC SHA-256 `0784839f4f1fd3ade660340301810d4a2109729b0ecbf47e6c2bf72bc9f96e7e`), body-modified `B` (`6774e33245dfeddc0a110c9ac2ea2244710a3d233140241589cb19ef370e4c55`), doc-comment-modified `C`, and unsupported raw-pointer input (`daab1c093c8af871b3d7751a9625f49137f3bedf03f19e9ab3a3c46b10fb078d`) demonstrated:

| Test cell | Process / destination configuration | Exit code(s) | Observed output inventory and digests |
| --- | --- | --- | --- |
| `A1 → A2 → C → B → A3` (`support/charon-aeneas-boundary/`) | Fresh processes, private destinations | All `0` | `A1/A2/A3` raw LLBCs (`0784839f…`, `5389fa29…`, `0784839f…`) normalized to `5eaaaea233c5…` after sorting `short_names`/`item_names`; all 3 `A` runs and doc-comment `C` emitted identical `Funs.lean` (`f7f03a06…`), `Types.lean` (`a06e07ba…`), and `Snapshot.lean` (`f655d06e…`). `B` changed `Funs.lean` to `f0f5ca27…`. |
| Concurrent groups of 1 (`A`), 2 (`A, B`), and 4 (`A, B, A, B`) (`support/aeneas-process-contract/`) | Fresh processes, private `-dest` per job (1 and 6 measured lifetime overlaps) | All `0` | Every job matched its sequential oracle byte-for-byte (`A.lean` `239c1030…`, `Types.lean` `a06e07ba…`, `Funs.lean` `61d00aea…`; `B.lean` `ca425ba1…`, `Types.lean` `a06e07ba…`, `Funs.lean` `fffaaf29…`). |
| Concurrent `A` and `B` into one shared `-dest` | 2 processes, 1 shared directory | `0, 0` | Directory contained both `A.lean` and `B.lean` simultaneously alongside last-writer `Funs.lean`. |
| Split-file `A` followed by unsplit `A` in one `-dest` | Sequential, reused directory | `0`, then `0` | Unsplit `A` updated `A.lean` but left stale `Types.lean` and `Funs.lean` from the split run. |
| Valid `A` followed by unsupported raw-pointer LLBC in one `-dest` | Sequential, reused directory | `0`, then `1` | Failed second run left old `A.lean`, wrote new `Unsupported.lean`, and overwrote `Funs.lean` with partial output containing `sorry`. |
| Malformed Rust `pub fn broken(` after `A3` (`support/charon-aeneas-boundary/`) | Reused `current.llbc` destination | Charon `2` | `current.llbc` remained byte-identical to `A3`'s valid LLBC. |
| 1 µs timeout + `SIGKILL` (`-9`) (`support/aeneas-process-contract/`) | Private destination | `-9` | Process reaped cleanly; private destination remained empty. |

Basis: **source + execution** in `support/aeneas-process-contract/source-api-evidence.txt`, `support/aeneas-process-contract/raw-results.json`, and `support/charon-aeneas-boundary/raw-results.json`.

### Request-Identity Matrix and Lexical Declaration-Block Diffs (`support/aeneas-identity-manifest/`, `support/aeneas-declaration-block-diff/`)

In `support/aeneas-identity-manifest/`, a baseline Rust crate `identity_probe` (generating `Current.lean`, `Types.lean`, and `Funs.lean` with 12 Lean declaration heads covering `Wrap`, trait `Bump`, impl methods, `step`, `use_step`, `use_bump`, and mutually recursive `even`/`odd`) was subjected to six source mutations and nine CLI/environment controls (`support/aeneas-identity-manifest/results.json` SHA-256 `694c43532ac90504947bd5cfe9e34369cae68e2164683e8c3f772138022d45b4`, `support/aeneas-identity-manifest/handoff-manifest.json` SHA-256 `e9870d6f9844eb5ebc192d297d642319333549aac483d9f9a3322c75ba3c8826`). In `support/aeneas-declaration-block-diff/`, all 83 generated declaration blocks across the 21 Lean files were lexically delimited and compared against baseline (`support/aeneas-declaration-block-diff/comparison.json`, elapsed `0.0730 s`, peak self RSS `22,708,224` bytes, minimum reclaimable memory `25.1751%`):

| Controlled mutation or option change | Aeneas exit | Whole-file effect vs base (`Current.lean`, `Types.lean`, `Funs.lean`) | Lexical declaration-block diff vs base (`added / removed / changed / unchanged / moved-line` blocks in `support/aeneas-declaration-block-diff/`) |
| --- | ---: | --- | --- |
| Repeat same LLBC & options; or copied binary with `libs/libgmp.10.dylib` | `0` | All 3 files byte-identical to base | — |
| Copied binary **without** `libs/libgmp.10.dylib` | `-6` | `dyld` abort: `Library not loaded: @executable_path/libs/libgmp.10.dylib` | — |
| Mutate `step` function body (`use_step` unchanged in Rust) | `0` | `Funs.lean` changed; `Types.lean` & `Current.lean` equal | `0 / 0 / 1 (step) / 11 (incl. use_step) / 0` |
| Change `Wrap` from 1 to 2 `u32` fields (`use_bump` unchanged in Rust) | `0` | `Types.lean` and `Funs.lean` changed | `0 / 0 / 2 (Wrap, bump) / 10 (incl. use_bump) / 8` |
| Mutate `Bump` trait impl body | `0` | `Funs.lean` changed | `0 / 0 / 1 (bump) / 11 / 0` |
| Mutate `even` in `even`/`odd` recursive group | `0` | `Funs.lean` changed | `0 / 0 / 1 (even) / 11 (incl. odd) / 0` |
| Insert unrelated `helper` before `step` | `0` | `Funs.lean` changed (including `Source:` line numbers) | `1 (helper) / 0 / 0 / 12 / 5` |
| Delete `step` and `use_step` | `0` | `Funs.lean` changed; both declarations absent | `0 / 2 (step, use_step) / 0 / 10 / 3` |
| `-namespace Alternate` | `0` | `Types.lean` and `Funs.lean` changed | — |
| Omit `-split-files` and `-gen-lib-entry` | `0` | Only `Current.lean` emitted (leaves stale `Types.lean`/`Funs.lean` if run in shared dir) | — |
| `-max-heartbeats 500000` | `0` | `Types.lean` and `Funs.lean` changed despite identical LLBC | — |
| `-impl-namespace` or `-tuple-nested-proj` | `0` | No byte change on this fixture | — |
| Clear LLBC `short_names` array | `0` | No byte change (`Main.ml` clears `short_names` on load) | — |
| Forge LLBC `charon_version: "0.1.999"` | `1` | Incompatible-version error; 0 files written | — |
| Raw-pointer error into shared directory after base | `1` | `Funs.lean` overwritten from `93da487c…` to `aec4a418…` with `sorry`; `UserModel.lean` sentinel untouched | — |

Basis: **execution** in `support/aeneas-identity-manifest/results.json` and `support/aeneas-declaration-block-diff/comparison.json`.

### Fresh Lean Batch Oracle and External-Function Model Closure (`support/aeneas-manifest-batch-oracle/`)

In `support/aeneas-manifest-batch-oracle/`, 29 sequential commands (`support/aeneas-manifest-batch-oracle/results.json` SHA-256 `e5da18ed41a366760621b10a8bbfe0350104493706e997fb1633221e3fc1bba1`, `support/aeneas-manifest-batch-oracle/declaration-manifest.json` SHA-256 `a3a20c859da78e1ecf0a893d674e2e7fa2f6e582ed1bb463cbca9915e1411f9c`) checked generated Lean modules with Lean `v4.30.0-rc2` against `Aeneas.olean` (`67701a9e…`):

| Fixture and control | LLBC / `Funs.lean` / user-model SHA-256 | Fresh Lean `v4.30.0-rc2` batch compilation and proof oracle |
| --- | --- | --- |
| `oracle_probe`: `inc` uses `wrapping_add(1)` | LLBC `c25b76cd…`, `Funs.lean` `ae306b7a…` | `inc 0 = ok 1` and `twice 0 = ok 2` pass `rfl` (axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`); wrong claim `inc 0 = ok 2` fails. |
| `oracle_probe`: `inc` uses `wrapping_add(2)` (`twice` Rust text unchanged) | LLBC `359f1ad1…`, `Funs.lean` `97ef3a43…` (`Types.lean` unchanged) | `inc 0 = ok 2` and `twice 0 = ok 4` pass `rfl`; wrong claim `inc 0 = ok 3` fails. |
| `oracle_probe`: forged `charon_version = "0.1.999"` | — | Aeneas exits `1`; output directory remains empty. |
| `External` (`extern "C" fn external_double`): missing `FunsExternal.lean` | Fixed generated `External.lean`, `Types.lean`, `Funs.lean`, `FunsExternal_Template.lean` | Batch Lean compilation of `Funs.lean` fails on missing `External.FunsExternal` import. |
| `External`: axiom template copied to `FunsExternal.lean` | Model SHA-256 `20c41bce…` | Compiles; `#print axioms oracle_probe.call` lists `[external_double]`. |
| `External`: concrete `def external_double (x : Std.U32) : Result Std.U32 := ok (core.num.U32.wrapping_add x x)` | Model SHA-256 `8685ca7f…` (same generated Aeneas bytes) | Compiles; `call 1 = ok 2` passes `rfl` and `#print axioms oracle_probe.call` reports zero axioms. |

Basis: **execution** in `support/aeneas-manifest-batch-oracle/results.json`.

### Serialized Files versus Byte Buffers and `lean --stdin` (`support/aeneas-handoff-memory-vs-files/`)

On a 6,851-byte `inc` LLBC in `support/aeneas-handoff-memory-vs-files/results.json`:

- **File versus Python buffer copy into Aeneas:** Passing the `.llbc` path directly versus reading into a Python `bytes` buffer, copying in memory (`tracemalloc` peak `14 KiB` / `7 KiB`), and writing a second `source.llbc` before invoking `aeneas` yielded identical generated Lean files (`~209 ms`, peak RSS `~45 MiB` for file; `~211 ms`, peak RSS `~44 MiB` for buffer). Across 16 warm repeats, 6.7-KiB buffer operations had medians of `~20 µs` (read), `~0.4 µs` (in-memory copy), and `~67 µs` (write + `fsync`; single actual run `132 µs`).
- **Compiling generated Lean via `lean --stdin`:** Piping captured `Types.lean`, `Funs.lean`, and root module strings through `lean --stdin -o <module.olean>` succeeded without materializing `.lean` source files on disk and allowed a downstream proof consumer to pass, but all three `--stdin` `.olean` hashes differed from file-compiled `.olean` hashes, and an intentional proof error reported `<stdin>:2:52` rather than `CheckWrong.lean:2:52`.
- **Corruption and FIFO `SIGTERM` controls:** Truncated or first-byte-corrupted LLBC buffers made Aeneas exit nonzero with no output files. Mutating `1#u32` → `2#u32` in `Funs.lean` compiled cleanly to `.olean` but failed the downstream proof consumer. Blocking `Funs.lean` on a named pipe after `Types.lean` was emitted and sending `SIGTERM` (~257 ms file / ~218 ms buffer to barrier, ~1 ms to exit) left no surviving process-group members and succeeded on retry.

Basis: **execution** in `support/aeneas-handoff-memory-vs-files/results.json`.

## Boundaries

- **Not examined:** Same-process OCaml library execution (`Aeneas.Translate.translate_crate`) across sequential `A → B → A` or concurrent requests (no `ocamlc`/`dune`/`opam` toolchain or `.cmxa`/`.cma` archive was installed on the host).
- **Not examined:** Mutating Aeneas's compiled-in OCaml external-model registry (`ExtractBuiltinLean.ml`) and rebuilding the `aeneas` binary from source.
- **Known not to apply:**
  - Unchanged Rust or generated Lean declaration text for a caller (`use_step`, `use_bump`, `odd`, `twice`) does **not** mean its Lean proof obligations or evaluated semantics are unchanged when a callee, type definition, or trait implementation changes.
  - Generated Lean file digests alone do **not** identify the proof environment when generated code imports a user-supplied `FunsExternal.lean` module.
  - Aeneas `Source:` comments provide only lexical file/line hints; neither `nightly-2026.06.03` nor `nightly-2026.09.30` emits an authenticated `Charon def_id → Aeneas pure decl → Lean byte range` manifest.
- **Unsupported:** Dereferencing raw pointers in Rust is unsupported by the examined Aeneas pin (`exit 1`), which nevertheless writes partial `.lean` files containing `sorry` to `-dest`.

## Evidence

- **Process contract and Charon/Aeneas boundary subprobes:**
  - `support/aeneas-process-contract/probe.py` (SHA-256 `ea9924ef981f0534bed75d57b0f82ddb23c754b2ddd0fed381c443b5848cbab0`), `support/aeneas-process-contract/raw-results.json`, `support/aeneas-process-contract/source-api-evidence.txt` (SHA-256 `8c30b9b43825131b067f979929d6d2fa41fceec8c74e9f1741210dbc801429ab`), `support/aeneas-process-contract/fixture/`, and `support/aeneas-process-contract/artifacts/`.
  - `support/charon-aeneas-boundary/probe.py` (SHA-256 `ca098f663933e0d0993f9a0691ab50a24bec6d31f100e59d6ed3dabc94af82df`), `support/charon-aeneas-boundary/raw-results.json`, `support/charon-aeneas-boundary/handoff-manifest.json`, `support/charon-aeneas-boundary/host.txt`, `support/charon-aeneas-boundary/command.stdout`, `support/charon-aeneas-boundary/fixture/`, and `support/charon-aeneas-boundary/artifacts/`.
- **Identity manifest, declaration-block diff, and batch oracle subprobes:**
  - `support/aeneas-identity-manifest/probe.py` (SHA-256 `e561d0eaba807dcc9c23d2df1f084e7b8f6cb97aec88f09ffe0d13deea18426e`), `support/aeneas-identity-manifest/results.json` (SHA-256 `694c43532ac90504947bd5cfe9e34369cae68e2164683e8c3f772138022d45b4`), `support/aeneas-identity-manifest/handoff-manifest.json` (SHA-256 `e9870d6f9844eb5ebc192d297d642319333549aac483d9f9a3322c75ba3c8826`), `support/aeneas-identity-manifest/fixture/`, `support/aeneas-identity-manifest/inputs/`, and `support/aeneas-identity-manifest/outputs/`.
  - `support/aeneas-declaration-block-diff/compare.py`, `support/aeneas-declaration-block-diff/check.py`, `support/aeneas-declaration-block-diff/comparison.json`, `support/aeneas-declaration-block-diff/source-results.json`, `support/aeneas-declaration-block-diff/source-handoff-manifest.json`, `support/aeneas-declaration-block-diff/inputs/`, and `support/aeneas-declaration-block-diff/outputs/`.
  - `support/aeneas-manifest-batch-oracle/probe.py` (SHA-256 `2ff31ce81b1a85295b34c3f9aaf80e2e9f36379b4a7da4d266030e34ccd8bb56`), `support/aeneas-manifest-batch-oracle/results.json` (SHA-256 `e5da18ed41a366760621b10a8bbfe0350104493706e997fb1633221e3fc1bba1`), `support/aeneas-manifest-batch-oracle/declaration-manifest.json` (SHA-256 `a3a20c859da78e1ecf0a893d674e2e7fa2f6e582ed1bb463cbca9915e1411f9c`), and `support/aeneas-manifest-batch-oracle/work/`.
- **Memory-versus-file handoff subprobe:**
  - `support/aeneas-handoff-memory-vs-files/probe.py`, `support/aeneas-handoff-memory-vs-files/check.py`, `support/aeneas-handoff-memory-vs-files/results.json`, and `support/aeneas-handoff-memory-vs-files/work/`.

## Revalidation

To verify the retained declaration-block and memory-versus-file handoff evidence offline without invoking Charon, Aeneas, or Lean, run:

```sh
python3 -B support/aeneas-declaration-block-diff/check.py
python3 support/aeneas-handoff-memory-vs-files/check.py
```

To re-execute the full suite on a host with the pinned Charon, Aeneas, Rust nightly, and Lean `v4.30.0-rc2` binaries and cached `Aeneas.olean` runtime, run `probe.py` in each subprobe directory (`support/aeneas-process-contract/probe.py`, `support/charon-aeneas-boundary/probe.py`, `support/aeneas-identity-manifest/probe.py`, `support/aeneas-manifest-batch-oracle/probe.py`, and `support/aeneas-handoff-memory-vs-files/probe.py`), then re-run the checkers.
