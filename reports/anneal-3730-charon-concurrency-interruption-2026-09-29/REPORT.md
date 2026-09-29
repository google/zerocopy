# Concurrent Charon outputs and interrupted artifact families

## Summary

Pinned Charon 0.1.210 was run against two tiny saved Rust crates with at most two extraction processes at once. When `alpha` and `beta` used **different destinations**, both direct `charon rustc` and `charon cargo` pairs exited 0 and left two parseable, correctly identified LLBC files. When both processes used **one destination**, a zero exit from each producer did not imply that the shared file was usable: in the preserved run, 1/6 direct and 1/3 Cargo collision rounds left malformed JSON. In five `--format all` shared-base rounds, one JSON LLBC was malformed while the companion Postcard file remained deserializable. These are observed witnesses under scheduling races, not failure-rate estimates.

A FIFO at the second `--format all` output created a controlled stop **after** the JSON LLBC was complete and **before** a regular Postcard artifact existed. The process was still alive, was killed as a process group, and exited `-9`; a retry to the same base produced a complete JSON/Postcard pair. A separate FIFO stream kill captured 8,185 non-JSON prefix bytes; those bytes are a pipe stream specimen, not a partial regular LLBC file. Finally, a malformed Rust request against an existing valid destination exited 2 and left the old `alpha` LLBC byte-identical. Thus a consumer needs successful request identity, expected crate identity and a complete output-set transaction; parseability or file presence alone is insufficient in these observed cases.

## Applicability and method

The executable subject is Charon 0.1.210, SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`, with nightly-2026-05-31 Cargo/rustc hashes in `REPORT.json`. The matching source revision is identified there; behavioral claims below come from direct executable runs. The host was arm64 macOS with 8 GiB RAM. `support/probe.py` used only already installed binaries, offline Cargo packages with no registry dependencies, `CARGO_BUILD_JOBS=1` **per producer**, `CARGO_INCREMENTAL=0`, `RAYON_NUM_THREADS=1`, a 10-GiB free-disk guard and 25–35-second command timeouts. Separate Cargo pairs had separate `CARGO_TARGET_DIR`s; no backup volume, shared production target, or global installation was touched. The run-4 scratch tree occupied 1.5 MiB.

The fixture sources were two public functions per crate: a crate-specific `marker_alpha` or `marker_beta`, and a common function. Their source hashes were `8159027a71991d6bb4d95a90d461badfcdf4618c7eae11b5d79015ade3bcee6f` and `ce3f4d3f2789922c1f8fe59c9d49688ce32fdb348fc512880610f7bd0ab9866f`. Charon's `--dest-file` supplied the output path; for `--format all`, it supplied a base that produced `.llbc` and `.llbc.postcard`. Every regular JSON output was parsed and checked for `has_errors`, `translated.crate_name`, local declarations, byte size and SHA-256. Postcard outputs were checked by pinned `charon pretty-print --format postcard` and marker name. Full commands, exits, stderr/stdout, paths normalized to `$WORK`, and file-set manifests are in `support/results.json`.

## Findings

### Destination isolation worked in this small case; shared destinations did not

Two direct `charon rustc` processes launched together with private `alpha.llbc` and `beta.llbc` destinations both exited 0. The files parsed with `has_errors: false` and the expected `alpha`/`beta` crate and marker names. Two offline `charon cargo` builds with private target directories and private LLBC destinations did the same. **Basis: execution.** This is one two-process case, not a proof of safe parallel scaling or shared-cache independence.

The collision results from the preserved run were:

| Shared output mode | Rounds | Producer exits | Parseable outputs | Malformed outputs |
| --- | ---: | --- | ---: | ---: |
| Direct `charon rustc`, one `.llbc` | 6 | Both 0 in every round | 5 | 1 |
| `charon cargo`, private targets but one `.llbc` | 3 | Both 0 in every round | 2 | 1 |
| Direct `--format all`, one output base | 5 | Both 0 in every round | 4 JSON files | 1 JSON file |

In the malformed Cargo witness, the JSON ended with an extra fragment resembling `ors":false}` after a complete object. In the direct witness, the parser rejected a mixed shared file. The malformed `--format all` JSON had a deserializable Postcard companion identifying `beta`; the four rounds where both formats decoded showed the same crate in both formats. **Basis: execution.** Concurrent writes may also yield a valid whole `alpha` or `beta` file; the observed schedule changed the winner. The experiment did not observe a fully parseable cross-format subject mismatch, and it does not establish that every Charon output is always corrupted under contention.

### Restart, source order, flags and warmed Cargo are distinct controls

Two fresh Charon processes translated the identical `alpha.rs` source into different destination paths. Raw LLBC SHA-256 values differed (`1ee92d10…` and `7805baf5…`), while the local-name lists and per-body JSON hashes matched. The LLBC embeds destination/options and an order-sensitive short-name map, so byte inequality in this control is not a demonstrated semantic difference. Reordering two source declarations changed their serialized local order; adding `--cfg selected` added `alpha::flagged`, whereas the same source without the flag did not. Per-body hashes also changed with some ordering/flag controls and should not be treated as a semantic comparator without examining IDs, spans and provenance. **Basis: execution.** `support/summary.json` records full hashes and local-name lists.

With a single warm Cargo target and identical destination argument, all three requests exited 0 and wrote an LLBC: first build, unchanged source after output deletion, then a comment-only source touch. Cargo stderr said `Compiling alpha` each time, including the unchanged request. This exact `charon cargo` fixture therefore did **not** reproduce a skipped Charon-producing invocation. It does not rule out skips under a different target, wrapper fingerprint, Cargo profile or package graph. **Basis: execution.** Every CLI request used a fresh process; Charon same-process library reuse/reset remains untested.

### Interrupted output can leave stale or incomplete publication candidates

After a successful `alpha` extraction, a malformed `beta` input was sent to the **same regular destination**. Charon exited 2 and the old `alpha` file retained SHA-256 `6de2fd7b4e4db63bf445282d197353d1bfcc259993b6349f74ee9bf1c848e4c0`. A consumer that checks only file existence could mistake it for the failed `beta` request's result. **Basis: execution.** This tests a compiler failure before new serialization; other failure stages could behave differently.

Three named-pipe barriers separated output phases:

1. With a FIFO destination and no reader, the Charon process was still alive after the small crate had time to compile; killing its process group returned `-9`. No regular destination existed. This is a bounded open/write barrier, not a traced internal call site.
2. With a FIFO reader for a 320-function crate, 8,185 bytes had arrived while the writer was alive. Killing its process group returned `-9`; the captured prefix SHA-256 was `f57a1140086a74c5f2c3bcf539424a37c103846fdcecaaa03a89763b31eab063` and was not valid JSON. The FIFO is not a regular file, so this does not show Charon leaving a partial regular file on disk. A fresh retry to a regular destination exited 0 and produced a parseable `large` LLBC.
3. With `--format all`, the first `.llbc` was complete and parseable (`alpha`, SHA-256 `6425124eb0020595b8630d5363e7da915c7214dc9f37e24ef83327cb0889cbca`) while the second `.llbc.postcard` name was a FIFO rather than a regular artifact. Killing the still-live process group returned `-9`. After removing the FIFO, a same-base retry exited 0 and wrote a parseable JSON LLBC plus a Postcard file that `charon pretty-print` accepted. **Basis: execution.** This directly shows a non-atomic two-file output family under a controlled interruption, without claiming a particular regular-file partial-write behavior.

## Remaining #3731 work

| Item | This report's evidence | Exact residual |
| --- | --- | --- |
| I073 saved Rust versus overlay | All extraction inputs were saved, stable files. | Compare unsaved buffer/shadow workspace and clean saved baseline with Cargo build scripts, macros, included files and source identity. |
| I076 compilation-unit collisions | Separate alpha/beta direct and Cargo units; shared-destination races. | Host/target variants, feature/profile collisions, workspace unit graph identity and complete manifest authentication. |
| I077 process isolation/reset | Fresh process restarts and concurrent independent processes. | Same-process Charon API reset/state leakage and cancellation feasibility; no library worker was exercised. |
| I078 output transaction/completeness | Malformed shared files, stale retained file, two-format partial family and successful retry. | Real Anneal stage/publish transaction, atomic family publication, requested-subject echo, schema/version and integrity checks under every failure stage. |
| I079 LLBC identity/normalization | Raw hash differs across output path/process despite stable local function bodies; order/flag controls. | A justified semantic comparator that preserves spans, crate/tool/options/subject identities and tests harmless metadata variations. |
| I080 resource sharing/cleanup | At most two bounded producers, separate Cargo targets and process-group kills. | Measured physical memory/disk and descendant cleanup across many workers, reused targets and long runs. |
| I105 cancellation | Direct Charon/Cargo kill barriers around output. | Per-stage cancellation across actual Cargo→Charon→Aeneas→Lake→Lean trees, late messages and scheduler-owned publication fences. |
| I148 translation determinism | Restart/order/cfg/raw-hash controls plus selected local body/name projection. | Full LLBC semantic equivalence and generated Lean comparison across pins, process histories and harmless textual instability. |

## Evidence, limits and replay

- `support/probe.py` (SHA-256 `bf8867ed0d0da1719c39fb963c3f15896901cae7af73c544145cc568b8d0565f`) generates all sources, packages and barriers. `support/analyze.py` asserts distinct-output identities, collision exits/witnesses, failure/stale hashes, interruptions and retries.
- `support/results.json` (SHA-256 `14b79f1b2456174600ac83707527030634f47953acf6719651dd7b3325dfd9b9`) preserves every command and output projection; `support/summary.json` contains the compact run-4 outcomes and a hash manifest for 34 raw files under `support/artifacts/`.
- The raw malformed collision LLBCs, full distinct/restart/variant LLBCs, complete first file from the interrupted two-format family, interrupted FIFO byte prefix and both retry outputs are preserved in `support/artifacts/`. They may embed disposable scratch paths; those paths are evidence, not durable dependencies.

Run `python3 support/probe.py --work /new/absent/conversation-scratch/path`, then `python3 support/analyze.py` from this package on the pinned local toolchain. The work path must not exist; no download or installation occurs. Collision interleavings are nondeterministic, so a new run need not reproduce the same count or winner. The analyzer expects at least one malformed shared-output witness for the preserved run; if replay has none, inspect all successful exits and repeat the bounded collision rounds rather than treating zero observed corruptions as proof of safety. The FIFO controls require local named-pipe semantics and do not substitute for regular-file crash-durability or a product-level output transaction.
