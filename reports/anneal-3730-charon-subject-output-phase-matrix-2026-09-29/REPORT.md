# Charon/Cargo compilation subjects and regular-file output interruption

## Summary

Pinned Charon 0.1.210 extracted a small offline Cargo fixture through separate library, binary, test, feature, source-order, flag, and host-target requests. The important subject-control failure was `charon cargo ... --test check --dest-file one.llbc`: each of four identical requests invoked Charon's rustc driver for the library, the named test, **and** the binary. The one destination ended as the test crate in two runs and the binary crate in two runs, although all four commands exited 0. A success exit and a parseable LLBC therefore did not identify the requested test compilation unit. Verbose Cargo invocation records and each result's serialized crate name establish the mismatch.

A file-size limit interrupted Charon while writing a regular-file destination. The process failed with signal 25; the prior parseable destination was replaced by a 4,096-byte unparsable file. A separately retained last-good LLBC stayed intact, and an uncapped retry of the same request replaced the damaged destination with a parseable LLBC. This is direct evidence that this `--dest-file` path did not provide atomic last-good publication under the induced output failure. The package preserves the partial bytes and request-private manifests. There is no Anneal extraction service or same-process Charon-library experiment here.

This report addresses [#3731](https://github.com/google/zerocopy/issues/3731) I073–I080/I105/I148 and [#3730](https://github.com/google/zerocopy/issues/3730) D01–D07 within the exact bounds below. The strongest new results concern I076 and I078.

## Fixture, identities, and guardrails

The fixture `subject_matrix` has an independent library, an independent `subject_matrix_cli` binary, and a `check` integration test. The library has `alpha`, `beta`, mutually exclusive feature functions, and two doc markers. The binary and test do not depend on the library's symbols, avoiding a Charon wrapper limitation observed in a discarded setup run where an expected library rlib was absent. All retained requests used Cargo `--offline --locked -v`, one Cargo job, disabled incremental compilation, and request-private copied source roots, target directories, output paths, and JSON manifests. At most two Charon processes ran simultaneously. The work directory was under this conversation's Meta/Data scratch area; no toolchain was installed.

Executed host: macOS 26.6.2 arm64. Binary SHA-256: Charon `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`, Cargo `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1`, rustc `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc` from nightly 2026-05-31. The base library source SHA-256 was `b4013f29aab99417d099eba3acc9bb803e600b2e1038c040b89d23a16614d0e7`. Each `support/manifests/*.json` records the full source-tree hashes, flags, target/output paths, binary hashes, verbose rustc driver lines, exit, time, destination hash and parse status. `support/raw-results.json` collects the 17 requests and target inventories.

## Compilation-unit matrix

| Request | Actual driver units in the retained run | Final destination |
| --- | --- | --- |
| `--lib` | `subject_matrix` | Parseable library LLBC, 14,708 bytes. |
| `--bin subject_matrix_cli` | library, then binary | Parseable binary LLBC, 54,391 bytes. |
| Four `--test check` requests | library, test, binary in varying order | Two parseable `check` LLBCs and two parseable `subject_matrix_cli` LLBCs. All exited 0. |
| `--lib --features selected` | selected library | `feature_only` present, `default_only` absent. |
| `--lib --target aarch64-apple-darwin` | host-target library | Parseable library LLBC. |
| `--lib` with `RUSTFLAGS=-C opt-level=1` | library | Parseable library LLBC; same local names as baseline. |
| `--lib` after comment prefix, declaration reorder, and A restoration | one library per request | Parseable LLBCs with source spans/order reflecting each source; restored A had the baseline local names and body-hash projection. |
| Two simultaneous private `--lib` requests, default and selected | one library driver per process | Separate parseable outputs with the respective feature functions. |
| `--lib --target x86_64-apple-darwin` | attempted library | Exit 101, no destination: the x86_64 standard library was not installed. |

The four test requests are the most informative collision control. For each, Cargo's verbose log contains three `Running ... charon-driver rustc --crate-name ...` lines, while the single `--dest-file` contains one serialized crate. The final winner varied in this run (`check`, binary, `check`, binary). The output crate name and local functions, not the requested `--test` flag or exit 0, reveal which unit was actually retained. This does not prove the precise writer interleaving or that every Charon revision behaves alike. It shows that this invocation-wide destination is insufficient as a request-private unit artifact when Cargo invokes more than one driver. One safe producer design would bind each captured driver result to its full compilation-unit identity and select explicitly before publication; that is a design implication, not an implemented Anneal result.

The two simultaneous requests used separate source, target, and output roots. They completed in about 0.18 seconds each and left distinct default/selected function sets. The result supports private-root coexistence for this tiny fixture, not shared-writable Cargo target safety. Target inventories after the run summed to about 101 KiB across the retained request roots; the quota target had 10 files/4,498 bytes before retry. These are logical file bytes, not allocated disk blocks, peak RSS, or a scaling estimate. No worker pool or reused Charon library was tested.

## Source and flag identity

The `lib-comment` fixture prepended an unrelated source comment: `alpha`, `beta`, and `default_only` kept their names but source line numbers moved by one. `lib-reorder` swapped `alpha` and `beta`, changing declaration order and span positions; `lib-restored` used the original source bytes again. Explicit host target and `RUSTFLAGS=-C opt-level=1` retained the same local function-name and body-hash projections as base in this run. Raw LLBC hashes differed even for restored A, so neither raw byte equality nor a source-blind normalization is justified. The serialized body hash is itself sensitive to declaration identifiers and metadata under reorder/comment shifts; it is not a semantic equivalence proof. The manifest must retain source bytes, Cargo target/features/flags, tool binary, and exact output's crate identity before treating a result as current.

The x86_64 request failed with rustc E0463 (`std` unavailable) and no LLBC. This bounds host/target evidence to the installed aarch64 macOS target plus a missing-target failure. It does not test an installed cross target, proc macro host units, build scripts, dependency closure, or target-specific code generation.

## Regular-file output-phase failure and retry

The probe first copied a successful library LLBC to `last-good.llbc` and to the active regular-file destination. The next Charon request inherited `RLIMIT_FSIZE=4096`. Its driver received signal 25; Charon/Cargo returned 255, and the active destination became exactly 4,096 bytes with SHA-256 `4390037b0612ebba6ea815a004418de02c8a60d4e14cb0952ff47750203315aa` and no parseable LLBC object. The preserved old output's acquired SHA-256 was `c4060a3b6d1221566c26acc9610d4f76e8011bd5c2deb5c831c2e60a0df18e24`. `support/artifacts/quota-partial.llbc` retains the actual incomplete bytes; `support/artifacts/last-good.llbc` retains the independent old bytes. The failing request's manifest records the signal and driver command.

An uncapped retry using the same source root, Cargo target, and destination returned 0 and produced parseable library LLBC. The last-good copy did not change. Each process group had no remaining PID when checked after completion. This is a bounded cleanup observation after file-limit failure and retry; it does not cover SIGKILL during parsing, descendant escape, filesystem crash durability, or every extraction stage. A consumer must reject the failed and partial result; merely finding the destination path after failure would be unsound. The probe makes no claim that Charon itself publishes atomically.

## Exact residuals

| Item | Evidence added | Still unresolved |
| --- | --- | --- |
| I073/I074 | Private copied source roots with identical A bytes, comment/reorder variants, complete source manifests. | Unsaved editor overlays, original-path equivalence, path dependencies, `build.rs`, proc macros, `include_*`, env inputs; prior warm-target report covers some of these separately. |
| I075 | Every private request's output and driver line checked; no warm-Cargo omission was induced here. | Wrapper and target combinations that skip extraction in a warmed target; prior warm-target report contains a narrower successful regeneration control. |
| I076 | Lib/bin/test/feature/host-target matrix; four `--test` commands had three driver units and two final crate identities despite exit 0. | Complete unit-key schema, host+target proc macro units, same-named sibling crates, multi-target destination handling in a real Anneal wrapper. |
| I077 | Fresh processes with A, reordered B, A restoration and post-failure retry. | Same-process Charon library reset, reusable worker state after errors, long-lived compiler-driver feasibility. |
| I078 | Real regular-file output failure yielded a 4 KiB unparsable replacement; independent last-good survived and retry repaired active output. | Kills at parse/translation/pre-open/post-write/rename phases, version and full-subject validation, transactional wrapper publication, unsupported-code distinction. |
| I079/I148 | Source comments/order, feature, host-target flag, optimization flag, raw and projected identities retained. | Semantics-preserving normalization across revisions, annotation association under all perturbations, actual cross-version diff oracle. |
| I080/I105 | Two private concurrent requests, target inventories, file-limit interruption, process-group-empty checks and retry. | Shared-writable targets, real overlays at scale, peak memory, external cancellation and descendants during each pipeline stage. |

## Replay and evidence

Run `python3 support/probe.py --work /absolute/absent/owned/path` from this report package. The parent directory needs at least 15 GiB free. The script recreates `support/artifacts/`, `support/manifests/`, and `support/raw-results.json`; copy the package first if preserving these acquired bytes. It checks each successful result, feature identity, all three driver units for test requests, private concurrent outputs, partial-file rejection, last-good preservation, uncapped retry, absent cross-target result, and empty process groups. The run is one observed schedule; test-unit completion order, raw LLBC map serialization, file hashes, and timings may vary. The retained `support/raw-results.json` SHA-256 is `153519e76c32aae9ebaf735eac748519deaec9023db9566f8d5e6d372fd9b56a`; script SHA-256 `71f10e3745448d1da23af25c985688bdff7c7aff71f325b87e127b5ecda1e8fa`.
