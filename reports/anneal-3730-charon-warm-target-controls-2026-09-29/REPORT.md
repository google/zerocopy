# Charon/Cargo warm-target and materialized-snapshot controls

## Summary

In this pinned, offline two-crate Cargo fixture, `charon cargo` regenerated a fresh LLBC on repeated requests with a warm target directory: it overwrote a deliberately invalid destination sentinel and created an absent destination. Ordinary Cargo's second build had reported `Fresh`, so the observed Charon invocation behaved differently from a plain warm build. A copied B workspace with a private target translated its own path-sensitive build-script constant as `217`; the same B workspace using the origin's warmed target translated the edited B Rust function but reused the origin's old generated constant `205`, still exiting 0 with `has_errors: false`. An independent cold build of B at the origin path also produced `205`. This is a concrete failure of the assumption that copying source files plus sharing a Cargo target preserves the intended compilation subject.

The experiment adds bounded execution evidence for [google/zerocopy#3731](https://github.com/google/zerocopy/issues/3731) I073–I080 and #3730 D07–D09. No Anneal or editor overlay implementation was exercised.

## Applicability and fixture

The executed tools were Charon `0.1.210` (binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`), Cargo nightly 2026-05-31 (`71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1`), and rustc nightly 2026-05-31 (`2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`) on macOS arm64 with 8 GiB RAM. The host had about 52 GiB free at setup. A 20 GiB free-disk guard, `CARGO_BUILD_JOBS=1`, `CARGO_INCREMENTAL=0`, `RAYON_NUM_THREADS=1`, offline/locked Cargo flags, and sequential calls bounded the probe. Each Charon request had a 50-second timeout. The retained measurements are one run per cell, not benchmark distributions or peak-RSS measurements.

The `warm_probe` app has a path dependency `dep_path`, a `build.rs` that writes `SNAPSHOT_VALUE = BUILD_VALUE + len(CARGO_MANIFEST_DIR)`, and an `include_str!("payload.txt")` function. The ordinary Rust function `step` and invented `/// proof-id:` comment change from A to B. A B candidate was first held only as fixture text; its bytes were written to a copied `shadow-copy-longer` workspace while the original disk workspace remained A. The same B source and payload bytes were then temporarily written to the original workspace for a separate cold-target comparison and restored to A. The `proof-id:` string is a test marker, not an established Anneal annotation grammar.

All Charon calls selected exactly `--package warm_probe --lib` with `--preset aeneas`, `--offline`, and `--locked`. Full source-tree hashes, command arguments, statuses, generated build-script artifact hashes/text, target inventories, and LLBC projections are in `support/results.json`. Ten successful LLBCs are separately preserved under `support/artifacts/cases/`; targets were deleted after their file inventories were saved.

## Observations

### Warm targets did not skip this Charon-producing invocation

| Case | Wall time | LLBC destination | Relevant target state |
| --- | ---: | --- | --- |
| Origin A, cold shared target | 0.518 s | New parseable `warm_probe` LLBC | 1,193,497 bytes after build. |
| Origin A, same warm target, sentinel prewritten | 0.077 s | Sentinel overwritten by parseable LLBC | Target inventory stayed 1,193,497 bytes. |
| Origin A, same warm target, destination absent | 0.077 s | New LLBC created | Same target size. |
| Origin A, separate cold target | 0.502 s | New LLBC created | 1,193,539 bytes. |
| Origin A, separate target then warm sentinel | 0.077 s | Sentinel overwritten | 1,193,539 bytes. |
| Origin A, target prewarmed by ordinary Cargo | 0.509 s | New LLBC created | 2,236,319 bytes after Charon. |

The two ordinary `cargo build -v` calls into the prewarm target completed in 0.414 and 0.017 seconds; the second logged `Fresh warm_probe`. The subsequent Charon request nevertheless logged compilation and created the LLBC. Its target tree was about 2.24 MB, versus about 1.19 MB after a Charon-only cold build, with exact per-file hashes retained. These are fixture-specific target inventories, not a general claim about Charon's cache design or physical disk blocks.

All six A Charon output modes in the table plus restored A had the same local function-body-hash projection, including `step`, `payload_len`, `generated_value`, and the build-script constant. Their raw LLBC hashes differed in this run, so the report does not equate raw bytes across warm/cold/path cases. The sentinel control is decisive for I075 only in the tested command/flags: a warm Cargo target did **not** cause a success-without-fresh-LLBC here. It does not establish that every wrapper, target selection, or Cargo/Charon revision will force the producer.

### A copied workspace and a shared target produced a mixed subject

The shadow B and temporarily materialized origin B had **identical source-tree file hashes**, including Cargo manifests, lockfile, path-dependency source, app source, build script, and payload. A cold private-target Charon run in the shadow produced `generated.rs` text `pub const SNAPSHOT_VALUE: u32 = 217;`; the same B bytes at the origin path produced `205`. This is the intended path-sensitive behavior of the fixture: `CARGO_MANIFEST_DIR` differs. The shadow run did not mutate the origin A source or payload before the explicit disk-B comparison.

The shadow B extraction against the origin's **warmed shared target** exited 0 and generated B's `step` body, matching the private shadow B oracle. Its `generated.rs` artifact and serialized `SNAPSHOT_VALUE` body instead matched origin A (`205`), not private shadow B (`217`). The shared target retained 1,193,497 bytes, the same size as origin A's target after this cell. The run's LLBC had `crate_name: warm_probe` and `has_errors: false`; those fields alone cannot detect this stale build-script product. The separately retained per-file target hashes and the `SNAPSHOT_VALUE` body hash establish the split.

This demonstrates a **specific same-target reuse hazard** for path-sensitive build-script output when copying this workspace. It does not prove that arbitrary Cargo target sharing is unsafe, that the Rust compiler itself miscompiled the source, or that a path-insensitive build script would behave the same way. It does show why a materialized snapshot needs its dependency/build-script/environment closure and a fresh oracle for any proposed target sharing rule. A source-tree digest by itself omitted the location value consumed by `build.rs`.

### Failure leaves old LLBC at the requested path

After successful A extraction, the script prefilled a destination with that successful LLBC, wrote malformed `pub fn broken(` to the origin app, and invoked Charon against the warm target. The process exited 101 with an unclosed-delimiter error; the destination SHA-256 before and after was identical. It remained parseable and marked `has_errors: false`, but belonged to the earlier A request. The fixture source was restored afterward. This repeats the old-output failure class under a warmed Cargo target and directly tests the artifact hash; status plus request-specific ownership must gate publication.

## Exact residuals

| Item | New executed slice | Remaining work |
| --- | --- | --- |
| I073 | Saved A versus B materialized in a shadow tree, then B temporarily saved at the original path. | Real unsaved editor overlay, annotation-only candidate, and an Anneal UI contract that labels which bytes were verified. No compiler overlay API was tested. |
| I074 | Path dependency, build script, generated Rust, included text, and moved workspace; private/shared target comparison found a stale path-sensitive product. | Proc macros, richer environment/target inputs, absolute-path assumptions in dependency code, and a faithful general shadow-workspace construction algorithm. |
| I075 | Warm same/separate targets, invalid sentinel, absent destination, and plain-Cargo `Fresh` versus Charon regeneration. | Other wrapper modes, target kinds, Charon/Cargo revisions, interruption before producer launch, and an actual success-without-new-LLBC counterexample if one exists. |
| I076 | One explicit package/library unit and its `crate_name` were checked for every successful LLBC. | Multiple primary targets, same-named crates, host/target units, parallel producers, and destination collision arbitration. |
| I077 | Fresh Charon processes on A/B/A-like source states, including failure. | Same-process library/driver reset, error-state reuse, cancellation, and fresh-oracle comparison for a reused process. |
| I078 | Warm-target malformed source retained old LLBC byte for byte despite nonzero status. | Kills at extraction stages, malformed/partial current artifacts, atomic publication, version/subject completeness fences under multi-unit output. |
| I079 | Exact raw LLBCs, source-file hashes, generated-file hashes, path-sensitive constant bodies, and A body projections. | Validated LLBC normalization, comment/order/flag/compiler-revision ablations, and semantic equivalence versus provenance freshness. |
| I080 | Separate/shared target file inventories and size snapshots; ordinary Cargo prewarming expanded the resulting target tree. | Parallel consumers, locking/contention, cancellation cleanup, incremental-on matrix, sustained RSS/disk drift, and larger dependency workspaces. |

No Aeneas, Lean, proof obligation, current Anneal pipeline, editor, MCP, or theorem verification ran in this package. The target artifact hashes are retained, while target files themselves were removed to respect disk limits; the raw LLBCs and workspace fixture remain for replay. The single-run timings should not be used as throughput predictions.

## Evidence and replay

- `support/probe.py`, SHA-256 `c9bc12936bf3dd34741f615eee0670457c5d22e156c750bfb6bc0c5bcdade665`: fixture construction, serial command matrix, source restoration, sentinels, artifact inventories, and assertions.
- `support/results.json`, acquired SHA-256 `cbab1f2a121f0596e05cb071b07c6e6c5e4d3adcebae7478be6b29bf73da53a6`: complete records for 11 Charon requests and two ordinary Cargo warmups, including command/status/log/time, source-tree and target-file SHA-256 values, generated Rust text, and parsed LLBC function bodies.
- `support/versions/` preserves A/B source and payload bytes; `support/fixture/origin/` contains restored A and `support/fixture/shadow-copy-longer/` contains B. `support/artifacts/cases/` retains every successful request's LLBC. `support/artifacts/failed-old.llbc` is deliberately the previous successful LLBC carried through a failed request.

Run `python3 support/probe.py` from this package directory on a host with the exact installed tool paths shown in the script. It recreates its fixture/artifacts/results, asserts all discriminating controls, and removes transient target directories. Compare the asserted relationships and input/artifact hashes before comparing wall times or raw LLBC bytes; absolute paths affect this fixture's generated value by design.
