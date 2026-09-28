# Charon extraction performance and scaling

## Summary

Sixteen bounded runs on a tiny three-function fixture measured whole-crate, one-root, many-root, and no-serialize modes. They establish a baseline only, not a scaling curve; the report defines controlled workload axes and coverage checks for larger Cargo and workspace studies.

## Applicability

Direct measurements use Charon 0.1.210, `--preset aeneas`, Rust nightly 2026-05-31, one macOS arm64 dependency-free source file, and one process at a time. Related corpus reports: [charon-dependency-and-source-coverage-nightly-2026-06-03](../charon-dependency-and-source-coverage-nightly-2026-06-03/REPORT.md), [charon-multi-target-cargo-behavior-0-1-210](../charon-multi-target-cargo-behavior-0-1-210/REPORT.md).

## Findings


Scope: current Anneal redesign; Charon extraction only. This report is Nix-independent and makes no performance commitment or verification claim. Anneal's [principles](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/PRINCIPLES.md) and [design contract](https://github.com/google/zerocopy/blob/bd0956be95c5f798f0c0484921b9b9d1fc6e9988/anneal/DESIGN.md) require complete coverage and explicit trust. A faster extraction is useful only if the selected Rust behavior and any omitted or opaque items remain visible in the result. The `v1/` tree is historical evidence, not current design authority.

### What the checked-in sources establish

- Charon's default `--start-from crate` enqueues the current crate module and traverses all its local items. Explicit `--start-from` paths, `--start-from-pub`, and `--start-from-attribute` select other initial items. Translation uses a queue and a processed set; references encountered during translation enqueue further items. Thus cost can depend on local crate size, selected roots, reachable bodies, and referenced foreign signatures, not just the number of root flags. See local Charon `docs/what_charon_translates.md` and `charon/src/bin/charon-driver/translate/translate_crate.rs` (`enqueue_module_item`, `translate`, and the queue loop).
- Current-crate items default to transparent. Foreign items default to `Foreign`: signatures are brought in and all-public struct fields or enum variants can be translated; bodies are generally omitted. `--include` can make a foreign item transparent, increasing the reachable graph. `--opaque` stops exploring a matched body or module, but must not be interpreted as a proved implementation. Prefix matching means a module pattern can affect a subtree. `--extract-opaque-bodies` can greatly enlarge extraction. Source annotations can be more opaque than CLI inclusion.
- `--start-from-pub` and `--start-from-attribute` iterate the crate's HIR definitions to find roots; their setup cost may therefore grow with total crate size even when few items are selected. Explicit path resolution also has a cost, so many root flags are not necessarily free. These are source-based expectations, not measured scaling laws.
- `charon cargo` runs `cargo build` with `RUSTC_WRAPPER=charon-driver`. Dependencies and host build scripts are compiled normally; selected target crates are extracted. Consequently a Cargo measurement includes dependency builds, build scripts, proc macros, rustc front-end work, Charon translation, transformation passes, and output serialization. The driver runs passes after rustc extraction and then serializes. See Charon `charon/src/bin/charon/main.rs`, `charon/src/bin/charon-driver/driver.rs`, and `charon/src/bin/charon-driver/main.rs`.
- Charon's CLI has `--no-serialize`, `--format json|postcard|all`, and `--ullbc`. These permit stage comparisons, but `--ullbc`, presets, MIR stage, opacity, and feature flags change the translated artifact and cannot be treated as interchangeable performance settings. Multi-target `--targets` currently spawns one thread per target and its help calls this path extremely slow; exclude it from a single-worker scaling baseline.
- Current Anneal `src/resolve.rs` resolves individual package targets and target kinds and provides a distinct LLBC path per artifact. The `src/scanner.rs` comment says Charon compiles the entire target. Those files establish the current artifact-resolution intent; the checked-in `src/main.rs` is still mostly setup scaffolding, so no end-to-end Anneal extraction performance is claimed here.

### Direct observation: one small existing fixture

The only measured input was `../charon-llbc-output-goldens-and-revision-diffs-2026-09-27/support/translation-goldens/probe.rs`, a 264-byte, dependency-free library source with three public functions (`checked_add`, `choose`, `bump`). From the checkout root, I sourced `$CHECKOUT_LOCAL_TOOLS/env.sh`, set `CHARON_TOOLCHAIN_IS_IN_PATH=1`, `CARGO_BUILD_JOBS=1`, `RAYON_NUM_THREADS=1`, and `CARGO_INCREMENTAL=0`, and ran `charon rustc --preset aeneas` directly. No Cargo workspace or dependency build was triggered. The wrapper `support/charon-scaling/measure.py` ran one Charon process at a time, killed its process group at 20 seconds (TERM, then KILL after 2 more seconds), and captured child exit, monotonic wall time, child CPU time, and macOS `ru_maxrss`. It and `runs.jsonl` preserve exact commands and per-run values. Four runs per mode were made in interleaved order; the first whole-crate run was cold relative to this sequence.

| Mode | Additional Charon flags | Emitted declarations (`ordered_decls`) | JSON bytes | Wall time, four runs (s) | Child peak RSS range (MiB) |
| --- | --- | ---: | ---: | --- | ---: |
| Whole crate | none | 6 | 19,822 | .269, .150, .086, .090 | 101.2–101.5 |
| One root | `--start-from crate::choose` | 1 | 5,739 | .089, .088, .088, .081 | 99.8–99.8 |
| Three roots | one `--start-from` each for `choose`, `bump`, `checked_add` | 6 | 19,874 | .090, .082, .090, .090 | 101.3–101.5 |
| Whole, no file | `--no-serialize` | not emitted | 0 | .083, .090, .090, .084 | 101.3–101.6 |

All 16 wrapper-recorded Charon commands exited 0 before timeout. The three emitted JSON files have `has_errors: false`. The one-root output contains only `choose`; the whole and three-root outputs contain the three local functions plus referenced external declarations. The slightly different whole/three byte counts also reflect options and ordering embedded in JSON, so raw bytes are not a semantic size comparison. `ru_maxrss` is the maximum resident size of a child process, not total simultaneous process-tree memory. On this tiny input, warm wall times are about 0.08–0.09 seconds across modes and the first whole run is an outlier; these data do not identify a useful scaling slope or isolate serialization cost. The earlier attempt to use `/usr/bin/time -l` wrote LLBC but returned 1 because its `sysctl kern.clockrate` query was denied; none of its timing is used above.

Exact measured command form (the wrapper fills in `MODE` and optional flags):

```sh
# Set PATH to the pinned local binaries identified above.
CHARON_TOOLCHAIN_IS_IN_PATH=1 CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 CARGO_INCREMENTAL=0 \
  python3 support/charon-scaling/measure.py MODE
```

The wrapper invokes `charon rustc --preset aeneas [mode flags] --dest-file support/charon-scaling/MODE.llbc -- ../charon-llbc-output-goldens-and-revision-diffs-2026-09-27/support/translation-goldens/probe.rs --crate-type lib --crate-name probe --edition 2021`; the no-serialize mode omits `--dest-file`. Each JSON record includes the literal argument vector. The environment was macOS Darwin 25.6.0, `arm64`. Local binaries reported Charon `0.1.210`, `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`, host `aarch64-apple-darwin`, LLVM `22.1.6`, Cargo `1.98.0-nightly (fbb61be30 2026-05-26)`, Python `3.14.7`, and GNU `timeout` `9.11` (the wrapper uses Python's timeout). SHA-256: local `charon` binary `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`; release `charon-driver` binary `09a530746044c0ef169f7d0cfa099700c06934163a70b138cafc6d125d08037e`; local driver launcher script `234ec4cd40eeb42fa1f749f653614cfc251a79bb1f53a903160b921b6cf90b90`. The local Charon source checkout is `0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, but that checkout hash alone does not prove the release binary's build identity.

### Proposed benchmark matrix (not yet run)

Use generated, deterministic crates in a dedicated scratch workspace, with fixed source templates and an input manifest recording item counts, source bytes, reachable nodes and edges, Cargo lockfile, feature/cfg set, target, exact tool hashes, and flags. Keep each scenario's crate count and dependency graph explicit. First run bounded pilot sizes; extend only after peak memory and wall time stay within the agreed budget. Run each cell three to five times, rotate order, and report individual values plus median and spread. Distinguish a clean target directory from a warmed dependency cache; never call a cache-warmed result a cold build.

| Question | Controlled fixture axis | Compare | Main readouts |
| --- | --- | --- | --- |
| Whole-crate extraction | 10, 100, then 1,000 independent functions; separately grow body statements and source bytes | Default `crate`; `--start-from` one function; `--no-serialize` at each size | Wall/CPU, peak process-tree RSS, LLBC bytes, local declaration and body counts, failures |
| Many roots | Fixed crate with 1,000 small independent items; choose 1, 10, 100, 1,000 distinct explicit roots, then equivalent `--start-from-pub`/attribute sets | Same reachable set against whole crate | Root-resolution time, translation time, duplicate enqueues if instrumented, output count, command length |
| Dependency chasing | Chain and branching call/type graphs at fixed total nodes; vary reachable fraction and foreign signature fanout | One root vs many roots; default foreign opacity vs a narrowly specified `--include` | Reached local/foreign items, body/signature presence, time/RSS/bytes; missing references and warnings |
| Large workspace | 1, 10, 50 workspace members of matched total LOC, then one large member; include path dependencies, a build script/proc macro case, and lib/bin targets | `charon cargo` selected `-p`/`--lib`/`--bin` versus `--workspace`; clean and warm target directories | Per-rustc-unit times, Cargo build time, total wall/CPU, concurrent RSS, LLBC artifact inventory, cache reuse |

For Cargo cells, use the same manifest and isolated `CARGO_TARGET_DIR`, `CARGO_BUILD_JOBS=1`, one target triple, `--locked --offline`, and an already local dependency set. Example shape (after generating and inspecting a fixture):

```sh
# Set PATH to the pinned local binaries identified above.
export CHARON_TOOLCHAIN_IS_IN_PATH=1 CARGO_BUILD_JOBS=1 RAYON_NUM_THREADS=1 CARGO_INCREMENTAL=0
export CARGO_TARGET_DIR=support/charon-scaling/target-CELL
gtimeout --signal=TERM --kill-after=2s 120s \
  charon cargo --preset aeneas \
    --dest-file support/charon-scaling/CELL.llbc \
    -- --locked --offline -j 1 -p FIXTURE_PACKAGE --lib
```

The 120-second bound is a **proposed** per-cell ceiling, not a run performed here. Pilot first with smaller limits; set a process-tree RSS ceiling and free-space check before 1,000-item or 50-member cells. Use separate output paths for each selected target. Do not use one fixed `--dest-file` for a multi-target Cargo selection: selected rustc units could otherwise overwrite the artifact, invalidating both coverage and timing interpretation. A workspace wide Charon invocation should be attempted only after target enumeration and artifact routing are implemented and checked.

### Attribution and correctness checks

1. **Split Cargo build from extraction.** Record a plain `cargo build --locked --offline -j 1` baseline for each clean/warm fixture, then `charon cargo --no-serialize`, then full `charon cargo`, using identical package/target/features and distinct target directories or an explicitly documented cache protocol. The differences are diagnostic bounds, not additive phase timings: Cargo fingerprinting, driver changes, and cache state may differ. For exact attribution, add temporary Charon instrumentation in an isolated experiment checkout around root resolution, queue processing, transformation passes, and serialization; do not infer those phases from whole-process wall time alone.
2. **Capture rustc units.** Log each Cargo/rustc invocation, whether it is a dependency, build script, proc macro, or selected target, and its start/end time. Aggregate sequential CPU and wall by unit; sample the full process tree for concurrent RSS and disk I/O. Pin one Cargo worker so build parallelism does not hide extraction cost. Keep host and target compilation separate.
3. **Normalize by work actually done.** Parse LLBC for local/foreign declarations, body-bearing items, ordered declarations, source-file bytes, output bytes, and `has_errors`; save diagnostics and exit codes. Count graph nodes/edges and requested/reached roots from the fixture manifest. Compare time per reached body and per emitted byte only within identical presets and Rust/Charon versions. Repeat-run JSON ordering can vary, as recorded in [translation-goldens.md](../charon-llbc-output-goldens-and-revision-diffs-2026-09-27/REPORT.md); compare schema-aware counts, not raw digests alone.
4. **Detect lost coverage.** Every cell needs expected local root and reachable item sets, allowed foreign opacity, and an artifact inventory keyed by Cargo package, target, target kind, feature/cfg set, and target triple. A zero exit or smaller LLBC is not a performance success if a selected body vanished, a warning appeared, or one output overwrote another. Record unsupported translation and time/memory limit failures separately from valid completed samples. Verify the output's target and options before computing metrics.
5. **Interpret slopes cautiously.** Fit separate curves against total HIR items, root count, reachable translated items, output bytes, and Cargo units. A flat root-only curve with rising workspace time suggests build/front-end cost; a rise with reached bodies suggests queue/translation/pass cost; a rise only between `--no-serialize` and full output suggests export cost. These are hypotheses to confirm with phase instrumentation and repeated controlled runs.

### Limits and next decision

The observed data cover one tiny source file, one host/target, one preset, and warm local tools. They do not measure Cargo dependency compilation, many-root lookup at scale, foreign-body inclusion, large workspaces, end-to-end Anneal, or process-tree aggregate memory. The benchmark matrix is a proposal, not an outcome. The first useful next experiment is a bounded generated crate at 10/100 items and a two-member local Cargo workspace, after artifact routing and coverage assertions are in place.

**Setup or future prompt:** no setup change is needed. A future prompt should specify an explicit time, memory, and disk budget for the Cargo/workspace matrix and authorize generated scratch fixtures plus optional temporary Charon phase instrumentation in an isolated checkout.

## Boundaries

No Cargo dependency build, large crate, multi-member workspace, foreign-body expansion, or Anneal end-to-end extraction was measured. Process-tree RSS was unavailable; reported RSS is the Charon child metric only.

## Evidence

This report's subject identities are recorded in `REPORT.json`. Source links in the Findings are pinned to immutable upstream or zerocopy revisions where available. Executed-probe support material is included under `support/charon-scaling/`; local home/checkout prefixes are redacted in text artifacts.

## Revalidation

Use the retained fixture and measurement wrapper for repeat runs. For scaling, first pilot 10/100 generated items with one Cargo worker, strict time/memory/disk budgets, and output-coverage assertions before increasing sizes.
