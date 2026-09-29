# Two Charon consumers sharing a private Cargo target

## Summary

Two pinned `charon cargo` processes used distinct source roots and LLBC destinations but one fresh, writable `CARGO_TARGET_DIR`. Both processes overlapped, Cargo reported a build-directory file-lock wait for the second process, and both exited 0 with parseable LLBC. In a second fresh shared target, the first process was terminated after its build script entered; the companion completed and emitted parseable LLBC. The sampled process-tree RSS and scratch disk use stayed far below the preset guards. This is a two-process component control for #3731 I080, not a throughput or scaling envelope.

## Applicability

The executable subjects were Charon 0.1.210 (SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`) and the cached nightly-2026-05-31 arm64 Cargo and rustc binaries (SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1` and `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`). The host was macOS arm64 with 8 GiB physical RAM and 49,013,444,608 free disk bytes at preflight. There was no download or installation.

The exact input derives from the retained `anneal-3730-charon-warm-target-controls-2026-09-29/support/fixture/origin` tree (Git tree `af738e8e51a229bdc2940cc1caf176c2bec711b2` at the audited reference HEAD). A byte-for-byte copy is preserved in `support/fixture-origin/`. The probe copied it into private `A` and `B` roots, inserted a two-second sleep and entry marker into each copied `app/build.rs`, and invoked the same package/library selection from both roots. `A` and `B` had equal path lengths and otherwise equal source bytes; this fixture cannot discriminate a stale path-dependent build-script value between them.

Each child used `CARGO_BUILD_JOBS=1`, `CARGO_INCREMENTAL=0`, `RAYON_NUM_THREADS=1`, `CARGO_NET_OFFLINE=true`, and pinned `RUSTUP_HOME`, `CARGO_HOME`, `PATH`, and `DYLD_LIBRARY_PATH`. The command shape was:

```console
charon cargo --preset aeneas --dest-file "$SCRATCH/work/<phase>-<A-or-B>.llbc" -- --manifest-path "$SCRATCH/work/<A-or-B>/Cargo.toml" --package warm_probe --lib --offline --locked
```

The exact absolute paths, environment construction and process launch are in `support/probe-observed.py`; raw command stderr, PIDs, process-tree samples, exits and artifact hashes are in `support/results.json`. The `complete` and `cancel` phases used different fresh private target directories. The probe ran one pair at a time, with a 25-second phase timeout, a 1.5-GiB sampled RSS-sum guard per child tree, a 4-GiB private-work-tree disk guard and a 10-GiB free-disk preflight. No user's main Cargo target directory was used.

## Findings

### Both processes overlapped and Cargo serialized the shared build directory

In the `complete` phase, both process groups had live members in 43 sampled intervals spanning about 3.52 seconds. The first process's sampled tree RSS sum reached 155,184 KiB; the second's reached 33,664 KiB. Peak sampled scratch use was 1,376 KiB, and the final shared target occupied 1,260 KiB by `du -sk`. Both processes exited 0. Their private outputs were 24,068 bytes each, parsed as `warm_probe` LLBC with `has_errors: false`, and had distinct SHA-256 hashes preserved beside the transcript.

The second child's retained stderr contains `Blocking waiting for file lock on build directory`. This is an observed Cargo lock wait in an overlapping pair, not a proof that all Charon or rustc activity was serialized. The first child's stderr also records package-cache lock waits. **Basis: execution** in `support/results.json` and `support/artifacts/`.

### A cancelled owner did not prevent the companion from completing

In the `cancel` phase, the first child was sent `SIGTERM` to its process group after its modified build script wrote the entry marker and while the second child was still live. The first exited `-15` without an LLBC destination. A retained sample after that exit still shows members in the companion group. The companion then exited 0 and emitted a 24,064-byte parseable `warm_probe` LLBC with `has_errors: false`; its stderr includes a build-directory lock wait. The sampled tree RSS sums peaked at 181,696 KiB and 105,648 KiB, and the private work tree at 2,652 KiB. Neither resource guard fired.

After both phases, a separate post-run `ps` read found no members in any of the four process groups. It counted 35 regular files in each temporary target tree, then removed the private scratch `work/` tree and verified it was absent. The resulting `support/cleanup.json` is a post-run observation; it does not establish crash durability or absence of a process that escaped the inspected groups. **Basis: execution** in `support/results.json`, `support/cleanup.json`, and the retained companion LLBC.

## Boundaries

- This was two tiny, path-only Cargo packages with one path dependency, a deterministic two-second build-script delay, two launch phases and no registry packages. There was no representative long-running Anneal extraction workload, incremental-on matrix, larger dependency graph, sustained run, native plugin, editor, or proof consumer.
- The monitor slept 50 ms between samples and summed RSS over each observed process tree, including any shared pages more than once. The actual sampling interval also includes `ps` and `du` work. The maxima are neither true peak resident memory nor unique physical memory. `du -sk` samples measure private directory allocation, not machine-wide disk pressure.
- The equal-length source paths and identical Rust bodies mean parseable outputs do not rule out a wrong-root build-script product. The earlier warm-target report owns the separately observed path-sensitive stale-product counterexample; this experiment adds overlap, lock and cancellation observations.
- The retained script captures at most the last 3,000 characters of each output stream; all four recorded stderr values are shorter than that cap. Lock messages have no individual timestamps, so the transcript does not prove the exact instant at which the second child acquired or waited on the lock.
- Terminating one process group and observing companion completion does not establish safe shared-target reuse after arbitrary crashes, lock recovery under many producers, or any Anneal scheduling, publication or cleanup policy.

## Evidence

- `support/probe-observed.py` (SHA-256 `8ea5be460e0ce3d1ec99f7f6dfa1cf4ffac9c402eddbbcd6e6f69cb82aab0de1`) is the exact executed script. `support/probe.py` differs only by pointing to the preserved local `support/fixture-origin/` copy for replay.
- `support/results.json` (SHA-256 `ad8da2539f790ffb728374bb006925f90ee527863a692ab82a85b06868d8e31b`) retains preflight, 77 sampled process/disk snapshots, complete short stdout/stderr values, exits and output hashes. `support/artifacts/` retains the three successful raw LLBC outputs, with SHA-256 `9e8a04820ae19333e5bcb6e26e9007a2f1a6edf8b5ddb43d8914eb6dc37b9986`, `e284623c7768e23486bcfac0d0aa0b8bfebd38c5d7118c5350d28292b47c15c8`, and `dd05cfe299cf3f86201001c15e3f55def2c707ebda8c25e690252a8c78f5cd2c`.
- `support/cleanup.json` (SHA-256 `ce73e0fd77286c8b43f7bbffe4d9486645e8cae7b653d719e6a55ba82fca60e9`) records the later process-group check, target-tree counts and private scratch removal. `support/check.py` validates the retained pins, script/fixture relationship, bounded overlap, lock messages, cancellation/companion chronology, raw LLBCs and cleanup record without launching any tools.

Issue alignment: **additional partial evidence for #3731 I080**. Separate target-directory parallelism and sequential shared-target behavior were already retained in `anneal-3730-charon-concurrency-interruption-2026-09-29` and `anneal-3730-charon-warm-target-controls-2026-09-29`. This package exercises their missing intersection. The requested resource and cleanup comparison across representative parallel snapshot consumers remains open.

## Revalidation

Run `python3 support/check.py` in this package for the retained result. To repeat the tiny fixture, copy the package to a disposable location with at least 10 GiB free disk, run `python3 support/probe.py` there, inspect both result phases, and remove its generated `support/work/` after preserving any new output. The replay uses only the installed local binaries at the absolute paths in the script and writes no shared target directory. Compare exits, overlap, lock evidence, output parsing and bounds; do not require PIDs, timing, RSS samples or LLBC byte hashes to match across paths.
