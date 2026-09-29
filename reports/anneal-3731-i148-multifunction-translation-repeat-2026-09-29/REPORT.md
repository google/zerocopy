# I148: error-free multi-function Charon/Aeneas repeat corpus

Observed on 2026-09-29 with the locally installed Charon 0.1.210, Rust/Cargo nightly-2026-05-31, Aeneas selected by Anneal's nightly-2026.06.03 bundle, and Lean 4.30.0-rc2. `support/results.json` records exact executable hashes and invocations. This is a local component experiment, not an Anneal V2 product run.

## Fixture and method

The private Rust library has five public functions, one public two-field struct, branches, arithmetic, and calls among the functions. `support/fixture/` includes the source, manifest and offline lockfile. The runner invoked `charon cargo --preset aeneas` with one Cargo job, incremental compilation disabled, `RAYON_NUM_THREADS=1`, `--lib --offline --locked`, and the cached pinned toolchain. Three consecutive calls used the same source, target and LLBC destination; the first was cold and the next two were warm. Two further calls overlapped on the same source with private Cargo target directories and private LLBC destinations. This limited concurrent Charon work to two processes.

All five raw LLBC files were preserved. The checker parses each, requires `has_errors: false`, and compares complete JSON after two narrow operations: replacing `translated.options.dest_file` with a common marker and sorting `translated.short_names` by its six unique typed item keys. No declaration order, body, span, file, target, error flag, or other option is removed or normalized. The original raw bytes and provenance remain in `support/artifacts/`.

Each raw LLBC was copied unchanged to a private input path with the common basename `probe.llbc`, then processed by the pinned Aeneas CLI using `-backend lean -no-progress-bar -sequential -split-files -gen-lib-entry`. The common basename is necessary because Aeneas uses it in generated Lean module/import names. All generated files were retained and compared by inventory and whole-file SHA-256. One generated set was compiled with the cached Lean backend, followed by a direct `#check` of all five definitions and `#print axioms i148_corpus.combine`.

## Result

All five Charon calls exited 0 and produced error-free LLBC. Their five raw SHA-256 hashes differed. The only parsed differences were the requested destination path and the order of six `short_names` entries; after the two stated operations, the complete parsed LLBC values matched. The two concurrent Charon invocation intervals overlapped by about 165 ms, as retained in `support/results.json`. The timestamps bracket `subprocess.run`, rather than separately recording OS process start and exit times.

All five Aeneas calls exited 0 and generated the same three Lean files byte for byte: `Types.lean`, `Funs.lean`, and `Probe.lean`. `Funs.lean` contains the same five definitions (`add_one`, `choose`, `pair_sum`, `make_pair`, `combine`) in every case. It contains no literal `sorry`, `axiom`, `theorem`, or `decreasing_by` marker. The direct Lean compilation and five-name check exited 0. The printed axiom inventory for `combine` was `[propext, Classical.choice, Quot.sound]`; this is an elaboration result for the generated definition, not a Rust refinement proof.

The five Charon calls took 63–498 ms, the five Aeneas calls 226–265 ms, and the one direct Lean compilation/check sequence about 18.4 s on this host. These times are local observations with a warmed dependency cache, not a scaling estimate. The preserved package occupies under 1 MiB; no dependency was installed or downloaded.

## Scope and remaining work

This adds a successful, multi-declaration case between the earlier tiny Charon/Aeneas fixture and the large zerocopy library extraction whose LLBC reported errors. It demonstrates five distinct raw LLBC identities converging to one generated Lean file inventory under the pinned CLI and selected flags. It does not establish that arbitrary `short_names` reordering is safe for every LLBC consumer, that arbitrary textual variation preserves semantics, or that the generated model refines Rust. It does not measure Lake invalidation cost for this corpus; the published R43 package measured same-path Lake replay for its smaller order-only fixture. The selected Anneal V2 generation flags, publishing path, representative workload and proof/obligation provenance remain I148 gates.

## Revalidation

Run `python3 -B support/check.py` from this directory. It checks recorded tool hashes against metadata, retained source/raw/log hashes, commands and exit statuses, recorded invocation overlap, error-free and narrowly equivalent LLBC, identical generated Lean, five declarations, and the retained Lean check output without rerunning the tools or requiring the local executables. `support/probe.py` is the replay specification; it requires a fresh package with empty `support/artifacts/` and `support/logs/` directories and uses only existing local pins. The retained run rows do not capture child environment variables; the private Cargo target settings are preserved in the probe. The retained result was checked with `python3 -B support/check.py` after completion. The absolute paths in `support/results.json` record execution-time locations before the evidence was arranged into this reference package; the checker uses the retained relative evidence paths.
