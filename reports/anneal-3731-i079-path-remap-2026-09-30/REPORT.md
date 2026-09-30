# Rust path remapping in diagnostics and pinned Charon LLBC

## Summary

A deliberately invalid Rust source file produced a JSON diagnostic with `file_name: src/error.rs` under plain rustc and `/virtual/anneal-src/error.rs` with `--remap-path-prefix=src=/virtual/anneal-src`. The same flag was visibly passed to Charon's Cargo-invoked driver during a successful extraction of a tiny three-file crate. In both Charon LLBC outputs, the local file table retained `src/lib.rs`, `src/left/common.rs`, and `src/right/common.rs`; all three local item file IDs, spans, and source texts matched. The observation gives **I079** a concrete cross-tool path-remap specimen; it supplies **I031** context only. Both rows retain their existing residuals and product gates.

## Applicability and novelty

The run used the installed Charon 0.1.210 binary (SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`) and nightly-2026-05-31 Cargo/rustc binaries (SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1` and `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`) on macOS arm64. These hashes identify observed executables; this package does not establish their source build commits. Everything ran offline from locally installed tools, with private Cargo targets and separate LLBC destinations. There was no installation or download.

The earlier [cross-tool diagnostic path normalization](../cross-tool-diagnostic-path-normalization-2026-09-27/REPORT.md) report reviewed source but ran no remap fixture. The [v54 symlink-file identity](../anneal-3731-i079-symlink-module-identity-2026-09-30/REPORT.md) experiment compared lexical paths and inodes without a remap flag. This experiment exercises that remaining path-remap cell. The two module files are physical copies with identical bytes; Unicode text within them is incidental and adds no span-unit claim.

## Method

`prepare.py` pinned the exact fixture hashes and competing remap hypotheses in `oracle.json` before acquisition. `probe.py` copied the fixture once into a disposable private work directory. It ran four processes sequentially: plain rustc JSON error control; remapped rustc JSON error control; plain Charon Cargo extraction; and Charon Cargo extraction with `RUSTFLAGS=--remap-path-prefix=src=/virtual/anneal-src`. The Charon commands used `--preset aeneas`, `--offline --locked`, one Cargo job, no incremental compilation, and private targets and destinations. Exact argv, selected environment, process IDs, timestamps, raw stdout/stderr, LLBC bytes, exit statuses and resource samples are retained.

The rustc controls used the same `src/error.rs` bytes, with one deliberately unresolved `missingForRemap` identifier. The Charon controls used the same `Cargo.toml`, `Cargo.lock`, `src/lib.rs` and two `common.rs` files. The rustc error file was not part of the Charon crate module tree, so the Charon runs compiled successfully. This is a comparison of diagnostic path rewriting with serialized LLBC source identity under the same flag, not a claim that the diagnostic and LLBC refer to the same item.

## Findings

Both rustc processes returned status 1, as expected for the unresolved identifier. Parsing retained JSON stderr gives a single matching diagnostic span at line 1, column 41, with `file_name` `src/error.rs` in the plain control and `/virtual/anneal-src/error.rs` in the flagged control. The rustc command argv includes the remap flag only in the flagged case. This positive control establishes that the selected flag changes diagnostic filename serialization for that file.

Both Charon processes returned status 0, and their LLBC reports `has_errors: false`. The retained Cargo verbose stderr shows the `charon-driver rustc` command included `--remap-path-prefix=src=/virtual/anneal-src` in the flagged run and omitted it in the plain run. The environment record also shows `RUSTFLAGS` only in the flagged run. Thus the LLBC comparison is not explained by a failure to forward the flag to the driver.

Despite that flag, both LLBC file tables have local IDs 0=`src/lib.rs`, 1=`src/left/common.rs`, 2=`src/right/common.rs`, with byte-identical embedded contents and matching SHA-256 source hashes. `combine` points to file ID 0, `left::step` to 1, and `right::step` to 2. Their serialized spans and source texts match between runs. The rest of the full decoded LLBC trees differ at exactly five leaves: the requested `translated.options.dest_file`, plus four positional `translated.short_names` key/value leaves at entries 0 and 2. The typed short-name key/name maps agree. The ordering variance is observed, not attributed to path remapping. The two raw LLBC SHA-256 values are `c574d05f3036d0c6d652b088cbd8a9ac99f3e1315fe5d3a905b3896b3a42853f` and `323fbe9ee1881ef8e896da2eec36d99affa98ddb6638d42bdc91d848bfcaf530`; they are not byte-identical.

This fixture shows a real cross-tool divergence: rustc JSON diagnostic source filename was remapped, while pinned Charon's serialized local LLBC filenames remained package-relative. It does not establish which internal rustc or Charon source-map step selected those LLBC names, nor whether different flags, absolute source input paths, generated files, platforms or versions behave the same way.

## Evidence and boundaries

`fixture/` retains all authored bytes. `oracle.json`, `results.json`, `raw/` and `artifacts/` retain the exact acquisition and outputs. `check.py` decodes the raw LLBC files independently and asserts equality with the recorded result projections; checks diagnostic JSON, command-line flag propagation, source hashes, file IDs, spans, source texts and the five raw decoded differences; and applies in-memory wrong-file-path and swapped-item-file-ID negative controls. `python3 -B check.py` passes offline. `comparison.json` records the checked projection. The retained `results.json` hash is `e27b10622230a96ed937d66ae6d388ac4de19b9927c73a61df6a4e7b13fd83cf`.

The one-shot runner required above 30% estimated reclaimable RAM and above 10 GiB free disk before each process. It would stop below 20% reclaimable, below 10 GiB disk, above 512 MiB process-group RSS, above 100 MiB private work allocation, or beyond 15 seconds per process. Initial admission was 31.7997% and 18,642,374,656 free bytes. Minimum sampled reclaimable was 31.5468%; minimum disk was 18,642,145,280 bytes; maximum sampled group RSS was 123,008 KiB and maximum scratch 80 KiB. All four sessions finished and the private work tree was removed. Sampling can miss transient peaks.

One fixture and one execution per control cannot define a general normalization policy, stable cache key, authenticated source provenance, or Anneal editor mapping. No Aeneas-to-Lean generation, Lean server, or actual Anneal workspace was exercised. I079 and I031 remain partial at their prior gates and prerequisites.

## Revalidation

Run `python3 -B check.py` in this package for offline evidence validation. To repeat the experiment, copy `fixture/`, `prepare.py`, `probe.py`, `check.py` and `oracle.json` to a fresh private directory with no `work/`, `raw/`, `artifacts/` or `results.json`, then run `python3 -B probe.py` after fresh admission. The one-shot runner refuses to overwrite an acquisition.
