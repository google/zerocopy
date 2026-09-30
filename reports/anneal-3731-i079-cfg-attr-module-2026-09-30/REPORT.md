# Charon LLBC source identity under Cargo `cfg_attr(path)` selection

## Summary

A tiny crate declares one logical `selected` module with two `cfg_attr(path)` attributes. Two corrected, offline Charon extractions differ by the Cargo `alternate` feature alone. Both succeed. Their LLBC outputs retain the same logical item `cfg_attr_module_probe::selected::marker` with file ID 1 and identical source span, while the selected physical source entry changes from `src/default.rs` to `src/alternate.rs`, its embedded bytes and marker literal change from 17 to 29, and the unselected file is absent from each file table. This is bounded executed **I079** evidence; **I031** receives source-provenance context only. Product gates, statuses and prerequisites remain open.

## Applicability and novelty

The run used installed Charon 0.1.210 (SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`) and nightly-2026-05-31 Cargo/rustc (SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1` and `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`) on macOS arm64. These hashes pin observed executables, not their build-source commits. Nothing was installed or downloaded.

The [Rust module-file resolution](../rust-module-file-resolution-nightly-2026-05-31/REPORT.md) and [Rust conditional-compilation](../rust-conditional-compilation-nightly-2026-05-31/REPORT.md) reports explained `cfg_attr(path)` through source inspection; neither executed Charon for this case. Earlier I079 [same-inode alias](../anneal-3731-i079-symlink-module-identity-2026-09-30/REPORT.md) and [path-remap](../anneal-3731-i079-path-remap-2026-09-30/REPORT.md) runs kept the selected physical source fixed. This report measures the missing conditional-selection cell.

## Method

The source root has `#[cfg_attr(feature = "alternate", path = "alternate.rs")]` and `#[cfg_attr(not(feature = "alternate"), path = "default.rs")]` on one `mod selected;`. Both files define `pub fn marker() -> u32` with the same layout and span; only their return literals differ, 17 or 29. `read()` calls the selected marker. `prepare.py` pinned fixture hashes, expected source files, logical name and hypotheses in `oracle.json` before acquisition.

The corrected default command used Cargo `--no-default-features`. The corrected alternate command used `--no-default-features --features alternate`. All other crate inputs and Charon options matched, apart from separate Cargo target directories and requested LLBC destinations. Cargo verbose stderr retained the driver commands: the default had neither `feature="alternate"` nor `feature="default"`; the alternate had `feature="alternate"` and no `feature="default"`. Both used `--offline --locked`, one Cargo job and no incremental compilation.

An initial *preliminary* acquisition used `--features alternate` without `--no-default-features`, so Cargo also enabled the empty `default` feature. Its oracle, results, raw stdout/stderr and LLBC files remain in `preliminary/` for provenance. It is **excluded** from the reported comparison. The corrected pair ran in a fresh private directory after new resource admission, and the top-level `results.json`, `raw/` and `artifacts/` are the sole basis for findings.

## Findings

Both corrected Charon processes exited 0 with `has_errors: false`. Default LLBC local file ID 0 is `src/lib.rs` and ID 1 is `src/default.rs`, with source SHA-256 `8acab6fdf4017bc1b4fcf457d3a0f6b48e566be9d4a914135d26b13c38fd7cb2`. Alternate LLBC local ID 0 is the identical `src/lib.rs` and ID 1 is `src/alternate.rs`, with source SHA-256 `26838ffc849d01dd50d2d3039a024f8dce4b65b8eac18bbdaa38ec4550ad820a`. The unselected file does not appear in either serialized file table. The root source hash is identical in both (`a9ad07c4a1ae7eb74e77836a89605f5b546f07f6f7117a4e387f55202dee68c1`).

The logical `cfg_attr_module_probe::selected::marker` item points to file ID 1 in both outputs and has span line 1, columns 0–29 in both. Its serialized `source_text` and MIR literal are 17 in default, 29 in alternate. The root `read` item remains at file ID 0 with unchanged span/source text. A full decoded-tree comparison finds exactly five differing leaves: selected file name, selected file contents, marker MIR literal, marker source text and requested destination path. No `short_names` ordering variance appears in this pair. The raw LLBC SHA-256 values are `6afd8dc318bc9282887dc2b890c5b06a0ea0a9bb0b2284fd4dfa2236beba7498` and `f63c540636eef0caaf351a63db9569507b3d3e20d3015dd64c7e3d44a19e569c`; raw outputs are not byte-identical.

For this crate and feature pair, the serialized logical name and numeric file ID alone cannot identify which physical module source was selected. Any one of the selected path, embedded source content, or active feature state distinguishes these two observed outputs. The pair does not establish which fields an Anneal cache key needs or a stable cross-build numeric ID contract.

## Evidence and boundaries

`fixture/` preserves authored bytes; `oracle.json` and `prepare.py` preserve predeclared hypotheses; `probe.py`, `results.json`, `raw/` and `artifacts/` retain the corrected one-shot commands, environment, PIDs, times, resources, output bytes and LLBC. `preliminary/` is explicitly excluded as described above. `check.py` reconstructs decoded projections from raw LLBC, checks all fixture hashes and source selections, exact logical item name/span, the five-leaf diff, actual driver cfg flags and both run guards; it rejects wrong selected-file and wrong item-file-ID mutations in memory. `python3 -B check.py` passes offline. The corrected acquisition `results.json` SHA-256 is `979dc2b0f410e8829f676299887a9cfab56341c361836359d666bf8c38f81405`.

Corrected initial admission estimated 31.7987% reclaimable RAM and 18,710,818,816 free disk bytes. Minimum sampled reclaimable was 31.3913%, minimum disk 18,710,593,536 bytes; maximum process-group RSS was 123,120 KiB and maximum scratch was 76 KiB. The runner would stop below 20% reclaimable, below 10 GiB disk, above 512 MiB group RSS, above 100 MiB scratch, or beyond 15 seconds per process. Both processes ended, post-run group RSS was zero and the private work tree was removed. Sampled maxima can miss brief peaks.

One crate, two feature states, one execution per state and one compiler/Charon pair cannot establish general `cfg_attr` behavior, arbitrary source-map ownership, reordering stability, Aeneas/Lean translation, diagnostic routing or Anneal policy. I079 and I031 remain partial at their existing product gates.

## Revalidation

Run `python3 -B check.py` in this package. For a fresh extraction, copy `fixture/`, `prepare.py`, `probe.py`, `check.py` and `oracle.json` to a new private package without any acquired outputs, then run `python3 -B probe.py` after fresh admission. The runner refuses to overwrite existing results.
