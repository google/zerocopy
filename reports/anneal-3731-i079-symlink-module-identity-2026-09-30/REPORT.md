# Charon file identity for two Rust module paths sharing one inode

## Summary

On macOS APFS, one tiny Rust crate loaded `left/common.rs` and `right/common.rs` through two relative symlinks to the same `shared.rs` file. A matched control used two physical copies with identical bytes at those same logical module paths. Pinned Charon/Cargo completed both offline extractions. In each LLBC, `src/left/common.rs` and `src/right/common.rs` were separate local file-table entries with IDs 1 and 2, even though the aliases shared one device/inode. `left::step` and `right::step` retained distinct logical item names and pointed to the corresponding separate file IDs. The physical-copy control had the same file table, item names/IDs/spans and embedded source bytes.

This adds a narrow executed **I079** file-identity specimen absent from the earlier source-only Rust module-resolution report. It is **I031 context** for source provenance, not an authenticated Rust-to-Lean diagnostic map. I079 and I031 remain partial at their existing product gates. One run on one filesystem does not establish a cross-platform or general cache-key rule.

## Applicability

The run used the locally installed Charon 0.1.210 executable (SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`) and nightly-2026-05-31 Cargo/rustc executables (SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1` / `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`) on macOS 26.6.2 arm64. These are hashes of observed binaries; this package does not establish their build-source commits. Commands used `--offline --locked`, private Cargo target directories and separate LLBC destinations, with `CARGO_BUILD_JOBS=1`, `CARGO_INCREMENTAL=0` and `RAYON_NUM_THREADS=1`. No package was installed or downloaded.

The predeclared source root has `#[path = "left/common.rs"]` and `#[path = "right/common.rs"]` modules plus a `combine` function. Its shared module bytes contain one `step` function with a Unicode string, which is incidental to this file-identity question. The `alias` layout creates both `common.rs` entries as relative `../shared.rs` symlinks; the `copy` layout writes two independent physical files with the same bytes. Both layouts preserve the same `Cargo.toml`, `Cargo.lock`, root source, module names, source hashes and arguments except for private root/target/destination paths. `oracle.json` fixes these inputs and the competing path-identity hypotheses before execution.

The [Rust module/file source review](../rust-module-file-resolution-nightly-2026-05-31/REPORT.md) inferred that its pinned rustc implementation does not intentionally canonicalize lexical aliases before source-map identity, but explicitly had no symlink execution. Earlier [I079 local span](../anneal-3731-i079-local-span-source-text-2026-09-29/REPORT.md), [generated file](../anneal-3731-i079-generated-file-charon-spans-2026-09-30/REPORT.md) and [generated CRLF](../anneal-3731-i079-generated-edge-spans-2026-09-30/REPORT.md) probes did not compare two lexical module paths to one inode within a crate. This report tests that remaining concrete case.

## Findings

### Identical physical source bytes did not collapse the two local LLBC file entries

The fixture source hashes were `491a614d6596dcbc48c999f468f706908df0e635e848feb11faae77a06a77a2e` for root `lib.rs` and `8865d4672ee3a15e03a3de9c80d62296553f38bb8178fe93ab3c3c6189368d14` for `shared.rs`. The retained `lstat`/`stat` manifest proves both alias paths were symlinks whose dereferenced device/inode pair was equal; their `resolve()` targets were also equal. The physical-copy control paths were regular files with distinct inodes but the same SHA-256 content.

Each Charon run exited 0 with `has_errors: false`. The alias LLBC recorded local files 0=`src/lib.rs`, 1=`src/left/common.rs`, and 2=`src/right/common.rs`; file IDs 1 and 2 each embedded the exact `shared.rs` text and hash. The physical-copy LLBC recorded the same three entries with the same local paths, IDs and embedded contents. In both outputs, `symlink_module_probe::left::step` used file ID 1 and `symlink_module_probe::right::step` file ID 2; `combine` used root file ID 0. The two `step` item source texts and their recorded spans matched across layouts. **Basis: executed Charon LLBC plus independently retained filesystem/source manifest.**

The two raw LLBC hashes differ (`1b856001a5eeda4b86a4f74fcc0ede06d6e917581435910fa9156055916bc724` alias; `603a8931af4c51a6c9a9a8ffdaca9db56d66572a74536b4926288e48780449a9` copy). A full decoded-tree comparison found exactly seven differing leaves: the requested `dest_file`, plus six positional `short_names` key/value leaves across three entries. The typed-key-to-name maps agree. The file table, item names and local item spans/source text agree. This is a one-pair decoded comparison; the short-name ordering difference is **not attributed** to symlink versus copy, and the matching selected fields do not prove semantic equivalence or byte reproducibility. The checker detects an in-memory duplicate file path and a wrong `right::step` file ID as negative controls.

### The observed file IDs are lexical path distinctions, not a stable content identity

Because both symlink aliases dereferenced the same inode and contained the same bytes, the separate LLBC IDs cannot be explained by physical inode or content distinctions in this fixture. The observed distinction tracks the two lexical module paths under this macOS/Rust/Charon combination. The control shows the same two-path structure when inodes are distinct. This supports preserving a source file locator alongside item identity and source bytes; it does not define an Anneal canonicalization rule or a cross-process stable LLBC file-ID contract. **Basis: observed alias/control contrast and bounded inference.**

## Boundaries

- One crate, two relative symlink aliases, one macOS APFS host, one Charon/Rust pair and one extraction per layout. Other filesystems, symlink spellings, `--remap-path-prefix`, `cfg_attr(path)`, nested module loading and compiler revisions were not tested.
- The Unicode text only makes the exact copied bytes easy to distinguish; this run does not add a Unicode span-unit finding to the earlier I079 probes.
- Charon file IDs are numeric positions within these serialized LLBCs. Their equality between the two matched layouts is observed, not a promise that IDs remain stable after reorder, edits or later versions.
- The separate module names matter. The run does not isolate whether rustc or Charon first assigns the distinct file IDs internally, only what the serialized LLBC exposes.
- No Aeneas translation, Lean diagnostic, Anneal annotation attachment, source-map implementation, or cache-key policy was exercised. I031 receives provenance context only.
- Sampled maxima can miss short peaks. The largest sampled Charon process-group RSS was 125,440 KiB; minimum sampled reclaimable estimate was 31.8718%, minimum disk free 17.565 GiB and maximum temporary work allocation 96 KiB. These stayed inside the live resource guards.

## Evidence

`fixture/` retains the regular source files and package manifest. `prepare.py` and `oracle.json` freeze source hashes, logical names and hypotheses; `probe.py` constructs the symlink/copy layouts, records `lstat`/`stat` dev/inode and resolved paths, runs two guarded Charon commands, and retains `results.json`, raw stdout/stderr and both `.llbc` files. The source fixture SHA, command arguments, selected environment, process IDs, timestamps, exit statuses and resource samples are preserved. The acquisition `results.json` SHA-256 is `2acbcbea3a2b8b52315d86fd990ac1a59dd2216c1a3d3e9170547e9b1a10a61a`.

`check.py` reads the raw artifacts, source bytes and prelaunch oracle; it verifies device/inode contrast, exact paths/file IDs/item ownership, resource and cleanup limits, all seven decoded differences and two mutation controls. `comparison.json` records its expected summary. `python3 -B check.py` passes offline. Initial admission measured 32.2016% estimated reclaimable memory and 17.566 GiB disk free; both commands remained above 30% reclaimable and 10 GiB disk. Abort conditions were below 20% reclaimable, below 10 GiB disk, above 512 MiB process-group RSS, above 100 MiB private work allocation, or over 15 seconds per command. The temporary work trees were removed after retaining the evidence.

## Revalidation

Run `python3 -B check.py` from this package. To repeat extraction, copy `fixture/`, `prepare.py`, `probe.py`, `check.py` and `oracle.json` into a fresh private package directory without `work/`, `raw/`, `artifacts/` or `results.json`, then run `python3 -B probe.py` after fresh admission. The runner refuses to overwrite an acquired run. Compare file-table paths, item file IDs, source hashes and typed short-name maps; do not equate raw LLBC hashes or positional short-name order with source identity. Cross-platform or Anneal policy claims require additional subjects.
