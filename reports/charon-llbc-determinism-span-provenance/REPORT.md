# Charon LLBC Translation Determinism, `short_names` Permutation Impact, Source-File Identity, and Unicode/Generated Span Provenance

## Summary

Twelve component experiments and cross-revision source inspections across Charon (`0.1.210` / `0c91ca1a8e00`, Aeneas-pinned `a535e914f74d`, and upstream `e435e5f34186`), Aeneas (`nightly-2026.06.03`), Lean 4 / Lake (`v4.30.0-rc2`), and Rust/Cargo (`nightly`) establish the exact determinism boundaries, downstream Lean/Lake stability, file-table identity rules, and line/column coordinate conventions of serialized Charon LLBC:

1. **Cause and downstream neutrality of raw LLBC hash churn (`support/charon-warm-noop-byte-diff/`, `support/charon-shortname-aeneas-impact/`, `support/multifunction-translation-repeat/`, `support/five-function-lake-replay/`):**
   - Five consecutive warm, source-unchanged `charon cargo` runs on the same path emitted 10,936-byte LLBC files that were byte-identical everywhere except zero-based byte offsets `2645–2869` (`$.translated.short_names`), where four `Fun` ID entries permuted across runs (`0,1,2,3`, `3,2,1,0`, `0,2,1,3`, `0,3,2,1`, `2,0,1,3`; sorting `short_names` by key yields a single canonical SHA-256 `ec4dc523318d…`). In Charon's `compute_short_names.rs`, names are collected in a randomized `std::collections::HashMap<String, FoundName>` before iteration into an insertion-ordered `SeqHashMap` (`IndexMap`) serialized as a JSON array by `SeqHashMapToArray`.
   - Because Aeneas clears `short_names` on LLBC load, translating all five `short_names`-permuted LLBC variants (and five sequential/concurrent repeats of a 5-function, 2-field-struct corpus) produced **byte-identical** Lean files (`Types.lean`, `Funs.lean`, `Probe.lean`, and `FunsExternal_Template.lean`). Replacing those byte-identical generated `.lean` files in-place in a warm Lake project caused `lake build -v` to mark all local modules `Replayed` with unchanged `.trace` and `.olean` hashes, whereas mutating `add_one` from `x + 1` to `x + 2` rebuilt `Probe.Funs`, `Probe`, and `Consumer` while replaying `Probe.Types`.
2. **Source relocation and inert-comment provenance (`support/charon-relocation-comment-provenance/`):** Moving identical Rust source bytes (`f665adfd…`) between two directory roots changed only `translated.files[0].name.Local` in normalized LLBC and only the `Source: '<path>', lines 1:0-1:48` doc-comment line in Aeneas's emitted `Probe.lean` (`1faf6714…` vs `adbae3eb…`). Appending a trailing `//` comment after the function (`174c26fe…`) changed `translated.files[0].contents` in LLBC but emitted byte-identical `Probe.lean` (`1faf6714…`).
3. **File-table identity under symlinks, `--remap-path-prefix`, and `cfg_attr(path)` (`support/symlink-module-identity/`, `support/path-remap/`, `support/cfg-attr-module/`):**
   - Across `charon/src/bin/charon-driver/translate/translate_ctx.rs` and `charon/src/ast/meta.rs` in `0c91ca1a8e00`, `a535e914f74d`, and `e435e5f34186`, file registration (`register_file`, `VirtualFile` vs `LocalFile`) and ordered `Vector<FileId, File>` serialization assign deterministic single-threaded `FileId` indices keyed by lexical path rather than physical inode or diagnostic remap prefix.
   - Loading two modules (`src/left/common.rs` and `src/right/common.rs`) via relative symlinks to the same `shared.rs` inode on APFS still created two separate LLBC file-table entries (`FileId 1` and `FileId 2`), matching a physical-copy control.
   - Passing `RUSTFLAGS=--remap-path-prefix=src=/virtual/anneal-src` rewrote `rustc`'s JSON diagnostic `file_name` from `src/error.rs` to `/virtual/anneal-src/error.rs` and was forwarded to `charon-driver rustc`, yet Charon's LLBC file table still serialized un-remapped package-relative paths (`src/lib.rs`, `src/left/common.rs`, `src/right/common.rs`).
   - Switching `#[cfg_attr(feature = "alternate", path = "alternate.rs")]` versus `default.rs` on `mod selected;` kept `cfg_attr_module_probe::selected::marker` at `FileId 1` and span line 1 columns `0–29` in both LLBCs while swapping `FileId 1`'s physical filename (`src/default.rs` vs `src/alternate.rs`), embedded contents, and literal (`17` vs `29`) and omitting the unselected file from the file table.
4. **ASCII, Unicode display-cell, generated-file, and CRLF/tab span conventions (`support/local-span-source-text/`, `support/unicode-charon-spans/`, `support/generated-file-charon-spans/`, `support/generated-edge-spans/`):**
   - Charon serializes spans with **1-based line numbers, 0-based start columns, and exclusive end columns**. Across 64 ASCII local item spans in 16 edit/revert LLBCs, `item_meta.source_text` matched the exact end-exclusive slice of `app/src/lib.rs`.
   - On non-ASCII source (both in `src/lib.rs` file ID 0 and in `build.rs`-generated `OUT_DIR/generated.rs` file ID 1), Charon's column numbers do **not** count UTF-8 bytes, Unicode scalar values, or UTF-16 code units: across 7 local records in each fixture, all 7 matched a **display-cell + fixed 4-space tab calculation** where emoji `😀` has width `2`, combining acute accent (`U+0301` in `é`) has width `0`, and each `\t` character adds a fixed `4` columns regardless of current column alignment.
   - When `OUT_DIR/generated.rs` contained 201 bytes with six `CRLF` (`\r\n`) line endings (`1a8f1e3b…`), Charon embedded **195 LF-normalized bytes** (`59d0ebba…`) in `translated.files[1].contents` and in multiline `item_meta.source_text`.

## Applicability

The findings in this report cover the following subjects from `REPORT.json`:

- **Charon `0.1.210` executable and source** (`AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, macOS `aarch64-apple-darwin` binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`), **Charon Aeneas-pinned source revision** (`AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`), and **Charon updated upstream source revision** (`AeneasVerif/charon@e435e5f341863a49a7e85d2fee9988bc0c687c82`);
- **Aeneas `nightly-2026.06.03`** (`AeneasVerif/aeneas@ac9f1bc5262a5e4ff1e24ca78617121382202727`, binary SHA-256 `f476001e1a8e8c5cb1d8a621a25716d8e15f0809c8a023c5349357acc0911d03`);
- **Lean 4 and Lake `v4.30.0-rc2`** (`leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, `lean` SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, `lake` SHA-256 `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`);
- **Rust compiler `nightly`** (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, binary SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`) and **Cargo `nightly`** (`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, binary SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1`).

**Shared behavior versus cross-revision deltas:** All executable probes ran against the pinned Charon `0.1.210` (`0c91ca1a8e00`), Aeneas `ac9f1bc5262a`, Lean/Lake `3dc1a088b6d2`, and Rust/Cargo `nightly` binaries on macOS `arm64`. Direct source comparison across the three Charon revisions (`0c91ca1a8e00`, `a535e914f74d`, and `e435e5f34186`) in `charon/src/bin/charon-driver/translate/translate_ctx.rs` and `charon/src/ast/meta.rs` confirms that span registration (`register_file`, `VirtualFile` versus `LocalFile`) and ordered `Vector<FileId, File>` file-table serialization retain identical single-threaded deterministic `FileId` assignment across all three revisions.

## Findings

### Warm No-Op `short_names` Permutations and Downstream Aeneas/Lean/Lake Invariance

In `support/charon-warm-noop-byte-diff/`, five consecutive `charon cargo --preset aeneas --dest-file <same probe.llbc> -- --manifest-path <same Cargo.toml> --lib --offline --locked -j 1` runs on a tiny root crate with two path dependencies (`dep_a`, `dep_b`) and a build script completed in `0.752 s` (cold run 1) and `0.076–0.078 s` (warm runs 2–5). All five LLBC files were exactly `10,936` bytes, identical across bytes `0..2644` and `2870..10935`, and differed only inside the 225-byte `translated.short_names` JSON array at zero-based offsets `2645–2869`:

| Run | `Fun` ID order in `translated.short_names` | Raw LLBC SHA-256 prefix | Canonical `short_names`-sorted LLBC SHA-256 | Generated `Types.lean` / `FunsExternal_Template.lean` / `Funs.lean` / `Probe.lean` byte sizes & distinct SHA-256 count across all 5 runs (`support/charon-shortname-aeneas-impact/`) |
| ---: | --- | --- | --- | --- |
| 1 | `0, 1, 2, 3` | `ec4dc523318d` | `ec4dc523318d6e1ed34b0d82f3650fe68c69998d17bbd65a3552c19d0cbed1ba` | `506 B` (1 hash) / `1,125 B` (1 hash) / `893 B` (1 hash) / `18 B` (1 hash) |
| 2 | `3, 2, 1, 0` | `e211fbe97e71` | same | identical |
| 3 | `0, 2, 1, 3` | `bb30246bfd6f` | same | identical |
| 4 | `0, 3, 2, 1` | `5fcf6f267387` | same | identical |
| 5 | `2, 0, 1, 3` | `d9559b90f96e` | same | identical |

- **Emitter mechanism (`support/charon-warm-noop-byte-diff/source-inspection.json`):** In `AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, `compute_short_names.rs` inserts candidate names into `std::collections::HashMap<String, FoundName>` (seeded with per-process random SipHash keys), iterates that map, and inserts into `ctx.translated.short_names` (`SeqHashMap` / `IndexMap`), which `SeqHashMapToArray` serializes in insertion order.
- **Downstream Aeneas, direct Lean, and Lake replay (`support/charon-shortname-aeneas-impact/`):** Passing all five LLBCs to `aeneas -backend lean -no-progress-bar -sequential -split-files -gen-lib-entry` (236–259 ms each) produced byte-identical Lean files across all five runs. Five fresh direct Lean batch consumers (8.3–12.0 s each) produced identical `.olean` hashes and verified `r37u0.combined (x : Aeneas.Std.U32) : Aeneas.Std.Result Aeneas.Std.U32` with axiom list `[dep_a.dep_a, dep_b.dep_b]` and no `sorryAx`. Across five fresh private Lake projects (1,686 total jobs, 4 newly built `Probe` modules, 9.1–21.5 s), `Probe.Types.olean`, `Probe.Funs.olean`, and `Probe.olean` hashes matched across all five directories, while `Probe.FunsExternal.olean` differed only because it embedded each project's `run-N` path. Inside `run-1`'s Lake project, one no-write rebuild and four in-place overwrites with `run-2..run-5`'s generated `.lean` files (1.8–2.3 s each) reported all four `Probe` modules as `Replayed` with unchanged `.trace` and `.olean` hashes and mtimes.

Basis: **source + execution** in `support/charon-warm-noop-byte-diff/results.json`, `support/charon-warm-noop-byte-diff/source-inspection.json`, and `support/charon-shortname-aeneas-impact/results.json`.

### Multi-Function Sequential/Concurrent Determinism and Lake Invalidation (`support/multifunction-translation-repeat/`, `support/five-function-lake-replay/`)

In `support/multifunction-translation-repeat/`, a dependency-free library with five public functions (`add_one`, `choose`, `pair_sum`, `make_pair`, `combine`) and a two-field struct was extracted five times via `charon cargo --preset aeneas` (3 sequential calls on one target/destination—1 cold, 2 warm—plus 2 concurrent calls overlapping by ~165 ms on private targets/destinations; 63–498 ms per Charon call). All five raw LLBC SHA-256 digests differed, but after normalizing `translated.options.dest_file` and sorting the six entries of `translated.short_names`, all five parsed JSON trees were identical. Translating each via Aeneas (226–265 ms) produced byte-identical Lean files across all five runs:

- `Types.lean`: SHA-256 `698540ae6f0215de8fe7c221807d967a2c34710f09bdc40028d84f48c8d84aa6`
- `Funs.lean`: SHA-256 `a23e4de51aad5573134decee8733450afdb3924c306f51f51f41b537982c9ecd` (containing all 5 definitions with no `sorry`, `axiom`, or `decreasing_by`)
- `Probe.lean`: SHA-256 `88d15c5183e48c512f4ecfb38c430356859b255fe1dcf6a613fd51c7ba36820d`

In `support/five-function-lake-replay/`, a Lake consumer importing `Probe` and proving five equality-to-self theorems (`combine_self` axioms `[propext, Classical.choice, Quot.sound]`, peak process-tree RSS `2.138 GiB`, minimum preflight free memory `35%`, free disk `42.64 GiB`) executed an eight-step sequence across the 1,686-job Lake graph:

| Step | Elapsed (s) | Local `Probe.Types` / `Probe.Funs` / `Probe` / `Consumer` status | Local `.olean` and `.trace` SHA-256 behavior |
| --- | ---: | --- | --- |
| 1. Fresh baseline | 48.552 | `Built / Built / Built / Built` | Baseline `Types.olean` `95ed236a…`, `Funs.olean` `b92df6b2…`, `Types.trace` `aaaa4c28…`, `Funs.trace` `4a2c7cb9…`, `Probe.trace` `d5a78c46…`, `Consumer.trace` `99e1cc20…` |
| 2. Warm no-write | 4.911 | `Replayed / Replayed / Replayed / Replayed` | All `.olean` and `.trace` hashes and mtimes identical to baseline |
| 3–6. Replace in-place with `gen-2..gen-5` | 3.320, 3.093, 3.317, 3.128 | `Replayed / Replayed / Replayed / Replayed` | All `.olean` and `.trace` hashes and mtimes identical to baseline |
| 7. Mutate `add_one` (`x + 1` → `x + 2`, `Funs.lean` `f5f50d29…`) | 24.453 | `Replayed / Built / Built / Built` | `Types.olean` and `Types.trace` unchanged; `Funs.olean` → `8778abd8…`, `Funs.trace` → `3b0727dc…`, `Probe.trace` → `f2e43422…`, `Consumer.trace` → `6a183641…`, while `Probe.olean` and `Consumer.olean` bytes stayed identical despite `Built` status |
| 8. Changed no-write | 4.170 | `Replayed / Replayed / Replayed / Replayed` | All `.olean` and `.trace` hashes identical to step 7 |

Basis: **execution** in `support/multifunction-translation-repeat/results.json` and `support/five-function-lake-replay/results.json`.

### Source Relocation, Inert Comments, Symlinks, `--remap-path-prefix`, and `cfg_attr(path)`

Four focused probes isolated how filesystem paths, compiler remap flags, and conditional module attributes are recorded in Charon's `translated.files` table (whose single-threaded `register_file` / `Vector<FileId, File>` implementation is shared across Charon `0c91ca1a8e00`, `a535e914f74d`, and `e435e5f34186`):

1. **Relocation and trailing inert comments (`support/charon-relocation-comment-provenance/`):**
   - Extracting byte-identical `src/lib.rs` (`f665adfda34d93ee8dd8db1ee7d798dc449d7e498bffd31634eec59d8f243b94`) at `origin-root/src/lib.rs` versus `other-root/src/lib.rs` produced LLBCs that (after normalizing `dest_file` and sorting `item_names`, `short_names`, and `assoc_item_names`) differed solely at `translated.files[0].name.Local`. Aeneas's emitted `Probe.lean` files (`1faf6714…` vs `adbae3eb…`) differed solely on the `Source: '<path>', lines 1:0-1:48` comment line.
   - Appending `// Inert fixture note after the function.` at `origin-root/src/lib.rs` (`174c26fe…`) changed only `translated.files[0].contents` in normalized LLBC and produced `Probe.lean` byte-identical to `origin` (`1faf6714…`).
2. **Symlink module aliases sharing one inode (`support/symlink-module-identity/`):**
   - In a crate with `#[path = "left/common.rs"] mod left;` and `#[path = "right/common.rs"] mod right;` (`src/lib.rs` `491a614d6596dcbc48c999f468f706908df0e635e848feb11faae77a06a77a2e`), making both `common.rs` paths relative symlinks to the parent directory's `shared.rs` (SHA-256 `8865d4672ee3a15e03a3de9c80d62296553f38bb8178fe93ab3c3c6189368d14`, equal APFS `(st_dev, st_ino)`) still serialized two distinct local file entries (`0 = src/lib.rs`, `1 = src/left/common.rs`, `2 = src/right/common.rs`), matching the physical-copy control (`alias` LLBC `1b856001…` vs `copy` LLBC `603a8931…`, differing at 7 leaves: `dest_file` + 6 positional `short_names` leaves; `results.json` SHA-256 `2acbcbea3a2b8b52315d86fd990ac1a59dd2216c1a3d3e9170547e9b1a10a61a`).
3. **Diagnostic versus LLBC path remapping (`support/path-remap/`):**
   - Passing `--remap-path-prefix=src=/virtual/anneal-src` to `rustc` rewrote JSON diagnostic `file_name` on `src/error.rs` (line 1, col 41) from `src/error.rs` to `/virtual/anneal-src/error.rs`. Passing `RUSTFLAGS=--remap-path-prefix=src=/virtual/anneal-src` to `charon cargo` forwarded the flag to `charon-driver rustc`, yet both plain (`c574d05f…`) and flagged (`323fbe9e…`) LLBCs recorded un-remapped `0 = src/lib.rs`, `1 = src/left/common.rs`, `2 = src/right/common.rs` (`results.json` SHA-256 `e27b10622230a96ed937d66ae6d388ac4de19b9927c73a61df6a4e7b13fd83cf`, differing only at `dest_file` and 4 positional `short_names` leaves).
4. **Conditional module file selection via `cfg_attr(path)` (`support/cfg-attr-module/`):**
   - On a root `src/lib.rs` (`a9ad07c4a1ae7eb74e77836a89605f5b546f07f6f7117a4e387f55202dee68c1`) declaring `#[cfg_attr(feature = "alternate", path = "alternate.rs")]` and `#[cfg_attr(not(feature = "alternate"), path = "default.rs")]` on `mod selected;`, extracting with `--no-default-features` (`6afd8dc3…`) versus `--no-default-features --features alternate` (`f63c5406…`) kept `cfg_attr_module_probe::selected::marker` at `FileId 1` and span line 1 columns `0–29`, while replacing `FileId 1` between `src/default.rs` (`8acab6fd…`, literal `17`) and `src/alternate.rs` (`26838ffc…`, literal `29`) and omitting the unselected file from each LLBC (`results.json` SHA-256 `979dc2b0f410e8829f676299887a9cfab56341c361836359d666bf8c38f81405`, 5 differing leaves total).

Basis: **source + execution** in `support/charon-relocation-comment-provenance/results.json`, `support/symlink-module-identity/results.json`, `support/path-remap/results.json`, and `support/cfg-attr-module/results.json`.

### ASCII, Unicode Display-Cell, Generated-File, and CRLF/Tab Span Coordinates

Four span-verification probes compared Charon's serialized `(line, col)` spans and `item_meta.source_text` against independently retained source bytes:

1. **ASCII file-ID-0 spans (`support/local-span-source-text/`):** Across 16 retained edit/revert LLBCs (`baseline` `app/src/lib.rs` `bbe231375dfe3d5ae46a420067496a466ee223e8e2acb2aa54d0c931691d041e` and edited `d264e3214d6b82cc98a3dc13d3fb4d839d1ed54ccdf705225c17210195e61bae`), all **64** local single-line spans (`step`, `use_step`, `payload_len`, `generated_value`) matched `item_meta.source_text` under 1-based lines, 0-based start columns, and exclusive end columns (32 generated file-ID-1 records in that older corpus had no separately saved `generated.rs` and were excluded).
2. **Unicode file-ID-0 (`support/unicode-charon-spans/`) and `build.rs` generated file-ID-1 (`support/generated-file-charon-spans/`) spans:** Using `support/unicode-charon-spans/fixture/src/lib.rs` (`b26ba311378fd7aeffcb4e82f2d38768e3577fa0df6b629cbdb602043655822c`) and an independently saved 212-byte `OUT_DIR/generated.rs` (`support/generated-file-charon-spans/generated.rs`, SHA-256 `d0ee5a2c97d8a1797c31955136c6f5dbf62cde9cdc4f88f7a5cf5f551ba2d0c8`), five unique items (serialized as 7 local records because `EMOJI` and `COMBINING` appear in both function and global arrays) placed emoji `😀` before `after_emoji` on line 1, decomposed `e` + combining acute (`U+0301`) before `after_combining` on line 2, and both inside line 3:

| Unique local item | Observed LLBC start→end col (`support/unicode-charon-spans/` / `support/generated-file-charon-spans/`) | UTF-8 bytes | Unicode scalars | UTF-16 units | Fixture display cells (`😀`=2, `U+0301`=0) |
| --- | ---: | ---: | ---: | ---: | ---: |
| `EMOJI`, line 1 | `0→29` / `0→29` | `0→31` | `0→28` | `0→29` | **`0→29`** |
| `after_emoji`, line 1 | `30→73` / `30→73` | `32→75` | `29→72` | `30→73` | **`30→73`** |
| `COMBINING`, line 2 | `0→32` / `0→32` | `0→34` | `0→33` | `0→33` | **`0→32`** |
| `after_combining`, line 2 | `33→80` / `33→80` | `35→82` | `34→81` | `34→81` | **`33→80`** |
| `unicode_body` / `generated_body`, line 3 | `0→46` / `0→48` | `0→50` / `0→52` | `0→46` / `0→48` | `0→47` / `0→49` | **`0→46` / `0→48`** |

In both fixtures, mismatch counts across all 7 local records were **7 for UTF-8 bytes, 6 for Unicode scalars, 4 for UTF-16 units, and 0 for display cells**.

3. **CRLF line endings, leading tabs, and multiline generated items (`support/generated-edge-spans/`):** An independently saved 201-byte `OUT_DIR/generated.rs` (`support/generated-edge-spans/generated.rs`, SHA-256 `1a8f1e3ba34f78259326d24feeebf69c6b03356019ba08773e4f5992c833c620`) containing six `CRLF` line endings, tabs, emoji `😀`, combining acute `U+0301`, and multiline `tabbed_multiline` was embedded into LLBC file ID 1 as **195 LF-normalized bytes** (`59d0ebba3ee4303cb2284105e1915e7cdfd5bf95995e4f20ebc901b1de319e99`). Across all 6 local file-ID-1 records (`PREFIX` line 1 `0→31`, `after_prefix` line 1 `35→71` after a `\t` at col 31, `tabbed_multiline` line 2 col 4 → line 5 col 5, and `AFTER` line 6 `0→28`), mismatch counts were: UTF-8 byte `6`, Unicode scalar `4`, UTF-16 unit `6`, 1-cell tab `2`, fixed 8-cell tab `2`, 4-cell tab-stop `1` (which predicts col `32` instead of `35` after a tab at col 31), 8-cell tab-stop `2`, and **fixed 4-cell tab + display width `0`**.

Basis: **execution** in `support/local-span-source-text/comparison.json`, `support/unicode-charon-spans/comparison.json`, `support/generated-file-charon-spans/comparison.json`, and `support/generated-edge-spans/comparison.json`.

## Boundaries

- **Not examined:** Complex Unicode grapheme clusters (ZWJ sequences, regional indicators, bidirectional text), procedural-macro token-span hygiene chains across crates, or Windows native path separators.
- **Unknown:** Whether non-Aeneas consumers of Charon LLBC depend on the array ordering of `translated.short_names`.
- **Known not to apply:**
  - Raw LLBC SHA-256 equality does not hold across warm no-op repeats because `compute_short_names.rs` iterates a randomized `HashMap`.
  - Charon span columns are **neither** UTF-8 byte offsets, Unicode scalar indices, UTF-16 code units (LSP default), nor tab-stop-aligned display columns; converting Charon spans to UTF-8 byte ranges or LSP UTF-16 positions requires the original source line text (accounting for `CRLF → LF` normalization in embedded file contents).
  - `--remap-path-prefix` rewrites `rustc` JSON diagnostic paths but does **not** rewrite Charon's local LLBC file table at this pin.

## Evidence

- **Determinism, `short_names`, and Lake replay subprobes:**
  - `support/charon-warm-noop-byte-diff/probe.py`, `support/charon-warm-noop-byte-diff/verify.py`, `support/charon-warm-noop-byte-diff/results.json`, `support/charon-warm-noop-byte-diff/source-inspection.json`, `support/charon-warm-noop-byte-diff/fixture/`, `support/charon-warm-noop-byte-diff/diffs/`, and `support/charon-warm-noop-byte-diff/artifacts/`.
  - `support/charon-shortname-aeneas-impact/probe.py`, `support/charon-shortname-aeneas-impact/check.py`, `support/charon-shortname-aeneas-impact/results.json`, `support/charon-shortname-aeneas-impact/logs/`, and `support/charon-shortname-aeneas-impact/work/`.
  - `support/multifunction-translation-repeat/probe.py`, `support/multifunction-translation-repeat/check.py`, `support/multifunction-translation-repeat/results.json`, `support/multifunction-translation-repeat/fixture/`, `support/multifunction-translation-repeat/logs/`, and `support/multifunction-translation-repeat/artifacts/`.
  - `support/five-function-lake-replay/probe.py`, `support/five-function-lake-replay/check.py`, `support/five-function-lake-replay/results.json`, `support/five-function-lake-replay/summary.json`, `support/five-function-lake-replay/theorem-output.txt`, `support/five-function-lake-replay/logs/`, and `support/five-function-lake-replay/work/`.
- **Relocation, symlink, remap, and `cfg_attr(path)` subprobes:**
  - `support/charon-relocation-comment-provenance/probe.py`, `support/charon-relocation-comment-provenance/check.py`, `support/charon-relocation-comment-provenance/results.json`, `support/charon-relocation-comment-provenance/work/`, and `support/charon-relocation-comment-provenance/artifacts/`.
  - `support/symlink-module-identity/prepare.py`, `support/symlink-module-identity/probe.py`, `support/symlink-module-identity/check.py`, `support/symlink-module-identity/oracle.json`, `support/symlink-module-identity/results.json` (`2acbcbea…`), `support/symlink-module-identity/comparison.json`, `support/symlink-module-identity/fixture/`, `support/symlink-module-identity/raw/`, and `support/symlink-module-identity/artifacts/`.
  - `support/path-remap/prepare.py`, `support/path-remap/probe.py`, `support/path-remap/check.py`, `support/path-remap/oracle.json`, `support/path-remap/results.json` (`e27b1062…`), `support/path-remap/comparison.json`, `support/path-remap/fixture/`, `support/path-remap/raw/`, and `support/path-remap/artifacts/`.
  - `support/cfg-attr-module/prepare.py`, `support/cfg-attr-module/probe.py`, `support/cfg-attr-module/check.py`, `support/cfg-attr-module/oracle.json`, `support/cfg-attr-module/results.json` (`979dc2b0…`), `support/cfg-attr-module/comparison.json`, `support/cfg-attr-module/fixture/`, `support/cfg-attr-module/raw/`, `support/cfg-attr-module/artifacts/`, and `support/cfg-attr-module/preliminary/`.
- **ASCII, Unicode, and generated-file span subprobes:**
  - `support/local-span-source-text/compare.py`, `support/local-span-source-text/check.py`, `support/local-span-source-text/comparison.json`, `support/local-span-source-text/source-results.json`, `support/local-span-source-text/source-states/`, and `support/local-span-source-text/artifacts/`.
  - `support/unicode-charon-spans/probe.py`, `support/unicode-charon-spans/check.py`, `support/unicode-charon-spans/results.json`, `support/unicode-charon-spans/comparison.json`, `support/unicode-charon-spans/fixture/`, and `support/unicode-charon-spans/unicode.llbc`.
  - `support/generated-file-charon-spans/probe.py`, `support/generated-file-charon-spans/check.py`, `support/generated-file-charon-spans/results.json`, `support/generated-file-charon-spans/comparison.json`, `support/generated-file-charon-spans/fixture/`, `support/generated-file-charon-spans/generated.rs`, `support/generated-file-charon-spans/generated.llbc`, and `support/generated-file-charon-spans/raw/`.
  - `support/generated-edge-spans/oracle.py`, `support/generated-edge-spans/probe.py`, `support/generated-edge-spans/check.py`, `support/generated-edge-spans/predeclared.json`, `support/generated-edge-spans/results.json`, `support/generated-edge-spans/comparison.json`, `support/generated-edge-spans/fixture/`, `support/generated-edge-spans/generated.rs`, `support/generated-edge-spans/generated.llbc`, and `support/generated-edge-spans/raw/`.

## Revalidation

Every subprobe includes an offline verifier that validates all retained hashes, JSON diffs, Lake traces, and span coordinate predictions without running compilers:

```sh
python3 support/charon-warm-noop-byte-diff/verify.py
python3 -B support/charon-shortname-aeneas-impact/check.py
python3 -B support/multifunction-translation-repeat/check.py
python3 -B support/five-function-lake-replay/check.py
python3 -B support/charon-relocation-comment-provenance/check.py
python3 -B support/symlink-module-identity/check.py
python3 -B support/path-remap/check.py
python3 -B support/cfg-attr-module/check.py
python3 -B support/local-span-source-text/check.py
python3 -B support/unicode-charon-spans/check.py
python3 -B support/generated-file-charon-spans/check.py
python3 -B support/generated-edge-spans/check.py
```
