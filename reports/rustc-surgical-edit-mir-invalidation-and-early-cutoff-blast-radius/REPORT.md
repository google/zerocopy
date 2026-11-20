# Surgical-Edit MIR Invalidation, `Const::Unevaluated` Early Cutoff, and `-O3` Incremental Blast Radius in `rustc`

## Summary

Across two multi-thousand-line production Rust crates—`miniz_oxide 0.9.1` (`Frommi/miniz_oxide` at `4e582392df3a739d2b0dfd2c537dc33e8942be38`, `358` `Runtime(PostCleanup)` MIR bodies and `280` `Runtime(Optimized)` MIR bodies) and `serde_json 1.0.154` (`serde-rs/json` at `20572a6d066958542d79cdd6cf1a7cd9f0c8e1f8`, `1,105` `Runtime(PostCleanup)` MIR bodies and `1,121` `Runtime(Optimized)` MIR bodies)—five controlled surgical source edits (`E1`–`E5`) compiled with `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) and `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) establish four quantitative laws governing function-modular MIR verification early cutoff, post-optimization MIR amplification, `-O3` LLVM IR stability, and `-C incremental` object reuse:

1. **Canonical Span-Stripped and `DefPath`-Keyed `Runtime(PostCleanup)` MIR Eliminates `100%` of Non-Semantic Source-Shift and Item-Append Noise (`E1`, `E5`):**
   - Inserting six comment lines near the top of a central module (`E1`) mutates **`80 / 358` (`22.35%`)** raw `Runtime(PostCleanup)` MIR dumps in `miniz_oxide` (`src/inflate/core.rs`) and **`148 / 1,105` (`13.39%`)** in `serde_json` (`src/ser.rs`). Stripping source-span comments and embedded `{closure@file:l1:c1: l2:c2}` / `<impl at file:l1:c1: l2:c2>` coordinates collapses the invalidation count to **`0 / 358`** and **`0 / 1,105`**, respectively.
   - Appending a new `pub fn` at end-of-file (`E5`, zero line shifts on existing items) still mutates **`2 / 358`** raw `PostCleanup` MIR dumps in `miniz_oxide` and **`17 / 1,105`** in `serde_json` through sequential crate-local `DefIndex` and scope-metadata shifts in modules parsed after the edited file; canonical span-stripped, `DefPath`-normalized MIR reduces existing-item invalidation to **`0`** on both crates (`+1` newly added body only).
2. **Pre-Inlining (`PostCleanup`) vs. Post-Optimization (`PreCodegen` and `-O3` LLVM IR) Blast-Radius Amplification (`E2`, `E3`):**
   - Modifying an expression inside a widely called `#[inline]` helper (`E3`) invalidates **exactly `1`** span-stripped `Runtime(PostCleanup)` MIR body on both `miniz_oxide` (`HuffmanTable::fast_lookup`, `1 / 358`) and `serde_json` (`<&mut Serializer<W, F> as serde::Serializer>::serialize_str`, `1 / 1,105`, down from `130` raw span-shifted bodies).
   - After `rustc`'s MIR optimization pipeline (`Inline`, `GVN`, `SROA`, `InstSimplify`), the blast radius expands `4x`–`6x` to **`4 / 280`** `Runtime(Optimized)` MIR bodies on `miniz_oxide` and **`6 / 1,121`** on `serde_json`. After LLVM `-O3` optimization, it reaches **`5 / 38`** LLVM IR functions (`cgu=1`) on `miniz_oxide` and **`20 / 271`** changed + **`7` added / `7` removed** `.llvm.<hash>` ThinLTO-promoted symbols (**`27`** symbol-level diffs, or **`10`** unique bodies after CGU-hash normalization) at `cgu=16` on `serde_json`.
3. **The `Const::Unevaluated` Early-Cutoff Soundness Hazard at `Runtime(PostCleanup)` (`E4`):**
   - Expression-position references to crate-internal `const` items remain symbolic (`Const::Unevaluated(DefId)`) in `Runtime(PostCleanup)` MIR and are only folded into scalar literals during `Runtime(Optimized)` (`GVN` / constant propagation). Mutating `const BASE_EXTRA_MASK: usize = 32 - 1` to `16 - 1` in `miniz_oxide` (`E4`) changes **only `1 / 358`** `PostCleanup` MIR body (`inflate::core::BASE_EXTRA_MASK` itself), leaving callers `decompress_fast` and `decompress_with_limit` **syntactically unchanged** in `PostCleanup` MIR even though both callers change in `PreCodegen` MIR (`2 / 280`) and `-O3` LLVM IR (`2 / 38`).
   - Conversely, pattern-position `const` references (`const BB: u8 = b'b'` -> `b'x'` in `serde_json` `E4`) are eagerly evaluated by CTFE during HIR-to-MIR match-pattern construction into concrete `SwitchInt` branch targets (`98` -> `120`), directly mutating `ser::format_escaped_str_contents` (`1 / 1,105`) in `PostCleanup` MIR, whereas trivial literal `const` items skip `Runtime(PostCleanup)` body emission (`lit_to_const`) and remain symbolic inside static array initializers (`static ESCAPE`). Sound early cutoff at `Runtime(PostCleanup)` (including Anneal's capture boundary in `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`) **must** therefore include both the transitive `Const::Unevaluated` dependency cone (`3 / 358` in `miniz_oxide`) and evaluated `ConstValue` digests of referenced literal `const` definitions.
4. **Post-`-O3` LLVM IR Couplings That Defeat Function- and CGU-Local Caching (`E1`, `E2`, `E4`, `E5`):**
   - **Implicit `&core::panic::Location` relocations (`E1`):** Even under `-C debuginfo=0`, a pure comment-line shift mutates **`3 / 38`** (`cgu=1`) and **`3 / 63`** (`cgu=16`) `-O3` LLVM IR functions in `miniz_oxide` (`apply_match`, `decompress_with_limit`, `transfer`) because implicit bounds-check and panic cold paths reference content-addressed `@alloc_<32hex>` static `Location` descriptors carrying line numbers (`0` functions change once `@alloc_*` symbol hashes are normalized).
   - **LLVM `MergeFunctions` pass unmerging (`E2` at `cgu=1`):** Editing a single literal `(0, 0)` -> `(0, 1)` inside private leaf `serde_json::ser::key_must_be_a_string` (`1 / 1,105` MIR bodies) mutates **`31 / 184` (`16.85%`)** `-O3` LLVM IR functions and adds **`+1` new `define`** (`184` -> `185`, `serde_json::value::ser::key_must_be_a_string`) under `-C codegen-units=1`, because `MergeFunctions` had previously merged the two structurally identical `key_must_be_a_string` helpers across modules.
   - **ThinLTO `.llvm.<hash>` cross-CGU cascading in `-C incremental` (`cgu=16`):** On `serde_json`, modifying `1 / 16` (`E2`) or `2 / 16` (`E4`) pre-LTO bitcode modules (`.pre-lto.bc`) triggers **`16 / 16` `.rcgu.o` re-emissions (`0 / 16` inode-reused)** (`9 / 16` and `10 / 16` `.rcgu.o` files changing bytes) as ThinLTO cross-module summary hashes propagate across partitions; incremental `-O3` wall-clock speedups over clean builds consequently plateau at **`1.68x`–`4.00x`** (`392.95`–`694.33 ms` vs. `876.17`–`1,571.39 ms` clean).

## Applicability

- **Examined compilers and host environment:**
  - `rust-lang/rust` release `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, commit date `2026-10-13`, `x86_64-unknown-linux-gnu`, bundled LLVM `23.1.1`) for all `-C opt-level=3 -C debuginfo=0 --emit=llvm-ir` measurements (at both `-C codegen-units=1` and `-C codegen-units=16`) and all `-C opt-level=3 -C codegen-units=16 -C debuginfo=0 -C incremental=<dir>` rebuild wall-clock and `.rcgu.o` / `.pre-lto.bc` reuse measurements.
  - `rust-lang/rust` `1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, commit date `2026-11-11`, `x86_64-unknown-linux-gnu`, bundled LLVM `23.1.5`) for unstable `-Z mir-include-spans=true -Z dump-mir="runtime-post-cleanup | runtime-optimized"` textual MIR pass dumps (`3-2-000.runtime-post-cleanup.after.mir` and `3-3-000.runtime-optimized.after.mir`), because stable `rustc 1.99.1` gates `-Z` flags without bootstrap overrides.
- **Examined target crates and dependency graphs:**
  - `Frommi/miniz_oxide` `0.9.1` (`4e582392df3a739d2b0dfd2c537dc33e8942be38`, subdirectory `miniz_oxide`), compiled with `--edition=2021 --crate-type=lib --cfg feature="with-alloc"` against precompiled `adler2 2.0.1` (`-C opt-level=3`), representing an algorithmic bit-manipulation and table-lookup crate with dense intra-module `#[inline]` helpers (`src/inflate/core.rs`, `2,381` baseline lines).
  - `serde-rs/json` `1.0.154` (`20572a6d066958542d79cdd6cf1a7cd9f0c8e1f8`), compiled with `--edition=2021 --crate-type=lib --cfg feature="default" --cfg feature="std" --cfg fast_arithmetic="64"` against precompiled `itoa 1.0.18`, `memchr 2.8.3`, `serde_core 1.0.229`, and `zmij 1.0.23` (`-C opt-level=3`), representing a trait-generic serialization/deserialization crate with heavy monomorphization across `Vec<u8>` and `fmt::Display` writers (`src/ser.rs`, `2,285` baseline lines).
  - Both crates include a fixed, unedited concrete exerciser module (`pub mod __vrustc_exerciser`) appended identically to `src/lib.rs` in baseline `E0` and all five edits `E1`–`E5` (`roundtrip_zlib` calling `compress_to_vec_zlib` and `decompress_to_vec_zlib` in `miniz_oxide`; `exercise_all` calling `from_str`, `from_slice`, `to_vec`, and `to_vec_pretty` on `serde_json::Value` in `serde_json`) so that generic and public entrypoints remain reachable during library dead-code pruning and LTO.
- **Relationship to Anneal MIR verification (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
  - Anneal's `rustc-capture` driver (`trusted/rustc-capture/src/driver.rs:76-95`) extracts `Runtime(PostCleanup)` MIR (`tcx.mir_drops_elaborated_and_const_checked`) into `Trusted.MirAst` (`trusted/lean/Trusted/MirAst.lean:53-60, 492-560`). The `PostCleanup` early-cutoff and `Const::Unevaluated` dependency-cone findings directly govern sound incremental proof-obligation caching at that capture seam.

## Findings

### 1. Experimental Protocol, Compiler Stages, and Canonicalization Definitions

`Basis: source + execution (support/e2_4_real_incremental_mir_cutoff.py, support/e2_4_real_incremental_mir_cutoff.json)`

To prevent cross-stage confounding, every surgical edit $E_i \in \{E_1, E_2, E_3, E_4, E_5\}$ is evaluated independently as a single transition $E_0 \rightarrow E_i$ from the exact unmodified baseline $E_0$ across four compiler representations:

1. **Phase 1 — Pre-optimization `Runtime(PostCleanup)` MIR (`*.3-2-000.runtime-post-cleanup.after.mir`):**
   - Dumped with `-C opt-level=3 -Z mir-include-spans=true -Z dump-mir="runtime-post-cleanup | runtime-optimized"`.
   - **Raw digest (`raw_changed_count`):** SHA-256 over exact `.mir` bytes, keyed by crate-relative item stem (`<filename>` stripped of `<crate>.` prefix and `.3-2-000.runtime-post-cleanup.after.mir` suffix).
   - **Span-stripped canonical digest (`span_stripped_changed_count`):** Strips full-line `//` headers/comments, trailing scope/span annotations (`// [return place ]in scope ...`, `// scope ... at ...`, `// mir::...`, `// ty::...`, `// + ...`), and embedded line/column coordinates inside closure and impl path segments (`{closure@file.rs:l1:c1: l2:c2}` $\rightarrow$ `{closure@file.rs}`; `<impl at file.rs:l1:c1: l2:c2>` $\rightarrow$ `<impl at file.rs>`), while preserving `100%` of local variable declarations, types, basic blocks, statements, rvalues, constant operands, and terminators.
   - **Span-stripped + transitive `Const::Unevaluated` dependency cone (`span_stripped_plus_const_cone_changed_count`):** Fixed-point closure propagating invalidation from any changed MIR body whose `DefPath` $d$ appears as a symbolic `const <path>` reference inside another body's canonical MIR text.
2. **Phase 2 — Post-optimization `Runtime(Optimized)` / `PreCodegen` MIR (`*.3-3-000.runtime-optimized.after.mir`):**
   - Captured after `rustc`'s full runtime MIR optimization pass pipeline (including `Inline`, `PromoteTemps`, `GVN`, `SROA`, `InstSimplify`, and `DeadStoreElimination`), hashed both raw and span-stripped.
3. **Phase 3 — Post-`-O3` LLVM IR (`rustc 1.99.1 -C opt-level=3 -C debuginfo=0 --emit=llvm-ir` at `cgu=1` and `cgu=16`):**
   - Parses every `define ... @<sym>(...) { ... }` across all emitted `.ll` modules, expanding numeric `#N` attribute-group references inline (`attributes #N = { ... }`) and stripping `!dbg`/`!prof`/`!guid` metadata tags so purely syntactic LLVM numbering shifts do not masquerade as code changes.
   - Evaluates three nested equivalences per symbol:
     - **Exact normalized (`llvm_o3_fn_changed`):** Exact symbol name and normalized instruction sequence.
     - **`@alloc_*` panic-location erased (`llvm_o3_alloc_location_erased_changed`):** Replaces content-addressed `@alloc_<32hex>` and `@anon.<32hex>.<id>` constant pool symbol names with `@ALLOC_CONST` to isolate `&core::panic::Location` line-shift relocations.
     - **CGU-hash and `@alloc_*` erased (`llvm_o3_alloc_and_cgu_hash_erased_changed`):** Additionally normalizes `.llvm.<decimal_hash>` ThinLTO local-promotion suffixes on both function names and call targets to `.llvm.HASH`.
4. **Phase 4 — `rustc 1.99.1` `-O3` Incremental Rebuild Timing and Object-File Inode Reuse (`-C opt-level=3 -C codegen-units=16 -C debuginfo=0 -C incremental=<dir>`):**
   - Measures median wall-clock over `3` clean cold `-O3` builds (after `1` warm-up build on $E_0$) vs. median wall-clock over `3` independent $E_0 \rightarrow E_i$ incremental rebuilds.
   - Before every incremental trial, the incremental session directory is reset via a full non-hardlinked directory copy (`shutil.copytree`) from a clean $E_0$ seed snapshot, and every baseline `.rcgu.o` inode in the active session directory is hardlinked into an external pin directory (`os.link`, verified immutable by SHA-256 after `rustc` exits). Pinning prevents `tmpfs` from recycling inode numbers when `rustc`'s session garbage collector deletes the predecessor `s-<timestamp>-*` directory, providing exact counts of hardlink-reused `.rcgu.o` files (`st_ino` preserved), re-emitted `.rcgu.o` files, byte-modified `.rcgu.o` files, and byte-modified `.pre-lto.bc` bitcode modules.

Table 1 summarizes the unmodified baseline (`E0`) scale of both crates across all four compiler stages:

| Crate Subject | Central Edited Module (Baseline Lines) | `PostCleanup` MIR Bodies | `PreCodegen` (`Optimized`) MIR Bodies | `-O3` LLVM IR Functions (`cgu=1`) | `-O3` LLVM IR Unique Symbols / Total `define`s (`cgu=16`) | Clean `-O3` Build Median (`ms`, `cgu=16`) | Initial `-C incremental` Seed Build (`ms`, `cgu=16`) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `miniz_oxide 0.9.1` | `src/inflate/core.rs` (`2,381`) | `358` | `280` | `38` | `63` / `63` | `1,264.29` | `1,401.91` (`16` `.o`, `16` `.bc`) |
| `serde_json 1.0.154` | `src/ser.rs` (`2,285`) | `1,105` | `1,121` | `184` | `271` / `274` | `1,288.82` | `1,553.36` (`16` `.o`, `16` `.bc`) |

Note the bidirectional shift between `PostCleanup` and `PreCodegen` MIR body counts: `miniz_oxide` drops from `358` to `280` (`-78` bodies) because `const` definitions and promoted array/constant bodies dump at `runtime-post-cleanup` without running through `runtime-optimized`, whereas `serde_json` rises from `1,105` to `1,121` (`+16` bodies) because synthetic shims and closures materialized for monomorphized trait methods outnumber non-runtime `const` items.

---

### 2. Complete Surgical-Edit Invalidation Matrix Across `miniz_oxide 0.9.1` and `serde_json 1.0.154` (`E1`–`E5`)

`Basis: execution (support/e2_4_real_incremental_mir_cutoff.json)`

The five surgical edits probe orthogonal axes of compiler invalidation on `miniz_oxide/src/inflate/core.rs` and `serde_json/src/ser.rs`:

- **`E1` (`E1_top_comment_shift` — pure line-number shift):**
  - `miniz_oxide`: Insert `6` `//` comment lines immediately above `pub const TINFL_LZ_DICT_SIZE: usize = 32_768;` at `src/inflate/core.rs:42`.
  - `serde_json`: Insert `6` `//` comment lines immediately above `/// A structure for serializing Rust values into JSON.` (`pub struct Serializer`) at `src/ser.rs:15`, shifting all `199` downstream functions and impl methods in `src/ser.rs` by `+6` lines.
- **`E2` (`E2_private_noninline_leaf` — private, non-generic, non-inlined leaf body):**
  - `miniz_oxide`: Change `table.tree.fill(0);` to `table.tree.fill(1);` inside private `inflate::core::init_tree` (`src/inflate/core.rs:899`, zero line shift).
  - `serde_json`: Change `Error::syntax(ErrorCode::KeyMustBeAString, 0, 0)` to `(0, 1)` inside private `ser::key_must_be_a_string` (`src/ser.rs:788`, zero line shift).
- **`E3` (`E3_widely_inlined_helper` — widely called `#[inline]` helper body):**
  - `miniz_oxide`: Change `self.look_up[(bit_buf & (FAST_LOOKUP_SIZE - 1) as BitBuffer) as usize]` to `((bit_buf ^ 1) & ...)` inside `#[inline] const fn HuffmanTable::fast_lookup` (`src/inflate/core.rs:74-76`, zero line shift).
  - `serde_json`: Insert a branch guard `if value.len() == 0x7fff_ffff { "" } else { value }` inside `#[inline] fn serialize_str` on `<&mut Serializer<W, F> as serde::Serializer>` (`src/ser.rs:189-192`, expanding the method by `+5` lines and simultaneously shifting downstream spans in `src/ser.rs`).
- **`E4` (`E4_internal_const` — internal `const` value modification):**
  - `miniz_oxide`: Change `const BASE_EXTRA_MASK: usize = 32 - 1;` to `16 - 1;` at `src/inflate/core.rs:545` (referenced in expression position inside `decompress_fast` and `decompress_with_limit`).
  - `serde_json`: Change `const BB: u8 = b'b';` to `b'x';` at `src/ser.rs:2135` (referenced both in match-pattern position inside `ser::format_escaped_str_contents` and in expression position inside `static ESCAPE: [u8; 256]`).
- **`E5` (`E5_append_new_pub_fn` — EOF public function addition, zero line shifts):**
  - Append `pub fn __vrustc_probe_added(x: u64) -> u64 { x.wrapping_add(1) }` at EOF of `src/inflate/core.rs` (line `2,382`) and `src/ser.rs` (line `2,286`), respectively.

Table 2 records the complete MIR and `-O3` LLVM IR invalidation counts for **`miniz_oxide 0.9.1`**:

| Edit | `PostCleanup` MIR Raw Changed (`/ 358`) | `PostCleanup` Span-Stripped Changed | `PostCleanup` + `Const` Cone Changed | `PreCodegen` MIR Raw / Span-Stripped (`/ 280`) | `-O3` LLVM IR `cgu=1` Exact / `@alloc`-Erased (`/ 38`) | `-O3` LLVM IR `cgu=16` Exact / `@alloc`-Erased / CGU-Erased (`/ 63`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `E1_top_comment_shift` | `80` | **`0`** | **`0`** | `63` / **`0`** | **`3`** / `0` | **`3`** / `0` / `0` |
| `E2_private_noninline_leaf` | `1` | **`1`** | **`1`** | `1` / **`1`** | **`1`** / `1` | **`1`** / `1` / `1` |
| `E3_widely_inlined_helper` | `1` | **`1`** | **`1`** | `4` / **`4`** | **`5`** / `5` | **`3`** / `3` / `3` |
| `E4_internal_const` | `1` | **`1`** *(unsound alone)* | **`3`** | `2` / **`2`** | **`2`** / `2` | **`2`** / `2` / `2` |
| `E5_append_new_pub_fn` (`+1` MIR item) | `2` | **`0`** (`+1` added) | **`0`** (`+1` added) | `1` / **`0`** (`+1` added) | **`0`** / `0` (`0` added) | **`0`** / `0` / `0` (`0` added) |

Table 3 records the complete MIR and `-O3` LLVM IR invalidation counts for **`serde_json 1.0.154`**:

| Edit | `PostCleanup` MIR Raw Changed (`/ 1,105`) | `PostCleanup` Span-Stripped Changed | `PostCleanup` + `Const` Cone Changed | `PreCodegen` MIR Raw / Span-Stripped (`/ 1,121`) | `-O3` LLVM IR `cgu=1` Exact / `@alloc`-Erased (`+Added/-Rem` on `184`) | `-O3` LLVM IR `cgu=16` Exact / CGU-Erased (`+Added/-Rem` on `271`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `E1_top_comment_shift` | `148` | **`0`** | **`0`** | `143` / **`0`** | **`0`** / `0` (`+0/-0`) | **`0`** / `0` (`+0/-0`) |
| `E2_private_noninline_leaf` | `1` | **`1`** | **`1`** | `1` / **`1`** | **`31`** / `30` (**`+1/-0`**) | **`11`** / **`1`** (**`+4/-4`**) |
| `E3_widely_inlined_helper` | `130` | **`1`** | **`1`** | `127` / **`6`** | **`2`** / `2` (`+0/-0`) | **`20`** / **`10`** (**`+7/-7`**) |
| `E4_internal_const` | `1` | **`1`** | **`1`** *(+ static table)* | `1` / **`1`** | **`2`** / `2` (`+0/-0`) | **`12`** / **`4`** (**`+4/-4`**) |
| `E5_append_new_pub_fn` (`+1` MIR item) | `17` | **`0`** (`+1` added) | **`0`** (`+1` added) | `3` / **`0`** (`+1` added) | **`0`** / `0` (`+0/-0`) | **`0`** / `0` (`+0/-0`) |

Table 4 records the real `rustc 1.99.1 -C opt-level=3 -C codegen-units=16 -C debuginfo=0 -C incremental` rebuild performance and object/bitcode reuse across both crates:

| Crate & Edit | Clean `-O3` Median (`ms`) | Incremental `-O3` Median (`ms`) | Speedup vs. Clean (`x`) | `.rcgu.o` Reused / Total (Hardlink Inode) | `.rcgu.o` Re-Emitted / Bytes Changed | `.pre-lto.bc` Changed / Total |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `miniz_oxide` `E1` (comment shift) | `1,115.08` | `556.82` | `2.003x` | `12 / 16` | `4` re-emitted / `2` changed | `2 / 16` |
| `miniz_oxide` `E2` (private leaf) | `889.27` | `528.34` | `1.683x` | `13 / 16` | `3` re-emitted / `1` changed | `1 / 16` |
| `miniz_oxide` `E3` (`#[inline]` fn) | `1,186.01` | `531.57` | `2.231x` | `12 / 16` | `4` re-emitted / `2` changed | `2 / 16` |
| `miniz_oxide` `E4` (`const` mask) | `1,571.39` | `392.95` | `3.999x` | `13 / 16` | `3` re-emitted / `1` changed | `1 / 16` |
| `miniz_oxide` `E5` (append `pub fn`) | `876.17` | `416.59` | `2.103x` | `13 / 16` | `3` re-emitted / `1` changed | `1 / 16` |
| `serde_json` `E1` (comment shift) | `1,249.05` | `518.41` | `2.409x` | `15 / 16` | `1` re-emitted / **`0`** changed | **`0 / 16`** |
| `serde_json` `E2` (private leaf) | `1,004.63` | `471.32` | `2.132x` | **`0 / 16`** | **`16`** re-emitted / **`9`** changed | `1 / 16` |
| `serde_json` `E3` (`#[inline]` fn) | `1,069.50` | `491.20` | `2.177x` | `8 / 16` | `8` re-emitted / `4` changed | `3 / 16` |
| `serde_json` `E4` (`const BB`) | `1,206.23` | `589.05` | `2.048x` | **`0 / 16`** | **`16`** re-emitted / **`10`** changed | `2 / 16` |
| `serde_json` `E5` (append `pub fn`) | `1,241.81` | `694.33` | `1.789x` | **`0 / 16`** | **`16`** re-emitted / **`11`** changed | `3 / 19` (`+3` CGUs) |

---

### 3. Span Stripping, Sequential `DefIndex` Perturbation, and Pre-Inlining Early Cutoff (`E1`, `E3`, `E5`)

`Basis: source + execution + derived`

Comparing raw `.mir` digests against canonical span-stripped `DefPath`-keyed digests across `E1`, `E3`, and `E5` isolates three distinct sources of spurious invalidation that a naive MIR verifier or translation-validation cache must normalize away:

1. **Intra-file line-shift cascades (`E1` and `serde_json` `E3`):**
   - When `-Z mir-include-spans=true` (or equivalent `Statement::source_info` / `LocalDecl::source_info` `Span` fields in `rustc_middle::mir::Body`) is included in a per-body hash, inserting `6` comment lines near the top of `src/inflate/core.rs` (`E1`) invalidates `80 / 358` `PostCleanup` bodies, and inserting `6` comment lines near line `15` of `src/ser.rs` (`E1`) invalidates `148 / 1,105` `PostCleanup` bodies.
   - Even an ordinary multi-line code edit inside a single `#[inline]` method (`serde_json` `E3`, which expands `serialize_str` at `src/ser.rs:190` by `5` lines) shifts spans for `129` untouched items below line `195`, producing **`130` raw `PostCleanup` MIR diffs** when only **`1` body (`serialize_str`)** actually changed semantics.
   - Note that line/column coordinates also leak into `DefPath`-like header and operand strings for anonymous impl blocks and closures (`ser::<impl at .../src/ser.rs:63:1: 66:18>::serialize_str` and `{closure@...}`). Canonicalization must erase `:line:col: line:col` suffixes inside impl and closure descriptors—or key impl blocks by semantic `(SelfTy, TraitRef)` / disambiguated HIR path—rather than stripping trailing `//` comments alone.
2. **Cross-module sequential `DefIndex` and `SourceMap` offset perturbation on EOF append (`E5`):**
   - In `E5`, `pub fn __vrustc_probe_added` is appended strictly at the last line of `src/inflate/core.rs` (`miniz_oxide`) and `src/ser.rs` (`serde_json`), leaving every existing byte offset and line/column coordinate inside the edited file unchanged.
   - Nevertheless, **`2 / 358`** existing raw `PostCleanup` `.mir` dumps change in `miniz_oxide` and **`17 / 1,105`** change in `serde_json` (`3 / 1,121` in `PreCodegen`). Because `rustc` assigns crate-local `DefIndex` values and `SourceMap` global `BytePos` intervals sequentially in module-expansion order (`mod ser;` precedes `pub mod value;`, `mod io;`, `mod iter;`, `mod lexical;`, `mod number;`, `mod read;`, and `mod raw;` in `serde_json/src/lib.rs:427-441`), growing `src/ser.rs` by `76` bytes and `+1` HIR item shifts internal scope/span metadata in subsequently loaded submodules. Span-stripped, `DefPath`-normalized MIR reduces existing-item invalidation to **`0 / 358`** and **`0 / 1,105`**.
3. **Function-modular verification cutoff at `PostCleanup` vs. inlining amplification at `PreCodegen` (`E3`):**
   - At `Runtime(PostCleanup)`, `#[inline]` calls remain explicit `TerminatorKind::Call` edges (`Trusted.MirAst.TerminatorKind.call` in `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/Trusted/MirAst.lean:780-795`). If `HuffmanTable::fast_lookup`'s specification (`requires`/`ensures` contract) is unchanged, an implementation edit inside `fast_lookup` (`E3`) requires re-verifying **only `1 / 358` (`0.28%`)** `PostCleanup` body in `miniz_oxide` and **`1 / 1,105` (`0.09%`)** in `serde_json`.
   - Waiting until `Runtime(Optimized)` (`PreCodegen`) to discharge proof obligations multiplies the re-verification set `4x` on `miniz_oxide` (`fast_lookup` + `lookup`, `decode_huffman_code`, and `decompress_fast`) and `6x` on `serde_json` (`serialize_str` + two `serialize_char` impls, `serialize_newtype_variant`, `serialize_struct_variant`, and `serialize_tuple_variant`), and waiting until `-O3` LLVM IR (`cgu=16`) multiplies it up to **`10`–`20` monomorphized functions** (`format_escaped_str`, `Compound::serialize_entry`, `Serializer::collect_seq`, `Value::from`, `WriterFormatter::write_all`).

---

### 4. The `Const::Unevaluated` Early-Cutoff Soundness Hazard (`E4`)

`Basis: source + execution + derived`

Edit `E4` uncovers a sharp, load-bearing asymmetry in how `rustc` lowers `const` references into `Runtime(PostCleanup)` MIR depending on syntactic position (expression vs. pattern) and constant complexity (compound expression vs. trivial literal):

1. **Compound expression-position `const` (`miniz_oxide` `E4`: `const BASE_EXTRA_MASK: usize = 32 - 1` $\rightarrow$ `16 - 1`):**
   - Because `32 - 1` is a binary arithmetic expression (`Rvalue::BinaryOp(BinOp::SubWithOverflow, ...)` with an overflow `Assert` terminator), `rustc` builds a `Runtime(PostCleanup)` MIR body for `inflate::core::BASE_EXTRA_MASK`.
   - Inside `inflate::core::decompress_fast` and `inflate::core::decompress_with_limit`, however, expression-position occurrences of `BASE_EXTRA_MASK` are lowered in `Runtime(PostCleanup)` MIR as symbolic **`Const::Unevaluated(DefId(inflate::core::BASE_EXTRA_MASK))`** operands (`const inflate::core::BASE_EXTRA_MASK`), *not* as evaluated scalar `ConstValue::Scalar(31_usize)` literals.
   - Consequently, when `BASE_EXTRA_MASK` changes from `32 - 1` (`31`) to `16 - 1` (`15`):
     - Syntactic span-stripped `PostCleanup` MIR hashing detects **only `1 / 358` changed body** (`inflate::core::BASE_EXTRA_MASK`), reporting **`0` changes** to `decompress_fast` and `decompress_with_limit`!
     - During `Runtime(Optimized)` (`PreCodegen`) MIR optimization, `GVN` / constant propagation evaluates `Const::Unevaluated` via CTFE and substitutes `const 15_usize` into `BitAnd` rvalues inside both `decompress_fast` and `decompress_with_limit`, mutating **`2 / 280` `PreCodegen` MIR bodies** and **`2 / 38` (`cgu=1`) / `2 / 63` (`cgu=16`) `-O3` LLVM IR functions** (while `BASE_EXTRA_MASK` itself disappears after CTFE).
2. **Trivial literal `const` in pattern position vs. static array initializer (`serde_json` `E4`: `const BB: u8 = b'b'` $\rightarrow$ `b'x'`):**
   - `const BB: u8 = b'b'` (`src/ser.rs:2135`) is a single byte literal. `rustc`'s literal constant fast path (`lit_to_const`) does **not** emit a `Runtime(PostCleanup)` `.mir` dump for `ser::BB` itself (`n_baseline = 1,105` has no `ser.BB` entry).
   - Where `BB` appears as a `match` arm pattern inside `ser::format_escaped_str_contents`, `rustc_mir_build` eagerly invokes CTFE during pattern lowering to construct concrete `TerminatorKind::SwitchInt` integer branch targets (`switchInt(...) -> [..., 98: bb_b, ...]` $\rightarrow$ `[..., 120: bb_b, ...]`), so `ser::format_escaped_str_contents` **does** change directly in `PostCleanup` MIR (`1 / 1,105`).
   - Where `BB` appears in expression position inside `static ESCAPE: [u8; 256] = [UU, ..., BB, ...]` (`src/ser.rs:2147-2165`), `ser::ESCAPE`'s `Runtime(PostCleanup)` MIR body retains symbolic `[..., const ser::BB, ...]` (`0` syntactic diff in `ser::ESCAPE`'s `PostCleanup` `.mir` text!), even though the emitted `-O3` `.rodata` byte table `@...ESCAPE` mutates byte `8` from `0x62` (`'b'`) to `0x78` (`'x'`)!
3. **Mandatory Early-Cutoff Invariant for `Runtime(PostCleanup)` Verifiers:**
   - Keying incremental proof-obligation reuse on a function's span-stripped `Runtime(PostCleanup)` MIR AST alone is **unsound**: any theorem proved about `decompress_fast` (for example, bounds safety of indexing a 32-entry table with `idx & BASE_EXTRA_MASK` if `BASE_EXTRA_MASK` were widened from `16 - 1` to `64 - 1`) would silently stay cached across a `const` edit!
   - Sound early cutoff at `Runtime(PostCleanup)` requires hashing every body $f$ together with the Merkle digest of:
     1. Every `ty::ConstKind::Unevaluated(uv)` (`DefId` + generic args) and `static` `DefId` transitively reachable from $f$'s MIR operands (either via their `PostCleanup` MIR + CTFE digest or via `tcx.const_eval_poly` / `eval_to_valtree` evaluated `ConstValue`), covering both MIR-backed compound `const` items (`BASE_EXTRA_MASK`, expanding `miniz_oxide` `E4` from `1 / 358` to **`3 / 358`**) and trivial literal `const` items (`BB` inside `ESCAPE`) that skip `Runtime(PostCleanup)` body generation;
     2. Every callee `DefId`'s contract/specification summary (`#[spec]` or inline operational body when proved by unfolding); and
     3. Layout/type definitions (`ty::AdtDef`, `repr`, trait impls) referenced by local declarations and projections in $f$.

---

### 5. Post-`-O3` LLVM IR and `-C incremental` Couplings (`Location` Pools, `MergeFunctions`, ThinLTO `.llvm.<hash>`, and `.rmeta` Inlining)

`Basis: execution + source + derived`

Even when MIR changes are confined to `0` or `1` function body, four backend mechanisms in `rustc 1.99.1` + LLVM `23.1.1` widen invalidation across post-`-O3` LLVM IR functions and `.rcgu.o` object files:

1. **Implicit `&core::panic::Location` constant-pool relocations under `-C debuginfo=0` (`miniz_oxide` `E1`):**
   - Although `-C debuginfo=0` strips DWARF `!dbg` metadata, Rust's runtime panic and slice bounds-check machinery (`core::panicking::panic_bounds_check`, `Option::unwrap`, `slice::copy_from_slice`) passes a static `&'static core::panic::Location<'static>` containing `(file_ptr, file_len, line: u32, col: u32)`.
   - `rustc_codegen_ssa` interns each `Location` as an anonymous global `@alloc_<32hex>` whose 128-bit symbol hash incorporates its contents. Shifting line numbers by `+6` in `miniz_oxide/src/inflate/core.rs` (`E1`) rehashes `@alloc_*` globals referenced inside `apply_match`, `decompress_with_limit`, and `transfer`, mutating **`3 / 38`** (`cgu=1`) and **`3 / 63`** (`cgu=16`) `-O3` LLVM IR function bodies and causing `rustc -C incremental` to re-emit `4 / 16` `.rcgu.o` files (`2 / 16` with changed machine-code relocation symbols). Erasing `@alloc_<32hex>` symbol hashes drops the LLVM IR diff to **`0`** (`llvm_o3_alloc_location_erased_changed = 0`).
   - By contrast, `serde_json` `E1` exhibits **`0 / 184`** (`cgu=1`) and **`0 / 271`** (`cgu=16`) changed `-O3` LLVM IR functions and **`0 / 16` byte-changed `.rcgu.o` files** (with `1 / 16` `.rcgu.o` re-emitted identically), because the serialized hot paths in `src/ser.rs` return `Result<_, Error>` without bounds-check `Location` allocations anchored below line `15` in the surviving `-O3` functions.
2. **LLVM `MergeFunctions` pass unmerging (`serde_json` `E2` at `-C codegen-units=1`):**
   - In `serde_json`, two private helpers—`serde_json::ser::key_must_be_a_string` (`src/ser.rs:787`) and `serde_json::value::ser::key_must_be_a_string` (`src/value/ser.rs`)—both construct `Error::syntax(ErrorCode::KeyMustBeAString, 0, 0)` in baseline `E0`. Under `-C opt-level=3 -C codegen-units=1`, both functions reside in the single LLVM module and compile to identical IR; LLVM's `MergeFunctions` pass (`rustc` enables `-Z merge-functions=trampolines` / `unnamed_addr` merging by default on targets supporting it) collapses `value::ser::key_must_be_a_string` into `ser::key_must_be_a_string`, leaving `184` `define`s.
   - Changing `(0, 0)` to `(0, 1)` inside `ser::key_must_be_a_string` (`E2`) breaks body equality between the two functions. `value::ser::key_must_be_a_string` reappears as an independent `define` (`184` $\rightarrow$ **`185`**, `added_demangled = ["serde_json::value::ser::key_must_be_a_string"]`), and unmerging plus unnamed-address constant/callee re-indexing cascades across **`31 / 184` (`16.85%`)** functions (`30` after `@alloc_*` erasure), touching unrelated `FromStr`, `Index`, `Debug::fmt`, and `SliceRead` implementations!
3. **ThinLTO `.llvm.<hash>` promotion and `0 / 16` `.rcgu.o` reuse in `rustc -C incremental` (`serde_json` `E2`, `E4`, `E5` at `cgu=16`):**
   - Under `-C opt-level=3 -C codegen-units=16`, `rustc` runs intra-crate ThinLTO across the 16 CGUs. When `internal` functions are promoted for cross-CGU importing, LLVM appends a module-hash suffix `.llvm.<u64>` (for example, `<Value as Serialize>::serialize::<&mut Serializer<&mut Vec<u8>>>.llvm.14736115641352483984`).
   - On `serde_json` `E2`, only **`1 / 16` `.pre-lto.bc`** bitcode module changes bytes (`pre_lto_bc_changed_bytes = 1`) and only **`1 / 271`** function body changes after `.llvm.<hash>` normalization (`llvm_o3_alloc_and_cgu_hash_erased_changed = 1`). Yet mutating that single CGU's module hash renames `4` promoted `<Value as Serialize>::serialize` symbols (`.llvm.14736115641352483984` $\rightarrow$ `.llvm.8968351992519068916`), mutating `11` caller definitions across other CGUs and invalidating ThinLTO summary imports across the entire crate: **`16 / 16` `.rcgu.o` object files are re-emitted (`0 / 16` inode-reused, `9 / 16` with changed bytes)**! The identical `0 / 16` `.rcgu.o` reuse occurs on `serde_json` `E4` (`2 / 16` `.pre-lto.bc` changed $\rightarrow$ `16 / 16` `.rcgu.o` re-emitted, `10 / 16` changed bytes) and `E5` (`3 / 19` `.pre-lto.bc` changed $\rightarrow$ `16 / 16` `.rcgu.o` re-emitted, `11 / 16` changed bytes).
4. **`cross_crate_inline_threshold` `.rmeta`-only emission on new small `pub fn` items (`E5`):**
   - Appending `pub fn __vrustc_probe_added(x: u64) -> u64 { x.wrapping_add(1) }` to an `--crate-type=lib` (`rlib`) crate at `-C opt-level=3` adds `+1` body in `PostCleanup` and `PreCodegen` MIR, yet adds **`0` `define`s in `-O3` LLVM IR** at both `cgu=1` and `cgu=16` on both `miniz_oxide` and `serde_json`!
   - Under `-C opt-level=3`, `rustc`'s automatic cross-crate MIR inliner (`cross_crate_inline_threshold`) marks small non-generic `pub fn` items as cross-crate inlinable in `.rmeta` rather than emitting an exported object-file symbol when unreferenced locally (confirmed directly on a minimal 6-line `--crate-type=lib -C opt-level=3` reproducer). Even so, under `-C incremental` on `serde_json`, partitioning the new item creates `3` additional pre-LTO bitcode units (`16` $\rightarrow$ `19` `.pre-lto.bc`) and triggers `16 / 16` `.rcgu.o` re-emissions (`694.33 ms`, `1.789x` vs. clean).

## Boundaries

- **Debug/unoptimized (`-C opt-level=0`) incremental builds (`not examined`):** All LLVM IR and `-C incremental` measurements in this package use release optimization (`-C opt-level=3 -C debuginfo=0`), where intra-crate ThinLTO, `MergeFunctions`, and `cross_crate_inline_threshold` are active. Under `-C opt-level=0` (where ThinLTO and `MergeFunctions` are disabled), CGU `.rcgu.o` hardlink reuse on `serde_json` `E2`/`E4`/`E5` will be substantially higher than `0 / 16`.
- **Cross-crate downstream `.rmeta` invalidation (`not examined`):** This study measures intra-crate MIR, LLVM IR, `.pre-lto.bc`, and `.rcgu.o` invalidation within `miniz_oxide` and `serde_json`. How surgical edits to a `pub` or `#[inline]` item (`E3`, `E5`) propagate across crate boundaries via `SVH` (`StrictVersionHash`) and `.rmeta` query hashes in multi-crate Cargo workspaces was `not examined` here.
- **Procedural macros, `build.rs` code generation, and trait coherence edits (`not examined`):** Edits `E1`–`E5` modify module comments, function bodies, internal `const` definitions, and leaf `pub fn` additions; adding a blanket `impl` or modifying a `proc_macro` expansion touches crate-wide trait-selection queries not exercised by `E1`–`E5`.
- **Stronger conclusions `known not to apply`:**
  - *Syntactic `Runtime(PostCleanup)` MIR equality implies semantic equivalence:* **Known not to apply** (`E4`). Expression-position `Const::Unevaluated` operands remain symbolic in `PostCleanup` MIR, so mutating a `const` definition changes callee/caller runtime behavior (`decompress_fast`, `decompress_with_limit`, `ESCAPE`) with zero syntactic diff in the referencing body's `PostCleanup` MIR.
  - *`-C debuginfo=0` makes `-O3` LLVM IR invariant to comment/whitespace line shifts:* **Known not to apply** (`miniz_oxide` `E1`). Implicit `&core::panic::Location` descriptors carry source line numbers into `@alloc_*` `.rodata` globals unless `-Z location-detail=none` or panic-immediate-abort strips line numbers.
  - *Editing a private non-inlined leaf function changes at most `1` `-O3` LLVM IR function and `1` incremental `.rcgu.o` object file:* **Known not to apply** (`serde_json` `E2`, where `MergeFunctions` unmerging mutates `31 / 184` functions at `cgu=1` and ThinLTO `.llvm.<hash>` cascading re-emits `16 / 16` `.rcgu.o` files at `cgu=16`).

## Evidence

- **Preserved executable probe and complete structured measurement dataset:**
  - `support/e2_4_real_incremental_mir_cutoff.py` — standalone Python 3.10+ harness compiling leaf `.rlib` dependencies (`adler2 2.0.1`, `itoa 1.0.18`, `memchr 2.8.3`, `serde_core 1.0.229`, `zmij 1.0.23`), applying exact `E0`–`E5` source transforms on `miniz_oxide 0.9.1` and `serde_json 1.0.154` in `/tmp/vrustc_e2_4`, computing raw/span-stripped/`Const::Unevaluated`-cone MIR hashes, normalizing `-O3` LLVM IR (`cgu=1` and `cgu=16`), and benchmarking inode-pinned `rustc 1.99.1 -C incremental` rebuilds.
  - `support/e2_4_real_incremental_mir_cutoff.json` — full recorded JSON output (`observed_at: 2026-11-20`) including toolchain `-vV` metadata, per-edit changed demangled symbol lists, `3`-sample timing arrays, and `.rcgu.o` / `.pre-lto.bc` reuse counts.
- **Primary pinned upstream revisions:**
  - `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc 1.99.1`, LLVM `23.1.1`).
  - `rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, LLVM `23.1.5`).
  - `Frommi/miniz_oxide` at `4e582392df3a739d2b0dfd2c537dc33e8942be38` (`miniz_oxide 0.9.1`, `miniz_oxide/src/inflate/core.rs:42, 74, 545, 898`).
  - `serde-rs/json` at `20572a6d066958542d79cdd6cf1a7cd9f0c8e1f8` (`serde_json 1.0.154`, `src/ser.rs:15, 190, 787, 2135, 2147-2165`).
  - `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/rustc-capture/src/driver.rs:76-95` `Runtime(PostCleanup)` capture hook; `trusted/lean/Trusted/MirAst.lean:492-560, 780-795` `ConstOperand` and `TerminatorKind` representations).

## Revalidation

1. **Fast minimal discriminator (~2 seconds, requires only `rustc +nightly` or `RUSTC_BOOTSTRAP=1 rustc +1.99.1`):**
   Compile a two-function crate containing `pub const MASK: usize = 32 - 1; pub fn apply(x: usize) -> usize { x & MASK }` with `-C opt-level=3 -Z dump-mir="runtime-post-cleanup | runtime-optimized"`, change `32 - 1` to `16 - 1`, and verify that `apply`'s `runtime-post-cleanup` MIR still contains symbolic `const MASK` (`0` diff after span stripping) while `apply`'s `runtime-optimized` MIR changes from `BitAnd(copy _1, const 31_usize)` to `BitAnd(copy _1, const 15_usize)`.
2. **Full two-crate `E0`–`E5` reproduction (~75 seconds):**
   Ensure `rustup` toolchains `1.99.1` and `nightly` are installed and Cargo's registry cache (`$CARGO_HOME/registry/src/index.crates.io-*`) contains `miniz_oxide-0.9.1`, `adler2-2.0.1`, `serde_json-1.0.154`, `itoa-1.0.18`, `memchr-2.8.3`, `serde_core-1.0.229`, and `zmij-1.0.23`, then run:

```bash
VRUSTC_OUT_JSON=/tmp/revalidated_e2_4.json \
  python3 reports/rustc-surgical-edit-mir-invalidation-and-early-cutoff-blast-radius/support/e2_4_real_incremental_mir_cutoff.py
```

Verify in `/tmp/revalidated_e2_4.json` that `E1` span-stripped `PostCleanup` MIR invalidation equals `0` on both crates, `miniz_oxide` `E4` jumps from `1` (`span_stripped_changed_count`) to `3` (`span_stripped_plus_const_cone_changed_count`), and `serde_json` `E2` exhibits `MergeFunctions` unmerging (`+1` `define`) at `cgu=1` and `0 / 16` `.rcgu.o` reuse at `cgu=16`.
