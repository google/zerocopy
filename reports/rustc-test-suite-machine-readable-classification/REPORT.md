# Machine-Readable Classification of `rustc` 1.99.1 Test Suites

## Summary

Across all 21 `compiletest` suites in `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `tests/` contains **24,545 top-level test entrypoints** (24,477 `.rs` / `.goml` / `rmake.rs` / `Makefile` test files plus 68 `.js` files in `tests/rustdoc-js-std`, accompanied by 1,341 auxiliary `.rs` files in `auxiliary/` subdirectories and 13,667 `.stderr` golden files). Standard-library crates under `library/` add **4,819 `#[test]` functions** (led by `coretests` with 1,645, `alloctests` with 1,228, and `std` with 965).

Mechanically classifying every test file in `tests/` (`support/test_catalog.jsonl.gz` and `support/test_classification_summary.json`) partitions the 24,545 compiler test entrypoints into five pipeline tiers:

1. **Frontend-Only Tests (`15,175` files / `61.8%`)**: `15,036` files in `tests/ui`, `26` in `tests/ui-fulldeps`, and `113` in `tests/pretty`. These tests either carry `//@ check-pass` (`4,084` files) or expect frontend type/borrow/resolve/syntax diagnostics (`//~ ERROR`, `//@ check-fail`, `.stderr`) without invoking backend code generation or object linking.
2. **Backend-Agnostic Codegen, Linking, and Execution Tests (`5,625` files / `22.9%`)**: `4,826` files in `tests/ui` (including `3,859` explicit `//@ run-pass`, `594` `//@ build-pass`, `227` `//@ build-fail`, and `run-fail` / `run-crash` tests), `49` in `tests/ui-fulldeps`, `347` in `tests/run-make`, `9` in `tests/run-make-cargo`, `1` in `tests/build-std`, `178` in `tests/incremental`, `169` in `tests/debuginfo`, and `46` in `tests/codegen-units`. These exercise MIR-to-machine lowering, ABI calling conventions, object emission, linking, debuginfo, or runtime execution without coupling to LLVM IR text.
3. **MIR-Only Pass Tests (`400` files / `1.6%`)**: All `400` files in `tests/mir-opt`, which inspect `-Zdump-mir` outputs and `.diff` files before backend codegen.
4. **LLVM-Specific or Assembly-Text-Coupled Tests (`1,450` files / `5.9%`)**: `801` files in `tests/codegen-llvm` (`FileCheck` over LLVM IR), `163` in `tests/assembly-llvm` (`FileCheck` over assembly mnemonics, often with `needs-llvm-components`), `99` in `tests/coverage` + `coverage-run-rustdoc`, `211` in `tests/ui` + `ui-fulldeps` (using `-Cllvm-args` or `needs-llvm-components`), `177` in `tests/run-make` + `run-make-cargo` (invoking `FileCheck`, `clang`, `llvm-*` tools, or LLVM bitcode LTO), and `2` in `tests/incremental`.
5. **Rustdoc and ICE Crash Suites (`1,892` files / `7.7%`)**: `1,713` files across `rustdoc-{html,ui,json,gui,js,js-std}` and `179` ICE reproducers in `tests/crashes`.

## Applicability

- **Pinned subject**: `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc 1.99.1`).
- **Dataset location**:
  - `support/test_catalog.jsonl.gz`: Gzip-compressed JSON Lines catalog with one record per test file (`24,477` records across all non-JS suites; 562 KB compressed), recording `path`, `suite`, `mode`, `tier`, `pass_mode`, `fail_mode`, `revisions`, `observes`, `only`, `ignore`, `needs`, `clif_status`, and `gcc_status`.
  - `support/test_classification_summary.json`: Aggregated per-suite counts, top 100 directives, top 60 `only-*` / `ignore-*` / `needs-*` conditions, and LLVM component frequencies.
  - `support/classify_tests_and_directives.py`: Standalone reproducible classifier script.

## Findings

### 1. Per-Suite Breakdown by Pipeline Tier and Alternate-Backend Status

Basis: source + execution of `support/classify_tests_and_directives.py` over `rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`

| Suite (`tests/<suite>`) | Mode | Total Files | Frontend-Only | Backend-Codegen | LLVM / Asm Specific | MIR / Rustdoc / ICE | Kept by `cg_clif` | Kept by `cg_gcc` (Pass + Error Runs) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `ui` | `ui` | 20,072 | 15,036 | 4,826 | 210 | 0 | 7,357 | 19,360 |
| `ui-fulldeps` | `ui` | 76 | 26 | 49 | 1 | 0 | 0 | 0 |
| `codegen-llvm` | `codegen` | 801 | 0 | 0 | 801 | 0 | 0 | 0 |
| `run-make` | `run-make` | 519 | 0 | 347 | 172 | 0 | 448 | 505 |
| `mir-opt` | `mir-opt` | 400 | 0 | 0 | 0 | 400 (`mir-only`) | 0 | 0 |
| `incremental` | `incremental` | 180 | 0 | 178 | 2 | 0 | 173 | 0 |
| `crashes` | `crashes` | 179 | 0 | 0 | 0 | 179 (`ice`) | 0 | 0 |
| `debuginfo` | `debuginfo` | 169 | 0 | 169 | 0 | 0 | 0 | 0 |
| `assembly-llvm` | `assembly` | 163 | 0 | 0 | 163 | 0 | 0 | 0 |
| `pretty` | `pretty` | 113 | 113 | 0 | 0 | 0 | 0 | 0 |
| `coverage` | `coverage-map` / `run` | 98 | 0 | 0 | 98 | 0 | 0 | 0 |
| `codegen-units` | `codegen-units` | 46 | 0 | 46 | 0 | 0 | 46 | 0 |
| `run-make-cargo` | `run-make` | 14 | 0 | 9 | 5 | 0 | 11 | 14 |
| `build-std` | `run-make` | 1 | 0 | 1 | 0 | 0 | 0 | 0 |
| `coverage-run-rustdoc` | `coverage-run-rustdoc` | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| `rustdoc-html` | `rustdoc-html` | 837 | 0 | 0 | 0 | 837 (`rustdoc`) | 0 | 0 |
| `rustdoc-ui` | `ui` | 390 | 0 | 0 | 0 | 390 (`rustdoc`) | 0 | 0 |
| `rustdoc-json` | `rustdoc-json` | 194 | 0 | 0 | 0 | 194 (`rustdoc`) | 0 | 0 |
| `rustdoc-gui` | `rustdoc-gui` | 146 | 0 | 0 | 0 | 146 (`rustdoc`) | 0 | 0 |
| `rustdoc-js` | `rustdoc-js` | 78 | 0 | 0 | 0 | 78 (`rustdoc`) | 0 | 0 |
| `rustdoc-js-std` | `rustdoc-js` | 68 (`.js`) | 0 | 0 | 0 | 68 (`rustdoc`) | 0 | 0 |
| **Total (`tests/`)** | — | **24,545** | **15,175** | **5,625** | **1,453** | **2,292** | **8,035** | **19,879** |

### 2. Directive, Target Condition (`only-*` / `ignore-*`), and Capability (`needs-*`) Frequencies

Basis: execution (`support/test_classification_summary.json`)

1. **Most Frequent Directives Across `tests/`**:
   - `compile-flags` (`7,087`), `check-pass` (`4,084`), `has` (`4,047`, rustdoc HTML checks), `run-pass` (`3,859`), `edition` (`2,636`), `revisions` (`2,321`), `gdb-command` (`1,787`), `needs-llvm-components` (`1,437`), `aux-build` (`1,407`), `lldb-command` (`1,326`), `gdb-check` (`1,297`), `is` (`1,006`), `lldb-check` (`897`), `cdb-check` (`797`), `ignore-backends` (`754`), `run-rustfix` (`705`), `build-pass` (`594`), `cdb-command` (`459`), `count` (`416`), `add-minicore` (`402`), `ignore-cross-compile` (`393`), `normalize-stderr` (`371`), `ignore-compare-mode-next-solver` (`365`), `known-bug` (`309`), `reference` (`289`), `proc-macro` (`280`), `error-pattern` (`248`), `matches` (`235`), `check-fail` (`232`), `build-fail` (`227`).
2. **Target Restriction Distribution (`only-*` and `ignore-*`)**:
   - **Architecture/Target `only-*` filters**: `only-x86_64` (`208`), `only-linux` (`82`), `only-64bit` (`64`), `only-aarch64` (`61`), `only-windows` (`50`), `only-x86_64-unknown-linux-gnu` (`43`), `only-msvc` (`34`), `only-x86` (`27`), `only-apple` (`27`), `only-unix` (`23`), `only-wasm32` (`20`), `only-elf` (`15`), `only-wasm32-wasip1` (`15`), `only-nightly` (`14`), `only-nvptx64` (`13`), `only-gnu` (`13`), `only-pauthtest` (`12`), `only-32bit` (`12`), `only-x86_64-pc-windows-msvc` (`8`), `only-aarch64-unknown-linux-gnu` (`6`), `only-aarch64-apple-darwin` (`4`).
   - **Backend/Environment `ignore-*` filters**: `ignore-backends` (`754`), `ignore-cross-compile` (`393`), `ignore-compare-mode-next-solver` (`365`), `ignore-windows` (`59`), `ignore-windows-gnu` (`57`), `ignore-emscripten` (`52`), `ignore-stage1` (`49`), `ignore-compare-mode-polonius` (`43`), `ignore-msvc` (`42`), `ignore-remote` (`42`), `ignore-sgx` (`39`), `ignore-android` (`38`), `ignore-lldb` (`38`), `ignore-auxiliary` (`35`), `ignore-fuchsia` (`35`), `ignore-apple` (`29`), `ignore-wasm` (`27`), `ignore-wasm32` (`25`), `ignore-nvptx64` (`24`), `ignore-parallel-frontend` (`23`), `ignore-std-debug-assertions` (`18`).
3. **Required Capabilities (`needs-*`) and LLVM Target Components**:
   - `needs-llvm-components` (`1,437`): `x86` (`451`), `aarch64` (`281`), `arm` (`180`), `riscv` (`126`), `powerpc` (`71`), `mips` (`65`), `systemz` (`45`), `sparc` (`43`), `webassembly` (`41`), `loongarch` (`34`), `nvptx` (`29`), `avr` (`23`), `amdgpu` (`21`), `bpf` (`16`), `hexagon` (`14`), `msp430` (`14`), `m68k` (`13`), `csky` (`4`), `xtensa` (`3`).
   - Runtime and toolchain capabilities: `needs-unwind` (`209`), `needs-subprocess` (`179`), `needs-target-std` (`120`), `needs-threads` (`105`), `needs-asm-support` (`95`), `needs-sanitizer-cfi` (`65`), `needs-enzyme` (`57`), `needs-crate-type` (`33`), `needs-rustc-debug-assertions` (`26`), `needs-dynamic-linking` (`23`), `needs-sanitizer-support` (`21`), `needs-rust-lld` (`18`), `needs-sanitizer-address` (`17`), `needs-sanitizer-kcfi` (`17`), `needs-deterministic-layouts` (`15`), `needs-profiler-runtime` (`12`), `needs-offload` (`10`), `needs-xray` (`9`).

### 3. Mechanical Selection Queries for a Verified Compiler Replacement

Basis: derived from `support/test_catalog.jsonl.gz` schema

Using `support/test_catalog.jsonl.gz`, a designer can select exact test subsets for any verification milestone or target triple with a single filter pass:

1. **Milestone 1 — Verified MIR/Backend Codegen Without Unwinding or Threads (`no_std` / `minicore` + `core`)**:
   - Filter: `tier == "backend-codegen"` AND `"unwind" not in needs` AND `"threads" not in needs` AND `"subprocess" not in needs` (or `"add-minicore"` in directives, `402` tests).
2. **Milestone 2 — Full Backend Codegen & Execution on a Tier 1 Target (`<triple>`)**:
   - Filter: `tier == "backend-codegen"` AND `only` is empty or matches `<triple>`'s `{arch, os, family, env, pointer_width, binary_format}` AND `ignore` does not match `<triple>`.
   - Yields **5,312 applicable backend-codegen test files** on `x86_64-unknown-linux-gnu`, **5,148** on `aarch64-unknown-linux-gnu`, **5,094** on `i686-unknown-linux-gnu`, **5,081** on `aarch64-apple-darwin`, **5,119** on `x86_64-pc-windows-msvc`, and **5,062** on `x86_64-pc-windows-gnu`.
3. **Milestone 3 — Full Frontend + Backend Drop-In Parity (`rustc` Replacement)**:
   - Filter: `tier in ("frontend-only", "backend-codegen", "mir-only")`, excluding only `tier == "llvm-specific"` (`1,290` tests that inspect LLVM IR text, LLVM coverage maps, or pass `-Cllvm-args`).

## Boundaries

- **Implicit `needs-unwind` / `needs-threads` in older `tests/ui` files**: While 209 tests carry explicit `//@ needs-unwind` and 105 carry `//@ needs-threads`, some older `run-pass` tests spawn threads or call `panic::catch_unwind` without an explicit `needs-*` directive when `needs-target-std` is assumed. When targeting a `panic=abort` or single-threaded target, combine directive filtering with a source grep for `catch_unwind` / `thread::spawn`.
- **`run-make` internal command inspection**: The classifier tags `run-make` recipes (`rmake.rs`) as `llvm-specific` when they reference `llvm_`, `llvm-`, `FileCheck`, `clang`, `-Clto`, or `linker-plugin-lto` (`172` of `519` recipes), and `backend-codegen` otherwise (`347` recipes).

## Evidence

- **Machine-readable dataset and summary**:
  - `support/test_catalog.jsonl.gz` (`24,477` JSONL records, one per test file across 20 non-JS suites).
  - `support/test_classification_summary.json` (suite totals, directive frequencies, condition counts, LLVM component counts).
  - `support/classify_tests_and_directives.py` (deterministic Python extractor).
- **Primary upstream source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `tests/` (`21` suite directories, `26,548` `.rs` files, `13,667` `.stderr` files).
  - `library/{coretests,alloctests,std,alloc,core,compiler-builtins,stdarch,portable-simd,std_detect,test}` (`4,819` `#[test]` functions).

## Revalidation

Run `python3 support/classify_tests_and_directives.py --rust-root <path-to-rust> --out-dir <out>` to regenerate `test_classification_summary.json` and `test_catalog.jsonl.gz` for any newer `rust-lang/rust` revision.
