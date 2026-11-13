# Download-Weighted Crates.io Code-Generation Demand and MIR Construct Census

## Summary

Evaluating what real-world Rust crates demand from a verified compiler backend—weighted
by crates.io download volume across the pinned Top-100 corpus (`8,422,968,730`
recent 90-day downloads, `52,249,410,051` all-time downloads, `1,900,057` lines
of non-test Rust across `3,421` `.rs` files) and compared against `833` cached
packages from the `1,129`-package transitive dependency closure and `16`
compiled stratified crates (`5,759` MIR functions, `34,866` basic blocks)—yields
four governing insights for compiler design:

1. **Pervasiveness of `unsafe`, atomics, and layout representations in high-download crates:**
   Across the Top-100 crates, **64.0% unweighted (`64.2%` recent-download-weighted,
   `65.7%` all-time-download-weighted)** contain at least one `unsafe` construct
   (`62.0%` `unsafe {}` blocks, `40.0%` `unsafe fn`, `33.0%` `unsafe impl`,
   `13.0%` `unsafe trait`), while only **14.0%** carry `#![forbid(unsafe_code)]`
   and **1.0%** (`rustix`) carries `#![deny(unsafe_code)]`. Across the broader
   833-crate dependency closure, `unsafe` usage remains **`56.8%` (`473/833`)**.
   Atomics (`Atomic*`, `Ordering`, `fence`) appear in **`31.0%` (`31.7%`
   download-weighted)** of Top-100 crates (`24.6%` in the 833-crate closure),
   `#[repr(transparent)]` in **`26.0%` (`29.0%` download-weighted)**,
   `#[repr(C)]` in **`18.0%` (`18.6%` download-weighted)**, `#[repr(align(N))]`
   in **`13.0%` (`12.8%` download-weighted)**, and `#[repr(packed)]` in **`6.0%`
   (`6.8%` download-weighted)**.
2. **Concentration of SIMD, `#[target_feature]`, runtime CPU dispatch, and inline assembly:**
   Vendor SIMD (`core::arch::{x86,x86_64,aarch64,wasm32}`) is used by **`6.0%`
   (`8.1%` download-weighted)** of the Top-100 (`hashbrown`, `getrandom`,
   `rand`, `memchr`, `aho-corasick`, `ppv-lite86`) and **`8.9%` (`74/833`)** of
   the dependency closure. Compile-time `cfg(target_feature = "...")` appears in
   **`9.0%` (`11.3%` download-weighted)**, function-level
   `#[target_feature(enable = "...")]` (`avx2`, `sse2`, `ssse3`, `sse4.1`, `avx`,
   `neon`, `simd128`, `rdrand`) and runtime feature detection
   (`is_x86_feature_detected!`, `is_aarch64_feature_detected!`, `cpufeatures::new!`)
   each appear in **`4.0%` (`4.6%` download-weighted; `4.6%` / `4.2%` in the
   closure)**, and inline assembly (`asm!` / `naked_asm!`) appears in **`3.0%`
   (`3.7%` download-weighted: `getrandom`, `rustix`, `parking_lot`; `3.0%` or
   `25/833` in the closure)**. Notably, **`0.0%` (`0/100` and `0/833`)** of
   ecosystem crates define custom `#[repr(simd)]` types directly; all ecosystem
   SIMD goes through `core::arch` vendor types (`__m128i`, `__m256i`,
   `uint8x16_t`).
3. **FFI, `#[link]` kinds, `catch_unwind`, TLS, build scripts, and `#![feature]` gates:**
   Non-Rust `extern` ABIs (`"C"` in `9` Top-100 crates, `"system"` in `6`)
   appear in **`12.0%` (`12.5%` download-weighted; `14.3%` in the closure)**;
   `#[link(...)]` attributes appear in **`5.0%` (`5.5%` download-weighted)**,
   including Windows `kind = "raw-dylib"` in `getrandom` and `windows-targets`;
   `catch_unwind` / `resume_unwind` appears in **`11.0%` (`10.8%`
   download-weighted)**; `thread_local!` appears in **`13.0%` (`13.4%`
   download-weighted)** (whereas unstable `#[thread_local]` appears only in
   `libc`, `1.0%`); and `build.rs` scripts appear in **`21.0%` (`22.6%`
   download-weighted; `18.1%` in the closure)**, with foreign C/ASM compilation
   via `cc`/`cmake` occurring in **`0.0%` of the Top-100** and **`1.3%`
   (`11/833`: `blake3`, `ring`, `libsqlite3-sys`, `iana-time-zone-haiku`)** of
   the dependency closure. Although **`45.0%` (`46.0%` download-weighted)** of
   Top-100 crates contain a `#![feature(...)]` attribute in source, **82.2%
   (`37/45`)** of those are documentation-only `doc_cfg` / `doc_auto_cfg` gates
   wrapped in `#[cfg_attr(docsrs, feature(doc_cfg))]`.
4. **Comparison with published unsafe-Rust studies (2020–2021):**
   Whereas unweighted full-crates.io surveys by Astrauskas et al. (OOPSLA 2020)
   and Evans et al. (ICSE 2020) found explicit `unsafe` in `21.1%`–`29.0%` of
   all crates, restricting to the Top-100 most-downloaded crates (or weighting
   by downloads) more than doubles the `unsafe` incidence to **`64.0%`–`65.7%`**,
   confirming Evans et al.'s propagation finding that heavily depended-upon core
   libraries (`hashbrown`, `syn`, `libc`, `bitflags`, `serde`, `memchr`,
   `parking_lot`, `tokio`) concentrate low-level memory, SIMD, and FFI
   primitives behind safe public APIs.

## Applicability

These measurements apply to the pinned **Rust 1.99.1** baseline (`rust-lang/rust`
`58cf8f9c35b355199727627d07ae34a4e2846d67`) and the shared three-tier crate
corpus defined in `rustc-experimental-corpora-and-harness-conventions`
(`support/crates_manifest.json`):

- **Tier A (`Top-100` by recent downloads):** `100` crates totaling
  `8,422,968,730` recent downloads and `52,249,410,051` all-time downloads
  (`1,900,057` lines of non-test `.rs` code across `3,421` files), scanned from
  checksum-verified `.crate` archives after stripping all `//` and `/* ... */`
  comments.
- **Tier B (`833` cached packages from the `1,129`-package dependency closure):**
  Provides a wide-ecosystem comparison that includes `57` procedural-macro
  crates (`proc-macro = true`) and `11` native C/ASM `-sys` crates (`ring`,
  `blake3`, `libsqlite3-sys`).
- **Tier C (`16` compiled stratified workspace crates):** Compiled with
  `cargo +1.99.1-x86_64-unknown-linux-gnu rustc --lib --offline -- -C opt-level=3 --emit=mir`
  to measure post-cleanup MIR construct frequencies across `5,759` functions and
  `34,866` basic blocks.

## Findings

### 1. Download-weighted codegen feature census across the Top-100 and 833-crate closure

Basis: source + execution

Table 1 presents the complete feature census across the Top-100 crates (both
unweighted crate count/percentage and weighted by recent 90-day and all-time
crates.io download volume) alongside the 833-crate dependency closure.

| Code-Generation Feature / Construct | Top-100 Crates (`N/100`) | Top-100 Recent-Download Share (`%` of `8.42B`) | Top-100 All-Time-Download Share (`%` of `52.25B`) | 833-Crate Closure (`N/833`, `%`) | Representative Crates in Sample |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Any `unsafe` construct** | `64` (`64.0%`) | **`64.2%`** | **`65.7%`** | `473` (`56.8%`) | `hashbrown`, `syn`, `getrandom`, `bitflags`, `itertools` |
| `unsafe { ... }` block | `62` (`62.0%`) | **`61.7%`** | **`62.8%`** | `452` (`54.3%`) | `hashbrown`, `syn`, `getrandom`, `itertools`, `indexmap` |
| `unsafe fn` declaration | `40` (`40.0%`) | **`42.5%`** | **`42.6%`** | `306` (`36.7%`) | `hashbrown`, `syn`, `getrandom`, `itertools`, `rand` |
| `unsafe impl` block | `33` (`33.0%`) | **`33.5%`** | **`34.8%`** | `218` (`26.2%`) | `hashbrown`, `syn`, `bitflags`, `libc`, `socket2` |
| `unsafe trait` declaration | `13` (`13.0%`) | **`13.5%`** | **`13.4%`** | `72` (`8.6%`) | `hashbrown`, `libc`, `regex-automata`, `rustix`, `smallvec` |
| `#![forbid(unsafe_code)]` | `14` (`14.0%`) | **`14.0%`** | **`12.9%`** | `103` (`12.4%`) | `bitflags` (default), `base64`, `rand_chacha`, `regex-syntax` |
| `#![deny(unsafe_code)]` | `1` (`1.0%`) | **`1.1%`** | **`1.0%`** | `13` (`1.6%`) | `rustix` (Selectively overridden in backend modules) |
| **Atomics (`Atomic*`, `Ordering`, `fence`)** | `31` (`31.0%`) | **`31.7%`** | **`31.6%`** | `205` (`24.6%`) | `hashbrown`, `getrandom`, `proc-macro2`, `serde`, `once_cell` |
| **`#[repr(transparent)]`** | `26` (`26.0%`) | **`29.0%`** | **`28.4%`** | `154` (`18.5%`) | `hashbrown`, `syn`, `bitflags`, `indexmap`, `windows-sys` |
| **`#[repr(C)]`** | `18` (`18.0%`) | **`18.6%`** | **`18.1%`** | `145` (`17.4%`) | `hashbrown`, `windows-sys`, `libc`, `unicode-ident`, `rustix` |
| **`#[repr(align(N))]`** | `13` (`13.0%`) | **`12.8%`** | **`12.5%`** | `75` (`9.0%`) | `libc`, `unicode-ident`, `regex-automata`, `rustix`, `crossbeam-utils` |
| **`#[repr(packed)]`** | `6` (`6.0%`) | **`6.8%`** | **`6.7%`** | `39` (`4.7%`) | `windows-sys`, `libc`, `rustix`, `linux-raw-sys`, `zerocopy` |
| **`#[repr(simd)]`** | `0` (`0.0%`) | **`0.0%`** | **`0.0%`** | `0` (`0.0%`) | *(None outside `core::arch` / `core::simd`)* |
| **Compile-time `cfg(target_feature)`** | `9` (`9.0%`) | **`11.3%`** | **`11.5%`** | `64` (`7.7%`) | `hashbrown`, `getrandom`, `rand`, `libc`, `memchr` |
| **Vendor SIMD (`core::arch::*`)** | `6` (`6.0%`) | **`8.1%`** | **`8.0%`** | `74` (`8.9%`) | `hashbrown`, `getrandom`, `rand`, `memchr`, `aho-corasick`, `ppv-lite86` |
| **`#[target_feature(enable = "...")]`** | `4` (`4.0%`) | **`4.6%`** | **`4.7%`** | `38` (`4.6%`) | `getrandom`, `memchr`, `aho-corasick`, `ppv-lite86` |
| **Runtime CPU detection (`is_*_feature_detected!`, `cpufeatures`)** | `4` (`4.0%`) | **`4.6%`** | **`4.7%`** | `35` (`4.2%`) | `getrandom`, `memchr`, `aho-corasick`, `ppv-lite86` |
| **Inline assembly (`asm!`, `naked_asm!`, `global_asm!`)** | `3` (`3.0%`) | **`3.7%`** | **`3.5%`** | `25` (`3.0%`) | `getrandom`, `rustix`, `parking_lot` |
| **Direct `core::intrinsics::*`** | `1` (`1.0%`) | **`1.1%`** | **`1.0%`** | `5` (`0.6%`) | `rustix` |
| **Non-Rust `extern` ABI (`"C"`, `"system"`, `"C-unwind"`)** | `12` (`12.0%`) | **`12.5%`** | **`12.1%`** | `119` (`14.3%`) | `getrandom`, `windows-sys`, `libc`, `rustix`, `parking_lot` |
| **`#[link(...)]` attribute** | `5` (`5.0%`) | **`5.5%`** | **`5.4%`** | `28` (`3.4%`) | `getrandom`, `libc`, `windows-targets`, `nix`, `time` |
| **`#[link(..., kind = "raw-dylib")]`** | `1` (`1.0%`) | **`1.7%`** | **`1.5%`** | `3` (`0.4%`) | `getrandom`, `windows-targets` |
| **`catch_unwind` / `resume_unwind`** | `11` (`11.0%`) | **`10.8%`** | **`11.2%`** | `57` (`6.8%`) | `itertools`, `proc-macro2`, `once_cell`, `smallvec`, `tokio` |
| **`thread_local!` macro** | `13` (`13.0%`) | **`13.4%`** | **`13.5%`** | `89` (`10.7%`) | `hashbrown`, `rand`, `proc-macro2`, `regex-automata`, `parking_lot`, `tokio` |
| **`#[thread_local]` attribute** | `1` (`1.0%`) | **`1.4%`** | **`1.5%`** | `8` (`1.0%`) | `libc` |
| **`#[linkage = "..."]` attribute** | `0` (`0.0%`) | **`0.0%`** | **`0.0%`** | `1` (`0.1%`) | `core-foundation-sys` |
| **`#[link_section = "..."]` attribute** | `0` (`0.0%`) | **`0.0%`** | **`0.0%`** | `5` (`0.6%`) | `wasi`, `wasip2`, `wasm-bindgen-backend` |
| **Exported symbols (`#[no_mangle]`, `#[export_name]`, `#[used]`)** | `1` (`1.0%`) | **`0.9%`** | **`0.8%`** | `18` (`2.2%`) | `hyper` (C API), `wasm-bindgen` |
| **Custom build script (`build.rs`)** | `21` (`21.0%`) | **`22.6%`** | **`21.7%`** | `151` (`18.1%`) | `getrandom`, `libc`, `proc-macro2`, `thiserror`, `quote`, `serde` |
| **`build.rs` compiling foreign C/C++/ASM (`cc`, `cmake`)** | `0` (`0.0%`) | **`0.0%`** | **`0.0%`** | `11` (`1.3%`) | `blake3`, `ring`, `libsqlite3-sys`, `iana-time-zone-haiku` |
| **Procedural macro (`proc-macro = true`)** | `2` (`2.0%`) | **`2.5%`** | **`2.5%`** | `57` (`6.8%`) | `thiserror-impl`, `serde_derive` |
| **Conditional `#![feature(...)]` gates** | `45` (`45.0%`) | **`46.0%`** | **`46.1%`** | `261` (`31.3%`) | `doc_cfg` (`37/100`), `doc_auto_cfg` (`4/100`), `dropck_eyepatch` (`2/100`), `allocator_api` (`1/100`) |

Three technical details inside Table 1 directly shape compiler design priorities:

1. **Unstable `#![feature(...)]` gates are overwhelmingly `docsrs` metadata or
   opt-in nightly features:** Of the `45` Top-100 crates containing a
   `#![feature(...)]` attribute, `37` (`35.9%` download weight) enable `doc_cfg`
   and `4` (`4.5%` download weight) enable `doc_auto_cfg` behind
   `#[cfg_attr(docsrs, ...)]`. Only `8` Top-100 crates conditionally gate
   language or library features behind opt-in Cargo `nightly` features:
   `hashbrown` (`core_intrinsics`, `dropck_eyepatch`, `min_specialization`,
   `allocator_api`, `slice_ptr_get`, `extend_one`, `rustc_attrs`), `smallvec`
   (`dropck_eyepatch`, `may_dangle`), `indexmap` (`test`), and `thiserror`
   (`error_generic_member_access`). All `100` Top-100 crates compile on stable
   `rustc 1.99.1` under default features without enabling any `#![feature]`.
2. **ABI string concentration:** Across the Top-100, non-Rust `extern` blocks
   and function pointers use only two foreign calling conventions: `"C"` (`9`
   crates, `9.3%` download weight: `getrandom`, `libc`, `rustix`, `parking_lot`,
   `socket2`, `mio`, `nix`, `hyper`, `time`) and `"system"` (`6` crates, `7.0%`
   download weight: `windows-sys`, `windows-targets`, `getrandom`, `libc`,
   `parking_lot`, `socket2`—where `"system"` resolves to `"stdcall"` on
   `i686-pc-windows-*` and `"C"` on all 64-bit Tier 1 targets).
3. **Target features enabled in the wild:** Across the Top-100, function-level
   `#[target_feature(enable = "...")]` uses only `9` distinct feature strings:
   `avx2` (`3` crates: `memchr`, `aho-corasick`, `ppv-lite86`), `sse2` (`2`:
   `memchr`, `ppv-lite86`), `ssse3` (`2`: `aho-corasick`, `ppv-lite86`), `neon`
   (`2`: `memchr`, `aho-corasick`), `sse4.1` (`1`), `avx` (`1`), `rdrand` (`1`:
   `getrandom`), `rand` (`1`: `getrandom` on AArch64 `rndr`), and `simd128`
   (`1`: `ppv-lite86` on Wasm).

### 2. MIR construct frequency distribution across the stratified crate sample

Basis: execution

Table 2 reports the post-cleanup MIR construct frequencies across `16` compiled
crates from the stratified 25-crate sample (`arrayvec`, `bitflags`, `byteorder`,
`bytes`, `glob`, `hashbrown`, `http`, `itoa`, `libc`, `mio`, `once_cell`,
`parking_lot`, `proc-macro2`, `regex`, `ryu`, and `smallvec`; `5,759` functions,
`34,866` basic blocks, `76,335` statements, `34,618` terminators) and compares
them with `core + alloc` (`14,486` functions, `63,050` basic blocks, `264,546`
statements).

| MIR Category | Construct | Ecosystem Stratified Sample Count | Ecosystem Category Share (`%`) | `core + alloc` Category Share (`%`) | Structural Difference Between Ecosystem & Stdlib |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Statements** (`76,335` total) | `StorageDead(Local)` | `26,862` | `35.19%` | `32.81%` | Nearly identical ($\sim 1/3$ of all MIR statements) |
| **Statements** | `Assign(Place, Rvalue)` | `25,970` | `34.02%` | `37.24%` | Nearly identical ($\sim 1/3$ of all MIR statements) |
| **Statements** | `StorageLive(Local)` | `23,503` | `30.79%` | `29.95%` | Nearly identical ($\sim 1/3$ of all MIR statements) |
| **Terminators** (`34,618` total) | `Call` | `13,741` | **`39.69%`** | `27.25%` | Ecosystem code is **+12.4 percentage points more call-heavy** than `core` |
| **Terminators** | `Return` | `6,248` | `18.05%` | `24.15%` | Fewer single-block leaf functions than `core` intrinsics/wrappers |
| **Terminators** | `SwitchInt` | `5,978` | `17.27%` | `18.42%` | Consistent branch/pattern-match density ($\sim 17	ext{–}18\%$) |
| **Terminators** | `Goto` | `5,360` | `15.48%` | `22.21%` | Control-flow joins after `SwitchInt` and `Call` |
| **Terminators** | `Drop` | `1,703` | **`4.92%`** | `1.99%` | Ecosystem types (`Vec`, `String`, `Box`, `Bytes`) drop **2.5$	imes$ more often** than `core` |
| **Terminators** | `Unreachable` | `830` | `2.40%` | `2.69%` | Exhaustive `match` / uninhabited enum branches |
| **Terminators** | `UnwindResume` | `646` | **`1.87%`** | `0.90%` | Cleanup landing-pad resumes scale with `Drop` frequency |
| **Terminators** | `Assert` | `112` | `0.32%` | `2.38%` | Bounds/division assertions (many inlined from `core::slice`) |
| **Rvalues** (`25,970` total) | `Use` / `Copy` / `Move` | `6,690` | `25.76%` | `36.66%` | Local variable moves and copies |
| **Rvalues** | `Ref` (`&` / `&mut`) | `6,008` | **`23.13%`** | `5.05%` | Ecosystem borrows references **4.6$	imes$ more frequently** than `core` |
| **Rvalues** | `Aggregate` (structs, enums, tuples) | `5,257` | **`20.24%`** | `16.94%` | High rate of `Result`/`Option`/struct construction |
| **Rvalues** | `Cast` (`IntToInt`, `PtrToPtr`, `Unsize`, `PointerCoercion`) | `3,621` | `13.94%` | `17.96%` | Integer and pointer casts |
| **Rvalues** | `BinaryOp` | `2,210` | `8.51%` | `17.31%` | Arithmetic, bitwise, and comparison operations |
| **Rvalues** | `Discriminant` | `1,655` | **`6.37%`** | `2.69%` | Enum tag reads (`Option`, `Result`, parser/regex state machines) |
| **Rvalues** | `UnaryOp` (`Not`, `Neg`, `PtrMetadata`) | `297` | `1.14%` | `1.64%` | Boolean/bitwise negation and slice length/metadata extraction |
| **Rvalues** | `RawPtr` (`&raw const` / `&raw mut`) | `128` | `0.49%` | `1.69%` | Raw address-of expressions |
| **Rvalues** | `Repeat` (`[x; N]`) | `104` | `0.40%` | `0.06%` | Fixed-size array initializers |

### 3. Comparison with published studies of unsafe Rust

Basis: documentation + derived

Table 3 compares our empirical Rust 1.99.1 census (`2026`) against the major
published academic studies of unsafe Rust across crates.io.

| Study & Corpus | Examined Sample & Methodology | Reported `unsafe` Crate Share | Key Findings & Relationship to Rust 1.99.1 Census |
| :--- | :--- | :--- | :--- |
| **Astrauskas et al. (OOPSLA 2020)**, *"How Do Programmers Use Unsafe Rust?"* | `31,869` crates across crates.io (`rustc` nightly `2019-08`, HIR/MIR inspection) | **`21.1%`** of all crates (`23.6%` including macro expansions) | Found that across all published crates (mostly small, low-download leaves), `~79%` contain no explicit `unsafe`, and raw pointer dereferencing (`*ptr`), `unsafe fn` calls (FFI + stdlib unchecked APIs), and mutable statics dominate. In our Top-100 download corpus, `unsafe` is **3.0$	imes$ higher (`64.0%`)** because download volume is heavily concentrated in foundational container, parser, sync, and OS-binding crates. |
| **Evans et al. (ICSE 2020)**, *"Is Rust Used Safely by Software Developers?"* | All crates.io versions up to `2019` (`~24,000` crates, AST + call-graph analysis) | **`29.0%`** direct `unsafe` across crates; **`>50%`** among top-downloaded crates | Demonstrated that while fewer than `30%` of all crates write `unsafe` blocks directly, **over half of the most-downloaded crates use `unsafe` directly**, and `~90%` of crates depend transitively on an `unsafe`-using crate. Our `64.2%` download-weighted Top-100 figure and `56.8%` transitive-closure figure directly corroborate Evans et al.'s top-heavy concentration law seven years later. |
| **Qin et al. (PLDI 2020)**, *"Understanding Memory and Thread Safety Practices and Issues in Real-World Rust Programs"* | `5` large applications (`Servo`, `TiKV`, `Redox`, `Tock`, `Ethereum Parity`) + `850` bugs | `100%` of sampled systems workspaces use `unsafe` | Categorized `unsafe` uses into performance optimization (uninitialized memory, bounds-check elision, SIMD), FFI (`extern "C"`), concurrency primitives (`UnsafeCell` + atomics), and hardware/OS access (`asm!`). In our Top-100 census, those exact four motivations account for `62/64` unsafe crates: performance/containers (`hashbrown`, `smallvec`, `bytes`, `memchr`), FFI (`libc`, `windows-sys`, `rustix`), sync (`parking_lot`, `once_cell`, `tokio`), and SIMD (`aho-corasick`, `ppv-lite86`). |
| **This Census (`Rust 1.99.1`, 2026)** | Top-100 by downloads (`8.42B` recent / `52.25B` total) + `833`-crate dependency closure | **`64.0%`** (`64.2%` dl-weighted) in Top-100; **`56.8%`** in 833-crate closure | Reveals three secular shifts since 2019–2020: (1) direct `core::intrinsics` (`1.0%`) and `#[repr(simd)]` (`0.0%`) have almost completely disappeared from ecosystem crates in favor of stabilized `core::ptr`, `core::hint`, and `core::arch` APIs; (2) `#![forbid(unsafe_code)]` has risen to `14.0%` of the Top-100 (`12.4%` of closure); and (3) `#[repr(transparent)]` (`29.0%` dl-weighted) and `MaybeUninit`/atomic state machines (`31.7%` dl-weighted) have replaced legacy `mem::uninitialized()` and raw `transmute` patterns. |

## Boundaries

- **Target-conditional source scanning vs. single-target MIR emission:** The
  source-level census (Section 1) inspects all non-test `.rs` files packaged in
  each crate archive across all `#[cfg(...)]` branches, whereas the MIR
  construct census (Section 2) measures post-cleanup MIR emitted for
  `x86_64-unknown-linux-gnu` under default Cargo features at `-C opt-level=3`.
- **Macro expansion horizon:** Source-level counts record constructs written in
  each crate's `.rs` source files; `unsafe` blocks generated inside macro
  expansions (`pin_project_lite`, `bitflags`, `tokio::select!`) are captured in
  the compiled MIR construct census (Section 2) rather than the lexical source
  counts of downstream caller crates.

## Evidence

- **Pinned crate corpus manifest:**
  `reports/rustc-experimental-corpora-and-harness-conventions/support/crates_manifest.json`
  (100 top crates with verified `.crate` SHA-256 digests, 25 stratified crates,
  and 1,129 dependency-closure packages).
- **Published literature compared in Section 3:**
  - Vytautas Astrauskas, Christoph Matheja, Federico Poli, Peter Müller, and
    Alexander J. Summers, *"How Do Programmers Use Unsafe Rust?"*, Proc. ACM
    Program. Lang. 4, OOPSLA, Article 136 (November 2020).
  - Ana Nora Evans, Brad Campbell, and Mary Lou Soffa, *"Is Rust Used Safely by
    Software Developers?"*, Proceedings of the ACM/IEEE 42nd International
    Conference on Software Engineering (ICSE 2020), pp. 246–257.
  - Boqin Qin, Yilun Chen, Zeming Yu, Linhai Song, and Yiying Zhang,
    *"Understanding Memory and Thread Safety Practices and Issues in Real-World
    Rust Programs"*, Proceedings of the 41st ACM SIGPLAN Conference on
    Programming Language Design and Implementation (PLDI 2020), pp. 763–779.
- **Preserved support datasets:**
  - `support/ecosystem_census_top100.json` — per-crate feature vector and
    download weights for all 100 top crates plus aggregate summaries for the
    Top-100 and 833-crate closure.
  - `support/ecosystem_census_summary.csv` — flat CSV comparison table of
    unweighted, recent-download-weighted, all-time-download-weighted, and
    833-crate closure percentages across all 32 codegen features.
  - `support/mir_construct_frequencies.json` — per-crate and aggregate MIR
    statement, terminator, and Rvalue frequencies across the 16 compiled
    stratified crates.

## Revalidation

To revalidate the MIR construct distribution on a newer `rustc` toolchain for
any crate in the stratified sample, run:

```bash
cargo +1.99.1-x86_64-unknown-linux-gnu rustc --lib --offline -- -C opt-level=3 --emit=mir
```

and compare the statement, terminator, and Rvalue counts against
`support/mir_construct_frequencies.json`.
